import datetime
import os
import re
import shutil
import threading
import time
from io import BytesIO
from pathlib import Path
from threading import Lock
from typing import Any, List, Dict, Tuple, Optional
from urllib.parse import urljoin, urlparse
from xml.dom import minidom

import chardet
import pytz
import requests
from PIL import Image
from apscheduler.schedulers.background import BackgroundScheduler
from lxml import etree
from requests import RequestException
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer
from watchdog.observers.polling import PollingObserver
from app.helper.downloader import DownloaderHelper
from app.helper.mediaserver import MediaServerHelper
from app.helper.sites import SitesHelper
from app.chain.media import MediaChain
from app.modules.indexer.spider import SiteSpider

from app.core.config import settings
from app.core.meta.words import WordsMatcher
from app.core.metainfo import MetaInfo, MetaInfoPath
from app.db.site_oper import SiteOper
from app.log import logger
from app.plugins import _PluginBase
from app.schemas.types import MediaType, NotificationType
from app.utils.common import retry
from app.utils.dom import DomUtils
from app.utils.http import RequestUtils
from app.utils.system import SystemUtils

ffmpeg_lock = threading.Lock()
lock = Lock()
delete_record_lock = Lock()


class FileMonitorHandler(FileSystemEventHandler):
    """
    目录监控响应类
    """

    def __init__(self, watching_path: str, file_change: Any, watch_role: str = "source", **kwargs):
        super(FileMonitorHandler, self).__init__(**kwargs)
        self._watch_path = watching_path
        self.file_change = file_change
        self._watch_role = watch_role

    def on_created(self, event):
        self.file_change.event_handler(event=event,
                                       source_dir=self._watch_path,
                                       event_path=event.src_path,
                                       watch_role=self._watch_role)

    def on_moved(self, event):
        self.file_change.event_handler(event=event,
                                       source_dir=self._watch_path,
                                       event_path=event.dest_path,
                                       watch_role=self._watch_role)

    def on_deleted(self, event):
        self.file_change.event_handler(event=event,
                                       source_dir=self._watch_path,
                                       event_path=event.src_path,
                                       watch_role=self._watch_role)


class ChildrenScraper(_PluginBase):
    # 插件名称
    plugin_name = "儿童刮削"
    # 插件描述
    plugin_desc = "监控儿童剧，按配置硬链接入库，可选 PG数据库、TMDB、好学获取封面和简介。"
    # 插件图标
    plugin_icon = "scraper.png"
    # 插件版本
    plugin_version = "1.0.0"
    # 插件作者
    plugin_author = "qin"
    # 作者主页
    author_url = "https://github.com/qin9125"
    # 插件配置项ID前缀
    plugin_config_prefix = "childrenscraper_"
    # 加载顺序
    plugin_order = 26
    # 可使用的用户级别
    auth_level = 1

    # 私有属性
    _enabled = False
    _monitor_confs = None
    _onlyonce = False
    _image = False
    _exclude_keywords = ""
    _transfer_type = "link"
    _observer = []
    _timeline = "00:00:10"
    _dirconf = {}
    _targetconf = {}
    _source_target_file_map = {}
    _target_source_file_map = {}
    _source_target_dir_map = {}
    _target_source_dir_map = {}
    _renameconf = {}
    _coverconf = {}
    _interval = 30
    _notify = False
    _delete_sync = False
    _delete_downloaders = []
    _refresh_mediaserver = False
    _mediaservers = []
    _scrape_sources = ["tmdb", "hxpt"]
    _pg_host = ""
    _pg_port = 5432
    _pg_database = ""
    _pg_username = ""
    _pg_password = ""
    _pg_table = "public.pt_detail_meta"
    _delete_record_cache = {}
    _notify_image_urls = {}
    _media_query_cache = {}
    _image_download_fail_cache = {}
    _series_poster_fail_cache = {}
    _title_cache = {}
    _medias = {}
    _syncing = False
    _last_config = {}

    @staticmethod
    def __config_bool(value) -> bool:
        """
        MoviePilot 表单值可能是字符串，统一转换后再进入开关逻辑。
        """
        if isinstance(value, bool):
            return value
        if value is None:
            return False
        if isinstance(value, (int, float)):
            return value != 0
        return str(value).strip().lower() in {"true", "1", "yes", "on"}

    # 定时器
    _scheduler: Optional[BackgroundScheduler] = None

    def init_plugin(self, config: dict = None):
        # 清空配置
        self._dirconf = {}
        self._targetconf = {}
        self._source_target_file_map = {}
        self._target_source_file_map = {}
        self._source_target_dir_map = {}
        self._target_source_dir_map = {}
        self._renameconf = {}
        self._coverconf = {}
        self._media_query_cache = {}
        self._image_download_fail_cache = {}
        self._series_poster_fail_cache = {}
        self._title_cache = {}

        if config:
            self._last_config = dict(config)
            self._enabled = self.__config_bool(config.get("enabled"))
            self._onlyonce = self.__config_bool(config.get("onlyonce"))
            self._image = self.__config_bool(config.get("image"))
            self._interval = config.get("interval")
            self._notify = self.__config_bool(config.get("notify"))
            self._delete_sync = self.__config_bool(config.get("delete_sync"))
            self._delete_downloaders = config.get("delete_downloaders") or []
            if isinstance(self._delete_downloaders, str):
                self._delete_downloaders = [item.strip() for item in re.split(r"[,，\s]+", self._delete_downloaders) if item.strip()]
            if not self._delete_downloaders and config.get("delete_downloader"):
                self._delete_downloaders = [config.get("delete_downloader")]
            self._refresh_mediaserver = self.__config_bool(config.get("refresh_mediaserver"))
            self._mediaservers = config.get("mediaservers") or []
            if isinstance(self._mediaservers, str):
                self._mediaservers = [item.strip() for item in re.split(r"[,，\s]+", self._mediaservers) if item.strip()]
            if not self._mediaservers and config.get("mediaserver"):
                self._mediaservers = [config.get("mediaserver")]
            self._scrape_sources = self.__normalize_scrape_sources(config.get("scrape_sources"))
            self._pg_host = str(config.get("pg_host") or "").strip()
            self._pg_port = config.get("pg_port") or 5432
            self._pg_database = str(config.get("pg_database") or "").strip()
            self._pg_username = str(config.get("pg_username") or "").strip()
            self._pg_password = str(config.get("pg_password") or "")
            self._pg_table = str(config.get("pg_table") or "public.pt_detail_meta").strip()
            self._monitor_confs = config.get("monitor_confs")
            self._exclude_keywords = config.get("exclude_keywords") or ""
            self._transfer_type = config.get("transfer_type") or "link"

        # 停止现有任务
        self.stop_service()

        if self._enabled or self._onlyonce:
            # 定时服务
            self._scheduler = BackgroundScheduler(timezone=settings.TZ)
            if self._notify:
                # 追加入库消息统一发送服务
                self._scheduler.add_job(self.send_msg, trigger='interval', seconds=30)

            # 读取目录配置
            monitor_confs = str(self._monitor_confs or "").split("\n")
            if not monitor_confs:
                return
            for monitor_conf in monitor_confs:
                # 格式 监控方式#监控目录#目的目录#是否重命名#封面比例
                if not monitor_conf:
                    continue
                if str(monitor_conf).count("#") != 4:
                    logger.error(f"{monitor_conf} 格式错误")
                    continue
                conf_parts = str(monitor_conf).split("#")
                mode = conf_parts[0].strip()
                source_dir = conf_parts[1].strip()
                target_dir = conf_parts[2].strip()
                rename_conf = conf_parts[3].strip()
                cover_conf = conf_parts[4].strip()

                source_dir = source_dir if source_dir == "/" else source_dir.rstrip("/")
                target_dir = target_dir if target_dir == "/" else target_dir.rstrip("/")
                if not source_dir or not target_dir:
                    logger.error(f"{monitor_conf} 格式错误：监控目录和目的目录不能为空")
                    self.systemmessage.put("儿童刮削监控配置错误：监控目录和目的目录不能为空")
                    continue
                target_dir_path = Path(target_dir)
                target_dir_root = target_dir_path.resolve(strict=False)
                if not target_dir_path.is_absolute() or target_dir_root == Path(target_dir_root.anchor):
                    logger.error(f"{monitor_conf} 格式错误：目的目录必须是非根目录的绝对路径")
                    self.systemmessage.put("儿童刮削监控配置错误：目的目录必须是非根目录的绝对路径")
                    continue

                # 存储目录监控配置
                self._dirconf[source_dir] = target_dir
                self._targetconf[target_dir] = source_dir
                self._renameconf[source_dir] = rename_conf
                self._coverconf[source_dir] = cover_conf
                if self._delete_sync:
                    self.__rebuild_link_index_async(source_dir=source_dir)

                # 启用目录监控
                if self._enabled:
                    # 检查媒体库目录是不是下载目录的子目录
                    try:
                        if target_dir and Path(target_dir).is_relative_to(Path(source_dir)):
                            logger.warn(f"{target_dir} 是下载目录 {source_dir} 的子目录，无法监控")
                            self.systemmessage.put(f"{target_dir} 是下载目录 {source_dir} 的子目录，无法监控")
                            continue
                    except Exception as e:
                        logger.debug(str(e))
                        pass

                    try:
                        if mode == "compatibility":
                            # 兼容模式，目录同步性能降低且NAS不能休眠，但可以兼容挂载的远程共享目录如SMB
                            observer = PollingObserver(timeout=10)
                        else:
                            # 内部处理系统操作类型选择最优解
                            observer = Observer(timeout=10)
                        self._observer.append(observer)
                        observer.schedule(FileMonitorHandler(source_dir, self, watch_role="source"),
                                          path=source_dir,
                                          recursive=True)
                        observer.daemon = True
                        observer.start()
                        logger.info(f"{source_dir} 的目录监控服务启动")
                    except Exception as e:
                        err_msg = str(e)
                        if "inotify" in err_msg and "reached" in err_msg:
                            logger.warn(
                                f"目录监控服务启动出现异常：{err_msg}，请在宿主机上（不是docker容器内）执行以下命令并重启："
                                + """
                                     echo fs.inotify.max_user_watches=524288 | sudo tee -a /etc/sysctl.conf
                                     echo fs.inotify.max_user_instances=524288 | sudo tee -a /etc/sysctl.conf
                                     sudo sysctl -p
                                     """)
                        else:
                            logger.error(f"{source_dir} 启动目录监控失败：{err_msg}")
                        self.systemmessage.put(f"{source_dir} 启动目录监控失败：{err_msg}")

                    try:
                        if not Path(target_dir).exists():
                            os.makedirs(target_dir, exist_ok=True)
                        if mode == "compatibility":
                            target_observer = PollingObserver(timeout=10)
                        else:
                            target_observer = Observer(timeout=10)
                        self._observer.append(target_observer)
                        target_observer.schedule(FileMonitorHandler(target_dir, self, watch_role="target"),
                                                 path=target_dir,
                                                 recursive=True)
                        target_observer.daemon = True
                        target_observer.start()
                        logger.info(f"{target_dir} 的目标目录监控服务启动")
                    except Exception as e:
                        err_msg = str(e)
                        logger.error(f"{target_dir} 启动目标目录监控失败：{err_msg}")
                        self.systemmessage.put(f"{target_dir} 启动目标目录监控失败：{err_msg}")

            # 运行一次定时服务
            if self._onlyonce:
                logger.info("儿童监控服务启动，立即运行一次")
                self._scheduler.add_job(func=self.sync_all, trigger='date',
                                        run_date=datetime.datetime.now(
                                            tz=pytz.timezone(settings.TZ)) + datetime.timedelta(seconds=3),
                                        name="儿童监控全量执行")
                # 关闭一次性开关
                self._onlyonce = False
                # 保存配置
                self.__update_config()

            # 启动任务；仅开启媒体库刷新时也要启动调度器，用于合并目录监控触发的刷新。
            if self._scheduler.get_jobs() or (self._enabled and self._refresh_mediaserver):
                self._scheduler.print_jobs()
                self._scheduler.start()

        if self._image:
            self._image = False
            self.__update_config()
            self.__handle_image()

    def sync_all(self):
        """
        立即运行一次，全量同步目录中所有文件
        """
        if self._syncing:
            logger.warn("儿童监控全量同步正在执行，跳过重复触发")
            return
        logger.info("开始全量同步儿童监控目录 ...")
        self._syncing = True
        try:
            # 遍历所有监控目录
            for mon_path in self._dirconf.keys():
                # 遍历目录下所有文件
                for file_path in SystemUtils.list_files(Path(mon_path), settings.RMT_MEDIAEXT):
                    self.__handle_file(is_directory=Path(file_path).is_dir(),
                                       event_path=str(file_path),
                                       source_dir=mon_path)
        finally:
            self._syncing = False
        logger.info("全量同步儿童监控目录完成！")
        self.__refresh_mediaserver_library()

    def __rebuild_link_index(self, source_dir: Optional[str] = None):
        """
        根据源目录重新建立源文件与目标硬链接的双向映射。
        """
        source_dirs = [source_dir] if source_dir else list(self._dirconf.keys())
        for mon_path in source_dirs:
            if not mon_path or not Path(mon_path).exists():
                continue
            for file_path in SystemUtils.list_files(Path(mon_path), settings.RMT_MEDIAEXT):
                target_path, _ = self.__build_target_path(event_path=str(file_path), source_dir=mon_path)
                if target_path:
                    self.__remember_link(source_path=str(file_path), target_path=target_path)

    def __rebuild_link_index_async(self, source_dir: Optional[str] = None):
        """
        后台重建删除联动索引，避免保存配置时同步扫描大目录导致接口长时间不返回。
        """
        thread = threading.Thread(target=self.__rebuild_link_index,
                                  kwargs={"source_dir": source_dir},
                                  name="ChildrenScraperLinkIndex",
                                  daemon=True)
        thread.start()

    def __remember_link(self, source_path: str, target_path: Path):
        """
        记录硬链接源路径和目标路径，供目标目录反向删除时使用。
        """
        source_file = self.__normalize_path_text(source_path)
        target_file = self.__normalize_path_text(target_path)
        source_dir = Path(source_file).parent.as_posix()
        target_dir = Path(target_file).parent.as_posix()
        self._source_target_file_map[source_file] = target_file
        self._target_source_file_map[target_file] = source_file
        self._source_target_dir_map[source_dir] = target_dir
        self._target_source_dir_map[target_dir] = source_dir

    def __forget_link(self, source_path: Optional[str] = None, target_path: Optional[str] = None):
        """
        删除已失效的路径映射。
        """
        if source_path:
            source_path = self.__normalize_path_text(source_path)
            target_path = self._source_target_file_map.pop(source_path, None) or target_path
        if target_path:
            target_path = self.__normalize_path_text(target_path)
            source_path = self._target_source_file_map.pop(target_path, None) or source_path
        if source_path:
            self._source_target_file_map.pop(self.__normalize_path_text(source_path), None)
        if target_path:
            self._target_source_file_map.pop(self.__normalize_path_text(target_path), None)

    def __find_target_dir_by_source_dir(self, source_path: str) -> Optional[str]:
        """
        查找源目录对应的目标目录，优先精确匹配，失败时按最长父目录匹配。
        """
        source_path = self.__normalize_path_text(source_path)
        if source_path in self._source_target_dir_map:
            return self._source_target_dir_map.get(source_path)
        for indexed_source, indexed_target in sorted(self._source_target_dir_map.items(),
                                                     key=lambda item: len(item[0]),
                                                     reverse=True):
            if indexed_source.startswith(f"{source_path}/") or source_path.startswith(f"{indexed_source}/"):
                return indexed_target
        return None

    def __find_source_dir_by_target_dir(self, target_path: str) -> Optional[str]:
        """
        查找目标目录对应的源目录，优先精确匹配，失败时按最长父目录匹配。
        """
        target_path = self.__normalize_path_text(target_path)
        if target_path in self._target_source_dir_map:
            return self._target_source_dir_map.get(target_path)
        for indexed_target, indexed_source in sorted(self._target_source_dir_map.items(),
                                                     key=lambda item: len(item[0]),
                                                     reverse=True):
            if indexed_target.startswith(f"{target_path}/") or target_path.startswith(f"{indexed_target}/"):
                return indexed_source
        return None

    def __handle_image(self):
        """
        立即运行一次，裁剪封面
        """
        if not self._dirconf or not self._dirconf.keys():
            logger.error("未正确配置，停止裁剪 ...")
            return

        logger.info("开始全量裁剪封面 ...")
        # 遍历所有监控目录
        for mon_path in self._dirconf.keys():
            cover_conf = self._coverconf.get(mon_path)
            target_path = self._dirconf.get(mon_path)
            # 遍历目录下所有文件
            for file_path in SystemUtils.list_files(Path(target_path), ["poster.jpg"]):
                try:
                    if Path(file_path).name != "poster.jpg":
                        continue
                    image = Image.open(file_path)
                    if image.width / image.height != int(str(cover_conf).split(":")[0]) / int(
                            str(cover_conf).split(":")[1]):
                        self.__save_poster(input_path=file_path,
                                           poster_path=file_path,
                                           cover_conf=cover_conf)
                        logger.info(f"封面 {file_path} 已裁剪 比例为 {cover_conf}")
                except Exception:
                    continue
        logger.info("全量裁剪封面完成！")

    def event_handler(self, event, source_dir: str, event_path: str, watch_role: str = "source"):
        """
        处理文件变化
        :param event: 事件
        :param source_dir: 监控目录
        :param event_path: 事件文件路径
        """
        # 回收站及隐藏的文件不处理
        if (event_path.find("/@Recycle") != -1
                or event_path.find("/#recycle") != -1
                or event_path.find("/.") != -1
                or event_path.find("/@eaDir") != -1):
            logger.info(f"{event_path} 是回收站或隐藏的文件，跳过处理")
            return

        # 命中过滤关键字不处理
        if self._exclude_keywords:
            for keyword in self._exclude_keywords.split("\n"):
                if keyword and re.findall(keyword, event_path):
                    logger.info(f"{event_path} 命中过滤关键字 {keyword}，不处理")
                    return

        # 目标目录只处理删除事件，避免硬链接生成后被反向当作新增源文件处理
        if watch_role == "target":
            if event.event_type == "deleted":
                self.__handle_deleted_target(is_directory=event.is_directory,
                                             event_path=event_path,
                                             target_dir=source_dir)
            return

        # 源目录删除文件夹时也需要处理整部剧联动删除
        if event.event_type == "deleted" and event.is_directory:
            self.__handle_deleted_source_dir(event_path=event_path,
                                             source_dir=source_dir)
            return

        # 不是媒体文件不处理
        if Path(event_path).suffix not in settings.RMT_MEDIAEXT:
            logger.debug(f"{event_path} 不是媒体文件")
            return

        # 文件发生变化
        logger.debug(f"变动类型 {event.event_type} 变动路径 {event_path}")
        if event.event_type == "deleted":
            self.__handle_deleted_file(is_directory=event.is_directory,
                                       event_path=event_path,
                                       source_dir=source_dir)
            return

        self.__handle_file(is_directory=event.is_directory,
                           event_path=event_path,
                           source_dir=source_dir)

    def __build_target_path(self, event_path: str, source_dir: str) -> Tuple[Optional[Path], Optional[str]]:
        """
        根据监控配置计算源文件对应的目标硬链接路径。
        """
        dest_dir = self._dirconf.get(source_dir)
        rename_conf = self._renameconf.get(source_dir)
        if not dest_dir or str(dest_dir).strip() == "/" or not str(dest_dir).strip():
            logger.error(f"{source_dir} 对应的目的目录为空或无效，无法计算联动删除目标")
            return None, None

        dest_dir = str(dest_dir).strip()
        dest_dir = dest_dir if dest_dir == "/" else dest_dir.rstrip("/")
        dest_root = Path(dest_dir).resolve(strict=False)
        if not Path(dest_dir).is_absolute() or dest_root == Path(dest_root.anchor):
            logger.error(f"{source_dir} 对应的目的目录 {dest_dir} 无效，无法计算联动删除目标")
            return None, None

        target_path = event_path.replace(source_dir, dest_dir)
        title = None
        try:
            if str(rename_conf) == "true" or str(rename_conf) == "false":
                rel_target = Path(target_path).resolve(strict=False).relative_to(dest_root)
                parent = rel_target.parent
                last = Path(rel_target.name)
                if str(rename_conf).lower() == "true":
                    title = self.__resolve_series_title(event_path=event_path,
                                                        source_dir=source_dir,
                                                        parent_name=Path(parent).name)
                    target_path = dest_root / title / last
                else:
                    title = str(parent)
            elif str(rename_conf) == "smart":
                rel_target = Path(target_path).resolve(strict=False).relative_to(dest_root)
                parent = rel_target.parent
                last = Path(rel_target.name)
                title = self.__resolve_series_title(event_path=event_path,
                                                    source_dir=source_dir,
                                                    parent_name=Path(parent).name)
                target_path = dest_root / title / last
            else:
                logger.error(f"{target_path} 智能重命名失败，无法计算联动删除目标")
                return None, None

            target_path = Path(target_path)
            if not target_path.resolve(strict=False).is_relative_to(dest_root):
                logger.error(f"目标路径 {target_path} 不在目的目录 {dest_dir} 下，跳过联动删除")
                return None, None

            pattern = r'S\d+E\d+'
            matches = re.search(pattern, target_path.name)
            if matches:
                target_path = self.__apply_season_layout(target_path)
            if not target_path.resolve(strict=False).is_relative_to(dest_root):
                logger.error(f"目标路径 {target_path} 不在目的目录 {dest_dir} 下，跳过联动删除")
                return None, None
            return target_path, title
        except Exception as e:
            logger.error(f"计算联动删除目标失败：{event_path} - {e}")
            return None, None

    @staticmethod
    def __get_source_lookup_title(event_path: str, source_dir: str) -> str:
        """
        获取源下载侧的种子目录名，用于匹配 PT Depiler 写入的站点元数据。
        PT Depiler 可能会按站点分类创建一级目录，如 儿童/Piggo/种子目录/文件.mp4，
        因此不能直接取监控目录下一层，需要取离视频最近的有效父目录。
        """
        try:
            rel_path = Path(event_path).resolve(strict=False).relative_to(Path(source_dir).resolve(strict=False))
            parents = list(rel_path.parts[:-1])
            while parents and re.fullmatch(r"(season[\s._-]*\d+|s\d+)", str(parents[-1]), re.I):
                parents.pop()
            if parents:
                return str(parents[-1]).strip()
            return str(rel_path.stem or rel_path.name).strip()
        except Exception:
            path = Path(event_path)
            return str(path.parent.name or path.stem or path.name).strip()

    def __resolve_series_title(self,
                               event_path: str,
                               source_dir: str,
                               parent_name: str = None,
                               file_meta: Any = None) -> str:
        """
        生成剧名目录：优先用 MetaInfoPath/MetaInfo 的本地解析结果，
        失败时回退到源目录/种子名的轻量清理结果，避免硬链接命名依赖 TMDB 识别。
        """
        source_lookup_title = self.__get_source_lookup_title(event_path=event_path,
                                                             source_dir=source_dir)
        cache_key = f"{source_dir}|{source_lookup_title or parent_name or Path(event_path).parent.name}"
        if cache_key in self._title_cache:
            return self._title_cache[cache_key]

        candidates = []

        def add_candidate(value: Any, source: str = ""):
            title = self.__clean_series_title_candidate(value)
            if title:
                candidates.append((title, source))

        # MoviePilot 的 MetaInfoPath 会合并文件名、上级目录和上上级目录，比简单 split 更稳。
        try:
            path_meta = file_meta or MetaInfoPath(Path(event_path))
            for attr in ("name", "cn_name", "en_name", "original_name"):
                add_candidate(getattr(path_meta, attr, None), f"metapath.{attr}")
        except Exception as e:
            logger.debug(f"MetaInfoPath 识别剧名失败：{event_path} - {e}")

        for raw_title in [source_lookup_title, parent_name, Path(event_path).parent.name]:
            raw_title = self.__strip_leading_media_tags(raw_title)
            if not raw_title:
                continue
            try:
                prepared_title, _ = WordsMatcher().prepare(str(raw_title))
                add_candidate(prepared_title, "wordsmatcher")
            except Exception:
                pass
            try:
                meta = MetaInfo(str(raw_title))
                for attr in ("name", "cn_name", "en_name", "original_name"):
                    add_candidate(getattr(meta, attr, None), f"metainfo.{attr}")
            except Exception:
                pass

        for title, source in candidates:
            if self.__is_usable_series_title(title):
                logger.debug(f"剧名识别：{source_lookup_title} -> {title} ({source})")
                self._title_cache[cache_key] = title
                return title

        fallback = self.__fallback_series_title_from_text(source_lookup_title or parent_name or Path(event_path).parent.name)
        self._title_cache[cache_key] = fallback
        return fallback

    def __clean_series_title_candidate(self, title: Any) -> str:
        """
        清理候选剧名，去掉语言标签、季号和路径非法字符。
        """
        title = str(title or "").strip().strip("/\\")
        if not title:
            return ""
        title = self.__strip_leading_media_tags(title)
        title = re.sub(r"[\\/:*?\"<>|]+", " ", title)
        title = re.sub(r"\s+", " ", title).strip()
        return self.__normalize_series_title(title)

    def __is_usable_series_title(self, title: Any) -> bool:
        """
        判断候选是否像真实剧名，而不是语言标签、站点分类或资源标题残片。
        """
        title = str(title or "").strip()
        if not title:
            return False
        if re.fullmatch(r"(piggo|qingwa|hxpt|好学|猪猪|pter|pterclub|pt)", title, re.I):
            return False
        media_tag_pattern = (
            r"国语|国配|中文|中配|台配|粤语|粤配|英语|英文|日语|韩语|"
            r"普通话|中字|中文字幕|双语|国英双语|国粤双语|国语中字|粤语中字"
        )
        if re.fullmatch(media_tag_pattern, title, re.I):
            return False
        release_markers = (
            r"\b(?:S\d{1,2}E\d{1,4}|2160p|1080p|720p|WEB[-_. ]?DL|BluRay|"
            r"H\.?26[45]|HEVC|AVC|AAC|AC3|DDP|PigoWeb|FROGWeb|PTerWEB|Complete)\b"
        )
        if re.search(release_markers, title, re.I):
            return False
        return len(title) >= 2

    def __fallback_series_title_from_text(self, title: Any) -> str:
        """
        最后兜底：从原始种子/目录名中切掉季号、年份、分辨率等资源字段。
        """
        title = self.__strip_leading_media_tags(title)
        title = str(title or "").strip().strip("/\\")
        if not title:
            return "未知儿童剧"
        if Path(title).suffix.lower() in settings.RMT_MEDIAEXT:
            title = Path(title).stem
        first_dot_part = title.split(".")[0].strip()
        if re.search(r"[\u4e00-\u9fff]", first_dot_part) and len(first_dot_part) >= 2:
            return self.__normalize_series_title(first_dot_part)
        title = re.split(r"[\s._-]+S\d{1,2}(?:E\d{1,4})?\b", title, maxsplit=1, flags=re.I)[0]
        title = re.split(r"[\s._-]+(?:19|20)\d{2}\b", title, maxsplit=1)[0]
        title = re.split(r"[\s._-]+(?:2160p|1080p|720p|WEB[-_. ]?DL|BluRay|H\.?26[45]|HEVC|AAC|PigoWeb|FROGWeb)\b",
                         title,
                         maxsplit=1,
                         flags=re.I)[0]
        title = re.sub(r"[._]+", " ", title)
        title = re.sub(r"\s+", " ", title).strip()
        return self.__normalize_series_title(title) or "未知儿童剧"

    @staticmethod
    def __normalize_series_title(title: Any) -> str:
        """
        归一化目标剧名目录，避免同一剧因源目录带“第一季/S01”被拆成多部剧。
        """
        title = str(title or "").strip().strip("/\\")
        if not title:
            return title
        title = title.strip("[]【】()（） ")
        title = re.sub(r"[\s._-]*(?:Season|Series)[\s._-]*\d{1,2}$", "", title, flags=re.I)
        title = re.sub(r"[\s._-]*S\d{1,2}$", "", title, flags=re.I)
        title = re.sub(r"[\s._-]*第[零〇一二三四五六七八九十百两\d]+[季部辑]$", "", title)
        return title.strip().strip("/\\")

    @staticmethod
    def __strip_leading_media_tags(title: Any) -> str:
        """
        去掉源目录开头的语言/版本标签，避免 [国语].xxx 被识别成“国语”。
        只处理明确的媒体标签，不删除 [米奇妙妙屋] 这类可能是真剧名的标签。
        """
        title = str(title or "").strip()
        if not title:
            return title
        tag_pattern = (
            r"国语|国配|中文|中配|台配|粤语|粤配|英语|英文|日语|韩语|"
            r"普通话|中字|中文字幕|双语|国英双语|国粤双语|国语中字|粤语中字"
        )
        while True:
            new_title = re.sub(rf"^\s*[\[【(（]\s*(?:{tag_pattern})\s*[\]】)）][\s._-]*", "", title, flags=re.I)
            if new_title == title:
                return title
            title = new_title.strip()

    def __fallback_tag_title(self, title: Any, parent_name: str) -> str:
        """
        WordsMatcher 如果把语言标签识别成标题，则回退到清理后的父目录名。
        """
        title = self.__normalize_series_title(title)
        cleaned_parent = self.__strip_leading_media_tags(parent_name)
        media_tag_pattern = (
            r"国语|国配|中文|中配|台配|粤语|粤配|英语|英文|日语|韩语|"
            r"普通话|中字|中文字幕|双语|国英双语|国粤双语|国语中字|粤语中字"
        )
        if title and not re.fullmatch(media_tag_pattern, str(title), re.I):
            return title
        fallback = self.__normalize_series_title(cleaned_parent.split(".")[0])
        return fallback or title

    @staticmethod
    def __apply_season_layout(target_path: Path) -> Path:
        """
        把目标文件统一整理到 剧名/Season 01/原始发布文件名。
        文件名保留分辨率、编码和发布组信息，便于在媒体库中区分来源版本。
        """
        match = re.search(r"S(\d{1,2})E(\d{1,4})", target_path.name, re.I)
        if not match:
            return target_path
        season = int(match.group(1))
        episode_name = target_path.name
        season_dir = f"Season {season:02d}"
        parent = target_path.parent
        if re.fullmatch(r"Season\s+\d{1,2}", parent.name, re.I):
            if parent.name.lower() == season_dir.lower():
                return parent / episode_name
            return parent.parent / season_dir / episode_name
        return parent / season_dir / episode_name

    @staticmethod
    def __get_series_dir(target_path: Path) -> Path:
        """
        获取剧集根目录，Season 目录下的媒体文件返回上一层。
        """
        parent = Path(target_path).parent
        if re.fullmatch(r"Season\s+\d{1,2}", parent.name, re.I):
            return parent.parent
        return parent

    @staticmethod
    def __normalize_path_text(path: Any) -> str:
        return Path(str(path)).as_posix().rstrip("/")

    @staticmethod
    def __replace_path_prefix(path: Any, source: str, target: str) -> Optional[str]:
        if not source or not target:
            return None
        path_text = Path(str(path)).as_posix()
        source_path = Path(str(source).strip()).as_posix().rstrip("/")
        target_path = Path(str(target).strip()).as_posix().rstrip("/")
        if path_text == source_path:
            return target_path
        source_prefix = f"{source_path}/"
        if path_text.startswith(source_prefix):
            suffix = path_text[len(source_prefix):]
            return (Path(target_path) / suffix).as_posix()
        return None

    def __normalize_downloader_return_path(self, path: Any, downloader_config: Any) -> str:
        """
        把下载器返回路径按 MP 下载器路径映射反转为容器可见路径。
        """
        normalized_path = Path(str(path)).as_posix()
        path_mapping = getattr(downloader_config, "path_mapping", None)
        if path_mapping:
            for storage_path, download_path in path_mapping:
                mapped_path = self.__replace_path_prefix(normalized_path, download_path, storage_path)
                if mapped_path:
                    normalized_path = mapped_path
                    break
        return normalized_path.rstrip("/")

    @staticmethod
    def __paths_related(left: str, right: str) -> bool:
        left = Path(left).as_posix().rstrip("/")
        right = Path(right).as_posix().rstrip("/")
        return left == right or left.startswith(f"{right}/") or right.startswith(f"{left}/")

    def __torrent_matches_path(self, server: Any, torrent: Any, source_path: str, downloader_config: Any) -> bool:
        """
        判断 qB torrent 是否包含被删除的源文件路径。
        """
        torrent_hash = torrent.get("hash")
        save_path = torrent.get("save_path")
        content_path = torrent.get("content_path")
        name = torrent.get("name")
        candidates = []
        if content_path:
            candidates.append(content_path)
        if save_path and name:
            candidates.append(Path(save_path) / name)

        for candidate in candidates:
            normalized = self.__normalize_downloader_return_path(candidate, downloader_config)
            if self.__paths_related(source_path, normalized):
                return True

        if not torrent_hash:
            return False
        torrent_files = server.get_files(tid=torrent_hash)
        if not torrent_files:
            return False
        for torrent_file in torrent_files:
            file_name = torrent_file.get("name")
            if not file_name:
                continue
            if save_path:
                candidate = Path(save_path) / file_name
                normalized = self.__normalize_downloader_return_path(candidate, downloader_config)
                if self.__paths_related(source_path, normalized):
                    return True
            if content_path:
                candidate = Path(content_path).parent / file_name
                normalized = self.__normalize_downloader_return_path(candidate, downloader_config)
                if self.__paths_related(source_path, normalized):
                    return True
        return False

    def __delete_downloader_record(self, source_path: str, source_is_dir: bool = False):
        """
        按源文件路径查找并删除所选 qB 下载器中的任务记录，不删除下载文件。
        """
        if not self._delete_downloaders:
            logger.warn("已开启删除联动，但未选择下载器，跳过 qB 下载记录删除")
            return
        try:
            source_path = self.__normalize_path_text(source_path)
            source_parent = source_path if source_is_dir else Path(source_path).parent.as_posix()

            with delete_record_lock:
                now = datetime.datetime.now().timestamp()
                for downloader in self._delete_downloaders:
                    cache_key = f"{downloader}|{source_parent}"
                    cache_info = self._delete_record_cache.get(cache_key)
                    if cache_info and now - cache_info.get("time", 0) < 600:
                        status = cache_info.get("status")
                        if status == "deleted":
                            logger.debug(f"qB 下载记录已在本轮删除过，跳过重复查询：{downloader} {source_parent}")
                            continue
                        if status == "miss":
                            logger.debug(f"qB 下载记录本轮已确认未匹配，跳过重复查询：{downloader} {source_parent}")
                            continue

                    service = DownloaderHelper().get_service(name=downloader, type_filter="qbittorrent")
                    if not service:
                        logger.warn(f"未找到 qB 下载器：{downloader}，跳过下载记录删除")
                        continue
                    server = service.instance

                    torrents, error = server.get_torrents(tags=None)
                    if error:
                        logger.error(f"获取 qB 下载器 {downloader} 种子列表失败，跳过下载记录删除")
                        continue
                    deleted_hashes = []
                    for torrent in torrents:
                        torrent_hash = torrent.get("hash")
                        if not torrent_hash:
                            continue
                        if self.__torrent_matches_path(server=server,
                                                       torrent=torrent,
                                                       source_path=source_path,
                                                       downloader_config=service.config):
                            if server.delete_torrents(delete_file=False, ids=torrent_hash):
                                deleted_hashes.append(torrent_hash)
                                logger.warn(f"检测到源文件删除，已删除 qB 下载记录（不删文件）：{downloader} {torrent_hash} {torrent.get('name')}")
                            else:
                                logger.error(f"删除 qB 下载记录失败：{downloader} {torrent_hash} {torrent.get('name')}")
                    if deleted_hashes:
                        self._delete_record_cache[cache_key] = {
                            "time": now,
                            "status": "deleted",
                            "hashes": deleted_hashes
                        }
                        continue

                    self._delete_record_cache[cache_key] = {
                        "time": now,
                        "status": "miss"
                    }
                    logger.info(f"未在 qB 下载器 {downloader} 找到源文件对应任务：{source_path}")
        except Exception as e:
            logger.error(f"删除 qB 下载记录失败：{source_path} - {e}")

    def __is_under_root(self, path: str, roots: List[str]) -> bool:
        try:
            check_path = Path(path).resolve(strict=False)
            for root in roots:
                root_path = Path(root).resolve(strict=False)
                if check_path != root_path and check_path.is_relative_to(root_path):
                    return True
        except Exception as e:
            logger.error(f"路径安全校验失败：{path} - {e}")
        return False

    def __delete_path(self, path: str, roots: List[str], reason: str) -> bool:
        """
        在限定根目录内删除文件或文件夹。
        """
        path = self.__normalize_path_text(path)
        if not path or path == "/" or not self.__is_under_root(path, roots):
            logger.error(f"{reason} 路径 {path} 不在允许目录内，跳过删除")
            return False
        try:
            path_obj = Path(path)
            if not path_obj.exists():
                logger.debug(f"{reason} 路径不存在，跳过：{path}")
                return False
            if path_obj.is_dir():
                shutil.rmtree(path_obj)
                logger.warn(f"{reason}，已删除文件夹：{path}")
            else:
                path_obj.unlink()
                logger.warn(f"{reason}，已删除文件：{path}")
            return True
        except Exception as e:
            logger.error(f"{reason} 删除失败：{path} - {e}")
            return False

    def __handle_deleted_source_dir(self, event_path: str, source_dir: str):
        """
        源目录整部剧被删除时，同步删除目标目录并删除 qB 记录。
        """
        if not self._delete_sync:
            logger.debug(f"删除联动未开启，忽略源目录删除事件：{event_path}")
            return
        event_path = self.__normalize_path_text(event_path)
        if event_path == self.__normalize_path_text(source_dir):
            logger.warn(f"检测到源监控根目录删除，跳过联动删除：{event_path}")
            return
        target_dir = self.__find_target_dir_by_source_dir(event_path)
        if target_dir:
            self.__delete_path(path=target_dir,
                               roots=list(self._targetconf.keys()),
                               reason="源目录已删除，联动删除目标目录")
        else:
            logger.warn(f"源目录已删除，但未找到对应目标目录：{event_path}")
        self.__delete_downloader_record(source_path=event_path, source_is_dir=True)

    def __handle_deleted_target(self, is_directory: bool, event_path: str, target_dir: str):
        """
        目标目录删除时反向删除源文件/源目录，并按整部剧目录删除 qB 记录。
        """
        if not self._delete_sync:
            logger.debug(f"删除联动未开启，忽略目标删除事件：{event_path}")
            return
        event_path = self.__normalize_path_text(event_path)
        if event_path == self.__normalize_path_text(target_dir):
            logger.warn(f"检测到目标监控根目录删除，跳过联动删除：{event_path}")
            return
        if is_directory:
            source_path = self.__find_source_dir_by_target_dir(event_path)
            if not source_path:
                logger.warn(f"目标目录已删除，但未找到对应源目录：{event_path}")
                return
            self.__delete_path(path=source_path,
                               roots=list(self._dirconf.keys()),
                               reason="目标目录已删除，反向删除源目录")
            self.__delete_downloader_record(source_path=source_path, source_is_dir=True)
            return

        if Path(event_path).suffix not in settings.RMT_MEDIAEXT:
            logger.debug(f"{event_path} 不是媒体文件")
            return
        source_path = self._target_source_file_map.get(event_path)
        if not source_path:
            self.__rebuild_link_index()
            source_path = self._target_source_file_map.get(event_path)
        if not source_path:
            logger.warn(f"目标文件已删除，但未找到对应源文件：{event_path}")
            return
        self.__delete_path(path=source_path,
                           roots=list(self._dirconf.keys()),
                           reason="目标文件已删除，反向删除源文件")
        self.__delete_downloader_record(source_path=source_path)
        self.__forget_link(source_path=source_path, target_path=event_path)

    def __handle_deleted_file(self, is_directory: bool, event_path: str, source_dir: str):
        """
        源文件删除时同步删除目标硬链接，并按所选 qB 下载器删除任务记录。
        """
        if not self._delete_sync:
            logger.debug(f"删除联动未开启，忽略删除事件：{event_path}")
            return
        if is_directory:
            logger.debug(f"{event_path} 是目录删除事件，跳过；文件删除事件会单独处理")
            return

        target_path, _ = self.__build_target_path(event_path=event_path, source_dir=source_dir)
        if target_path and target_path.exists():
            try:
                target_path.unlink()
                logger.warn(f"源文件已删除，联动删除硬链接：{target_path}")
            except Exception as e:
                logger.error(f"联动删除硬链接失败：{target_path} - {e}")
        elif target_path:
            logger.debug(f"源文件已删除，目标硬链接不存在，跳过：{target_path}")

        self.__delete_downloader_record(source_path=event_path)
        if target_path:
            self.__forget_link(source_path=event_path, target_path=str(target_path))

    def __handle_file(self, is_directory: bool, event_path: str, source_dir: str):
        """
        同步一个文件
        :event.is_directory
        :param event_path: 事件文件路径
        :param source_dir: 监控目录
        """
        try:
            # 转移路径
            dest_dir = self._dirconf.get(source_dir)
            # 是否重命名
            rename_conf = self._renameconf.get(source_dir)
            # 封面比例
            cover_conf = self._coverconf.get(source_dir)
            if not dest_dir or str(dest_dir).strip() == "/" or not str(dest_dir).strip():
                logger.error(f"{source_dir} 对应的目的目录为空或无效，跳过硬链接；请检查监控目录配置第三段")
                return
            dest_dir = str(dest_dir).strip()
            dest_dir = dest_dir if dest_dir == "/" else dest_dir.rstrip("/")
            dest_root = Path(dest_dir).resolve(strict=False)
            if not Path(dest_dir).is_absolute() or dest_root == Path(dest_root.anchor):
                logger.error(f"{source_dir} 对应的目的目录 {dest_dir} 无效，跳过硬链接；目的目录必须是非根目录的绝对路径")
                return
            # 元数据
            file_meta = MetaInfoPath(Path(event_path))
            if not file_meta.name:
                logger.error(f"{Path(event_path).name} 无法识别有效信息")
                return
            mediainfo = None
            transfer_flag = False
            title = None
            target_path = None
            source_lookup_title = self.__get_source_lookup_title(event_path=event_path,
                                                                 source_dir=source_dir)
            if not transfer_flag:
                target_path = event_path.replace(source_dir, dest_dir)

                # 目录重命名
                if str(rename_conf) == "true" or str(rename_conf) == "false":
                    rename_conf = str(rename_conf).lower() == "true"
                    rel_target = Path(target_path).resolve(strict=False).relative_to(dest_root)
                    parent = rel_target.parent
                    last = Path(rel_target.name)
                    if rename_conf:
                        title = self.__resolve_series_title(event_path=event_path,
                                                            source_dir=source_dir,
                                                            parent_name=Path(parent).name,
                                                            file_meta=file_meta)
                        target_path = dest_root / title / last
                    else:
                        title = parent
                else:
                    if str(rename_conf) == "smart":
                        rel_target = Path(target_path).resolve(strict=False).relative_to(dest_root)
                        parent = rel_target.parent
                        last = Path(rel_target.name)
                        title = self.__resolve_series_title(event_path=event_path,
                                                            source_dir=source_dir,
                                                            parent_name=Path(parent).name,
                                                            file_meta=file_meta)
                        target_path = dest_root / title / last
                    else:
                        logger.error(f"{target_path} 智能重命名失败")
                        return

                # 文件夹同步创建
                target_path = Path(target_path)
                try:
                    if not target_path.resolve(strict=False).is_relative_to(dest_root):
                        logger.error(f"目标路径 {target_path} 不在目的目录 {dest_dir} 下，跳过硬链接；请检查监控目录配置")
                        return
                except Exception as e:
                    logger.error(f"目标路径 {target_path} 校验失败，跳过硬链接：{e}")
                    return

                if is_directory:
                    # 目标文件夹不存在则创建
                    if not target_path.exists():
                        logger.info(f"创建目标文件夹 {target_path}")
                        os.makedirs(target_path, exist_ok=True)
                else:
                    # 媒体重命名
                    try:
                        pattern = r'S\d+E\d+'
                        matches = re.search(pattern, Path(target_path).name)
                        if matches:
                            target_path = self.__apply_season_layout(Path(target_path))
                        else:
                            print("未找到匹配的季数和集数")
                    except Exception as e:
                        print(e)

                    try:
                        if not Path(target_path).resolve(strict=False).is_relative_to(dest_root):
                            logger.error(f"目标路径 {target_path} 不在目的目录 {dest_dir} 下，跳过硬链接；请检查监控目录配置")
                            return
                    except Exception as e:
                        logger.error(f"目标路径 {target_path} 校验失败，跳过硬链接：{e}")
                        return

                    # 目标文件夹不存在则创建
                    if not Path(target_path).parent.exists():
                        logger.info(f"创建目标文件夹 {Path(target_path).parent}")
                        os.makedirs(Path(target_path).parent, exist_ok=True)

                    # 文件：nfo、图片、视频文件
                    if Path(target_path).exists():
                        logger.debug(f"目标文件 {target_path} 已存在")
                        self.__ensure_series_metadata(target_path=target_path,
                                                      title=title,
                                                      source_title=source_lookup_title,
                                                      rename_conf=rename_conf,
                                                      cover_conf=cover_conf)
                        self.__schedule_mediaserver_refresh(target_path=target_path, title=title)
                        return

                    # 硬链接
                    retcode = self.__transfer_command(file_item=Path(event_path),
                                                      target_file=target_path,
                                                      transfer_type=self._transfer_type)
                    if retcode == 0:
                        logger.info(f"文件 {event_path} 硬链接到 {target_path} 完成")
                        self.__remember_link(source_path=event_path, target_path=target_path)
                        series_dir = self.__get_series_dir(target_path)
                        # 生成 tvshow.nfo
                        if not (series_dir / "tvshow.nfo").exists():
                            self.__gen_tv_nfo_file(dir_path=series_dir,
                                                   title=title)

                        # 生成儿童封面
                        if not (series_dir / "poster.jpg").exists():
                            thumb_path = self.gen_file_thumb(title=title,
                                                             source_title=source_lookup_title,
                                                             rename_conf=rename_conf,
                                                             file_path=target_path)
                            if thumb_path and Path(thumb_path).exists():
                                self.__save_poster(input_path=thumb_path,
                                                   poster_path=series_dir / "poster.jpg",
                                                   cover_conf=cover_conf)
                                thumb_path.unlink()
                            else:
                                # 检查是否有缩略图
                                thumb_files = SystemUtils.list_files(directory=series_dir,
                                                                     extensions=[".jpg"])
                                if thumb_files:
                                    # 生成poster
                                    for thumb in thumb_files:
                                        self.__save_poster(input_path=thumb,
                                                           poster_path=series_dir / "poster.jpg",
                                                           cover_conf=cover_conf)
                                        break
                                    # 删除多余jpg
                                    for thumb in thumb_files:
                                        Path(thumb).unlink()
                        self.__schedule_mediaserver_refresh(target_path=target_path, title=title)
                    else:
                        logger.error(f"文件 {event_path} 硬链接到 {target_path} 失败，错误码：{retcode}")
            if self._notify:
                # 发送消息汇总
                media_list = self._medias.get(mediainfo.title_year if mediainfo else title) or {}
                target_dir = None
                if "target_path" in locals() and target_path:
                    try:
                        target_dir = str(self.__get_series_dir(Path(target_path)) if not is_directory else Path(target_path))
                    except Exception:
                        target_dir = None
                if media_list:
                    media_files = media_list.get("files") or []
                    if media_files:
                        if str(event_path) not in media_files:
                            media_files.append(str(event_path))
                    else:
                        media_files = [str(event_path)]
                    media_list = {
                        "files": media_files,
                        "time": datetime.datetime.now(),
                        "target_dir": media_list.get("target_dir") or target_dir,
                        "image": media_list.get("image") or self._notify_image_urls.get(target_dir)
                    }
                else:
                    media_list = {
                        "files": [str(event_path)],
                        "time": datetime.datetime.now(),
                        "target_dir": target_dir,
                        "image": self._notify_image_urls.get(target_dir)
                    }
                self._medias[mediainfo.title_year if mediainfo else title] = media_list
        except Exception as e:
            logger.error(f"event_handler_created error: {e}")
            print(str(e))

    def send_msg(self):
        """
        定时检查是否有媒体处理完，发送统一消息
        """
        if self._notify:
            if not self._medias or not self._medias.keys():
                return

            # 遍历检查是否已刮削完，发送消息
            for medis_title_year in list(self._medias.keys()):
                media_list = self._medias.get(medis_title_year)
                logger.info(f"开始处理媒体 {medis_title_year} 消息")

                if not media_list:
                    continue

                # 获取最后更新时间
                last_update_time = media_list.get("time")
                media_files = media_list.get("files")
                if not last_update_time or not media_files:
                    continue

                # 判断剧集最后更新时间距现在是否已超过入库消息延迟，超过后发送消息
                if (datetime.datetime.now() - last_update_time).total_seconds() > int(self._interval):
                    series_dir = None
                    if media_list.get("target_dir"):
                        series_dir = Path(media_list.get("target_dir"))
                    plot = self.__read_nfo_plot(series_dir) if series_dir else None
                    text = "类别：儿童"
                    if plot:
                        text = f"{text}\n简介：{plot}"
                    image = media_list.get("image")
                    # 发送消息
                    message_kwargs = {
                        "mtype": NotificationType.Organize,
                        "title": f"{medis_title_year} 共{len(media_files)}集已入库",
                        "text": text
                    }
                    if image:
                        message_kwargs["image"] = image
                    self.post_message(**message_kwargs)
                    # 发送完消息，移出key
                    del self._medias[medis_title_year]
                    continue

    @staticmethod
    def __transfer_command(file_item: Path, target_file: Path, transfer_type: str) -> int:
        """
        使用系统命令处理单个文件
        :param file_item: 文件路径
        :param target_file: 目标文件路径
        :param transfer_type: RmtMode转移方式
        """
        with lock:
            if Path(target_file).exists():
                logger.debug(f"目标文件 {target_file} 已存在，跳过转移")
                return 0

            # 转移
            if transfer_type == 'link':
                # 硬链接
                retcode, retmsg = SystemUtils.link(file_item, target_file)
            elif transfer_type == 'softlink':
                # 软链接
                retcode, retmsg = SystemUtils.softlink(file_item, target_file)
            elif transfer_type == 'move':
                # 移动
                retcode, retmsg = SystemUtils.move(file_item, target_file)
            else:
                # 复制
                retcode, retmsg = SystemUtils.copy(file_item, target_file)

        if retcode != 0:
            logger.error(retmsg)

        return retcode

    def __save_poster(self, input_path, poster_path, cover_conf):
        """
        保存图片做封面；仅在开启封面裁剪时按配置比例裁剪。
        """
        try:
            if not self._image:
                if Path(input_path).resolve() != Path(poster_path).resolve():
                    shutil.copyfile(input_path, poster_path)
                return

            image = Image.open(input_path)

            # 需要截取的长宽比（比如 16:9）
            if not cover_conf:
                target_ratio = 2 / 3
            else:
                covers = cover_conf.split(":")
                target_ratio = int(covers[0]) / int(covers[1])

            # 获取原始图片的长宽比
            original_ratio = image.width / image.height

            # 计算截取后的大小
            if original_ratio > target_ratio:
                new_height = image.height
                new_width = int(new_height * target_ratio)
            else:
                new_width = image.width
                new_height = int(new_width / target_ratio)

            # 计算截取的位置
            left = (image.width - new_width) // 2
            top = (image.height - new_height) // 2
            right = left + new_width
            bottom = top + new_height

            # 截取图片
            cropped_image = image.crop((left, top, right, bottom))

            # 保存截取后的图片
            cropped_image.save(poster_path)
        except Exception as e:
            print(str(e))

    @staticmethod
    def __set_nfo_text_node(doc, root, tag_name: str, value: str):
        """
        设置或新增 NFO 文本节点。
        """
        nodes = root.getElementsByTagName(tag_name)
        if nodes:
            node = nodes[0]
            while node.firstChild:
                node.removeChild(node.firstChild)
        else:
            node = doc.createElement(tag_name)
            root.appendChild(node)
        node.appendChild(doc.createTextNode(value))

    def __gen_tv_nfo_file(self, dir_path: Path, title: str, plot: str = None):
        """
        生成电视剧的NFO描述文件
        :param dir_path: 电视剧根目录
        """
        # 开始生成XML
        logger.info(f"正在生成电视剧NFO文件：{dir_path.name}")
        doc = minidom.Document()
        root = DomUtils.add_node(doc, doc, "tvshow")

        # 标题
        DomUtils.add_node(doc, root, "title", title)
        DomUtils.add_node(doc, root, "originaltitle", title)
        DomUtils.add_node(doc, root, "season", "-1")
        DomUtils.add_node(doc, root, "episode", "-1")
        if plot:
            self.__set_nfo_text_node(doc, root, "plot", plot)
            self.__set_nfo_text_node(doc, root, "outline", plot)
        # 保存
        self.__save_nfo(doc, dir_path.joinpath("tvshow.nfo"))

    def __save_tv_plot_nfo(self, dir_path: Path, title: str, plot: str):
        """
        把站点简介写入 tvshow.nfo，供 Emby 显示剧情简介。
        """
        if not plot:
            return
        nfo_path = dir_path.joinpath("tvshow.nfo")
        try:
            if nfo_path.exists():
                doc = minidom.parse(str(nfo_path))
                roots = doc.getElementsByTagName("tvshow")
                root = roots[0] if roots else None
                if not root:
                    root = DomUtils.add_node(doc, doc, "tvshow")
            else:
                doc = minidom.Document()
                root = DomUtils.add_node(doc, doc, "tvshow")
                DomUtils.add_node(doc, root, "title", title)
                DomUtils.add_node(doc, root, "originaltitle", title)
                DomUtils.add_node(doc, root, "season", "-1")
                DomUtils.add_node(doc, root, "episode", "-1")

            self.__set_nfo_text_node(doc, root, "plot", plot)
            self.__set_nfo_text_node(doc, root, "outline", plot)
            self.__save_nfo(doc, nfo_path)
            logger.info(f"站点简介已写入NFO：{nfo_path}")
        except Exception as e:
            logger.error(f"站点简介写入NFO失败：{nfo_path} - {e}")

    @staticmethod
    def __nfo_has_plot(dir_path: Path) -> bool:
        """
        判断 tvshow.nfo 是否已有简介。
        """
        nfo_path = dir_path.joinpath("tvshow.nfo")
        if not nfo_path.exists():
            return False
        try:
            doc = minidom.parse(str(nfo_path))
            for tag_name in ["plot", "outline"]:
                nodes = doc.getElementsByTagName(tag_name)
                if nodes and nodes[0].firstChild and str(nodes[0].firstChild.nodeValue).strip():
                    return True
        except Exception:
            return False
        return False

    @staticmethod
    def __read_nfo_plot(dir_path: Path) -> Optional[str]:
        """
        读取 tvshow.nfo 中的简介。
        """
        nfo_path = dir_path.joinpath("tvshow.nfo")
        if not nfo_path.exists():
            return None
        try:
            doc = minidom.parse(str(nfo_path))
            for tag_name in ["plot", "outline"]:
                nodes = doc.getElementsByTagName(tag_name)
                if nodes and nodes[0].firstChild:
                    plot = str(nodes[0].firstChild.nodeValue).strip()
                    if plot:
                        return plot
        except Exception as e:
            logger.debug(f"读取NFO简介失败：{nfo_path} - {e}")
        return None

    def __ensure_series_metadata(self,
                                 target_path: Path,
                                 title: str,
                                 rename_conf: str,
                                 cover_conf: str,
                                 source_title: Optional[str] = None):
        """
        已有硬链接文件也补齐 tvshow.nfo、简介和 poster。
        """
        try:
            series_dir = self.__get_series_dir(target_path)
            nfo_path = series_dir / "tvshow.nfo"
            poster_path = series_dir / "poster.jpg"

            if not nfo_path.exists():
                self.__gen_tv_nfo_file(dir_path=series_dir, title=title)

            need_plot = not self.__nfo_has_plot(series_dir)
            need_poster = not poster_path.exists()
            if not need_plot and not need_poster:
                return
            if need_poster:
                failed_at = self._series_poster_fail_cache.get(str(series_dir))
                if failed_at and time.time() - failed_at < 3600:
                    logger.debug(f"该剧封面近期获取失败，跳过重复处理：{series_dir}")
                    need_poster = False
                    if not need_plot:
                        return

            site_media = None
            if str(rename_conf) == "smart" and (need_plot or need_poster):
                site_media = self.__query_media(title=title,
                                                file_path=target_path,
                                                source_title=source_title)

            if need_plot and site_media and site_media.get("plot"):
                self.__save_tv_plot_nfo(dir_path=series_dir,
                                        title=title,
                                        plot=site_media.get("plot"))

            if need_poster:
                thumb_path = target_path.with_name(target_path.stem + "-site.jpg")
                if site_media and site_media.get("image"):
                    if self.__save_image(url=site_media.get("image"), file_path=thumb_path):
                        self._notify_image_urls[str(series_dir)] = site_media.get("image")
                        self.__save_poster(input_path=thumb_path,
                                           poster_path=poster_path,
                                           cover_conf=cover_conf)
                        thumb_path.unlink(missing_ok=True)
                        self._series_poster_fail_cache.pop(str(series_dir), None)
                        return
                    fallback_media = self.__query_next_media_after_source(current_source=site_media.get("source"),
                                                                          title=title,
                                                                          file_path=target_path,
                                                                          source_title=source_title,
                                                                          require_image=True)
                    if fallback_media and fallback_media.get("plot") and need_plot and not self.__nfo_has_plot(series_dir):
                        self.__save_tv_plot_nfo(dir_path=series_dir,
                                                title=title,
                                                plot=fallback_media.get("plot"))
                    if fallback_media and fallback_media.get("image"):
                        if self.__save_image(url=fallback_media.get("image"), file_path=thumb_path):
                            self._notify_image_urls[str(series_dir)] = fallback_media.get("image")
                            self.__save_poster(input_path=thumb_path,
                                               poster_path=poster_path,
                                               cover_conf=cover_conf)
                            thumb_path.unlink(missing_ok=True)
                            self._series_poster_fail_cache.pop(str(series_dir), None)
                            return

                if not self._image:
                    self._series_poster_fail_cache[str(series_dir)] = time.time()
                    logger.info(f"未从刮削来源获取到封面，封面裁剪开关未开启，跳过视频截图：{series_dir}")
                    return

                thumb_path = target_path.with_name(target_path.stem + "-thumb.jpg")
                self.get_thumb(video_path=str(target_path),
                               image_path=str(thumb_path),
                               frames=self._timeline)
                if thumb_path.exists():
                    self.__save_poster(input_path=thumb_path,
                                       poster_path=poster_path,
                                       cover_conf=cover_conf)
                    thumb_path.unlink(missing_ok=True)
                    self._series_poster_fail_cache.pop(str(series_dir), None)
                else:
                    self._series_poster_fail_cache[str(series_dir)] = time.time()
        except Exception as e:
            logger.error(f"补齐儿童元数据失败：{target_path} - {e}")

    def __save_nfo(self, doc, file_path: Path):
        """
        保存NFO
        """
        xml_str = doc.toprettyxml(indent="  ", encoding="utf-8")
        file_path.write_bytes(xml_str)
        logger.info(f"NFO文件已保存：{file_path}")

    def gen_file_thumb_from_site(self,
                                 title: str,
                                 file_path: Path,
                                 media_path: Optional[Path] = None,
                                 source_title: Optional[str] = None):
        """
        先从 TMDB 查询封面和简介，失败后从已配置 Cookie 的站点查询。
        """
        try:
            site_media = self.__query_media(title=title,
                                            file_path=media_path,
                                            source_title=source_title)
            image = site_media.get("image") if site_media else None
            plot = site_media.get("plot") if site_media else None
            series_dir = self.__get_series_dir(media_path) if media_path else self.__get_series_dir(file_path)

            if not image:
                logger.error(f"检索 {title} 封面失败")
                return None

            if plot:
                self.__save_tv_plot_nfo(dir_path=series_dir,
                                        title=title,
                                        plot=plot)

            # 下载图片保存
            if self.__save_image(url=image, file_path=file_path):
                self._notify_image_urls[str(series_dir)] = image
                return file_path
            fallback_media = self.__query_next_media_after_source(current_source=site_media.get("source") if site_media else None,
                                                                  title=title,
                                                                  file_path=media_path,
                                                                  source_title=source_title,
                                                                  require_image=True)
            fallback_image = fallback_media.get("image") if fallback_media else None
            fallback_plot = fallback_media.get("plot") if fallback_media else None
            if fallback_plot and not plot:
                self.__save_tv_plot_nfo(dir_path=series_dir,
                                        title=title,
                                        plot=fallback_plot)
            if fallback_image and self.__save_image(url=fallback_image, file_path=file_path):
                self._notify_image_urls[str(series_dir)] = fallback_image
                return file_path
            return None
        except Exception as e:
            logger.error(f"检索 {title} 封面失败 {str(e)}")
            return None

    def __query_source_media(self,
                             source: str,
                             title: str,
                             file_path: Optional[Path] = None,
                             source_title: Optional[str] = None) -> Optional[dict]:
        """
        按单个来源查询元数据。
        """
        source = str(source or "").strip()
        site_title = str(source_title or title or "").strip()
        if source == "pg":
            return self.__query_pg_media(title=site_title)
        if source == "tmdb":
            return self.__query_tmdb_media(title=title, file_path=file_path)
        if source == "hxpt":
            return self.__query_site_media(title=site_title)
        return None

    def __query_next_media_after_source(self,
                                        current_source: Optional[str],
                                        title: str,
                                        file_path: Optional[Path] = None,
                                        source_title: Optional[str] = None,
                                        require_image: bool = False) -> Optional[dict]:
        """
        当前来源拿到的封面下载失败后，继续尝试后续来源。
        """
        sources = self._scrape_sources or []
        if current_source in sources:
            sources = sources[sources.index(current_source) + 1:]
        for source in sources:
            media = self.__query_source_media(source=source,
                                              title=title,
                                              file_path=file_path,
                                              source_title=source_title)
            if not media:
                continue
            if media.get("image") and self.__is_known_invalid_poster_url(media.get("image")):
                logger.warn(f"{source} 返回无效占位封面，跳过该封面：{media.get('image')}")
                media["image"] = None
            if require_image and not media.get("image"):
                continue
            if media.get("image") or media.get("plot"):
                logger.info(f"{current_source or '前一来源'} 封面不可用，改用 {source} 元数据")
                return media
        return None

    def __query_media(self,
                      title: str,
                      file_path: Optional[Path] = None,
                      source_title: Optional[str] = None) -> Optional[dict]:
        """
        元数据查询入口：严格按配置来源顺序查询，前一个来源失败后继续下一个来源。
        """
        site_title = str(source_title or title or "").strip()
        title_key = str(title or "").strip()
        cache_key = (tuple(self._scrape_sources or []), title_key, site_title)
        cached = self._media_query_cache.get(cache_key)
        if cached:
            cache_ttl = 300 if cached.get("media") else 60
        else:
            cache_ttl = 0
        if cached and time.time() - cached.get("time", 0) < cache_ttl:
            return cached.get("media")

        fallback_media = None
        for source in self._scrape_sources or []:
            media = self.__query_source_media(source=source,
                                              title=title,
                                              file_path=file_path,
                                              source_title=source_title)

            if media and (media.get("image") or media.get("plot")):
                if media.get("image") and self.__is_known_invalid_poster_url(media.get("image")):
                    logger.warn(f"{source} 返回无效占位封面，跳过该封面：{media.get('image')}")
                    media["image"] = None
                if media.get("plot") and not media.get("image"):
                    # 仅有简介时继续尝试后续来源获取封面；若后续都失败，最后仍返回简介。
                    fallback_media = media
                    continue
                if fallback_media and fallback_media.get("plot") and not media.get("plot"):
                    media["plot"] = fallback_media.get("plot")
                self._media_query_cache[cache_key] = {
                    "time": time.time(),
                    "media": media
                }
                return media

        if fallback_media:
            self._media_query_cache[cache_key] = {
                "time": time.time(),
                "media": fallback_media
            }
            return fallback_media

        self._media_query_cache[cache_key] = {
            "time": time.time(),
            "media": None
        }
        return None

    @staticmethod
    def __normalize_scrape_sources(value: Any) -> List[str]:
        """
        标准化刮削来源，保留用户配置顺序并去重。
        """
        if value is None:
            value = ["tmdb", "hxpt"]
        if isinstance(value, str):
            value = [item.strip() for item in re.split(r"[,，\s]+", value) if item.strip()]
        if not isinstance(value, list):
            value = []

        allowed_sources = {"tmdb", "hxpt", "pg"}
        sources = []
        for item in value:
            item = str(item or "").strip()
            if item in allowed_sources and item not in sources:
                sources.append(item)
        return sources

    @staticmethod
    def __quote_pg_identifier(name: str) -> str:
        """
        PostgreSQL 标识符转义，只允许普通 schema/table/column 名称。
        """
        name = str(name or "").strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            raise ValueError(f"非法PG标识符：{name}")
        return f'"{name}"'

    def __quote_pg_table(self) -> str:
        """
        生成安全的 PostgreSQL 表名，支持 schema.table。
        """
        table = str(self._pg_table or "public.pt_detail_meta").strip()
        parts = [part.strip() for part in table.split(".") if part.strip()]
        if not parts or len(parts) > 2:
            raise ValueError(f"非法PG表名：{table}")
        return ".".join(self.__quote_pg_identifier(part) for part in parts)

    @staticmethod
    def __get_pg_search_keywords(title: str) -> List[str]:
        """
        从媒体标题中生成用于 PG 元数据表模糊匹配的关键词。
        """
        title = str(title or "").strip()
        if not title:
            return []
        titles = [title]
        age_with_dash = re.sub(r"(\d+)\s*到\s*(\d+)\s*岁", r"\1-\2岁", title)
        age_with_to = re.sub(r"(\d+)\s*[-~～—]\s*(\d+)\s*岁", r"\1到\2岁", title)
        for item in (age_with_dash, age_with_to):
            if item and item not in titles:
                titles.append(item)

        keywords = []
        for item in titles:
            if item not in keywords:
                keywords.append(item)
        cleaned = re.sub(r"[._·・]+", " ", title)
        cleaned = re.sub(r"\s+", " ", cleaned).strip()
        if cleaned and cleaned not in keywords:
            keywords.append(cleaned)
        chinese = "".join(re.findall(r"[\u4e00-\u9fff]+", title))
        if chinese and len(chinese) >= 2 and chinese not in keywords:
            keywords.insert(0, chinese)
        compact = ChildrenScraper.__compact_pg_text(title)
        if compact and len(compact) >= 2 and compact not in keywords:
            keywords.append(compact)
        return keywords[:5]

    @staticmethod
    def __compact_pg_text(value: str) -> str:
        """
        归一化 PG 标题匹配文本，解决站点标题和下载目录在空格/标点上的差异。
        """
        value = str(value or "").lower()
        value = re.sub(r"(\d+)\s*到\s*(\d+)\s*岁", r"\1到\2岁", value)
        value = re.sub(r"(\d+)\s*[-~～—]\s*(\d+)\s*岁", r"\1到\2岁", value)
        return re.sub(r"[^0-9a-z\u4e00-\u9fff]+", "", value)

    @staticmethod
    def __get_pg_search_segments(title: str) -> List[str]:
        """
        提取中文分段关键词，避免 S01/Complete/标点差异导致整串匹配失败。
        """
        title = str(title or "").strip()
        if not title:
            return []
        title = re.sub(r"(\d+)\s*到\s*(\d+)\s*岁", r"\1-\2岁", title)
        segments = []
        for segment in re.findall(r"[\u4e00-\u9fff]{2,}", title):
            segment = segment.strip()
            if len(segment) >= 2 and segment not in segments:
                segments.append(segment)
        return segments[:5]

    @staticmethod
    def __get_pg_season_patterns(title: str) -> List[str]:
        """
        从源种子名提取季号，避免同系列不同季互相误匹配。
        """
        title = str(title or "").strip()
        if not title:
            return []
        season_no = None
        match = re.search(r"(?:^|[\s._-])S(\d{1,2})(?:[\s._-]|E|\b)", title, re.I)
        if not match:
            match = re.search(r"Season[\s._-]*(\d{1,2})", title, re.I)
        if match:
            season_no = int(match.group(1))
        if season_no is None:
            return []
        season_chinese = {
            1: "一", 2: "二", 3: "三", 4: "四", 5: "五",
            6: "六", 7: "七", 8: "八", 9: "九", 10: "十",
            11: "十一", 12: "十二", 13: "十三", 14: "十四", 15: "十五",
            16: "十六", 17: "十七", 18: "十八", 19: "十九", 20: "二十",
        }.get(season_no)
        patterns = [
            f"S{season_no:02d}",
            f"S{season_no}",
            f"Season {season_no:02d}",
            f"Season {season_no}",
            f"第{season_no}季",
        ]
        if season_chinese:
            patterns.append(f"第{season_chinese}季")
        return list(dict.fromkeys([
            *patterns
        ]))

    def __query_pg_media(self, title: str) -> Optional[dict]:
        """
        从 PT Depiler 写入的 PostgreSQL 元数据表读取封面和简介。
        """
        if not all([self._pg_host, self._pg_database, self._pg_username, self._pg_password]):
            logger.warn("已勾选PG数据库来源，但PG连接信息未填写完整")
            return None
        keywords = self.__get_pg_search_keywords(title)
        if not keywords:
            return None
        try:
            import psycopg2
        except Exception as e:
            logger.error(f"PG数据库来源不可用，缺少 psycopg2 依赖：{e}")
            return None

        table_name = None
        try:
            table_name = self.__quote_pg_table()
        except Exception as e:
            logger.error(f"PG数据库表名配置错误：{e}")
            return None

        try:
            port = int(self._pg_port or 5432)
        except Exception:
            port = 5432

        conditions = []
        params = []
        compact_expr = (
            "regexp_replace(lower("
            "coalesce(torrent_title, '')"
            "), '[^0-9a-z一-龥]+', '', 'g')"
        )
        for keyword in keywords:
            pattern = f"%{keyword}%"
            compact_keyword = self.__compact_pg_text(keyword)
            if compact_keyword:
                conditions.append(
                    f"(torrent_title ILIKE %s OR {compact_expr} ILIKE %s)"
                )
                params.extend([pattern, f"%{compact_keyword}%"])
                continue
            conditions.append("(torrent_title ILIKE %s)")
            params.append(pattern)
        segments = self.__get_pg_search_segments(title)
        if segments:
            segment_conditions = []
            for segment in segments:
                pattern = f"%{segment}%"
                segment_conditions.append("(torrent_title ILIKE %s)")
                params.append(pattern)
            conditions.append(f"({' AND '.join(segment_conditions)})")
        season_patterns = self.__get_pg_season_patterns(title)
        season_sql = ""
        if season_patterns:
            season_conditions = []
            for season_pattern in season_patterns:
                pattern = f"%{season_pattern}%"
                season_conditions.append("(torrent_title ILIKE %s)")
                params.append(pattern)
            season_sql = f" AND ({' OR '.join(season_conditions)})"
        rank_title = str(title or "").strip()
        rank_cleaned = re.sub(r"[._·・]+", " ", rank_title)
        rank_cleaned = re.sub(r"\s+", " ", rank_cleaned).strip()
        rank_compact = self.__compact_pg_text(rank_title)
        order_params = [
            rank_title,
            f"%{rank_title}%",
            f"%{rank_cleaned}%",
            f"%{rank_compact}%"
        ]

        sql = f"""
            SELECT poster_url, overview, title, torrent_title, site_name, detail_url, db_written_at, write_delay_ms
            FROM {table_name}
            WHERE ({' OR '.join(conditions)}){season_sql}
            ORDER BY
                CASE
                    WHEN torrent_title = %s THEN 0
                    WHEN torrent_title ILIKE %s THEN 1
                    WHEN torrent_title ILIKE %s THEN 2
                    WHEN {compact_expr} ILIKE %s THEN 3
                    ELSE 9
                END,
                db_written_at DESC NULLS LAST, updated_at DESC NULLS LAST, id DESC
            LIMIT 1
        """
        params.extend(order_params)

        try:
            with psycopg2.connect(
                host=self._pg_host,
                port=port,
                dbname=self._pg_database,
                user=self._pg_username,
                password=self._pg_password,
                connect_timeout=5,
            ) as conn:
                with conn.cursor() as cur:
                    cur.execute("SET TIME ZONE 'Asia/Shanghai'")
                    cur.execute(sql, params)
                    row = cur.fetchone()
            if not row:
                logger.info(f"PG数据库未匹配到元数据：{title}")
                return None
            image, plot, db_title, db_torrent_title, site_name, detail_url, db_written_at, write_delay_ms = row
            logger.info(f"PG数据库已匹配元数据：{title} -> {db_torrent_title or db_title}")
            return {
                "image": str(image).strip() if image else None,
                "plot": str(plot).strip() if plot else None,
                "source": "pg",
                "site": site_name,
                "detail_url": detail_url,
                "db_written_at": db_written_at,
                "write_delay_ms": write_delay_ms
            }
        except Exception as e:
            logger.error(f"PG数据库查询 {title} 失败：{e}")
            return None

    def __query_tmdb_media(self, title: str, file_path: Optional[Path] = None) -> Optional[dict]:
        """
        使用 MoviePilot 内置识别链从 TMDB 获取封面和简介。
        """
        try:
            mediainfo = None
            if file_path:
                context = MediaChain().recognize_by_path(str(file_path), obtain_images=True)
                mediainfo = context.media_info if context else None
            if not mediainfo and title:
                meta = MetaInfo(title)
                meta.type = MediaType.TV
                mediainfo = MediaChain().recognize_by_meta(meta, obtain_images=True)
            if not mediainfo:
                return None
            image = mediainfo.get_poster_image(default=False) if hasattr(mediainfo, "get_poster_image") else None
            plot = str(mediainfo.overview).strip() if getattr(mediainfo, "overview", None) else None
            if image or plot:
                logger.info(f"TMDB已获取 {title} 元数据：{getattr(mediainfo, 'title_year', '')}")
                return {
                    "image": image,
                    "plot": plot,
                    "source": "tmdb"
                }
        except Exception as e:
            logger.warn(f"TMDB检索 {title} 失败，改用站点检索：{e}")
        return None

    def __query_site_media(self, title: str) -> Optional[dict]:
        """
        从已配置 Cookie 的 PT 站检索封面和简介。
        """
        site_confs = [
            {
                "source": "hxpt",
                "domain": "hxpt.org",
                "search_url": f"https://www.hxpt.org/torrents.php?search_mode=0&search_area=0&page=0&search={title}",
                "image_xpath": "//*[@id='kdescr']//img/@src | //img/@src"
            },
            {
                "source": "hxpt",
                "domain": "www.hxpt.org",
                "search_url": f"https://www.hxpt.org/torrents.php?search_mode=0&search_area=0&page=0&search={title}",
                "image_xpath": "//*[@id='kdescr']//img/@src | //img/@src"
            }
        ]
        sources = self._scrape_sources or []
        searched_domains = set()
        for site_conf in site_confs:
            if site_conf.get("source") not in sources:
                continue
            domain = site_conf.get("domain")
            if domain in searched_domains:
                continue
            site = SiteOper().get_by_domain(domain)
            if site and site.domain in searched_domains:
                continue
            index = SitesHelper().get_indexer(domain)
            if not site:
                continue
            searched_domains.add(domain)
            searched_domains.add(site.domain)
            logger.info(f"开始检索 {site.name} {title}")
            site_media = self.__get_site_torrents(url=site_conf.get("search_url"),
                                                  site=site,
                                                  image_xpath=site_conf.get("image_xpath"),
                                                  index=index)
            if site_media and site_media.get("image"):
                return site_media
        return None

    @staticmethod
    def __is_known_invalid_poster_url(url: str) -> bool:
        """
        已知无效占位图 URL。命中后直接跳过，让后续来源继续尝试。
        """
        lower = str(url or "").strip().lower()
        invalid_parts = [
            "/p2678916217.",
        ]
        return any(part in lower for part in invalid_parts)

    def __is_invalid_poster_content(self, content: bytes, url: str = "") -> bool:
        """
        判断下载结果是否为无效占位图，而不是实际海报。
        """
        if not content:
            return True
        if self.__is_known_invalid_poster_url(url):
            return True
        try:
            image = Image.open(BytesIO(content)).convert("RGB")
        except Exception:
            return True

        width, height = image.size
        if width < 120 or height < 120:
            return True

        # Piggo/Douban token 失效图通常是大面积浅灰蓝底，中下部只有大号深色文字。
        # 这里不按域名排除，避免误伤正常 cache.piggo.me/doubanio 海报。
        small = image.resize((80, 120))
        pixels = list(small.getdata())
        total = len(pixels)
        dark_ratio = sum(1 for r, g, b in pixels if r < 80 and g < 80 and b < 80) / total
        colorful_ratio = sum(1 for r, g, b in pixels if max(r, g, b) - min(r, g, b) > 50) / total
        top_pixels = list(small.crop((0, 0, 80, 50)).getdata())
        top_bright_ratio = sum(1 for r, g, b in top_pixels if r > 205 and g > 210 and b > 215) / len(top_pixels)
        top_dark_ratio = sum(1 for r, g, b in top_pixels if r < 100 and g < 100 and b < 100) / len(top_pixels)

        return top_bright_ratio > 0.88 and top_dark_ratio < 0.01 and 0.02 < dark_ratio < 0.22 and colorful_ratio < 0.12

    @retry(RequestException, logger=logger)
    def __save_image(self, url: str, file_path: Path):
        """
        下载图片并保存
        """
        try:
            url = str(url or "").strip()
            if not url:
                return False
            failed_at = self._image_download_fail_cache.get(url)
            if failed_at and time.time() - failed_at < 3600:
                logger.debug(f"站点封面图近期下载失败，跳过重复请求：{url}")
                return False
            logger.info(f"正在下载站点封面图：{url} ...")
            headers = {
                "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                              "AppleWebKit/537.36 (KHTML, like Gecko) "
                              "Chrome/126.0.0.0 Safari/537.36",
                "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8"
            }
            image_domain = urlparse(url).netloc.lower()
            if "doubanio.com" in image_domain:
                headers["Referer"] = "https://movie.douban.com/"
            self.__apply_image_site_cookie(headers=headers, image_url=url)

            proxy_config = self.__get_proxy_config()
            request_modes = [("代理", proxy_config)] if proxy_config else []
            request_modes.append(("直连", None))

            last_error = None
            for mode_name, proxies in request_modes:
                try:
                    r = requests.get(url=url,
                                     headers=headers,
                                     proxies=proxies,
                                     timeout=30)
                except RequestException as err:
                    last_error = str(err)
                    logger.warn(f"站点封面图{mode_name}下载失败：{file_path.parent} - {last_error}")
                    continue

                if r and r.status_code == 200 and r.content:
                    if self.__is_invalid_poster_content(r.content, url):
                        self._image_download_fail_cache[url] = time.time()
                        logger.warn(f"站点封面图为无效占位图，跳过：{file_path.parent}")
                        return False
                    file_path.write_bytes(r.content)
                    self._image_download_fail_cache.pop(url, None)
                    logger.info(f"站点封面图已保存：{file_path.parent}")
                    return True

                status_code = r.status_code if r is not None else "无响应"
                last_error = f"状态码：{status_code}"
                logger.warn(f"站点封面图{mode_name}下载失败，{last_error}，路径：{file_path.parent}")

            self._image_download_fail_cache[url] = time.time()
            logger.warn(f"站点封面图下载失败，已尝试代理/直连：{file_path.parent} - {last_error or '无响应'}")
            return False
        except RequestException as err:
            self._image_download_fail_cache[str(url)] = time.time()
            raise err
        except Exception as err:
            self._image_download_fail_cache[str(url)] = time.time()
            logger.error(f"站点封面图下载失败：{file_path.parent} - {str(err)}")
            return False

    def __get_site_torrents(self, url: str, site, image_xpath, index):
        """
        查询站点资源
        """
        page_source = self.__get_page_source(url=url, site=site)
        if not page_source:
            logger.error(f"请求站点 {site.name} 失败")
            return None
        _spider = SiteSpider(indexer=index, page=1)
        torrents = _spider.parse(page_source)
        if not torrents:
            logger.error(f"未检索到站点 {site.name} 资源")
            return None

        # 获取种子详情页
        torrent_detail_source = self.__get_page_source(url=torrents[0].get("page_url"), site=site)
        if not torrent_detail_source:
            logger.error(f"请求种子详情页失败 {torrents[0].get('page_url')}")
            return None

        html = etree.HTML(torrent_detail_source)
        if not html:
            logger.error(f"请求种子详情页失败 {torrents[0].get('page_url')}")
            return None

        images = html.xpath(image_xpath)
        images.extend(self.__extract_image_urls(torrent_detail_source))
        image = self.__select_site_image(images=images, base_url=torrents[0].get("page_url"))
        if not image:
            logger.error(f"未获取到种子封面图 {torrents[0].get('page_url')}")
            return None

        return {
            "image": image,
            "plot": self.__extract_site_plot(html=html)
        }

    @staticmethod
    def __select_site_image(images: List[str], base_url: str) -> Optional[str]:
        """
        从详情页图片中挑一个最像封面的地址。
        """
        if not images:
            return None
        skip_words = [
            "logo", "avatar", "smilies", "icon", "star", "medal", "arrow",
            "pic/nexus", "bonus", "blank", "spacer", "forum_pic", "trans.gif",
            "ddlevelsfiles", "styles/", "favicon"
        ]
        candidates = []
        seen = set()
        for image in images:
            image = str(image or "").strip()
            if not image:
                continue
            image_url = urljoin(base_url, image)
            lower = image_url.lower()
            if lower.startswith("data:image"):
                continue
            if any(word in lower for word in skip_words):
                continue
            if not re.search(r"\.(jpg|jpeg|png|webp)(?:[?#].*)?$", lower) and "ykimg.com" not in lower:
                continue
            if lower in seen:
                continue
            seen.add(lower)
            candidates.append(image_url)
        if not candidates:
            return None
        for image_url in candidates:
            lower = image_url.lower()
            if "doubanio.com/view/photo" in lower or "l_ratio_poster" in lower:
                return image_url
        for image_url in candidates:
            lower = image_url.lower()
            if "img.ptang.top" in lower:
                return image_url
        for image_url in candidates:
            lower = image_url.lower()
            if "ykimg.com" in lower or "pig_image" in lower:
                return image_url
        return candidates[0]

    @staticmethod
    def __extract_image_urls(html_text: str) -> List[str]:
        """
        从详情页源码里提取图片 URL，兼容 NexusPHP 正文中的 [img] 链接。
        """
        if not html_text:
            return []
        return re.findall(
            r"https?://[^\s\]\"'<>]+\.(?:jpg|jpeg|png|webp)(?:\?[^\s\]\"'<>]*)?",
            html_text,
            re.I
        )

    @staticmethod
    def __clean_site_text(text: str) -> str:
        if not text:
            return ""
        return (text.replace("\r", "\n")
                .replace("\xa0", " ")
                .replace("\u3000", " ")
                .replace("　", " "))

    def __extract_site_plot(self, html) -> Optional[str]:
        """
        从 PT 详情页的 #kdescr 中提取 ◎简介 段落。
        """
        try:
            texts = html.xpath("string(//*[@id='kdescr'])") or html.xpath("string(//body)")
            text = self.__clean_site_text(str(texts))
            if not text:
                return None
            match = re.search(
                r"(?:◎\s*)?简\s*介\s*(.*?)(?:\n\s*(?:种子文件|显示/隐藏原始 MediaInfo|引用|General\b|mediainfo\b|MediaInfo\b|◎[^\n]*资料|◎[^\n]*截图|◎)|$)",
                text,
                re.S | re.I
            )
            if not match:
                return None
            plot = match.group(1)
            lines = []
            for line in plot.splitlines():
                line = re.sub(r"[ \t]+", " ", line).strip()
                if not line:
                    continue
                if re.match(r"^(引用|General\b|mediainfo\b|MediaInfo\b)", line, re.I):
                    break
                lines.append(line)
            plot = "\n".join(lines).strip()
            if not plot:
                return None
            logger.info(f"已获取站点简介：{plot[:80]}")
            return plot
        except Exception as e:
            logger.error(f"提取站点简介失败：{e}")
            return None

    @staticmethod
    def __get_proxy_config() -> Optional[dict]:
        """
        使用 MoviePilot 全局代理配置。
        """
        proxy_host = str(getattr(settings, "PROXY_HOST", "") or "").strip().strip("'\"")
        if not proxy_host:
            return None
        return {
            "http": proxy_host,
            "https": proxy_host
        }

    @staticmethod
    def __image_cookie_site_domain(image_url: str) -> Tuple[Optional[str], Optional[str]]:
        """
        部分站点图片 CDN 也受 Cloudflare/Cookie 保护，下载图片时需要带原站 Cookie。
        """
        image_domain = urlparse(str(image_url or "")).netloc.lower()
        if image_domain.endswith("piggo.me"):
            return "piggo.me", "https://piggo.me/"
        return None, None

    def __apply_image_site_cookie(self, headers: dict, image_url: str) -> None:
        """
        给受保护的图片域补站点 Cookie，避免 cache/origin.piggo.me 返回 Cloudflare 403。
        """
        site_domain, referer = self.__image_cookie_site_domain(image_url)
        if not site_domain:
            return
        if referer:
            headers["Referer"] = referer
        try:
            site = SiteOper().get_by_domain(site_domain)
            if site and site.cookie:
                headers["Cookie"] = site.cookie
        except Exception as err:
            logger.warn(f"读取图片站点 Cookie 失败：{site_domain} - {err}")

    def __get_page_source(self, url: str, site):
        """
        获取页面资源
        """
        ret = RequestUtils(
            cookies=site.cookie,
            proxies=self.__get_proxy_config(),
            timeout=30,
        ).get_res(url, allow_redirects=True)
        if ret is not None:
            # 使用chardet检测字符编码
            raw_data = ret.content
            if raw_data:
                try:
                    result = chardet.detect(raw_data)
                    encoding = result['encoding']
                    # 解码为字符串
                    page_source = raw_data.decode(encoding)
                except Exception as e:
                    # 探测utf-8解码
                    if re.search(r"charset=\"?utf-8\"?", ret.text, re.IGNORECASE):
                        ret.encoding = "utf-8"
                    else:
                        ret.encoding = ret.apparent_encoding
                    page_source = ret.text
            else:
                page_source = ret.text
        else:
            page_source = ""

        if page_source and self.__is_invalid_site_page(page_source):
            logger.warn(f"{site.name} 返回登录、权限或安全验证页")
            return ""

        return page_source

    @staticmethod
    def __is_invalid_site_page(page_source: str) -> bool:
        if not page_source:
            return True
        invalid_patterns = [
            "login.php",
            "type=\"password\"",
            "异地登录安全验证",
            "必须启用2FA",
            "正在进行安全验证",
            "Just a moment",
            "Attention Required",
            "Cloudflare"
        ]
        return any(pattern in page_source for pattern in invalid_patterns)

    def gen_file_thumb(self, title: str, file_path: Path, rename_conf: str, source_title: Optional[str] = None):
        """
        处理一个文件
        """
        # 智能重命名时从站点检索
        if str(rename_conf) == "smart":
            series_dir = self.__get_series_dir(file_path)
            failed_at = self._series_poster_fail_cache.get(str(series_dir))
            if failed_at and time.time() - failed_at < 3600:
                logger.debug(f"该剧封面近期获取失败，跳过重复处理：{series_dir}")
                return None
            thumb_path = file_path.with_name(file_path.stem + "-site.jpg")
            if thumb_path.exists():
                logger.info(f"缩略图已存在：{thumb_path}")
                return thumb_path
            self.gen_file_thumb_from_site(title=title,
                                          file_path=thumb_path,
                                          media_path=file_path,
                                          source_title=source_title)
            if Path(thumb_path).exists():
                logger.info(f"{file_path} 站点封面图已获取：{thumb_path}")
                self._series_poster_fail_cache.pop(str(series_dir), None)
                return thumb_path
            if not self._image:
                self._series_poster_fail_cache[str(series_dir)] = time.time()
                logger.info(f"未从刮削来源获取到封面，封面裁剪开关未开启，跳过视频截图：{file_path}")
                return None

        if not self._image:
            series_dir = self.__get_series_dir(file_path)
            self._series_poster_fail_cache[str(series_dir)] = time.time()
            logger.info(f"封面裁剪开关未开启，跳过视频截图：{file_path}")
            return None

        with ffmpeg_lock:
            try:
                thumb_path = file_path.with_name(file_path.stem + "-thumb.jpg")
                if thumb_path.exists():
                    logger.info(f"缩略图已存在：{thumb_path}")
                    return thumb_path
                self.get_thumb(video_path=str(file_path),
                               image_path=str(thumb_path),
                               frames=self._timeline)
                if Path(thumb_path).exists():
                    logger.info(f"{file_path} 缩略图已生成：{thumb_path}")
                    series_dir = self.__get_series_dir(file_path)
                    self._series_poster_fail_cache.pop(str(series_dir), None)
                    return thumb_path
                series_dir = self.__get_series_dir(file_path)
                self._series_poster_fail_cache[str(series_dir)] = time.time()
            except Exception as err:
                series_dir = self.__get_series_dir(file_path)
                self._series_poster_fail_cache[str(series_dir)] = time.time()
                logger.error(f"FFmpeg处理文件 {file_path} 时发生错误：{str(err)}")
                return None
        return None

    @staticmethod
    def get_thumb(video_path: str, image_path: str, frames: str = None):
        """
        使用ffmpeg从视频文件中截取缩略图
        """
        if not frames:
            frames = "00:00:10"
        if not video_path or not image_path:
            return False
        cmd = 'ffmpeg -y -i "{video_path}" -ss {frames} -frames 1 "{image_path}"'.format(
            video_path=video_path,
            frames=frames,
            image_path=image_path)
        result = SystemUtils.execute(cmd)
        if result:
            return True
        return False

    def __update_config(self):
        """
        更新配置
        """
        config = {
            "enabled": self._enabled,
            "exclude_keywords": self._exclude_keywords,
            "transfer_type": self._transfer_type,
            "onlyonce": self._onlyonce,
            "interval": self._interval,
            "notify": self._notify,
            "image": self._image,
            "delete_sync": self._delete_sync,
            "delete_downloaders": self._delete_downloaders,
            "refresh_mediaserver": self._refresh_mediaserver,
            "mediaservers": self._mediaservers,
            "scrape_sources": self._scrape_sources,
            "pg_host": self._pg_host,
            "pg_port": self._pg_port,
            "pg_database": self._pg_database,
            "pg_username": self._pg_username,
            "pg_password": self._pg_password,
            "pg_table": self._pg_table,
            "monitor_confs": self._monitor_confs
        }
        self.update_config(self.__merge_existing_config(config))

    def __read_saved_config(self) -> Dict[str, Any]:
        """
        读取 MoviePilot 已保存配置。
        get_form 有时不会先经过 init_plugin，这里主动兜底读取，避免表单显示空值。
        """
        if isinstance(self._last_config, dict) and self._last_config:
            return dict(self._last_config)
        for method_name in ("get_config", "get_plugin_config"):
            method = getattr(self, method_name, None)
            if not callable(method):
                continue
            try:
                config = method()
            except TypeError:
                try:
                    config = method(self.plugin_config_prefix)
                except Exception:
                    continue
            except Exception:
                continue
            if isinstance(config, dict):
                self._last_config = dict(config)
                return dict(config)
        return {}

    def __merge_existing_config(self, config: Dict[str, Any]) -> Dict[str, Any]:
        """
        自动保存配置时保护已有的文本配置，避免一次性运行、封面裁剪等内部保存把空值写回。
        """
        saved_config = self.__read_saved_config()
        merged_config = dict(saved_config)
        merged_config.update(config)
        for key in (
                "pg_password",
                "monitor_confs",
                "delete_downloaders",
                "mediaservers",
                "scrape_sources",
                "pg_host",
                "pg_database",
                "pg_username",
                "pg_table"):
            value = merged_config.get(key)
            if (value is None or value == "" or value == []) and saved_config.get(key) not in (None, "", []):
                merged_config[key] = saved_config.get(key)
        self._last_config = dict(merged_config)
        return merged_config

    def get_state(self) -> bool:
        return self._enabled

    @staticmethod
    def get_command() -> List[Dict[str, Any]]:
        pass

    def get_api(self) -> List[Dict[str, Any]]:
        pass

    @staticmethod
    def __get_downloader_items() -> List[dict]:
        """
        获取已启用的 qB 下载器列表。
        """
        try:
            services = DownloaderHelper().get_services(type_filter="qbittorrent")
            return [
                {
                    "title": name,
                    "value": name
                }
                for name in services.keys()
            ]
        except Exception as e:
            logger.error(f"获取下载器列表失败：{e}")
            return []

    @staticmethod
    def __get_mediaserver_items() -> List[dict]:
        """
        获取 MoviePilot 已启用的媒体服务器列表。
        """
        try:
            return [
                {
                    "title": config.name,
                    "value": config.name
                }
                for config in MediaServerHelper().get_configs().values()
            ]
        except Exception as e:
            logger.error(f"获取媒体服务器列表失败：{e}")
            return []

    @staticmethod
    def __get_scrape_source_items() -> List[dict]:
        """
        获取可选刮削来源。
        """
        return [
            {
                "title": "TMDB",
                "value": "tmdb"
            },
            {
                "title": "好学",
                "value": "hxpt"
            },
            {
                "title": "PG数据库",
                "value": "pg"
            }
        ]

    def __get_quiet_delay(self) -> int:
        """
        获取媒体库刷新静默等待时间。
        """
        return 30

    def __schedule_mediaserver_refresh(self, target_path: Optional[Path] = None, title: Optional[str] = None):
        """
        目录监控入库时合并刷新媒体库，避免一集一刷。
        """
        if not self._refresh_mediaserver or self._syncing:
            return
        if not self._scheduler:
            self.__refresh_mediaserver_library(target_path=target_path, title=title)
            return
        run_date = datetime.datetime.now(tz=pytz.timezone(settings.TZ)) + datetime.timedelta(
            seconds=self.__get_quiet_delay()
        )
        self._scheduler.add_job(func=self.__refresh_mediaserver_library,
                                trigger='date',
                                run_date=run_date,
                                kwargs={
                                    "target_path": target_path,
                                    "title": title
                                },
                                id="childrenscraper_refresh_mediaserver",
                                name="儿童刮削后刷新媒体库",
                                replace_existing=True)

    def __refresh_mediaserver_library(self, target_path: Optional[Path] = None, title: Optional[str] = None):
        """
        通知所选媒体服务器刷新媒体库。
        """
        if not self._refresh_mediaserver:
            return
        if not self._mediaservers:
            logger.warn("已开启媒体库刷新，但未选择媒体服务器，跳过刷新")
            return

        servers = MediaServerHelper().get_services(name_filters=self._mediaservers)
        if not servers:
            logger.warn(f"未找到已选择的媒体服务器：{', '.join(self._mediaservers)}，跳过刷新")
            return

        for name, service in servers.items():
            try:
                if hasattr(service.instance, "refresh_root_library"):
                    service.instance.refresh_root_library()
                    logger.info(f"已通知 {name} 刷新媒体库")
                else:
                    logger.warn(f"{name} 未找到可用刷新接口，跳过刷新")
            except Exception as e:
                logger.error(f"通知 {name} 刷新媒体库失败：{e}")

    def get_form(self) -> Tuple[List[dict], Dict[str, Any]]:
        """
        拼装插件配置页面，需要返回两块数据：1、页面配置；2、数据结构
        """
        form_config = self.__merge_existing_config({})
        return [
            {
                'component': 'VForm',
                'content': [
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enabled',
                                            'label': '启用插件',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'onlyonce',
                                            'label': '立即运行一次',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'image',
                                            'label': '封面裁剪',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'notify',
                                            'label': '发送通知',
                                        }
                                    }
                                ]
                            },
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSelect',
                                        'props': {
                                            'model': 'transfer_type',
                                            'label': '转移方式',
                                            'items': [
                                                {'title': '移动', 'value': 'move'},
                                                {'title': '复制', 'value': 'copy'},
                                                {'title': '硬链接', 'value': 'link'},
                                                {'title': '软链接', 'value': 'softlink'},
                                            ]
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'interval',
                                            'label': '入库消息延迟',
                                            'placeholder': '30'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 12
                                },
                                'content': [
                                    {
                                        'component': 'VAutocomplete',
                                        'props': {
                                            'model': 'scrape_sources',
                                            'label': '刮削来源',
                                            'items': self.__get_scrape_source_items(),
                                            'multiple': True,
                                            'chips': True,
                                            'clearable': True,
                                            'hint': '按已选芯片从左到右作为优先级；第一来源失败或未获取到封面/简介时再尝试后面的来源。PG数据库会读取 PT Depiler 元数据表。',
                                            'persistent-hint': True
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'pg_host',
                                            'label': 'PG地址',
                                            'placeholder': '192.168.1.100',
                                            'hint': '勾选PG数据库来源后使用。',
                                            'persistent-hint': True
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 2
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'pg_port',
                                            'label': 'PG端口',
                                            'placeholder': '5432'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'pg_database',
                                            'label': 'PG数据库',
                                            'placeholder': 'pt_depiler'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'pg_table',
                                            'label': 'PG表名',
                                            'placeholder': 'public.pt_detail_meta'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'pg_username',
                                            'label': 'PG用户名',
                                            'placeholder': 'pt_depiler'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'pg_password',
                                            'label': 'PG密码',
                                            'type': 'password',
                                            'placeholder': '请输入PG密码'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'refresh_mediaserver',
                                            'label': '刷新媒体库',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 9
                                },
                                'content': [
                                    {
                                        'component': 'VAutocomplete',
                                        'props': {
                                            'model': 'mediaservers',
                                            'label': '媒体服务器',
                                            'items': self.__get_mediaserver_items(),
                                            'multiple': True,
                                            'chips': True,
                                            'clearable': True,
                                            'hint': '硬链接和刮削任务完成后，通知所选媒体服务器刷新媒体库。',
                                            'persistent-hint': True
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 3
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'delete_sync',
                                            'label': '删除联动',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 9
                                },
                                'content': [
                                    {
                                        'component': 'VAutocomplete',
                                        'props': {
                                            'model': 'delete_downloaders',
                                            'label': '下载器',
                                            'items': self.__get_downloader_items(),
                                            'multiple': True,
                                            'chips': True,
                                            'clearable': True,
                                            'hint': '删除联动会双向删除源文件和硬链接；整部剧目录删除时按路径匹配所选 qB 下载器任务，只删除下载记录，不删除下载文件。',
                                            'persistent-hint': True
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VTextarea',
                                        'props': {
                                            'model': 'monitor_confs',
                                            'label': '监控目录',
                                            'rows': 5,
                                            'placeholder': '监控方式#监控目录#目的目录#是否重命名#封面比例'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                },
                                'content': [
                                    {
                                        'component': 'VTextarea',
                                        'props': {
                                            'model': 'exclude_keywords',
                                            'label': '排除关键词',
                                            'rows': 2,
                                            'placeholder': '每一行一个关键词'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                },
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'text': '配置说明：'
                                                    'https://github.com/gctts/MoviePilot-ChildrenScraper#readme'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                },
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'text': '按插件配置硬链接入库，不走 MoviePilot 转移分类；刮削来源按已选顺序依次尝试；PG数据库来源读取 PT Depiler 写入的元数据表；全部来源失败时回退为视频截图。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                },
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'text': '开启封面裁剪后，会把封面裁剪成配置的比例。'
                                        }
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        ], {
            "enabled": form_config.get("enabled", self._enabled),
            "onlyonce": False,
            "image": form_config.get("image", self._image),
            "notify": form_config.get("notify", self._notify),
            "delete_sync": form_config.get("delete_sync", self._delete_sync),
            "delete_downloaders": form_config.get("delete_downloaders") or self._delete_downloaders or [],
            "refresh_mediaserver": form_config.get("refresh_mediaserver", self._refresh_mediaserver),
            "mediaservers": form_config.get("mediaservers") or self._mediaservers or [],
            "scrape_sources": form_config.get("scrape_sources") or self._scrape_sources or ["tmdb", "hxpt"],
            "pg_host": form_config.get("pg_host") or self._pg_host or "",
            "pg_port": form_config.get("pg_port") or self._pg_port or 5432,
            "pg_database": form_config.get("pg_database") or self._pg_database or "pt_depiler",
            "pg_username": form_config.get("pg_username") or self._pg_username or "pt_depiler",
            "pg_password": form_config.get("pg_password") or self._pg_password or "",
            "pg_table": form_config.get("pg_table") or self._pg_table or "public.pt_detail_meta",
            "interval": form_config.get("interval") or self._interval or 30,
            "monitor_confs": form_config.get("monitor_confs") or self._monitor_confs or "",
            "exclude_keywords": form_config.get("exclude_keywords") or self._exclude_keywords or "",
            "transfer_type": form_config.get("transfer_type") or self._transfer_type or "link"
        }

    def get_page(self) -> List[dict]:
        pass

    def stop_service(self):
        """
        退出插件
        """
        try:
            if self._scheduler:
                self._scheduler.remove_all_jobs()
                if self._scheduler.running:
                    self._scheduler.shutdown()
                self._scheduler = None
        except Exception as e:
            logger.error("退出插件失败：%s" % str(e))

        if self._observer:
            for observer in self._observer:
                try:
                    observer.stop()
                    observer.join()
                except Exception as e:
                    print(str(e))
        self._observer = []
