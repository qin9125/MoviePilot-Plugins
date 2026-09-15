# MoviePilot-Plugins

适配 MoviePilot V2 插件市场的自用插件仓库。

在 MoviePilot **插件商店 → 添加第三方仓库**中填写：

   ```text
   https://github.com/qin9125/MoviePilot-Plugins
   ```
   
## 插件

- [儿童刮削](docs/ChildrenScraper.md)，插件 ID：`ChildrenScraper`
- [短剧刮削](docs/ShortPlayMonitor.md)，插件 ID：`ShortPlayMonitorCustom`
- 订阅助手，插件 ID：`SubscribeAssistant`
- NodeSeek 签到，插件 ID：`nodeseeksign`

## 短剧刮削改动

- 禁用 TMDB 识别/刮削执行路径。
- 移除 AGSV、ilolicon 封面站点。
- 使用 MoviePilot 站点管理中已配置 Cookie 的 `pterclub.net`、`zmpt.cc` 检索封面和简介。
- 剧集简介写入 `tvshow.nfo`，并在入库通知中显示简介。
- 站点检索失败时回退为视频截图。
- 已有硬链接文件在立即运行时可补齐缺失的 `poster.jpg` 和 `tvshow.nfo`。
- 支持源目录和目标目录双向删除联动。
- 支持多选 qB 下载器，整部剧目录删除时按路径匹配所选 qB 下载记录。
- 支持选择 MoviePilot 已配置的媒体服务器，硬链接/刮削完成后合并刷新媒体库。
- 没有新的硬链接10秒后通知媒体库刷新。
- 入库通知支持使用站点原始封面链接作为通知图片。

## 使用说明

监控方式：

- `fast`：性能模式，内部处理系统操作类型选择最优解。
- `compatibility`：兼容模式，目录同步性能降低且 NAS 不能休眠，但可以兼容挂载的远程共享目录如 SMB，建议使用。

是否重命名：

- `true` 自定义识别词。
- `false`。
- `smart` 自动取剧名。

封面比例：`2:3`

删除联动：

- 删除源文件会同步删除硬链接。
- 删除硬链接会同步删除源文件。
- 删除整部剧目录时会联动删除所选 qB 下载器中的下载记录。

媒体库刷新：

- 只会列出 MoviePilot 已配置的媒体服务器。
- 刷新会在一段时间没有新的硬链接后触发，时间取“入库消息延迟”，最低 10 秒。
