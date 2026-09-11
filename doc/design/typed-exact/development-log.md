# Typed exact 接口层：首步架构与可行性

日期：2026-09-11。最初误归档在 CCV 的 `b096a28`；现迁入 VST 开发分支
`fusion/vst-2.16-dev`。库接口开发与设计归 VST，CCV 只负责消费及集成验证。

## 完成内容

用户同意建立真正面向Agent的typed exact层。本步按新公开接口的设计流程，完成：

- 调研原VST type_func、aggregate/spacer、field_at与typed load/store包装。
- 提出exact_data_at/exact_field_at同资源加强语义及四模块分层，用户proof不接触mapsto后端作为核心验收目标。
- 明确padding保有但未知、partial write仅升级覆盖区域、普通未知输入不要求exact。
- 构建独立Coq原型：10条generic predicate/scalar-view/store定理和4个具体layout定理全部Qed，coqchk通过。
  primitive store仍来自原sealed Floyd，未新增正确性假设。
- 两union成员顺序、窄成员suffix资源、padding struct均实际检查；这些只验证布局，
  不冒充完整字段focus/reassembly或客户端body已证明。
- 独立架构审无已坐实blocking，指出两层资源同步分解与混合精度连续操作必须先证。

文档：[research.md](research.md)、[architecture.md](architecture.md)。
探针：[prototypes/](prototypes/)；归档源来自实际编译的私有build目录。
审核：[architecture-review.md](architecture-review.md)。

## 未完成与下一步

架构的exact精度语义和首批范围待确认，再进入函数级细化/事前expectations与公开模块实现。
没有修改VST库源码/正常发布说明、安装库、helper、原run或其证书。
当前14条探针不等于完整接口层；尤其scalar store虽已有typed-only语句规则，
Agent尚没有自动推导参数/消解义务的高层tactic，不能把它称为最终易用接口。

## 度量

| 指标 | 数值 |
|------|------|
| 新增代码行数 | 约180行研究Coq/C探针，生产代码0 |
| 修改代码行数 | 0生产代码 |
| 删除代码行数 | 0 |
| 涉及文件数 | 7份研究/架构/探针/审核/日志 |
| 新增测试用例数 | 14条Coq设计探针 |
| 测试通过率 | 14/14 Qed、coqchk通过 |
| 发现 bug 数 | 0已判定生产bug；识别1类组合证明风险 |
| 修复 bug 数 | 0 |
| 迭代轮次 | 调研/架构/独立审1轮；Coq导入/展开探针数次迭代 |
