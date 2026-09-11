# Typed exact 接口层开发入口

**状态：WIP，架构与可行性原型阶段，尚未提供正式typed API或Agent自动化。**

## 分支与归属

- **`fusion/vst-2.16-dev`**：本接口层的代码、设计、原型、测试和审核。
- **`fusion/vst-2.16`**：CCV 可选择的已验上游，功能完备并通过回归/安装/审计后才从dev合并。
- CCV 仓库负责安装器、Skill消费和集成验收，不维护VST库接口的第二份设计或原型。

## 阅读顺序

1. [架构及公开语义](architecture.md)
2. [调研与14条已检查Coq探针的证据边界](research.md)
3. [原型源码](prototypes/)
4. [独立架构审查](architecture-review.md)
5. [开发日志](development-log.md)
6. [基于已归档 run2 的真实证明简化与typed原型接入实验](experiments/README.md)

这些工件从 CCV 提交 `b096a28` 迁入；迁移只纠正仓库与分支归属，没有改变原型的声明或证明。
现有可用接口说明位于 [doc/fusion.md](../../fusion.md)。

## 合入可用上游的条件

完成typed谓词/结构桥、load/store规则、Agent前端、新客户端proof、ordinary回归、assumptions/coqchk与
真实安装验收，再进行合并审查。只完成设计或原型不能合入可用分支，也不更新现有run使用的opam库。
