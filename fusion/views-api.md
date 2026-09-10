# Exact 视图的公共 API 与安装边界

## 1. 为什么安装成模块

“已经有 Qed 源码”“用户可以 Require 到它”“把某个名字承诺为可复用 API”是三件事。

版本 1 的核心目标是验证新增强 store 能否进入同一个 sealed Floyd，并被原版 VSU
消费。为避免 `proofauto` 初始化循环，exact 谓词和 semantic store 被先拆到低层；
随后只把 primitive 和 nth-SEP store wrapper 纳入了安装清单。通用视图证明随
实验代码一起留在 `fusion/tests/union_exact_view.v`，虽然有完整证明和回归，却没有
进入用户的 `VST.floyd.*` loadpath。

这是一项最小原型阶段留下的库打包缺口，不是这些引理只能用于测试，也不是证明不可靠。
正式 worker 因此能找到 store 规则，却需要重新寻找、复制甚至推导低字视图。仅告诉
它“用 exact 表示”不足以消除这部分工作。

本候选把通用实现迁到库中，测试目录只保留 import 兼容层和实际客户端回归。
业务 union 的布局、funspec、函数 body 仍由用户证明，不混入通用 API。

## 2. 分层

| 模块 | 责任 | 常见用户是否需要深入其实现 |
| --- | --- | --- |
| `FusionExact` | 精确编码 ownership、对齐、backward store assertion | 通常只使用谓词 |
| `FusionMemvals` | 与业务布局无关的 memval 资源拼接、前缀及编码转换 | 仅高级视图/缓冲区证明需要 |
| `FusionViews64` | Mint64 整数的低字、高字、宽读和 split/reassemble | 直接应用其公共定理 |
| `FusionStore` | 普通 Floyd 的强 store wrapper，并导出上述视图 | 常用入口 |

正常用户在 `proofauto` 环境下额外导入 `FusionStore` 即可。不必去 test 目录找 `.v`，
也不必展开 `yesat`、`jam` 或逐地址的 rmap 所有权来做一次普通低字读取。

## 3. 面向用户的数值视图

以下名字是本候选明确提供的 API：

| 引理 | 保证 | 显式前提 |
| --- | --- | --- |
| `exact_Mint64_has_low32_mapsto_le` | 精确 64 位编码给出低 32 位的普通可读视图，`* TT` 借出 | 小端、readable share |
| `exact_Mint64_has_mapsto` | 普通 64 位 `mapsto`，值为原 `Vlong x` | readable share |
| `exact_Mint64_has_full_mapsto_frame` | 带 `* TT` 的宽读借用形式 | readable share |
| `exact_Mint64_has_high32_mapsto_le` | `offset_val 4 p` 上的高字视图 | 小端、readable share、isptr、偏移可表示 |
| `exact_Mint64_split32_le` | 两个不重叠的 exact32 片段与 exact64 的等式，可反向重组 | 小端、isptr、偏移可表示；等式保留 Mint64 对齐 |
| `exact_Mint32_has_mapsto` | exact32 到普通 unsigned 32 位视图 | readable share |

核心低字接口的完整形状：

```coq
forall sh x p,
  Archi.big_endian = false ->
  readable_share sh ->
  exact_mapsto sh Mint64 (Vlong x) p |--
    mapsto sh tuint p (Vint (Int64.loword x)) * TT
```

**低字借用不要求构造未使用尾片的 `p+4` 指针**，也没有额外的 `p+8 < modulus`
前提。高字和真正的两片分离重组则保留必要的偏移条件，不能把两种 API 混用。

这些定理给出 `mapsto`。若目标是业务 `data_at` 或 `field_at`，相应的
`field_compatible`、布局和范围事实仍要由业务表示提供；安装视图库不意味着可以
省掉这些条件。

## 4. 可复用的较低层接口

`FusionMemvals` 对高级用户提供：

- `memvals_at`、`pointer_aligned`、`pointer_offset`。
- `memvals_at_app`：真正的相邻片段分离，保留指针偏移可表示条件。
- `memvals_at_prefix`：只借前缀，无须形成尾片的可表示指针。
- `exact_mapsto_memvals`：exact 编码与 memval 资源之间的等式。

`FusionViews64` 还提供纯编码分解
`encode_val_Mint64_Vlong_split_le`，用于需要显式位/字节计算的证明。

地址级 `address_memvals_at` 和其辅助证明保留在模块源码中，便于审查和高级调试；
本次并不把每一个辅助证明的名字都承诺为稳定外部 API。比如数值转换中的
`memvals_Mint32_has_mapsto` 标为 `Local Lemma`，普通客户端应使用已经列出的
`exact_Mint32_has_mapsto` 或高层视图。

因此，安装模块不是“把所有内部引理一股脑暴露”，而是把**有复用价值的抽象边界**
交付给客户端，保留修改内部证明的空间。

## 5. 正确组合与错误前提

正常链路仍是：

```text
ordinary ownership
  → exact store rule
  → exact_mapsto
  → ordinary readable mapsto view
  → ordinary load，继续保留完整 exact ownership
```

不能用 statement-level `semax_store_exact` 直接证明一个没有赋值语句的 mpred 蕴含。
也不能从普通宽值 `field_at/mapsto` 无条件恢复 exact 编码；完整八字节 footprint
不等于唯一的字节表示。Fragment 反例仍成立。

对重叠的多个可读视图使用蕴含/`&&`，不要用 `*` 伪造重复所有权。新客户端回归把
低字、高字、宽读和原 exact 资源用合取放在一起，并保留独立 frame，验证这条用法。

## 6. 本次验证与当前 run

已完成候选源码的编译、暂存安装、公开 import 客户端、既有 seed/body/VSU 回归、
Fragment 反例、assumptions 和递归 `coqchk`。通用视图没有引入新的全局假设。

这是新版本候选的 staged install，不是对运行中的 CCV 工具链做原地升级。
发布版本 1 的源代码、tag、安装包和当前 run 的 lock/skills 均保留原样。发布并
接入版本 2 需要新的版本锁和相应 CCV 身份支持，不能借本次成功静默切换正在进行
的证明。
