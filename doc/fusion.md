# Exact 视图：公共 API、构建与安装

## 1. 概述

Fusion 在 VST 2.16 上提供可选的精确写入规则和可复用的内存视图引理，用于验证
宽整数写入后的重叠窄读，例如写入 union 的 64 位成员后读取其 32 位成员。

普通 `mapsto` 描述解码后的值，并不总能确定较窄读取所需的具体编码。
Fusion 在写入时通过 `exact_mapsto` 保留精确的 memval 表示，再从中导出普通可读视图，
使后续读取仍能保持完整对象的所有权。

这些能力集成在同一个 sealed Floyd `semax` 中，可与普通 `semax_body`、函数调用及
VSU 组合使用。公共接口包括精确 store、memval 前缀借用与拼接，以及整数的低字、
高字、宽读和拆分重组视图；具体前提见第 3–5 节。

使用入口为 `VST.floyd.FusionStore`。应用程序的布局、对齐、所有权条件、funspec 和
函数体证明由使用者提供。当前验证环境为 x86-64 小端、Rocq 9.0.0 和 CompCert 3.17；
安装与测试方法见第 6–7 节。

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

以下名字是当前明确提供的 API：

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

## 6. 标准 opam 安装

维护分支为 `fusion/vst-2.16`。使用独立环境和标准 opam，不需要专属安装器或发布清单：

```sh
opam switch create vst-fusion ocaml-base-compiler.4.14.2 --no-switch --repositories=coq-released,default
opam pin add --switch=vst-fusion --no-action coq-vst 'git+https://github.com/lihaokun/VST.git#fusion/vst-2.16'
opam install --switch=vst-fusion --skip-updates coq-vst
```

前置：opam 已初始化且配置了 `default` 和 `coq-released` 仓库。
switch 名不属于 API。更新只在没有验证 run 使用此环境时显式执行：

```sh
opam update --switch=vst-fusion --development coq-vst
opam upgrade --switch=vst-fusion --skip-updates coq-vst
```

包版本是普通依赖元数据，不是支持矩阵；历史构建的源码身份由实际 Git/opam 记录说明。

## 7. 构建与回归

从 VST 根目录在匹配的 opam 环境中运行：

```sh
opam exec --switch=vst-fusion -- make -j2 vst test-fusion ZLIST=platform BITSIZE=64
opam exec --switch=vst-fusion -- make test-fusion-installed ZLIST=platform BITSIZE=64
```

普通 `make test BITSIZE=64` 也编译 `progs64/fusion/` 的回归；原 `make vst/install` 是库构建安装的唯一入口。
`test-fusion-installed` 在独立目录重新编译客户端、审计 assumptions 并运行 coqchk，不修改安装环境。
开发者可显式指定 `FUSION_VST_ROOT=<staging/VST>` 核候选安装，不能据源码中的模块推断已安装能力。
候选用正常 `make install INSTALLDIR=<staging/VST>`，其 zlist 是所选环境的独立依赖。
