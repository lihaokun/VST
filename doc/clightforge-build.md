# ClightForge 语义组件消费验收（2026-11-17）

## 基线与最小改动

- VST 起点为 `5639fbc49e8d6cdb67d691fa8c71791a24a06d2e`，与 CCV
  依赖分析基线完全相同，工作树干净；独立分支 `build/clightforge-semantics`。
- ClightForge 来源为干净的 `63b9314865048986ebe235fce5ef7f4530e1952d`。
- 沿用现有 Make 目标、依赖闭包、安装和假设检查入口；增加默认
  `COMPCERT=semantics` / `SEMANTICS_DIR` 配置，读取生产者的 JSON 配置。
  不改变数学定义、已有证明或 soundness/VSU/Fusion/concurrency 模块集合。
- `coq-vst.opam` 不再依赖 `coq-compcert` 或另一套 `coq-flocq`；组件由调用者
  独立导出并通过环境变量供给，不伪装成官方 opam 包。
- `util/coqflags`、`_CoqProject-export`、安装配置和已安装 Fusion 检查使用所选
  组件的实际路径；安装文件仍由原 Make 图枚举，不再运行假 `CLIGHTGEN`。

## 组件

```text
root: /home/ubuntu/clightforge-semantics-vst-63b9314
id: f2c0fb8d2327db86250dcb932c94800166693b88e925b8acb6738f1a2ff7dc23
profile: x86_64-linux
semantic_version: 3.17
source_clean: true
payload: 80 .v + 80 full .vo，含同一导出的 Flocq
toolchain: rocq90 / Rocq 9.0.0 / OCaml 4.14.2
```

在 `/home/ubuntu/ClightForge` 执行：

```sh
opam exec --switch=rocq90 -- make PROFILE=x86_64-linux -j2 semantics-export \
  EXPORT_DIR=/home/ubuntu/clightforge-semantics-vst-63b9314
python3 -B build/components/identity.py verify-semantics \
  --root /home/ubuntu/clightforge-semantics-vst-63b9314 \
  --expect /home/ubuntu/ClightForge/_build/x86_64-linux/.component-config/semantics-manifest.json
```

两条命令均成功。导出复用了生产者已有语义构建；来源工作树保持干净。
组件身份/重建及许可说明由生产者的 `semantics.json`、README 和核验入口拥有。
VST 的配置读取脚本不是另一套内容身份核验器。

## 重建与安装

在干净 VST 源码树执行以下命令；换底座时须先清理旧 VST 编译产物。
安装目录独立，避免覆盖宿主已有 VST。

```sh
export SEMANTICS_DIR=/home/ubuntu/clightforge-semantics-vst-63b9314
export COQEXTRAFLAGS='-boot -R /home/ubuntu/.opam/rocq90/lib/coq/theories Corelib -R /home/ubuntu/.opam/rocq90/lib/coq/user-contrib/Stdlib Stdlib -R /home/ubuntu/.opam/rocq90/lib/coq/user-contrib/Ltac2 Ltac2'
opam exec --switch=rocq90 -- make -j2 vst progs64
opam exec --switch=rocq90 -- make install \
  INSTALLDIR=/home/ubuntu/vst-clightforge-63b9314/VST
opam exec --switch=rocq90 -- make assumptions.txt
opam exec --switch=rocq90 -- make test-fusion-installed \
  FUSION_VST_ROOT=/home/ubuntu/vst-clightforge-63b9314/VST
```

本轮手动构建使用仓库自身的 `ZLIST=bundled`。opam 配方保留其原来的
`ZLIST=platform`，供给方为 `coq-vst-zlist`；本轮没有修改宿主 opam 安装状态。

构建额外在 bubblewrap mount namespace 中将下列目录屏蔽为空目录：

```text
/home/ubuntu/.opam/rocq90/lib/coq/user-contrib/{compcert,Flocq,VST}
/home/ubuntu/VST-clightforge/{compcert,compcert_new}
```

安装和消费检查还屏蔽了 switch 的 `bin`，仅重新绑定真实的
`coqc coqdep coqtop coqchk coq_makefile rocq`。该环境下 `clightgen` 和
`ccomp` 不可由 PATH 找到。没有卸载宿主包，也没有制造占位 binary。
初次 full 构建使用 `-boot` 和上述目录屏蔽，未调用任何官方生成器。
默认目标用仓库已有 Clight 示例；新的 C 样例只由实际 ClightForge 生成。

## 消费命令

在 VST 根目录用 Bash 定义：

```sh
P=/home/ubuntu/.opam/rocq90/lib/coq
S=/home/ubuntu/clightforge-semantics-vst-63b9314
I=/home/ubuntu/vst-clightforge-63b9314/VST
args=(-q -boot -R "$P/theories" Corelib -R "$P/user-contrib/Stdlib" Stdlib
      -R "$P/user-contrib/Ltac2" Ltac2 -R "$S/compcert" compcert
      -R "$S/Flocq" Flocq -Q "$I" VST)
opam exec --switch=rocq90 -- coqc "${args[@]}" -o .build/vst_api.vo \
  /home/ubuntu/c-code-verify/scripts/toolchain/vst_api.v
opam exec --switch=rocq90 -- coqc "${args[@]}" -o .build/fusion_api.vo \
  /home/ubuntu/c-code-verify/scripts/toolchain/fusion_api.v
/home/ubuntu/ClightForge/_build/x86_64-linux/bin/clightforge \
  util/clightforge/cell.c -o .build/cell.v
opam exec --switch=rocq90 -- coqc "${args[@]}" .build/cell.v
opam exec --switch=rocq90 -- coqc "${args[@]}" -Q .build '' \
  -o .build/verif_cell.vo util/clightforge/verif_cell.v
```

`cell.c` 包含读取和写入 `unsigned int *` 的两个函数；证明给出带可读/可写
share 前提和 `data_at` 所有权的 `semax_body`，而不只是检查生成文件可导入。

## 实际结果

| 检查 | 结果 |
|---|---|
| `make -j2 vst progs64`，全部 full 模式 | 退出 0；301 个 VST 模块重新编译，无旧官方底座 VST `.vo` 复用 |
| `make install` 到独立目录 | 成功；287 个 `.v` 和对应 full `.vo`，与原安装闭包一致 |
| 80 个组件库逐一 Require / Locate | 全部来自选定组件根 |
| 6 个 VST 根 Locate | proofauto、VSU、SeparationLogicAsLogicSoundness、FusionStore、tcb、concurrency.ghosts 全部来自新安装根 |
| CCV `vst_api.v` | full 编译成功 |
| CCV `fusion_api.v` | full 编译成功，包括公开 `MainTheorem.semax_store_exact` 的类型核验 |
| `make assumptions.txt` | 成功，原白名单检查通过 |
| 实际生成的 `cell.v` 及 `verif_cell.v` | full 编译成功，两个 `semax_body` 均 Qed |
| `make test-fusion-installed` | 退出 0；独立重编 9 个 Fusion 客户端、原假设白名单比对和递归 `coqchk` 全部通过 |
| `opam lint coq-vst.opam`、Shell 语法、`git diff --check` | 通过 |
| `FLOCQ=platform` 误配置控制 | 仍显式使用组件的 Flocq |
| 请求 `BITSIZE=32` | 拒绝，报所选组件为 64 位 |
| 组件 Flocq 被屏蔽、宿主旧库仍存在 | 拒绝，报 `missing component file: Flocq/Calc/Bracket.v`，不 fallback |

构建后再次运行生产者内容核验成功；组件未被 VST 构建修改。安装载荷没有
`compcert/` 或 `Flocq/` 副本，没有官方 binary 或 bundled 编译器源码。

开发过程中的问题均保留实际含义：安装枚举的递归 Make 最初未收到命令行
`SEMANTICS_DIR`，已改为显式传递配置；新写的 void-store 样例证明需补上
正常返回的 `entailer!` 义务，未修改已有逻辑；已安装 Fusion 检查首轮被执行器
120 秒上限中断，不能计为通过，随后使用不受该短调用上限影响的运行方式重做。
重做结果为 `Fusion installed clients, assumptions and coqchk: PASS`。
原 Make 全树 coqdep 扫描还会报告历史/可选例子的缺库警告；本轮未裁剪这些
文件。所选 301 模块真实 full 编译成功，不以这类警告后的部分图代替编译验收。

本机原始日志保存在工作树 `.build/`：`full-build.log` / `full-build.exit`、
`install.log`、`locations.log`、`vst-api.log`、`fusion-api.log`、`soundness.log`、
`verif-cell.log`、`fusion-installed.log`，以及两个负控制日志。根目录
`assumptions.txt` 是现有 Make 检查的生成输出，不纳入提交。

## 信任边界

`veric/tcb.v` 的 `VST_sound` 经 `NullExtension`、`SequentialClight2` 和
`semax_prog` 实现链推出 Clight safety。其显式前提包括 `ec_mem_sub`、
`semax_prog` 和成功初始化内存，不是无条件的 C 到机器码正确性结论。
现有 `make assumptions.txt` 已通过：假设包括经典逻辑/实数选择、命题与函数
外延、proof irrelevance、外部函数/内联汇编语义关系，以及
`Clight_core.inline_external_call_mem_events`。未新增公理或 admission。
Fusion 检查的假设集合与原 `util/fusion/assumptions.allowlist` 完全一致；
客户端检查还确认未依赖 `Events.external_functions_sem` 或
`Events.inline_assembly_sem`。实际生成程序的两个函数证明只依赖既有的七项
逻辑/实数选择/外延性假设，没有外部函数语义关系或新增项目公理。
Archi 的 Parameter 与 profile 中的实现值仍保持原来的区别。
