# Fusion typed exact 层：调研与可行性探针

日期：2026-09-11。用户已确认方向：Fusion 应提供 Agent 可直接使用的 typed 接口，
而不是要求每个 run 展开到 mapsto 再手工拼装。本文是开发者调研，已发布接口的使用说明见
[doc/fusion.md](../../fusion.md)；本WIP在 `fusion/vst-2.16-dev` 开发，验收后才合并到可用上游。

## 1. 目标

- 用户规格使用 `exact_data_at` / `exact_field_at` 与原 `reptype`、字段路径。
- 普通 typed ownership 能在实际写入后获得 exact typed ownership。
- 重叠读取保持完整 exact 资源及外部 frame；正常客户端不用 mapsto/memval/wand 后端接口。
- Agent 的自动化入口能从 Clight、LOCAL、SEP 推导地址、值、类型和目标资源，失败返回 typed 层诊断。
- 原 ordinary store、semax_body、VSU、opam 默认路径保持不变。

## 2. 已有实现可以复用什么

| VST 源码位置 | 可复用能力 |
|---|---|
| `floyd/data_at_rec_lemmas.v:50–58` | `type_func` 遍历数组、结构体、union，并调用原 aggregate/spacer 构造器 |
| `floyd/aggregate_pred.v` | array_pred、struct/union_data_at_rec_aux、withspacer，布局和padding已经集中定义 |
| `floyd/field_at.v:124–126` | field_at = field_compatible + 子对象谓词的字段偏移 |
| `floyd/field_at.v:2384–2459` | typed field/data_at ↔ ordinary mapsto 的已有桥及ramification |
| `floyd/loadstore_field_at.v:44–171` | 以field_at作为public前提的load/store wrapper，证明内部使用mapsto；可作为新层的模式参考 |
| `floyd/nested_loadstore.v` | 普通typed聚合体的字段focus/update与值注入 |
| `floyd/FusionStore.v` | 已证 exact store wrapper；继续作为内部实现，不需要新sealed判断 |
| `floyd/FusionViews64.v` | 已证低字/高字/宽值视图，typed层只负责安全组合，不重证字节算术 |

结论：没有必要重新实现一套C布局算法；缺口是typed precision、字段装配和Agent前端。

## 3. 推荐的谓词结构

先采用以下加强型定义，保留原VST typed合同：

```text
exact_data_at sh t v p
  = data_at sh t v p && exact_representation sh t v p

exact_field_at sh t path v p
  = field_at sh t path v p &&
    exact_representation(子类型, v, 子地址)
```

`&&` 对同一份资源加约束，不是 `*` 的两份重叠所有权。
内部 exact_representation 复用type_func和aggregate辅助构造器，在非volatile scalar叶子替换为exact编码资源。
普通typed conjunct保证field_compatible、value_fits和forget定理不依赖尚未证明的全类型decode/encode恒等式。
这也避免仅用 `!!field_compatible && exact_mapsto` 就对所有C类型贸然声称读回相同值。

与直接替换原data_at的比较：加强定义是可选、相容的；原predicate语义不变。
与只增加几个mapsto别名的比较：新层必须继续有typed store/load规则和自动化，定义本身不是完成标准。
此组合定义会在term中保留ordinary与exact两种描述；第一轮编译测量若显示明显重复遍历成本，再在保持公开合同下
证明内部归约等价，不在未测前凭感觉换架构。

## 4. 两条不可省略的精度边界

### 4.1 exact 不等于“padding也被固定成某串字节”

struct按各字段编码，union按typed值选择的成员编码；其余padding空间通过原spacer保有，内容未被凭空固定。
例如8字节union选择64位成员时整8字节编码确定；选择32位成员时，只确定4字节，剩余4字节仍保有但未知。
因而不能从后者无条件证明一个确定的64位读取。

### 4.2 局部写不能把其它ordinary字段一起升级成exact

ordinary struct的一个字段被写入，只给出该字段的新编码；未写字段依然可能具有普通decode允许的不同表示。
要返回完整exact struct，未改字段必须原先已经exact，或本段执行确实建立了全部所需编码。
其它情况使用typed字段级exact资源与原ordinary frame组合，禁止通过错误的全对象升级获得假证明。

此外，`exact_data_at ... Vundef` 不应被当作任意未初始化空间；普通未知资源继续用 `data_at_` / `field_at_`。
不新增一个把default_val固定成Undef字节的“exact_data_at_”来冒充未知内容。

## 5. 本次独立 Coq 探针

探针源：[typed_exact_prototype.v](prototypes/typed_exact_prototype.v)、
[layout_probes.v](prototypes/layout_probes.v)、
[layout_cases.c](prototypes/layout_cases.c)。
命名空间 `TypedExactPrototype`，不是已安装模块。

已实际编译并经 `coqchk` 核验 **14 条 Qed**：

- exact_data_at / exact_field_at 的ordinary投影；generic data_at local-facts。
- tuint/tulong scalar编码归约；exact64 + typed兼容事实构造exact_data_at。
- typed low32借用，以及与完整exact源资源同时成立的借用形式。
- ordinary scalar data_at（包括old=Vundef的实例）到exact64后置所需的内部ramification。
- **typed-only public statement 的scalar store wrapper**：调用者的声明中不出现mapsto、chunk或wand，
  对任意share、SEP位置、P/Q/R、表达式成立；内部从现有semax_store_exact_nth_ram派生。
- 两个字段顺序相反的union，选择wide成员时都归约到8字节exact表示。
- 选择low成员时，严格保留额外4字节未知padding。
- 含tag、padding、union payload的struct，其各区域分离布局正确。

探针的类型/布局case是新建的独立小C，不import任何业务run的rep/body。
审查使用实际安装 `vst-fusion`（公共源码f21783d）；没有修改安装库、VST源码或已完成run。
打印的低字/store根Assumptions只含原VST经典公理，未新增外部正确性假设。

复现：从VST根把 `doc/design/typed-exact/prototypes/` 下这三个源文件复制到
`.build/typed-exact/`，在该目录运行：

```bash
opam exec --switch=vst-fusion -- coqc -q typed_exact_prototype.v
opam exec --switch=vst-fusion -- clightgen -normalize -canonical-idents layout_cases.c
opam exec --switch=vst-fusion -- coqc -q layout_cases.v
opam exec --switch=vst-fusion -- coqc -q layout_probes.v
opam exec --switch=vst-fusion -- coqchk -silent typed_exact_prototype layout_probes
```

本次实测给coqc外层120s、句级30s，coqchk外层300s；这些是探针预算，不改生产编译纪律。
尚未证明：所有类型的generic字段focus/reassembly、完整typed cross-field语句规则、Agent自动化和新客户端body。
不能把14条探针通过说成新接口层已经完成或已部署。

## 6. 首批支持与建议顺序

语义定义按原type_func处理类型树；**第一批可用操作**聚焦非volatile tuint/tulong、
相应scalar字段与union成员、外部frame及已具备前提的struct字段组合。
其它整数宽度、浮点/pointer重解释、任意端序跨读、volatile操作和整struct/union赋值不因有谓词定义而自动获得规则。
原型中volatile基元保留原memory_block分支，不宣传它有exact编码；正式操作入口要在支持检查中明确拒绝volatile路径。

先确认架构与上述精度边界，再细化：谓词/结构引理 → typed视图/字段规则 → typed语句规则 →
自动化 → 多布局客户端与完整VST/CCV验收。实际代码的proofauto/import DAG必须保持无环。
