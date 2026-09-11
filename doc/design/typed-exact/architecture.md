# 架构：Fusion typed exact ownership

日期：2026-09-11。**阶段：新接口层的调研/架构与可编译原型；尚未进入公开模块实现。**
用户已确认总体目标；本文的精度语义和首批支持范围待架构确认后进入函数级细化。
调研与实测依据见 [研究记录](research.md)。

开发分支为 **`fusion/vst-2.16-dev`**；实现、设计与审核均在本VST仓库完成。
**`fusion/vst-2.16` 是 CCV 可用上游**，仅在功能、客户端、安装和审计验收完备后从dev合并。
两个分支承担开发/可用集成的不同阶段，不是同时维护两套API版本。

## 1. 目标与验收口径

G1：Agent 的spec/rep使用typed `exact_data_at` / `exact_field_at`，与原reptype和field path一致。
G2：实际store从普通typed资源建立exact精度，不要求caller提前给出本不需要的exact编码。
G3：同成员/重叠成员读取保持完整exact源资源和frame，不把窄读视图当最终完整POST。
G4：正常客户端使用高层入口即可完成body，不展开exact内部，不调用mapsto/memval或手组wand。
G5：原ordinary VST及CCV使用不变，不更改sealed semax或引入假设通道。

**完成判据不是新增一个定义或把示例重排**：必须有不同标识符、成员顺序、share、SEP位置及frame的
新C客户端，证明源只使用公开typed接口。基础设施层允许使用mapsto，客户端不需要。
失败诊断也应尽量停在typed条件：类型/路径/布局/权限/精度前提，而不是要求用户读rmap展开式。

## 2. 谓词与语义合同

### 2.1 公开数据结构

```coq
exact_data_at  {cs : compspecs} (sh : share) (t : type)
              (v : reptype t) (p : val) : mpred
exact_field_at {cs : compspecs} (sh : share) (t : type) (path : list gfield)
              (v : reptype (nested_field_type t path)) (p : val) : mpred
```

没有新业务value record/allocator model，不要求每个union自建typeclass或复制一套proof functor。
类型和layout权威仍是本TU的CompSpecs；public value使用VST原有struct产品、union和类型。

概念定义：

```text
exact_data_at  = ordinary data_at  && exact_representation(该完整typed值)
exact_field_at = ordinary field_at && exact_representation(该子对象typed值，在字段偏移处)
```

普通层与exact层描述同一资源；`&&`不是分离重复所有权。
field_at拥有所选字段区域，不自动拥有完整enclosing struct。

### 2.2 内部编码结构（不要求Agent展开）

- 非volatile By_value叶子：所用memory_chunk上`encode_val`对应的exact资源。
- array：按长度/元素步长递归，使用原array_pred。
- struct：字段typed值与偏移递归，用原struct_data_at_rec_aux和spacer保有padding。
- union：按原reptype的选定成员递归，用原union_data_at_rec_aux保有剩余空间；不是所有成员用`*`同时持有。
- 与原data_at相交保留value_fits、fc等合同；不能无前提假设decode(encode(v))=v对所有type/value成立。

首批operation API仅支持已验的非volatile整数场景。volatile基元的底层定义保留普通unknown资源语义；
它不属于exact编码保证，也不因此获得load/store规则。volatile聚合体/继承属性必须在支持性检查中整体拒绝，
不能只查最终字段的attr就绕过根类型限定。其它type的递归定义不等于声明其操作已支持。

### 2.3 不变量

I1：exact_data_at蕴含同一typed ordinary data_at；exact_field_at同理。
I2：padding资源不丢失，但其未被写入的内容不被固定为0/Undef/某个数组。
I3：ordinary→exact必须来自真实write、真实初始化编码事实或足够强的已有表示；没有无条件cast lemma。
I4：局部写只升级实际覆盖区域；要组装完整exact对象，未改区域也须具有所需exact事实。
I5：借视图保留原谓词/SEP，重叠多视图用蕴含/`&&`，非复制所有权。
I6：tc、cast后值、权限、field_compatible、偏移可表示、bounds、端序义务均保留。
I7：普通forward语义不变；新exact入口显式选用；不加Axiom/Parameter/Admitted绕过。

`exact_data_at ... default_val` 不是普通未知空间的替身。未知/未初始化输入继续使用data_at_/field_at_，
其写入建立新exact值的规则须单独证明，不以“exact underscore”固定未知字节。

## 3. 模块划分与依赖

建议在VST仓库新增以下模块，保持原公开模块不动：

```text
FusionExact / FusionMemvals / FusionViews64
            ↓
FusionDataAt          typed predicate、ordinary投影、基础事实
            ↓
FusionDataAtLemmas    scalar/field/aggregate桥、typed视图、focus/reassembly
            ↓                 FusionStore（原有）
            └──────────┬──────────┘
                   FusionForward    typed semax规则与自动化
                         ↓
                     Fusion        用户导入入口
```

都在 `floyd/` 并接正常 Make/opam。原 `FusionStore` 不反向导入typed层，
避免 `proofauto → sealed soundness → FusionExact` 的已有初始化路径形成环。
用户可以继续使用旧低层接口；新层通过新入口统一导出，不另做v1/v2选择矩阵。

### 3.1 FusionDataAt

Requires：给定合法CompSpecs与typed value。
Ensures：定义上述加强谓词，提供forget/local-facts/isptr等定理与可用hint；
所有事实在kernel中证明，不在tactic里私自假定。
副作用：仅增加库定义/引理及显式导入时的提示，不改原data_at定义。

### 3.2 FusionDataAtLemmas

Requires：操作所需的合法路径、类型、非volatile、权限、边界与端序条件。
Ensures：提供typed普通视图、exact field focus、资源保持与值重组。
实现内部复用现有layout/ramification与FusionViews64，不在每个run重证。
初始scalar low32借用允许显式target fc，最终常用wrapper须从源fc/layout推出它，
不能把原型中暂显式的内部前提全部照搬成Agent额外义务。

### 3.3 FusionForward

Requires：规范semax目标、LOCAL/SEP与足够的typed ownership；支持范围内的真实Clight load/store。
Ensures：派生typed-only语句规则，正常后置保持更新后的typed exact资源或原frame。
对statement的判断仍是原semax，body/call/VSU完全沿用。

拟议用户入口（具体语法在细化时定稿）：

- `forward_exact_store`：识别赋值左值、cast后的值和资源项，执行typed exact store。
- `forward_exact_load`：识别同成员/已登记重叠视图，执行typed load并保持源资源。
- `forward_exact`：仅分派这两种支持语句；未支持时报告，不静默退回普通forward丢精度。
- 允许一个显式资源索引/路径作为歧义消解参数，但常规单一候选时自动推导n与type/chunk。

需要隐藏的内部义务：mapsto_/wand构造、底层frame重排、原型式LOCAL求值手拆、反复rewrite offset0。
仍由用户负责：业务不变量、真正的布局/别名/权限前提、unsupported场景的合同选择。

## 4. 首批操作矩阵

| 场景 | 首批合同 |
|---|---|
| 普通data_at/data_at_标量写入 | 写后exact_data_at；old内容不要求已精确 |
| 整个union通过完整宽成员写入 | 建立选定成员的exact_data_at，保有完整union及padding；layout条件机械化求解 |
| 相同位置宽写→低字重叠读 | 返回低字typed值，保留原exact对象；小端与目标合法性条件不丢 |
| 高字/拆分视图 | 使用原FusionViews64显式偏移界，通过typed桥接后提供；不套用低字的较弱前提 |
| struct已有exact字段的局部更新 | 可focus/update/reassemble；其它字段与padding保持 |
| ordinary struct仅写一个字段 | 只建立该字段exact与原typed frame；不能声称整个struct全部exact |
| 任意业务rep不透明包装 | 用户可注册typed展开/视图，库不猜它的语义；初始验收以直接typed谓词为主 |
| volatile、原VST不支持的By_copy赋值、未登记重解释 | 明确不支持，不因有predicate定义就提供假规则 |

“首批”是本次接口实现的范围，不是按旧/新版library选择的兼容矩阵。

## 5. 核心协作论证

- G1：DataAt负责类型和值语义；原typed conjunct直接维护I1及local facts。
- G2：Lemmas把普通typed写权接到既有exact store；Forward在真实Sassign处应用，所以I3不被绕过。
- G3：Lemmas从源表示给出借用视图；stock load仍保持原SEP，Forward只更新LOCAL，维护I2/I4/I5。
- G4：Forward自动处理库可推导条件；typed-only客户端测试覆盖不出现后端义务，示例代码简化只是结果。
- G5：所有派生规则引用同一sealed semax/现有kernel证明，原predicate/tactic不替换，默认opam路径不增加依赖。

关键假设：所选工具链支持现有FusionStore与整数视图；CompSpecs/字段布局来自实际Clight；
用户声称的业务输入域与资源前提需通过原CCV分析/人审流程。新层不替人判断规约意图。

## 6. 分步实施与验证

1. **架构确认**：确认精度边界、首批范围与公开模块分层。本次已形成14条真Qed设计探针，非公开API。
2. **细化与事前契约审核**：固定全部public签名、tactic输入输出、失败分类及每个资源分支；
   expectations由独立审阅者先读契约抽取，之后才写生产实现。
3. **谓词/结构地基**：新模块 definitions、forget/local-facts、scalar/array/struct/union展开与资源保持，零admit。
4. **typed语句桥与自动化**：先规则再tactic，禁止仅提供十几个原始参数的壳就宣称Agent友好。
5. **新客户端验收**：至少两个union成员顺序、任意writable/readable share、非0 SEP位置、独立frame、
   padding struct；正常proof无backend名/展开。完整普通VST回归、assumptions与coqchk。
6. **CCV消费**：在独立环境真实安装、补项目级typed API probe/Skill入口，新run重新建区，
   不给普通opam用户强制装typed exact层，不热改存量run。

### 关键负例

- ordinary representation不能直接升级exact；保留原Fragment编码反例，不能用失败tactic代替数学反例。
- narrow store不能推出未写字节的确定宽值；padding未知不能断言为零。
- 重叠视图不能复制SEP；错误目标对齐、越界offset、readonly store、大端低字误用要拒绝。
- scalar初值Vundef的普通未知ownership仍允许合法覆盖写；不能因为新谓词而加强caller PRE。
- partial ordinary aggregate不得被误组装成全部exact；frame sentinel必须在POST可见。
- 不同字段名/顺序/SEP位置不能迫使用户复制模板或手造mapsto桥。

静态检查客户端无后端token只是工程回归，不是完整语义安全边界；真正保证仍是全部定理kernel接受和前提审查。

## 7. 当前状态与下一出口

已完成调研、概念定义与关键可行性探针；正式模块、全路径typed wrappers、自动化、客户端body与安装尚未完成。
原型的scalar语句规则虽然已Qed，但它仍是有多个参数的基础规则，不能据此标记G4完成。

下一出口是确认本架构，特别是：**exact保证有效非volatile值单元的编码、padding保有但不固定；
局部write只升级实际覆盖区域**。这两条是新谓词和POST的公开语义，不应在实现中隐式决定。

## 8. 架构审查后的明确化

独立审查见 [architecture-review.md](architecture-review.md)：未发现已坐实的blocking语义错误，
指出以下必须在下一阶段消解的结构性义务。

1. **分解不是一般分配律**：不能使用
   `(P * Q) && (R * S) = (P && R) * (Q && S)` 这类一般不成立的等式。
   typed/精确两种描述要使用一致的字段地址、范围及share证明可按同一资源分割。
   现有4个layout探针只检查exact_representation的布局，不是该定理的证明。
   生产谓词定型前先证明具有padding与frame的字段focus/reassembly；若改为叶子级加强表示，
   必须证明它与已确认语义等价，不能偷偷加强输入域；做不到须回到架构裁决。
2. **首批32/64位都支持实际写**：包括union窄成员写；它返回窄成员编码+保有未知suffix，
   不生成一个确定宽值。高字/拆分属于首批typed定理，额外偏移界保留；自动化优先覆盖完整宽写→低读，
   其余typed视图可显式调用，仍不得要求客户端展开到mapsto。
3. **混合精度必须可继续使用**：字段级exact与ordinary frame是高层API可消费的POST形式，
   不能让第一次写入成功、下一次读写却需要客户端手工拼底层桥。验收必须包含连续操作，
   以及尝试读未被确定的suffix时的准确失败诊断。
4. **可构造性与成本**：除了forget投影，还须从真实store构造非空typed exact实例，
   分别核值域、权限、frame和编译成本；不能仅以“强前提蕴含ordinary”证明接口有用。

上述是架构建议的明确化，不把尚未完成的字段组合和Agent自动化标成已验。
