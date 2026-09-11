# Run2 作为 typed exact 接口的对照实验

日期：2026-09-11。**开发实验，不是新cert，不修改原run或基线归档。**

## 原始基线

CCV 已将使用可用上游 `fusion/vst-2.16` @ `f21783d` 的第二轮归档：
[原始归档](https://github.com/lihaokun/c-code-verify/tree/5d7aa86/verifications/union-word-view-memory_safety_leak_freedom_lifecycle-2026-09-11)。
原工作区交付commit为 `0cccc8e848c8e9578062f3995d20637e73e34df7`，18份最终Coq源。
归档已有独立clean replay和原证书/报告，保持原字节；下面实验不复用原证书给变体背书。

## 实验 A：排除现有工具未被使用造成的样板成本

[run2_reuse.py](run2_reuse.py) 从归档复制proof源到 `.build`，只修改4条辅助引理的Proof体：

| 引理 | 原Proof体行数 | 简化后 | 复用 |
|---|---:|---:|---|
| wv_loword_unsigned | 4 | 1 | Int.unsigned_repr_eq |
| wv_load_low32_address | 17 | 2 | go_lowerx / unfold_lift / LOCAL等式 / entailer! |
| wv_store_whole_address | 14 | 2 | 同上 |
| wv_store_whole_eval | 9 | 2 | 同上 |
| 合计 | 44 | 7 | 减少37行 |

具体funspec、rep、goal claim、C/Clight以及原定理陈述均不改。
18文件clean build通过（20.701s），admit=0，两个root的actual axioms exact-set不变，
coqchk通过（259.227s）。完整记录：[run2-reuse-result.json](run2-reuse-result.json)。

这不是typed层目标的替代品。它只建立“已经充分使用当前库”的比较基线，
避免将已有go_lowerx就能消除的代码误当作必须新增定理才能解决的问题。

## 实验 B：在真实body中接入typed scalar-store原型

同一脚本加 `--typed-store`：仍保持原规约不变，但以原型
`TypedExactPrototype.semax_store_exact_data_at_tulong` 替换body中的低层store调用。
原型是本目录上级prototypes中的开发代码，不是已安装公开模块。

路径：

```text
旧union data_at PRE
  → 用已有wv_initializer转成scalar typed PRE
  → typed scalar-store得到exact_data_at tulong
  → typed_wide_to_wv_exact转回旧run所需表示
  → 旧load包装继续读取，完成同一body/VSU
```

### 结果

- 新增原型模块后19个源全量重编通过，body/main/VSU/goal仍闭合；
  两个结论根的actual axioms与原归档精确相等，coqchk通过。
- store body的Proof体从21行变19行，但新增10行转换桥，另有import/空行。
- 两个修改文件的完整行数对比：

| 文件 | 原run | 实验A | 实验B |
|---|---:|---:|---:|
| lemmas_word_view.v | 187 | 169 | 169 |
| verif_word_view_word_view_store_low.v | 121 | 102 | 112 |
| 合计 | 308 | 271 | 281 |

**只接一个typed scalar wrapper，并没有让这个union客户端进一步变短。**
它确实能服务真实body，但当前仍需要类型转换和回接旧rep。
这一额外成本部分来自“原规约保持不变”的迁移要求，不意味着最终直接使用typed union API的客户端也要保留该桥。

第一次尝试在 `replace_nth n R` 的反向推断上失败：Coq未从后置推断R；显式给
`R := [data_at Ews tulong (Vlong c0) p]` 后第二次通过。
这是前端应从当前SEP提取的参数，不应成为Agent反复猜测的义务。
失败尝试保留在本机 `.build/run2-typed-store/`，不计为通过。
成功记录：[run2-typed-store-result.json](run2-typed-store-result.json)。
成功clean build为21.513s，coqchk为260.756s；这是单次实测，不据此给出性能加速结论。

## 对架构的影响

1. **原型不是最终接口**：需要直接处理union/field typed ownership，不能只给scalar wrapper让Agent每次手造前后桥。
2. **仍须先证结构组合**：B把union通过已证的特定layout等式转为scalar，没有证明一般
   `(ordinary aggregate) && (exact aggregate)` 的同步切分/重组。原S1风险尚未消除。
3. **混合精度的连续使用仍是必要场景**：此次单次完整宽写不覆盖partial ordinary struct的问题，不能据此放宽S2。
4. **自动化必须负责可推导参数**：SEP索引/R、字段路径、cast后的值与地址求值由前端读取当前目标；
   用户只提供真正的业务不变量与缺失资源事实。
5. **保留正确精度边界**：padding保有但未知；局部写不能提升未写区域。客户端行数不能反过来决定把POST写强或偷加强PRE。

## 复现

在本VST开发仓库根执行，参数指向已下载的CCV归档目录：

```sh
python3 doc/design/typed-exact/experiments/run2_reuse.py <archive> --output .build/run2-reuse
python3 doc/design/typed-exact/experiments/run2_reuse.py <archive> --typed-store --output .build/run2-typed-store
```

输出目录必须新建，已有结果不覆盖；输出含变体proof、精确patch、编译日志和result.json。
现有 `vst-fusion` 必须具有原始Fusion模块，`--switch`可选其它匹配环境。
本脚本不运行FSM、不签发证书、不写归档或安装库；副本从零编译，不复制.vo。
