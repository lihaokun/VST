(* 整数列表的机器表示规范化与存在性重建。
   命名空间 [IntegerList]，公开四套实际定义（s32/u32/s64/u64），
   每套 4 定义 6 引理：norm_m/encode_m/values_m/range_m 与
   norm_m_repr/norm_m_length/norm_m_range/norm_m_values/recover_m/rebuild_m。
   轻量导入：functional_base（已导出 VST.zlist.sublist）；不导入 proofauto。
   norm_* 只做机器表示规范化，不保证输入输出 Z 相等；
   recover_* 只接受 Vint/Vlong 形状的列表，拒绝 Vundef/Vptr/其余构造。
   rebuild_m 是调用后规范化的存在性入口（witness = norm_m lo，
   调用形态 destruct (rebuild_m lo) as [lo' […]]; replace 编码表）；纯由上方
   公开引理组装，无新数学。restore（裸 val 列表折回消费方抽象 rep，
   data_at … ⊢ EX fv, <抽象 rep> sh fv p）依赖消费方自己的 Rep 定义：
   本模块不预知任何消费方的 Rep，restore 由消费方以 recover_m 的
   values_m zs = vs 等式（data_at 值表可换）自行配出。 *)

Set Default Timeout 300.

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import VST.floyd.functional_base.

Local Open Scope Z_scope.
Import ListNotations.

Module IntegerList.

(* Step P4: s32 模式 —— W=int, repr=Int.repr, read=Int.signed,
   ctor=Vint, 界 Int.min_signed..Int.max_signed。 *)

Definition norm_s32 (zs : list Z) : list Z :=
  map (fun z => Int.signed (Int.repr z)) zs.

Definition encode_s32 (zs : list Z) : list int :=
  map Int.repr zs.

Definition values_s32 (zs : list Z) : list val :=
  map Vint (encode_s32 zs).

Definition range_s32 (z : Z) : Prop :=
  Int.min_signed <= z <= Int.max_signed.

(* 编码不变：repr 与 signed/repr 往返逐项对齐。 *)
Lemma norm_s32_repr : forall zs : list Z,
  encode_s32 (norm_s32 zs) = encode_s32 zs.
Proof.
  intros zs. unfold norm_s32, encode_s32.
  rewrite map_map. apply map_ext. intros z. unfold Basics.compose.
  apply Int.repr_signed.
Qed.

(* 长度不变。 *)
Lemma norm_s32_length : forall zs : list Z,
  Zlength (norm_s32 zs) = Zlength zs.
Proof.
  intros zs. unfold norm_s32. apply Zlength_map.
Qed.

(* 规范化后逐项落入 signed 32 位闭区间。 *)
Lemma norm_s32_range : forall zs : list Z,
  Forall range_s32 (norm_s32 zs).
Proof.
  intros zs. apply Forall_map. apply Forall_forall. intros z _.
  unfold Basics.compose, range_s32.
  pose proof (Int.signed_range (Int.repr z)). lia.
Qed.

(* 与 encode 的复合在规范化前后不变。 *)
Lemma norm_s32_values : forall zs : list Z,
  values_s32 (norm_s32 zs) = values_s32 zs.
Proof.
  intros zs. unfold values_s32. f_equal. apply norm_s32_repr.
Qed.

(* 已定义 Vint 形状的 val 列表可恢复为一列落在范围内的 Z，
   编码后与原列表一致；尾表长度严格递减，其余 val 构造
   （Vundef/Vptr/Vlong/浮点等）不满足形状前提，不设默认分支。 *)
Lemma recover_s32 : forall vs : list val,
  Forall (fun v => exists w : int, v = Vint w) vs ->
  exists zs : list Z,
    values_s32 zs = vs /\ Zlength zs = Zlength vs /\ Forall range_s32 zs.
Proof.
  induction vs as [| v vs IH]; intros HF.
  - exists []. repeat split; reflexivity || constructor.
  - pose proof (Forall_inv_tail HF) as HFT.
    apply Forall_inv in HF as [w Hw]. subst v.
    destruct (IH HFT) as [zs' [Hvals [Hlen Hrange]]].
    exists (Int.signed w :: zs'). repeat split.
    + assert (Hhead : values_s32 (Int.signed w :: zs')
                      = Vint w :: values_s32 zs').
      { unfold values_s32, encode_s32. simpl.
        rewrite Int.repr_signed. reflexivity. }
      rewrite Hhead, Hvals. reflexivity.
    + simpl. rewrite !Zlength_cons. rewrite Hlen. reflexivity.
    + unfold range_s32.
      apply Forall_cons; [apply Int.signed_range | exact Hrange].
Qed.

(* 调用后规范化的存在性入口：与 lo 编码相等、
   长度相等、逐项入界的 lo' 存在；witness 即 norm_s32（= playbook witness）。 *)
Lemma rebuild_s32 : forall lo : list Z,
  exists lo' : list Z,
    encode_s32 lo' = encode_s32 lo /\
    Zlength lo' = Zlength lo /\
    Forall range_s32 lo'.
Proof.
  intros lo. exists (norm_s32 lo). repeat split.
  - apply norm_s32_repr.
  - apply norm_s32_length.
  - apply norm_s32_range.
Qed.

(* Step P4: u32 模式 —— read=Int.unsigned, 界 0..Int.max_unsigned。 *)

Definition norm_u32 (zs : list Z) : list Z :=
  map (fun z => Int.unsigned (Int.repr z)) zs.

Definition encode_u32 (zs : list Z) : list int :=
  map Int.repr zs.

Definition values_u32 (zs : list Z) : list val :=
  map Vint (encode_u32 zs).

Definition range_u32 (z : Z) : Prop :=
  0 <= z <= Int.max_unsigned.

Lemma norm_u32_repr : forall zs : list Z,
  encode_u32 (norm_u32 zs) = encode_u32 zs.
Proof.
  intros zs. unfold norm_u32, encode_u32.
  rewrite map_map. apply map_ext. intros z. unfold Basics.compose.
  apply Int.repr_unsigned.
Qed.

Lemma norm_u32_length : forall zs : list Z,
  Zlength (norm_u32 zs) = Zlength zs.
Proof.
  intros zs. unfold norm_u32. apply Zlength_map.
Qed.

Lemma norm_u32_range : forall zs : list Z,
  Forall range_u32 (norm_u32 zs).
Proof.
  intros zs. apply Forall_map. apply Forall_forall. intros z _.
  unfold Basics.compose, range_u32.
  pose proof (Int.unsigned_range (Int.repr z)).
  unfold Int.max_unsigned, Int.modulus in *. lia.
Qed.

Lemma norm_u32_values : forall zs : list Z,
  values_u32 (norm_u32 zs) = values_u32 zs.
Proof.
  intros zs. unfold values_u32. f_equal. apply norm_u32_repr.
Qed.

Lemma recover_u32 : forall vs : list val,
  Forall (fun v => exists w : int, v = Vint w) vs ->
  exists zs : list Z,
    values_u32 zs = vs /\ Zlength zs = Zlength vs /\ Forall range_u32 zs.
Proof.
  induction vs as [| v vs IH]; intros HF.
  - exists []. repeat split; reflexivity || constructor.
  - pose proof (Forall_inv_tail HF) as HFT.
    apply Forall_inv in HF as [w Hw]. subst v.
    destruct (IH HFT) as [zs' [Hvals [Hlen Hrange]]].
    exists (Int.unsigned w :: zs'). repeat split.
    + assert (Hhead : values_u32 (Int.unsigned w :: zs')
                      = Vint w :: values_u32 zs').
      { unfold values_u32, encode_u32. simpl.
        rewrite Int.repr_unsigned. reflexivity. }
      rewrite Hhead, Hvals. reflexivity.
    + simpl. rewrite !Zlength_cons. rewrite Hlen. reflexivity.
    + unfold range_u32. apply Forall_cons.
      * pose proof (Int.unsigned_range w).
        unfold Int.max_unsigned, Int.modulus in *. lia.
      * exact Hrange.
Qed.

(* 存在性规范化：witness = norm_u32。 *)
Lemma rebuild_u32 : forall lo : list Z,
  exists lo' : list Z,
    encode_u32 lo' = encode_u32 lo /\
    Zlength lo' = Zlength lo /\
    Forall range_u32 lo'.
Proof.
  intros lo. exists (norm_u32 lo). repeat split.
  - apply norm_u32_repr.
  - apply norm_u32_length.
  - apply norm_u32_range.
Qed.

(* Step P4: s64 模式 —— W=int64, read=Int64.signed,
   ctor=Vlong, 界 Int64.min_signed..Int64.max_signed。 *)

Definition norm_s64 (zs : list Z) : list Z :=
  map (fun z => Int64.signed (Int64.repr z)) zs.

Definition encode_s64 (zs : list Z) : list int64 :=
  map Int64.repr zs.

Definition values_s64 (zs : list Z) : list val :=
  map Vlong (encode_s64 zs).

Definition range_s64 (z : Z) : Prop :=
  Int64.min_signed <= z <= Int64.max_signed.

Lemma norm_s64_repr : forall zs : list Z,
  encode_s64 (norm_s64 zs) = encode_s64 zs.
Proof.
  intros zs. unfold norm_s64, encode_s64.
  rewrite map_map. apply map_ext. intros z. unfold Basics.compose.
  apply Int64.repr_signed.
Qed.

Lemma norm_s64_length : forall zs : list Z,
  Zlength (norm_s64 zs) = Zlength zs.
Proof.
  intros zs. unfold norm_s64. apply Zlength_map.
Qed.

Lemma norm_s64_range : forall zs : list Z,
  Forall range_s64 (norm_s64 zs).
Proof.
  intros zs. apply Forall_map. apply Forall_forall. intros z _.
  unfold Basics.compose, range_s64.
  pose proof (Int64.signed_range (Int64.repr z)). lia.
Qed.

Lemma norm_s64_values : forall zs : list Z,
  values_s64 (norm_s64 zs) = values_s64 zs.
Proof.
  intros zs. unfold values_s64. f_equal. apply norm_s64_repr.
Qed.

Lemma recover_s64 : forall vs : list val,
  Forall (fun v => exists w : int64, v = Vlong w) vs ->
  exists zs : list Z,
    values_s64 zs = vs /\ Zlength zs = Zlength vs /\ Forall range_s64 zs.
Proof.
  induction vs as [| v vs IH]; intros HF.
  - exists []. repeat split; reflexivity || constructor.
  - pose proof (Forall_inv_tail HF) as HFT.
    apply Forall_inv in HF as [w Hw]. subst v.
    destruct (IH HFT) as [zs' [Hvals [Hlen Hrange]]].
    exists (Int64.signed w :: zs'). repeat split.
    + assert (Hhead : values_s64 (Int64.signed w :: zs')
                      = Vlong w :: values_s64 zs').
      { unfold values_s64, encode_s64. simpl.
        rewrite Int64.repr_signed. reflexivity. }
      rewrite Hhead, Hvals. reflexivity.
    + simpl. rewrite !Zlength_cons. rewrite Hlen. reflexivity.
    + unfold range_s64.
      apply Forall_cons; [apply Int64.signed_range | exact Hrange].
Qed.

(* 存在性规范化：witness = norm_s64。 *)
Lemma rebuild_s64 : forall lo : list Z,
  exists lo' : list Z,
    encode_s64 lo' = encode_s64 lo /\
    Zlength lo' = Zlength lo /\
    Forall range_s64 lo'.
Proof.
  intros lo. exists (norm_s64 lo). repeat split.
  - apply norm_s64_repr.
  - apply norm_s64_length.
  - apply norm_s64_range.
Qed.

(* Step P4: u64 模式 —— read=Int64.unsigned, 界 0..Int64.max_unsigned。 *)

Definition norm_u64 (zs : list Z) : list Z :=
  map (fun z => Int64.unsigned (Int64.repr z)) zs.

Definition encode_u64 (zs : list Z) : list int64 :=
  map Int64.repr zs.

Definition values_u64 (zs : list Z) : list val :=
  map Vlong (encode_u64 zs).

Definition range_u64 (z : Z) : Prop :=
  0 <= z <= Int64.max_unsigned.

Lemma norm_u64_repr : forall zs : list Z,
  encode_u64 (norm_u64 zs) = encode_u64 zs.
Proof.
  intros zs. unfold norm_u64, encode_u64.
  rewrite map_map. apply map_ext. intros z. unfold Basics.compose.
  apply Int64.repr_unsigned.
Qed.

Lemma norm_u64_length : forall zs : list Z,
  Zlength (norm_u64 zs) = Zlength zs.
Proof.
  intros zs. unfold norm_u64. apply Zlength_map.
Qed.

Lemma norm_u64_range : forall zs : list Z,
  Forall range_u64 (norm_u64 zs).
Proof.
  intros zs. apply Forall_map. apply Forall_forall. intros z _.
  unfold Basics.compose, range_u64.
  pose proof (Int64.unsigned_range (Int64.repr z)).
  unfold Int64.max_unsigned, Int64.modulus in *. lia.
Qed.

Lemma norm_u64_values : forall zs : list Z,
  values_u64 (norm_u64 zs) = values_u64 zs.
Proof.
  intros zs. unfold values_u64. f_equal. apply norm_u64_repr.
Qed.

Lemma recover_u64 : forall vs : list val,
  Forall (fun v => exists w : int64, v = Vlong w) vs ->
  exists zs : list Z,
    values_u64 zs = vs /\ Zlength zs = Zlength vs /\ Forall range_u64 zs.
Proof.
  induction vs as [| v vs IH]; intros HF.
  - exists []. repeat split; reflexivity || constructor.
  - pose proof (Forall_inv_tail HF) as HFT.
    apply Forall_inv in HF as [w Hw]. subst v.
    destruct (IH HFT) as [zs' [Hvals [Hlen Hrange]]].
    exists (Int64.unsigned w :: zs'). repeat split.
    + assert (Hhead : values_u64 (Int64.unsigned w :: zs')
                      = Vlong w :: values_u64 zs').
      { unfold values_u64, encode_u64. simpl.
        rewrite Int64.repr_unsigned. reflexivity. }
      rewrite Hhead, Hvals. reflexivity.
    + simpl. rewrite !Zlength_cons. rewrite Hlen. reflexivity.
    + unfold range_u64. apply Forall_cons.
      * pose proof (Int64.unsigned_range w).
        unfold Int64.max_unsigned, Int64.modulus in *. lia.
      * exact Hrange.
Qed.

(* 存在性规范化：witness = norm_u64。 *)
Lemma rebuild_u64 : forall lo : list Z,
  exists lo' : list Z,
    encode_u64 lo' = encode_u64 lo /\
    Zlength lo' = Zlength lo /\
    Forall range_u64 lo'.
Proof.
  intros lo. exists (norm_u64 lo). repeat split.
  - apply norm_u64_repr.
  - apply norm_u64_length.
  - apply norm_u64_range.
Qed.

End IntegerList.
