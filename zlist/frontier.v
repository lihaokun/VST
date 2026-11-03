(* M1：纯列表前沿（zlist/frontier.v）
   提供公开定义 filled / prefix_holds，以及十条公开引理：
   filled_length、filled_empty、filled_full、filled_step、filled_map、
   filled_map_step、filled_next、prefix_holds_sublist、prefix_holds_store、
   frontier_Forall_step。
   索引一律为 Z；只有读 Znth 的接口要求 Inhabitant 实例。
   filled_map_step 的尾值 d 属于 B，不要求 d 在 f 的像内；
   prefix_holds_store 在 j = i（拒绝分支）时不要求新写值满足 Q。 *)
Set Default Timeout 300.

From Stdlib Require Import ZArith Lists.List Lia.
Import ListNotations.
Require Import VST.zlist.sublist.
Import SublistInternalLib.

Local Open Scope Z_scope.

(* ================= 公开定义 ================= *)

(* 定义 1/2：把前缀 prefix 用默认尾值 d 补齐到总长 n。 *)
Definition filled {A} (prefix : list A) (d : A) (n : Z) : list A :=
  prefix ++ Zrepeat d (n - Zlength prefix).

(* 定义 2/2：xs 的前 i 项都满足 Q。 *)
Definition prefix_holds {A} {dA : Inhabitant A}
    (Q : A -> Prop) (i : Z) (xs : list A) : Prop :=
  forall k : Z, 0 <= k < i -> Q (Znth k xs).

(* ================= 内部辅助引理（不属于公开接口） ================= *)

(* 正长度的 Zrepeat 可拆出头部，供 filled_step 使用。 *)
Lemma Zrepeat_cons_pos {A} : forall (d : A) n,
  0 < n -> Zrepeat d n = d :: Zrepeat d (n - 1).
Proof.
  intros d n H.
  assert (E : n = 1 + (n - 1)) by lia.
  rewrite E at 1.
  rewrite <- (Zrepeat_app 1 (n - 1) d) by lia.
  reflexivity.
Qed.

(* 局部 Forall 的拼接引入（避免依赖 stdlib 版本差异）。 *)
Lemma Forall_app_intro {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; simpl; intros H1 H2.
  - exact H2.
  - inversion H1; subst. constructor; [assumption | apply IH; assumption].
Qed.

(* 拼接的右半提取：Forall P (l1 ++ l2) 蕴含 Forall P l2。 *)
Lemma Forall_app_inv_r {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P (l1 ++ l2) -> Forall P l2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros l2 H.
  - exact H.
  - simpl in H. inversion H; subst. apply IH. assumption.
Qed.

(* ================= 公开引理：filled 族 ================= *)

(* 已填长度恰为 n（不制造越界默认元素）。 *)
Lemma filled_length {A} : forall (prefix : list A) d n,
  Zlength prefix <= n -> Zlength (filled prefix d n) = n.
Proof.
  intros prefix d n H. unfold filled.
  rewrite Zlength_app, Zlength_Zrepeat by lia. lia.
Qed.

(* 空前缀退化为纯尾段。 *)
Lemma filled_empty {A} : forall (d : A) n,
  filled [] d n = Zrepeat d n.
Proof.
  intros d n. unfold filled.
  rewrite Zlength_nil, Zminus_0_r. apply app_nil_l.
Qed.

(* 满前缀不再补任何元素。 *)
Lemma filled_full {A} : forall (prefix : list A) d,
  filled prefix d (Zlength prefix) = prefix.
Proof.
  intros prefix d. unfold filled.
  rewrite Z.sub_diag, Zrepeat_neg by lia. apply app_nil_r.
Qed.

(* 前沿推进：在旧前沿位置写入 v 等价于把 v 接进前缀。
   前提要求严格剩余长度；不满足时本引理不适用（见测试的负例）。 *)
Lemma filled_step {A} : forall (prefix : list A) d n v,
  Zlength prefix < n ->
  upd_Znth (Zlength prefix) (filled prefix d n) v =
  filled (prefix ++ [v]) d n.
Proof.
  intros prefix d n v H. unfold filled.
  pose proof (Zlength_Zrepeat A d (n - Zlength prefix) ltac:(lia)) as HLr.
  rewrite upd_Znth_app2 by lia.
  rewrite Z.sub_diag.
  rewrite Zrepeat_cons_pos by lia.
  rewrite upd_Znth0.
  rewrite Zlength_app.
  replace (Zlength [v]) with 1 by reflexivity.
  rewrite <- app_assoc.
  f_equal.
  replace (n - (Zlength prefix + 1)) with (n - Zlength prefix - 1) by lia.
  reflexivity.
Qed.

(* map 与 filled 交换；f 任意，不要求单射。 *)
Lemma filled_map {A B} : forall (f : A -> B) prefix d n,
  map f (filled prefix d n) = filled (map f prefix) (f d) n.
Proof.
  intros f prefix d n. unfold filled.
  rewrite map_app, map_Zrepeat, Zlength_map.
  reflexivity.
Qed.

(* 编码后列表上的前沿推进；尾值 d : B 不要求在 f 的像内。 *)
Lemma filled_map_step {A B} : forall (f : A -> B) prefix d n v,
  Zlength prefix < n ->
  upd_Znth (Zlength prefix) (filled (map f prefix) d n) (f v) =
  filled (map f (prefix ++ [v])) d n.
Proof.
  intros f prefix d n v H.
  replace (Zlength prefix) with (Zlength (map f prefix))
    by (rewrite Zlength_map; reflexivity).
  rewrite filled_step by (rewrite Zlength_map; exact H).
  rewrite map_app. reflexivity.
Qed.

(* 旧前沿位置的当前值为默认尾值 d。 *)
Lemma filled_next {A} {dA : Inhabitant A} : forall (prefix : list A) d n,
  Zlength prefix < n -> Znth (Zlength prefix) (filled prefix d n) = d.
Proof.
  intros prefix d n H. unfold filled.
  rewrite (app_Znth2 A dA prefix (Zrepeat d (n - Zlength prefix))
             (Zlength prefix)) by lia.
  rewrite Z.sub_diag.
  rewrite (Znth_Zrepeat A dA 0 (n - Zlength prefix) d) by lia.
  reflexivity.
Qed.

(* ================= 公开引理：prefix_holds / frontier 族 ================= *)

(* 前沿谓词与已处理段的 Forall 互推；上界 i <= Zlength xs 防止把默认元素当真元素。 *)
Lemma prefix_holds_sublist {A} {dA : Inhabitant A} : forall Q i (xs : list A),
  0 <= i <= Zlength xs ->
  (prefix_holds Q i xs <-> Forall Q (sublist 0 i xs)).
Proof.
  intros Q i xs H.
  assert (HL : Zlength (sublist 0 i xs) = i).
  { pose proof (Zlength_sublist 0 i xs ltac:(lia) ltac:(lia)) as E.
    rewrite Zminus_0_r in E. exact E. }
  unfold prefix_holds. split.
  - intros Hholds.
    apply Forall_forall. intros x Hin.
    apply In_Znth in Hin. destruct Hin as [k [Hk Hx]]. subst x.
    rewrite HL in Hk.
    assert (Hsub : Znth k (sublist 0 i xs) = Znth k xs).
    { pose proof (Znth_sublist 0 k i xs ltac:(lia) ltac:(lia)) as E.
      rewrite Z.add_0_r in E. exact E. }
    rewrite Hsub. apply Hholds. exact Hk.
  - intros HForall k Hk.
    assert (Hsub : Znth k (sublist 0 i xs) = Znth k xs).
    { pose proof (Znth_sublist 0 k i xs ltac:(lia) ltac:(lia)) as E.
      rewrite Z.add_0_r in E. exact E. }
    rewrite <- Hsub. apply Forall_Znth.
    + rewrite HL. exact Hk.
    + exact HForall.
Qed.

(* 前沿写入后谓词保持：j = i 时（拒绝分支）不要求 v 满足 Q；
   j = i + 1 时（接受分支）要求 Q v。 *)
Lemma prefix_holds_store {A} {dA : Inhabitant A} : forall Q (xs : list A) i j v,
  0 <= i < Zlength xs -> i <= j <= i+1 ->
  (i < j -> Q v) -> prefix_holds Q i xs ->
  prefix_holds Q j (upd_Znth i xs v).
Proof.
  intros Q xs i j v Hi Hj Hv Hholds.
  unfold prefix_holds. intros k Hk.
  destruct (Z.eq_dec j i) as [Hji|Hne].
  - subst j.
    destruct (Z.eq_dec k i) as [->|Hkne].
    + (* k = i 且 j = i：与 Hk 的严格上界矛盾，此情形不可达 *)
      exfalso. lia.
    + rewrite upd_Znth_diff by lia. apply Hholds. lia.
  - assert (Hj1 : j = i + 1) by lia.
    subst j.
    destruct (Z.eq_dec k i) as [->|Hkne].
    + rewrite upd_Znth_same by lia. apply Hv. lia.
    + rewrite upd_Znth_diff by lia. apply Hholds. lia.
Qed.

(* 前沿一步：两段 Forall 同时推进；未处理后缀保持不动，长度不变。 *)
Lemma frontier_Forall_step {A} : forall (P Q : A -> Prop) xs i v,
  0 <= i < Zlength xs ->
  Forall Q (sublist 0 i xs) ->
  Forall P (sublist i (Zlength xs) xs) -> Q v ->
  Forall Q (sublist 0 (i+1) (upd_Znth i xs v)) /\
  Forall P (sublist (i+1) (Zlength xs) (upd_Znth i xs v)).
Proof.
  intros P Q xs i v Hi HQ HP Hv.
  assert (HL1 : Zlength (sublist 0 i xs) = i).
  { pose proof (Zlength_sublist 0 i xs ltac:(lia) ltac:(lia)) as E.
    rewrite Zminus_0_r in E. exact E. }
  assert (HL2 : Zlength (sublist i (i+1) xs) = 1).
  { pose proof (Zlength_sublist i (i+1) xs ltac:(lia) ltac:(lia)) as E.
    replace (i + 1 - i) with 1 in E by lia. exact E. }
  assert (Hmid : upd_Znth 0 (sublist i (i+1) xs) v = [v]).
  { rewrite upd_Znth_old_upd_Znth by (rewrite HL2; lia).
    unfold old_upd_Znth. rewrite HL2.
    change (0 + 1) with 1.
    rewrite !sublist_nil. reflexivity. }
  split.
  - (* 前缀段：0..i 保持原值，第 i 位写入 v *)
    rewrite (sublist_upd_Znth_lr xs i 0 (i+1) v) by lia.
    rewrite Zminus_0_r.
    rewrite <- (sublist_rejoin 0 i (i+1) xs) by lia.
    rewrite (upd_Znth_app2 (sublist 0 i xs) (sublist i (i+1) xs) i v) by lia.
    rewrite HL1. rewrite Z.sub_diag. rewrite Hmid.
    apply Forall_app_intro.
    + exact HQ.
    + constructor; [exact Hv | constructor].
  - (* 后缀段：i+1..n 未被触碰；HP 去掉已处理首项即得 *)
    rewrite (sublist_upd_Znth_r xs i (i+1) (Zlength xs) v) by lia.
    rewrite (sublist_split i (i+1) (Zlength xs) xs) in HP by lia.
    apply Forall_app_inv_r in HP.
    exact HP.
Qed.
