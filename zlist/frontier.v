(* 纯列表前沿（zlist/frontier.v）
   filled 是定义性缩写：prefix ++ Zrepeat d (n - Zlength prefix)。
   引理陈述尽量站在使用方的展开表达式形态上；filled 形作为缩写变体并存。
   索引一律为 Z；只有读 Znth 的接口要求 Inhabitant 实例。
   尾值 d 不要求在编码函数的像内（Vundef 尾合法）；
   prefix_holds_store 在 j = i（拒绝分支）时不要求新写值满足 Q。 *)
Set Default Timeout 300.

From Stdlib Require Import ZArith Lists.List Lia.
Import ListNotations.
Require Import VST.zlist.sublist.
Require Import VST.zlist.Zlength_solver.
Import SublistInternalLib.

Local Open Scope Z_scope.

(* ================= 公开定义 ================= *)

(* 把前缀 prefix 用默认尾值 d 补齐到总长 n（定义性缩写）。 *)
Definition filled {A} (prefix : list A) (d : A) (n : Z) : list A :=
  prefix ++ Zrepeat d (n - Zlength prefix).

(* xs 的前 i 项都满足 Q。 *)
Definition prefix_holds {A} {dA : Inhabitant A}
    (Q : A -> Prop) (i : Z) (xs : list A) : Prop :=
  forall k : Z, 0 <= k < i -> Q (Znth k xs).

(* ================= 通用列表辅助引理 ================= *)

(* 正长度的 Zrepeat 可拆出头部。 *)
Lemma Zrepeat_cons_pos {A} : forall (d : A) n,
  0 < n -> Zrepeat d n = d :: Zrepeat d (n - 1).
Proof.
  intros d n H.
  assert (E : n = 1 + (n - 1)) by lia.
  rewrite E at 1.
  rewrite <- (Zrepeat_app 1 (n - 1) d) by lia.
  reflexivity.
Qed.

(* Forall 的拼接引入与右半提取。 *)
Lemma Forall_app_intro {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; simpl; intros H1 H2.
  - exact H2.
  - inversion H1; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma Forall_app_inv_r {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P (l1 ++ l2) -> Forall P l2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros l2 H.
  - exact H.
  - simpl in H. inversion H; subst. apply IH. assumption.
Qed.

(* ================= 填充族：展开形式（使用方表达式形态） ================= *)

(* 展开形式的关键一步：在已填长度位写入 v，等价于前缀追加 v。
    前提要求严格剩余长度。 *)
Lemma filled_stepU {A} : forall (prefix : list A) (d : A) (n : Z) (v : A),
  Zlength prefix < n ->
  upd_Znth (Zlength prefix) (prefix ++ Zrepeat d (n - Zlength prefix)) v =
  (prefix ++ [v]) ++ Zrepeat d (n - (Zlength prefix + 1)).
Proof.
  intros prefix d n v H.
  pose proof (Zlength_Zrepeat A d (n - Zlength prefix) ltac:(lia)) as HLr.
  rewrite upd_Znth_app2 by lia.
  rewrite Z.sub_diag.
  rewrite Zrepeat_cons_pos by lia.
  rewrite upd_Znth0.
  rewrite <- app_assoc.
  f_equal.
  replace (n - (Zlength prefix + 1)) with (n - Zlength prefix - 1) by lia.
  reflexivity.
Qed.

(* 编码层的展开形式：map 后前缀的推进一步。 *)
Lemma filled_map_stepU_at {A B} (f : A -> B) (prefix : list A)
    (d : B) (n j : Z) (v : A) :
  Zlength prefix = j -> Zlength prefix < n ->
  upd_Znth j (map f prefix ++ Zrepeat d (n - j)) (f v) =
  map f (prefix ++ [v]) ++ Zrepeat d (n - (j + 1)).
Proof.
  intros Hj Hn.
  assert (Hn' : Zlength (map f prefix) < n) by (rewrite Zlength_map; exact Hn).
  rewrite <- Hj.
  transitivity
    (upd_Znth (Zlength (map f prefix))
       (map f prefix ++ Zrepeat d (n - Zlength (map f prefix))) (f v)).
  - f_equal.
    + rewrite Zlength_map. reflexivity.
    + f_equal. rewrite Zlength_map. reflexivity.
  - rewrite filled_stepU by exact Hn'.
    rewrite map_app. simpl map.
    rewrite Zlength_map.
    replace (Zlength [f v]) with 1 by reflexivity.
    rewrite <- app_assoc.
    reflexivity.
Qed.

(* 编码层一步，前沿由前缀自身长度承载（使用方免传 j）。 *)
Lemma filled_map_stepU {A B} (f : A -> B) (prefix : list A)
    (d : B) (n : Z) (v : A) :
  Zlength prefix < n ->
  upd_Znth (Zlength prefix) (map f prefix ++ Zrepeat d (n - Zlength prefix)) (f v) =
  map f (prefix ++ [v]) ++ Zrepeat d (n - (Zlength prefix + 1)).
Proof.
  intros Hn.
  apply (filled_map_stepU_at f prefix d n (Zlength prefix) v); [reflexivity | exact Hn].
Qed.

(* ================= 填充族：filled 缩写形式 ================= *)

Lemma filled_length {A} : forall (prefix : list A) d n,
  Zlength prefix <= n -> Zlength (filled prefix d n) = n.
Proof.
  intros prefix d n H. unfold filled.
  rewrite Zlength_app, Zlength_Zrepeat by lia. lia.
Qed.

Lemma filled_empty {A} : forall (d : A) n,
  filled [] d n = Zrepeat d n.
Proof.
  intros d n. unfold filled.
  rewrite Zlength_nil, Zminus_0_r. apply app_nil_l.
Qed.

Lemma filled_full {A} : forall (prefix : list A) d,
  filled prefix d (Zlength prefix) = prefix.
Proof.
  intros prefix d. unfold filled.
  rewrite Z.sub_diag, Zrepeat_neg by lia. apply app_nil_r.
Qed.

Lemma filled_step {A} : forall (prefix : list A) d n v,
  Zlength prefix < n ->
  upd_Znth (Zlength prefix) (filled prefix d n) v =
  filled (prefix ++ [v]) d n.
Proof.
  intros prefix d n v H. unfold filled in *.
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

Lemma filled_map {A B} : forall (f : A -> B) prefix d n,
  map f (filled prefix d n) = filled (map f prefix) (f d) n.
Proof.
  intros f prefix d n. unfold filled.
  rewrite map_app, map_Zrepeat, Zlength_map.
  reflexivity.
Qed.

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

(* ================= 前沿族 ================= *)

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
    + exfalso. lia.
    + rewrite upd_Znth_diff by lia. apply Hholds. lia.
  - assert (Hj1 : j = i + 1) by lia.
    subst j.
    destruct (Z.eq_dec k i) as [->|Hkne].
    + rewrite upd_Znth_same by lia. apply Hv. lia.
    + rewrite upd_Znth_diff by lia. apply Hholds. lia.
Qed.

(* 前缀的接受/拒绝写入（Forall/sublist 记法）：
    表示转换及更新长度义务在库内闭合。
    j = i 时不要求 Q v，j = i + 1 时才需新值满足 Q。 *)
Lemma Forall_sublist_store {A} {dA : Inhabitant A} (Q : A -> Prop) xs i j v :
  0 <= i < Zlength xs -> i <= j <= i + 1 -> (i < j -> Q v) ->
  Forall Q (sublist 0 i xs) ->
  Forall Q (sublist 0 j (upd_Znth i xs v)).
Proof.
  intros Hi Hj Hv HF.
  destruct (prefix_holds_sublist Q j (upd_Znth i xs v)
              ltac:(rewrite Zlength_upd_Znth; lia)) as [Hfw _].
  apply Hfw.
  apply prefix_holds_store.
  - exact Hi.
  - lia.
  - exact Hv.
  - destruct (prefix_holds_sublist Q i xs ltac:(lia)) as [_ Hbwd].
    exact (Hbwd HF).
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
  - rewrite (sublist_upd_Znth_lr xs i 0 (i+1) v) by lia.
    rewrite Zminus_0_r.
    rewrite <- (sublist_rejoin 0 i (i+1) xs) by lia.
    rewrite (upd_Znth_app2 (sublist 0 i xs) (sublist i (i+1) xs) i v) by lia.
    rewrite HL1. rewrite Z.sub_diag. rewrite Hmid.
    apply Forall_app_intro.
    + exact HQ.
    + constructor; [exact Hv | constructor].
  - rewrite (sublist_upd_Znth_r xs i (i+1) (Zlength xs) v) by lia.
    rewrite (sublist_split i (i+1) (Zlength xs) xs) in HP by lia.
    apply Forall_app_inv_r in HP.
    exact HP.
Qed.
