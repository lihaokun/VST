(* =====================================================================
   bridges.v — union 视角 ↔ 标量视图的桥接引理（B1/B2 的验证基础设施）

   机制（全部实证于 2026-09-03，VST 2.16）：
   - data_at tseed (inr c) 的归约：spacer (8-8=0) 塌缩，活跃成员 v64
     占满 8 字节 ⇒ guard 换成后即得 tulong 视图；
   - data_at tseed (inl x) 的归约：活跃成员 v32 = 4 字节 mapsto +
     4 字节 spacer（memory_block，可被 TT 吸收）；
   - data_at_rec 标量分支与 mapsto 为【纯转换】（data_at_rec_eq 的
     Tint/Tlong 分支直接就是 mapsto），绕开带 6 个前提的
     mapsto_data_at（field_at.v:2422）；
   - guard（field_compatible）经 andp_left2 直接 drop（andp 为逐点
     合取，消去无损 soundness——派生方向丢信息是合法的）。
   ===================================================================== *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import seed_union_rw.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Local Open Scope Z.
Local Open Scope logic.

Definition tseed := Tunion _seed noattr.

(* ---------- 具体常量钉子（cenv 计算一次，之后不再展开） ---------- *)
Lemma sizeof_tseed_eq : sizeof tseed = 8.
Proof. reflexivity. Qed.

Lemma sizeof_tuint_eq : sizeof tuint = 4.
Proof. reflexivity. Qed.

Lemma complete_legal_tulong : complete_legal_cosu_type tulong = true.
Proof. reflexivity. Qed.

Lemma complete_legal_tuint : complete_legal_cosu_type tuint = true.
Proof. reflexivity. Qed.

Lemma align_compat_tulong_of_seed : forall s,
  align_compatible tseed s -> align_compatible tulong s.
Proof.
  intros s Hal.
  unfold align_compatible in Hal |- *.
  destruct s; try exact I.
  assert (Hco : Maps.PTree.get _seed cenv_cs = Some (get_co _seed)) by reflexivity.
  assert (Hall := align_compatible_rec_Tunion_inv cenv_cs _seed noattr
                    (get_co _seed) (Ptrofs.unsigned i) Hco Hal _v64 tulong eq_refl).
  exact Hall.
Qed.

Lemma align_compat_tuint_of_seed : forall s,
  align_compatible tseed s -> align_compatible tuint s.
Proof.
  intros s Hal.
  unfold align_compatible in Hal |- *.
  destruct s; try exact I.
  assert (Hco : Maps.PTree.get _seed cenv_cs = Some (get_co _seed)) by reflexivity.
  assert (Hall := align_compatible_rec_Tunion_inv cenv_cs _seed noattr
                    (get_co _seed) (Ptrofs.unsigned i) Hco Hal _v32 tuint eq_refl).
  exact Hall.
Qed.

Lemma size_compat_tulong_of_seed : forall s,
  size_compatible tseed s -> size_compatible tulong s.
Proof.
  intros s H. unfold size_compatible in *.
  rewrite sizeof_tseed_eq in H. exact H.
Qed.

Lemma size_compat_tuint_of_seed : forall s,
  size_compatible tseed s -> size_compatible tuint s.
Proof.
  intros s H. unfold size_compatible in *.
  rewrite sizeof_tseed_eq in H; rewrite sizeof_tuint_eq.
  destruct s; simpl; lia.
Qed.

Lemma fc_tulong_of_seed : forall s,
  field_compatible tseed [] s -> field_compatible tulong [] s.
Proof.
  intros s [Hisp [Hcl [Hsz [Hal Hlegal]]]].
  unfold field_compatible.
  split; [exact Hisp |].
  split; [apply complete_legal_tulong |].
  split; [apply size_compat_tulong_of_seed; exact Hsz |].
  split; [apply align_compat_tulong_of_seed; assumption |].
  exact Hlegal.
Qed.

Lemma fc_tuint_of_seed : forall s,
  field_compatible tseed [] s -> field_compatible tuint [] s.
Proof.
  intros s [Hisp [Hcl [Hsz [Hal Hlegal]]]].
  unfold field_compatible.
  split; [exact Hisp |].
  split; [apply complete_legal_tuint |].
  split; [apply size_compat_tuint_of_seed; exact Hsz |].
  split; [apply align_compat_tuint_of_seed; assumption |].
  exact Hlegal.
Qed.

(* ---------- 主桥（load 方向） ---------- *)

(* B1 桥：v64 活跃（inr）⇒ 整个 8 字节对象就是 tulong 视图 *)
Lemma seed64_load_bridge : forall sh c s,
  data_at sh tseed (inr (Vlong (Int64.repr c))) s |--
    mapsto sh tulong s (Vlong (Int64.repr c)) * TT.
Proof.
  intros sh c s.
  unfold data_at, field_at, at_offset, offset_val.
  simpl.
  rewrite data_at_rec_eq.
  simpl.
  unfold union_pred. simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 8) 0); [ | lia].
  lazymatch goal with
  | |- context [data_at_rec sh tulong (Vlong (Int64.repr c)) ?p] =>
      change (data_at_rec sh tulong (Vlong (Int64.repr c)) p)
        with (mapsto sh tulong p (Vlong (Int64.repr c)))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero sh tulong s (Vlong (Int64.repr c))).
  apply andp_left2.
  apply sepcon_TT.
Qed.

(* B2 桥：v32 活跃（inl）⇒ 前 4 字节是 tuint 视图，后 4 字节 spacer 由 TT 吸收 *)
Lemma seed32_load_bridge : forall sh x s,
  data_at sh tseed (inl (Vint (Int.repr x))) s |--
    mapsto sh tuint s (Vint (Int.repr x)) * TT.
Proof.
  intros sh x s.
  unfold data_at, field_at, at_offset, offset_val.
  simpl.
  rewrite data_at_rec_eq.
  simpl.
  unfold union_pred. simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 4) 0); [lia |].
  destruct (Z.eq_dec (8 - 4) 0); [lia |].
  lazymatch goal with
  | |- context [data_at_rec sh tuint (Vint (Int.repr x)) ?p] =>
      change (data_at_rec sh tuint (Vint (Int.repr x)) p)
        with (mapsto sh tuint p (Vint (Int.repr x)))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero sh tuint s (Vint (Int.repr x))).
  apply andp_left2.
  apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* ---------- 视图桥（data_at 形式，供 semax_pre_post 的 skip 换视角用） ---------- *)

Lemma seed64_view_bridge : forall sh c s,
  data_at sh tseed (inr (Vlong (Int64.repr c))) s |--
    data_at sh tulong (Vlong (Int64.repr c)) s * TT.
Proof.
  intros sh c s.
  unfold data_at, field_at, at_offset, offset_val.
  simpl; rewrite data_at_rec_eq; simpl; unfold union_pred; simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 8) 0); [ | lia].
  lazymatch goal with
  | |- context [data_at_rec sh tulong (Vlong (Int64.repr c)) ?p] =>
      change (data_at_rec sh tulong (Vlong (Int64.repr c)) p)
        with (mapsto sh tulong p (Vlong (Int64.repr c)))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero sh tulong s (Vlong (Int64.repr c))).
  rewrite sepcon_andp_prop'.
  apply andp_right.
  - apply andp_left1. apply prop_derives. intros Hfc. apply fc_tulong_of_seed. exact Hfc.
  - apply andp_left2. apply sepcon_TT.
Qed.

Lemma seed32_view_bridge : forall sh x s,
  data_at sh tseed (inl (Vint (Int.repr x))) s |--
    data_at sh tuint (Vint (Int.repr x)) s * TT.
Proof.
  intros sh x s.
  unfold data_at, field_at, at_offset, offset_val.
  simpl; rewrite data_at_rec_eq; simpl; unfold union_pred; simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 4) 0); [lia |].
  lazymatch goal with
  | |- context [data_at_rec sh tuint (Vint (Int.repr x)) ?p] =>
      change (data_at_rec sh tuint (Vint (Int.repr x)) p)
        with (mapsto sh tuint p (Vint (Int.repr x)))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero sh tuint s (Vint (Int.repr x))).
  rewrite sepcon_andp_prop'.
  apply andp_right.
  - apply andp_left1. apply prop_derives. intros Hfc. apply fc_tuint_of_seed. exact Hfc.
  - apply andp_left2. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* ---------- 扁平桥（供 forward 直接消费；B1 无 spacer，B2 拆双 item） ---------- *)

Lemma seed64_flat_bridge : forall sh c s,
  data_at sh tseed (inr (Vlong (Int64.repr c))) s |--
    data_at sh tulong (Vlong (Int64.repr c)) s.
Proof.
  intros sh c s.
  unfold data_at, field_at, at_offset, offset_val.
  simpl; rewrite data_at_rec_eq; simpl; unfold union_pred; simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 8) 0); [ | lia].
  lazymatch goal with
  | |- context [data_at_rec sh tulong (Vlong (Int64.repr c)) ?p] =>
      change (data_at_rec sh tulong (Vlong (Int64.repr c)) p)
        with (mapsto sh tulong p (Vlong (Int64.repr c)))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero sh tulong s (Vlong (Int64.repr c))).
  apply andp_right.
  - apply andp_left1. apply prop_derives. intros Hfc. apply fc_tulong_of_seed. exact Hfc.
  - apply andp_left2. apply derives_refl.
Qed.

Lemma seed32_dual_bridge : forall sh x s,
  data_at sh tseed (inl (Vint (Int.repr x))) s |--
    data_at sh tuint (Vint (Int.repr x)) s * memory_block sh 4 (offset_val 4 s).
Proof.
  intros sh x s.
  unfold data_at, field_at, at_offset, offset_val.
  simpl; rewrite data_at_rec_eq; simpl; unfold union_pred; simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 4) 0); [lia |].
  lazymatch goal with
  | |- context [data_at_rec sh tuint (Vint (Int.repr x)) ?p] =>
      change (data_at_rec sh tuint (Vint (Int.repr x)) p)
        with (mapsto sh tuint p (Vint (Int.repr x)))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero sh tuint s (Vint (Int.repr x))).
  unfold at_offset.
  rewrite offset_offset_val. rewrite ?Z.add_0_r, ?Z.add_0_l.
  change (8 - 4) with 4.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 4))
          | _ => Vundef end) with (offset_val 4 s).
  rewrite sepcon_andp_prop'.
  apply andp_right.
  - apply andp_left1. apply prop_derives. intros Hfc. apply fc_tuint_of_seed. exact Hfc.
  - apply andp_left2. apply derives_refl.
Qed.

(* ---------- semax_pre_post 的换视角包装（concrete temps 版） ---------- *)

Lemma wrapper64 : forall Delta s c,
  ENTAIL Delta,
    PROP () LOCAL (temp _s s; temp _c (Vlong (Int64.repr c)))
         SEP (data_at Ews tseed (inr (Vlong (Int64.repr c))) s) |--
    PROP () LOCAL (temp _s s; temp _c (Vlong (Int64.repr c)))
         SEP (data_at Ews tulong (Vlong (Int64.repr c)) s).
Proof.
  intros Delta s c.
  apply andp_left2.
  apply andp_right; [apply prop_right; exact I |].
  apply andp_right.
  + apply andp_left2. apply andp_left1. apply derives_refl.
  + apply andp_left2. apply andp_left2.
    unfold SEPx. cbn [fold_right_sepcon]. rewrite ?sepcon_emp.
    intro rho. apply seed64_flat_bridge.
Qed.

Lemma wrapper32 : forall Delta s x,
  ENTAIL Delta,
    PROP () LOCAL (temp _s s; temp _x (Vint (Int.repr x)))
         SEP (data_at Ews tseed (inl (Vint (Int.repr x))) s) |--
    PROP () LOCAL (temp _s s; temp _x (Vint (Int.repr x)))
         SEP (data_at Ews tuint (Vint (Int.repr x)) s;
              memory_block Ews 4 (offset_val 4 s)).
Proof.
  intros Delta s x.
  apply andp_left2.
  apply andp_right; [apply prop_right; exact I |].
  apply andp_right.
  + apply andp_left2. apply andp_left1. apply derives_refl.
  + apply andp_left2. apply andp_left2.
    unfold SEPx. cbn [fold_right_sepcon]. rewrite ?sepcon_emp.
    intro rho. apply seed32_dual_bridge.
Qed.
