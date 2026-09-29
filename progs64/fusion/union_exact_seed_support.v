(* Proved seed-union assertions and load adapters. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
From VST.progs64.fusion Require Import seed_union_rw union_exact_seed_interface.
Require Import VST.floyd.FusionViews64.

Module SeedSupport (Import Layout : SEED_LAYOUT).
Local Existing Instance CompSpecs.

Local Open Scope logic.

Definition exact_seed_type := Tunion _seed noattr.

Definition exact_seed_v64 (sh : share) (x : int64) (p : val) : mpred :=
  !! field_compatible exact_seed_type [] p &&
  exact_mapsto sh Mint64 (Vlong x) p.

Definition seed_data_v64 (sh : share) (x : int64) (p : val) : mpred :=
  data_at sh exact_seed_type (seed_value x) p.

Lemma exact_seed_v64_isptr : forall sh x p,
  exact_seed_v64 sh x p |-- !! isptr p.
Proof.
  intros. unfold exact_seed_v64.
  apply andp_left1. apply prop_derives.
  intros [Hptr _]. exact Hptr.
Qed.

Definition seed_store_v64_lvalue : expr :=
    (Efield
      (Ederef (Etempvar _s (tptr exact_seed_type)) exact_seed_type)
      _v64 tulong).

Definition seed_store_v64_value : expr := Etempvar _c tulong.

Definition seed_store_v64_statement : statement :=
  Sassign seed_store_v64_lvalue seed_store_v64_value.

Definition seed_load_v32_expr : expr :=
    (Efield
      (Ederef (Etempvar _s (tptr exact_seed_type)) exact_seed_type)
      _v32 tuint).

Definition seed_load_v32_statement : statement :=
  Sset _t'1 seed_load_v32_expr.

Lemma seed_store_v64_address : forall Delta c0 x s,
  ENTAIL Delta,
    PROP () LOCAL (temp _s s; temp _c (Vlong x))
    SEP (seed_data_v64 Ews c0 s) |--
    local (fun rho => s = eval_lvalue seed_store_v64_lvalue rho).
Proof.
  intros. unfold seed_store_v64_lvalue, seed_data_v64.
  rewrite data_at_isptr.
  apply andp_left2. intro rho.
  unfold PROPx, LOCALx, SEPx. simpl.
  unfold local, lift1. unfold_lift. simpl.
  constructor. intros w H.
  destruct H as [_ Hrest]. simpl in Hrest |- *.
  destruct Hrest as [Hlocals Hsep].
  destruct Hlocals as [[Hs _] _].
  destruct Hsep as [w1 [w2 [_ [Hdata _]]]].
  destruct Hdata as [Hptr _].
  rewrite <- Hs.
  rewrite seed_lookup. simpl.
  rewrite isptr_offset_val_zero by exact Hptr.
  change (s = s). reflexivity.
Qed.

Lemma seed_store_v64_eval : forall Delta c0 x s,
  ENTAIL Delta,
    PROP () LOCAL (temp _s s; temp _c (Vlong x))
    SEP (seed_data_v64 Ews c0 s) |--
    local (fun rho => Vlong x =
      eval_expr (Ecast seed_store_v64_value tulong) rho).
Proof.
  intros. unfold seed_store_v64_value.
  apply andp_left2. intro rho.
  unfold PROPx, LOCALx, SEPx. simpl.
  unfold local, lift1. unfold_lift. simpl.
  constructor. intros w H.
  destruct H as [_ Hrest]. simpl in Hrest |- *.
  destruct Hrest as [Hlocals _].
  destruct Hlocals as [_ [[Hx _] _]].
  rewrite <- Hx. change (Vlong x = Vlong x). reflexivity.
Qed.

Lemma exact_seed_load_v32_address : forall Delta x s,
  ENTAIL Delta,
    PROP () LOCAL (temp _s s; temp _c (Vlong x))
    SEP (exact_seed_v64 Ews x s) |--
    local (fun rho => s = eval_lvalue seed_load_v32_expr rho).
Proof.
  intros Delta x s.
  unfold seed_load_v32_expr.
  apply andp_left2. intro rho.
  unfold PROPx, LOCALx, SEPx. simpl.
  unfold local, lift1. unfold_lift. simpl.
  constructor. intros w H.
  destruct H as [Hlocal Hexact].
  simpl in Hexact |- *.
  destruct Hexact as [Hlocals Hsep].
  destruct Hlocals as [[Hs _] _].
  destruct Hsep as [w1 [w2 [_ [Hseed _]]]].
  destruct Hseed as [Hfc _].
  destruct Hfc as [Hptr _].
  rewrite <- Hs.
  rewrite seed_lookup. simpl.
  rewrite isptr_offset_val_zero by exact Hptr.
  change (s = s). reflexivity.
Qed.

Lemma seed_v64_store_ramify : forall c0 x s,
  seed_data_v64 Ews c0 s |--
    mapsto_ Ews tulong s *
      (exact_mapsto Ews Mint64 (Vlong x) s -* exact_seed_v64 Ews x s).
Proof.
  intros c0 x s.
  unfold seed_data_v64.
  unfold data_at, field_at, at_offset, offset_val.
  simpl; rewrite data_at_rec_eq; simpl.
  unfold exact_seed_type in *.
  (* Generalize the dependent value before rewriting the composite lookup. *)
  generalize (seed_value_shape c0).
  generalize (unfold_reptype (seed_value c0)).
  unfold reptype_unionlist, get_co.
  rewrite seed_lookup. simpl.
  intros v Hv. apply JMeq_eq in Hv. subst v.
  unfold union_pred; simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 8) 0); [| lia].
  lazymatch goal with
  | |- context [data_at_rec Ews tulong (Vlong c0) ?p] =>
      change (data_at_rec Ews tulong (Vlong c0) p)
        with (mapsto Ews tulong p (Vlong c0))
  end.
  change (match s with
          | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr 0))
          | _ => Vundef end) with (offset_val 0 s).
  rewrite <- (mapsto_offset_zero Ews tulong s (Vlong c0)).
  unfold exact_seed_v64.
  apply RAMIF_PLAIN.solve with
    (F := !! field_compatible exact_seed_type [] s && emp).
  - rewrite sepcon_andp_prop, sepcon_emp.
    apply andp_derives; [apply derives_refl |].
    apply mapsto_mapsto_.
  - rewrite sepcon_andp_prop', emp_sepcon.
    apply derives_refl.
Qed.

(* Instantiate semax_load_nth_ram using exact_Mint64_has_low32_mapsto_le.
   The exact 8-byte predicate remains in SEP, so repeated low-word loads do
   not forget the high word. *)
Lemma semax_seed_load_v32_exact :
  forall {Espec : OracleKind} (Delta : tycontext)
    (x : int64) (s : val) (k : statement) (Post : ret_assert),
    typeof_temp Delta _t'1 = Some tuint ->
    ENTAIL Delta,
      PROP () LOCAL (temp _s s; temp _c (Vlong x))
      SEP (exact_seed_v64 Ews x s) |--
      (tc_lvalue Delta seed_load_v32_expr) &&
      local (fun _ => tc_val tuint (Vint (Int64.loword x))) ->
    semax Delta
      (PROP ()
       LOCAL (temp _t'1 (Vint (Int64.loword x));
              temp _s s; temp _c (Vlong x))
       SEP (exact_seed_v64 Ews x s))
      k Post ->
    semax Delta
      (PROP ()
       LOCAL (temp _s s; temp _c (Vlong x))
      SEP (exact_seed_v64 Ews x s))
      (Ssequence seed_load_v32_statement k) Post.
Proof.
  intros Espec Delta x s k Post Htemp Htc Hk.
  eapply semax_seq'; [| exact Hk].
  unfold seed_load_v32_statement.
  eapply semax_pre0; [apply now_later |].
  eapply semax_load_nth_ram with
    (n := 0%nat) (sh := Ews) (Pre := exact_seed_v64 Ews x s)
    (p := s) (v := Vint (Int64.loword x)) (t1 := tuint) (t2 := tuint).
  - reflexivity.
  - exact Htemp.
  - reflexivity.
  - apply exact_seed_load_v32_address.
  - reflexivity.
  - auto.
  - unfold exact_seed_v64. apply andp_left2.
    apply exact_Mint64_has_low32_mapsto_le.
    + reflexivity.
    + auto.
  - exact Htc.
Qed.

End SeedSupport.
