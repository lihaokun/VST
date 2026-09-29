Require Import VST.floyd.proofauto.
Require Import VST.floyd.FusionStore.
From VST.progs64.fusion Require Import seed_program union_exact_seed_interface union_exact_seed_spec.
Import compcert.lib.Maps.
Local Open Scope logic.

Module ProgramLayout <: SEED_LAYOUT.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Lemma seed_lookup : PTree.get seed_union_rw._seed cenv_cs = Some SeedReference.seed_composite.
Proof. reflexivity. Qed.
Definition seed_value (x : int64) : reptype (Tunion seed_union_rw._seed noattr) := inr (Vlong x).
Lemma seed_value_shape : forall x,
  JMeq (unfold_reptype (seed_value x)) (inr (Vlong x) : val + val).
Proof. intros; exact (unfold_reptype_JMeq _ (seed_value x)). Qed.
End ProgramLayout.
#[export] Instance CompSpecs : compspecs := ProgramLayout.CompSpecs.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Include SeedSpec ProgramLayout.

Definition exact_spec := w64_r32_exact_spec.
Definition caller_spec : ident * funspec :=
  DECLARE _mixed_caller
  WITH c0 : int64, x : int64, s : val
  PRE [tptr tseed_exact, tulong]
    PROP () PARAMS (s; Vlong x)
    SEP (data_at Ews tseed_exact (inr (Vlong c0)) s)
  POST [tuint]
    PROP () RETURN (Vint (Int64.loword x))
    SEP (seed_v64_exact Ews x s).
Definition main_spec :=
  DECLARE _main
  WITH gv : globals
  PRE [] main_pre prog tt gv
  POST [tint] main_post prog gv.
Definition Gprog : funspecs := [exact_spec; caller_spec; main_spec].

Lemma body_w64_r32 : semax_body Vprog Gprog f_w64_r32 exact_spec.
Proof.
  start_function.
  change (fn_body f_w64_r32) with
    (Ssequence seed_store_v64_statement
      (Ssequence seed_load_v32_statement (Sreturn (Some (Etempvar _t'1 tuint))))).
  eapply semax_seq' with (P' :=
    PROP () LOCAL (temp _s s; temp _c (Vlong x))
    SEP (exact_seed_v64 Ews x s)).
  - unfold seed_store_v64_statement.
    eapply semax_pre0; [apply now_later |].
    eapply semax_store_exact_nth_ram with
      (n := 0%nat) (Pre := seed_data_v64 Ews c0 s)
      (R := [seed_data_v64 Ews c0 s]) (Post := exact_seed_v64 Ews x s)
      (p := s) (v := Vlong x) (sh := Ews) (t1 := tulong) (ch := Mint64).
    + reflexivity.
    + reflexivity.
    + apply seed_store_v64_address.
    + apply seed_store_v64_eval.
    + reflexivity.
    + auto.
    + apply seed_v64_store_ramify.
    + unfold seed_store_v64_lvalue, seed_store_v64_value, seed_data_v64.
      entailer!.
  - eapply semax_seed_load_v32_exact.
    + reflexivity.
    + unfold seed_load_v32_expr.
      sep_apply exact_seed_v64_isptr. entailer!.
    + forward.
Qed.

Lemma seed_initializer sh x p :
  data_at sh tulong (Vlong x) p =
  data_at sh tseed_exact (inr (Vlong x)) p.
Proof.
  assert (HA : align_compatible tulong p = align_compatible tseed_exact p).
  { unfold align_compatible. destruct p; try reflexivity.
    apply prop_ext; split; intro H.
    - eapply align_compatible_rec_Tunion with (co := get_co _seed).
      + reflexivity.
      + reflexivity.
      + intros id t Ht. simpl in Ht.
        destruct (ident_eq id _v32).
        * inversion Ht; subst.
          eapply align_compatible_rec_by_value; [reflexivity |].
          pose proof (align_compatible_rec_by_value_inv _ tulong Mint64 _ eq_refl H) as HD.
          change (8 | Ptrofs.unsigned i) in HD.
          change (4 | Ptrofs.unsigned i).
          destruct HD as [k Hk]; exists (2*k)%Z; lia.
        * destruct (ident_eq id _v64); inversion Ht; subst; exact H.
    - exact (align_compatible_rec_Tunion_inv cenv_cs _seed noattr (get_co _seed)
        _ eq_refl H _v64 tulong eq_refl). }
  unfold data_at, field_at, at_offset, offset_val.
  simpl; rewrite (data_at_rec_eq sh tseed_exact); simpl; unfold union_pred; simpl.
  unfold field_compatible. rewrite <- HA.
  unfold size_compatible; simpl.
  unfold withspacer, spacer.
  destruct (Z.eq_dec (8 - 8) 0); [| lia].
  reflexivity.
Qed.

Lemma body_caller : semax_body Vprog Gprog f_mixed_caller caller_spec.
Proof. start_function. forward_call (c0, x, s). forward. Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  rewrite seed_initializer.
  forward_call (Int64.zero, Int64.repr 4294967338, gv _global_seed).
  forward.
Qed.

(* The pre-existing forward store keeps its ordinary data_at postcondition. *)
Lemma ordinary_forward_store_regression : forall {Espec : OracleKind} c0 x s,
  semax (func_tycontext f_w64_r32 Vprog Gprog nil)
    (PROP () LOCAL (temp _s s; temp _c (Vlong x))
     SEP (data_at Ews tseed_exact (inr (Vlong c0)) s))
    seed_store_v64_statement
    (normal_ret_assert
      (PROP () LOCAL (temp _s s; temp _c (Vlong x))
       SEP (data_at Ews tseed_exact (inr (Vlong x)) s))).
Proof.
  intros.
  unfold seed_store_v64_statement, seed_store_v64_lvalue, seed_store_v64_value.
  forward.
  entailer!.
Qed.

Require Import VST.floyd.VSU.

Definition seedVSU : @VSU NullExtension.Espec [] []
  ltac:(QPprog prog) Gprog (InitGPred (Vardefs ltac:(QPprog prog))).
Proof.
  mkVSU prog Gprog.
  - solve_SF_internal body_w64_r32.
  - solve_SF_internal body_caller.
  - solve_SF_internal body_main.
Qed.

Print Assumptions semax_store_exact_nth_ram.
Print Assumptions body_w64_r32.
Print Assumptions body_caller.
Print Assumptions body_main.
Print Assumptions ordinary_forward_store_regression.
Print Assumptions seedVSU.
