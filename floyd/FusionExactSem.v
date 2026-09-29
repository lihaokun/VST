Require Import VST.floyd.FusionExact.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax_straight.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem VST.veric.res_predicates.
Require Import VST.veric.semax VST.veric.semax_lemmas VST.veric.semax_conseq.
Require Import VST.veric.extend_tc VST.veric.expr_lemmas VST.veric.expr_lemmas4.
Require Import VST.veric.Clight_lemmas VST.veric.Clight_assert_lemmas.
Import Clight expr2 Clight_seplog.
Import predicates_hered.
Import compcert_rmaps.RML.R compcert_rmaps.

Local Open Scope Z.
Local Open Scope logic.

(* Coherence identifies the encoded bytes, without a decoding assumption. *)
Lemma coherent_address_mapsto_exact : forall m phi ch v sh b ofs stored,
  contents_cohere m phi ->
  Mem.getN (size_chunk_nat ch) ofs (Maps.PMap.get b (Mem.mem_contents m)) =
    encode_val ch stored ->
  res_predicates.address_mapsto ch v sh (b, ofs) phi ->
  app_pred (exact_address_mapsto sh ch stored (b, ofs)) phi.
Proof.
  intros m phi ch v sh b ofs stored HC HB [bl [[HL [HD HA]] HR]].
  split; [exact HA |].
  unfold res_predicates.address_mapsto_old.
  intro loc. specialize (HR loc).
  hnf in HR |- *.
  destruct (adr_range_dec (b, ofs) (size_chunk ch) loc) as [Hin | Hout];
    [| exact HR].
  destruct HR as [rsh HR]. exists rsh.
  unfold res_predicates.yesat_raw in *.
  try rewrite preds_fmap_NoneP in *.
  pose proof (HC _ _ _ _ _ HR) as [HCbyte _].
  rewrite <- HCbyte in HR.
  destruct loc as [b' z]. destruct Hin as [Heq Hz]. simpl in Heq, Hz.
  subst b'.
  rewrite (nth_getN m b ofs z (size_chunk ch) Hz) in HR
    by (pose proof (size_chunk_pos ch); lia).
  replace (Z.to_nat (size_chunk ch)) with (size_chunk_nat ch) in HR
    by (destruct ch; reflexivity).
  rewrite HB in HR. exact HR.
Qed.

Lemma address_mapsto_can_store_exact :
  forall jm ch v sh (WS : writable0_share sh) b ofs stored frame,
  (res_predicates.address_mapsto ch v sh (b, Ptrofs.unsigned ofs) *
    exactly frame)%pred (m_phi jm) ->
  exists m',
    { STORE : Mem.store ch (m_dry jm) b (Ptrofs.unsigned ofs) stored = Some m' |
      (exact_address_mapsto sh ch stored (b, Ptrofs.unsigned ofs) *
        exactly frame)%pred
        (m_phi (store_juicy_mem _ _ _ _ _ _ STORE)) }.
Proof.
  intros jm ch v sh WS b ofs stored frame H.
  assert (HA : (align_chunk ch | Ptrofs.unsigned ofs)).
  { destruct H as [a [f [HJ [[bl [[HL [HD HA]] HR]] HF]]]]. exact HA. }
  destruct (semax_straight.address_mapsto_can_store' jm ch ch v sh WS
    b ofs stored frame H (decode_encode_val_ok_same ch) HA)
    as [m' [STORE Hpost]].
  exists m'; exists STORE.
  destruct Hpost as [a [f [HJ [[v' [HD HM]] HF]]]].
  exists a; exists f. split; [exact HJ |]. split; [| exact HF].
  eapply coherent_address_mapsto_exact; [| | exact HM].
  - eapply contents_cohere_join_sub.
    + exact (juicy_mem_contents (store_juicy_mem _ _ _ _ _ _ STORE)).
    + exists f; exact HJ.
  - simpl. rewrite (Mem.store_mem_contents _ _ _ _ _ _ STORE), Maps.PMap.gss.
    rewrite <- (encode_val_length ch stored). apply Mem.getN_setN_same.
Qed.

Section SemanticStore.
Context {CS : compspecs} {Espec : OracleKind}.
Local Open Scope pred.

Lemma semax_store_exact : forall Delta e1 e2 sh P ch,
  writable0_share sh ->
  access_mode (typeof e1) = By_value ch ->
  semax.semax Espec Delta
    (fun rho => |> (tc_lvalue Delta e1 rho &&
      tc_expr Delta (Ecast e2 (typeof e1)) rho &&
      (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) * P rho)))
    (Sassign e1 e2)
    (normal_ret_assert (fun rho =>
      exact_mapsto sh ch
        (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho)))
        (eval_lvalue e1 rho) * P rho)).
Proof.
intros Delta e1 e2 sh P ch WS Hmode.
apply semax_conseq.semax_pre with
  (fun rho : environ => EX v3: val,
    |> tc_lvalue Delta e1 rho && |> tc_expr Delta (Ecast e2 (typeof e1)) rho &&
    |> (mapsto sh (typeof e1) (eval_lvalue e1 rho) v3 * P rho)).
intro. apply andp_left2. unfold mapsto_.
apply exp_right with Vundef. repeat rewrite later_andp; auto.
apply extract_exists_pre; intro v3.
apply semax_straight_simple; auto.
intros jm jm1 Delta' ge ve te rho k F f TS [TC1 TC2] TC4 Hcl Hge Hage [H0 H0'] HGG'.
specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
assert (typecheck_environ Delta rho) as TC.
{ destruct TC4. eapply typecheck_environ_sub; eauto. }
pose proof TC1 as TC1'. pose proof TC2 as TC2'.
apply (tc_lvalue_sub _ _ _ TS) in TC1'; [| auto].
apply (tc_expr_sub _ _ _ TS) in TC2'; [| auto].
unfold tc_expr in TC2, TC2'; simpl in TC2, TC2'.
rewrite denote_tc_assert_andp in TC2, TC2'.
simpl in TC2,TC2'; super_unfold_lift.
destruct TC2 as [TC2 TC3]. destruct TC2' as [TC2' TC3'].
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi Hage))).
pose proof I.
destruct H0 as [?w [?w [? [? [?w [?w [H3 [H4 H5]]]]]]]].
unfold mapsto in H4. rewrite Hmode in H4.
destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 HGG' Hge
  (guard_environ_e1 _ _ _ TC4)) as [b0 [i [He1 He1']]]; auto.
rewrite He1' in *.
destruct (join_assoc H3 (join_comm H0)) as [?w [H6 H7]].
destruct (type_is_volatile (typeof e1)) eqn:NONVOL; try contradiction.
rewrite if_true in H4 by auto.
assert (exists v, address_mapsto ch v sh (b0, Ptrofs.unsigned i) w1)
  by (destruct H4 as [[H4' H4] |[? [? ?]]]; eauto).
clear v3 H4; destruct H2 as [v3 H4].
assert (H11' : (address_mapsto ch v3 sh (b0, Ptrofs.unsigned i) * TT)%pred (m_phi jm1))
  by (exists w1; exists w3; split3; auto).
assert (H11 : (address_mapsto ch v3 sh (b0, Ptrofs.unsigned i) * exactly w3)%pred (m_phi jm1)).
{ exists w1; exists w3; split3; auto. hnf; eauto. }
destruct (address_mapsto_can_store_exact jm1 ch v3 sh WS b0 i
  (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1)))
  w3 H11) as [m' [STORE AM]].
exists (store_juicy_mem _ _ _ _ _ _ STORE).
exists te; exists rho; split3; auto.
subst; simpl; auto.
rewrite level_store_juicy_mem. apply age_level; auto.
split; auto. split. split3; auto.
generalize (eval_expr_relate _ _ _ _ _ e2 jm1 HGG' Hge
  (guard_environ_e1 _ _ _ TC4)); intro.
spec H2; [assumption |].
rewrite <- (age_jm_dry Hage) in H2, He1.
econstructor; try eassumption.
unfold tc_lvalue in TC1. simpl in TC1. auto.
instantiate (1 := force_val (Cop.sem_cast (eval_expr e2 rho)
  (typeof e2) (typeof e1) (m_dry jm))).
rewrite (age_jm_dry Hage).
rewrite cop2_sem_cast'; auto.
2: eapply typecheck_expr_sound; eauto.
eapply cast_exists; eauto. destruct TC4; auto.
eapply Clight.assign_loc_value. apply Hmode.
unfold tc_lvalue in TC1. simpl in TC1. auto.
unfold Mem.storev. simpl m_dry. rewrite (age_jm_dry Hage). exact STORE.
apply (resource_decay_trans _ (Mem.nextblock (m_dry jm1)) _ (m_phi jm1)).
rewrite (age_jm_dry Hage); lia.
apply (age1_resource_decay _ _ Hage).
apply resource_nodecay_decay. apply juicy_store_nodecay.
{ intros. clear - H11' H2 WS.
  destruct H11' as [phi1 [phi2 [? [? ?]]]].
  destruct H0 as [bl [_ H0]]. specialize (H0 (b0,z)).
  hnf in H0. rewrite if_true in H0 by (split; auto; lia).
  destruct H0. hnf in H0.
  apply (resource_at_join _ _ _ (b0,z)) in H. rewrite H0 in H.
  inv H; simpl; apply join_writable01 in RJ; auto;
  unfold perm_of_sh; rewrite if_true by auto; if_tac; constructor. }
rewrite level_store_juicy_mem. split; [apply age_level; auto |].
simpl. unfold inflate_store; rewrite ghost_of_make_rmap.
apply age1_ghost_of, age_jm_phi; auto.
split.
2: { eapply (corable_core _ (m_phi jm1)), pred_hereditary; eauto;
       [| apply age_jm_phi; auto].
     symmetry. apply rmap_ext.
     do 2 rewrite level_core.
     rewrite <- level_juice_level_phi; rewrite level_store_juicy_mem. reflexivity.
     intro loc. unfold store_juicy_mem. simpl.
     rewrite <- core_resource_at. unfold inflate_store.
     rewrite resource_at_make_rmap. rewrite <- core_resource_at.
     case_eq (m_phi jm1 @ loc); intros; auto.
     destruct k0; simpl resource_fmap; repeat rewrite core_YES; auto.
     simpl. rewrite !ghost_of_core.
     unfold inflate_store; rewrite ghost_of_make_rmap; auto. }
rewrite sepcon_comm. rewrite sepcon_assoc.
eapply sepcon_derives; try apply AM; auto.
- rewrite He1'. unfold exact_mapsto.
  rewrite cop2_sem_cast'; auto.
  eapply typecheck_expr_sound; eauto.
- intros ? Hrest.
  destruct Hrest as (w4 & Hnec & Hext).
  destruct (nec_join2 H6 Hnec) as [w2' [w' [? [? ?]]]].
  eapply pred_upclosed; eauto.
  exists w2'; exists w'; split3; auto; eapply pred_nec_hereditary; eauto.
Qed.
End SemanticStore.
