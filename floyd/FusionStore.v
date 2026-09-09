Require Import VST.floyd.proofauto.
Require Export VST.floyd.FusionExact.
Import LiftNotation.
Local Open Scope logic.

(* Ordinary Floyd store: replace one SEP entry and retain its ramified frame. *)
Lemma semax_store_exact_nth_ram :
  forall {Espec : OracleKind} {cs : compspecs}
    n Delta P Q R e1 e2 Pre Post p v sh t1 ch,
    typeof e1 = t1 ->
    access_mode t1 = By_value ch ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      local (`(eq p) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      local (`(eq v) (eval_expr (Ecast e2 t1))) ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    (Pre |-- mapsto_ sh t1 p * (exact_mapsto sh ch v p -* Post)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 t1) ->
    @semax cs Espec Delta
      (|> PROPx P (LOCALx Q (SEPx R))) (Sassign e1 e2)
      (normal_ret_assert (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros Espec cs n Delta P Q R e1 e2 Pre Post p v sh t1 ch
    Hty Hmode Hp Hv Hnth Hsh Hram Htc.
  evar (F : environ -> mpred).
  eapply semax_pre;
    [| eapply semax_post';
       [| apply VST.floyd.SeparationLogicAsLogicSoundness.MainTheorem.semax_store_exact with (P := F) (ch := ch) (sh := sh);
          [auto | rewrite Hty; exact Hmode]]].
  - change (local (tc_environ Delta) && |> PROPx P (LOCALx Q (SEPx R)) |--
      |> (tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 (typeof e1)) &&
        (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * F))).
    unfold F.
    apply later_left2.
    apply andp_right; [subst; auto |].
    simpl lifted.
    change (@LiftNatDed environ mpred Nveric) with (@LiftNatDed' mpred Nveric).
    rewrite (add_andp _ _ Hp), (add_andp _ _ Hv).
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    rewrite !(andp_comm _ (local _)).
    rewrite <- (andp_dup (local (`(eq p) (eval_lvalue e1)))), andp_assoc.
    do 3 rewrite <- local_sepcon_assoc2. rewrite <- local_sepcon_assoc1.
    eapply derives_trans.
    + apply sepcon_derives; [| apply derives_refl].
      instantiate (1 := `(mapsto_ sh (typeof e1)) (eval_lvalue e1) *
        `(exact_mapsto sh ch v p -* Post)).
      unfold local, lift1; unfold_lift; intro rho; simpl.
      subst t1. normalize.
    + rewrite sepcon_assoc. apply derives_refl.
  - change (local (tc_environ Delta) &&
      (`(exact_mapsto sh ch)
        (eval_expr (Ecast e2 (typeof e1))) (eval_lvalue e1) * F) |--
      PROPx P (LOCALx Q (SEPx (replace_nth n R Post)))).
    apply andp_left2. unfold F.
    rewrite <- sepcon_assoc.
    rewrite !local_sepcon_assoc2, <- !local_sepcon_assoc1.
    erewrite SEP_replace_nth_isolate with (Rn' := Post), <- insert_SEP by eauto.
    apply sepcon_derives; auto.
    change (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))
      with (eval_expr (Ecast e2 (typeof e1))).
    unfold local, lift1; unfold_lift; intro rho; simpl.
    normalize.
    subst t1. apply modus_ponens_wand.
Qed.
