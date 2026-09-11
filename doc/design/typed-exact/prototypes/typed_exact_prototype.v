(* 设计探针，不是已发布的 Fusion API。 *)
Set Default Timeout 30.
Require Import VST.floyd.proofauto VST.floyd.FusionStore.
Require Import VST.floyd.type_induction VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred.
Import VST.floyd.aggregate_pred.aggregate_pred.
Import VST.floyd.aggregate_pred.auxiliary_pred.
Local Open Scope logic.

Module TypedExactPrototype.
Section Predicates.
Context {cs : compspecs}.

Definition exact_representation (sh : share) : forall t, reptype t -> val -> mpred :=
  type_func (fun t => reptype t -> val -> mpred)
    (fun t v p =>
      if type_is_volatile t then memory_block sh (sizeof t) p
      else match access_mode t with
           | By_value ch => exact_mapsto sh ch (repinject t v) p
           | _ => FF
           end)
    (fun t n a P v => array_pred 0 (Z.max 0 n)
       (fun i v => at_offset (P v) (sizeof t * i)) (unfold_reptype v))
    (fun id a P v => struct_data_at_rec_aux sh
       (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_data_at_rec_aux sh
       (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v)).

Definition exact_data_at sh t (v : reptype t) p : mpred :=
  data_at sh t v p && exact_representation sh t v p.

Definition exact_field_at sh t gfs (v : reptype (nested_field_type t gfs)) p : mpred :=
  field_at sh t gfs v p &&
  at_offset (exact_representation sh (nested_field_type t gfs) v) (nested_field_offset t gfs) p.

Lemma exact_data_at_forget : forall sh t v p,
  exact_data_at sh t v p |-- data_at sh t v p.
Proof. intros. apply andp_left1. apply derives_refl. Qed.

Lemma exact_field_at_forget : forall sh t gfs v p,
  exact_field_at sh t gfs v p |-- field_at sh t gfs v p.
Proof. intros. apply andp_left1. apply derives_refl. Qed.

Lemma exact_data_at_local_facts : forall sh t v p,
  exact_data_at sh t v p |-- !! (field_compatible t [] p /\ value_fits t v).
Proof. intros. eapply derives_trans; [apply exact_data_at_forget | apply data_at_local_facts]. Qed.

Lemma exact_representation_tulong : forall sh x p,
  exact_representation sh tulong (Vlong x) p = exact_mapsto sh Mint64 (Vlong x) p.
Proof. intros. unfold exact_representation. rewrite type_func_eq. reflexivity. Qed.

Lemma exact_representation_tuint : forall sh x p,
  exact_representation sh tuint (Vint x) p = exact_mapsto sh Mint32 (Vint x) p.
Proof. intros. unfold exact_representation. rewrite type_func_eq. reflexivity. Qed.

Lemma exact_data_at_tulong_intro : forall sh x p,
  readable_share sh -> field_compatible tulong [] p ->
  exact_mapsto sh Mint64 (Vlong x) p |-- exact_data_at sh tulong (Vlong x) p.
Proof.
  intros sh x p Hsh Hfc. unfold exact_data_at.
  rewrite exact_representation_tulong. apply andp_right; [| apply derives_refl].
  rewrite <- (mapsto_data_at' sh tulong (Vlong x) (Vlong x) p)
    by (try reflexivity; auto; apply JMeq_refl).
  apply exact_Mint64_has_mapsto. exact Hsh.
Qed.

Lemma exact_data_at_low32_borrow : forall sh x p,
  Archi.big_endian = false -> readable_share sh -> field_compatible tuint [] p ->
  exact_data_at sh tulong (Vlong x) p |-- data_at sh tuint (Vint (Int64.loword x)) p * TT.
Proof.
  intros sh x p Hle Hsh Hfc. unfold exact_data_at.
  rewrite exact_representation_tulong. apply andp_left2.
  rewrite <- (mapsto_data_at' sh tuint (Vint (Int64.loword x)) (Vint (Int64.loword x)) p)
    by (try reflexivity; auto; apply JMeq_refl).
  apply exact_Mint64_has_low32_mapsto_le; assumption.
Qed.

Lemma exact_data_at_low32_views : forall sh x p,
  Archi.big_endian = false -> readable_share sh -> field_compatible tuint [] p ->
  exact_data_at sh tulong (Vlong x) p |--
    (data_at sh tuint (Vint (Int64.loword x)) p * TT) && exact_data_at sh tulong (Vlong x) p.
Proof.
  intros. apply andp_right; [apply exact_data_at_low32_borrow; assumption | apply derives_refl].
Qed.

Lemma data_at_tulong_store_ramify : forall sh old x p,
  writable_share sh ->
  data_at sh tulong old p |--
    mapsto_ sh tulong p * (exact_mapsto sh Mint64 (Vlong x) p -* exact_data_at sh tulong (Vlong x) p).
Proof.
  intros sh old x p Hw.
  apply derives_trans with
    (!! (field_compatible tulong [] p /\ value_fits tulong old) && data_at sh tulong old p).
  - apply andp_right; [apply data_at_local_facts | apply derives_refl].
  - apply derives_extract_prop. intros [Hfc Hfit].
    rewrite <- (mapsto_data_at' sh tulong old old p)
      by (try reflexivity; auto; apply JMeq_refl).
    apply RAMIF_PLAIN.solve with emp.
    + rewrite sepcon_emp. apply mapsto_mapsto_.
    + rewrite emp_sepcon. apply exact_data_at_tulong_intro; auto.
Qed.

(* 用户面候选：所有前提/后置均为typed ownership，mapsto只在内部证明中使用。 *)
Lemma semax_store_exact_data_at_tulong :
  forall {Espec : OracleKind} n Delta P Q R e1 e2 old x sh p,
  typeof e1 = tulong ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (fun rho => p = eval_lvalue e1 rho) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    local (fun rho => Vlong x = eval_expr (Ecast e2 tulong) rho) ->
  nth_error R n = Some (data_at sh tulong old p) ->
  writable_share sh ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 tulong) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) (Sassign e1 e2)
    (normal_ret_assert (PROPx P (LOCALx Q
      (SEPx (replace_nth n R (exact_data_at sh tulong (Vlong x) p)))))).
Proof.
  intros Espec n Delta P Q R e1 e2 old x sh p Hty Haddr Hval Hnth Hsh Htc.
  eapply semax_pre0; [apply now_later |].
  eapply semax_store_exact_nth_ram with
    (n := n) (Pre := data_at sh tulong old p)
    (Post := exact_data_at sh tulong (Vlong x) p)
    (p := p) (v := Vlong x) (sh := sh) (t1 := tulong) (ch := Mint64); eauto.
  apply data_at_tulong_store_ramify. exact Hsh.
Qed.

End Predicates.
End TypedExactPrototype.
Print Assumptions TypedExactPrototype.exact_data_at_low32_borrow.
Print Assumptions TypedExactPrototype.data_at_tulong_store_ramify.
Print Assumptions TypedExactPrototype.semax_store_exact_data_at_tulong.
