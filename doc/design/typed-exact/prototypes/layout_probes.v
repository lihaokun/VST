Set Default Timeout 30.
Require Import VST.floyd.proofauto VST.floyd.FusionStore.
Require Import VST.floyd.type_induction.
Require Import typed_exact_prototype layout_cases.
Import TypedExactPrototype.
Local Open Scope logic.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Lemma cell_a_wide_encoding : forall sh x p,
  exact_representation sh (Tunion _cell_a noattr) (inr (Vlong x)) p =
  exact_mapsto sh Mint64 (Vlong x) p.
Proof.
  intros. unfold exact_representation at 1. rewrite type_func_eq. simpl.
  cbv [eq_rect_r eq_rect]. unfold withspacer, spacer. simpl. reflexivity.
Qed.

Lemma cell_a_low_keeps_padding : forall sh x p,
  exact_representation sh (Tunion _cell_a noattr) (inl (Vint x)) p =
  exact_mapsto sh Mint32 (Vint x) p * memory_block sh 4 (offset_val 4 p).
Proof.
  intros. unfold exact_representation at 1. rewrite type_func_eq. simpl.
  cbv [eq_rect_r eq_rect]. unfold withspacer, spacer. simpl. reflexivity.
Qed.

Lemma framed_record_encoding : forall sh tag x p,
  exact_representation sh (Tstruct _record_with_frame noattr) (Vint tag, inl (Vlong x)) p =
  (exact_mapsto sh Mint32 (Vint tag) p * memory_block sh 4 (offset_val 4 p)) *
  exact_mapsto sh Mint64 (Vlong x) (offset_val 8 p).
Proof.
  intros. unfold exact_representation at 1. rewrite type_func_eq. simpl.
  cbv [eq_rect_r eq_rect]. unfold withspacer, spacer, at_offset.
  destruct p; simpl; try reflexivity. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma cell_b_wide_encoding : forall sh x p,
  exact_representation sh (Tunion _cell_b noattr) (inl (Vlong x)) p =
  exact_mapsto sh Mint64 (Vlong x) p.
Proof.
  intros. unfold exact_representation at 1. rewrite type_func_eq. simpl.
  cbv [eq_rect_r eq_rect]. unfold withspacer, spacer. simpl. reflexivity.
Qed.
