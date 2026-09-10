(* Installed-client regression: no test-local view implementation is imported. *)
Require Import VST.floyd.proofauto VST.floyd.FusionStore.
Require Import compcert.common.Memdata.
Local Open Scope logic.
Local Open Scope Z.

(* All three overlapping observations coexist with full exact ownership and an
   unrelated frame. They are conjunctions, never duplicate separating ownership. *)
Lemma borrow_three_views_with_frame : forall sh x p F,
  Archi.big_endian = false -> readable_share sh -> isptr p ->
  0 <= pointer_offset p + 4 <= Ptrofs.max_unsigned ->
  exact_mapsto sh Mint64 (Vlong x) p * F |--
    ((exact_mapsto sh Mint64 (Vlong x) p &&
      (mapsto sh tuint p (Vint (Int64.loword x)) * TT) &&
      (mapsto sh tuint (offset_val 4 p) (Vint (Int64.hiword x)) * TT) &&
      (mapsto sh tulong p (Vlong x) * TT)) * F).
Proof.
  intros sh x p F Hle Hread Hp Hrange.
  apply sepcon_derives; [| apply derives_refl].
  repeat apply andp_right.
  - apply derives_refl.
  - apply exact_Mint64_has_low32_mapsto_le; assumption.
  - apply exact_Mint64_has_high32_mapsto_le; assumption.
  - apply exact_Mint64_has_full_mapsto_frame; assumption.
Qed.

(* The prefix interface still works without constructing a suffix pointer. *)
Lemma borrow_low_view_with_frame : forall sh x p F,
  Archi.big_endian = false -> readable_share sh ->
  exact_mapsto sh Mint64 (Vlong x) p * F |--
    ((exact_mapsto sh Mint64 (Vlong x) p &&
      (mapsto sh tuint p (Vint (Int64.loword x)) * TT)) * F).
Proof.
  intros; apply sepcon_derives; [| apply derives_refl].
  apply andp_right; [apply derives_refl |].
  apply exact_Mint64_has_low32_mapsto_le; assumption.
Qed.

(* Concrete representation ambiguity, not a general rmap nonderivability claim. *)
Lemma wide_decode_does_not_fix_low_decode :
  exists bl,
    length bl = size_chunk_nat Mint64 /\
    decode_val Mint64 bl = Vlong Int64.zero /\
    bl <> encode_val Mint64 (Vlong Int64.zero) /\
    decode_val Mint32 (firstn 4 bl) = Vundef.
Proof.
  exists (inj_value Q64 (Vlong Int64.zero)).
  vm_compute. repeat split; discriminate.
Qed.

Fail Check union_exact_view.exact_Mint64_has_low32_mapsto_le.
Fail Check exact_semax.
Print Assumptions borrow_three_views_with_frame.
Print Assumptions borrow_low_view_with_frame.
Print Assumptions wide_decode_does_not_fix_low_decode.
