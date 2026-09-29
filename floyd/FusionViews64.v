(* Numeric view projections; exact ownership is retained by borrowed reads. *)
Require Import VST.floyd.proofauto.
Require Import compcert.common.Memdata.
Require Export VST.floyd.FusionMemvals.
Local Open Scope Z.
Local Open Scope logic.

Local Lemma memvals_Mint32_has_mapsto : forall sh x p,
  readable_share sh -> pointer_aligned Mint32 p ->
  memvals_at sh (encode_val Mint32 (Vint x)) p |-- mapsto sh tuint p (Vint x).
Proof.
  intros sh x p Hread HA. destruct p; try contradiction.
  unfold memvals_at, mapsto; simpl.
  destruct (readable_share_dec sh); [| contradiction].
  apply orp_right1, andp_right; [apply prop_right; exact I |].
  replace (Vint x) with (decode_val Mint32 (encode_val Mint32 (Vint x))).
  - apply (address_memvals_at_to_address_mapsto sh Mint32 (Vint x)
      (b, Ptrofs.unsigned i)); exact HA.
  - unfold encode_val, decode_val. rewrite proj_inj_bytes.
    f_equal. apply decode_encode_int_4.
Qed.

(* Specialize Memdata.bytes_of_int64 to Vlong and little-endian targets. *)
Lemma encode_val_Mint64_Vlong_split_le :
  Archi.big_endian = false ->
  forall x,
    encode_val Mint64 (Vlong x) =
      encode_val Mint32 (Vint (Int64.loword x)) ++
      encode_val Mint32 (Vint (Int64.hiword x)).
Proof.
  intros Hle x.
  unfold encode_val, inj_bytes.
  rewrite <- map_app.
  f_equal.
  unfold encode_int, rev_if_be.
  rewrite Hle.
  apply bytes_of_int64.
Qed.

(* Keep the low-word interface free of an unnecessary p+4 bound. *)
Lemma exact_Mint64_has_low32_mapsto_le : forall sh x p,
  Archi.big_endian = false ->
  readable_share sh ->
  exact_mapsto sh Mint64 (Vlong x) p |--
    mapsto sh tuint p (Vint (Int64.loword x)) * TT.
Proof.
  intros sh x p Hle Hread.
  destruct p as [| | | | |b ofs]; try apply FF_left.
  rewrite exact_mapsto_memvals by exact I.
  apply derives_extract_prop; intro Halign.
  rewrite (encode_val_Mint64_Vlong_split_le Hle x).
  eapply derives_trans; [apply memvals_at_prefix |].
  apply sepcon_derives; [| apply derives_refl].
  apply (memvals_Mint32_has_mapsto sh (Int64.loword x) (Vptr b ofs) Hread).
  simpl in Halign |- *. destruct Halign as [k Hk].
  refine (ex_intro _ (2 * k)%Z _). lia.
Qed.

(* Retaining Mint64 alignment is essential for the reverse direction. *)
Lemma exact_Mint64_split32_le : forall sh x p,
  Archi.big_endian = false -> isptr p ->
  0 <= pointer_offset p + 4 <= Ptrofs.max_unsigned ->
  exact_mapsto sh Mint64 (Vlong x) p =
    !! pointer_aligned Mint64 p &&
    (exact_mapsto sh Mint32 (Vint (Int64.loword x)) p *
     exact_mapsto sh Mint32 (Vint (Int64.hiword x)) (offset_val 4 p)).
Proof.
  intros sh x p Hle Hp Hr. destruct p; try contradiction.
  unfold exact_mapsto, offset_val, pointer_aligned; simpl in *.
  rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr 4) by computable.
  rewrite Ptrofs.unsigned_repr by exact Hr.
  rewrite !exact_address_mapsto_memvals.
  rewrite (encode_val_Mint64_Vlong_split_le Hle x), address_memvals_at_app.
  change (Zlength (encode_val Mint32 (Vint (Int64.loword x)))) with 4.
  rewrite sepcon_andp_prop, sepcon_andp_prop'.
  apply pred_ext; entailer!.
  simpl in H |- *. destruct H as [k Hk]. split; first
    [refine (ex_intro _ (2 * k)%Z _); lia
    | refine (ex_intro _ (2 * k + 1)%Z _); lia].
Qed.

Lemma exact_Mint32_has_mapsto : forall sh x p,
  readable_share sh ->
  exact_mapsto sh Mint32 (Vint x) p |-- mapsto sh tuint p (Vint x).
Proof.
  intros sh x p Hread. destruct p; try apply FF_left.
  rewrite exact_mapsto_memvals by exact I.
  apply derives_extract_prop; intro HA.
  apply memvals_Mint32_has_mapsto; assumption.
Qed.

Lemma exact_Mint64_has_high32_mapsto_le : forall sh x p,
  Archi.big_endian = false -> readable_share sh -> isptr p ->
  0 <= pointer_offset p + 4 <= Ptrofs.max_unsigned ->
  exact_mapsto sh Mint64 (Vlong x) p |--
    mapsto sh tuint (offset_val 4 p) (Vint (Int64.hiword x)) * TT.
Proof.
  intros sh x p Hle Hread Hp Hr.
  rewrite exact_Mint64_split32_le by assumption.
  apply andp_left2. rewrite sepcon_comm.
  apply sepcon_derives; [apply exact_Mint32_has_mapsto; assumption | apply TT_right].
Qed.

Lemma exact_Mint64_has_mapsto : forall sh x p,
  readable_share sh ->
  exact_mapsto sh Mint64 (Vlong x) p |-- mapsto sh tulong p (Vlong x).
Proof.
  intros sh x p Hread.
  destruct p as [| | | | |b ofs]; try apply FF_left.
  unfold exact_mapsto. rewrite exact_address_mapsto_memvals.
  apply derives_extract_prop; intro HA.
  unfold mapsto; simpl.
  destruct (readable_share_dec sh); [| contradiction].
  apply orp_right1, andp_right; [apply prop_right; exact I |].
  replace (Vlong x) with (decode_val Mint64 (encode_val Mint64 (Vlong x))).
  - apply (address_memvals_at_to_address_mapsto sh Mint64 (Vlong x)
      (b, Ptrofs.unsigned ofs)); exact HA.
  - unfold encode_val, decode_val. rewrite proj_inj_bytes.
    f_equal. apply decode_encode_int_8.
Qed.

Lemma exact_Mint64_has_full_mapsto_frame : forall sh x p,
  readable_share sh ->
  exact_mapsto sh Mint64 (Vlong x) p |-- mapsto sh tulong p (Vlong x) * TT.
Proof.
  intros. eapply derives_trans; [apply exact_Mint64_has_mapsto; assumption |].
  rewrite <- (sepcon_emp (mapsto sh tulong p (Vlong x))) at 1.
  apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.
