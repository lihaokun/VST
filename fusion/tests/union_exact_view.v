(* Proved exact-memory compatibility layer for narrowing integer reads. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.loadstore_mapsto.
Require Import compcert.common.Memdata.
Require Export VST.floyd.FusionExact.

Local Open Scope Z.
Local Open Scope logic.

Definition address_memvals_at
    (sh : share) (bl : list memval) (a : address) : mpred :=
  predicates_hered.allp
    (res_predicates.jam
      (adr_range_dec a (Zlength bl))
      (fun loc =>
        res_predicates.yesat compcert_rmaps.RML.R.NoneP
          (compcert_rmaps.VAL
            (nth (Z.to_nat (snd loc - snd a)) bl Undef)) sh loc)
      res_predicates.noat).

Lemma address_memvals_at_app : forall sh bl1 bl2 b ofs,
  address_memvals_at sh (bl1 ++ bl2) (b, ofs) =
    address_memvals_at sh bl1 (b, ofs) *
    address_memvals_at sh bl2 (b, ofs + Zlength bl1).
Proof.
  intros.
  pose proof (Zlength_nonneg bl1) as Hlen1.
  pose proof (Zlength_nonneg bl2) as Hlen2.
  unfold address_memvals_at.
  simpl fst; simpl snd.
  apply res_predicates.allp_jam_split2.
  - eexists; apply res_predicates.is_resource_pred_YES_VAL'.
  - eexists; apply res_predicates.is_resource_pred_YES_VAL'.
  - eexists; apply res_predicates.is_resource_pred_YES_VAL'.
  - rewrite Zlength_app. split; intros [b' z]; unfold adr_range; simpl.
    + split.
      * intros [Hb Hz]. subst b'.
        destruct (Z_lt_ge_dec z (ofs + Zlength bl1)).
        -- left; split; auto; lia.
        -- right; split; auto; lia.
      * intros [[Hb Hz] | [Hb Hz]]; subst b'; split; auto; lia.
    + intros [_ Hz1] [_ Hz2]. lia.
  - intros [b' z] Hrange. unfold adr_range in Hrange. simpl in Hrange.
    destruct Hrange as [-> Hz]. simpl.
    f_equal. f_equal.
    rewrite app_nth1; auto.
    rewrite <- ZtoNat_Zlength.
    apply Z2Nat.inj_lt; lia.
  - intros [b' z] Hrange. unfold adr_range in Hrange. simpl in Hrange.
    destruct Hrange as [-> Hz]. simpl.
    f_equal. f_equal.
    rewrite app_nth2.
    + f_equal.
      apply Nat2Z.inj.
      rewrite Nat2Z.inj_sub.
      * rewrite !Z2Nat.id by lia.
        rewrite <- Zlength_correct.
        lia.
      * rewrite <- ZtoNat_Zlength.
        apply Z2Nat.inj_le; lia.
    + rewrite <- ZtoNat_Zlength.
      apply Z2Nat.inj_le; lia.
  - intros loc m sh' k Hrange Hyes Hoption.
    left.
    destruct Hyes as [rsh Hyes].
    unfold res_predicates.yesat_raw in Hyes.
    rewrite Hyes in Hoption.
    inversion Hoption; exact I.
Qed.

Lemma exact_address_mapsto_memvals : forall sh ch v a,
  exact_address_mapsto sh ch v a =
    !! (align_chunk ch | snd a) &&
    address_memvals_at sh (encode_val ch v) a.
Proof.
  intros.
  unfold exact_address_mapsto, res_predicates.address_mapsto_old,
    address_memvals_at, res_predicates.nthbyte.
  rewrite Zlength_correct, encode_val_length, <- size_chunk_conv.
  reflexivity.
Qed.

Lemma address_memvals_at_to_address_mapsto : forall sh ch v a,
  (align_chunk ch | snd a) ->
  address_memvals_at sh (encode_val ch v) a |--
    res_predicates.address_mapsto ch
      (decode_val ch (encode_val ch v)) sh a.
Proof.
  intros sh ch v a Halign.
  constructor.
  unfold address_memvals_at, res_predicates.address_mapsto.
  rewrite Zlength_correct, encode_val_length, <- size_chunk_conv.
  intros w Hw.
  exists (encode_val ch v).
  split.
  - split3; auto using encode_val_length.
  - exact Hw.
Qed.

Definition memvals_at (sh : share) (bl : list memval) (p : val) : mpred :=
  match p with
  | Vptr b ofs => address_memvals_at sh bl (b, Ptrofs.unsigned ofs)
  | _ => FF
  end.

Definition pointer_aligned (ch : memory_chunk) (p : val) : Prop :=
  match p with
  | Vptr _ ofs => (align_chunk ch | Ptrofs.unsigned ofs)
  | _ => False
  end.

Definition pointer_offset (p : val) : Z :=
  match p with Vptr _ ofs => Ptrofs.unsigned ofs | _ => 0 end.

(* The split pointer, including an empty suffix, must not wrap. *)
Lemma memvals_at_app : forall sh bl1 bl2 p,
  isptr p ->
  0 <= pointer_offset p + Zlength bl1 <= Ptrofs.max_unsigned ->
  memvals_at sh (bl1 ++ bl2) p =
    memvals_at sh bl1 p * memvals_at sh bl2 (offset_val (Zlength bl1) p).
Proof.
  intros sh bl1 bl2 p Hp Hr.
  destruct p; try contradiction.
  unfold memvals_at, offset_val; simpl in *.
  pose proof (Ptrofs.unsigned_range i).
  pose proof (Zlength_nonneg bl1).
  rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr (Zlength bl1)) by lia.
  rewrite Ptrofs.unsigned_repr by exact Hr.
  apply address_memvals_at_app.
Qed.

Lemma exact_mapsto_memvals : forall sh ch v p,
  isptr p ->
  exact_mapsto sh ch v p =
    !! pointer_aligned ch p && memvals_at sh (encode_val ch v) p.
Proof.
  intros sh ch v p Hp. destruct p; try contradiction.
  apply exact_address_mapsto_memvals.
Qed.

Lemma memvals_Mint32_has_mapsto : forall sh x p,
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

(* A prefix projection needs no representable pointer to the unused suffix. *)
Lemma memvals_at_prefix : forall sh bl1 bl2 p,
  memvals_at sh (bl1 ++ bl2) p |-- memvals_at sh bl1 p * TT.
Proof.
  intros. destruct p; try apply FF_left.
  unfold memvals_at. rewrite address_memvals_at_app.
  apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* Keep the shipped low-word interface free of an unnecessary p+4 bound. *)
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
