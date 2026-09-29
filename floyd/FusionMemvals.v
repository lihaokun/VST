(* Reusable exact memval ownership operations. See doc/fusion.md for the supported API. *)

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

(* A prefix projection needs no representable pointer to the unused suffix. *)
Lemma memvals_at_prefix : forall sh bl1 bl2 p,
  memvals_at sh (bl1 ++ bl2) p |-- memvals_at sh bl1 p * TT.
Proof.
  intros. destruct p; try apply FF_left.
  unfold memvals_at. rewrite address_memvals_at_app.
  apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.
