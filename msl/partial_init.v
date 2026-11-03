(* M3：部分初始化（msl/partial_init.v）
   提供公开定义 partial_cell / partial_init / partial_resume 与九条公开引理：
   partial_init_empty / full / overfull / focus / restore / put / forget / indexed / fixed。
   逻辑上下文同 M2（NatDed + SepLog + ClassicalSep + CorableSepLog，载体 L）。

   定义不要求值类型 V 的默认值：None 状态在证明内使用显式 option 默认
   （Inhabitant (option V) 由 zlist 的全局实例给 None）；读槽位的接口带 {dS : Inhabitant S}。
   done 是唯一权威前缀，前沿 = Zlength done；状态表 filled (map (@Some V) done) None
   (Zlength slots)；长度 guard 用 &&；partial_resume 的两个 continuation 用 && 共享同一余部，
   不用 * 复制。restore / put 不加边界前提；forget 要求真实 E→U 蕴含；
   indexed / fixed 是对固定长度数组旧 indexed 表示的两个等式适配，只读初始化前缀，
   fixed 不要求 values 长到全部槽数。 *)
Set Default Timeout 300.

Require Import VST.msl.base.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.iter_sepcon.
Require Import VST.zlist.sublist.
Require Import VST.zlist.frontier.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.

Local Open Scope logic.

(* ================= 内部辅助：filled 表的读取 ================= *)

(* 表的前缀段逐位读原前缀。 *)
Lemma filled_Znth_lt {A} {dA : Inhabitant A} :
  forall (prefix : list A) (d : A) (n i : Z),
    (i < Zlength prefix)%Z -> Znth i (filled prefix d n) = Znth i prefix.
Proof.
  intros prefix d n i H. unfold filled.
  rewrite app_Znth1 by exact H.
  reflexivity.
Qed.

(* 表的后缀段逐位读尾默认值（落在 Zrepeat 段）。 *)
Lemma filled_Znth_ge {A} {dA : Inhabitant A} :
  forall (prefix : list A) (d : A) (n i : Z),
    (Zlength prefix <= i)%Z ->
    Znth i (filled prefix d n) =
    Znth (i - Zlength prefix) (Zrepeat d (n - Zlength prefix)).
Proof.
  intros prefix d n i H. unfold filled.
  rewrite app_Znth2 by lia.
  reflexivity.
Qed.

(* ================= 公开定义 ================= *)

Section PartialInit.

  Context {S V : Type}.
  Context {L : Type}.
  Context {ND : NatDed L}.
  Context {SL : SepLog L}.
  Context {ClS : ClassicalSep L}.
  Context {CoSL : CorableSepLog L}.

  (* 定义 1/3：槽位状态——未初始化为 U s，已初始化为 v 则 E s v。
     取当前槽的接口带 {dS : Inhabitant S} 由使用处提供；定义本身不要求 V 的默认值。 *)
  Definition partial_cell (U : S -> L) (E : S -> V -> L)
      (s : S) (o : option V) : L :=
    match o with
    | None => U s
    | Some v => E s v
    end.

  (* 定义 2/3：部分初始化状态。done 是唯一权威前缀，前沿 = Zlength done；
     状态表 filled (map (@Some V) done) None (Zlength slots)；长度 guard 用 &&。 *)
  Definition partial_init (U : S -> L) (E : S -> V -> L)
      (slots : list S) (done : list V) : L :=
    !! ((Zlength done <= Zlength slots)%Z) &&
    iter_sepcon2 (partial_cell U E) slots
      (filled (map (@Some V) done) None (Zlength slots)).

  (* 定义 3/3：前沿恢复接口。两个 continuation 用 && 共享同一余部（不用 * 复制）。 *)
  Definition partial_resume {dS : Inhabitant S}
      (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V) : L :=
    (U (Znth (Zlength done) slots) -* partial_init U E slots done) &&
    (ALL v : V, E (Znth (Zlength done) slots) v -*
            partial_init U E slots (done ++ [v])).

  (* ================= 内部辅助：配对 fold 的四种展开 ================= *)

  (* 正长度 Zrepeat 可拆出头部。 *)
  Lemma Zrepeat_cons_S {W : Type} :
    forall (y : W) (k : Z), (0 <= k)%Z -> Zrepeat y (Z.succ k) = y :: Zrepeat y k.
  Proof.
    intros y k Hk.
    unfold Zrepeat.
    rewrite Z2Nat.inj_succ by lia.
    cbn [repeat].
    reflexivity.
  Qed.

  (* 常量状态表的配对 fold 逐槽化。 *)
  Lemma iter_sepcon2_Zrepeat {W : Type} :
    forall (p : S -> W -> L) (l1 : list S) (y : W),
      iter_sepcon2 p l1 (Zrepeat y (Zlength l1)) = iter_sepcon (fun s => p s y) l1.
  Proof.
    intros p l1 y.
    induction l1 as [|a l1 IH].
    - reflexivity.
    - rewrite Zlength_cons.
      rewrite Zrepeat_cons_S by apply Zlength_nonneg.
      cbn [iter_sepcon2 iter_sepcon].
      rewrite IH.
      reflexivity.
  Qed.

  (* 全 Some 状态表的配对 fold 与取值函数的配对 fold 重合。 *)
  Lemma iter_sepcon2_cell_some :
    forall (U : S -> L) (E : S -> V -> L) (l1 : list S) (l2 : list V),
      iter_sepcon2 (partial_cell U E) l1 (map (@Some V) l2) = iter_sepcon2 E l1 l2.
  Proof.
    intros U E l1 l2.
    revert l2.
    induction l1 as [|a l1 IH]; intros [|b l2].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn [iter_sepcon2 map partial_cell].
      rewrite IH.
      reflexivity.
  Qed.

  (* 配对 fold 到单列表 fold 的真实蕴含：逐槽 p s w |-- g s。 *)
  Lemma iter_sepcon2_derives_single {W : Type} :
    forall (p : S -> W -> L) (g : S -> L) (l1 : list S) (l2 : list W),
      (forall s w, p s w |-- g s) ->
      iter_sepcon2 p l1 l2 |-- iter_sepcon g l1.
  Proof.
    intros p g l1 l2 H.
    revert l2.
    induction l1 as [|a l1 IH]; intros l2.
    - destruct l2 as [|b l2]; cbn [iter_sepcon2 iter_sepcon].
      + apply derives_refl.
      + apply FF_left.
    - destruct l2 as [|b l2]; cbn [iter_sepcon2 iter_sepcon].
      + apply FF_left.
      + apply sepcon_derives.
        * apply H.
        * apply IH.
  Qed.

  (* 等长两表上的配对 fold 展开为 upto 上的位置 fold。 *)
  Lemma iter_sepcon2_upto_eq {W : Type} {dS : Inhabitant S} {dW : Inhabitant W} :
    forall (p : S -> W -> L) (l1 : list S) (l2 : list W),
      Zlength l1 = Zlength l2 ->
      iter_sepcon2 p l1 l2 =
      iter_sepcon (fun i => p (Znth i l1) (Znth i l2))
                  (upto (Z.to_nat (Zlength l1))).
  Proof.
    intros p l1 l2 Hlen.
    revert l2 Hlen.
    induction l1 as [|a l1 IH]; intros l2 Hlen.
    - destruct l2 as [|b l2].
      + reflexivity.
      + replace (Zlength (@nil S)) with 0%Z in Hlen by reflexivity.
        rewrite Zlength_cons in Hlen. exfalso.
        pose proof (Zlength_nonneg l2). lia.
    - destruct l2 as [|b l2].
      + replace (Zlength (@nil W)) with 0%Z in Hlen by reflexivity.
        rewrite Zlength_cons in Hlen. exfalso.
        pose proof (Zlength_nonneg l1). lia.
      + rewrite !Zlength_cons in Hlen.
        assert (Heq : Zlength l1 = Zlength l2) by lia.
        cbn [iter_sepcon2].
        rewrite Zlength_cons.
        rewrite Z2Nat.inj_succ by apply Zlength_nonneg.
        cbn [upto iter_sepcon].
        rewrite <- iter_sepcon_map.
        rewrite !Znth_0_cons.
        f_equal.
        rewrite (IH l2 Heq).
        apply iter_sepcon_func_strong.
        intros x Hin.
        rewrite In_upto in Hin.
        destruct Hin as [Hx0 _].
        replace (Z.succ x) with (x + 1)%Z by apply Z.add_1_r.
        rewrite !Znth_pos_cons by lia.
        replace ((x + 1) - 1)%Z with x by lia.
        reflexivity.
  Qed.

  (* ================= 公开引理 ================= *)

  (* Step P3: empty——空前缀退化为对全部槽位的 U fold；guard 为真，无 V 默认值。 *)
  Lemma partial_init_empty :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S),
      partial_init U E slots ([] : list V) = iter_sepcon U slots.
  Proof.
    intros U E slots.
    unfold partial_init.
    cbn [map Zlength].
    rewrite filled_empty.
    rewrite iter_sepcon2_Zrepeat.
    cbn [partial_cell].
    rewrite prop_true_andp by apply Zlength_nonneg.
    apply iter_sepcon_func.
    intros s.
    reflexivity.
  Qed.

  (* Step P3: full——前缀长度等于槽数时状态表恰为全 Some 表，退化为 E fold。 *)
  Lemma partial_init_full :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V),
      (Zlength done = Zlength slots)%Z ->
      partial_init U E slots done = iter_sepcon2 E slots done.
  Proof.
    intros U E slots done H.
    unfold partial_init.
    rewrite prop_true_andp by lia.
    assert (Hn : (Zlength slots)%Z = Zlength (map (@Some V) done))
      by (rewrite Zlength_map; symmetry; exact H).
    rewrite Hn, filled_full.
    apply iter_sepcon2_cell_some.
  Qed.

  (* Step P3: overfull——done 超过槽数时 guard 为假，整体为 FF；不靠截断。 *)
  Lemma partial_init_overfull :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V),
      (Zlength slots < Zlength done)%Z ->
      partial_init U E slots done = FF.
  Proof.
    intros U E slots done H.
    unfold partial_init.
    rewrite prop_false_andp by lia.
    reflexivity.
  Qed.

  (* Step P3: focus——j = 前沿严格小于槽数时，从部分初始化状态借出前沿槽位的 U，
     余部同时支撑两个 continuation（&& 共享，不复制）。 *)
  Lemma partial_init_focus {dS : Inhabitant S} :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V),
      (Zlength done < Zlength slots)%Z ->
      partial_init U E slots done |--
        U (Znth (Zlength done) slots) * partial_resume U E slots done.
  Proof.
    intros U E slots done Hlt.
    unfold partial_resume.
    unfold partial_init.
    rewrite prop_true_andp by lia.
    assert (HTlen : (Zlength slots)%Z =
              Zlength (filled (map (@Some V) done) None (Zlength slots))).
    { rewrite filled_length by (rewrite Zlength_map; lia). reflexivity. }
    rewrite (iter_sepcon2_Znth (partial_cell U E) slots
               (filled (map (@Some V) done) None (Zlength slots))
               (i := Zlength (map (@Some V) done))
               ltac:(rewrite Zlength_map; pose proof (Zlength_nonneg done); lia)
               HTlen).
    rewrite (filled_next (map (@Some V) done) None (Zlength slots)
               ltac:(rewrite Zlength_map; exact Hlt)).
    cbn [partial_cell].
    rewrite Zlength_map.
    apply sepcon_derives; [apply derives_refl |].
    apply andp_right.
    - (* 恢复支：借出的 U s 拼回前沿位置即回到 partial_init *)
      rewrite <- wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply derives_refl.
    - (* 推进支：在前沿位置写入 Some v 后表沿 filled_step 前进一格 *)
      apply allp_right.
      intros v.
      rewrite <- wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply andp_right;
        [ apply prop_right; rewrite Zlength_app;
          replace (Zlength [v]) with 1%Z by reflexivity; lia
        | ].
      rewrite map_app.
      cbn [map].
      rewrite <- (filled_step (map (@Some V) done) None (Zlength slots) (Some v)
                    ltac:(rewrite Zlength_map; exact Hlt)).
      rewrite (Zlength_map V (option V) (@Some V) done).
      assert (HTlen2 : (Zlength slots)%Z =
                Zlength (upd_Znth (Zlength done)
                           (filled (map (@Some V) done) None (Zlength slots))
                           (Some v))).
      { rewrite upd_Znth_Zlength
          by (rewrite <- HTlen; pose proof (Zlength_nonneg done); lia).
        exact HTlen. }
      rewrite (iter_sepcon2_Znth (partial_cell U E) slots
                 (upd_Znth (Zlength done)
                    (filled (map (@Some V) done) None (Zlength slots)) (Some v))
                 (i := Zlength done)
                 ltac:(pose proof (Zlength_nonneg done); lia)
                 HTlen2).
      rewrite (upd_Znth_same (Zlength done)
                 (filled (map (@Some V) done) None (Zlength slots)) (Some v))
        by (rewrite <- HTlen; pose proof (Zlength_nonneg done); lia).
      rewrite (remove_upd_Znth (Zlength done)
                 (filled (map (@Some V) done) None (Zlength slots)) (Some v))
        by (rewrite <- HTlen; pose proof (Zlength_nonneg done); lia).
      cbn [partial_cell].
      apply derives_refl.
  Qed.

  (* Step P3: restore——持有前沿槽位的 U 与恢复接口时回到 partial_init；无边界前提。 *)
  Lemma partial_init_restore {dS : Inhabitant S} :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V),
      U (Znth (Zlength done) slots) * partial_resume U E slots done |--
      partial_init U E slots done.
  Proof.
    intros U E slots done.
    unfold partial_resume.
    eapply derives_trans with
      (Q := U (Znth (Zlength done) slots) *
            (U (Znth (Zlength done) slots) -* partial_init U E slots done)).
    - apply sepcon_derives; [apply derives_refl |].
      apply andp_left1.
      apply derives_refl.
    - rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply derives_refl.
  Qed.

  (* Step P3: put——持有前沿槽位的 E v 与恢复接口时推进到 done ++ [v]；无边界前提。 *)
  Lemma partial_init_put {dS : Inhabitant S} :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V) (v : V),
      E (Znth (Zlength done) slots) v * partial_resume U E slots done |--
      partial_init U E slots (done ++ [v]).
  Proof.
    intros U E slots done v.
    unfold partial_resume.
    eapply derives_trans with
      (Q := E (Znth (Zlength done) slots) v *
            (E (Znth (Zlength done) slots) v -* partial_init U E slots (done ++ [v]))).
    - apply sepcon_derives; [apply derives_refl |].
      apply andp_left2.
      eapply allp_left.
      apply derives_refl.
    - rewrite (sepcon_comm (E (Znth (Zlength done) slots) v)
                 (E (Znth (Zlength done) slots) v -*
                  partial_init U E slots (done ++ [v]))).
      apply wand_sepcon_adjoint.
      apply derives_refl.
  Qed.

  (* Step P3: forget——真实的逐槽 E→U 蕴含把部分初始化状态弱化为纯 U fold。 *)
  Lemma partial_init_forget :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V),
      (forall s : S, forall v : V, E s v |-- U s) ->
      partial_init U E slots done |-- iter_sepcon U slots.
  Proof.
    intros U E slots done H.
    unfold partial_init.
    apply andp_left2.
    apply (iter_sepcon2_derives_single (partial_cell U E) U slots
             (filled (map (@Some V) done) None (Zlength slots))).
    intros s [v |]; cbn [partial_cell].
    - apply H.
    - apply derives_refl.
  Qed.

  (* Step P3: indexed——合法前缀下与 upto 上的位置 fold 的等式适配；
     i < 前沿读 E，i >= 前沿读 U，无 V 默认值泄露进未填后缀。 *)
  Lemma partial_init_indexed {dS : Inhabitant S} {dV : Inhabitant V} :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (done : list V),
      (Zlength done <= Zlength slots)%Z ->
      partial_init U E slots done =
        iter_sepcon
          (fun i : Z => if Z_lt_dec i (Zlength done)
                        then E (Znth i slots) (Znth i done)
                        else U (Znth i slots))
          (upto (Z.to_nat (Zlength slots))).
  Proof.
    intros U E slots done Hle.
    unfold partial_init.
    rewrite prop_true_andp by lia.
    rewrite (iter_sepcon2_upto_eq (partial_cell U E) slots
               (filled (map (@Some V) done) None (Zlength slots)))
      by (rewrite filled_length by (rewrite Zlength_map; lia); reflexivity).
    apply iter_sepcon_func_strong.
    intros i Hin.
    rewrite In_upto in Hin.
    destruct Hin as [Hx0 Hin2].
    rewrite Z2Nat.id in Hin2 by apply Zlength_nonneg.
    destruct (Z_lt_dec i (Zlength done)) as [Hlt | Hge].
    - rewrite (filled_Znth_lt (map (@Some V) done) None (Zlength slots) i
                 ltac:(rewrite Zlength_map; exact Hlt)).
      rewrite (Znth_map i (@Some V) done (conj Hx0 Hlt)).
      reflexivity.
    - rewrite (filled_Znth_ge (map (@Some V) done) None (Zlength slots) i
                 ltac:(rewrite Zlength_map; lia)).
      rewrite Znth_Zrepeat by (rewrite !Zlength_map; lia).
      reflexivity.
  Qed.

  (* Step P3: fixed——固定长度数组的等式适配；只读初始化前缀 sublist 0 j values，
     不要求 values 长到全部槽数；未填后缀完全不读 values。 *)
  Lemma partial_init_fixed {dS : Inhabitant S} {dV : Inhabitant V} :
    forall (U : S -> L) (E : S -> V -> L) (slots : list S) (values : list V) (j : Z),
      (0 <= j <= Zlength slots)%Z -> (j <= Zlength values)%Z ->
      partial_init U E slots (sublist 0 j values) =
        iter_sepcon
          (fun i : Z => if Z_lt_dec i j
                        then E (Znth i slots) (Znth i values)
                        else U (Znth i slots))
          (upto (Z.to_nat (Zlength slots))).
  Proof.
    intros U E slots values j Hj Hvals.
    assert (Hdlen : Zlength (sublist 0 j values) = j).
    { pose proof (Zlength_sublist 0 j values ltac:(lia) ltac:(exact Hvals)) as H.
      lia. }
    rewrite (partial_init_indexed U E slots (sublist 0 j values)
               ltac:(rewrite Hdlen; lia)).
    rewrite Hdlen.
    apply iter_sepcon_func_strong.
    intros i Hin.
    rewrite In_upto in Hin.
    destruct Hin as [Hx0 Hin2].
    rewrite Z2Nat.id in Hin2 by apply Zlength_nonneg.
    destruct (Z_lt_dec i j) as [Hlt | Hge].
    - rewrite (Znth_sublist 0 i j values) by lia.
      rewrite Z.add_0_r.
      reflexivity.
    - reflexivity.
  Qed.

End PartialInit.
