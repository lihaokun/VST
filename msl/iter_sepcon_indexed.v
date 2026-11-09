(* 槽位 indexed 表示的共享底座。
   iter_sepcon_focus_indexed 直接处理 upto fold：借出第 i 槽并保留任意新值的恢复条件。
   使用方展开原 rep 后实例化元素资源函数即可，不必自行转换成双列表或改写 wand 的尾部。
   indexed_slots、长度/读取事实以及两条等式桥也公开，供非标准使用形态组合。
   原槽位表长度不受额外约束；值表长度与枚举槽数的关系按各入口前提提供。
   iter_sepcon2_upto_eq 仅需 NatDed/SepLog；当前组合桥与 focus 的显式签名还带
   ClassicalSep/CorableSepLog，使用时以实际类型为准。partial_init 保留原同名薄别名。 *)

Set Default Timeout 300.

Require Import VST.msl.base.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.wand_frame.
Require Import VST.zlist.sublist.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.

Local Open Scope logic.

(* ================= 派生表：indexed_slots ================= *)

(* 对原 slots 取前 n 个索引的派生表。n < 0 时为空表（total）；
   索引越界时 Znth 取 Inhabitant 默认值——语义责任在使用处的 rep，不在本定义。 *)
Definition indexed_slots {S : Type} {dS : Inhabitant S}
    (slots : list S) (n : Z) : list S :=
  map (fun i => Znth i slots) (upto (Z.to_nat n)).

Lemma indexed_slots_length {S : Type} {dS : Inhabitant S} :
  forall (slots : list S) (n : Z), (0 <= n)%Z -> Zlength (indexed_slots slots n) = n.
Proof.
  intros slots n Hn.
  unfold indexed_slots.
  rewrite Zlength_map, Zlength_upto.
  rewrite Z2Nat.id by exact Hn.
  reflexivity.
Qed.

Lemma Znth_indexed_slots {S : Type} {dS : Inhabitant S} :
  forall (slots : list S) (n i : Z), (0 <= i < n)%Z -> Znth i (indexed_slots slots n) = Znth i slots.
Proof.
  intros slots n i Hi.
  unfold indexed_slots.
  rewrite Znth_map by (rewrite Zlength_upto; rewrite Z2Nat.id by lia; lia).
  rewrite Znth_upto by (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

(* ================= 配对 fold → upto 位置 fold（自 partial_init.v 迁入） ================= *)

Section IndexedSlots.

  Context {S X : Type}.
  Context {L : Type}.
  Context {ND : NatDed L}.
  Context {SL : SepLog L}.
  Context {ClS : ClassicalSep L}.
  Context {CoSL : CorableSepLog L}.

  (* 等长两表上的配对 fold 展开为 upto 上的位置 fold。
     自 msl/partial_init.v（Section PartialInit）逐字迁入。 *)
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

End IndexedSlots.

(* ================= 组合桥：indexed ↔ 双列表 ================= *)

(* indexed_slots 派生表上的配对 fold 与 upto 上的位置 fold 重合。
   无独立 0<=n 前提：Zlength xs = n 经 Zlength_nonneg 已蕴含 0<=n。
   n < 0：indexed_slots slots n = []（total），前提 Zlength xs = n 因
   Zlength xs >= 0 不可满足——负 n 由消费者既有的值表长度前提排除。
   Zlength slots < n（索引越界）：Znth 返回 Inhabitant 默认值，桥仍真。 *)
Lemma iter_sepcon2_indexed_slots_eq
    {S X : Type} {dS : Inhabitant S} {dX : Inhabitant X}
    {L : Type} {ND : NatDed L} {SL : SepLog L} {ClS : ClassicalSep L} {CoSL : CorableSepLog L} :
  forall (p : S -> X -> L) (slots : list S) (xs : list X) (n : Z),
  Zlength xs = n ->
  iter_sepcon2 p (indexed_slots slots n) xs =
  iter_sepcon (fun i => p (Znth i slots) (Znth i xs)) (upto (Z.to_nat n)).
Proof.
  intros p slots xs n Hv.
  assert (Hn0 : (0 <= n)%Z) by (pose proof (Zlength_nonneg xs); lia).
  assert (HlenI : Zlength (indexed_slots slots n) = n)
    by (apply indexed_slots_length; exact Hn0).
  rewrite iter_sepcon2_upto_eq by (rewrite HlenI; symmetry; exact Hv).
  rewrite HlenI.
  apply iter_sepcon_func_strong.
  intros x Hx.
  rewrite In_upto in Hx. destruct Hx as [Hx0 Hx1].
  rewrite Z2Nat.id in Hx1 by lia.
  rewrite Znth_indexed_slots by lia.
  reflexivity.
Qed.

(* ================= 库级 indexed 形 focus 入口（消费者形态） ================= *)

(* 借出第 i 槽 + 对任意新值的恢复 wand——write-focus 模板的库级化。
   陈述直接落在消费者形态上（upto fold，无 iter_sepcon2、无 indexed_slots
   出现在接口中）：项目侧 unfold 原 rep 后直接 apply，不再自带
   「桥 + Znth 传输 + wand 尾转换」。
   前提：0 <= i < n 是索引前提（聚焦位置必须是 upto fold 的合法索引）；
   Zlength xs = n 是折 covering n 槽 ↔ 值表 n 项的语义绑定（同时蕴含 0<=n）；
   对 slots 长度无前提（索引越界点态由 Znth 默认值吸收）。 *)
Lemma iter_sepcon_focus_indexed
    {S X : Type} {dS : Inhabitant S} {dX : Inhabitant X}
    {L : Type} {ND : NatDed L} {SL : SepLog L} {ClS : ClassicalSep L} {CoSL : CorableSepLog L} :
  forall (p : S -> X -> L) (slots : list S) (xs : list X) (n i : Z),
  (0 <= i < n)%Z -> Zlength xs = n ->
  iter_sepcon (fun k => p (Znth k slots) (Znth k xs)) (upto (Z.to_nat n)) |--
  p (Znth i slots) (Znth i xs) *
  (ALL x', p (Znth i slots) x' -*
   iter_sepcon (fun k => p (Znth k slots) (Znth k (upd_Znth i xs x')))
               (upto (Z.to_nat n))).
Proof.
  intros p slots xs n i Hi Hv.
  assert (Hlen : Zlength (upto (Z.to_nat n)) = n)
    by (rewrite Zlength_upto, Z2Nat.id by lia; lia).
  rewrite (iter_sepcon_Znth (fun k => p (Znth k slots) (Znth k xs))
                            (upto (Z.to_nat n)) i) by (rewrite Hlen; lia).
  rewrite Znth_upto by (rewrite Z2Nat.id; lia).
  apply sepcon_derives; [ apply derives_refl | ].
  apply allp_right; intro x'.
  apply wand_frame_intro'.
  rewrite (iter_sepcon_Znth (fun k => p (Znth k slots) (Znth k (upd_Znth i xs x')))
                            (upto (Z.to_nat n)) i) by (rewrite Hlen; lia).
  rewrite Znth_upto by (rewrite Z2Nat.id; lia).
  rewrite upd_Znth_same by lia.
  apply sepcon_derives; [ apply derives_refl | ].
  apply derives_refl'.
  apply iter_sepcon_func_strong.
  intros x Hx.
  apply In_remove_upto in Hx as [Hxb Hxne]; [ | lia ].
  rewrite Z2Nat.id in Hxb by lia.
  rewrite upd_Znth_diff by lia.
  reflexivity.
Qed.
