(* msl/partial_init_bridge.v — 第3组：playbook 部分填充接口（plem-2 §6/§2）。 *)
(* 依赖底座 msl/iter_sepcon_indexed.v（indexed_slots / indexed_slots_length / Znth_indexed_slots /
   iter_sepcon2_upto_eq 迁移 / iter_sepcon2_indexed_slots_eq，第2组）尚未发布。
   本文件当前内容 = Section 泛型上下文 + indexed_rep 定义 + 三条不依赖底座的公开引理
   （rep_0 / rep_weaken / rep_full，现成库 iter_sepcon_func_strong / iter_sepcon_derives 直证，零 setoid）。
   底座发布后追加（签名已按 docs/design/playbook-lemma-extraction/
   playbook-bridges-detailed-design.md §6 冻结，RHS 槽表一律使用底座的 indexed_slots，本文件不复制定义）：
     Lemma rep_eq_partial_init : 0 <= j <= n -> Zlength contents = j ->
       indexed_rep Elem U slots contents j n =
       partial_init U (fun p w => Elem p w) (indexed_slots slots n) contents.
     Lemma rep_focus : 0 <= j < n -> Zlength contents = j ->
       indexed_rep Elem U slots contents j n |--
       U (Znth j slots) * (ALL w, Elem (Znth j slots) w -*
         indexed_rep Elem U slots (contents ++ [w]) (j+1) n).
     Lemma rep_focus2 : 0 <= j < n -> Zlength contents = j ->
       indexed_rep Elem U slots contents j n |--
       U (Znth j slots) * ((U (Znth j slots) -* indexed_rep Elem U slots contents j n) &&
         (ALL w, Elem (Znth j slots) w -* indexed_rep Elem U slots (contents ++ [w]) (j+1) n)).
   不新增全局 Inhabitant / hint / 公理；载体泛型 L，逻辑上下文同 M3。 *)
Set Default Timeout 300.

Require Import VST.msl.base.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.partial_init.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.iter_sepcon_indexed.
Require Import VST.zlist.sublist.
Require Import VST.zlist.frontier.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope logic.

(* 内部辅助：mpred 等式转 derives（subst 路线；用于 eq goal 下的 f_equal 链，
   避免 wand 深层的 setoid 依赖）。与归档 glue 同功能，接口冻结后统一归名。 *)
Lemma eq_to_derives {A : Type} {ND0 : NatDed A} (PQ0 RQ0 : A) : PQ0 = RQ0 -> PQ0 |-- RQ0.
Proof. intros H. subst RQ0. apply derives_refl. Qed.

Section PartialBridge.

  Context {S W L : Type}.
  Context {dS : Inhabitant S} {dW : Inhabitant W}.
  Context {ND : NatDed L} {SL : SepLog L} {ClS : ClassicalSep L} {CoSL : CorableSepLog L}.

  (* playbook §6 填充 rep 原形（显式定义；需要 dS 与 dW：逐槽读 slots 与 contents）。
     变量 j/n/contents/slots 相互独立；关联前提在使用面（0<=j<=n、Zlength contents=j 等）。 *)
  Definition indexed_rep (Elem : S -> W -> L) (U : S -> L)
      (slots : list S) (contents : list W) (j n : Z) : L :=
    iter_sepcon (fun i => if Z_lt_le_dec i j
                          then Elem (Znth i slots) (Znth i contents)
                          else U (Znth i slots))
                (upto (Z.to_nat n)).

  (* 空等式：零前提、任意 contents/n（upto 对负 n 为空，两侧同为空 fold）。
     [现成库可证：iter_sepcon_func_strong]，不经过内部模型。 *)
  Lemma rep_0 :
    forall (Elem : S -> W -> L) (U : S -> L)
        (slots : list S) (contents : list W) (n : Z),
    indexed_rep Elem U slots contents 0 n =
    iter_sepcon (fun i => U (Znth i slots)) (upto (Z.to_nat n)).
  Proof.
    intros Elem U slots contents n.
    unfold indexed_rep.
    apply iter_sepcon_func_strong. intros x Hx.
    apply In_upto in Hx. destruct Hx as [Hx0 _].
    destruct (Z_lt_le_dec x 0) as [Hlt | _]; [ lia | reflexivity ].
  Qed.

  (* 弱化：仅真实逐槽 E→U 蕴含（非 free），任意 contents/j/n，零其它前提。
     [现成库可证：iter_sepcon_derives]，不经过内部模型；
     与归档 verif_ComputesT.v mtx_at_weaken 同款姿势。 *)
  Lemma rep_weaken :
    forall (Elem : S -> W -> L) (U : S -> L)
        (slots : list S) (contents : list W) (j n : Z),
    (forall (p:S) (w:W), Elem p w |-- U p) ->
    indexed_rep Elem U slots contents j n |--
    iter_sepcon (fun i => U (Znth i slots)) (upto (Z.to_nat n)).
  Proof.
    intros Elem U slots contents j n H.
    unfold indexed_rep.
    apply iter_sepcon_derives. intros x Hx.
    destruct (Z_lt_le_dec x j); [ apply H | apply derives_refl ].
  Qed.

  (* 满形展开等式：零前提、任意 contents/n（同一 contents 的逐点展开；
     负 n 时两侧同为空 fold；不含编码转换层——归档 mtx_at_to_polys 的长度前提
     属其 map-encode 变回原表的额外转换，不进本引理）。
     [现成库可证：iter_sepcon_func_strong + ZifyInst.of_nat_to_nat_eq]，不经过内部模型。 *)
  Lemma rep_full :
    forall (Elem : S -> W -> L) (U : S -> L)
        (slots : list S) (contents : list W) (n : Z),
    indexed_rep Elem U slots contents n n =
    iter_sepcon (fun i => Elem (Znth i slots) (Znth i contents)) (upto (Z.to_nat n)).
  Proof.
    intros Elem U slots contents n.
    unfold indexed_rep.
    apply iter_sepcon_func_strong. intros x Hx.
    apply In_upto in Hx.
    rewrite ZifyInst.of_nat_to_nat_eq in Hx.
    destruct (Z_lt_le_dec x n) as [Hlt | Hge].
    - reflexivity.
    - destruct (Z_le_dec 0 n) as [Hn0 | Hn].
      + rewrite (Z.max_r 0 n Hn0) in Hx. lia.
      + rewrite (Z.max_l 0 n ltac:(lia)) in Hx. lia.
  Qed.

  (* ---- 依赖底座（msl/iter_sepcon_indexed.v：indexed_slots 及其辅助）的三条公开入口 ---- *)

  (* 桥 A：indexed_rep ↔ partial_init（RHS 槽表为底座 indexed_slots，不新增 Zlength slots=n 前提） *)
  Lemma rep_eq_partial_init :
    forall (Elem : S -> W -> L) (U : S -> L)
        (slots : list S) (contents : list W) (j n : Z),
    (0 <= j <= n)%Z -> Zlength contents = j ->
    indexed_rep Elem U slots contents j n =
    partial_init U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) contents.
  Proof.
    intros Elem U slots contents j n Hj Hlen.
    rewrite (partial_init_indexed
               U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) contents
               ltac:(rewrite indexed_slots_length by lia; lia)).
    rewrite Hlen, (indexed_slots_length slots n ltac:(lia)).
    unfold indexed_rep.
    apply iter_sepcon_func_strong. intros x Hx.
    apply In_upto in Hx. destruct Hx as [Hx0 Hx1].
    rewrite Z2Nat.id in Hx1 by lia.
    rewrite Znth_indexed_slots by lia.
    cbn beta.
    destruct (Z_lt_dec x j) as [Hlt | Hge];
    destruct (Z_lt_le_dec x j) as [Hlt2 | Hge2]; try lia; reflexivity.
  Qed.

  (* 成功单 wand（借出第 j 槽 havoc + ALL 推进；经 rep_eq_partial_init + partial_init_focus） *)
  Lemma rep_focus :
    forall (Elem : S -> W -> L) (U : S -> L)
        (slots : list S) (contents : list W) (j n : Z),
    (0 <= j < n)%Z -> Zlength contents = j ->
    indexed_rep Elem U slots contents j n |--
    U (Znth j slots) *
    (ALL w : W, Elem (Znth j slots) w -*
        indexed_rep Elem U slots (contents ++ [w]) (j+1) n).
  Proof.
    intros Elem U slots contents j n Hj Hlen.
    rewrite (rep_eq_partial_init Elem U slots contents j n ltac:(lia) Hlen).
    eapply derives_trans with
      (Q := U (Znth (Zlength contents) (indexed_slots slots n)) *
            partial_resume U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) contents).
    - apply partial_init_focus.
      rewrite Hlen, indexed_slots_length by lia. lia.
    - unfold partial_resume. cbn beta.
      rewrite Hlen.
      rewrite (Znth_indexed_slots slots n j) by lia.
      apply sepcon_derives; [ apply derives_refl | ].
      apply andp_left2.
      apply allp_right. intros w.
      apply (allp_left _ w).
      apply (eq_to_derives _ _). f_equal.
      symmetry. apply rep_eq_partial_init; [ lia | ].
      rewrite Zlength_app. replace (Zlength [w]) with 1%Z by reflexivity. lia.
  Qed.

  (* 成功/失败双 wand（restore + advance，&& 共享同一余部；同 rep_focus 途径） *)
  Lemma rep_focus2 :
    forall (Elem : S -> W -> L) (U : S -> L)
        (slots : list S) (contents : list W) (j n : Z),
    (0 <= j < n)%Z -> Zlength contents = j ->
    indexed_rep Elem U slots contents j n |--
    U (Znth j slots) *
    ((U (Znth j slots) -* indexed_rep Elem U slots contents j n) &&
     (ALL w : W, Elem (Znth j slots) w -*
        indexed_rep Elem U slots (contents ++ [w]) (j+1) n)).
  Proof.
    intros Elem U slots contents j n Hj Hlen.
    rewrite (rep_eq_partial_init Elem U slots contents j n ltac:(lia) Hlen).
    eapply derives_trans with
      (Q := U (Znth (Zlength contents) (indexed_slots slots n)) *
            partial_resume U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) contents).
    - apply partial_init_focus.
      rewrite Hlen, indexed_slots_length by lia. lia.
    - unfold partial_resume. cbn beta.
      rewrite Hlen.
      rewrite (Znth_indexed_slots slots n j) by lia.
      apply sepcon_derives; [ apply derives_refl | apply andp_right ].
      { apply andp_left1.
        apply (eq_to_derives _ _). f_equal. }
      { apply (andp_left2
                 (U (Znth j slots) -* partial_init U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) contents)
                 (ALL v : W, Elem (Znth j slots) v -* partial_init U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) (contents ++ [v]))).
        apply allp_right. intros w0.
        apply (allp_left
                 (fun v0 : W => Elem (Znth j slots) v0 -* partial_init U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) (contents ++ [v0]))
                 w0).
        apply (eq_to_derives
                 (Elem (Znth j slots) w0 -* partial_init U (fun (p:S) (w:W) => Elem p w) (indexed_slots slots n) (contents ++ [w0]))
                 (Elem (Znth j slots) w0 -* indexed_rep Elem U slots (contents ++ [w0]) (j+1) n)).
        rewrite <- (rep_eq_partial_init Elem U slots (contents ++ [w0]) (j+1) n
                      ltac:(lia)
                      ltac:(rewrite Zlength_app; replace (Zlength [w0]) with 1%Z
                              by reflexivity; lia)).
        reflexivity.
      }
  Qed.

End PartialBridge.
