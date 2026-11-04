(* 展开形式的填充一步：将编码前缀与默认尾段的折叠接线放在库内。
   默认尾值不要求属于编码函数的像；不注册全局 hint 或默认值实例。 *)
Set Default Timeout 300.

From Stdlib Require Import ZArith Lists.List Lia.
Import ListNotations.
Require Import VST.zlist.sublist.
Require Import VST.zlist.Zlength_solver.
Require Import VST.zlist.frontier.

Local Open Scope Z_scope.

(* 将编码前缀和尾段折为 filled。 *)
Local Lemma filled_fold_map {A B} (f : A -> B) (prefix : list A) (d : B) (n : Z) :
  map f prefix ++ Zrepeat d (n - Zlength prefix) = filled (map f prefix) d n.
Proof.
  unfold filled. f_equal. rewrite Zlength_map. reflexivity.
Qed.

(* 将追加新值后的编码前缀和尾段折为 filled。 *)
Local Lemma filled_fold_snoc {A B} (f : A -> B) (prefix : list A) (v : A) (d : B) (n : Z) :
  map f (prefix ++ [v]) ++ Zrepeat d (n - (Zlength prefix + 1)) =
  filled (map f (prefix ++ [v])) d n.
Proof.
  unfold filled. rewrite Zlength_map, Zlength_app. reflexivity.
Qed.

(* 保留使用方的显式下标 j；双层编码可先由 map_map 合成函数。 *)
Lemma filled_map_stepU_at {A B} (f : A -> B) (prefix : list A)
    (d : B) (n j : Z) (v : A) :
  Zlength prefix = j -> Zlength prefix < n ->
  upd_Znth j (map f prefix ++ Zrepeat d (n - j)) (f v) =
  map f (prefix ++ [v]) ++ Zrepeat d (n - (j + 1)).
Proof.
  intros Hj Hn.
  rewrite <- Hj.
  rewrite filled_fold_map, filled_fold_snoc.
  apply filled_map_step. exact Hn.
Qed.

(* 前缀的接受/拒绝写入；表示转换及更新长度义务在库内闭合。
   j = i 时不要求 Q v，j = i + 1 时才需新值满足 Q。 *)
Lemma Forall_sublist_store {A} {dA : Inhabitant A} (Q : A -> Prop) xs i j v :
  0 <= i < Zlength xs -> i <= j <= i + 1 -> (i < j -> Q v) ->
  Forall Q (sublist 0 i xs) ->
  Forall Q (sublist 0 j (upd_Znth i xs v)).
Proof.
  intros Hi Hj Hv HF.
  destruct (prefix_holds_sublist Q j (upd_Znth i xs v)
              ltac:(rewrite Zlength_upd_Znth; lia)) as [Hfw _].
  apply Hfw.
  apply prefix_holds_store.
  - exact Hi.
  - lia.
  - exact Hv.
  - destruct (prefix_holds_sublist Q i xs ltac:(lia)) as [_ Hbwd].
    exact (Hbwd HF).
Qed.
