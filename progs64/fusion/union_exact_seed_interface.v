Require Import VST.floyd.proofauto.
From VST.progs64.fusion Require Import seed_union_rw.
Import compcert.lib.Maps.

(* The identifiers and expression shapes remain those of the generated seed.
   Only this composite is constrained; other composites may be arbitrary. *)
Module SeedReference.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition seed_composite := get_co _seed.
End SeedReference.

Module Type SEED_LAYOUT.
  Parameter CompSpecs : compspecs.
  Existing Instance CompSpecs.
  Parameter seed_lookup : PTree.get _seed cenv_cs = Some SeedReference.seed_composite.
  (* Pure representation evidence, not an assertion entailment or store rule.
     Concrete instances choose inr directly, without a runtime cast. *)
  Parameter seed_value : int64 -> reptype (Tunion _seed noattr).
  Parameter seed_value_shape : forall x,
    JMeq (unfold_reptype (seed_value x)) (inr (Vlong x) : val + val).
End SEED_LAYOUT.
