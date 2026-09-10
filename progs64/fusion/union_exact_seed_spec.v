Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.FusionViews64.
From VST.progs64.fusion Require Import seed_union_rw bridges union_exact_seed_interface union_exact_seed_support.

Module SeedSpec (Import Layout : SEED_LAYOUT).
Include SeedSupport Layout.
Local Existing Instance CompSpecs.
Local Open Scope Z.
Local Open Scope logic.

Definition tseed_exact := Tunion _seed noattr.
Definition seed_v64_exact (sh : share) (x : int64) (p : val) : mpred :=
  exact_seed_v64 sh x p.

Definition w64_r32_exact_spec : ident * funspec :=
  DECLARE _w64_r32
  WITH c0 : int64, x : int64, s : val
  PRE [tptr tseed_exact, tulong]
    PROP ()
    PARAMS (s; Vlong x)
    SEP (data_at Ews tseed_exact (seed_value c0) s)
  POST [tuint]
    PROP ()
    RETURN (Vint (Int64.loword x))
    SEP (seed_v64_exact Ews x s).

End SeedSpec.
