Require Import VST.veric.SeparationLogic.
Require Import compcert.common.Memdata.

Import Clight expr2.
Local Open Scope Z.
Local Open Scope logic.

Definition exact_address_mapsto
    (sh : share) (ch : memory_chunk) (v : val) (a : address) : mpred :=
  !! (align_chunk ch | snd a) &&
  res_predicates.address_mapsto_old ch v sh a.

Definition exact_mapsto
    (sh : share) (ch : memory_chunk) (v p : val) : mpred :=
  match p with
  | Vptr b ofs => exact_address_mapsto sh ch v (b, Ptrofs.unsigned ofs)
  | _ => FF
  end.

Definition exact_store_pre {CS : compspecs} (Delta : tycontext)
    (e1 e2 : expr) (P : environ -> mpred) : environ -> mpred :=
  EX sh : share, EX ch : memory_chunk,
  !! (writable_share sh /\ access_mode (typeof e1) = By_value ch) &&
  |> (tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 (typeof e1)) &&
    ((fun rho => mapsto_ sh (typeof e1) (eval_lvalue e1 rho)) *
     ((fun rho => exact_mapsto sh ch
       (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho)))
       (eval_lvalue e1 rho)) -* P))).
