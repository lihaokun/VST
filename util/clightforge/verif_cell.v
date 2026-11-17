Require Import VST.floyd.proofauto.
Require Import cell.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition cell_read_spec : ident * funspec :=
 DECLARE _cell_read
 WITH sh : share, p : val, x : int
 PRE [ tptr tuint ]
   PROP (readable_share sh) PARAMS (p)
   SEP (data_at sh tuint (Vint x) p)
 POST [ tuint ]
   PROP () RETURN (Vint x)
   SEP (data_at sh tuint (Vint x) p).

Definition cell_write_spec : ident * funspec :=
 DECLARE _cell_write
 WITH sh : share, p : val, x : int, old : int
 PRE [ tptr tuint, tuint ]
   PROP (writable_share sh) PARAMS (p; Vint x)
   SEP (data_at sh tuint (Vint old) p)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (data_at sh tuint (Vint x) p).

Definition Gprog : funspecs := ltac:(with_library prog [cell_read_spec; cell_write_spec]).

Lemma body_cell_read : semax_body Vprog Gprog f_cell_read cell_read_spec.
Proof. start_function. forward. forward. Qed.

Lemma body_cell_write : semax_body Vprog Gprog f_cell_write cell_write_spec.
Proof. start_function. forward. entailer!. Qed.

Print Assumptions body_cell_read.
Print Assumptions body_cell_write.
