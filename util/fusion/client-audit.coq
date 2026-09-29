Require Import VST.floyd.proofauto VST.floyd.FusionStore.
From VST.progs64.fusion Require Import fusion_checks verif_fusion views_client.
Set Printing All.
Print Assumptions body_w64_r32.
Print Assumptions body_caller.
Print Assumptions body_main.
Print Assumptions ordinary_forward_store_regression.
Print Assumptions seedVSU.
Print Assumptions checked_seedVSU.
Print Assumptions borrow_three_views_with_frame.
Print Assumptions borrow_low_view_with_frame.
Print Assumptions wide_decode_does_not_fix_low_decode.
Quit.
