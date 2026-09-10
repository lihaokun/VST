Require Import VST.floyd.proofauto.
Require Import VST.floyd.FusionExactSem.
Require Import VST.floyd.FusionStore.
From VST.progs64.fusion Require Import fusion_checks verif_fusion views_client.
Set Printing All.
Print Assumptions VST.floyd.SeparationLogicAsLogicSoundness.MainTheorem.semax_store_exact.
Print Assumptions FusionExactSem.semax_store_exact.
Print Assumptions VST.floyd.SeparationLogicAsLogicSoundness.VericExactStore.semax_store_exact_backward.
Print Assumptions VST.floyd.SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.semax_prog_sound.
Print Assumptions semax_store_exact_nth_ram.
Print Assumptions body_w64_r32.
Print Assumptions body_caller.
Print Assumptions body_main.
Print Assumptions ordinary_forward_store_regression.
Print Assumptions seedVSU.
Print Assumptions checked_seedVSU.
Print Assumptions VST.floyd.FusionViews64.exact_Mint64_has_low32_mapsto_le.
Print Assumptions VST.floyd.FusionViews64.exact_Mint64_has_high32_mapsto_le.
Print Assumptions VST.floyd.FusionViews64.exact_Mint64_has_mapsto.
Print Assumptions borrow_three_views_with_frame.
Print Assumptions borrow_low_view_with_frame.
Print Assumptions wide_decode_does_not_fix_low_decode.
Quit.
