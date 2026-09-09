Require Import VST.floyd.proofauto.
Require Import VST.floyd.FusionExactSem.
Require Import fusion_checks verif_fusion fusion_store.
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
Quit.
