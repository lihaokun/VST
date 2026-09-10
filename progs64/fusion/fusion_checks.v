Require Import VST.floyd.proofauto VST.floyd.VSU.
From VST.progs64.fusion Require Import seed_program verif_fusion.
Local Existing Instance verif_fusion.CompSpecs.
Local Open Scope logic.

(* The new rule uses the very judgment consumed by stock Floyd and VSU. *)
Example public_judgment_identity :
  @semax = @VST.floyd.SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Def.semax.
Proof. reflexivity. Qed.

Fail Check VST.floyd.SeparationLogicAsLogicSoundness.MainTheorem.DeepEmbedded.
Fail Check exact_semax.

(* Wrong internal bodies are not accepted merely because they are proved. *)
Goal semax_body Vprog Gprog f_w64_r32 exact_spec.
Proof. Fail exact body_caller. exact body_w64_r32. Qed.

(* Exercise the actual VSU body consumer, not only a standalone triple. *)
Definition checked_seedVSU : @VSU NullExtension.Espec [] []
  ltac:(QPprog prog) Gprog (InitGPred (Vardefs ltac:(QPprog prog))).
Proof.
  mkVSU prog Gprog.
  - Fail solve_SF_internal body_caller.
    solve_SF_internal body_w64_r32.
  - solve_SF_internal body_caller.
  - solve_SF_internal body_main.
Qed.
