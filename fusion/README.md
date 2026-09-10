# Optional exact stores and reusable views — version-2 candidate

Candidate branch: `fusion/views-api-v2`, based on the published version-1 commit
`1d6931e960c71636402a3c73a7c177fe1edccfcc` (VST 2.16).
Candidate package: `coq-vst.2.16+ccv-fusion.2`. No version-2 tag has been published.

The statement logic and semantic exact-store rule are unchanged. This candidate
promotes the previously test-local general memory/view proofs into installed
`VST.floyd.FusionMemvals` and `VST.floyd.FusionViews64` modules. `FusionStore`
re-exports the views, so ordinary clients can use:

```coq
Require Import VST.floyd.proofauto VST.floyd.FusionStore.
Check exact_Mint64_has_low32_mapsto_le.
Check exact_Mint64_has_mapsto.
Check semax_store_exact_nth_ram.
```

The API map, prerequisites and implementation-helper boundary are in
[views-api.md](views-api.md). Test code now consumes this installed API rather
than compiling a second view implementation. These are general library lemmas,
not pre-proved user function bodies.

## Isolated validation while a version-1 run is active

From this worktree, using an existing compatible compiler/CompCert environment:

```sh
opam exec --switch=vst-fusion-public-2.16-1 -- bash fusion/check-staged.sh
```

This clean-builds the candidate VST, installs into `fusion/.candidate/VST`,
builds every object in the install inventory, and tests that installation with
an explicit private loadpath. Only the separate zlist dependency is copied from
the selected compiler environment; VST core/Floyd/concurrency are compiled here.
It does not replace files in the selected switch, change its pin, or modify any
running CCV worktree/lock/skill.

The result is an **actual staging installation**, not a registered opam switch or
published release. Installed modules, the old seed/store/load/VSU regressions,
new overlapping-view/frame clients, a Fragment counterexample, assumptions and
recursive kernel checking are exercised. It is not a complete CCV FSM run.

The initial candidate clean build succeeded. Its first client check exposed a
missing explicit `proofauto` import and was corrected. Installation also exposed
an inherited upstream issue: the install inventory listed example `.vo` files
that `make vst` had not built, and a shell loop could conceal those copy failures.
The install target now builds its declared objects first and propagates copy
errors. The resulting staging installation has 279 `.vo` files (including the
previously unbuilt examples), and the final client/audit/kernel checks passed.

## Release boundary

Version-2 metadata uses `ccv-vst-fusion-v2`, `api_version=2`, a base-release commit,
and a seven-source payload inventory. The script `fusion/update_payload.py`
updates/checks that inventory after source changes. The existing version-1 CCV
detector and release locks intentionally do not accept this candidate silently.

After review and an explicit new release, `fusion/install.sh` defaults to the
separate `vst-fusion-2.16-2` switch. It still requires a clean committed checkout.
Do not overwrite or move the published version-1 tag. A currently running proof
must continue using its locked version; importing version-1 generic reference
sources under that run's normal workflow is a separate matter.

Supported candidate target remains x86-64 Linux, standard ABI, little-endian,
OCaml 4.14.2, Rocq 9.0.0 and CompCert 3.17. No new global correctness axiom is
introduced. The audit still distinguishes package soundness dependencies from
ordinary view/body/VSU dependencies.
