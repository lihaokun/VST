# Optional exact stores and reusable views

Maintained branch: `fusion/vst-2.16`, based on VST 2.16. The complete view API
has been integrated into this original branch. There is no separate supported
store-only line and no v1/v2 selection for clients. Package version numbers and
source inventories identify builds; they are not a catalogue of supported releases.

The statement logic and semantic exact-store rule are unchanged. This implementation
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

## Isolated validation while an existing run is active

From this worktree, using an existing compatible compiler/CompCert environment:

```sh
opam exec --switch=vst-fusion-public-2.16-1 -- bash fusion/check-staged.sh
```

This clean-builds the current VST, installs into `fusion/.candidate/VST`,
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

## Development and installation

The package currently records `ccv-vst-fusion-v2`, `api_version=2` and the
seven-source inventory. These describe the current interface and installed files,
not an instruction to maintain an old compatibility path. The script
`fusion/update_payload.py` updates/checks the source inventory after source edits.

Installation follows the public development branch, not a fixed tag/commit:

```sh
git clone --branch fusion/vst-2.16 https://github.com/lihaokun/VST.git
cd VST
bash fusion/install.sh vst-fusion 4
```

Before an update, finish the active verification run, update the clean checkout
with `git pull --ff-only`, and rerun the installer. It checks that the checkout
matches the branch being installed so the accompanying tests match that code.
It does not maintain/reinstall the old store-only implementation. The presently
running run's installed files are left alone until it finishes; historical Git
tags need not be rewritten or deleted for this policy.

Supported candidate target remains x86-64 Linux, standard ABI, little-endian,
OCaml 4.14.2, Rocq 9.0.0 and CompCert 3.17. No new global correctness axiom is
introduced. The audit still distinguishes package soundness dependencies from
ordinary view/body/VSU dependencies.
