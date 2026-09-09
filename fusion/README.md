# Optional exact-store extension for VST 2.16

Development branch: `fusion/vst-2.16`. Release tag: `v2.16-ccv-fusion.1`.
Based on upstream `v2.16`, commit `a18d024633dfc4036247872b3e8650a961ac5891`.

This branch preserves the public sealed Floyd judgment and adds an optional
`MainTheorem.semax_store_exact` rule, with `VST.floyd.FusionStore` providing the
nth-SEP ramification wrapper. Ordinary `mapsto`, `forward`, and VSU interfaces
retain their existing meanings. The deep assignment antecedent adds a third
branch; assignment inversion, frame, context/composite transport and soundness
are updated. Internal `DeepEmbeddedSoundness` takes an additional capability.

The five proof payloads are byte-identical to the tested VST-debug snapshot
`dbd55a6b1af2a91246f0890569c87ad39af9b3d4`. That historical payload revision remains
in `fusion/release.json`; it is not a claim that this fork has that Git commit.
The actual fork identity is the release Git commit/tag. The repository contains
all build inputs: installation does not read VST-debug or CCV.

## Install on another machine

Initially supported: x86-64 Linux, Python 3.12+, opam, Git, make/C build tools,
clang, GMP and pkg-config. Initialize opam and configure repositories named
`default` and `coq-released` before installation. The recipe pins OCaml 4.14.2,
Coq/Rocq 9.0.0, CompCert 3.17 and other tested dependency versions. Repository
metadata and host packages are not a bit-for-bit OS image.

```sh
git clone --branch v2.16-ccv-fusion.1 https://github.com/Lin23299/VST.git VST-fusion
cd VST-fusion
# Record/verify git rev-parse HEAD against the published release commit.
bash fusion/install.sh vst-fusion-2.16-1 4
```

The script refuses dirty source trees and existing unowned destinations. It pins
the exact checkout commit, builds a complete `coq-vst.2.16+ccv-fusion.1` package
in a dedicated switch, then tests the installed library. It never sets the global
default switch, edits an existing stock switch, or assumes CCV is installed.
Keep the clone for its local Git pin, or explicitly repin the same commit to the
remote repository after installation.

Use the package without changing the global default:

```sh
opam exec --switch=vst-fusion-2.16-1 -- coqc your_proof.v
opam exec --switch=vst-fusion-2.16-1 -- bash fusion/check.sh
```

`fusion/check.sh` compiles a real arbitrary-input wide-store/narrow-load seed,
ordinary caller/main and stock VSU, and checks wrong-body/sealing regressions,
assumptions and the kernel. No separate `exact_semax` judgment is imported.
The main function uses standard `main_post`; this is a VSU test, not an extra
termination, dry-safety or compiled-binary theorem.

## Package and audit

`make vst` builds the standard library closure including `simpleconc`; installation
also includes the concurrency/atomics dependencies needed by allocator clients.
New `.v/.vo` modules are included explicitly. No precompiled VST source input is
accepted. The separate zlist dependency is built in the selected switch.

Installed `VST/ccv-fusion.json` records target, source payload identity and every
installed `.vo` hash. `util/fusion_manifest.py verify <installed-VST-root>` checks
inventory integrity; `fusion/check.sh` separately verifies proofs and public APIs.
The manifest is not publisher authentication. Normal logical dependencies remain;
the semantic soundness audit includes the two CompCert `Events.*_sem` parameters,
but no new project correctness axiom or `Events.*_properties` assumption.

The source inventory hash in `fusion/payload.sha256` is
`ab7744ec54cd56e54df06ec011456b8fa77b2310846f0f86f86ba3f7dd60966f`.
It hashes sorted `<source-sha256>  <relative-path>\n` lines, not a Git diff.
