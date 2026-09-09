#!/usr/bin/env bash
# Install this exact clean Git revision; no dependency on CCV or VST-debug.
set -euo pipefail
root=$(realpath "$(dirname "$0")/..")
test "$(pwd -P)" = "$root" || { printf '%s\n' 'Run from the VST checkout root.' >&2; exit 2; }
switch=${1:-vst-fusion-2.16-1}
jobs=${2:-4}
[[ "$switch" =~ ^vst-fusion-[A-Za-z0-9._-]+$ && "$jobs" =~ ^[1-4]$ ]] || exit 2
[[ $(uname -s) = Linux && $(uname -m) = x86_64 ]] || exit 2
test -z "$(git -C "$root" status --porcelain --untracked-files=normal)" || {
  printf '%s\n' 'Install only a clean committed checkout.' >&2; exit 2;
}
revision=$(git -C "$root" rev-parse HEAD)
unset COQLIB ROCQLIB ROCQCORELIB COQPATH ROCQPATH CAML_LD_LIBRARY_PATH OCAMLPATH
unset INSTALLDIR COQBIN MAKEFLAGS MAKEFILES GNUMAKEFLAGS MFLAGS MAKEOVERRIDES MAKELEVEL
unset MAKE OPAMMAKECMD DESTDIR PREFIX COQC COQTOP COQDEP COQEXTRAFLAGS COQFLAGS EXTFLAGS
unset COMPCERT COMPCERT_INST_DIR COMPCERT_SRC_DIR COMPCERT_EXPLICIT_PATH FLOCQ ZLIST ARCH BITSIZE CLIGHTGEN
unset OPAMFAKE OPAMDRYRUN OPAMSHOW OPAMINPLACEBUILD OPAMREUSEBUILDDIR OPAMNOCHECKSUMS
default=$(opam option --global switch --safe)
trap 'test "$(opam option --global switch --safe)" = "$default"' EXIT
opam_root=$(opam var root)
if opam switch list --short | grep -Fxq "$switch"; then
  test -f "$opam_root/$switch/.vst-fusion-owner" || { printf '%s\n' 'Refusing unowned switch.' >&2; exit 2; }
else
  opam switch create "$switch" --empty --no-switch --repositories=coq-released,default -y
  printf '%s\n' 'vst-fusion-v1' > "$opam_root/$switch/.vst-fusion-owner"
fi
installed=$(opam list --switch="$switch" --installed --short --columns=version coq-vst)
[[ -z "$installed" || "$installed" = 2.16+ccv-fusion.1 ]] || exit 2
opam pin add --switch="$switch" --no-action -y coq-vst.2.16+ccv-fusion.1 "git+file://$root#$revision"
opam install --switch="$switch" -j "$jobs" -y --keep-build-dir coq-vst.2.16+ccv-fusion.1
opam switch set-invariant --switch="$switch" ocaml-base-compiler.4.14.2
opam exec --switch="$switch" -- bash "$root/fusion/check.sh"
