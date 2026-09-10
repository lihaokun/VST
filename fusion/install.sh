#!/usr/bin/env bash
# Install the current development branch; no separate release-version selection.
set -euo pipefail
root=$(realpath "$(dirname "$0")/..")
test "$(pwd -P)" = "$root" || { printf '%s\n' 'Run from the VST checkout root.' >&2; exit 2; }
switch=${1:-vst-fusion}
jobs=${2:-4}
[[ "$switch" =~ ^vst-fusion([.-][A-Za-z0-9._-]+)?$ && "$jobs" =~ ^[1-4]$ ]] || exit 2
[[ $(uname -s) = Linux && $(uname -m) = x86_64 ]] || exit 2
test -z "$(git -C "$root" status --porcelain --untracked-files=normal)" || {
  printf '%s\n' 'Install only a clean committed checkout.' >&2; exit 2;
}
revision=$(git -C "$root" rev-parse HEAD)
repository=https://github.com/lihaokun/VST.git
branch=fusion/vst-2.16
remote_head=$(git ls-remote "$repository" "refs/heads/$branch")
test "${remote_head%%[[:space:]]*}" = "$revision" || {
  printf '%s\n' 'Update the clean checkout to the current public development branch before installation.' >&2
  exit 2
}
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
  printf '%s\n' 'vst-fusion' > "$opam_root/$switch/.vst-fusion-owner"
fi
opam pin add --switch="$switch" --no-action -y coq-vst "git+$repository#$branch"
opam install --switch="$switch" -j "$jobs" -y --keep-build-dir coq-vst
opam switch set-invariant --switch="$switch" ocaml-base-compiler.4.14.2
opam exec --switch="$switch" -- bash "$root/fusion/check.sh"
