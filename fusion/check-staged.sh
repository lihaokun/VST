#!/usr/bin/env bash
# Clean candidate installation inside this worktree; selected opam libraries are read-only.
set -euo pipefail
root=$(realpath "$(dirname "$0")/..")
test "$(pwd -P)" = "$root"
prefix=${OPAM_SWITCH_PREFIX:?Run through opam exec --switch=<existing compatible switch>}
test "$(dirname "$(command -v coqc)")" = "$prefix/bin"
for key in COQLIB ROCQLIB ROCQCORELIB COQPATH ROCQPATH MAKEFLAGS MAKEFILES GNUMAKEFLAGS; do
  test -z "${!key:-}" || { printf 'Unexpected override: %s\n' "$key" >&2; exit 2; }
done
stage="$root/fusion/.candidate/VST"
test ! -L "$root/fusion/.candidate" && test ! -L "$root/fusion/.build"
python3 fusion/update_payload.py --check
args=("COQBIN=$prefix/bin/" "INSTALLDIR=$stage" COMPCERT=platform
      ZLIST=platform BITSIZE=64 ARCH=x86 IGNORECOQVERSION=true IGNORECOMPCERTVERSION=true)
make "${args[@]}" clean
# These are this worktree's generated artifacts, never source or installed libraries.
rm -rf "$root/fusion/.candidate" "$root/fusion/.build"
python3 util/fusion_manifest.py check-source . "$prefix/lib/coq/user-contrib/VST"
make -j2 "${args[@]}" vst
mkdir -p "$stage/zlist"
# zlist is a separately installed dependency, not an old copy of the VST core.
cp "$prefix"/lib/coq/user-contrib/VST/zlist/*.v "$prefix"/lib/coq/user-contrib/VST/zlist/*.vo "$stage/zlist/"
make -j2 "${args[@]}" install
python3 util/fusion_manifest.py install "$stage"
bash fusion/check.sh "$stage"
