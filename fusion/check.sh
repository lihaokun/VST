#!/usr/bin/env bash
# Check the installed package selected by the caller's opam environment.
set -euo pipefail
root=$(realpath "$(dirname "$0")/..")
test "$(pwd -P)" = "$root" || { printf '%s\n' 'Run from the VST checkout root.' >&2; exit 2; }
for var in COQLIB ROCQLIB ROCQCORELIB COQPATH ROCQPATH; do
  test -z "${!var:-}" || { printf 'Unexpected library override: %s\n' "$var" >&2; exit 2; }
done
# opam exec sets OPAM_SWITCH_PREFIX but does not necessarily set OPAMSWITCH;
# an unqualified nested `opam var prefix` can then report the global default.
prefix=${OPAM_SWITCH_PREFIX:?Run this check through opam exec --switch=...}
test "$(dirname "$(command -v coqc)")" = "$prefix/bin" || {
  printf '%s\n' 'Compiler PATH does not match OPAM_SWITCH_PREFIX.' >&2; exit 2;
}
# An explicit staging root is for candidate validation only. The active package
# and its toolchain lock are never changed by this command.
vst=${1:-$prefix/lib/coq/user-contrib/VST}
python3 util/fusion_manifest.py verify "$vst"
mkdir -p fusion/.build/tests
cp fusion/tests/*.v fusion/.build/tests/
(
  cd fusion/.build
  { printf -- '-Q "%s" VST\n' "$vst"; printf '%s\n' '-Q tests ""'; printf '%s\n' tests/*.v; } > _CoqProject
  coq_makefile -f _CoqProject -o Makefile.coq
  make -f Makefile.coq clean
  make -f Makefile.coq -j2 tests/fusion_checks.vo tests/views_client.vo
)
coqtop -quiet -Q "$vst" VST -Q fusion/.build/tests '' < fusion/audit.coq > fusion/.build/audit.log 2>&1
if grep -Eq 'Error:|Anomaly:|Warning:' fusion/.build/audit.log; then
  printf '%s\n' 'Audit failed; inspect fusion/.build/audit.log' >&2; exit 1
fi
awk '/^[A-Za-z_][A-Za-z_0-9.]*[[:space:]]*:/ {
  sub(/[[:space:]]*:.*/, "")
  if ($0 == "prop_ext") $0 = "Axioms.prop_ext"
  if ($0 == "functional_extensionality_dep") $0 = "FunctionalExtensionality.functional_extensionality_dep"
  if ($0 != "Axioms") print
}' fusion/.build/audit.log | sort -u > fusion/.build/audit.names
diff -u fusion/assumptions.allowlist fusion/.build/audit.names
coqchk -silent -Q "$vst" VST -Q fusion/.build/tests '' fusion_checks views_client
