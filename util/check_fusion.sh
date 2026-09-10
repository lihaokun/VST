#!/usr/bin/env bash
# 仅核指定安装根：独立编译所有客户端、假设审计、递归 kernel 检查。
set -euo pipefail
root=$(realpath "$(dirname "$0")/..")
prefix=${OPAM_SWITCH_PREFIX:?Use opam exec --switch=...}
vst=$(realpath "${1:-$prefix/lib/coq/user-contrib/VST}")
for module in FusionExact FusionExactSem FusionMemvals FusionViews64 FusionStore SeparationLogicAsLogicSoundness; do
  test -f "$vst/floyd/$module.vo" || { printf 'Missing installed module: %s\n' "$module" >&2; exit 1; }
done
unset COQPATH ROCQPATH COQLIB ROCQLIB COQCORELIB ROCQCORELIB CAML_LD_LIBRARY_PATH OCAMLPATH
unset MAKEFLAGS MAKEFILES GNUMAKEFLAGS MFLAGS MAKEOVERRIDES MAKELEVEL MAKE COQC COQTOP COQDEP COQFLAGS COQBIN OTHERFLAGS ROCQ
export PATH="$prefix/bin:$PATH"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$root"/progs64/fusion/*.v "$work/"
(
  cd "$work"
  args=(-Q "$vst" VST -Q . VST.progs64.fusion)
  # 文件存在不等于实际 import 到该文件；核指定库根的解析位置。
  for module in FusionExact FusionExactSem FusionMemvals FusionViews64 FusionStore SeparationLogicAsLogicSoundness; do
    printf 'Locate Library VST.floyd.%s.\n' "$module" |
      "$prefix/bin/coqtop" -q -quiet "${args[@]}" > locate.log 2>&1
    grep -Fq "$vst/floyd/$module.vo" locate.log || { cat locate.log >&2; exit 1; }
  done
  "$prefix/bin/coq_makefile" "${args[@]}" ./*.v -o Makefile.coq
  make -f Makefile.coq -j2
  "$prefix/bin/coqtop" -q -quiet "${args[@]}" < "$root/util/fusion/audit.coq" > audit.log 2>&1
  if grep -Eq 'Error:|Anomaly:|Warning:' audit.log; then cat audit.log >&2; exit 1; fi
  awk '/^[A-Za-z_][A-Za-z_0-9.]*[[:space:]]*:/ {
    sub(/[[:space:]]*:.*/, "")
    if ($0 == "prop_ext") $0 = "Axioms.prop_ext"
    if ($0 == "functional_extensionality_dep") $0 = "FunctionalExtensionality.functional_extensionality_dep"
    if ($0 != "Axioms") print
  }' audit.log | sort -u > audit.names
  diff -u "$root/util/fusion/assumptions.allowlist" audit.names
  # 客户端根不得借用包级 soundness 的 Events 关系参数。
  "$prefix/bin/coqtop" -q -quiet "${args[@]}" < "$root/util/fusion/client-audit.coq" > clients.log 2>&1
  if grep -Eq 'Error:|Anomaly:|Warning:|Events\.(external_functions_sem|inline_assembly_sem)' clients.log; then
    cat clients.log >&2; exit 1
  fi
  "$prefix/bin/coqchk" -silent "${args[@]}" VST.progs64.fusion.fusion_checks VST.progs64.fusion.views_client
)
printf '%s\n' 'Fusion installed clients, assumptions and coqchk: PASS'
