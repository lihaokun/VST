#!/usr/bin/env python3
"""在独立副本简化run2的proof bodies，不修改归档/合同/库，不产生证书。"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
VST = Path(__file__).resolve().parents[4]
EDITS = {
    "lemmas_word_view.v": {
        "wv_loword_unsigned": "  intros. unfold Int64.loword. apply Int.unsigned_repr_eq.\n",
        "wv_load_low32_address": "  intros. unfold wv_load_low32_expr, wv_exact. go_lowerx. unfold_lift in *.\n"
                                 "  destruct H1 as [Hp _]. rewrite <- Hp. entailer!.\n",
    },
    "verif_word_view_word_view_store_low.v": {
        "wv_store_whole_address": "  intros. unfold wv_data. go_lowerx. unfold_lift in *.\n"
                                  "  destruct H1 as [Hp _]. rewrite <- Hp. entailer!.\n",
        "wv_store_whole_eval": "  intros. go_lowerx. unfold_lift in *.\n"
                               "  destruct H2 as [Hx _]. rewrite <- Hx. entailer!.\n",
    },
}

TYPED_BRIDGE = '''Lemma typed_wide_to_wv_exact : forall sh x p,
  TypedExactPrototype.exact_data_at sh tulong (Vlong x) p |-- wv_exact sh x p.
Proof.
  intros. unfold TypedExactPrototype.exact_data_at, wv_exact.
  rewrite TypedExactPrototype.exact_representation_tulong.
  apply andp_right.
  - apply andp_left1. rewrite wv_initializer. unfold wv_data.
    eapply derives_trans; [apply data_at_local_facts | apply prop_derives; tauto].
  - apply andp_left2. apply derives_refl.
Qed.

'''

TYPED_BODY = '''  start_function.
  rewrite <- wv_initializer.
  eapply semax_seq' with (P' :=
    PROP () LOCAL (temp _p p; temp _value (Vlong x))
    SEP (TypedExactPrototype.exact_data_at Ews tulong (Vlong x) p)).
  - eapply TypedExactPrototype.semax_store_exact_data_at_tulong with
      (n := 0%nat) (R := [data_at Ews tulong (Vlong c0) p])
      (old := Vlong c0) (x := x) (sh := Ews) (p := p).
    + reflexivity.
    + rewrite wv_initializer. apply wv_store_whole_address.
    + rewrite wv_initializer. apply wv_store_whole_eval.
    + reflexivity.
    + auto.
    + entailer!.
  - sep_apply typed_wide_to_wv_exact.
    eapply wv_load_low32_exact.
    + reflexivity.
    + sep_apply wv_exact_isptr. entailer!.
    + forward.
'''


def sha(data):
    return hashlib.sha256(data).hexdigest()


def replace_proofs(text, edits):
    counts = {}
    for name, proof in edits.items():
        pattern = re.compile(r"(?ms)(^Lemma " + re.escape(name) + r"\b.*?^Proof\.\n)(.*?)(^Qed\.)")
        matches = list(pattern.finditer(text))
        if len(matches) != 1:
            raise ValueError(f"expected one proof: {name}")
        match = matches[0]
        counts[name] = {"before_proof_lines": len(match[2].splitlines()), "after_proof_lines": len(proof.splitlines())}
        text = text[:match.start(2)] + proof + text[match.end(2):]
    return text, counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--switch", default="vst-fusion")
    parser.add_argument("--output", type=Path, default=VST / ".build/run2-reuse")
    parser.add_argument("--typed-store", action="store_true", help="额外试接WIP typed scalar-store；不是正式新API")
    args = parser.parse_args()
    archive, out = args.archive.resolve(), args.output.resolve()
    if out.exists() or not out.is_relative_to(VST / ".build"):
        raise ValueError("output must be a new directory inside this VST checkout's .build")
    env = {k: v for k, v in os.environ.items() if not k.startswith(("FSM_", "CCV_")) and k not in {
        "COQLIB", "ROCQLIB", "COQCORELIB", "ROCQCORELIB", "COQPATH", "ROCQPATH", "OPAMSWITCH", "OPAM_SWITCH_PREFIX",
        "MAKEFLAGS", "MAKEFILES", "GNUMAKEFLAGS", "MFLAGS", "MAKEOVERRIDES", "COQFLAGS", "COQC", "ROCQ"}}
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    subprocess.run([sys.executable, str(archive / "reproduce/verify_manifest.py")], cwd=archive, env=env, check=True)
    out.mkdir(parents=True)
    proof = out / "proof/vst"
    shutil.copytree(archive / "proof/vst", proof)
    if list(proof.glob("*.vo")):
        raise ValueError("baseline archive must not supply compiled caches")
    before = {p.name: p.read_bytes() for p in proof.iterdir() if p.is_file()}
    if args.typed_store:
        shutil.copyfile(VST / "doc/design/typed-exact/prototypes/typed_exact_prototype.v", proof / "typed_exact_prototype.v")
    metrics = {}
    patches = []
    for name, edits in EDITS.items():
        original = before[name].decode()
        changed, counts = replace_proofs(original, edits)
        if args.typed_store and name == "verif_word_view_word_view_store_low.v":
            changed = changed.replace("Require Import VST.floyd.FusionStore.",
                                      "Require Import VST.floyd.FusionStore.\nRequire Import typed_exact_prototype.")
            changed, body_count = replace_proofs(changed, {"body_word_view_store_low": TYPED_BODY})
            changed = changed.replace("Lemma body_word_view_store_low", TYPED_BRIDGE + "Lemma body_word_view_store_low", 1)
            counts.update(body_count)
        (proof / name).write_text(changed)
        metrics.update(counts)
        patches.extend(difflib.unified_diff(original.splitlines(True), changed.splitlines(True),
                                           fromfile="a/proof/vst/" + name, tofile="b/proof/vst/" + name))
    (out / "simplification.patch").write_text("".join(patches))
    vfiles = sorted(p.name for p in proof.glob("*.v"))
    (proof / "_CoqProject").write_text('-R . ""\n' + "\n".join(vfiles) + "\n")
    steps = []
    report = {"schema_version": 1, "status": "failed", "archive_id": archive.name,
              "original_workspace_commit": json.loads((archive / "collection-summary.json").read_text())["workspace_commit"],
              "switch": args.switch, "source_count": len(vfiles), "proof_changes": metrics,
              "mode": "typed-store-prototype" if args.typed_store else "existing-api-reuse",
              "additional_client_bridge_lines": len(TYPED_BRIDGE.strip().splitlines()) if args.typed_store else 0,
              "steps": steps, "certification": "experiment only; original cert does not certify this variant"}

    def run(name, command, timeout=120, opam=False):
        if opam:
            command = ["opam", "exec", f"--switch={args.switch}", "--", *command]
        start = time.monotonic()
        result = subprocess.run(command, cwd=proof, env=env, capture_output=True, text=True, timeout=timeout)
        (out / (name + ".log")).write_text(result.stdout + result.stderr)
        steps.append({"name": name, "returncode": result.returncode, "seconds": time.monotonic() - start})
        if result.returncode:
            raise ValueError(f"{name} failed: {result.stderr[-2000:]}")
        return result.stdout

    try:
        run("coq_makefile", ["coq_makefile", "-f", "_CoqProject", "-o", "CoqMakefile"], opam=True)
        run("clean-build", ["make", "-f", "CoqMakefile", "-j2", "TIMER=timeout -k 30s 1800s"], timeout=3600, opam=True)
        for name in vfiles:
            source = proof / name
            vo = source.with_suffix(".vo")
            if not vo.is_file() or vo.stat().st_mtime_ns <= source.stat().st_mtime_ns:
                raise ValueError(f"stale/missing object: {name}")
            run("admit-" + name, [sys.executable, str(archive / "original-delivery/framework/admit_budget.py"), str(source), "0"])
        expected = json.loads((archive / "proof/evidence/axiom-audit.json").read_text())["payload"]["roots"]
        actual = {}
        for row in expected:
            qualified = row["qualified_name"]
            p = proof / "experiment_assumptions.v"
            p.write_text(f'Require Import {qualified.split(".")[0]}.\nPrint Assumptions {qualified}.\nGoal True. idtac "AUDIT_DONE". exact I. Qed.\n')
            text = run("axioms-" + qualified, ["coqc", "-q", "-R", ".", "", p.name], opam=True)
            if "AUDIT_DONE" not in text:
                raise ValueError("incomplete audit")
            aliases = {"Axioms.prop_ext": "prop_ext", "FunctionalExtensionality.functional_extensionality_dep": "functional_extensionality_dep"}
            names = sorted(aliases.get(n, n) for n in set(re.findall(r"(?m)^([A-Za-z_][A-Za-z0-9_.']*)\s*:", text)) - {"Axioms"})
            if names != sorted(row["assumptions"]):
                raise ValueError(f"axiom set changed: {qualified}")
            actual[qualified] = names
            for artifact in proof.glob("experiment_assumptions.*"):
                artifact.unlink()
        run("coqchk", ["coqchk", "-silent", "-R", ".", "", "link", "goals", "alloc_min", "alloc_ef"], timeout=600, opam=True)
        for name, data in before.items():
            if name not in EDITS and (proof / name).read_bytes() != data:
                raise ValueError(f"unexpected change outside proof bodies: {name}")
        report.update(status="passed", unchanged_files=sorted(set(before) - set(EDITS)),
                      actual_axioms=actual,
                      before_sha256={n: sha(before[n]) for n in EDITS},
                      after_sha256={n: sha((proof / n).read_bytes()) for n in EDITS})
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        report["error"] = str(exc)
    (out / "result.json").write_text(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(f"[run2-reuse] {report['status']}: {out / 'result.json'}")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
