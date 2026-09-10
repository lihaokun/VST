#!/usr/bin/env python3
"""构建接线负例：只使用临时安装目录，不改所选 switch。"""
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
MODULES = ("FusionExact", "FusionExactSem", "FusionMemvals", "FusionViews64",
           "FusionStore", "SeparationLogicAsLogicSoundness")


class BuildTests(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("OPAM_SWITCH_PREFIX"), "run via opam exec")
    def test_unsupported_external_version_is_rejected(self):
        result = subprocess.run(["make", "-o", ".depend", "nothing", "ZLIST=platform",
                                 "BITSIZE=64", "CV2=version=99.0"], cwd=ROOT,
                                capture_output=True, text=True, timeout=60)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Unsupported external COMPCERT VERSION", result.stderr)

    @unittest.skipUnless(os.environ.get("OPAM_SWITCH_PREFIX"), "run via opam exec")
    def test_other_arch_has_no_fusion_test_members(self):
        result = subprocess.run(["make", "-o", ".depend", "print_fusion_members",
                                 "--eval=print_fusion_members: ; @printf '%s\\n' '$(PROGS64_FILES)'",
                                 "ZLIST=platform", "BITSIZE=64", "ARCH=aarch64",
                                 "COMPCERT_ARCH=aarch64"], cwd=ROOT,
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("fusion/views_client.v", result.stdout)

    @unittest.skipUnless(os.environ.get("OPAM_SWITCH_PREFIX"), "run via opam exec")
    def test_install_build_failure_precedes_copy(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "VST"
            result = subprocess.run([
                "make", "install", "-o", "vst", "ZLIST=platform", "BITSIZE=64",
                f"INSTALLDIR={dest}", "INSTALL_FILES_VO=missing_required_fusion.vo"],
                cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing_required_fusion.vo", result.stderr)
            self.assertFalse(dest.exists())

    @unittest.skipUnless(os.environ.get("OPAM_SWITCH_PREFIX"), "run via opam exec")
    def test_canonical_clight_regeneration(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            for stem in ("seed_program", "seed_union_rw"):
                shutil.copyfile(ROOT / "progs64/fusion" / (stem + ".c"), work / (stem + ".c"))
                subprocess.run(["clightgen", "-normalize", "-canonical-idents", stem + ".c"],
                               cwd=work, check=True, capture_output=True, timeout=60)
                def normalize(text):
                    # 历史 fixture 清过行尾空格；只归一这一格式差异和已知路径字段。
                    text = re.sub(r'Definition source_file := "[^"]*"\.',
                                  'Definition source_file := "<source>".', text)
                    return "\n".join(line.rstrip() for line in text.splitlines()).rstrip()
                self.assertEqual(normalize((work / (stem + ".v")).read_text()),
                                 normalize((ROOT / "progs64/fusion" / (stem + ".v")).read_text()))

    @unittest.skipUnless(os.environ.get("OPAM_SWITCH_PREFIX"), "run via opam exec")
    def test_clean_preserves_nested_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            examples = work / "progs64/fusion"
            examples.mkdir(parents=True)
            for suffix in ("v", "c", "vo", "vos", "vok", "glob"):
                (examples / ("sample." + suffix)).touch()
            (examples / ".sample.aux").touch()
            cc = Path(os.environ["OPAM_SWITCH_PREFIX"]) / "lib/coq/user-contrib/compcert"
            subprocess.run(["make", "-f", str(ROOT / "Makefile"), "-o", ".depend", "clean",
                            "ZLIST=platform", "BITSIZE=64", "COMPCERT=inst_dir",
                            f"COMPCERT_INST_DIR={cc}", f"COMPCERT_INFO_PATH_REF={cc}"],
                           cwd=work, check=True, capture_output=True, timeout=60)
            self.assertEqual({p.name for p in examples.iterdir()}, {"sample.v", "sample.c"})

    def test_missing_installed_module_never_uses_source_tree(self):
        for missing in MODULES:
            with self.subTest(module=missing), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "VST"
                (root / "floyd").mkdir(parents=True)
                for module in MODULES:
                    if module != missing:
                        (root / "floyd" / (module + ".vo")).touch()
                env = {**os.environ, "OPAM_SWITCH_PREFIX": "/not-used"}
                result = subprocess.run(["bash", str(ROOT / "util/check_fusion.sh"), str(root)],
                                        cwd=ROOT, env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 1)
                self.assertIn(f"Missing installed module: {missing}", result.stderr)

    @unittest.skipUnless(os.environ.get("OPAM_SWITCH_PREFIX"), "run via opam exec")
    def test_first_copy_failure_cannot_be_hidden_by_last_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "VST"
            result = subprocess.run([
                "make", "--no-print-directory", "install", "-o", "vst", "MAKE=true",
                "ZLIST=platform", "BITSIZE=64", f"INSTALLDIR={dest}",
                "INSTALL_FILES=missing_fusion_regression.vo VERSION", "INSTALL_FILES_VO=",
                "EXTRA_INSTALL_FILES="], cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing_fusion_regression.vo", result.stderr)
            self.assertFalse((dest / "VERSION").exists())


if __name__ == "__main__":
    unittest.main()
