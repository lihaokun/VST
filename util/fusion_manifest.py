"""Package install hook and standalone installed-file integrity check."""
import hashlib
import json
from pathlib import Path
import sys


def sha(path):
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"Expected regular file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    action, directory = sys.argv[1:3]
    root = Path(directory).resolve()
    manifest = root / "ccv-fusion.json"
    if action == "verify":
        data = json.loads(manifest.read_text())
        source = Path(__file__).resolve().parent.parent
        expected = json.loads((source / "fusion/release.json").read_text())
        if {k: v for k, v in data.items() if k != "files"} != expected:
            raise SystemExit("Installed release metadata mismatch")
        inventory = (source / "fusion/payload.sha256").read_bytes()
        if hashlib.sha256(inventory).hexdigest() != expected["patch_sha256"]:
            raise SystemExit("Release payload inventory mismatch")
        for line in inventory.decode("ascii").splitlines():
            digest, name = line.split("  ", 1)
            if data["files"].get(name) != digest or name[:-2] + ".vo" not in data["files"]:
                raise SystemExit(f"Missing or incorrect installed payload: {name}")
        for name, digest in data["files"].items():
            if Path(name).is_absolute() or ".." in Path(name).parts or sha(root / name) != digest:
                raise SystemExit(f"Installed hash mismatch: {name}")
        actual = {p.relative_to(root).as_posix() for p in root.rglob("*.vo")}
        if actual != {name for name in data["files"] if name.endswith(".vo")}:
            raise SystemExit("Installed .vo inventory mismatch")
        print(f"Verified {len(actual)} installed .vo files; {manifest}")
        return
    data = json.loads(Path("fusion/release.json").read_text())
    inventory = Path("fusion/payload.sha256").read_bytes()
    if hashlib.sha256(inventory).hexdigest() != data["patch_sha256"]:
        raise SystemExit("Payload inventory hash mismatch")
    payload = dict(line.split("  ", 1)[::-1] for line in inventory.decode("ascii").splitlines())
    for name, digest in payload.items():
        if sha(root / name) != digest:
            raise SystemExit(f"Payload hash mismatch: {name}")
    if action == "check-source":
        if any(root.rglob("*.vo")):
            raise SystemExit("Refusing precompiled source tree")
        dependency_root = Path(sys.argv[3])
        # During opam reinstall the previous VST can still be installed while
        # compilation runs. Only zlist is an external input to this clean build.
        dependencies = {p.relative_to(dependency_root).as_posix(): sha(p)
                        for p in (dependency_root / "zlist").rglob("*.vo")}
        expected = {f"zlist/{name}.vo" for name in
                    ("Zlength_solver", "Zlist", "list_solver", "sublist")}
        if set(dependencies) != expected:
            raise SystemExit("Unexpected zlist dependency inventory before build")
        Path("ccv-dependency.json").write_text(json.dumps(dependencies, sort_keys=True))
        return
    if action != "install":
        raise SystemExit(f"Unknown action: {action}")
    files = {p.relative_to(root).as_posix(): sha(p) for p in sorted(root.rglob("*.vo"))}
    for name in payload:
        if name[:-2] + ".vo" not in files:
            raise SystemExit(f"Missing compiled payload: {name}")
        files[name] = sha(root / name)
    for name in ("concurrency/conclib.vo", "concurrency/ghosts.vo", "atomics/verif_lock.vo"):
        if name not in files:
            raise SystemExit(f"Missing standard vst closure: {name}")
    # Zlist is a separately built package sharing the VST installation directory.
    dependencies = json.loads(Path("ccv-dependency.json").read_text())
    for name, digest in files.items():
        expected = dependencies[name] if name in dependencies else sha(Path(name))
        if expected != digest:
            raise SystemExit(f"Installed/build mismatch: {name}")
    data["files"] = dict(sorted(files.items()))
    manifest.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(f"Installed {manifest}: {len(files)} hashed files")


if __name__ == "__main__":
    main()
