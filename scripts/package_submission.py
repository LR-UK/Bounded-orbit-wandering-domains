"""Create the review archive, with real contained source dependencies."""
from pathlib import Path
import hashlib
import json
import os
import zipfile
from audit_attribution import audit

root = Path(__file__).resolve().parents[1]
assert json.loads((root / "verification/submission.json").read_text())["result"] == "passed"
moves = json.loads((root / "verification/moved-sources.json").read_text())
for old_path, new_path in moves.items():
    assert not (root / old_path).exists(), f"Obsolete source remains: {old_path}"
    assert (root / new_path).is_file(), f"Missing moved source: {new_path}"
attribution = audit()
excluded = {".lake", ".git", "__pycache__"}
files = []
for directory, dirs, names in os.walk(root, followlinks=True):
    dirs[:] = sorted(d for d in dirs if d not in excluded)
    for name in sorted(names):
        path = Path(directory) / name
        if path.is_file() and path.suffix not in {".pyc", ".olean", ".ilean", ".trace"}:
            files.append(path)
manifest = {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in files if p.name != "package-sources.json"}
(root / "verification/package-sources.json").write_text(json.dumps(manifest, indent=2) + "\n")
files = [p for p in files if p.name != "package-sources.json"]
files.append(root / "verification/package-sources.json")
archive = root.parent / "bounded-wandering-palomar.zip"
with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as z:
    for path in files:
        z.write(path, Path(root.name) / path.relative_to(root))
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for rel, digest in attribution["attribution_files"].items():
        assert hashlib.sha256(z.read(f"{root.name}/{rel}")).hexdigest() == digest, rel
    for dep in ("FunctionTheory", "ComplexDynamics", "ComplexApproximation", "EremenkosConjecture"):
        assert f"{root.name}/dependencies/{dep}/lakefile.toml" in z.namelist()
    for info in z.infolist():
        assert (info.external_attr >> 16) & 0o170000 != 0o120000, info.filename
        assert not any(part in excluded for part in Path(info.filename).parts)
print(json.dumps({"archive": str(archive), "bytes": archive.stat().st_size,
                  "source_files": len(files), "contained_dependencies": True}))
