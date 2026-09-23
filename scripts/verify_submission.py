"""Build and audit this submission; not official Palomar Comparator."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
OUT.mkdir(exist_ok=True)
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
CONFIG = json.loads((ROOT / "comparator.json").read_text())
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def run(args, output):
    with (OUT / output).open("w") as stream:
        result = subprocess.run([LAKE, *args], cwd=ROOT, stdout=stream,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{args} failed; see verification/{output}")

subprocess.run([sys.executable, str(ROOT / "scripts/build_submission.py")], cwd=ROOT, check=True)
run(["build", "BoundedWanderingDomains", "Submission", "Challenge", "CoveringSolution"], "build.log")
build_warnings = [line for line in (OUT / "build.log").read_text().splitlines()
                  if line.startswith("warning:")]
unexpected_warnings = [line for line in build_warnings if not re.fullmatch(
    r"warning: Challenge\.lean:\d+:\d+: declaration uses `sorry`", line)]
assert not unexpected_warnings, "Unexpected build warnings: " + repr(unexpected_warnings)
run(["env", "lean", "verification/Axioms.lean"], "axioms.log")
run(["env", "lean", "verification/CoveringAxioms.lean"], "covering-axioms.log")
run(["env", "lean", "verification/UnconditionalAxioms.lean"], "unconditional-axioms.log")
for which in ("Challenge", "Solution"):
    run(["env", "lean", f"verification/Export{which}.lean"],
        f"{which.lower()}-declarations.log")

def declarations(which):
    result = {}
    for line in (OUT / f"{which}-declarations.log").read_text().splitlines():
        if "PALOMAR_DECL " in line:
            item = json.loads(line.split("PALOMAR_DECL ", 1)[1])
            assert item["name"] not in result
            result[item["name"]] = item
    return result

challenge, solution = declarations("challenge"), declarations("solution")
expected = set(CONFIG["theorem_names"] + CONFIG["definition_names"])
assert set(challenge) == set(solution) == expected
for name in sorted(expected):
    assert challenge[name] == solution[name], f"Declaration mismatch: {name}"

audit = (OUT / "axioms.log").read_text() + (OUT / "covering-axioms.log").read_text() + (OUT / "unconditional-axioms.log").read_text()
reports = re.findall(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    audit)
assert set(CONFIG["theorem_names"]) <= {n for n, _ in reports}
for name, axioms in reports:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= ALLOWED, name
assert "error:" not in audit

spec = importlib.util.spec_from_file_location(
    "foundation_verify", ROOT / "dependencies/FunctionTheory/scripts/verify.py")
lexer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lexer)
sources = sorted([*ROOT.glob("*.lean"), *(ROOT / "BoundedWanderingDomains").rglob("*.lean"),
                  *(ROOT / "RiemannDynamics").rglob("*.lean"), *(ROOT / "RMT4").rglob("*.lean")])
for source in sources:
    code = lexer.without_lean_comments(source.read_text())
    holes = re.findall(r"\b(?:sorry|admit)\b", code)
    if source.name == "Challenge.lean":
        assert holes == ["sorry", "sorry"]
    else:
        assert not holes, source.name
    assert not re.search(r"\b(?:axiom|native_decide)\b|Lean\.ofReduceBool", code), source.name

text = (ROOT / "Challenge.lean").read_text()
imports = re.findall(r"^import\s+(\S+)\s*$", text, re.M)
assert imports and all(i.startswith("Mathlib.") for i in imports)
assert len(text.splitlines()) <= 300 and len(text.encode()) <= 32 * 1024
for module in imports:
    rel = Path(*module.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "dependencies/FunctionTheory",
                 ROOT / "dependencies/ComplexDynamics",
                 ROOT / "dependencies/ComplexApproximation",
                 ROOT / "dependencies/EremenkosConjecture",
                 ROOT / "dependencies/EremenkosConjecture/vendor/schoenflies"):
        assert not (base / rel).exists(), f"Shadowed Mathlib import: {base / rel}"
assert "import Challenge" not in (ROOT / "Solution.lean").read_text()
assert set(CONFIG["permitted_axioms"]) == ALLOWED
assert "external_kernels" not in CONFIG
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
for package in manifest["packages"]:
    if package["type"] == "path":
        assert (ROOT / package["dir"]).resolve().is_relative_to(ROOT), package

report = {
    "result": "passed", "project_version": "1.1.0",
    "lean": (ROOT / "lean-toolchain").read_text().strip(),
    "mathlib": mathlib,
    "curvature": -1, "area_normalisation": "divide by 2*pi",
    "theorem_types_compared": len(CONFIG["theorem_names"]),
    "definition_types_and_bodies_compared": len(CONFIG["definition_names"]),
    "comparison": "elaborated expressions; binder display names and metadata erased",
    "axiom_reports": {n: [a.strip() for a in ax.split(",") if a.strip()]
                      for n, ax in reports},
    "project_lean_sources": len(sources),
    "challenge_lines": len(text.splitlines()), "challenge_bytes": len(text.encode()),
    "challenge_intentional_holes": 2, "challenge_direct_imports": imports,
    "unexpected_build_warnings": unexpected_warnings,
    "expected_challenge_warnings": build_warnings,
    "source_sha256": {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sources + [ROOT / "comparator.json", ROOT / "formalization.yaml",
                                          ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]},
    "official_comparator": "see comparator-status.json and comparator.log",
    "metadata_contract": "see metadata.json", "public_submission": "not made",
}
(OUT / "submission.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ("result", "theorem_types_compared",
      "definition_types_and_bodies_compared", "challenge_lines", "challenge_bytes")}))
