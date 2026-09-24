"""Audit the completed working branch; not official Comparator replay.

Unlike the historical submission verifier, this reports dependency linter and
deprecation warnings instead of asserting a warning-free build. Kernel errors,
nonstandard axioms, proof holes, and declaration mismatches remain fatal.
"""
from pathlib import Path
import hashlib, importlib.util, json, os, re, shutil, subprocess
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONFIG = json.loads((ROOT / "comparator.json").read_text())
def run(args, filename):
    with (OUT / filename).open("w") as stream:
        subprocess.run([LAKE, *args], cwd=ROOT, stdout=stream,
                       stderr=subprocess.STDOUT, check=True)
    return (OUT / filename).read_text()
build = run(["build", "BoundedWanderingDomains", "Submission", "Challenge",
             "CoveringSolution", "NewResults"], "completion-build.log")
audit = run(["env", "lean", "verification/NewResultsAxioms.lean"], "completion-axioms.log")
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", audit)
assert len(reports) == 7, reports
for name, axioms in reports:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= ALLOWED, name
assert "error:" not in audit
exports = {}
for which in ("Challenge", "Solution"):
    log = run(["env", "lean", f"verification/Export{which}.lean"], f"completion-{which.lower()}-declarations.log")
    declarations = {}
    for line in log.splitlines():
        if "PALOMAR_DECL " in line:
            item = json.loads(line.split("PALOMAR_DECL ", 1)[1])
            assert item["name"] not in declarations
            declarations[item["name"]] = item
    exports[which] = declarations
expected = set(CONFIG["theorem_names"] + CONFIG["definition_names"])
assert set(exports["Challenge"]) == set(exports["Solution"]) == expected
for name in expected:
    assert exports["Challenge"][name] == exports["Solution"][name], name
spec = importlib.util.spec_from_file_location("foundation_verify", ROOT / "dependencies/FunctionTheory/scripts/verify.py")
lexer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lexer)
sources = sorted([*ROOT.glob("*.lean"), *(p for d in
    ["BoundedWanderingDomains", "RiemannDynamics", "RMT4", "EremenkoLyubichConstant", "Ray"]
    for p in (ROOT / d).rglob("*.lean"))])
for source in sources:
    code = lexer.without_lean_comments(source.read_text())
    holes = re.findall(r"\b(?:sorry|admit)\b", code)
    assert holes == (["sorry", "sorry"] if source == ROOT / "Challenge.lean" else []), str(source)
    assert not re.search(r"\b(?:axiom|native_decide)\b|Lean\.ofReduceBool", code), str(source)
challenge = (ROOT / "Challenge.lean").read_text()
assert all(i.startswith("Mathlib.") for i in re.findall(r"^import\s+(\S+)\s*$", challenge, re.M))
assert len(challenge.splitlines()) <= 300
assert "import Challenge" not in (ROOT / "Solution.lean").read_text()
report = {
    "result": "passed", "date": "2026-09-24",
    "lean": (ROOT / "lean-toolchain").read_text().strip(),
    "mathlib": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
    "theorem_types_compared": len(CONFIG["theorem_names"]),
    "definition_types_and_bodies_compared": len(CONFIG["definition_names"]),
    "axioms": {n: [a.strip() for a in ax.split(",") if a.strip()] for n, ax in reports},
    "source_files_scanned": len(sources), "intentional_challenge_holes": 2,
    "build_warnings": [l for l in build.splitlines() if l.startswith("warning:")],
    "official_comparator": "not run for this snapshot",
    "new_results_in_registry_comparison": False,
    "source_sha256": {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
}
(OUT / "completion.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ["result", "theorem_types_compared", "definition_types_and_bodies_compared", "source_files_scanned"]}))
