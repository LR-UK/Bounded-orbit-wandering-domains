"""Build and audit the current paper statements and retained entire-function theorem (not official Comparator)."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
LAKE = shutil.which('lake')
if not LAKE:
    raise SystemExit('Put the pinned Lean toolchain on PATH first.')
CONFIG = json.loads((ROOT / 'comparator-paper.json').read_text(encoding='utf-8'))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ENV = dict(os.environ)
ENV.setdefault('LEAN_NUM_THREADS', '2')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--all', action='store_true', help='Also build the retained legacy and research entry points.')
args = parser.parse_args()
timings = []
report_path = OUT / 'paper-submission.json'
if report_path.exists():
    report_path.unlink()  # A failed recheck must not leave a stale success report.

def run(args, filename):
    print('Checking ' + filename, flush=True)
    started = time.perf_counter()
    with (OUT / filename).open('w', encoding='utf-8') as log:
        result = subprocess.run([LAKE, *args], cwd=ROOT, env=ENV, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{args} failed; see verification/{filename}')
    timings.append({'command': args, 'seconds': time.perf_counter() - started})

targets = ['Solution', 'Challenge']
if args.all:
    targets += ['Research.SurfaceResearch', 'Legacy.Solution', 'Legacy.Challenge', 'BoundedWanderingDomains.CoveringSolution',
                'Research.NewResults', 'Legacy.SingularLimitsChallenge', 'Legacy.SingularLimitsSolution']
run(['build', *targets], 'paper-build.log')
for module in ['Challenge', 'Solution']:
    run(['env', 'lean', f'verification/ExportPaper{module}.lean'], 'paper' + module.lower() + '-declarations.log')

def declarations(module):
    answer = {}
    for line in (OUT / ('paper' + module.lower() + '-declarations.log')).read_text(encoding='utf-8').splitlines():
        if 'PALOMAR_DECL ' in line:
            entry = json.loads(line.split('PALOMAR_DECL ', 1)[1])
            assert entry['name'] not in answer
            answer[entry['name']] = entry
    return answer

challenge, solution = declarations('Challenge'), declarations('Solution')
assert set(challenge) == set(solution), 'Missing compared declarations'
claim_names = [
    'BoundedWanderingDomains.wandering_orbit_locallyUniform_inftyClaim',
    'BoundedWanderingDomains.wandering_orbit_pointwise_spherical_singular_derivedSetClaim',
    'MeromorphicDynamics.WanderingLocallyUniformInfinityClaim',
    'SurfaceDynamics.NoCompactWanderingOrbitClaim',
    'SurfaceDynamics.NoCompactPositiveAreaWanderingSetClaim',
    'SurfaceDynamics.WanderingDerivedSingularLimitClaim',
]
expected_declarations = set(CONFIG['theorem_names'] + CONFIG['definition_names'] +
                            claim_names + ['SurfaceDynamics.LocalMap'])
assert set(challenge) == expected_declarations, 'Missing or unexpected declaration in comparison'
mismatches = {name: [key for key in set(challenge[name]) | set(solution[name])
                     if challenge[name].get(key) != solution[name].get(key)]
              for name in challenge if challenge[name] != solution[name]}
if mismatches:
    (OUT / 'paper-declaration-mismatches.json').write_text(json.dumps(mismatches, indent=2), encoding='utf-8')
    raise AssertionError('Independent declaration mismatch: ' + repr(mismatches))

# The solution exporter also prints the transitive axiom reports. Keeping
# these checks in the same Lean process avoids loading the large proof
# environment a second time. PaperAxioms.lean remains a standalone audit.
audit_text = (OUT / 'papersolution-declarations.log').read_text(encoding='utf-8')
axioms = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text))
assert set(CONFIG['theorem_names']) == set(axioms), 'Missing theorem axiom reports'
axioms = {name: [s.strip() for s in values.split(',') if s.strip()] for name, values in axioms.items()}
assert all(set(values) <= ALLOWED for values in axioms.values()), 'Unexpected axiom'
(OUT / 'paper-axioms.log').write_text(''.join(
    f"'{name}' depends on axioms: [{', '.join(values)}]\n" for name, values in axioms.items()), encoding='utf-8')

spec = importlib.util.spec_from_file_location('source_audit', ROOT / 'dependencies/FunctionTheory/scripts/verify.py')
source_audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source_audit)
bases = [ROOT] + [ROOT / 'dependencies' / name for name in
    ['FunctionTheory', 'ComplexDynamics', 'ComplexApproximation', 'EremenkosConjecture']]
bases.append(ROOT / 'dependencies/EremenkosConjecture/vendor/schoenflies')
trusted = {'Mathlib', 'Batteries', 'Aesop', 'Qq', 'ProofWidgets', 'LeanSearchClient',
           'ImportGraph', 'Plausible', 'Init', 'Lean', 'Std', 'Lake'}
visited = {}

def visit(module):
    if module in visited or module.split('.')[0] in trusted:
        return
    path = next((base / Path(*module.split('.')).with_suffix('.lean') for base in bases
                 if (base / Path(*module.split('.')).with_suffix('.lean')).is_file()), None)
    if path is None:
        raise RuntimeError('Cannot resolve proof import ' + module)
    code = source_audit.without_lean_comments(path.read_text(encoding='utf-8'))
    if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+)?axiom\s', code, re.M):
        raise AssertionError('Unexpected proof shortcut in ' + str(path.relative_to(ROOT)))
    if module.endswith('Challenge'):
        raise AssertionError('A challenge was imported by the proof')
    imports = [item for line in re.findall(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([^\n]+)', code, re.M)
               for item in line.split()]
    visited[module] = {'file': path.relative_to(ROOT).as_posix(), 'imports': imports,
                       'sha256': hashlib.sha256(path.read_text(encoding='utf-8').encode('utf-8')).hexdigest()}
    for dependency in imports:
        visit(dependency)

visit('Solution')
paper_visited = dict(visited)
if args.all:
    for module in ['Research.SurfaceResearch', 'Legacy.Solution', 'BoundedWanderingDomains.CoveringSolution', 'Research.NewResults',
                   'Legacy.SingularLimitsSolution']:
        visit(module)
report = {
    'result': 'passed', 'scope': 'Local Lean build, independent declaration equality, source closure and transitive axioms',
    'official_comparator': 'Not run by this script; use scripts/verify-comparator.sh comparator-paper.json on Linux',
    'theorems_compared': len(CONFIG['theorem_names']),
    'supporting_declarations_compared': len(challenge) - len(CONFIG['theorem_names']),
    'local_proof_modules_scanned': len(paper_visited), 'axioms': axioms,
    'built_all_entry_points': args.all,
    'all_local_proof_modules_scanned': len(visited),
    'source_hash_encoding': 'UTF-8 with LF line endings',
    'declarations_sha256': hashlib.sha256(json.dumps(challenge, sort_keys=True).encode()).hexdigest(),
    'proof_imports': paper_visited,
    'additional_proof_imports': {n: v for n, v in visited.items() if n not in paper_visited},
}
report_path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
(OUT / 'paper-check-timings.json').write_text(json.dumps(timings, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: report[k] for k in ['result', 'theorems_compared', 'supporting_declarations_compared', 'local_proof_modules_scanned']}))
