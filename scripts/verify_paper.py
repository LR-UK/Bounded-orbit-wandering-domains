"""Build and audit the six revised-paper statements (not official Comparator)."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess

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

def run(args, filename):
    print('Checking ' + filename, flush=True)
    with (OUT / filename).open('w', encoding='utf-8') as log:
        result = subprocess.run([LAKE, *args], cwd=ROOT, env=ENV, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{args} failed; see verification/{filename}')

run(['build', 'PaperSolution', 'PaperChallenge', 'SurfaceResearch'], 'paper-build.log')
run(['env', 'lean', 'verification/PaperAxioms.lean'], 'paper-axioms.log')
for module in ['PaperChallenge', 'PaperSolution']:
    run(['env', 'lean', f'verification/Export{module}.lean'], module.lower() + '-declarations.log')

def declarations(module):
    answer = {}
    for line in (OUT / (module.lower() + '-declarations.log')).read_text(encoding='utf-8').splitlines():
        if 'PALOMAR_DECL ' in line:
            entry = json.loads(line.split('PALOMAR_DECL ', 1)[1])
            assert entry['name'] not in answer
            answer[entry['name']] = entry
    return answer

challenge, solution = declarations('PaperChallenge'), declarations('PaperSolution')
assert set(challenge) == set(solution), 'Missing compared declarations'
mismatches = {name: [key for key in set(challenge[name]) | set(solution[name])
                     if challenge[name].get(key) != solution[name].get(key)]
              for name in challenge if challenge[name] != solution[name]}
if mismatches:
    (OUT / 'paper-declaration-mismatches.json').write_text(json.dumps(mismatches, indent=2), encoding='utf-8')
    raise AssertionError('Independent declaration mismatch: ' + repr(mismatches))

audit_text = (OUT / 'paper-axioms.log').read_text(encoding='utf-8')
axioms = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text))
assert set(CONFIG['theorem_names']) == set(axioms), 'Missing theorem axiom reports'
axioms = {name: [s.strip() for s in values.split(',') if s.strip()] for name, values in axioms.items()}
assert all(set(values) <= ALLOWED for values in axioms.values()), 'Unexpected axiom'

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

visit('PaperSolution')
report = {
    'result': 'passed', 'scope': 'Local Lean build, independent declaration equality, source closure and transitive axioms',
    'official_comparator': 'Not run by this script; use scripts/verify-comparator.sh comparator-paper.json on Linux',
    'theorems_compared': len(CONFIG['theorem_names']),
    'supporting_declarations_compared': len(challenge) - len(CONFIG['theorem_names']),
    'local_proof_modules_scanned': len(visited), 'axioms': axioms,
    'source_hash_encoding': 'UTF-8 with LF line endings',
    'declarations_sha256': hashlib.sha256(json.dumps(challenge, sort_keys=True).encode()).hexdigest(),
    'proof_imports': visited,
}
(OUT / 'paper-submission.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: report[k] for k in ['result', 'theorems_compared', 'supporting_declarations_compared', 'local_proof_modules_scanned']}))
