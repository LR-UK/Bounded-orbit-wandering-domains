"""Fetch Mathlib cache for imports throughout the contained source closure.

Mathlib's cache traverses Mathlib imports, but skips imports of local libraries.
Walk those libraries first so a root Solution.lean does not omit its foundations.
"""
from pathlib import Path
import importlib.util
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASES = [ROOT, *(ROOT / 'dependencies' / name for name in (
    'FunctionTheory', 'ComplexDynamics', 'ComplexApproximation', 'EremenkosConjecture')),
    ROOT / 'dependencies/EremenkosConjecture/vendor/schoenflies']
spec = importlib.util.spec_from_file_location('foundation_verify',
    ROOT / 'dependencies/FunctionTheory/scripts/verify.py')
lexer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lexer)
CACHE = {'Mathlib', 'Batteries', 'Aesop', 'Qq', 'ProofWidgets', 'LeanSearchClient',
         'ImportGraph', 'Plausible'}
CORE = {'Init', 'Lean', 'Std', 'Lake'}
seen, imports = set(), set()
pending = ['Solution', 'Challenge', 'BoundedWanderingDomains', 'CoveringSolution']
while pending:
    module = pending.pop()
    if module in seen:
        continue
    seen.add(module)
    prefix = module.split('.')[0]
    if prefix in CACHE:
        imports.add(module)
        continue
    if prefix in CORE:
        continue
    rel = Path(*module.split('.')).with_suffix('.lean')
    matches = [base / rel for base in BASES if (base / rel).is_file()]
    if len(matches) != 1 and not (ROOT / rel).is_file():
        raise RuntimeError(f'Module {module}: expected one contained source, found {matches}')
    code = lexer.without_lean_comments(matches[0].read_text())
    for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', code, re.M):
        pending.extend(line.split())
lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
print(f'Fetching cache for {len(imports)} direct foundation imports', flush=True)
subprocess.run([lake, 'exe', 'cache', 'get', *sorted(imports)], cwd=ROOT, check=True)
