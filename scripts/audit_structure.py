"""Inventory source imports, duplicate source text and diagnostic commands.

Run independently of the Lean build. A transitive import listed as redundant
is not automatically a candidate for removal: explicit imports can document
intended dependencies, and removing imports requires recompilation.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import os
import re
import subprocess

root = Path(__file__).resolve().parents[1]
out = root / 'verification'
out.mkdir(exist_ok=True)
spec = importlib.util.spec_from_file_location('lexer', root / 'dependencies/FunctionTheory/scripts/verify.py')
lexer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lexer)
bases = [root] + [root / 'dependencies' / n for n in
    ['FunctionTheory', 'ComplexDynamics', 'ComplexApproximation', 'EremenkosConjecture']]
bases.append(root / 'dependencies/EremenkosConjecture/vendor/schoenflies')
if (root / '.git').exists():
    tracked = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-z'], text=True).split('\0')
else:
    tracked = []
    for directory, folders, names in os.walk(root):
        folders[:] = [f for f in folders if f not in {'.git', '.lake', '__pycache__'}]
        tracked.extend((Path(directory) / name).relative_to(root).as_posix()
                       for name in names if name.endswith('.lean'))
files = [root / p for p in tracked if p.endswith('.lean')]
imports = {}
paths = {}
sizes = {}
diagnostics = {}
duplicates = defaultdict(list)
module_paths = defaultdict(list)
file_diagnostics = {}
for path in files:
    rel = path.relative_to(root).as_posix()
    code = lexer.without_lean_comments(path.read_text(encoding='utf-8'))
    match = [b for b in bases if path.is_relative_to(b)]
    b = max(match, key=lambda b: len(str(b)))
    module = '.'.join(path.relative_to(b).with_suffix('').parts)
    module_paths[module].append(rel)
    paths[module] = rel
    imports[module] = [s for line in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)', code, re.M)
                       for s in line.split() if s != '--']
    sizes[module] = {'bytes': path.stat().st_size, 'lines': len(code.splitlines())}
    diagnostics[module] = re.findall(r'^\s*#(?:print\s+axioms|check|eval)\b[^\n]*', code, re.M)
    file_diagnostics[rel] = len(diagnostics[module])
    duplicates[hashlib.sha256(re.sub(r'\s+', ' ', code).strip().encode()).hexdigest()].append(rel)

def closure(start):
    found = set()
    pending = list(start)
    while pending:
        name = pending.pop()
        if name in found:
            continue
        found.add(name)
        pending.extend(imports.get(name, []))
    return found

root_names = ['PaperSolution', 'PaperChallenge', 'Solution', 'Challenge', 'NewResults',
              'SingularLimitsChallenge', 'SingularLimitsSolution', 'SurfaceResearch', 'CoveringSolution']
closure_by_root = {n: closure([n]) for n in root_names}
paper = closure_by_root['PaperSolution']
all_roots = closure(root_names)
collisions = {n: ps for n, ps in module_paths.items() if len(ps) > 1}
assert not (all_roots & collisions.keys()), 'An active import resolves to multiple source files'
redundant = {}
for name, deps in imports.items():
    covered = {d: closure([d]) for d in deps}
    redundant[name] = [d for d in deps if any(d in covered[e] for e in deps if e != d)]
data = {
    'tracked_lean_files': len(files),
    'auxiliary_module_name_collisions': collisions,
    'root_closures': {n: {'local': len(s & imports.keys()), 'external_frontier': len(s - imports.keys())}
                      for n, s in closure_by_root.items()},
    'all_root_local_modules': len(all_roots & imports.keys()),
    'extra_local_modules_in_legacy_build': sorted((all_roots - paper) & imports.keys()),
    'unused_local_modules': sorted(imports.keys() - all_roots),
    'diagnostic_commands': sum(file_diagnostics.values()),
    'paper_diagnostic_commands': sum(len(diagnostics[n]) for n in paper & imports.keys()),
    'diagnostics_by_file': {p: count for p, count in file_diagnostics.items() if count},
    'exact_source_duplicates_ignoring_comments': [ps for ps in duplicates.values() if len(ps) > 1],
    'redundant_direct_imports': {paths[n]: ds for n, ds in redundant.items() if ds},
    'paper_modules': sorted(paper & imports.keys()),
    'imports': imports, 'paths': paths, 'sizes': sizes,
}
(out / 'structure-audit.json').write_text(json.dumps(data, indent=2), encoding='utf-8')
summary = {k: v for k, v in data.items() if k not in
    {'diagnostics_by_file','imports','paths','sizes','paper_modules','redundant_direct_imports', 'unused_local_modules'}}
summary['unused_local_module_count'] = len(data['unused_local_modules'])
summary['redundant_import_count'] = sum(map(len, data['redundant_direct_imports'].values()))
summary['largest_diagnostic_files'] = Counter(data['diagnostics_by_file']).most_common(15)
print(json.dumps(summary, indent=2))
