"""Reject tracked Lean sources that have not adopted Lean's module system."""
from pathlib import Path
import importlib.util
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'lean_comments', ROOT / 'dependencies/FunctionTheory/scripts/verify.py')
lexer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lexer)


def audit():
    if (ROOT / '.git').exists():
        names = subprocess.check_output(
            ['git', '-C', str(ROOT), 'ls-files', '-z'], text=True).split('\0')
        paths = sorted(ROOT / name for name in names if name.endswith('.lean'))
    else:
        paths = []
        for directory, folders, names in os.walk(ROOT):
            folders[:] = [f for f in folders if f not in {'.git', '.lake', '__pycache__'}]
            paths.extend(Path(directory) / name for name in names if name.endswith('.lean'))
        paths.sort()
    missing = []
    for path in paths:
        code = lexer.without_lean_comments(path.read_text(encoding='utf-8-sig')).lstrip()
        if not re.match(r'module\b', code):
            missing.append(path.relative_to(ROOT).as_posix())
    report = {'result': 'failed' if missing else 'passed',
              'scope': 'Module headers in all tracked Lean sources; visibility is checked by Lean builds',
              'lean_sources_checked': len(paths), 'missing_module_headers': missing}
    output = ROOT / 'verification/module-headers.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    if missing:
        raise SystemExit('Missing module headers:\n' + '\n'.join(missing))
    print(f'Module headers passed: {len(paths)} Lean sources.')
    return report


if __name__ == '__main__':
    audit()
