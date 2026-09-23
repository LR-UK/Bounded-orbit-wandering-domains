#!/usr/bin/env python3
"""Build the pinned Lean project and check its source and selected proof axioms."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def without_lean_comments(source):
    """Remove nested Lean comments, preserving strings and executable source.

    Strings are retained (and still scanned), including interpolation bodies.
    This permits ordinary words such as 'separation axiom' in upstream prose
    without modifying attributed source files just to satisfy the scan.
    """
    out = []
    i, depth, in_string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if source[i] == '\n':
                    out.append('\n')
                i += 1
        elif in_string:
            out.append(source[i])
            if source[i] == '\\' and i + 1 < len(source):
                out.append(source[i + 1])
                i += 2
                continue
            if source[i] == '"':
                in_string = False
            i += 1
        elif source.startswith('/-', i):
            out.append(' ')
            depth = 1
            i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            in_string = source[i] == '"'
            i += 1
    if depth:
        raise RuntimeError('Unterminated Lean block comment.')
    return ''.join(out)

def check_axioms(audit_source, output):
    expected = re.findall(r'^#print axioms\s+(\S+)\s*$', audit_source, re.MULTILINE)
    if not expected or len(expected) != len(set(expected)):
        raise RuntimeError('Audit must contain distinct named theorem checks.')
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    actual = [name for name, _ in reports]
    if len(actual) != len(expected) or set(actual) != set(expected):
        raise RuntimeError('The axiom reports do not match the requested declarations.')
    for name, report in reports:
        found = {part.strip() for part in report.split(',') if part.strip()}
        if found - ALLOWED_AXIOMS:
            raise RuntimeError(f'Unexpected axioms for {name}: {sorted(found - ALLOWED_AXIOMS)}')
    return len(expected)

def run_lake(lake, args, root, env, log):
    print('Running: lake ' + ' '.join(args), flush=True)
    chunks = []
    with log.open('w', encoding='utf-8', newline='\n') as stream:
        process = subprocess.Popen([lake, *args], cwd=root, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding='utf-8', errors='replace')
        for line in process.stdout:
            stream.write(line)
            chunks.append(line)
            print(line, end='', flush=True)
        result = process.wait()
    if result:
        raise RuntimeError(f'Lake exited with status {result}; see {log.name}.')
    return ''.join(chunks)

def main():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8', errors='replace')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', help='Optional path to the Lake executable.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    config = json.loads((root / 'scripts/proof-checks.json').read_text(encoding='utf-8'))
    lake = args.lake or shutil.which('lake')
    if not lake:
        raise RuntimeError('Install Lean/Elan and put lake on PATH, or provide --lake.')
    env = os.environ.copy()
    if args.lake:
        lake = str(Path(args.lake).resolve(strict=True))
        env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
    sources = []
    for entry in config['sources']:
        path = root / entry
        if not path.exists():
            raise RuntimeError(f'Missing proof source: {entry}')
        sources.extend(sorted(path.rglob('*.lean')) if path.is_dir() else [path])
    forbidden = re.compile(r'\b(sorry|admit|axiom|native_decide)\b')
    for path in sources:
        if forbidden.search(without_lean_comments(path.read_text(encoding='utf-8-sig'))):
            raise RuntimeError(f'Forbidden proof construct in {path.relative_to(root)}')
    evidence = root / 'verification'
    evidence.mkdir(exist_ok=True)
    summary_path = evidence / 'summary.json'
    if summary_path.exists():
        summary_path.unlink()  # Never leave a stale success record after a failed recheck.
    targets = config['targets']
    if not targets:
        raise RuntimeError('No build targets configured.')
    run_lake(lake, ['build', targets[0]], root, env, evidence / 'build.log')
    if len(targets) > 1:
        run_lake(lake, ['build', *targets[1:]], root, env, evidence / 'targets.log')
    audit_path = root / config['audit']
    output = run_lake(lake, ['env', 'lean', config['audit']], root, env, evidence / 'axioms.log')
    count = check_axioms(audit_path.read_text(encoding='utf-8-sig'), output)
    summary = {
        'result': 'passed', 'checkedAtUTC': datetime.now(timezone.utc).isoformat(),
        'toolchain': (root / 'lean-toolchain').read_text().strip(),
        'targets': targets, 'selectedAxiomReports': count,
        'allowedAxioms': sorted(ALLOWED_AXIOMS),
        'sourceHashNormalization': 'CRLF replaced by LF before SHA-256',
        'sourceSha256': {str(path.relative_to(root)).replace('\\', '/'):
            hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest() for path in sources},
    }
    summary_path.write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(f'PASSED: builds, source integrity, and {count} selected axiom reports.')

if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError) as exc:
        print(f'VERIFICATION FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
