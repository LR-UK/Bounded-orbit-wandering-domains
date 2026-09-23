"""Audit the retained attribution material; no network or legal conclusions."""
from pathlib import Path
import hashlib
import json
import os
import re

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def audit():
    records = {ROOT / 'LICENSE', ROOT / 'THIRD_PARTY_NOTICES.md',
               ROOT / 'DEPENDENCY_COMPATIBILITY.md',
               ROOT / 'verification/linter-updated-files.json',
               ROOT / 'verification/linter-compatibility.patch',
               ROOT / 'RIEMANN_DYNAMICS_LICENSE', ROOT / 'RMT4_LICENSE',
               ROOT / 'port-deprecation-updates.json',
               ROOT / 'verification/toolchain435-changes.json',
               ROOT / 'verification/toolchain435-changes.patch',
               ROOT / 'verification/palomar-contract/LICENSE',
               ROOT / 'verification/palomar-contract/PROVENANCE.md'}
    for name in ('FunctionTheory', 'ComplexDynamics', 'ComplexApproximation', 'EremenkosConjecture'):
        base = ROOT / 'dependencies' / name
        for filename in ('LICENSE', 'THIRD_PARTY_NOTICES.md', 'PROVENANCE.md'):
            path = base / filename
            assert path.is_file(), path
            records.add(path)
    for folder in (ROOT / 'dependencies/FunctionTheory/third_party',
                   ROOT / 'dependencies/EremenkosConjecture/vendor/schoenflies'):
        for directory, dirs, names in os.walk(folder, followlinks=True):
            dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '__pycache__'}]
            for name in names:
                path = Path(directory) / name
                if 'third_party' in path.parts or name in {'LICENSE', 'PROVENANCE.md', 'ALIGNMENT.json'}:
                    records.add(path)
    licences = sorted(p for p in records if (p.name == 'LICENSE' and 'palomar-contract' not in p.parts) or p.name in {'RIEMANN_DYNAMICS_LICENSE', 'RMT4_LICENSE'})
    assert len(licences) == 11
    for path in licences:
        text = path.read_text()
        assert 'Apache License' in text and 'Version 2.0, January 2004' in text, path
        assert 'END OF TERMS AND CONDITIONS' in text, path

    groups = []
    for name, rel, expected in (
        ('Tau Ceti', 'dependencies/FunctionTheory/TauCeti', 138),
        ('NoWanderingDomains', 'dependencies/FunctionTheory/NoWanderingDomains', 8),
        ('Schoenflies', 'dependencies/EremenkosConjecture/vendor/schoenflies/Schoenflies', 128),
    ):
        files = sorted((ROOT / rel).rglob('*.lean'))
        assert len(files) == expected, (name, len(files))
        authors = set()
        for path in files:
            text = path.read_text()
            assert 'Copyright (c)' in text[:1000] and 'Apache 2.0' in text[:1000], path
            authors.update(re.findall(r'(?m)^Authors?:\s*(.+)', text))
        groups.append({'name': name, 'files': len(files), 'header_authors': sorted(authors),
                       'source_sha256': {p.relative_to(ROOT).as_posix(): sha(p) for p in files}})
    for name in ('RiemannMappingFull', 'UnitDiscShift'):
        path = ROOT / 'BoundedWanderingDomains' / (name + '.lean')
        text = path.read_text()
        assert 'Yury Kudryashov' in text[:500] and 'Apache 2.0' in text[:500]
        assert 'd43061d911b1aeae0788591da437a3b115098962' in text
        records.add(path)
    checks = {
        'dependencies/FunctionTheory/TauCeti/Analysis/Complex/Conformal/Inverse/BoundaryCluster.lean': ['D. Cureton', '895c0a0', 'Apache-2.0'],
        'dependencies/FunctionTheory/FunctionTheory/RiemannSphere/Basic.lean': ['Geoffrey Irving', '753f7131cf96f4651294de4398368abf136c34de', 'Apache 2.0'],
        'dependencies/FunctionTheory/FunctionTheory/RiemannSphere/Coordinates.lean': ['Geoffrey Irving', '753f7131cf96f4651294de4398368abf136c34de', 'Apache 2.0'],
        'dependencies/FunctionTheory/FunctionTheory/NormalFamilies/FiniteChartConvergence.lean': ['Will (Ziang) Li', '0a6497b0cc9ed39a6a705bf013449635894b56d0', 'Apache-2.0'],
    }
    for rel, markers in checks.items():
        path = ROOT / rel
        text = path.read_text()
        assert all(marker in text for marker in markers), rel
        records.add(path)
    for target in re.findall(r'\]\(([^)]+)\)', (ROOT / 'THIRD_PARTY_NOTICES.md').read_text()):
        if not target.startswith(('http:', 'https:')):
            assert (ROOT / target).is_file(), target
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    report = {
        'result': 'passed', 'scope': 'Included source attribution and archive completeness',
        'licence_texts': {p.relative_to(ROOT).as_posix(): {'license': 'Apache-2.0', 'sha256': sha(p)} for p in licences},
        'attribution_files': {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(records)},
        'vendored_header_checks': groups,
        'separately_fetched_not_bundled': [
            {'name': p['name'], 'url': p['url'], 'revision': p['rev']}
            for p in manifest['packages'] if p['type'] == 'git'],
        'upstream_sources_refetched': False,
        'note': 'Checks retained licences, source headers, provenance records and links; not an independent legal review.'
    }
    (ROOT / 'verification/attribution.json').write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
    return report

if __name__ == '__main__':
    report = audit()
    print(json.dumps({'result': report['result'], 'licence_texts': len(report['licence_texts']),
                      'attribution_files': len(report['attribution_files']),
                      'vendored_headers': sum(g['files'] for g in report['vendored_header_checks'])}))
