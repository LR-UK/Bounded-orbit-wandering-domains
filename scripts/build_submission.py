"""Stage local Lean builds with at most four compiler processes.

This is only resource scheduling. scripts/verify_submission.py follows it with
Lake's ordinary full target and dependency-hash validation. Cached-file hints
here never substitute for that final check.
"""
from pathlib import Path
import importlib.util, re, subprocess, os, concurrent.futures, json, shutil
R=Path(__file__).resolve().parents[1]
B=[R,*(R/'dependencies'/n for n in ('FunctionTheory','ComplexDynamics','ComplexApproximation','EremenkosConjecture')),R/'dependencies/EremenkosConjecture/vendor/schoenflies']
spec=importlib.util.spec_from_file_location('v',R/'dependencies/FunctionTheory/scripts/verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
SKIP={'Mathlib','Batteries','Aesop','Qq','ProofWidgets','LeanSearchClient','ImportGraph','Plausible','Init','Lean','Std','Lake'}
graph={}; locations={}
def visit(m):
    if m in graph or m.split('.')[0] in SKIP: return
    rel=Path(*m.split('.')).with_suffix('.lean')
    b=next((b for b in B if (b/rel).is_file()),None)
    if b is None: raise RuntimeError(m)
    code=v.without_lean_comments((b/rel).read_text())
    ds=[x for l in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',code,re.M) for x in l.split() if x.split('.')[0] not in SKIP]
    graph[m]=set(ds);locations[m]=b
    for d in ds: visit(d)
for m in ('Solution','Challenge','BoundedWanderingDomains','CoveringSolution'):visit(m)
def cached(m):
    b=locations[m]/'.lake/build/lib/lean'/Path(*m.split('.'))
    return b.with_suffix('.olean').is_file() and b.with_suffix('.trace').is_file()
done={m for m in graph if cached(m)}
print(json.dumps({'total_local_modules':len(graph),'already_compiled':len(done),'remaining':len(graph)-len(done)}),flush=True)
env=dict(os.environ,LEAN_NUM_THREADS='2')
lake=shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
count=0
out=R/'verification/limited-build';out.mkdir(exist_ok=True)
def build(m):
    with (out/(m+'.log')).open('w') as f:
        p=subprocess.run([lake,'build','+'+m],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
    return m,p.returncode
while len(done)<len(graph):
    ready=sorted(m for m,ds in graph.items() if m not in done and ds<=done)
    if not ready:raise RuntimeError('No ready modules')
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for m,code in pool.map(build,ready):
            count+=1
            print(f'{count}: {m}: exit {code}',flush=True)
            if code:raise SystemExit(code)
            done.add(m)
print('All local modules compiled',flush=True)
