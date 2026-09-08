"""Compile the H97 import DAG, optionally reusing completed numerical certificates.

Default: compile every new module from source. --reuse-numeric is for the final
campaign audit after all 58 numerical modules have already compiled separately.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
parser=argparse.ArgumentParser()
parser.add_argument('--reuse-numeric',action='store_true')
parser.add_argument('--reuse-compiled',action='store_true',help='Reuse artifacts already compiled from their current source during this campaign')
args=parser.parse_args()
root=Path('/Users/roychen/workspace/claudecode/automath')
project=root/'lean/proofenv'
out=root/'engine/out/astra_708_lean_h97'
paths={'.'.join(p.relative_to(project).with_suffix('').parts):p for p in (project/'Erdos708/H97').rglob('*.lean')}
order=[]; visited=set(); active=set()
def visit(m):
    if m in visited:return
    assert m not in active, 'Import cycle: '+m
    active.add(m)
    for dep in re.findall(r'^import\s+(\S+)',paths[m].read_text(),re.M):
        if dep in paths:visit(dep)
    active.remove(m);visited.add(m);order.append(m)
visit('Erdos708.H97.Cards')
for module in sorted(paths):visit(module)
records=[]
for module in order:
    p=paths[module]; stem=p.relative_to(project).with_suffix('')
    numerical=bool(re.fullmatch(r'Numeric\d+_\d+(Rows)?',p.stem))
    record={'module':module,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    if args.reuse_compiled and p.with_suffix('.olean').exists() and p.with_suffix('.olean').stat().st_mtime >= p.stat().st_mtime:
        record['status']='previously compiled current source'
        record['olean_sha256']=hashlib.sha256(p.with_suffix('.olean').read_bytes()).hexdigest()
    elif args.reuse_numeric and numerical and p.stem not in {'Numeric4_4','Numeric4_4Rows'}:
        assert p.with_suffix('.olean').exists(), 'Missing numerical certificate: '+module
        record['status']='previously compiled numerical certificate'
    else:
        print('START',module,flush=True)
        t=time.monotonic(); logpath=out/('final_'+p.stem+'.log')
        with logpath.open('w') as log:
            result=subprocess.run(['lake','env','lean','-o',str(stem)+'.olean',str(stem)+'.lean'],cwd=project,
                env=os.environ|{'LEAN_PATH':'.'},stdout=log,stderr=subprocess.STDOUT)
        record.update(status='compiled' if result.returncode==0 else 'FAILED',exit_code=result.returncode,
            seconds=round(time.monotonic()-t,3),log=logpath.name)
        print('DONE',module,record['status'],record['seconds'],flush=True)
        if result.returncode:
            print(logpath.read_text()[:12000],flush=True)
            records.append(record)
            (out/'build_manifest.json').write_text(json.dumps(records,indent=2)+'\n')
            raise SystemExit(result.returncode)
    records.append(record)
    (out/'build_manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print('PASS',len(records),'modules',flush=True)
