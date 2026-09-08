from pathlib import Path
import json, subprocess, time, argparse
parser=argparse.ArgumentParser()
parser.add_argument("--min-L",type=int,default=4)
parser.add_argument("--reuse-rows",action="store_true")
parser.add_argument("--reuse-existing",action="store_true")
args=parser.parse_args()
root=Path('/Users/roychen/workspace/claudecode/automath')
out=root/'engine/out/astra_708_lean_h97'
project=root/'lean/proofenv'
for row in json.loads((out/'numeric_caps.json').read_text()):
    j,L=row['j'],row['L']
    if L<args.min_L: continue
    for suffix in ['Rows','']:
        name=f'Numeric{j}_{L}{suffix}'
        path=f'Erdos708/H97/Proofs/{name}'
        if args.reuse_existing and (project/(path+'.olean')).exists() and (project/(path+'.olean')).stat().st_mtime >= (project/(path+'.lean')).stat().st_mtime: continue
        if args.reuse_rows and suffix=='Rows' and (project/(path+'.olean')).exists(): continue
        print('START',name,flush=True)
        t=time.monotonic()
        with (out/(name+'.log')).open('w') as log:
            p=subprocess.run(['lake','env','lean','-o',path+'.olean',path+'.lean'],cwd=project,env=__import__('os').environ|{'LEAN_PATH':'.'},stdout=log,stderr=subprocess.STDOUT)
        print('DONE',name,'exit',p.returncode,'seconds',int(time.monotonic()-t),flush=True)
        if p.returncode:
            print((out/(name+'.log')).read_text()[:6000],flush=True)
            raise SystemExit(p.returncode)
