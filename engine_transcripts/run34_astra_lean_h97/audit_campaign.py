"""Read-only campaign inventory and dependency/sorry audit; never runs git."""
from pathlib import Path
import re,json,hashlib
root=Path('/Users/roychen/workspace/claudecode/automath')
base=root/'lean/proofenv'
folder=base/'Erdos708/H97'
items=[]
for path in sorted(folder.rglob('*.lean')):
    source=path.read_text()
    items.append({'module':'.'.join(path.relative_to(base).with_suffix('').parts),
      'path':str(path.relative_to(root)), 'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'lines':len(source.splitlines()), 'bytes':path.stat().st_size,
      'olean_exists':path.with_suffix('.olean').exists(),
      'compiled_source_current':path.with_suffix('.olean').exists() and path.with_suffix('.olean').stat().st_mtime >= path.stat().st_mtime,
      'imports':re.findall(r'^import\s+(\S+)',source,re.M),
      'sorry_lines':[i for i,line in enumerate(source.splitlines(),1) if re.search(r'\bsorry\b',line)],
      'native_decide':bool(re.search(r'\bnative_decide\b',source)),
      'new_axiom':bool(re.search(r'^\s*axiom\s',source,re.M))})
assert not any(i['native_decide'] or i['new_axiom'] for i in items)
assert all(not i['sorry_lines'] or i['module']=='Erdos708.H97.Cards' for i in items)
assert all('Erdos708.H97.Cards' not in i['imports'] for i in items)
(root/'engine/out/astra_708_lean_h97/inventory.json').write_text(json.dumps(items,indent=2)+'\n')
print(len(items),'modules;',sum(i['olean_exists'] for i in items),'with compiled artifacts')
print('Uncompiled:',', '.join(i['module'] for i in items if not i['olean_exists']))
print('Only statement Cards contain sorry. No H97 Cards imports, new axioms, or native_decide.')

cards=(folder/'Cards.lean').read_text()
audit=(folder/'Audit.lean').read_text()
for name in ['lemma'+str(i) for i in range(1,10)]+['hinge97']:
    a=re.search(r'theorem '+name+r'\b(.*?) :=',cards,re.S).group(1)
    b=re.search(r'theorem card_'+name+r'\b(.*?) :=',audit,re.S).group(1)
    assert a==b, 'Changed statement card: '+name
print('All ten Audit statements exactly match the original statement cards.')
