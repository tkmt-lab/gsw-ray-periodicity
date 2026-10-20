"""Verify pinned source/import closure and distinguish reports from kernel stdout."""
import re
from packet_common import ROOT,PIN,THM_PIN,load,local,fingerprint,strip_lean,result

def main():
 a=load('receipt-manifest.json');assert a['formal_source_commit']==PIN and a['status']=='MIXED_FIXED_RECEIPTS_AND_RECEIVED_K3_PROOF'
 assert a['new_lean_proofs']==a['new_scientific_runs']==0 and a['new_lean_runs']==0
 assert a['D12_new_classification_included'] is False
 records={r['path']:r for r in a['receipts']}
 for r in records.values():fingerprint(r)
 lean=[r for r in records.values() if r['path'].endswith('.lean')];assert len(lean)==a['lean_sources']==193
 seen=set()
 def visit(module):
  name='formal/'+module.replace('.','/')+'.lean';assert name in records,('import closure',module)
  if name in seen:return
  seen.add(name);r=records[name];assert r['source_commit']==(THM_PIN if name.startswith('formal/Formal/Claude3') else a['K3_source_commit'] if name in a['K3_added_source_paths'] else PIN)
  text=strip_lean(local(name).read_text())
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),('unproved/extra axiom',name)
  for m in re.finditer(r'(?m)^import\s+([^\n]+)',text):
   for item in m[1].split():
    if item.startswith('Formal.'):visit(item)
    else:assert item.startswith(('Mathlib','Lean','Std','Batteries','Aesop','Qq','Plausible','ImportGraph','ProofWidgets')),item
 for root in a['roots']:visit('Formal.'+root)
 benchmarks={r['path'] for r in a['benchmark_sources']}
 assert seen=={r['path'] for r in lean}-benchmarks
 for name in benchmarks:
  text=strip_lean(local(name).read_text());assert not re.search(r'(?m)^import Formal',text) and len(re.findall(r'\bsorry\b',text))==1
 assert not (seen & benchmarks), 'benchmark became proof dependency'
 actual={p.relative_to(ROOT).as_posix() for p in (ROOT/'formal').rglob('*.lean')}
 assert actual==seen|benchmarks,'unexpected/new proof payload'
 assert not any('claude-d12' in p.relative_to(ROOT).as_posix().lower() for p in ROOT.rglob('*'))
 packages=load('formal/lake-manifest.json')['packages'];assert packages
 for p in packages:assert p['type']=='git' and re.fullmatch('[a-f0-9]{40}',p['rev'])
 assert local('formal/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
 for r in load('extra-receipts.json'):fingerprint(r)
 # New claims cite fixed reports; none is masqueraded as fresh kernel stdout.
 claims=load('claims.json')
 for c in claims['claims']:
  for r in c['lean']:
   if r['verification_kind']=='coordinator-reported-kernel-output':assert r['receipt']['path'].endswith('.md.original.log')
 theorem=load('theorem1a-manifest.json')
 assert theorem['status']=='PASS' and theorem['owner_statement_confirmed']
 assert theorem['source_commit']==THM_PIN and len(theorem['sources'])==53
 assert {r['path'] for r in theorem['sources']}=={n for n in records if n.startswith('formal/Formal/Claude3')}
 for r in [*theorem['sources'],*theorem['receipts']]:fingerprint(r)
 execution=load('evidence/theorem1a/lean-execution.json')
 assert execution['status']=='PASS' and all(r['exit_code']==0 and r['max_lean_processes']<=1 and r['min_free_percent']>=20 and not r['stopped'] for r in execution['commands'])
 from check_k3_received import check_k3
 check_k3(ROOT)
 result(lean_sources=len(actual),proof_sources=len(seen),benchmark_sources=len(benchmarks),received_files=len(records),extra_receipts=len(load('extra-receipts.json')),inherited_theorem1a_execution_receipt=True,received_K3_coordinator_receipt=True,scope='static receipts, not proof checking')
if __name__=='__main__':main()
