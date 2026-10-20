"""Static C1 source/receipt/type scope checks; no Lean execution."""
from pathlib import Path
import json,re,hashlib
DECLS=['ClaudeChallengeC1.classification','ClaudeChallengeC1.main']

def check_c1(root):
 root=Path(root)
 from packet_common import strip_lean
 def load(n):return json.loads((root/n).read_text())
 def fp(r):
  p=Path(r['path']);assert not p.is_absolute() and '..' not in p.parts
  raw=(root/p).read_bytes();assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256'],('C1 fingerprint',r['path']);return raw
 m=load('c1-manifest.json');a=load('claims.json');by={c['id']:c for c in a['claims']}
 assert m['status']=='RECEIVED_REPORTED_PASS' and re.fullmatch('[0-9a-f]{40}',m['source_commit'])
 expected=[by['prop:closed']['lean'],[r for r in by['cor:catalog']['lean'] if r['declaration'].startswith('ClaudeChallengeC1.')]]
 assert [[r['declaration'] for r in rows] for rows in expected]==[[DECLS[0]],[DECLS[1]]],'missing C1 Lean declarations'
 assert by['prop:closed']['status']=='mixed-prose-and-formal-results'
 assert a['scope']['c1_graph_classification_received'] and a['scope']['c1_literal_ray_without_prose_bridge_received']
 assert not a['scope']['c1_ipr_formalized'] and not m['IPR_formalized']
 assert a['scope']['paper_to_specification_bridge']=='prose-not-formalized'
 assert all('statement_human_check' not in c for c in a['claims'] if c['id']!='thm:aligned')
 assert m['comparator_targets']==DECLS and m['independent_statement_readers']==1
 assert m['independent_reader_verdict']=='FAITHFUL WITH CAVEATS' and m['mirror_cases']==36
 assert not m['owner_confirmation_procedure_used'] and not m['new_lean_runs'] and not m['external_kernels_rerun'] and not m['OS_isolation']
 assert len(m['sources'])==23 and len(m['added_sources'])==21
 for r in m['sources']:
  text=strip_lean(fp(r).decode());assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),r['path']
 for r in m['records']:fp(r)
 detail=fp(m['worker_pre_comparator_report']).decode()
 assert all(x in detail for x in ['propext','Classical.choice','Quot.sound'])
 raw=fp(m['raw_comparator']).decode()
 for k in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:assert k+' kernel accepts the solution' in raw
 assert 'Your solution is okay!' in raw and 'ClaudeChallengeC1.classification, ClaudeChallengeC1.main' in raw
 config=json.loads(fp(m['configuration']));assert config['theorem_names']==DECLS and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
 for rows in expected:
  for r in rows:
   assert r['source_commit']==m['source_commit'] and not r['fresh_lean_run']
   assert r['verification_kind']=='coordinator-reported-kernel-output' and r['axioms']==['propext','Classical.choice','Quot.sound']
   assert r['source_closure']==m['sources'],'incomplete C1 source closure'
   text=fp(r['source']).decode();fp(r['receipt']);short=r['declaration'].rsplit('.',1)[1];start=re.search(r'(?m)^theorem '+short+r'\b',text).start()
   assert text[start:text.index(':=',start)].rstrip()==r['type_signature'],'C1 declaration type mismatch'
 challenge=strip_lean(fp(m['challenge']).decode());solution=strip_lean((root/'formal/Formal/Claude4C1ComparatorSolution.lean').read_text())
 assert len(re.findall(r'\bsorry\b',challenge))==2
 def signature(s,n):
  start=re.search(r'(?m)^theorem '+n+r'\b',s).start();return s[start:s.index(':=',start)].rstrip()
 for n in ['classification','main']:assert signature(challenge,n)==signature(solution,n)
 assert '(hr : 1 ≤ r)' in signature(challenge,'classification') and '(hs : 1 ≤ s)' in signature(challenge,'classification')
 def definition(s,n):
  x=re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|structure) '+re.escape(n)+r'\b',s);assert x,n
  stop=re.search(r'(?m)^(?:(?:noncomputable )?(?:def|abbrev|structure|theorem)|namespace|end|open|variable)\b',s[x.end():]);end=x.end()+stop.start() if stop else len(s)
  return ' '.join(s[x.start():end].split())
 assert definition(challenge,'PathExists')==definition(solution,'PathExists')
 assert len(m['definition_comparisons'])==22
 for r in m['definition_comparisons']:
  original=strip_lean((root/f'formal/Formal/{r["source"]}.lean').read_text());assert definition(challenge,r['definition'])==definition(original,r['definition'])
 mirror=json.loads(fp(m['mirror_result']));assert not mirror['bad'] and len(mirror['rows'])==36
 assert {(r['r'],r['s']) for r in mirror['rows']}=={(r,s) for r in range(1,7) for s in range(1,7)}
 assert all(r['V']==r['V_r004'] and r['E']==r['E_r004'] and r['deg_ok'] and r['deg5']==12 and r['boundary_only'] and r['path']==(r['s']==1) for r in mirror['rows'])
 return dict(received_C1_declarations=2,source_closure=23,added_sources=21,definition_comparisons=22,IPR_formalized=False,owner_confirmation_procedure_used=False,new_lean_runs=0,comparator_scope='both targets, same supplied proofs accepted by six kernels')
