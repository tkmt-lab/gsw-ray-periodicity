"""Static O2 source/receipt/type scope checks; no Lean execution."""
from pathlib import Path
import json,re,hashlib
DECLS=['ClaudeChallengeO2.classification','ClaudeChallengeO2.main']

def check_o2(root):
 root=Path(root)
 from packet_common import strip_lean
 def load(n):return json.loads((root/n).read_text())
 def fp(r):
  p=Path(r['path']);assert not p.is_absolute() and '..' not in p.parts
  raw=(root/p).read_bytes();assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256'],('O2 fingerprint',r['path']);return raw
 m=load('o2-manifest.json');a=load('claims.json');by={c['id']:c for c in a['claims']}
 assert m['status']=='RECEIVED_REPORTED_PASS' and re.fullmatch('[0-9a-f]{40}',m['source_commit'])
 expected=[[r for r in by[key]['lean'] if r['declaration'].startswith('ClaudeChallengeO2.')] for key in ['prop:closed','cor:catalog','prop:partial']]
 assert [[r['declaration'] for r in rows] for rows in expected]==[[DECLS[0]],[DECLS[1]],[DECLS[0]]],'missing O2 Lean declarations'
 assert by['prop:closed']['status']=='mixed-prose-and-formal-results'
 assert a['scope']['o2_graph_classification_received'] and a['scope']['o2_literal_ray_without_prose_bridge_received']
 assert not a['scope']['o2_ipr_formalized'] and not m['IPR_formalized']
 assert a['scope']['paper_to_specification_bridge']=='prose-not-formalized'
 assert all('statement_human_check' not in c for c in a['claims'] if c['id']!='thm:aligned')
 assert m['comparator_targets']==DECLS and m['independent_statement_readers']==1
 assert m['independent_reader_verdict']=='FAITHFUL WITH CAVEATS' and m['mirror_cases']==80
 assert not m['owner_confirmation_procedure_used'] and not m['new_lean_runs'] and not m['external_kernels_rerun'] and not m['OS_isolation']
 assert len(m['sources'])==54 and len(m['added_sources'])==50
 for r in m['sources']:
  text=strip_lean(fp(r).decode());assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),r['path']
 for r in m['records']:fp(r)
 detail=fp(m['worker_pre_comparator_report']).decode()
 assert all(x in detail for x in ['propext','Classical.choice','Quot.sound'])
 raw=fp(m['raw_comparator']).decode()
 for k in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:assert k+' kernel accepts the solution' in raw
 assert 'Your solution is okay!' in raw and 'ClaudeChallengeO2.classification, ClaudeChallengeO2.main' in raw
 config=json.loads(fp(m['configuration']));assert config['theorem_names']==DECLS and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
 for rows in expected:
  for r in rows:
   assert r['source_commit']==m['source_commit'] and not r['fresh_lean_run']
   assert r['verification_kind']=='coordinator-reported-kernel-output' and r['axioms']==['propext','Classical.choice','Quot.sound']
   assert r['source_closure']==m['sources'],'incomplete O2 source closure'
   text=fp(r['source']).decode();fp(r['receipt']);short=r['declaration'].rsplit('.',1)[1];start=re.search(r'(?m)^theorem '+short+r'\b',text).start()
   assert text[start:text.index(':=',start)].rstrip()==r['type_signature'],'O2 declaration type mismatch'
 challenge=strip_lean(fp(m['challenge']).decode());solution=strip_lean((root/'formal/Formal/Claude5O2ComparatorSolution.lean').read_text())
 assert len(re.findall(r'\bsorry\b',challenge))==2
 def signature(s,n):
  start=re.search(r'(?m)^theorem '+n+r'\b',s).start();return s[start:s.index(':=',start)].rstrip()
 for n in ['classification','main']:assert signature(challenge,n)==signature(solution,n)
 assert '(ht : 2 ≤ t)' in signature(challenge,'classification') and '(hd : 2 ≤ d)' in signature(challenge,'classification')
 def definition(s,n):
  x=re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|structure) '+re.escape(n)+r'\b',s);assert x,n
  stop=re.search(r'(?m)^(?:(?:noncomputable )?(?:def|abbrev|structure|theorem)|namespace|end|open|variable)\b',s[x.end():]);end=x.end()+stop.start() if stop else len(s)
  return ' '.join(s[x.start():end].split())
 assert definition(challenge,'PathExists')==definition(solution,'PathExists')
 assert len(m['definition_comparisons'])==22
 for r in m['definition_comparisons']:
  original=strip_lean((root/f'formal/Formal/{r["source"]}.lean').read_text());assert definition(challenge,r['definition'])==definition(original,r['definition'])
 mirror=json.loads(fp(m['mirror_result']));assert mirror['summary']['bad']==0 and len(mirror['rows'])==80
 assert {(r['t'],r['d']) for r in mirror['rows']}=={(t,d) for t in range(1,9) for d in range(1,11)}
 assert all(r['V']==r['V_r004'] and r['E']==r['E_r004'] and r['deg5']==12 and not r['other_deg'] and r['boundary_only'] and r['iso_r004'] and r['charts_injective'] and r['tri_edges_eq_adj'] and r['path']==(r['t']==1 or r['d']==1) and r['ok'] for r in mirror['rows'])
 assert m['unproved_small_boundary_existence']==[[1,1],[1,2],[2,1]]
 assert by['prop:partial']['status']=='mixed-prose-and-formal-results'
 return dict(received_O2_declarations=2,claim_links=3,source_closure=54,added_sources=50,definition_comparisons=22,IPR_formalized=False,unproved_small_boundary_existence=m['unproved_small_boundary_existence'],owner_confirmation_procedure_used=False,new_lean_runs=0,comparator_scope='both targets, same supplied proofs accepted by six kernels')
