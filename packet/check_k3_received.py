"""Check pinned K3 proof records and statement scope, without executing Lean."""
from pathlib import Path
import json,re,hashlib
K3_PIN='a77b2581d3a903ebb8668fc32c6ed087a1b1e8ec'
NEW_DECLS=['ClaudeChallengeK3.main','Claude4K3.k3_statement','Claude4K3.noThree']

def check_k3(root):
 root=Path(root)
 from packet_common import strip_lean
 def load(n):return json.loads((root/n).read_text())
 def fp(r):
  p=Path(r['path']);assert not p.is_absolute() and '..' not in p.parts
  raw=(root/p).read_bytes();assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256'],('K3 fingerprint',r['path']);return raw
 m=load('k3-manifest.json');a=load('claims.json');by={r['id']:r for r in a['claims']}
 assert m['status']=='RECEIVED_REPORTED_PASS' and m['source_commit']==K3_PIN
 assert [r['declaration'] for r in by['cor:catalog']['lean']]==NEW_DECLS[:1],'missing K3 Lean declarations'
 assert [r['declaration'] for r in by['thm:k3-sufficient']['lean']]==['Claude2K3.k3_sufficient',*NEW_DECLS[1:]],'missing K3 Lean declarations'
 assert by['cor:catalog']['status']=='mixed-prose-and-formal-results'
 assert all('statement_human_check' not in c for c in a['claims'] if c['id']!='thm:aligned'),'unsupported owner-confirmation field outside historical Theorem 1a record'
 scope=a['scope'];assert scope['k3_graph_necessity_received'] and scope['k3_literal_ray_without_prose_bridge_received']
 assert scope['paper_to_specification_bridge']=='prose-not-formalized' and not scope['k3_global_degree_classification']
 assert not scope['human_peer_review'] and not scope['novelty_established']
 assert m['correspondence_method']==['prior-specification','independent-ai-reader-of-v1-with-boundary-fix-before-proof','finite-computational-comparison']
 assert m['independent_statement_readers']==1 and not m['owner_confirmation_procedure_used']
 assert not m['new_lean_runs'] and not m['external_kernels_rerun'] and not m['OS_isolation']
 assert m['comparator_target']=='ClaudeChallengeK3.main only' and not m['classification_or_noThree_separate_comparator_targets']
 sources=m['sources'];assert len(sources)==36 and len(m['added_sources'])==25
 for r in sources:
  text=strip_lean(fp(r).decode());assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),r['path']
 for r in m['records']:fp(r)
 raw=fp(m['raw_comparator']).decode()
 for k in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:assert k+' kernel accepts the solution' in raw
 assert 'Your solution is okay!' in raw
 for n in NEW_DECLS[1:]:assert "'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in raw
 config=json.loads(fp(m['configuration']));assert config['theorem_names']==NEW_DECLS[:1]
 assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
 received=[by['cor:catalog']['lean'][0],*by['thm:k3-sufficient']['lean'][1:]]
 for r in received:
  text=fp(r['source']).decode();fp(r['receipt'])
  assert r['source_commit']==K3_PIN and r['verification_kind']=='coordinator-reported-kernel-output' and r['fresh_lean_run'] is False
  assert r['axioms']==['propext','Classical.choice','Quot.sound']
  assert r['source_closure']==sources,'incomplete K3 source closure'
  for q in r['source_closure']:fp(q)
  short=r['declaration'].rsplit('.',1)[1];start=re.search(r'(?m)^theorem '+re.escape(short)+r'\b',text).start()
  assert text[start:text.index(':=',start)].rstrip()==r['type_signature'],'K3 exact declaration type mismatch'
 challenge=strip_lean(fp(m['challenge']).decode());solution=strip_lean((root/'formal/Formal/Claude4K3ComparatorSolution.lean').read_text())
 def signature(s):
  start=re.search(r'(?m)^theorem main\b',s).start();return s[start:s.index(':=',start)].rstrip()
 assert signature(challenge)==signature(solution)
 assert '(hr : 1 ≤ r₀)' in signature(challenge) and '(hs : 1 ≤ s₀)' in signature(challenge)
 def definition(s,n):
  x=re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|structure) '+re.escape(n)+r'\b',s);assert x,n
  stop=re.search(r'(?m)^(?:(?:noncomputable )?(?:def|abbrev|structure|theorem)|namespace|end|open|variable)\b',s[x.end():]);end=x.end()+stop.start() if stop else len(s)
  return ' '.join(s[x.start():end].split())
 assert definition(challenge,'PathExists')==definition(solution,'PathExists')
 assert len(m['definition_comparisons'])==22
 for r in m['definition_comparisons']:
  original=strip_lean((root/f'formal/Formal/{r["source"]}.lean').read_text())
  assert definition(challenge,r['definition'])==definition(original,r['definition'])
 assert m['mirror_cases_K3']==66 and m['mirror_positive_boundary_scope']=='Interior r,s>=2 only; parameter-one finite checks are reported separately by the independent reader (68 total known instances).'
 assert 'sufficiency only' not in by['thm:k3-sufficient']['statement_plain'].lower()
 return dict(received_K3_declarations=3,source_closure=36,added_sources=25,prior_definition_comparisons=22,main_includes_parameter_one=True,no_general_prose_bridge_for_K3=True,general_bridge='prose-not-formalized',owner_confirmation_procedure_used=False,Lean_executed_here=False,comparison_scope='six kernels, same main proof only')
