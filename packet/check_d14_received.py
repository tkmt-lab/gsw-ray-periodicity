"""Static D14 reception checker: main-only Comparator scope, auxiliaries separate."""
from pathlib import Path
import json,re,hashlib
MAIN='ClaudeChallengeD14.main';AUX='Claude5D14.d14_no_path'
def check_d14(root):
 root=Path(root)
 from packet_common import strip_lean
 def load(n):return json.loads((root/n).read_text())
 def fp(r):
  p=Path(r['path']);assert not p.is_absolute() and '..' not in p.parts
  raw=(root/p).read_bytes();assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256'],('D14 fingerprint',r['path']);return raw
 m=load('d14-manifest.json');a=load('claims.json');by={c['id']:c for c in a['claims']}
 expected=[[r for r in by[key]['lean'] if r['declaration'].startswith(('ClaudeChallengeD14.','Claude5D14.'))] for key in ['cor:catalog','prop:partial']]
 assert [[r['declaration'] for r in rows] for rows in expected]==[[MAIN],[AUX]],'missing D14 Lean declarations'
 assert m['status']=='RECEIVED_REPORTED_PASS' and re.fullmatch('[0-9a-f]{40}',m['source_commit'])
 assert m['comparator_targets']==[MAIN] and not m['auxiliary_lemmas_are_comparator_targets'],'D14 Comparator scope promoted'
 assert m['unproved_small_boundary_existence']==[[1,1]] and not m['standalone_iff_added']
 assert a['scope']['d14_literal_ray_without_prose_bridge_received'] and a['scope']['d14_absence_lemma_received']
 assert a['scope']['d14_comparator_targets_main_only'] and not a['scope']['d14_small_boundary_existence_formalized']
 assert a['scope']['paper_to_specification_bridge']=='prose-not-formalized'
 assert m['independent_statement_readers']==1 and m['independent_reader_verdict']=='FAITHFUL WITH CAVEATS' and m['mirror_cases']==81
 assert not m['owner_confirmation_procedure_used'] and not m['new_lean_runs'] and not m['external_kernels_rerun'] and not m['OS_isolation']
 assert all('statement_human_check' not in c for c in a['claims'] if c['id']!='thm:aligned')
 assert len(m['sources'])==37 and len(m['added_sources'])==33
 for row in m['sources']:
  text=strip_lean(fp(row).decode());assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
 for row in m['records']:fp(row)
 detail=fp(m['worker_pre_comparator_report']).decode();summary=fp(m['coordinator_build_and_axiom_report']).decode()
 assert all(x in detail for x in ['propext','Classical.choice','Quot.sound',AUX,'pe_R1','pe_S1'])
 assert MAIN in summary and AUX in summary and '標準の3つ' in summary
 raw=fp(m['raw_comparator']).decode()
 for kernel in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:assert kernel+' kernel accepts the solution' in raw
 assert 'Your solution is okay!' in raw and MAIN in raw
 config=json.loads(fp(m['configuration']));assert config['theorem_names']==[MAIN] and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
 def signature(s,n):
  start=re.search(r'(?m)^theorem '+re.escape(n)+r'\b',s).start();return s[start:s.index(':=',start)].rstrip()
 def record(row):
  assert row['source_commit']==m['source_commit'] and not row['fresh_lean_run']
  assert row['verification_kind']=='coordinator-reported-kernel-output' and row['axioms']==['propext','Classical.choice','Quot.sound']
  assert row['source_closure']==m['sources'],'incomplete D14 closure'
  text=fp(row['source']).decode();fp(row['receipt']);assert signature(text,row['declaration'].rsplit('.',1)[1])==row['type_signature']
  expected_scope='paranoid-comparator-main-only' if row['declaration']==MAIN else 'coordinator-worker-build-and-axiom-report-only'
  assert row['receipt_scope']==expected_scope,'D14 Comparator scope promoted'
 for rows in expected:
  for row in rows:record(row)
 assert [row['declaration'] for row in m['auxiliary_records']]==[AUX,'Claude5D14.pe_R1','Claude5D14.pe_S1']
 for row in m['auxiliary_records']:record(row)
 challenge=strip_lean(fp(m['challenge']).decode());solution=strip_lean((root/'formal/Formal/Claude5D14ComparatorSolution.lean').read_text())
 assert len(re.findall(r'\bsorry\b',challenge))==1 and signature(challenge,'main')==signature(solution,'main')
 assert not re.search(r'(?m)^theorem classification\b',challenge)
 def definition(s,n):
  start=re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|structure) '+re.escape(n)+r'\b',s);assert start,n
  stop=re.search(r'(?m)^(?:(?:noncomputable )?(?:def|abbrev|structure|theorem)|namespace|end|open|variable)\b',s[start.end():]);end=start.end()+stop.start() if stop else len(s)
  return ' '.join(s[start.start():end].split())
 assert definition(challenge,'PathExists')==definition(solution,'PathExists')
 assert len(m['definition_comparisons'])==22
 for row in m['definition_comparisons']:
  original=strip_lean((root/f'formal/Formal/{row["source"]}.lean').read_text());assert definition(challenge,row['definition'])==definition(original,row['definition'])
 mirror=json.loads(fp(m['mirror_result']));assert mirror['summary']['bad']==0 and len(mirror['rows'])==81
 assert {(r['r'],r['s']) for r in mirror['rows']}=={(r,s) for r in range(1,10) for s in range(1,10)}
 assert all(r['V']==r['V_r004'] and r['E']==r['E_r004'] and r['deg5']==12 and not r['other_deg'] and r['boundary_only'] and r['iso_r004'] and r['charts_injective'] and r['tri_edges_eq_adj'] and r['path']==(r['r']==1 or r['s']==1) and r['ok'] for r in mirror['rows'])
 return dict(received_D14_main=1,auxiliary_Lean_records=3,comparator_targets=[MAIN],claim_links=2,source_closure=37,added_sources=33,new_lean_runs=0,scope='Same supplied main accepted by six kernels; auxiliary lemmas separately reported, no Comparator scope promotion.')
