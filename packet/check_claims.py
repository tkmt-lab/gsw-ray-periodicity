"""Check claim scope and exact received declaration types, not proof elaboration."""
import re
from schema_validator import validate
from packet_common import ROOT,PIN,THM_PIN,FAMILIES,load,fingerprint,local,result

def main():
 from check_k3_received import check_k3
 check_k3(ROOT)
 from check_owner_statement import check_owner_statement
 check_owner_statement(ROOT)
 a=load('claims.json');schema=load('claims.schema.json');validate(a,schema,schema)
 assert a['source_commit']==PIN;fingerprint(a['paper'])
 scope=a['scope'];baseline=load('scope-contract.json')
 assert 'general_geometric_lean_proof' not in scope and scope['general_specification_lean_proof'] is True, 'ambiguous geometric Lean flag restored'
 assert scope==baseline,'scope promotion or unrecorded change'
 assert scope['catalogue_families']==FAMILIES
 tex=local(a['paper']['path']).read_text();display=re.findall(r'\\claimid\{([^}]+)\}',tex)
 ids=[c['id'] for c in a['claims']];assert len(ids)==len(set(ids))==30 and set(ids)==set(display) and len(display)==30
 labels=re.findall(r'\\label\{([^}]+)\}',tex);assert len(labels)==len(set(labels)) and set(ids)<=set(labels)
 by={c['id']:c for c in a['claims']};states=load('claim-status-contract.json');assert {i:c['status'] for i,c in by.items()}==states
 done=set();active=set()
 def visit(i):
  assert i in by and i not in active,('dependency',i)
  if i in done:return
  active.add(i)
  for j in by[i]['depends_on']:visit(j)
  active.remove(i);done.add(i)
 assert [r['declaration'] for r in by['thm:aligned']['lean']]==['ClaudeChallenge2.main','ClaudeChallenge2.State.main_statement','ClaudeChallenge2.main_residue'], 'missing Theorem 1a Lean declarations'
 count=0;formal_claims=0
 for c in a['claims']:
  visit(c['id']);assert c['id']==c['paper_label'] and c['human_review'] is False
  for e in c['evidence']+[c['review_history']]:fingerprint(e)
  review=local(c['review_history']['path']).read_text()
  assert len(c['review_history']['row_ids'])==(13 if c['id'] in ['cor:catalog','thm:k3-sufficient','prop:closed','ex:k3-formal','lem:k3-corners','lem:k3-hex-interior','lem:k3-tri-interior'] else 12)
  for id in c['review_history']['row_ids']:assert len(re.findall(r'^\| '+re.escape(id)+r' ',review,re.M))==1
  assert bool(c['lean'])==(c['status']=='lean-result-received' or c['id']=='cor:catalog')
  formal_claims+=bool(c['lean'])
  for r in c['lean']:
   count+=1;assert r['source_commit']==(THM_PIN if c['id']=='thm:aligned' else 'a77b2581d3a903ebb8668fc32c6ed087a1b1e8ec' if r['declaration'] in ['ClaudeChallengeK3.main','Claude4K3.k3_statement','Claude4K3.noThree'] else PIN)
   assert r['fresh_lean_run'] is (c['id']=='thm:aligned')
   fingerprint(r['source']);fingerprint(r['receipt']);s=local(r['source']['path']).read_text()
   short=r['declaration'].rsplit('.',1)[-1];m=re.search(r'(?m)^theorem '+re.escape(short)+r'\b',s);assert m
   assert s[m.start():s.index(':=',m.start())].rstrip()==r['type_signature'],r['declaration']
   text=local(r['receipt']['path']).read_text()
   if r['verification_kind'] in ['historical-kernel-output','fresh-kernel-output']:
    m=re.search(re.escape("'"+r['declaration']+"'")+r' depends on axioms: \[([^]]*)\]',text);assert m
    assert r['axioms']==[x.strip() for x in m[1].split(',') if x.strip()]
   else:
    assert r['verification_kind']=='coordinator-reported-kernel-output'
    assert r['axioms']==['propext','Classical.choice','Quot.sound']
    assert all(x in text for x in ['propext','Classical.choice','Quot.sound'])
 assert formal_claims==13 and count==25
 assert [r['declaration'] for r in by['thm:aligned']['lean']]==['ClaudeChallenge2.main','ClaudeChallenge2.State.main_statement','ClaudeChallenge2.main_residue'], 'missing Theorem 1a Lean declarations'
 for r in by['thm:aligned']['lean']:
  assert r['verification_kind']=='fresh-kernel-output' and r['source_closure']
  for source in r['source_closure']:fingerprint(source)
  assert r['source_closure']==load('theorem1a-manifest.json')['sources'], 'incomplete theorem source closure'
 assert by['thm:aligned']['status']=='lean-result-received'
 assert by['thm:aligned']['lean'] and not by['claim:oblique']['lean']
 result(claims=30,received_formal_claims=formal_claims,declaration_records=count,lean_runs_by_this_static_command=0,fresh_theorem_receipt_present=True)
if __name__=='__main__':main()
