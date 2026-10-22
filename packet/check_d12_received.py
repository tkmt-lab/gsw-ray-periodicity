"""Static D12 Lean source/type/two-target receipt, statement-correspondence and article-edit checks; no Lean."""
from pathlib import Path
import hashlib,json,re
DECLS=['ClaudeChallengeD12.classification','ClaudeChallengeD12.main']
KERNELS=['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']
def check_v63(root):
    """Article 6.3 is exactly article 6.2 with the recorded D12 proof-scope edits."""
    root=Path(root)
    m=json.loads((root/'lines-v6.3-edit-map.json').read_text())
    old=(root/m['predecessor']).read_text();new=(root/m['target']).read_text()
    assert hashlib.sha256(old.encode()).hexdigest()==m['predecessor_sha256'] and hashlib.sha256(new.encode()).hexdigest()==m['target_sha256']
    text=old
    for e in m['edits']:
        assert text.count(e['before'])==1,('6.3 edit anchor',e['number'])
        text=text.replace(e['before'],e['after'])
    assert text==new,'unrecorded 6.2 to 6.3 edit'
    for env in ['definition','alignedtheorem','catalogcor','proposition','lemma','equation']:
        p=r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
        assert re.findall(p,new,re.S)==re.findall(p,old,re.S),'numbered mathematical block changed'
    for p in [r'\\\[.*?\\\]']:
        assert re.findall(p,new,re.S)==re.findall(p,old,re.S),'displayed mathematics changed'
    assert re.findall(r'\\claimid\{([^}]+)\}',new)==re.findall(r'\\claimid\{([^}]+)\}',old)
    assert not re.search(r'\b(?:R00[245]|Claude|Codex|coordinator|mailbox)\b',new),'internal process marker in article'
    assert 'is therefore not a third\nindependent derivation' in new or 'not a third\nindependent derivation' in new or 'not a third independent derivation' in ' '.join(new.split())
    assert 'Neither route\nis a Lean proof' not in new and 'No family-specific Lean proof of D12' not in new
    record=(root/'VERIFICATION-RECORD.md').read_text()
    for e in m['edits']:assert e['before'].rstrip() in record,('6.3 predecessor passage missing from record',e['number'])
    return len(m['edits'])
def check_d12_received(root):
    root=Path(root)
    from packet_common import strip_lean
    load=lambda name:json.loads((root/name).read_text())
    def fp(row):
        p=Path(row['path']);assert not p.is_absolute() and '..' not in p.parts
        raw=(root/p).read_bytes();assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],('D12 fingerprint',row['path'])
        return raw
    m=load('d12-manifest.json');claims=load('claims.json');by={c['id']:c for c in claims['claims']}
    records=[[r for r in by[key]['lean'] if r['declaration'].startswith('ClaudeChallengeD12.')] for key in ['thm:d12-classification','cor:catalog']]
    assert [[r['declaration'] for r in rows] for rows in records]==[[DECLS[0]],[DECLS[1]]],'missing D12 Lean declarations'
    assert by['thm:d12-classification']['status']=='lean-result-received'
    assert m['status']=='RECEIVED_REPORTED_PASS' and re.fullmatch('[a-f0-9]{40}',m['source_commit'])
    assert m['comparator_targets']==DECLS and m['recorded_kernels']==KERNELS
    assert m['classification_domain']=='natural r,s>=1' and not m['lean_derivation_independent_of_prose_routes']
    scope=claims['scope'];assert scope['d12_graph_classification_received'] and scope['d12_literal_ray_without_prose_bridge_received']
    assert not scope['d12_named_catalogue_correspondence_formalized'] and not scope['d12_lean_derivation_independent_of_prose_routes']
    assert scope['paper_to_specification_bridge']=='prose-not-formalized'
    assert not scope['human_peer_review'] and not scope['novelty_established']
    assert m['independent_reader_verdict']=='FAITHFUL WITH CAVEATS' and m['independent_statement_readers']==1
    assert m['new_lean_runs']==0 and not m['external_kernels_rerun'] and not m['OS_isolation'] and not m['owner_confirmation_procedure_used']
    assert len(m['sources'])==86 and len(m['added_sources'])==82 and m['new_proof_files']==81 and m['new_specifications']==1
    for row in m['sources']:
        text=strip_lean(fp(row).decode());assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
    for row in m['records']:fp(row)
    worker=fp(m['worker_report']).decode()
    assert all(x in worker for x in ['propext','Classical.choice','Quot.sound','classification','main'])
    stopped=fp(m['worker_stopped_comparator']).decode();assert 'Your solution is okay!' not in stopped
    raw=fp(m['raw_comparator']).decode()
    for k in KERNELS:assert k+' kernel accepts the solution' in raw
    assert 'Your solution is okay!' in raw and all(x in raw for x in DECLS)
    config=json.loads(fp(m['configuration']));assert config['theorem_names']==DECLS and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
    assert config['challenge_module']=='Formal.Claude7D12ComparatorChallenge' and config['solution_module']=='Formal.Claude7D12ComparatorSolution'
    def signature(text,name):
        start=re.search(r'(?m)^theorem '+re.escape(name)+r'\b',text).start()
        return text[start:text.index(':=',start)].rstrip()
    challenge=strip_lean(fp(m['challenge']).decode());solution=strip_lean((root/'formal/Formal/Claude7D12ComparatorSolution.lean').read_text())
    assert len(re.findall(r'\bsorry\b',challenge))==2
    for rows in records:
        for row in rows:
            assert row['source_commit']==m['source_commit'] and not row['fresh_lean_run']
            assert row['verification_kind']=='coordinator-reported-kernel-output' and row['axioms']==['propext','Classical.choice','Quot.sound']
            assert row['source_closure']==m['sources'] and row['receipt_scope']=='paranoid-comparator-two-targets'
            text=fp(row['source']).decode();fp(row['receipt']);name=row['declaration'].rsplit('.',1)[1]
            assert signature(text,name)==row['type_signature']==signature(challenge,name)
    def definition(text,name):
        start=re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|structure) '+re.escape(name)+r'\b',text);assert start,name
        stop=re.search(r'(?m)^(?:(?:noncomputable )?(?:def|abbrev|structure|theorem)|namespace|end|open|variable)\b',text[start.end():]);end=start.end()+stop.start() if stop else len(text)
        return ' '.join(text[start.start():end].split())
    assert definition(challenge,'PathExists')==definition(solution,'PathExists')
    assert len(m['definition_comparisons'])==22
    for row in m['definition_comparisons']:
        original=strip_lean((root/f'formal/Formal/{row["source"]}.lean').read_text())
        assert definition(challenge,row['definition'])==definition(original,row['definition'])
    mirror=json.loads(fp(m['mirror_result']));summary=mirror['summary']
    assert summary['cases']==240 and summary['full_cases']==144 and not summary['bad']
    assert not summary['classification_disagreements'] and summary['positives']==78 and summary['negatives']==162
    ci=(root/'CI-AXIOM-SPLIT.md').read_text()
    assert all(t in ci for t in ['tacticPeq','Axioms.lean','AxiomsD14.lean','D12','d12peq'])
    edits=check_v63(root)
    return dict(received_D12_declarations=2,comparator_targets=DECLS,source_closure=86,added_sources=82,
        article_6_3_edits=edits,lean_derivation_independent=False,new_lean_runs=0,scope=__doc__)
