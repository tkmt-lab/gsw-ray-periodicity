"""Static E10 source/type/two-target receipt and boundary-scope checks; no Lean."""
from pathlib import Path
import hashlib,json,re
DECLS=['ClaudeChallengeE10.classification','ClaudeChallengeE10.main']
def check_e10(root):
    root=Path(root)
    from packet_common import strip_lean
    load=lambda name:json.loads((root/name).read_text())
    def fp(row):
        p=Path(row['path']);assert not p.is_absolute() and '..' not in p.parts
        raw=(root/p).read_bytes();assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],('E10 fingerprint',row['path'])
        return raw
    m=load('e10-manifest.json');claims=load('claims.json');by={c['id']:c for c in claims['claims']}
    records=[[r for r in by[key]['lean'] if r['declaration'].startswith('ClaudeChallengeE10.')] for key in ['prop:closed','cor:catalog']]
    assert [[r['declaration'] for r in rows] for rows in records]==[[DECLS[0]],[DECLS[1]]],'missing E10 Lean declarations'
    assert m['status']=='RECEIVED_REPORTED_PASS' and re.fullmatch('[a-f0-9]{40}',m['source_commit'])
    assert m['comparator_targets']==DECLS and not m['r1_closed_classification_proved'],'E10 r1 scope promoted'
    assert m['classification_domain']=='natural p,s>=1, r>=2'
    scope=claims['scope'];assert scope['e10_graph_classification_received'] and scope['e10_literal_ray_without_prose_bridge_received']
    assert scope['e10_r1_ray_uses_formal_general_theorem'] and scope['e10_r1_geometric_model_hypotheses_formalized']
    assert not scope['e10_r1_closed_classification_formalized'] and not scope['e10_named_catalogue_correspondence_formalized'],'E10 r1 scope promoted'
    assert scope['paper_to_specification_bridge']=='prose-not-formalized'
    assert not scope['human_peer_review'] and not scope['novelty_established']
    assert m['independent_reader_verdict']=='FAITHFUL WITH CAVEATS' and m['independent_statement_readers']==1
    assert m['mirror_cases']==702 and m['reader_cases']==143 and m['reader_classification_cases']==103
    assert m['new_lean_runs']==0 and not m['external_kernels_rerun'] and not m['OS_isolation'] and not m['owner_confirmation_procedure_used']
    assert len(m['sources'])==166 and len(m['added_sources'])==111
    for row in m['sources']:
        text=strip_lean(fp(row).decode());assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
    for row in m['records']:fp(row)
    worker=fp(m['worker_pre_comparator_report']).decode();summary=fp(m['coordinator_build_and_axiom_report']).decode()
    assert all(x in worker for x in ['propext','Classical.choice','Quot.sound'])
    assert all(x in summary for x in DECLS) and '標準の3つ' in summary
    raw=fp(m['raw_comparator']).decode()
    for k in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:assert k+' kernel accepts the solution' in raw
    assert 'Your solution is okay!' in raw and all(x in raw for x in DECLS)
    config=json.loads(fp(m['configuration']));assert config['theorem_names']==DECLS and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
    def signature(text,name):
        start=re.search(r'(?m)^theorem '+re.escape(name)+r'\b',text).start()
        return text[start:text.index(':=',start)].rstrip()
    challenge=strip_lean(fp(m['challenge']).decode());solution=strip_lean((root/'formal/Formal/Claude5E10ComparatorSolution.lean').read_text())
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
    assert len(m['definition_comparisons'])==23
    for row in m['definition_comparisons']:
        original=strip_lean((root/f'formal/Formal/{row["source"]}.lean').read_text())
        assert definition(challenge,row['definition'])==definition(original,row['definition'])
    valid=strip_lean((root/'formal/Formal/Claude5E10SigAdj.lean').read_text())
    t1a=strip_lean((root/'formal/Formal/Claude5E10T1a.lean').read_text())
    assert 'theorem valid_e10S' in valid and 'ClaudeChallenge2.Valid (e10S Q) t ∧ ClaudeChallenge2.TrianglesInCharts (e10S Q) t' in valid
    assert 'ClaudeChallenge2.State.main_statement (e10S Q)' in t1a and 'valid_e10S' in t1a
    mirror=json.loads(fp(m['mirror_result']));summary=mirror['summary'];rows=mirror['rows']
    assert summary['bad']==0 and len(rows)==702 and summary['r_ge_2_cases']==620 and summary['r1_cases']==82
    assert not summary['r_ge_2_disagreements'] and len(summary['r1_path_vs_formula_disagreements'])==3
    for row in rows:
        p,r,s=row['p'],row['r'],row['s'];area=12*r*r+2*s*s+12*r*s+24*p*r+12*p*s
        assert row['V']==row['V_r004']==area//2+2 and row['E']==row['E_r004']==3*row['V']-6
        assert row['area2']==row['triangles']==area and row['deg5']==12 and not row['other_deg']
        assert all(row[k] for k in ['deg_seq_eq','tri_edges_eq_adj','boundary_only','charts_injective','same_as_aligned_surface','iso_r004','iso_r004_original_e10','ok'])
        if r>=2:assert row['path']==row['paper_cond']
    ci=(root/'CI-AXIOM-SPLIT.md').read_text()
    assert all(t in ci for t in ['tacticPeq','Axioms.lean','AxiomsD14.lean','O2','D14','E10'])
    return dict(received_E10_declarations=2,comparator_targets=DECLS,source_closure=166,added_sources=111,
        r1_classification=False,r1_ray_formal=True,new_lean_runs=0,scope=__doc__)
