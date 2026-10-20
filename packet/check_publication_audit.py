"""Current release-state/provenance-scope regressions; no Lean execution or publication."""
from pathlib import Path
import hashlib,json,re

def check_publication_audit(root):
    root=Path(root)
    def load(n):return json.loads((root/n).read_text())
    def fp(r):
        relative=Path(r['path']);assert not relative.is_absolute() and '..' not in relative.parts
        raw=(root/relative).read_bytes();assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256'],('audit fingerprint',str(relative));return raw
    from publication_privacy import check_scanner_source
    check_scanner_source(root)
    metadata=load('release-metadata.json');a3=metadata['paper_version']=='8.1';version='1.0.4' if a3 else '1.3.1'
    assert metadata['packet_version']==version
    provenance=load('PROVENANCE.json');authorization=load('publication-authorization.json')
    assert provenance['publication_on_hold'] is False,'publication hold restored'
    assert provenance['publication_status']=='owner-authorized-release' and not provenance['uploaded']
    assert authorization['status']=='owner-authorized-release' and authorization['authorized'] is True
    assert authorization['authorized_on']=='2026-10-20' and authorization['recorded_by']=='coordinator'
    assert authorization['decision_source_commit']=='38c95fa05863df44ee1e048344ae9944684fa76d'
    assert authorization['decision_full_file_sha256']=='dd9b8d5b5c75ab30ab9e910b0b5e26a76bfea56c6e22d228a7bfd8ce05cc7bf7'
    assert not authorization['publication_performed_by_research_team'] and not authorization['proof_peer_review'] and not authorization['novelty_review']
    assert authorization['publication_operation_role']=='coordinator'
    current=[root/n for n in ['AGENTS.md','README.md','CITING.md','FORMALIZATION.md']]
    tex=root/('paper-A3-v8.1-en.tex' if a3 else 'paper-lines-v4.7-en.tex');current.append(tex)
    for p in current:
        assert not re.search(r'publication\s+(?:(?:is|remains)\s+)?on\s+hold',p.read_text(),re.I),'publication hold restored in '+p.name
    citing=(root/'CITING.md').read_text()
    assert 'version '+metadata['paper_version']+'.' in citing,'citation article version stale'
    if not a3:assert 'All Lean and article bytes and proof/review scopes remain unchanged.' not in citing,'unqualified citation byte claim'
    if a3:
        formal=(root/'FORMALIZATION.md').read_text()
        assert 'are supplied byte-identically' not in formal,'redacted receipt byte-identity overclaim restored'
        assert 'privacy-redacted public derivatives' in formal and 'REDACTIONS.json' in formal
        assert 'historical source inventory is byte-identical' in ' '.join(re.sub(r'\[([^\]]+)\]\([^)]+\)',r'\1',formal).split())
        supplement=(root/'SUPPLEMENTARY-EVIDENCE.md').read_text()
        assert 'English v8.1' in supplement and '1.0.4' in supplement
        assert 'authorship and release metadata remain unassigned' not in supplement
    else:
        formal=(root/'FORMALIZATION.md').read_text()
        assert 'Where to read the challenge and the proof' in formal, 'challenge navigation missing'
        assert 'evidence/theorem1a/ComparatorChallenge.lean.original.log' in formal
        assert 'statement/Challenge2.lean' in formal and 'statement/ChallengeK3.lean' in formal
        article=(root/'paper-lines-v4.7-en.tex').read_text()
        assert 'contact details are supplied separately' not in article, 'separate artifact claim restored'
        assert 'intentionally omitted' in article and 'lake exe cache get' in article
        claims=load('claims.json');scope=claims['scope'];contract=load('scope-contract.json')
        assert 'general_geometric_lean_proof' not in scope and 'general_geometric_lean_proof' not in contract,'ambiguous geometric Lean flag restored'
        assert scope['general_specification_lean_proof'] is True and contract==scope
        assert scope['paper_to_specification_bridge']=='prose-not-formalized'
        assert not scope['human_peer_review'] and not scope['novelty_established']
        schema=load('claims.schema.json')['properties']['scope']
        assert schema['additionalProperties'] is False and 'general_specification_lean_proof' in schema['required']
        assert 'general_geometric_lean_proof' not in schema['properties']
    preservation=load('source-preservation.json')
    assert preservation['status']=='PASS' and preservation['inherited_lean_source_bytes_unchanged']
    assert preservation['source_count']==(165 if a3 else 193)
    assert preservation['new_lean_runs']==0 and not preservation['external_kernels_rerun']
    assert provenance['new_lean_runs']==0
    assert len(preservation['sources'])==preservation['source_count']
    for r in preservation['sources']:fp(r)
    for r in preservation['inherited_receipts']:fp(r)
    spec=root/'formal/Formal/ClaudeChallengeSpec.lean'
    assert hashlib.sha256(spec.read_bytes()).hexdigest()=='d14259d1c70dcae93c2e2e7f9a91a010304bf2a5b8335472177981ae354ff3af'
    stripped=re.sub(r'/\-!.*?\-/','',spec.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',stripped)
    note=preservation['stale_module_note']
    for name in ['FORMALIZATION.md','CHANGELOG.md','P006-corrections.md']:
        assert note in (root/name).read_text(),'stale module note missing from '+name
    from check_k3_received import check_k3
    check_k3(root)
    return dict(current_publication_state='owner-authorized-release',publication_performed_here=False,
                privacy_derivatives_distinguished=True,inherited_lean_source_bytes_preserved=True,
                new_lean_runs=0,historical_build_receipts_inherited=True,specification_vs_prose_scope_explicit=not a3)
