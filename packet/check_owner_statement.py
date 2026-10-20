"""Check recorded owner statement meaning and its exact source correspondence, not a proof."""
import difflib
import hashlib
import json
import re
from pathlib import Path

CHALLENGE='d2800a5c4560ce94b5f94faada54003063bcb3e38b599d32e035d23ab264a66d'
GUIDE='da5e185c56a54253c3ea9f59c4ee724f2070141ce442f992adad635a4f49a48f'
CURRENT='cecc4c3026271e570a154e287da26ee56eacaeb13e6621599be598131a578440'
DECISION_COMMIT='a674675a14e6e0a5a33c7e6fa198542d6fe76c88'
DECISION_FILE='dd9b8d5b5c75ab30ab9e910b0b5e26a76bfea56c6e22d228a7bfd8ce05cc7bf7'


def check_owner_statement(root):
    root=Path(root)
    def load(n):return json.loads((root/n).read_text())
    def fingerprint(row):
        relative=Path(row['path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        p=root/relative;raw=p.read_bytes()
        assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'owner statement fingerprint mismatch: '+str(relative)
        return raw
    a=load('claims.json');by={r['id']:r for r in a['claims']}
    assert a['scope']['owner_statement_confirmation'] is True,'owner statement confirmation reverted to pending'
    assert all(r['human_review'] is False for r in a['claims'])
    assert [r['id'] for r in a['claims'] if 'statement_human_check' in r]==['thm:aligned'],'owner confirmation applied outside Theorem 1a'
    h=by['thm:aligned']['statement_human_check'];receipt=load('owner-statement-confirmation.json')
    for row in [h,receipt]:
        assert row['status']=='confirmed','owner statement confirmation reverted to pending'
        assert row['checked_on']=='2026-10-20' and row['reviewer']=='owner'
        assert row['basis']=='owner-self-report-recorded-by-coordinator'
        assert row['scope']=='challenge-statement-meaning-only' and row['declaration']=='ClaudeChallenge2.main'
        assert row['proof_peer_review'] is row['prose_bridge_review'] is row['novelty_review'] is False
    assert receipt['reported_time']=='about 09:44 JST' and receipt['recorded_by']=='coordinator'
    assert receipt['challenge_version']==2 and receipt['guide_addendum_included']
    assert not receipt['K3_statement_check'] and not receipt['publication_approval_recorded_by_this_receipt']
    assert receipt['decision_source_commit']==DECISION_COMMIT and receipt['decision_full_file_sha256']==DECISION_FILE
    assert receipt['decision_source_identifier']=='docs/DECISIONS.md'
    assert h['challenge']==receipt['challenge'] and h['guide']==receipt['guide'] and h['comparison']==receipt['comparison']
    assert h['decision_extract']==receipt['decision_extract']
    assert h['receipt']['path']=='owner-statement-confirmation.json';fingerprint(h['receipt'])
    challenge=fingerprint(receipt['challenge']);guide=fingerprint(receipt['guide']);extract=fingerprint(receipt['decision_extract'])
    assert receipt['challenge']['sha256']==CHALLENGE and receipt['guide']['sha256']==GUIDE,'owner source pin changed'
    assert len(extract.decode().splitlines())==1
    assert all(x in extract.decode() for x in ['2026-10-20','09:44','Challenge2.lean','確認しました。問題ありません','証明の査読ではない'])
    assert '追記' in guide.decode() and '弱い' in guide.decode()
    fingerprint(receipt['comparison']);comparison=load('owner-copy-comparison.json')
    assert comparison['owner_copy']==receipt['challenge']
    assert comparison['current_copy']['sha256']==CURRENT
    current=fingerprint(comparison['current_copy']);diff=fingerprint(comparison['diff'])
    assert comparison['status']=='PASS' and comparison['only_import_lines_differ'] and comparison['normalized_bytes_identical']
    assert comparison['comment_or_definition_change'] is False
    strip=lambda s:re.sub(r'(?m)^import [^\n]+\n','',s)
    assert strip(challenge.decode())==strip(current.decode()),'owner statement body changed beyond imports'
    expected=''.join(difflib.unified_diff(challenge.decode().splitlines(True),current.decode().splitlines(True),fromfile=receipt['challenge']['path'],tofile=comparison['current_copy']['path']))
    assert diff.decode()==expected,'owner statement import diff mismatch'
    manifest=load('theorem1a-manifest.json')
    assert manifest['owner_statement_confirmed'] is True and manifest['owner_statement_confirmation']==h['receipt']
    assert not manifest['prose_geometry_bridge_formalized']
    assert by['thm:aligned']['status']=='lean-result-received'
    assert 'Owner statement meaning confirmed' in by['thm:aligned']['status_scope']
    assert 'Owner confirmation' not in ' '.join(by['thm:aligned']['remaining_obligations'])
    assert 'human proof peer review' in ' '.join(by['thm:aligned']['remaining_obligations'])
    assert not a['scope']['human_peer_review'] and not a['scope']['novelty_established']
    return dict(owner_statement_confirmed=True,statement_scope='Theorem 1a version 2 only',import_only_diff=True,
                proof_peer_review=False,prose_bridge_review=False,novelty_review=False,lean_execution=False)
