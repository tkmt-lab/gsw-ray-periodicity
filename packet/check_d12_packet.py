"""Read-only D12 scope, source fingerprints and rational identities; not Lean."""
from pathlib import Path
from fractions import Fraction
import ast,gzip,hashlib,json,re

STATUS='two-separately-derived-universal-proof-routes-received'

def check_preservation(raw,old):
    stripped=raw
    for tag in ['D12-SCOPE','D12-SECTION']:
        assert raw.count('% '+tag+'-BEGIN')==raw.count('% '+tag+'-END')==1
        stripped=re.sub(r'% '+tag+r'-BEGIN\n.*?% '+tag+r'-END\n','',stripped,flags=re.S)
    for env in ['definition','alignedtheorem','catalogcor','proposition','lemma','equation']:
        p=r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
        assert re.findall(p,stripped,re.S)==re.findall(p,old,re.S),'existing mathematical block changed'
    for p in [r'\\\[.*?\\\]',r'(?<!\\)\$(?!\$).*?(?<!\\)\$']:
        assert re.findall(p,stripped,re.S)==re.findall(p,old,re.S),'displayed mathematics changed'
    assert re.findall(r'\\claimid\{([^}]+)\}',stripped)==re.findall(r'\\claimid\{([^}]+)\}',old)
    expected=old.replace('Version 6.1, 21 October 2026','Version 6.2, 21 October 2026').replace('The author used Codex and Claude Code to assist with literature','The author used AI systems to assist with literature')
    expected=expected.replace('A full D12\nclassification is the subject of a separate article.', 'The full D12 classification is given in Section~\\ref{sec:d12-classification}.')
    expected=expected.replace('No new D12\nclassification is asserted by this paper.', 'The D12 classification in Section~\\ref{sec:d12-classification} retains its two prose/computer-assisted proof bases.')
    assert re.sub(r'\n{3,}','\n\n',stripped).strip()==re.sub(r'\n{3,}','\n\n',expected).strip(),'unrecorded predecessor edit'
    assert not re.search(r'\b(?:R00[245]|Claude|Codex|coordinator|mailbox)\b',raw),'internal process marker in article'

def certificates(x):
    if isinstance(x,list):
        for v in x:yield from certificates(v)
    elif isinstance(x,dict):
        if {'forms','indices','weights','constant'}<=x.keys():yield x
        for v in x.values():yield from certificates(v)

def check_d12(root):
    root=Path(root)
    claims=json.loads((root/'claims.json').read_text())
    c=next(c for c in claims['claims'] if c['id']=='thm:d12-classification')
    assert c['status']==STATUS and not c['lean'],'D12 Lean promotion'
    assert c['human_review'] is False and c['paper_label']==c['id']
    assert claims['scope']['new_D12_classification_included'] is True
    assert c['statement_plain']=='For all positive r,s, D12(r,s) has a literal path iff r|(s-1) or r|(s+1) or |r-3s|=1. Equivalently r=1; r=2 and s odd; or r>=3 with that criterion.'
    assert len(c['remaining_obligations'])==7 and 'No human proof review or Lean proof.' in c['remaining_obligations']
    ledger=json.loads((root/'d12/derivatives.json').read_text())
    assert ledger['status']=='PUBLIC_DERIVATIVES' and not ledger['originals_included']
    from publication_privacy import matches
    for p in (root/'d12').rglob('*'):
        if p.suffix=='.py':ast.parse(p.read_text(),filename=p.name)
        if p.suffix=='.gz':assert not matches(gzip.decompress(p.read_bytes()).decode()),'D12 compressed privacy scan'
    paths=set()
    for row in ledger['records']:
        r=row['public'];p=Path(r['path'])
        assert not p.is_absolute() and '..' not in p.parts and p.as_posix().startswith('d12/')
        assert p.as_posix() not in paths;paths.add(p.as_posix())
        raw=(root/p).read_bytes();assert hashlib.sha256(raw).hexdigest()==r['sha256'] and len(raw)==r['bytes'],'D12 derivative fingerprint'
        assert re.fullmatch('[0-9a-f]{64}',row['original_sha256']) and row['original_bytes']>0
    total=0
    for p in sorted((root/'d12/route-b').rglob('*.json')):
        for cert in certificates(json.loads(p.read_text())):
            forms=cert['forms'];indices=cert['indices'];weights=list(map(Fraction,cert['weights']))
            assert len(indices)==len(weights)>0 and len(set(indices))==len(indices)
            assert all(isinstance(i,int) and 0<=i<len(forms) for i in indices)
            assert all(w>=0 for w in weights)
            size=len(forms[0]);assert size>=2 and all(len(f)==size for f in forms)
            value=[sum(w*Fraction(forms[i][j]) for i,w in zip(indices,weights)) for j in range(size)]
            assert all(v==0 for v in value[:-1]) and value[-1]==Fraction(cert['constant'])<0,('D12 contradiction identity',p.name,cert.get('label'))
            total+=1
    assert len(paths)==78 and total==5413,'D12 certificate inventory incomplete'
    raw=(root/'paper-lines-v6.2-en.tex').read_text();check_preservation(raw,(root/'paper-lines-v6.1-en.tex').read_text())
    assert 'D12 ray consequence &' in raw and 'D12 classification &' in raw
    assert 'Neither route' in raw and 'is a Lean proof.' in raw and 'cyclic five-edge-connectivity' in raw
    return dict(status='PASS',rational_identities=total,derivative_files=len(paths),D12_lean=False,
                scope='Stored rational contradiction identities and static scope; all-parameter geometry, semantics and induction remain prose.')

if __name__=='__main__':print(json.dumps(check_d12(Path(__file__).resolve().parent),sort_keys=True))
