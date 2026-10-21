"""Static mathematical-preservation, editorial-scope and PDF-record check."""
import re
from packet_common import load, local, fingerprint, result, sha


def displays(tex):
    return [re.findall(pattern, tex, re.S) for pattern in
            [r'\\\[.*?\\\]', r'\\begin\{equation\}.*?\\end\{equation\}']]


def first_two_columns(tex, anchor):
    part = tex.split(anchor, 1)[1].split('\\end{tabular}', 1)[0]
    return [tuple(x.strip() for x in line.split('&')[:2])
            for line in part.splitlines() if '&' in line]


def main():
    tex = local('paper-lines-v6.1-en.tex').read_text()
    old = local('paper-lines-v6.0-en.tex').read_text()
    stack = []
    for match in re.finditer(r'\\(begin|end)\{([^}]+)\}', tex):
        if match[1] == 'begin':
            stack.append(match[2])
        else:
            assert stack and stack.pop() == match[2], 'TeX nesting'
    assert not stack
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    assert len(labels) == len(set(labels))
    assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)) <= set(labels)
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}', tex))
    for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', tex):
        assert set(group.split(',')) <= bib
    for env in ['definition', 'alignedtheorem', 'catalogcor']:
        pattern = r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
        assert len(re.findall(pattern, old, re.S)) == 1
        assert re.findall(pattern, tex, re.S) == re.findall(pattern, old, re.S), 'numbered mathematical statement changed'
    assert displays(tex) == displays(old), 'displayed mathematics changed'
    assert first_two_columns(tex, '\\subsection{The specified closed domains}') == first_two_columns(old, '\\subsection{The specified closed domains}'), 'closed domains/conditions changed'
    # Two central proof subsections are completely unchanged, including prose.
    for begin, end in [('\\subsection{States, transitions', '\\subsection{Folding the restricted'),
                       ('\\subsection{Folding the restricted', '\\subsection{The exact path sentence')]:
        assert tex[tex.index(begin):tex.index(end)] == old[old.index(begin):old.index(end)], 'proof subsection changed'
    ids = re.findall(r'\\claimid\{([^}]+)\}', tex)
    assert ids == re.findall(r'\\claimid\{([^}]+)\}', old) and len(ids) == 30
    assert set(ids) == {c['id'] for c in load('claims.json')['claims']}
    assert tex.count('VERIFICATION-RECORD.md') == 1, 'verification record reference count'
    assert '\\section{What is proved, and how}' in tex, 'current proof-scope section missing'
    assert tex.index('\\section{Introduction}') < tex.index('\\section{What is proved, and how}') < tex.index('\\label{sec:definitions}')
    ai = tex.split('\\section*{Acknowledgements and AI-use statement}', 1)[1].split('\\section*{License and contact}', 1)[0]
    body = tex.replace(ai, '')
    assert len(ai.strip().split('\n\n')) == 1 and ai.count('Codex') == ai.count('Claude Code') == 1, 'AI-use paragraph scope'
    patterns = [r'\bR00[245]\b', r'\bcoordinator\b', r'\b(?:received|receipts?|mailbox)\b',
                r'\bowner(?:s|\x27s)?\b', r'\bT\d{4}\b', r'\bClaude\b', r'\b(?:AH|AL|AM|AN|AD|M4)\b']
    for pattern in patterns:
        assert not re.search(pattern, body, re.I if pattern in patterns[1:4] else 0), 'internal process marker in article'
    assert not re.search(r'\b(?=[0-9a-f]{8,40}\b)(?=[0-9a-f]*[a-f])[0-9a-f]{8,40}\b', body), 'commit hash in article'
    record = local('VERIFICATION-RECORD.md').read_text()
    for term in ['R004', 'Comparator', 'independence', 'owner-confirmation', 'T0770', '2,814', 'OS process isolation', 'main_residue']:
        assert term in record, ('verification record content missing', term)
    for claim in ids:
        assert '`'+claim+'`' in record, ('verification claim missing', claim)
    ledger = load('editorial-edit-map.json')
    for entry in ledger['edits']:
        assert entry['before'].rstrip() in record, ('moved paragraph missing', entry['number'])
    assert ledger['predecessor_sha256'] == sha(local('paper-lines-v5.0-en.tex'))
    scope_ledger = load('scope-edit-map.json')
    assert scope_ledger['predecessor_sha256'] == sha(local('paper-lines-v6.0-en.tex'))
    assert scope_ledger['target_sha256'] == sha(local('paper-lines-v6.1-en.tex'))
    for entry in scope_ledger['edits']:
        assert entry['before'].rstrip() in record, 'E10 scope edit missing from record'
    assert 'sec:e10-formal' in tex and 'validity and triangle-lifting' in tex
    assert 'it gives no $r=1$ closed classification' in tex
    audit = load('editorial-audit.json')
    assert audit['status'] == 'PASS' and not any(audit['internal_name_scan'].values())
    abstract = tex.split('\\begin{abstract}', 1)[1].split('\\end{abstract}', 1)[0]
    assert 'fixed monadic second-order sentence' in abstract and 'unary finite' in abstract and 'known equivalence' in abstract
    assert 'oblique' in abstract and 'proof sketch' in abstract
    begin, end = tex.index('\\label{sec:extension}'), tex.index('\\label{sec:evidence}')
    for match in re.finditer(r'\b(?:C2|K4|O1)\b', tex):
        assert begin < match.start() < end, 'leapfrog outside prospects'
    corr = load('v3-correspondence.json')
    fingerprint(corr['source']); fingerprint(corr['target'])
    for row in corr['rows']:
        assert row['v4_label'] in labels and set(row['claim_ids']) <= set(ids)
    assert len(corr['rows']) == 28
    pdf = load(load('release-metadata.json')['pdf_validation_file'])
    assert pdf['status'] == 'PASS' and pdf['pages'] == 17
    assert sha(local(pdf['source_path'])) == pdf['source_sha256'] and sha(local(pdf['pdf_path'])) == pdf['pdf_sha256']
    assert pdf['visual_review']['all_pages_viewed'] and len(pdf['page_render_hashes']) == 17
    assert not pdf['overfull_boxes'] and not pdf['undefined_references'] and not pdf['duplicate_destinations']
    result(pages=17, claims=30, unchanged_numbered_blocks=3, displayed_math_unchanged=True,
           unchanged_proof_subsections=2, internal_process_markers=0, AI_tool_exceptions=2,
           scope='Static preservation, separate-record completeness and saved PDF review; not a new proof/kernel check.')


if __name__ == '__main__':
    main()
