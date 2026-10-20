"""Check TeX structure, declared correspondence and final PDF receipt."""
import re
from packet_common import load,local,fingerprint,result,sha

def main():
 tex=local('paper-lines-v4.9-en.tex').read_text();stack=[]
 for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',tex):
  if m[1]=='begin':stack.append(m[2])
  else:assert stack and stack.pop()==m[2],m[2]
 assert not stack
 labels=re.findall(r'\\label\{([^}]+)\}',tex);refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',tex)
 assert set(refs)<=set(labels)
 bib=set(re.findall(r'\\bibitem\{([^}]+)\}',tex))
 for row in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',tex):assert set(row.split(','))<=bib,row
 abstract=tex.split('\\begin{abstract}',1)[1].split('\\end{abstract}',1)[0]
 assert 'fixed monadic second-order sentence' in abstract and 'unary finite' in abstract and 'known equivalence' in abstract
 assert 'oblique' not in abstract
 assert tex.index('\\label{thm:aligned}')<tex.index('\\label{cor:catalog}')<tex.index('\\label{sec:extension}')
 start=tex.index('\\label{sec:extension}');end=tex.index('\\label{sec:evidence}')
 for m in re.finditer(r'\b(?:C2|K4|O1)\b',tex):assert start<m.start()<end,('leapfrog outside prospects',m[0])
 assert 'proof sketch' in tex and 'four' in tex.lower()
 assert 'abstracts and' in tex and 'S2191, S2192' in tex and '10^*' in tex
 assert 'Prose correspondence lemma (not formalized in Lean)' in tex
 assert "The owner confirmed the version-2 specification's meaning" in tex and 'Human proof peer review remains unrecorded' in tex
 assert 'Lean-proved' in tex and 'ClaudeChallenge2.main' in tex
 corr=load('v3-correspondence.json');fingerprint(corr['source']);fingerprint(corr['target'])
 v3=local(corr['source']['path']).read_text()
 sections=set(re.findall(r'^### (\d+\.\d+)\b',v3,re.M))
 covered={r['v3_section'] for r in corr['rows']}
 assert sections<=covered and len(corr['rows'])==28,(sections-covered,len(corr['rows']))
 ids={c['id'] for c in load('claims.json')['claims']}
 for r in corr['rows']:assert r['v4_label'] in labels and set(r['claim_ids'])<=ids
 receipt=load(load('release-metadata.json')['pdf_validation_file']);assert receipt['status']=='PASS' and receipt['pages']>=16
 assert sha(local(receipt['pdf_path']))==receipt['pdf_sha256'] and sha(local(receipt['source_path']))==receipt['source_sha256']
 assert receipt['visual_review']['all_pages_viewed'] and len(receipt['page_render_hashes'])==receipt['pages']
 assert not receipt['overfull_boxes'] and not receipt['undefined_references'] and not receipt['duplicate_destinations']
 assert 'ClaudeChallengeK3.main' in tex and 'Claude4K3.k3_statement' in tex and 'Claude4K3.noThree' in tex
 assert 'No K3 graph-necessity proof' not in tex and 'Lean graph sufficiency only' not in tex
 assert 'ClaudeChallengeC1.classification' in tex and 'ClaudeChallengeC1.main' in tex
 assert 'The IPR condition is outside Lean.' in tex
 assert 'ClaudeChallengeO2.classification' in tex and 'ClaudeChallengeO2.main' in tex
 assert 'IPR remains outside Lean.' in tex
 result(pages=receipt['pages'],claims=len(ids),correspondence_rows=28,scope='structure, correspondence and recorded visual receipt only')
if __name__=='__main__':main()
