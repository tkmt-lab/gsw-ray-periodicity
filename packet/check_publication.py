"""Static public metadata/license/contact checks; no upload or proof review."""
import json,hashlib,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def check_publication():
 a=json.loads((ROOT/'release-metadata.json').read_text());cff=json.loads((ROOT/'CITATION.cff').read_text())
 assert a['packet_version']=='1.6.0' and a['author']=='Tatsuhiko Takimoto' and a['affiliation']=='Independent researcher'
 assert a['organization'] is None and a['email'] is None and a['AI_statement_owner_approved'] is True
 assert a['contact']=='GitHub Issues' and a['contact_url_file']=='REPOSITORY-URL.txt'
 assert a['text_figures_data_license']=='CC-BY-4.0' and a['code_lean_license']=='Apache-2.0'
 assert not a['uploaded'] and a['doi'] is None
 expected={'8.1':'https://github.com/tkmt-lab/a3-gsw-classification','5.0':'https://github.com/tkmt-lab/gsw-ray-periodicity'}[a['paper_version']]
 assert (ROOT/a['contact_url_file']).read_text().strip()==expected,'wrong or unresolved repository URL'
 assert cff['repository-code']==expected,'CFF repository URL differs from approved URL'
 token='<'+'REPOSITORY-URL'+'>'
 current=[*ROOT.glob('*.md'),*ROOT.glob('*.txt'),ROOT/'CITATION.cff']
 assert not any(token in p.read_text() for p in current),'unresolved repository URL placeholder'
 person={'family-names':'Takimoto','given-names':'Tatsuhiko','affiliation':'Independent researcher'}
 assert cff['cff-version']=='1.2.0' and cff['type']=='software' and cff['version']=='1.6.0'
 assert cff['authors']==[person] and cff['license']=='Apache-2.0'
 article=cff['preferred-citation'];assert article['type']=='article' and article['version']==a['paper_version']
 assert article['authors']==[person] and article['license']=='CC-BY-4.0'
 # Validate the exact limited CFF object we emit against the supplied official field/enum vocabulary.
 schema=json.loads((ROOT/'cff-schema.json.original.log').read_text())
 assert set(cff)<=set(schema['properties']) and set(schema['required'])<=set(cff)
 assert set(article)<=set(schema['definitions']['reference']['properties'])
 assert set(person)<=set(schema['definitions']['person']['properties'])
 assert cff['license'] in schema['definitions']['license-enum']['enum'] and article['license'] in schema['definitions']['license-enum']['enum']
 assert not {'email','doi','date-released'}&set(cff)
 for r in json.loads((ROOT/'license-sources.json').read_text()):
  p=ROOT/r['path'];raw=p.read_bytes();assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256']
 claims=json.loads((ROOT/'claims.json').read_text());tex=(ROOT/claims['paper']['path']).read_text()
 pdf=json.loads((ROOT/a['pdf_validation_file']).read_text())
 assert pdf['status']=='PASS' and pdf['source_sha256']==claims['paper']['sha256']
 assert hashlib.sha256((ROOT/pdf['pdf_path']).read_bytes()).hexdigest()==pdf['pdf_sha256']
 assert pdf['visual_review']['all_pages_viewed']
 assert r'\author{Tatsuhiko Takimoto}' in tex and r'\address{Independent researcher}' in tex
 assert 'Acknowledgements and AI-use statement (draft)' not in tex
 assert 'Proposed wording:' not in tex and 'author placeholder' not in tex and '[human author]' not in tex
 assert 'not a statement already approved' not in tex and 'owner has not' not in tex.lower()
 assert 'License and contact' in tex and 'GitHub Issues' in tex and 'REPOSITORY-URL.txt' in tex
 assert 'CC BY 4.0' in tex and 'Apache-2.0' in tex
 if a['paper_version']=='8.1':
  assert 'full twelve-page' in tex and 'remain unread' in tex and 'did not locate this same two-stage' in tex
  assert 'P006-18' in (ROOT/'P006-corrections.md').read_text()
 else:
  assert 'operation permitting heptagons' in tex and 'operation permitting pentagons' not in tex
  assert 'two example rays for every ray parameter' in tex
  assert 'P006-L10' in (ROOT/'P006-corrections.md').read_text()
 if a['paper_version']=='5.0':
  ref=cff['references'];assert len(ref)==1
  r=ref[0];assert r['type']=='article' and r['authors']==[person]
  assert r['repository-code']=='https://github.com/tkmt-lab/a3-gsw-classification'
  assert r['version']=='8.1' and r['title'].startswith('A two-stage classification')
  assert set(r)<=set(schema['definitions']['reference']['properties'])
  assert 'classification and arithmetic argument~\\cite{A3}.' in tex
  assert '\\bibitem{A3} Tatsuhiko Takimoto' in tex
 from publication_privacy import check_privacy
 from check_publication_audit import check_publication_audit
 check_publication_audit(ROOT)
 privacy = check_privacy(ROOT)
 from check_owner_statement import check_owner_statement
 check_owner_statement(ROOT)
 return dict(**privacy,public_metadata=True,packet_version='1.6.0',repository_url=expected,uploaded=False,full_cff_schema_validation=False,scope='exact field/enum contract, not a general CFF schema engine')
if __name__=='__main__':print(json.dumps(dict(status='PASS',**check_publication())))
