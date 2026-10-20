"""Verify closed files, references, links and advertised local commands."""
import json,re,shlex
from urllib.parse import unquote,urlsplit
from packet_common import ROOT,local,sha,walk_refs,load,result

def main():
 rows={}
 for line in local('SHA256SUMS').read_text().splitlines():
  h,n=line.split('  ',1);assert n not in rows;assert sha(local(n))==h,('hash',n);rows[n]=h
 actual=set()
 for p in ROOT.rglob('*'):
  assert not p.is_symlink(),p
  assert not set(p.relative_to(ROOT).parts)&{'.git','.lake','__pycache__'},p
  if p.is_file():actual.add(p.relative_to(ROOT).as_posix())
 assert actual==set(rows)|{'SHA256SUMS'},('inventory',actual-set(rows),set(rows)-actual)
 for p in ROOT.rglob('*.json'):walk_refs(json.loads(p.read_text()))
 links=0
 for p in ROOT.glob('*.md'):
  for target in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',p.read_text()):
   u=urlsplit(target.strip('<>'))
   if u.scheme:assert u.scheme in ['https','http'];continue
   if u.path:local(unquote(u.path));links+=1
 commands=load('commands.json');advertised=[]
 for block in re.findall(r'```sh\n(.*?)```',local('AGENTS.md').read_text(),re.S):
  advertised+=[shlex.split(line) for line in block.splitlines() if line.strip()]
 assert advertised==[r['argv'] for r in commands]
 assert len(commands)==4
 for c in commands:
  assert c['argv'][:2]==['python3','-B'] and len(c['argv'])==3;local(c['argv'][2])
 from check_publication import check_publication
 publication=check_publication()
 assert publication['repository_url']==local('REPOSITORY-URL.txt').read_text().strip()
 result(files=len(actual),local_links=links,commands=len(commands),scope='filesystem and metadata closure only')
if __name__=='__main__':main()
