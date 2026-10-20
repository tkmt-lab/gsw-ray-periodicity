"""Local packet readers; checks are static receipt checks, never Lean execution."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
THM_PIN='5ea6bde55db57830bef11ea29dcd360b138c9dc8'
PIN='dbf1957c781a42c702fff08bae93d8c004305c7a'
FAMILIES=['A1','A2','B2','C1','K3','E10','D12','D14','D1','O2','A3']
def load(name):return json.loads(local(name).read_text())
def local(name):
 p=Path(name);assert name and not p.is_absolute() and '..' not in p.parts,('unsafe path',name)
 q=ROOT/p;assert q.resolve().is_relative_to(ROOT) and q.exists(),('missing/outside',name)
 return q
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fingerprint(r):
 p=local(r['path']);assert p.is_file() and sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],('fingerprint',r['path'])
def walk_refs(x):
 if isinstance(x,list):
  for v in x:walk_refs(v)
 elif isinstance(x,dict):
  if isinstance(x.get('path'),str):
   local(x['path'])
   if 'sha256' in x and 'bytes' in x:fingerprint(x)
  for k,v in x.items():
   if k!='path' or not isinstance(v,str):walk_refs(v)
def strip_lean(s):
 # Nested block comments and line comments, preserving strings separately.
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif quoted:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quoted=False;i+=1
   else:i+=1
   out.append(' ')
  elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j;out.append('\n')
  elif s[i]=='"':quoted=True;i+=1;out.append(' ')
  else:out.append(s[i]);i+=1
 assert not depth and not quoted,'unterminated Lean comment/string'
 return ''.join(out)
def result(**kw):print(json.dumps(dict(status='PASS',**kw),sort_keys=True))
