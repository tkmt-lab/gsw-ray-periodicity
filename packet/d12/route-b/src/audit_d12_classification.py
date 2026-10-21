"""Separate arithmetic/geometry audit; does not import the D12 certificate checkers."""
from fractions import Fraction as Q
from math import gcd, lcm
import gzip
import hashlib
import json
from pathlib import Path
import signal
import time
from linear_farkas import contradiction as fm
from mac_memory_guard import Guard

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}
AUDIT_PROOFS=[]


def count(name):
    COUNTS[name]=COUNTS.get(name,0)+1


def numbers(row):
    assert all(not isinstance(x,float) for x in row)
    return tuple(Q(x) for x in row)


def weighted(proof):
    """Clear all denominators, then use integer multiplication/addition only."""
    forms=list(map(numbers,proof['forms']))
    ids=proof['indices'];weights=numbers(proof['weights'])
    assert len(ids)==len(weights)==len(set(ids)) and all(w>=0 for w in weights)
    assert all(0<=i<len(forms) for i in ids)
    fd=lcm(*(x.denominator for row in forms for x in row))
    wd=lcm(*(x.denominator for x in weights))
    total=[sum(int(forms[i][j]*fd)*int(w*wd) for i,w in zip(ids,weights))
           for j in range(len(forms[0]))]
    assert all(x==0 for x in total[:-1]) and total[-1]<0
    assert Q(total[-1],fd*wd)==Q(proof['constant'])
    count('verified_farkas_certificates')


def normal(forms):
    """Canonical equivalent system, independently implemented for any dimension."""
    parallel={}
    dim=len(forms[0])-1 if forms else 2
    for row in forms:
        row=numbers(row)
        den=lcm(*(x.denominator for x in row))
        ints=[int(x*den) for x in row]
        g=gcd(*ints[:-1])
        if not g:
            if ints[-1]<0:
                return ((0,)*dim+(-1,),)
            continue
        direction=tuple(x//g for x in ints[:-1])
        bound=Q(ints[-1],g)
        if direction not in parallel or bound<parallel[direction]:
            parallel[direction]=bound
    result=[]
    for direction,bound in sorted(parallel.items()):
        row=tuple(x*bound.denominator for x in direction)+(bound.numerator,)
        g=gcd(*row)
        result.append(tuple(x//g for x in row))
    return tuple(result)


def plus(x,y): return tuple(a+b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def minus(x,y): return plus(x,neg(y))
def times(x,k): return tuple(a*k for a in x)
def c(n): return (0,0,n)
def vp(x,y): return tuple(plus(a,b) for a,b in zip(x,y))
def vm(x,y): return tuple(minus(a,b) for a,b in zip(x,y))
def shift(p,d,t): return vp(p,tuple(times(t,x) for x in d))
def rot(p,k):
    x,y=p
    for _ in range(k%6):
        x,y=neg(y),plus(x,y)
    return x,y
def cross(p,d): return minus(times(p[0],d[1]),times(p[1],d[0]))


def at(b,index):
    assert all(x%2==0 for x in index[:-1])
    odd=index[-1]%2
    half=tuple(x//2 for x in index[:-1])+((index[-1]-odd)//2,)
    return vp(shift(b['a'],b['d'],half),tuple(c(odd*x) for x in b['e']))


def ge(domain,f,label):
    forms=list(domain)+[minus(neg(f),c(1))]
    proof=fm(forms)
    assert proof is not None,(label,domain,f)
    record=dict(forms=forms,**proof)
    weighted(record)
    AUDIT_PROOFS.append(dict(label=label,**record))


def zero(domain,f,label):
    if any(f):
        ge(domain,f,label+'+')
        ge(domain,neg(f),label+'-')


def same(domain,p,q,label):
    for i,f in enumerate(vm(p,q)):
        zero(domain,f,f'{label}-{i}')


def explicit_geometry():
    r,s=(1,0,0),(0,1,0)
    L=plus(r,times(s,2));B=plus(r,times(s,3));C=plus(times(r,2),times(s,3));D=plus(r,s)
    z=c(0);twiceL=times(L,2)
    p0=[(z,z),(s,z),(s,D),(s,L),(neg(r),C),(neg(D),twiceL),
        (neg(times(D,2)),twiceL),(neg(C),twiceL),(neg(C),B),(neg(C),L),
        (neg(L),s),(neg(D),z)]
    p1=[(z,z),(D,z),(L,z),(L,D),(L,L),(s,C),(z,twiceL),
        (neg(D),twiceL),(neg(L),twiceL),(neg(L),B),(neg(L),L),(neg(s),s)]
    return [p0,p1],[list(range(12)),[0]+list(range(11,0,-1))],(L,B,C,D)


POLYS,CELLS,(L,B,C,D)=explicit_geometry()


def facets(f,p):
    x,y=p;xy=plus(x,y)
    if f==0:
        return [plus(x,C),minus((0,1,0),x),y,minus(times(L,2),y),plus(xy,D),minus(B,xy)]
    return [plus(x,L),minus(L,x),y,minus(times(L,2),y),xy,minus(times(L,2),xy)]


def seam(f,i):
    g=1-f
    u=CELLS[f][i];v=CELLS[f][(i+1)%12]
    x,y=POLYS[f][i],POLYS[f][(i+1)%12]
    a=POLYS[g][CELLS[g].index(u)];b=POLYS[g][CELLS[g].index(v)]
    k=next(k for k in range(6) if rot(vm(y,x),k)==vm(b,a))
    return g,k,vm(a,rot(x,k))


def edge_conditions(f,i,p):
    a,b=POLYS[f][i],POLYS[f][(i+1)%12]
    delta=vm(b,a)
    sample=[2*x[0]+2*x[1]+x[2] for x in delta]
    length=gcd(*sample);d=tuple(x//length for x in sample)
    axis=0 if d[0] else 1
    length=times(delta[axis],d[axis])
    diff=vm(p,a);t=times(diff[axis],d[axis])
    return [t,minus(length,t)],[cross(diff,d)]


def on_edge(domain,f,i,p,label):
    inequalities,equalities=edge_conditions(f,i,p)
    for f in inequalities:
        ge(domain,f,label)
    for f in equalities:
        zero(domain,f,label)


def candidate_geometry(case,record):
    domain=record['domain'];runs=case['runs']
    zeroform=c(0)
    assert runs[0]['a']==[[0,0,0],[0,0,0]]
    expected=[
        (0,[-1,0],[-1,1]),(0,[-1,1],[-1,0]),(0,[-1,1],[0,1]),
        (0,[0,1],[-1,1]),(0,[0,1],[1,0]),(0,[1,0],[0,1]),
        (1,[-1,1],[0,1]),(1,[0,1],[-1,1]),(1,[0,1],[1,0]),(1,[1,0],[0,1])]
    assert (runs[0]['face'],runs[0]['d'],runs[0]['e'])==expected[case['start']]
    lengths=[tuple(b['length']) for b in runs]
    bases=[zeroform]
    for n in lengths:
        bases.append(plus(bases[-1],n))
    for i,b in enumerate(runs):
        n=lengths[i]
        ge(domain,minus(n,c(3 if i<len(runs)-1 else 1)),f'length-{i}')
        for d in (b['d'],b['e'],[x-y for x,y in zip(b['d'],b['e'])]):
            assert d[0]**2+d[0]*d[1]+d[1]**2==1
        for parity in (0,1):
            hi=tuple(x//2 for x in n[:-1])+((n[-1]-1-parity)//2,)
            if hi==c(-1):
                continue
            origin=vp(b['a'],tuple(c(parity*x) for x in b['e']))
            for p in (origin,shift(origin,b['d'],hi)):
                for form in facets(b['face'],p):
                    ge(domain,form,f'inside-{i}-{parity}')
    for check in record['checks']:
        if check['kind']!='join':
            continue
        i=check['index'];old,new=runs[i:i+2]
        tail=[at(old,minus(lengths[i],c(k))) for k in (3,2,1)]
        g,k,z=seam(old['face'],check['edge'])
        assert g==new['face'] and k==check['rotation']
        for p in tail[1:]:
            on_edge(domain,old['face'],check['edge'],p,'join-edge')
        moved=[vp(rot(p,k),z) for p in tail[1:]]
        q=[at(new,c(j)) for j in range(3)]
        same(domain,vp(rot(vm(vp(tail[1],tail[2]),tail[0]),k),z),q[0],'join-0')
        same(domain,vm(vp(moved[1],q[0]),moved[0]),q[1],'join-1')
        same(domain,vm(vp(q[0],q[1]),moved[1]),q[2],'join-2')
    i=case['repeat_block']
    local=minus(tuple(case['repeat_index']),bases[i])
    ge(domain,local,'repeat-lo')
    ge(domain,minus(minus(lengths[i],c(1)),local),'repeat-hi')
    ge(domain,minus(minus(bases[-1],c(2)),tuple(case['repeat_index'])),'repeat-earlier')
    p=at(runs[i],local);end=at(runs[-1],minus(lengths[-1],c(1)))
    if runs[i]['face']==runs[-1]['face']:
        same(domain,p,end,'repeat')
    else:
        check=next(x for x in record['checks'] if x['kind']=='repeat')
        on_edge(domain,runs[i]['face'],check['edge'],p,'repeat-edge')
        g,k,z=seam(runs[i]['face'],check['edge'])
        assert g==runs[-1]['face'] and k==check['rotation']
        same(domain,vp(rot(p,k),z),end,'repeat')
    count('independently_rederived_short_geometries')


def odd_forms(case,domain):
    base=c(0);runs=case['runs']
    for i,b in enumerate(runs):
        n=tuple(b['length'])
        for parity in (0,1):
            if (base[-1]+parity)%2!=1:
                continue
            hi=tuple(x//2 for x in n[:-1])+((n[-1]-1-parity)//2,)
            if i==len(runs)-1 and parity==(n[-1]-1)%2:
                hi=minus(hi,c(1))
            origin=vp(b['a'],tuple(c(parity*x) for x in b['e']))
            d=b['d'];axis=0 if d[0] else 1
            for j,p in enumerate(POLYS[b['face']]):
                if CELLS[b['face']][j]==0:
                    continue
                delta=vm(p,origin);t=times(delta[axis],d[axis]);eq=cross(delta,d)
                yield list(domain)+[t,minus(hi,t),eq,neg(eq)]
        base=plus(base,n)


def coverage(data,candidates):
    odd_pool={normal(x['forms']) for x in data['constraints']}
    expected={(region,start) for region,starts in [
        ('s_eq_r',range(10)),('s2_to_rminus2_below3',range(10)),('r_eq_3s',range(10)),
        ('r_above_3s',range(10)),('s_above_r',(1,2,5,7,8,9))] for start in starts}
    assert {(x['region'],x['start']) for x in data['coverage']}==expected
    regions=dict(s_eq_r=[(1,-1,0),(-1,1,0)],
                 s2_to_rminus2_below3=[(1,-1,-2),(-1,3,-2)],
                 r_eq_3s=[(1,-3,0),(-1,3,0)],
                 r_above_3s=[(1,-3,-2)],s_above_r=[(-1,1,-2)])
    for proof in data['coverage']:
        assert normal(proof['initial'])==normal([(1,0,-2),(0,1,-2)]+regions[proof['region']])
        empty={normal(x['forms']) for x in proof['empty_proofs']}
        remain=[normal(proof['initial'])]
        for step in proof['steps']:
            candidate=candidates[step['candidate']]
            assert candidate['start']==proof['start']
            for forms in odd_forms(candidate,step['domain']):
                assert normal(forms) in odd_pool,('missing odd certificate',proof['region'],proof['start'])
                count('independently_rederived_odd_exclusions')
            intrinsic=data['domains'][step['candidate']]['domain']
            for form in intrinsic:
                ge(step['domain'],tuple(form),'safe-domain-subset')
            assert len(remain)==step['before']
            updated=[]
            for cell in remain:
                prefix=list(cell)
                for form in step['domain']:
                    excluded=normal(prefix+[minus(neg(tuple(form)),c(1))])
                    if excluded not in empty:
                        updated.append(excluded)
                    prefix=list(normal(prefix+[form]))
                    if tuple(prefix) in empty:
                        break
            assert len(updated)==step['after']
            remain=updated
        assert not remain and not proof['remaining']
        count('independently_replayed_coverage_regions')


def univariate(data):
    expected_lower={'r1':1,'s1':2,'r3s+1':1,'r3s-1':2}
    assert {case['name'] for case in data['cases']}==set(expected_lower)
    for row in data['constraints']:
        assert row['lower']==expected_lower[row['family']]
        lo=row['lower'];hi=None;impossible=False
        if 'nonnegative' in row:
            a,b=row['nonnegative']
            assert a>=0 and a*lo+b>=0
        else:
            for a,b in row['equalities']:
                if a==0:
                    impossible |= b!=0
                elif (-b)%a:
                    impossible=True
                else:
                    t=(-b)//a;lo=max(lo,t);hi=t if hi is None else min(hi,t)
            for a,b in row['inequalities']:
                if a>0:
                    lo=max(lo,(-b+a-1)//a)
                elif a<0:
                    t=(-b)//a;hi=t if hi is None else min(hi,t)
                else:
                    impossible |= b<0
            assert impossible or (hi is not None and lo>hi)
        count('integer_univariate_checks')


def walk_proofs(x):
    if isinstance(x,dict):
        if all(k in x for k in ('forms','indices','weights','constant')):
            yield x
        for value in x.values():
            yield from walk_proofs(value)
    elif isinstance(x,list):
        for value in x:
            yield from walk_proofs(value)


def main():
    signal.alarm(180)
    guard=Guard(512*1024**2);guard.check(start=True)
    tick=time.monotonic()
    inputs=['evidence/d12-boundary/symbolic-check-v3.json',
            'evidence/d12-positive-r2/affine-certificates.json',
            'evidence/d12-short/candidates-v2.json',
            'evidence/d12-short/symbolic-check-v5.json',
            'evidence/d12-loops/symbolic-check.json']
    raw=[(ROOT/p).read_bytes() for p in inputs]
    boundary,r2,candidates,short,loops=map(json.loads,raw)
    assert boundary['status']==short['status']==loops['status']=='SYMBOLIC_CERTIFICATE_PASS'
    univariate(boundary)
    for row in r2:
        a,b,c0,d=row['form'];k=row['k'];eps=row['epsilon'];lower=2 if eps==1 else 3
        expected=[a+k*b,b+c0,b,lower*(a+k*b)+eps*b+d]
        assert expected==row['nonnegative_coefficients'] and all(x>=0 for x in expected)
        count('r2_coefficient_checks')
    for data in (short,loops):
        for proof in walk_proofs(data):
            weighted(proof)
    candidates=candidates['candidates']
    assert len(candidates)==len(short['domains'])==29
    assert sorted(x['index'] for x in short['domains'])==list(range(29))
    for record in short['domains']:
        candidate_geometry(candidates[record['index']],record)
    coverage(short,candidates)
    guard.check(force=True)
    result=dict(status='PASS',counts=COUNTS,seconds=time.monotonic()-tick,
                inputs=[dict(path=p,sha256=hashlib.sha256(b).hexdigest()) for p,b in zip(inputs,raw)],
                scope='integer interval and coefficient arithmetic; all saved Farkas weights; independently rederived short-prefix geometry and odd exclusions; complete short-domain coverage replay; loop geometry remains the explicit inductive proof plus primary checker')
    target=ROOT/'evidence/d12-classification-audit'
    target.mkdir(exist_ok=True)
    assert not (target/'summary-v2.json').exists()
    # Supporting audit LPs are only used to recheck geometry; each has verified integer dual sums.
    (target/'rederived-proofs-v2.json.gz').write_bytes(gzip.compress(
        json.dumps(AUDIT_PROOFS,default=str,separators=(',',':')).encode(),mtime=0))
    (target/'summary-v2.json').write_text(json.dumps(result,indent=2)+'\n')
    (target/'memory-v2.json').write_text(json.dumps(guard.samples,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
