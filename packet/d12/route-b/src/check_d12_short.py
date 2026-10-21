"""Derive valid domains for fixed affine prefixes, then prove finite coverage."""
import hashlib
import json
from pathlib import Path
import resource
import signal
import time
from fractions import Fraction as Q
import d12_affine2 as a
from d12_affine2 import (ZERO,constant,fadd,fsub,scale,vadd,vsub,along,translate,
                        rotate,point,rows,ev,vev,crossfd,norm,turn)
from affine2 import simplify,serialize,normalize
from d12_affine2 import contradiction
from mac_memory_guard import Guard

R,S=(1,0,0),(0,1,0)
BASE=[(1,0,-2),(0,1,-2)]
ATLAS=None
STARTS=[(0,(-1,0),(-1,1)),(0,(-1,1),(-1,0)),(0,(-1,1),(0,1)),
        (0,(0,1),(-1,1)),(0,(0,1),(1,0)),(0,(1,0),(0,1)),
        (1,(-1,1),(0,1)),(1,(0,1),(-1,1)),(1,(0,1),(1,0)),(1,(1,0),(0,1))]


def clean(forms):
    return [normalize(f) for f in simplify(forms)]


def sample_edge(f,p,g,q,sample,other=()):
    poly=ATLAS['polygons'][f]
    for i,u in enumerate(poly):
        target,k,z=ATLAS['maps'][f,i]
        if target!=g:
            continue
        v=poly[(i+1)%12]
        d,L=a.unit_segment(u,v)
        axis=0 if d[0] else 1
        delta=vsub(p,u)
        t=scale(delta[axis],d[axis])
        if (ev(crossfd(delta,d),*sample)==0 and ev(t,*sample)>=0
                and ev(fsub(L,t),*sample)>=0
                and vev(vadd(rotate(p,k),z),*sample)==vev(q,*sample)
                and all(ev(crossfd(vsub(w,u),d),*sample)==0
                        and ev(scale(vsub(w,u)[axis],d[axis]),*sample)>=0
                        and ev(fsub(L,scale(vsub(w,u)[axis],d[axis])),*sample)>=0
                        for w in other)):
            return i,k,z
    raise AssertionError(('no sample edge',f,p,g,q,sample))


def derive(case):
    """Return sufficient linear conditions; all candidate samples must satisfy them."""
    runs,total=a.convert(case)
    rr=rows(runs)
    sample=case['sample_points'][0]
    domain=list(BASE)
    equations=list(map(tuple,case['sample_equalities']))
    checks=[]
    def equal(p,q):
        equations.extend(vsub(p,q))
    def edge_point(f,edge,p):
        poly=ATLAS['polygons'][f]
        d,L=a.unit_segment(poly[edge],poly[(edge+1)%12])
        delta=vsub(p,poly[edge])
        axis=0 if d[0] else 1
        t=scale(delta[axis],d[axis])
        equations.append(crossfd(delta,d))
        domain.extend([t,fsub(L,t)])
    first=runs[0]
    assert first['a']==(ZERO,ZERO)
    assert (first['face'],first['d'],first['e'])==STARTS[case['start']]
    for i,b in enumerate(runs):
        assert norm(b['d'])==norm(b['e'])==norm(tuple(x-y for x,y in zip(b['d'],b['e'])))==1
        domain.append(fsub(b['length'],constant(3 if i<len(runs)-1 else 1)))
    for row in rr:
        if row['hi']==constant(-1):
            continue
        for t in (row['lo'],row['hi']):
            p=vadd(row['a'],along(row['d'],t))
            domain.extend(a.halfplanes(ATLAS,row['face'],p))
    for i,(old,new) in enumerate(zip(runs,runs[1:])):
        tail=[point(old,fsub(old['length'],constant(j))) for j in (3,2,1)]
        predicted=vsub(vadd(tail[1],tail[2]),tail[0])
        edge,k,z=sample_edge(old['face'],tail[2],new['face'],
                            # Image of tail[2] is one step before new[0].
                            vsub(point(new,constant(1)),along(new['d'],constant(1))),
                            sample,other=tail[1:2])
        edge_point(old['face'],edge,tail[1])
        edge_point(old['face'],edge,tail[2])
        moved=[vadd(rotate(p,k),z) for p in tail[1:]]
        q0=point(new,ZERO);q1=point(new,constant(1));q2=point(new,constant(2))
        equal(vadd(rotate(predicted,k),z),q0)
        equal(vsub(vadd(moved[1],q0),moved[0]),q1)
        equal(vsub(vadd(q0,q1),moved[1]),q2)
        checks.append(dict(kind='join',index=i,edge=edge,rotation=k))
    target=runs[case['repeat_block']]
    local=fsub(tuple(case['repeat_index']),target['base'])
    assert local[-1]%2==case['repeat_parity']
    domain.extend([local,fsub(fsub(target['length'],constant(1)),local),
                   fsub(fsub(total,constant(2)),tuple(case['repeat_index']))])
    p=point(target,local)
    end=point(runs[-1],fsub(runs[-1]['length'],constant(1)))
    if target['face']==runs[-1]['face']:
        equal(p,end)
    else:
        edge,k,z=sample_edge(target['face'],p,runs[-1]['face'],end,sample)
        edge_point(target['face'],edge,p)
        equal(vadd(rotate(p,k),z),end)
        checks.append(dict(kind='repeat',edge=edge,rotation=k))
    domain += [z for e in equations for z in (e,scale(e,-1))]
    assert all(ev(f,*sample)>=0 for f in domain), (
        'raw constraints exclude sample',sample,[f for f in domain if ev(f,*sample)<0])
    domain=clean(domain)
    assert all(all(ev(f,*sample)>=0 for f in domain) for sample in case['sample_points']), (
        'derived domain excludes a sample',case['start'],domain)
    return domain,runs,checks


def no_odd_corners(domain,runs,label):
    a.DOMAIN=domain
    rr=rows(runs)
    for i,row in enumerate(rr):
        if row['global_parity']!=1:
            continue
        row=dict(row)
        # The last point is already repeated and cannot be a legal endpoint.
        last=runs[-1]
        if row['block']==len(runs)-1 and row['parity']==(last['length'][-1]-1)%2:
            row['hi']=fsub(row['hi'],constant(1))
        for j,p in enumerate(ATLAS['polygons'][row['face']]):
            # Any return to the starting pentagon already repeats a vertex.
            if ATLAS['cells'][row['face']][j]==0:
                continue
            a.empty(f'{label}/odd-{i}-{j}',*a.hit_point(row,p))


def safe_domains(domain,runs,proof):
    """Discard parameter subdomains where this (possibly overlong) prefix hits a pentagon."""
    domains=[domain]
    for row in rows(runs):
        if row['global_parity']!=1:
            continue
        row=dict(row)
        if row['block']==len(runs)-1 and row['parity']==(runs[-1]['length'][-1]-1)%2:
            row['hi']=fsub(row['hi'],constant(1))
        for j,p in enumerate(ATLAS['polygons'][row['face']]):
            if ATLAS['cells'][row['face']][j]==0:
                continue
            inequalities,equalities=a.hit_point(row,p)
            bad=list(inequalities)+[z for e in equalities for z in (e,scale(e,-1))]
            next_domains=[]
            for cell in domains:
                intersect=clean(cell+bad)
                cert=contradiction(intersect)
                if cert is not None:
                    next_domains.append(cell)
                else:
                    next_domains.extend(subtract(cell,bad,proof['empty_proofs']))
            domains=next_domains
    return domains


def subtract(domain,cut,proofs):
    """Integer partition: D\\{f>=0 for all f in cut}; no sampling."""
    current=list(domain)
    out=[]
    for f in cut:
        outside=clean(current+[fsub(scale(f,-1),constant(1))])
        certificate=contradiction(outside)
        if certificate is None:
            out.append(outside)
        else:
            proofs.append(dict(forms=outside,**certificate))
        current=clean(current+[f])
        certificate=contradiction(current)
        if certificate is not None:
            proofs.append(dict(forms=current,**certificate))
            break
    return out


def main():
    global ATLAS
    signal.alarm(240)
    guard=Guard(512*1024**2)
    guard.check(start=True)
    tick=time.monotonic()
    out=Path(__file__).resolve().parents[1]/'evidence/d12-short'
    target=out/'symbolic-check-v5.json'
    assert not target.exists()
    raw=(out/'candidates-v2.json').read_bytes()
    candidates=json.loads(raw)['candidates']
    a.DOMAIN=BASE
    ATLAS=a.symbolic_atlas(R,S)
    result=dict(status='RUNNING',input_sha256=hashlib.sha256(raw).hexdigest(),
                domains=[],coverage=[],constraints=a.RECORDS)
    try:
        derived=[]
        for i,case in enumerate(candidates):
            a.DOMAIN=BASE
            domain,runs,checks=derive(case)
            derived.append((case,domain,runs))
            result['domains'].append(dict(index=i,start=case['start'],domain=domain,checks=checks))
        # Negative half-plane r>=s plus all six short starts in s>=r+2.
        regions=[
            ('s_eq_r',[(1,-1,0),(-1,1,0)],range(10)),
            ('s2_to_rminus2_below3',[(1,-1,-2),(-1,3,-2)],range(10)),
            ('r_eq_3s',[(1,-3,0),(-1,3,0)],range(10)),
            ('r_above_3s',[(1,-3,-2)],range(10)),
            ('s_above_r', [(-1,1,-2)],(1,2,5,7,8,9)),
        ]
        for name,region,starts in regions:
            for start in starts:
                remaining=[clean(BASE+region)]
                proof=dict(region=name,start=start,initial=remaining[0],steps=[],empty_proofs=[])
                for i,(case,domain,runs) in enumerate(derived):
                    if case['start']!=start:
                        continue
                    intersection=clean(BASE+region+domain)
                    if contradiction(intersection) is not None:
                        continue
                    for safe in safe_domains(intersection,runs,proof):
                        no_odd_corners(safe,runs,f'{name}-{start}-{i}')
                        new=[]
                        for residual in remaining:
                            new.extend(subtract(residual,safe,proof['empty_proofs']))
                        proof['steps'].append(dict(candidate=i,domain=safe,
                                                  before=len(remaining),after=len(new)))
                        remaining=new
                        if not remaining:
                            break
                    if not remaining:
                        break
                proof['remaining']=remaining
                result['coverage'].append(proof)
                assert not remaining,('coverage gap',name,start,remaining)
                guard.check()
        result['status']='SYMBOLIC_CERTIFICATE_PASS'
    except Exception as error:
        result.update(status='UNPROVED',failure=repr(error))
        raise
    finally:
        result['seconds']=time.monotonic()-tick
        result['peak_rss_bytes']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        target.write_text(json.dumps(serialize(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('domains','coverage','constraints')}))


if __name__=='__main__':
    main()
