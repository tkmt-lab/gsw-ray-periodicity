"""Inductive E/O strip certificate for the two remaining D12 starts."""
import hashlib
import json
from pathlib import Path
import resource
import signal
import time
import d12_affine3 as a
from d12_affine3 import (ZERO,constant,fadd,fsub,scale,vadd,vsub,translate,
                        rotate,along,point,rows,ev,vev,crossfd,norm,turn)
from affine2 import serialize
from verify_d12_blocks import F, form
from d12_witness import block
from d12_atlas_trace import D12Atlas
from mac_memory_guard import Guard

R,S,H=F((1,0,0,0)),F((0,1,0,0)),F((0,0,1,0))
L=R+2*S; B=R+3*S; C=2*R+3*S; D=R+S
BASE=[(R-2).c,(S-2).c,H.c]
ATLAS=None
CHECKS=[]


def vector(p):
    return tuple(form(x).c for x in p)


def make(face,start,d,e,length):
    return dict(face=face,a=vector(start),d=d,e=e,length=form(length).c,base=ZERO)


def eo(h,parity,eps,kind):
    b=block(R,S,h,parity,eps,kind)
    return make(b['face'],b['start'],b['d'],b['e'],2*b['length'])


def mapped(b,g,k,z):
    return dict(b,face=g,a=vadd(rotate(b['a'],k),z),
                d=turn(b['d'],k),e=turn(b['e'],k))


def contains(f,p):
    return all(a.ge(x) for x in a.halfplanes(ATLAS,f,p))


def certify_inside(f,p,label):
    for i,x in enumerate(a.halfplanes(ATLAS,f,p)):
        a.positive(x,f'{label}/edge-{i}')


def certify_block(b,label,exclude_last=False):
    a.positive(fsub(b['length'],constant(3)),f'{label}/length')
    assert norm(b['d'])==norm(b['e'])==norm(tuple(x-y for x,y in zip(b['d'],b['e'])))==1
    for row in rows([b]):
        for name in ('lo','hi'):
            p=vadd(row['a'],along(row['d'],row[name]))
            certify_inside(b['face'],p,f'{label}/{row["parity"]}-{name}')
        if row['parity']==1:
            if exclude_last and (b['length'][-1]-1)%2==1:
                row=dict(row,hi=fsub(row['hi'],constant(1)))
            for i,p in enumerate(ATLAS['polygons'][b['face']]):
                a.empty(f'{label}/odd-corner-{i}',*a.hit_point(row,p))


def certify_join(old,new,edge,label):
    g,k,z=ATLAS['maps'][old['face'],edge]
    assert g==new['face']
    assert all(x%2==0 for x in old['length'])
    x=point(old,fsub(old['length'],constant(2)))
    y=point(old,fsub(old['length'],constant(1)))
    u=point(old,old['length'])
    v=point(old,fadd(old['length'],constant(1)))
    assert vadd(rotate(u,k),z)==new['a'],(label,'start')
    assert turn(old['d'],k)==new['d'] and turn(old['e'],k)==new['e'],(label,'direction')
    poly=ATLAS['polygons'][old['face']]
    edge_a=poly[edge];edge_b=poly[(edge+1)%12]
    direction,length=a.unit_segment(edge_a,edge_b)
    selected=[]
    for j,(tri,owners) in enumerate([([x,y,u],[0,0,1]),([y,u,v],[0,1,1])]):
        side=next((side for side in (0,1) if all(
            contains(old['face'] if side==0 else g,p if side==0 else vadd(rotate(p,k),z))
            for p in tri)),None)
        assert side is not None,(label,'join triangle',j)
        selected.append(side)
        for n,(p,owner) in enumerate(zip(tri,owners)):
            certify_inside(old['face'] if side==0 else g,
                           p if side==0 else vadd(rotate(p,k),z),
                           f'{label}/tri-{j}-point-{n}')
            if owner!=side:
                delta=vsub(p,edge_a)
                axis=0 if direction[0] else 1
                t=scale(delta[axis],direction[axis])
                assert crossfd(delta,direction)==ZERO,(label,'not on seam line')
                a.positive(t,f'{label}/seam-lo')
                a.positive(fsub(length,t),f'{label}/seam-hi')
    CHECKS.append(dict(label=label,edge=edge,rotation=k,triangle_faces=selected))


def antipodal_check():
    # R^3: P0(x,y)=(-x-L-r,2L-y); P1(x,y)=(-x,2L-y).
    z0=vector((-L-R,2*L));z1=vector((0,2*L))
    for eps in (-1,1):
        for kind in ('E','O'):
            b=eo(H,0,eps,kind)
            assert mapped(b,b['face'],3,z0 if b['face']==0 else z1)==eo(H,1,eps,kind)
    for f,z in ((0,z0),(1,z1)):
        for i,p in enumerate(ATLAS['polygons'][f]):
            label=ATLAS['cells'][f][i]
            wanted=ATLAS['polygons'][f][ATLAS['cells'][f].index((label+6)%12)]
            assert vadd(rotate(p,3),z)==wanted
    CHECKS.append(dict(label='P=R^3',corners=24,block_correspondences=4))


def entry_checks():
    a.DOMAIN=BASE
    prefix0=make(0,(0,0),(-1,0),(-1,1),2*D)
    prefix6=make(1,(0,0),(-1,1),(0,1),2*L)
    first=eo(F((0,0,0,0)),0,1,'E')
    # K=R^-1 J: face0 to face1 +(D,0), label i -> 11-i.
    kfirst=mapped(first,1,0,vector((D,0)))
    # R: face0 to face0 T+(s,D), label i -> i+2.
    rfirst=mapped(first,0,1,vector((S,D)))
    certify_block(prefix0,'entry-0')
    certify_block(prefix6,'entry-6')
    certify_join(prefix0,kfirst,10,'entry-0-to-K4')
    certify_join(prefix6,rfirst,9,'entry-6-to-R4')
    for f in (0,1):
        g=1-f;z=vector((D if f==0 else -D,0))
        for i,p in enumerate(ATLAS['polygons'][f]):
            label=ATLAS['cells'][f][i]
            q=ATLAS['polygons'][g][ATLAS['cells'][g].index((11-label)%12)]
            assert vadd(p,z)==q
    CHECKS.append(dict(label='K=R^-1 J',corners=24,initial_prefix_lengths=[(2*D).c,(2*L).c]))


def loop_checks():
    for eps in (-1,1):
        # Remaining width is at least r for minus, r+2 for plus.
        slack=0 if eps==-1 else 2
        a.DOMAIN=BASE+[(S-H-R-slack).c]
        E=eo(H,0,eps,'E');O=eo(H,0,eps,'O')
        nextE=eo(H+R,1,eps,'E')
        certify_block(E,f'cycle-{eps}/E')
        certify_block(O,f'cycle-{eps}/O')
        certify_join(E,O,3,f'cycle-{eps}/E-O')
        certify_join(O,nextE,5,f'cycle-{eps}/O-E')
        CHECKS.append(dict(label=f'cycle-{eps}',domain=a.DOMAIN,blocks=[E,O,nextE]))
    for eps in (-1,1):
        domains=[
            ('interior',BASE+[(H-R).c,(S-H-2).c,(R-S+H-2).c]),
            ('edge',BASE+[(H-R).c]+(
                [(S-H).c,(H-S).c] if eps==-1
                else [(S-H-R).c,(H+R-S).c]))
        ]
        for name,domain in domains:
            a.DOMAIN=domain
            E=eo(H,0,eps,'E');O=eo(H,0,eps,'O')
            W=make(0,(-C,R+5*S-H),(1,-1),
                   (1,0) if eps==-1 else (0,-1),
                   2*(R+S-H)-(0 if eps==-1 else 1))
            for kind,b in [('E',E),('O',O),('W',W)]:
                certify_block(b,f'terminal-{eps}-{name}/{kind}',exclude_last=kind=='W')
            certify_join(E,O,3,f'terminal-{eps}-{name}/E-O')
            certify_join(O,W,4,f'terminal-{eps}-{name}/O-W')
            # P^m of the earlier E_(m-1) has opposite orientation and parameter h-r.
            prev=eo(H-R,1,eps,'E')
            previous_index=4*R-(2 if eps==-1 else 1)
            end=point(W,fsub(W['length'],constant(1)))
            repeated=point(prev,previous_index.c)
            assert end==repeated,(eps,name,'repeat identity')
            a.positive(previous_index.c,f'terminal-{eps}-{name}/repeat-lo')
            a.positive(fsub(fsub(prev['length'],constant(1)),previous_index.c),
                       f'terminal-{eps}-{name}/repeat-hi')
            CHECKS.append(dict(label=f'terminal-{eps}-{name}',domain=domain,blocks=[E,O,W],
                               previous_E=prev,previous_index=previous_index.c,repeated_point=end))


def replay():
    """Pre-fixed finite QA, including both parities and remainder-zero boundaries."""
    out=[]
    for r in (2,3,4,5,8,11):
        for s in sorted({2*r,3*r,2*r+2,3*r+2,2*r+max(2,r-2)}):
            if s>80 or s<r+2 or s%r in (1,r-1):
                continue
            for eps,start in ((-1,3),(1,4)):
                m=s//r if eps==-1 else (s-2)//r
                h=m*r
                atlas=D12Atlas(r,s)
                f,tri=atlas.starts(0)[start]
                wanted=[]
                for j in range(m+1):
                    for kind in ('E','O'):
                        b=block(r,s,j*r,j%2,eps,kind)
                        for k in range(2*b['length']):
                            p=tuple(b['start'][i]+(k//2)*b['d'][i]+(k%2)*b['e'][i] for i in (0,1))
                            wanted.append(atlas.key(b['face'],p))
                wlen=2*(r+s-h)-(0 if eps==-1 else 1)
                for k in range(wlen):
                    e=(1,0) if eps==-1 else (0,-1)
                    p=(-2*r-3*s+k//2+(k%2)*e[0],
                       r+5*s-h-k//2+(k%2)*e[1])
                    if m%2:
                        p=(-p[0]-(r+2*s)-r,2*(r+2*s)-p[1])
                    wanted.append(atlas.key(0,p))
                actual=[]
                for i,key in enumerate(wanted):
                    if i<3:
                        q=atlas.key(f,tri[i])
                    else:
                        f,tri=atlas.step(f,tri)
                        q=atlas.key(f,tri[-1])
                    assert q==key,(r,s,eps,i,q,key)
                    if i%2==1 and i<len(wanted)-1:
                        assert q[0]!='v',(r,s,eps,i,'odd corner')
                    actual.append(q)
                assert actual[-1] in actual[:-1]
                out.append(dict(r=r,s=s,epsilon=eps,m=m,vertices=len(actual),
                                sha256=hashlib.sha256(json.dumps(actual).encode()).hexdigest()))
    return out


def main():
    global ATLAS
    signal.alarm(180)
    guard=Guard(512*1024**2);guard.check(start=True)
    tick=time.monotonic()
    out=Path(__file__).resolve().parents[1]/'evidence/d12-loops'
    out.mkdir(exist_ok=False)
    result=dict(status='RUNNING',checks=CHECKS,constraints=a.RECORDS)
    try:
        a.DOMAIN=BASE
        ATLAS=a.symbolic_atlas(R.c,S.c)
        antipodal_check()
        entry_checks()
        loop_checks()
        result['replays']=replay()
        result['status']='SYMBOLIC_CERTIFICATE_PASS'
    except Exception as error:
        result.update(status='UNPROVED',failure=repr(error))
        raise
    finally:
        guard.check(force=True)
        result['seconds']=time.monotonic()-tick
        result['peak_rss_bytes']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        (out/'symbolic-check.json').write_text(json.dumps(serialize(result),indent=2)+'\n')
        (out/'memory.json').write_text(json.dumps(guard.samples,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('constraints','checks','replays')}))
    print('constraints',len(a.RECORDS),'checks',len(CHECKS),'replays',len(result['replays']))


if __name__=='__main__':
    main()
