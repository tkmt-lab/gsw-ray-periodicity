"""Extension of our block certificates: r>=2 for epsilon=+1, r>=3 for -1."""
import json,signal
from dataclasses import dataclass
from pathlib import Path
from d12_witness import block

@dataclass(frozen=True)
class F:
    c:tuple
    def __add__(self,o):
        if isinstance(o,int): o=F((0,0,0,o))
        return F(tuple(a+b for a,b in zip(self.c,o.c)))
    __radd__=__add__
    def __mul__(self,k): return F(tuple(a*k for a in self.c))
    __rmul__=__mul__
    def __neg__(self): return self*-1
    def __sub__(self,o): return self+-o
    def __rsub__(self,o): return -self+o

R,S,H=F((1,0,0,0)),F((0,1,0,0)),F((0,0,1,0))
def form(x): return x if isinstance(x,F) else F((0,0,0,x))
def point(p): return tuple(form(x) for x in p)
def plus(p,q): return tuple(form(x)+y for x,y in zip(p,q))
def step(b,t): return plus(b['start'],tuple(form(t)*v for v in b['d']))
def turn(p,k):
    x,y=point(p)
    for _ in range(k%6): x,y=-y,x+y
    return x,y

def transform(p,k,z): return plus(turn(p,k),z)
def replace_h(f,value):
    f=form(f)
    return F((f.c[0],f.c[1],0,f.c[3]))+value*f.c[2]

def inequalities(face,p):
    x,y=point(p);L=R+2*S
    if face==0: return [S-x,2*L-y,R+3*S-x-y,y,x+2*R+3*S,x+y+R+S]
    return [L-x,2*L-y,2*L-x-y,y,x+L,x+y]

def nonnegative(f,k,epsilon):
    a,b,c,d=form(f).c
    # r=lower+U, h=V, s=h+k*r+epsilon+W, U,V,W>=0.
    lower=2 if epsilon==1 else 3
    coeff=(a+k*b,b+c,b,lower*(a+k*b)+epsilon*b+d)
    return all(x>=0 for x in coeff),coeff

certificates=[]
def certify(f,k,epsilon,label):
    ok,coef=nonnegative(f,k,epsilon)
    assert ok,(label,form(f).c,k,epsilon,coef)
    certificates.append(dict(label=label,form=form(f).c,k=k,epsilon=epsilon,nonnegative_coefficients=coef))

def inside(face,p,k,epsilon): return all(nonnegative(f,k,epsilon)[0] for f in inequalities(face,p))
def certify_inside(face,p,k,epsilon,label):
    for i,f in enumerate(inequalities(face,p)): certify(f,k,epsilon,f'{label}/edge{i}')

def unit(delta):
    x,y=point(delta)
    assert x.c[:3]==y.c[:3]==(0,0,0)
    assert (x.c[3],y.c[3]) in {(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)}

def main():
    signal.alarm(115)
    L=R+2*S;D=R+S;C=2*R+3*S
    joins=[]
    for eps in (-1,1):
        for parity in (0,1):
            for kind in ('E','O'):
                b=block(R,S,H,parity,eps,kind)
                certify(b['length']-1,1,eps,f'length/{eps}/{parity}/{kind}')
                for t in (0,b['length']-1):
                    even=step(b,t)
                    for odd in (0,1):
                        p=plus(even,tuple(odd*v for v in b['e']))
                        certify_inside(b['face'],p,1,eps,f'block/{eps}/{parity}/{kind}/{t}/{odd}')
                for delta in [b['d'],b['e'],tuple(x-y for x,y in zip(b['d'],b['e']))]: unit(delta)
                if kind=='E':
                    next_block=block(R,S,H,parity,eps,'O')
                    rot=5
                    off=(-2*R-5*S,R+4*S) if parity==0 else (C,-L)
                    edge_start=(S,L) if parity==0 else (-C,L)
                    edge_end=(-R,C) if parity==0 else (-L,S)
                    direction=(-1,1) if parity==0 else (1,-1)
                    edge_length=D
                    k=1
                else:
                    next_block=block(R,S,H+R,1-parity,eps,'E')
                    rot=4
                    off=(-4*R-6*S,4*L) if parity==0 else (0,0)
                    edge_start=(S,C) if parity==0 else (-S,S)
                    edge_end=(0,2*L) if parity==0 else (0,0)
                    direction=(-1,1) if parity==0 else (1,-1)
                    edge_length=S
                    k=2 if eps==-1 else 1
                expected_ends=([(-L,R+3*S),(-L,2*L)] if parity==0 else [(L,D),(L,0)]) if kind=='E' else ([(-C,2*L),(-2*D,2*L)] if parity==0 else [(S,0),(0,0)])
                assert [transform(edge_start,rot,off),transform(edge_end,rot,off)]==[point(p) for p in expected_ends]
                u=step(b,b['length']);v=plus(u,b['e'])
                assert transform(u,rot,off)==point(next_block['start'])
                assert turn(b['d'],rot)==point(next_block['d'])
                assert turn(b['e'],rot)==point(next_block['e'])
                x=step(b,b['length']-1);y=plus(x,b['e'])
                choices=[]
                for index,(tri,owners) in enumerate([([x,y,u],[0,0,1]),([y,u,v],[0,1,1])]):
                    selected=next((side for side in (0,1) if all(inside(b['face'] if side==0 else next_block['face'],p if side==0 else transform(p,rot,off),k,eps) for p in tri)),None)
                    assert selected is not None,(eps,parity,kind,index)
                    for n,(p,owner) in enumerate(zip(tri,owners)):
                        target=p if selected==0 else transform(p,rot,off)
                        certify_inside(b['face'] if selected==0 else next_block['face'],target,k,eps,f'join/{eps}/{parity}/{kind}/{index}/{n}')
                        if owner!=selected:
                            delta=tuple(form(a)-z for a,z in zip(p,edge_start))
                            parameter=delta[0]*direction[0]
                            assert delta==tuple(parameter*v for v in direction)
                            certify(parameter,k,eps,'shared-edge-start')
                            certify(edge_length-parameter,k,eps,'shared-edge-end')
                    for a,c in [(0,1),(0,2),(1,2)]: unit(tuple(p-q for p,q in zip(tri[a],tri[c])))
                    choices.append(selected)
                joins.append(dict(epsilon=eps,parity=parity,kind=kind,rotation=rot,offset=[form(x).c for x in off],triangle_faces=choices))
    # The last O block for the minus sign terminates at boundary label 7 or 1.
    for parity in (0,1):
        b=block(R,S,S-R+1,parity,-1,'O')
        endpoint=plus(step(b,b['length']-1),b['e'])
        assert endpoint==point((S,C) if parity==0 else (-S,S))
    # Plus ends with a single E pair, at label 1 or 7 in face 0.
    for parity in (0,1):
        b=block(R,S,S-1,parity,1,'E')
        a=point(b['start']);end=plus(a,b['e'])
        assert end==point((S,0) if parity==0 else (-C,2*L))
        for p in (a,end): certify_inside(0,p,1,1,'terminal-plus-pair')
    out=Path(__file__).resolve().parents[1]/'evidence/d12-positive-r2'
    out.mkdir(exist_ok=False)
    for name,obj in [('affine-certificates',certificates),('joins',joins)]:
        (out/f'{name}.json').write_text(json.dumps(obj,indent=2)+'\n')
    result=dict(status='PASS',main_block_types=8,join_types=len(joins),nonnegative_affine_certificates=len(certificates),endpoint_cases=4,
                domain='r>=2 for epsilon=+1; r>=3 for epsilon=-1; q>=1; simplicity proved separately')
    (out/'symbolic-summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__': main()
