"""Explicit D12 witness blocks fixed in plan-037; no path search."""
def block(r,s,h,parity,epsilon,kind):
    L=r+2*s; B=r+3*s
    if kind=='E':
        start=(h,0) if parity==0 else (-L-h-r,2*L)
        d=(0,1) if parity==0 else (0,-1)
        e=((-1,1) if parity==0 else (1,-1)) if epsilon==-1 else ((1,0) if parity==0 else (-1,0))
        length=B-h
        face=0
    else:
        start=(-L,r+4*s-h) if parity==0 else (L,h+r)
        d=(1,0) if parity==0 else (-1,0)
        e=((0,1) if parity==0 else (0,-1)) if epsilon==-1 else ((1,-1) if parity==0 else (-1,1))
        length=L+h+r
        face=1
    return dict(face=face,start=start,d=d,e=e,length=length)


def blocks(r,q,epsilon):
    assert r>=3 and q>=1 and epsilon in (-1,1)
    s=q*r+epsilon
    answer=[]
    for j in range(q):
        for kind in ('E','O'):
            answer.append(block(r,s,j*r,j%2,epsilon,kind))
    if epsilon==1:
        last=block(r,s,q*r,q%2,epsilon,'E')
        last['length']=1
        answer.append(last)
    return answer
