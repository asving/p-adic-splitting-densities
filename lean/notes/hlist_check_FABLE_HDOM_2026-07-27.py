import itertools, random
from fractions import Fraction as F
from math import gcd, ceil, floor

def lcm(a,b): return a*b//gcd(a,b)

# A (TRI) system: D coords; per coord j: modulus M[j] with allowed residue set R[j];
# floor f[j] in {0,1}; bound[j] = None or (c, {k:a_k}) meaning h_j >= c + sum a_k h_k + 1
class Sys:
    def __init__(s, D, M, R, f, bound):
        s.D,s.M,s.R,s.f,s.bound = D,M,R,f,bound

def brute(s, B):
    pts=set()
    for h in itertools.product(*[range(s.f[j], B+1) for j in range(s.D)]):
        ok=True
        for j in range(s.D):
            if h[j]%s.M[j] not in s.R[j]: ok=False;break
            if s.bound[j] is not None:
                c,co=s.bound[j]
                phi=c+sum(a*h[k] for k,a in co.items())
                if not (h[j]>=phi+1): ok=False;break
        if ok: pts.add(h)
    return pts

def strides(s):
    S=[0]*s.D
    for j in reversed(range(s.D)):
        v=s.M[j]
        for i in range(j+1,s.D):
            if s.bound[i] is not None:
                c,co=s.bound[i]
                if j in co and co[j]>0:
                    v=lcm(v, co[j].denominator*S[i])
        S[j]=v
    return S

def lift(t, r, S):
    # least integer >= t congruent to r mod S ; t rational or int
    t0=ceil(t) if isinstance(t,F) else t
    return t0 + ((r - t0) % S)

# piece: fixed: {j:val}; floorc: {j:int}; resolved: {j:('C',) or ('A',(c,coeffs))}
# bounds live: {j:(c,coeffs over live ks)}; uppers: list of (c,coeffs,limit) meaning c+sum<= limit (cascade mode)
def solve(s, mode, fuel=[0]):
    S=strides(s); out=[]
    cells=itertools.product(*[[r for r in range(S[j]) if r%s.M[j] in s.R[j]] for j in range(s.D)])
    for r in cells:
        st={'fixed':{}, 'floorc':{j:s.f[j] for j in range(s.D)}, 'res':{},
            'bounds':{j:s.bound[j] for j in range(s.D) if s.bound[j] is not None},
            'uppers':[], 'r':r,'S':S}
        stack=[st]
        while stack:
            fuel[0]+=1
            if fuel[0]>2_000_000: raise RuntimeError('fuel')
            P=stack.pop()
            # substitute fixed into bounds
            drop=False
            for j in list(P['bounds']):
                c,co=P['bounds'][j]
                c2=c; co2={}
                for k,a in co.items():
                    if k in P['fixed']: c2+=a*P['fixed'][k]
                    else: co2[k]=a
                if j in P['fixed']:
                    if co2:
                        if mode=='cascade': P['uppers'].append((c2,co2,P['fixed'][j]-1))
                        # literal mode: DROP (data model has no slot)
                    else:
                        if not (P['fixed'][j]>=c2+1): drop=True
                    del P['bounds'][j]
                elif co2: P['bounds'][j]=(c2,co2)
                else:
                    P['floorc'][j]=max(P['floorc'][j], ceil(c2)+1); del P['bounds'][j]
            if drop: continue
            # fixed coords must respect floors/residues
            for j,v in P['fixed'].items():
                if v<s.f[j] or v%s.M[j] not in s.R[j]: drop=True
            if drop: continue
            # cascade: process an upper constraint citing live coords
            if mode=='cascade' and P['uppers']:
                (c,co,lim)=P['uppers'].pop()
                c2=c; co2={}
                for k,a in co.items():
                    if k in P['fixed']: c2+=a*P['fixed'][k]
                    else: co2[k]=a
                if not co2:
                    if c2<=lim: stack.append(P)
                    continue
                k=min(co2)  # enumerate this coord
                lo=lift(P['floorc'][k], r[k], S[k])
                # max value: others at min
                rest=sum(a*lift(P['floorc'][kk],r[kk],S[kk]) for kk,a in co2.items() if kk!=k)
                hi=(F(lim)-c2-rest)/co2[k]
                v=lo
                while v<=hi:
                    Q={'fixed':dict(P['fixed']),'floorc':dict(P['floorc']),'res':dict(P['res']),
                       'bounds':dict(P['bounds']),'uppers':list(P['uppers'])+[(c2,co2,lim)],'r':r,'S':S}
                    Q['fixed'][k]=v
                    if k in Q['res']:
                        if Q['res'][k][0]=='A':
                            cA,coA=Q['res'][k][1]; Q['uppers'].append((cA,dict(coA),v))
                        del Q['res'][k]
                    stack.append(Q); v+=S[k]
                continue
            # find lowest unresolved live coord with an affine bound
            js=[j for j in P['bounds'] if j not in P['fixed']]
            if not js:
                out.append(term_piece(s,P)); continue
            j=min(js); c,co=P['bounds'][j]
            # integerization constant on the cell: use residue point
            pt={k:r[k] for k in co}
            phival=c+sum(a*pt[k] for k,a in co.items())
            crc=ceil(phival)-phival  # ceil(phi)=phi+crc on cell lattice
            Fj=P['floorc'][j]
            # SPLIT: A: phi+crc+1 >= Fj ; B: phi+crc <= Fj-2
            # B side: enumerate all cited live coords in finite box, filter, fix
            lo_vals={}
            okB=True
            limB=F(Fj-2)-crc  # phi <= limB
            for k,a in co.items():
                rest=sum(a2*lift(P['floorc'][k2],r[k2],S[k2]) for k2,a2 in co.items() if k2!=k)
                hi=(limB-c-rest)/a
                lo=lift(P['floorc'][k],r[k],S[k])
                if hi<lo: okB=False;break
                lo_vals[k]=(lo,hi)
            if okB and co:
                ranges=[]
                for k,(lo,hi) in lo_vals.items():
                    vs=[]; v=lo
                    while v<=hi: vs.append((k,v)); v+=S[k]
                    ranges.append(vs)
                for tup in itertools.product(*ranges):
                    val=c+sum(a*dict(tup)[k] for k,a in co.items())
                    if not (val<=limB): continue
                    Q={'fixed':dict(P['fixed']),'floorc':dict(P['floorc']),'res':dict(P['res']),
                       'bounds':dict(P['bounds']),'uppers':list(P['uppers']),'r':r,'S':S}
                    for k,v in tup:
                        Q['fixed'][k]=v
                        if k in Q['res']:
                            if Q['res'][k][0]=='A':
                                cA,coA=Q['res'][k][1]; Q['uppers'].append((cA,dict(coA),v))
                            del Q['res'][k]
                    del Q['bounds'][j]
                    Q['floorc'][j]=max(Q['floorc'][j], ceil(val)+1)  # constant bound merges (<=Fj-1 anyway)
                    stack.append(Q)
            # A side: slab decomposition over cited coords, in level order
            def slab(P0, cited, t0):
                # condition: sum_{k in cited} a_k h_k >= t0 (nonneg a); spawn pieces
                if not cited:
                    if 0>=t0: stack.append(P0)
                    return
                k=cited[0]; a=co[k]
                rest=sum(co[k2]*lift(P0['floorc'][k2],r[k2],S[k2]) for k2 in cited[1:])
                T=(F(t0)-rest)/a  # solo threshold value for h_k
                Tl=lift(T, r[k], S[k])
                # slab: h_k >= Tl, condition implied
                Q={'fixed':dict(P0['fixed']),'floorc':dict(P0['floorc']),'res':dict(P0['res']),
                   'bounds':dict(P0['bounds']),'uppers':list(P0['uppers']),'r':r,'S':S}
                if Tl>Q['floorc'][k]:
                    Q['floorc'][k]=Tl
                    if k in Q['res'] and Q['res'][k][0]=='A':
                        Q['bounds'][k]=Q['res'][k][2]; del Q['res'][k]  # re-split at level k with orig bound
                stack.append(Q)
                # below: fix h_k, recurse
                v=lift(P0['floorc'][k],r[k],S[k])
                while v<Tl:
                    Q2={'fixed':dict(P0['fixed']),'floorc':dict(P0['floorc']),'res':dict(P0['res']),
                        'bounds':dict(P0['bounds']),'uppers':list(P0['uppers']),'r':r,'S':S}
                    Q2['fixed'][k]=v
                    if k in Q2['res']:
                        if Q2['res'][k][0]=='A':
                            cA,coA=Q2['res'][k][1]; Q2['uppers'].append((cA,dict(coA),v))
                        del Q2['res'][k]
                    slab(Q2, cited[1:], t0-a*v)
                    v+=S[k]
            PA={'fixed':dict(P['fixed']),'floorc':dict(P['floorc']),'res':dict(P['res']),
                'bounds':dict(P['bounds']),'uppers':list(P['uppers']),'r':r,'S':S}
            del PA['bounds'][j]
            PA['res'][j]=('A',(c+crc+1,dict(co)),(c,dict(co)))  # phi_up ; orig bound kept for re-splits
            t0=F(Fj-1)-crc-c
            slab(PA, sorted(co), t0)
    return out

def term_piece(s,P):
    r,S=P['r'],P['S']
    for j in range(s.D):
        if j not in P['fixed'] and j not in P['res']:
            P['res'][j]=('C',)
    return P

def gen_points(s,P,B):
    r,S=P['r'],P['S']; pts=[]
    def rec(j,h):
        if j==s.D: pts.append(tuple(h)); return
        if j in P['fixed']:
            v=P['fixed'][j]
            if v>B: return
            rec(j+1,h+[v])
        elif P['res'][j][0]=='C':
            v=lift(P['floorc'][j],r[j],S[j])
            while v<=B: rec(j+1,h+[v]); v+=S[j]
        else:
            c,co=P['res'][j][1]
            phi1=c+sum(a*h[k] for k,a in co.items())
            v=lift(phi1, r[j], S[j])
            v=max(v, lift(P['floorc'][j],r[j],S[j]))  # should coincide on A side; check
            v0=lift(phi1,r[j],S[j])
            assert v==v0, ('floor exceeded affine lift', P)
            while v<=B: rec(j+1,h+[v]); v+=S[j]
    rec(0,[])
    return pts

def check(s,B,mode='cascade',verbose=False):
    bf=brute(s,B); pieces=solve(s,mode)
    allpts=[]; per=[]
    for P in pieces:
        pts=gen_points(s,P,B); per.append(set(pts)); allpts+=pts
    un=set(allpts)
    dup=len(allpts)-len(un)
    strays=un-bf; orphans=bf-un
    return bf,un,dup,strays,orphans,pieces

random.seed(7)
def rnd_sys(D):
    M=[random.choice([1,1,2,3,4]) for _ in range(D)]
    R=[set(random.sample(range(m), random.randint(1,m))) for m in M]
    f=[random.choice([0,1]) for _ in range(D)]
    bound=[None]*D
    for j in range(1,D):
        if random.random()<0.8:
            ks=random.sample(range(j), random.randint(1,j))
            co={k:F(random.randint(0,3),random.randint(1,3)) for k in ks}
            co={k:a for k,a in co.items() if a>0}
            if co: bound[j]=(F(random.randint(-6,3)),co)
    return Sys(D,M,R,f,bound)

def run(name,s,B=24,mode='cascade'):
    bf,un,dup,strays,orphans,pieces=check(s,B,mode)
    status='OK' if (dup==0 and not strays and not orphans) else 'FAIL'
    print(f'{name}: {status} |bf|={len(bf)} pieces={len(pieces)} dup={dup} strays={sorted(strays)[:4]} orphans={sorted(orphans)[:4]}')
    return status

print('== displayed examples ==')
# refuting instance: y >= x/2+1, x=y=0 mod 2
run('refute-inst', Sys(2,[2,2],[{0},{0}],[0,0],[None,(F(0),{0:F(1,2)})]))
# (E3) y >= x/2-1/2  -> phi = x/2-3/2
run('E3', Sys(2,[1,1],[{0},{0}],[0,0],[None,(F(-3,2),{0:F(1,2)})]))
# (E1) y >= x-2 -> phi=x-3
run('E1', Sys(2,[1,1],[{0},{0}],[0,0],[None,(F(-3),{0:F(1)})]))
# gate family: floors 1, h1 odd, h1 >= 2h0+1 -> phi=2h0
run('gate', Sys(2,[1,2],[{0},{1}],[1,1],[None,(F(0),{0:F(2)})]))
print('== break attempt (E5): y>=x+1, z>=y-5 ==')
E5=Sys(3,[1,1,1],[{0},{0},{0}],[0,0,0],[None,(F(0),{0:F(1)}),(F(-6),{1:F(1)})])
run('E5-literal',E5,20,'literal')
run('E5-cascade',E5,20,'cascade')
print('== random stress (cascade) ==')
bad=0
for i in range(400):
    s=rnd_sys(random.choice([2,3]))
    try:
        st=run(f'rnd{i}',s,20)
        if st!='FAIL' : pass
        else: bad+=1
    except RuntimeError as e:
        print(f'rnd{i}: FUEL'); bad+=1
print('random failures:',bad)
