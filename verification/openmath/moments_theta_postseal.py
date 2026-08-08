"""Post-seal, disclosed: the contraction constant Theta(q,k) of MOMENTS S4 Step 4."""
from fractions import Fraction as Fr
def theta(q,k,I=40):
    d=lambda m: Fr(1,q**(m*(m-1)//2))
    c0=lambda mu: Fr(q-1,q)*Fr(1,1)*(Fr(q,1)**(1-mu-mu*(mu-1)//2) if 1-mu-mu*(mu-1)//2<0 else Fr(q**(1-mu-mu*(mu-1)//2),1))
    def c0f(mu):
        e=1-mu-mu*(mu-1)//2
        return Fr(q-1,q)*(Fr(1,q**(-e)) if e<0 else Fr(q**e,1))
    def alpha(j): return (1-Fr(d(j-1),q**(j-1)))/(1-Fr(d(j),q**(j-1)))
    def beta(m): return Fr(c0f(m-1),q**(m-1))/(1-Fr(d(m),q**(m-1)))
    A=Fr(1)
    for j in range(2*k+1,I): A*=alpha(j)
    S=Fr(0)
    for i in range(2*k,I):
        rho=sum((beta(m) for m in range(i+1,I)),Fr(0))/A
        S+=Fr(q**i)*rho
    return S,A
for q in (2,3,5,7):
    row=[]
    for k in (1,2,3,4):
        S,A=theta(q,k)
        row.append(f'k={k}: Theta={float(S):.6g} (A={float(A):.6f})')
    print(f'q={q}  '+'   '.join(row))
