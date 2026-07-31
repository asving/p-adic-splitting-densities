\\ M02 T2: exact-square family (X-b)^2, b=3, p=3 — lifts realize distinct types
p = 3; b = 3;
certif(f) = {
  my(fac = factorpadic(f, p, 60), out = []);
  for (i = 1, #fac[,1],
    my(g = fac[i,1], d = poldegree(g), e, fdeg);
    \\ for deg-1 factors: (e,f)=(1,1). For deg-2 irreducible over Q_3:
    \\ ramified iff v_3(disc g) is odd
    if (d == 1, out = concat(out, [[1,1]]),
      my(vd = valuation(poldisc(g), p));
      if (vd % 2 == 1, out = concat(out, [[2,1]]), out = concat(out, [[1,2]])));
  );
  vecsort(out);
}
print("pert +3^9  (odd-val):   ", certif((x-b)^2 + 3^9));
print("pert -3^8  (QR resid):  ", certif((x-b)^2 - 3^8));
print("pert -2*3^8 (nonQR):    ", certif((x-b)^2 - 2*3^8));
\\ scaling count check: exact squares (X-b')^2 with b' = 3(1+3s) mod 3^N: count = 3^(N-2)
for (N = 2, 6, print("N=", N, "  #S_N = ", 3^(N-2), "  (p^2-scaling would need ", 3^(2*(N-2)), " rel. N=2)"));
quit
