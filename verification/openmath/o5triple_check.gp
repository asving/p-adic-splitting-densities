\\ O5triple falsifiers (Phase B, 2026-07-31).
\\ T1: Lemma STEEP verdict-constancy at ORDER-1 corners: exact-key lift
\\     (j0 = 1) vs steep-finite-side lifts of the same level-N class must
\\     realize the SAME (e,f) multiset.
\\ T2: Lemma STEEP at ORDER-2 (degree-2 Eisenstein key): same constancy;
\\     plus a NEGATIVE control below the certificate band (types are
\\     EXPECTED to vary there -- demonstrates the band is load-bearing).
\\ T3: Theorem A checksum: sum e*f = n and all multiplicities 1 on random
\\     separable samples.
\\ T4: per-factor single-track (Lemma H0 corollary) + order-1 one-sided
\\     polygon for fully x-tracked irreducible factors (Lemma PF surrogate).

fails = 0; checks = 0;
ck(cond, msg) = { checks++; if(!cond, fails++; print("FAIL: ", msg)); }

efof(h, p) = {
  if(poldegree(h) == 1, return([1,1]));
  my(K = nfinit([h, [p]]), pr = idealprimedec(K,p)[1]);
  [pr.e, pr.f]; }

localtype(g, p) = {
  my(fp = factorpadic(g, p, 120), out = List());
  for(i = 1, matsize(fp)[1],
    my(h = liftall(fp[i,1]), m = fp[i,2], ef = efof(h,p));
    for(j = 1, m, listput(out, ef)));
  vecsort(Vec(out)); }

multsOK(g, p) = {
  my(fp = factorpadic(g, p, 120), ok = 1);
  for(i = 1, matsize(fp)[1], if(fp[i,2] != 1, ok = 0));
  ok; }

onesided(F, p) = {
  \\ F monic, Fbar = x^deg: hull from (0,v(a0)) to (deg,0) must be one side
  my(d = poldegree(F), c0 = polcoeff(F,0), ok = 1);
  if(c0 == 0, return(0)); \\ exact key: not a finite-side case, skip as fail-safe
  my(v0 = valuation(c0, p));
  for(i = 1, d-1,
    my(ci = polcoeff(F,i));
    if(ci != 0,
      my(vi = valuation(ci, p));
      if(d*vi < (d-i)*v0, ok = 0)));
  ok; }

\\ ---------- T1: order-1 corner ----------
print("T1: order-1 STEEP corner (exact key vs steep side)");
{
for(ip = 1, 3,
  my(p = [2,3,5][ip]);
  for(M = 2, 4,
    my(base = x^2 + p^M*x, t0 = localtype(base, p));
    ck(t0 == [[1,1],[1,1]], Str("T1 base type p=",p," M=",M," got ",t0));
    for(c = 1, min(p-1, 3),
      for(dE = 1, 2,
        my(g = base + c*p^(2*M+dE));
        ck(localtype(g,p) == t0,
           Str("T1 lift p=",p," M=",M," c=",c," E=",2*M+dE))))));
}
print("  done. checks so far: ", checks, "  fails: ", fails);

\\ ---------- T2: order-2 corner, Eisenstein key ----------
print("T2: order-2 STEEP corner (phi = x^2 - p), + negative control");
negvar = 0; negtot = 0;
{
for(ip = 1, 3,
  my(p = [2,3,5][ip]);
  for(M = 2, 3,
    my(phi = x^2 - p, base = phi^2 - p^M*phi, t0 = localtype(base, p));
    ck(t0 == [[2,1],[2,1]], Str("T2 base type p=",p," M=",M," got ",t0));
    for(c = 1, min(p-1, 2),
      for(dE = 1, 2,
        my(g = base + c*p^(2*M+dE));
        ck(localtype(g,p) == t0,
           Str("T2 lift p=",p," M=",M," c=",c," E=",2*M+dE))));
    for(c = 1, min(p-1, 2),
      my(g = base + c*p^(2*M-1));
      negtot++;
      if(localtype(g,p) != t0, negvar++))));
}
print("  negative control: ", negvar, "/", negtot, " sub-band lifts changed type (nonzero expected; NOT a failure)");
print("  done. checks so far: ", checks, "  fails: ", fails);

\\ ---------- T3: checksum + separable multiplicity 1 ----------
print("T3: checksum sum(e*f) = n and mult-1 on random separable samples");
setrand(20260731);
{
for(ip = 1, 4,
  my(p = [2,3,5,7][ip]);
  for(n = 2, 6,
    my(cnt = 0);
    while(cnt < 25,
      my(g = x^n + sum(i = 0, n-1, random(p^6)*x^i));
      if(poldisc(g) != 0 && valuation(poldisc(g), p) < 40,
        cnt++;
        my(t = localtype(g, p), s = sum(i = 1, #t, t[i][1]*t[i][2]));
        ck(s == n, Str("T3 checksum p=",p," n=",n," g=",g," sum=",s));
        ck(multsOK(g, p), Str("T3 mult p=",p," n=",n," g=",g))))));
}
print("  done. checks so far: ", checks, "  fails: ", fails);

\\ ---------- T4: single-track + one-sided polygon per irreducible factor --
print("T4: per-factor single-track reduction + one-sided NP (x-tracked)");
{
for(ip = 1, 3,
  my(p = [2,3,5][ip]);
  for(trial = 1, 40,
    my(d = 2 + random(4),
       g = x^d + p*sum(i = 0, d-1, random(p^5)*x^i));
    if(poldisc(g) != 0 && valuation(poldisc(g), p) < 40,
      my(fp = factorpadic(g, p, 120));
      for(i = 1, matsize(fp)[1],
        my(F = liftall(fp[i,1]), dF = poldegree(F));
        if(dF >= 1,
          my(fm = factormod(F, p), ndis = matsize(fm)[1]);
          ck(ndis == 1,
             Str("T4 single-track p=",p," F=",F," ndis=",ndis));
          if(dF >= 2 && fm[1,1] == Mod(1,p)*x,
             ck(onesided(F, p), Str("T4 one-sided p=",p," F=",F))))))));
}
print("  done. checks: ", checks, "  fails: ", fails);

print("");
print("O5TRIPLE FALSIFIER SUMMARY: ", checks, " checks, ", fails, " failures.");
if(fails == 0, print("ALL PASS"), print("*** FAILURES PRESENT ***"));
quit;
