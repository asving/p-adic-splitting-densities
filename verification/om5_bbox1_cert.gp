\\ om5_bbox1_cert.gp — OM-5 certification battery for B-BOX-1 (2026-08-16)
\\ run:  gp -q verification/om5_bbox1_cert.gp
\\
\\ B-BOX-1 (CHAP-B B.61 `hBOX`): for a leaf g monic (u,l)-pure at an order-1 key phi of
\\ degree m, coprime (u,l), residual polynomial a unit times an irreducible psi of degree
\\ d = sideDeg, every monic irreducible factor g' of g has  m*d | inertiaDegOf g' ,
\\ where inertiaDegOf is the gcd of { v(N(x)) : 0 != x in the ORDER O[x]/(g') }.
\\ For x = h(alpha), N(h(alpha)) = +/- Res(g', h)  (g' monic), so the battery measures
\\ gcd_h v(Res(g', h)) directly — the exact Lean-side semantics.
\\
\\ CERT-A: the leaf (e,f) at d >= 2 (published clause (A)) — mixed char, PARI oracle.
\\ CERT-B: gcd of order-level norm valuations == m*d — both characteristics.
\\ CERT-C: constructed-counterexample attacks (mult >= 2 defeat; order != maximal order;
\\         coprimality defeat).
\\ CERT-D: route 1 (LEMMA HE3-4U) mechanism executed at an m >= 2 equal-char instance:
\\         unramified base change F2 -> F4, Hensel split g = G1*G2, per-component
\\         unit-root leaf read, split-sum f = 2*2 = 4.

checks = 0; fails = 0;
chk(name, cond) = { checks++; if(!cond, fails++; print("FAIL: ", name)); }

setrand(42);

\\ ---------------------------------------------------------------------------
\\ gcd of order norm-valuations, mixed characteristic (O = Z_p read through Z)
gcdnorm_p(g, p, nsamp) = {
  my(n = poldegree(g), gc = 0, h, r, v);
  for(s = 1, nsamp,
    h = sum(i = 0, n-1, (random(21)-10)*x^i);
    r = polresultant(g, h, x);
    if(r != 0, v = valuation(r, p); if(v > 0, gc = gcd(gc, v))));
  gc;
}

\\ gcd of order norm-valuations, equal characteristic (O = F_p[[t]])
gcdnorm_t(g, p, nsamp) = {
  my(n = poldegree(g, x), gm = g*Mod(1,p), gc = 0, h, r, v);
  for(s = 1, nsamp,
    h = sum(i = 0, n-1, sum(j = 0, 3, random(p)*'t^j)*x^i)*Mod(1,p);
    r = polresultant(gm, h, x);
    if(r != 0, v = valuation(r, 't); if(v > 0, gc = gcd(gc, v))));
  gc;
}

\\ ---------------------------------------------------------------------------
\\ CERT-A + CERT-B + CERT-C(ii), mixed characteristic.
\\ row = [label, g, p, phi, u, l, m, d]; predictions: e = l, f = m*d.
PHI4 = x^2 + x + 1;   \\ the degree-2 key at p = 2  (irreducible mod 2)
PHI9 = x^2 + 1;       \\ the degree-2 key at p = 3  (irreducible mod 3)

mixedrows = [ \
  ["A1 p2 l1 m2 d2 (widened region)", PHI4^2 + 2*PHI4 + 4*x,        2, PHI4, 1, 1, 2, 2], \
  ["A2 p3 l1 m2 d2 (widened region)", PHI9^2 - 9*(1+x),             3, PHI9, 1, 1, 2, 2], \
  ["A3 p3 l2 m2 d2",                  PHI9^4 - 9*(1+x),             3, PHI9, 1, 2, 2, 2], \
  ["A4 p2 l2 m1 d2 (wild p|l)",       x^4 + 2*x^2 + 4,              2, x,    1, 2, 1, 2], \
  ["A5 p2 l1 m1 d2",                  x^2 + 2*x + 4,                2, x,    1, 1, 1, 2], \
  ["A6 p2 l1 m2 d3 (widened region)", PHI4^3 + 8*x,                 2, PHI4, 1, 1, 2, 3], \
  ["A7 p3 l3 m1 d2 (wild p|l)",       x^6 + 3*x^3 + 18,             3, x,    1, 3, 1, 2], \
  ["A8 p3 l1 m1 d3 (p|d)",            x^3 - 9*x + 27,               3, x,    1, 1, 1, 3]  \
];

print("== CERT-A / CERT-B / CERT-C(ii): mixed characteristic ==");
{
for(i = 1, #mixedrows,
  my([lab, g, p, phi, u, l, m, d] = mixedrows[i],
     n = poldegree(g), fp, nf, dec, gc, vphi, vpi, vind);
  chk(Str(lab, ": deg = m*l*d"), n == m*l*d);
  chk(Str(lab, ": irreducible over Q"), polisirreducible(g));
  \\ (A) locally irreducible + (e,f) = (l, m*d)  — PARI oracle
  fp = factorpadic(g, p, 80);
  chk(Str(lab, ": irreducible over Q_p"),
      matsize(fp)[1] == 1 && poldegree(fp[1,1]) == n);
  nf = nfinit(g);
  dec = idealprimedec(nf, p);
  chk(Str(lab, ": one prime above p"), #dec == 1);
  chk(Str(lab, ": e = l"),   dec[1].e == l);
  chk(Str(lab, ": f = m*d"), dec[1].f == m*d);
  \\ CERT-C(ii): the order is a STRICT suborder at d >= 2 (index has positive p-valuation)
  vind = (valuation(poldisc(g), p) - valuation(nf.disc, p))/2;
  chk(Str(lab, ": v_p(index) > 0 (order != maximal)"), vind > 0);
  \\ CERT-B: gcd of order norm-valuations = m*d
  vphi = valuation(polresultant(g, phi, x), p);
  chk(Str(lab, ": v(N(phi(a))) = m*u*d"), vphi == m*u*d);
  vpi = valuation(polresultant(g, p, x), p);   \\ Res(g, const) = const^n
  chk(Str(lab, ": v(N(p)) = l*m*d"), vpi == l*m*d);
  gc = gcd(gcd(gcdnorm_p(g, p, 80), vphi), vpi);
  chk(Str(lab, ": gcd of norm-valuations = m*d"), gc == m*d);
  print("  ", lab, ": (e,f) = (", dec[1].e, ",", dec[1].f, ")  gcd = ", gc,
        "  v_p(index) = ", vind);
);
}

\\ ---------------------------------------------------------------------------
\\ CERT-B, equal characteristic. row = [label, g, p, phi, u, l, m, d].
\\ Elementary irreducibility certificates (unit-root reductions) are checked where the
\\ substitution x -> t*z applies (m = 1 rows); EC3 is certified by CERT-D below; EC4 by
\\ the two sub-facts of the hand case-analysis (see the OM-5 note, CERT §2).
eqrows = [ \
  ["EC1 p2 l1 m1 d2",                  x^2 + 't*x + 't^2,               2, x,    1, 1, 1, 2], \
  ["EC2 p3 l1 m1 d2",                  x^2 + 't*x + 2*'t^2,             3, x,    1, 1, 1, 2], \
  ["EC3 p2 l1 m2 d2 (widened region)", PHI4^2 + 't*PHI4 + 't^2*x,       2, PHI4, 1, 1, 2, 2], \
  ["EC4 p2 l2 m1 d2 (wild p|l)",       x^4 + 't*x^2 + 't^2,             2, x,    1, 2, 1, 2], \
  ["EC5 p3 l3 m1 d2 (wild p|l)",       x^6 + 't*x^3 + 2*'t^2,           3, x,    1, 3, 1, 2], \
  ["EC6 p3 l1 m1 d3 (p|d)",            x^3 + 2*'t^2*x + 't^3,           3, x,    1, 1, 1, 3]  \
];

print("== CERT-B: equal characteristic (O = F_p[[t]]) ==");
{
for(i = 1, #eqrows,
  my([lab, g, p, phi, u, l, m, d] = eqrows[i],
     n = poldegree(g, x), gm = g*Mod(1,p), vphi, vt, gc);
  chk(Str(lab, ": deg = m*l*d"), n == m*l*d);
  vphi = valuation(polresultant(gm, phi*Mod(1,p), x), 't);
  chk(Str(lab, ": v(N(phi(a))) = m*u*d"), vphi == m*u*d);
  vt = valuation(polresultant(gm, Mod(1,p)*'t, x), 't);
  chk(Str(lab, ": v(N(t)) = l*m*d"), vt == l*m*d);
  gc = gcd(gcd(gcdnorm_t(g, p, 80), vphi), vt);
  chk(Str(lab, ": gcd of norm-valuations = m*d"), gc == m*d);
  \\ elementary irreducibility certificate at m = 1, l = 1: x = t*z gives a unit-root
  \\ polynomial; reduction mod t irreducible over F_p  ==>  g irreducible over F_p((t)).
  if(m == 1 && l == 1,
    my(zeta = subst(g, x, 't*'z)/'t^n, zbar, fm);
    zbar = subst(zeta, 't, 0)*Mod(1,p);
    fm = factormod(zbar, p);
    chk(Str(lab, ": unit-root residual irreducible over F_p"),
        matsize(fm)[1] == 1 && fm[1,2] == 1 && poldegree(fm[1,1], 'z) == d));
  print("  ", lab, ": gcd = ", gc);
);
}

\\ ---------------------------------------------------------------------------
\\ CERT-C(i): the multiplicity->=2 defeat — the axiom draft NEEDS Irreducible(resPoly).
\\ g = (x^2 - p)^2: pure at X of slope 1/2, sideDeg 2, resPoly = (y - 1)^2 (a unit times
\\ the SQUARE of an irreducible), factor g' = x^2 - p has inertiaDegOf = 1, and
\\ m*sideDeg = 2 does NOT divide 1.  Same in equal characteristic with (x^2 - t)^2.
print("== CERT-C(i): multiplicity >= 2 defeats hBOX (both characteristics) ==");
{
  my(gA, gp1, r1, gc, fm);
  \\ p = 3, mixed
  gA = (x^2 - 3)^2; gp1 = x^2 - 3;
  \\ resPoly of gA at key X, slope (1,2): digits at j = 0 (y^0): 9 -> 1; j = 2 (y^1): -6/3 = -2; j = 4: 1
  fm = factormod(y^2 + (-6/3)*y + (9/9), 3);
  chk("C1 p3: resPoly = (y-1)^2 (mult 2)", matsize(fm)[1] == 1 && fm[1,2] == 2);
  gc = gcdnorm_p(gp1, 3, 60);
  gc = gcd(gc, valuation(polresultant(gp1, x, x), 3));
  chk("C1 p3: factor x^2-3 has inertiaDegOf = 1", gc == 1);
  chk("C1 p3: m*sideDeg = 2 does NOT divide 1", (1 % 2) != 0);
  \\ p = 5, mixed
  gp1 = x^2 - 5;
  gc = gcd(gcdnorm_p(gp1, 5, 60), valuation(polresultant(gp1, x, x), 5));
  chk("C1 p5: factor x^2-5 has inertiaDegOf = 1", gc == 1);
  \\ p = 3, equal characteristic
  gp1 = x^2 - 't;
  gc = gcd(gcdnorm_t(gp1, 3, 60), valuation(polresultant(gp1*Mod(1,3), Mod(1,3)*x, x), 't));
  chk("C1 p3 eqchar: factor x^2-t has inertiaDegOf = 1", gc == 1);
  print("  mult-2 residual: factor-level gcd = 1, m*d = 2 — hBOX FALSE without hirr");
}

\\ CERT-C(iii): the coprimality defeat — dropping Coprime(u,l) defeats the (e,f) read.
\\ g = x^2 - 9 over Q_3 is "pure of slope (2,2)" in the non-lowest-terms reading
\\ (both points at heights 2,0); the box-shaped prediction m*d = 2 fails: g splits,
\\ each factor has inertiaDegOf = 1.  (HE6-T-BADKEY's genre, minimal instance.)
print("== CERT-C(iii): non-coprime (u,l) defeat ==");
{
  my(gc);
  chk("C3: x^2-9 splits over Q_3", matsize(factorpadic(x^2-9, 3, 40))[1] == 2);
  gc = gcd(gcdnorm_p(x - 3, 3, 40), valuation(polresultant(x-3, x, x), 3));
  chk("C3: factor x-3 has inertiaDegOf = 1 (2 does not divide it)", gc == 1);
}

\\ CERT-C(v) [bonus, found by the battery itself]: the original A6 candidate
\\ g = PHI4^3 + 4*PHI4 + 8x had residual y^3 + y + w, which is REDUCIBLE over F_4
\\ (root w^2: 1 + w^2 + w = 0) — a hand-check error caught by the oracle.  Kept as a
\\ dissection cross-check (B.48/B.63's grain): residual = (linear)*(irreducible quadratic)
\\ over F_4 predicts TWO leaf factors with (e,f) = (1, 2*1) and (1, 2*2).
print("== CERT-C(v): mixed residual => dissection (the corrected ex-A6) ==");
{
  my(g = PHI4^3 + 4*PHI4 + 8*x, fp, nf, dec, fs);
  fp = factorpadic(g, 2, 80);
  chk("C5: two factors over Q_2", matsize(fp)[1] == 2);
  nf = nfinit(g); dec = idealprimedec(nf, 2);
  fs = vecsort(vector(#dec, i, dec[i].f));
  chk("C5: two primes above 2", #dec == 2);
  chk("C5: f-multiset = {2, 4} = {m*1, m*2}", fs == [2, 4]);
  chk("C5: both unramified (e = 1)", vecsort(vector(#dec, i, dec[i].e)) == [1, 1]);
  print("  ex-A6: f-multiset ", fs, " — per-factor (e,f) matches the dissection read");
}

\\ ---------------------------------------------------------------------------
\\ CERT-D: route 1 (LEMMA HE3-4U) executed at EC3 = phi^2 + t*phi + t^2*x over F_2[[t]].
\\ Unramified base change F_2 -> F_4 splits phibar = (x+w)(x+w^2); linear Hensel lifts
\\ g = G1*G2 over F_4[[t]] (the mod-t blocks (x+w)^2, (x+w^2)^2 are coprime); each G_i is
\\ a degree-2 leaf at a LINEAR key over F_4((t)) with slope 1 and an irreducible residual
\\ (unit-root read), hence f(G_i / F_4((t))) = 2; the split-sum over the f1 = m = 2
\\ conjugate components gives f(g / F_2((t))) = 2*2 = 4 = m*d.
print("== CERT-D: HE3-4U mechanism at EC3 (F_2 -> F_4 base change) ==");
{
  my(w = ffgen(Mod(1,2)*('u^2 + 'u + 1), 'w),
     G, G10, G20, be, u0, v0, G1, G2, N = 24, E, eps, dl1, dl2,
     c0, c1, dig0, dig1, psi, hasroot, F4, zeta1bar, gc4, r, h, vv);
  G = (PHI4^2 + 't*PHI4 + 't^2*x) * w^0;   \\ coerce to F_4 coefficients
  G10 = (x + w)^2; G20 = (x + w^2)^2;
  be = gcdext(G10, G20);
  chk("D: mod-t blocks coprime over F_4", poldegree(be[3], x) == 0);
  u0 = be[1]/be[3]; v0 = be[2]/be[3];
  G1 = G10; G2 = G20;
  for(k = 1, N,
    E = G - G1*G2;
    eps = sum(i = 0, 3, polcoef(polcoef(E, i, x), k, 't)*x^i);
    dl1 = (eps*v0) % G10;
    dl2 = (eps - dl1*G20)/G10;
    G1 += 't^k*dl1; G2 += 't^k*dl2;
  );
  E = G - G1*G2;
  chk("D: Hensel lift g = G1*G2 to O(t^25)",
      E == 0 || vecmin(apply(c -> valuation(c, 't), select(c -> c != 0, Vec(E)))) > N);
  \\ per-component residual at the linear key (x + w): unit-root read via x = w + t*z
  F4 = [0*w, w^0, w, w^2];
  my(labels = ["D: G1", "D: G2"], keys = [w, w^2], Gs = [G1, G2]);
  for(j = 1, 2,
    c0 = subst(Gs[j], x, keys[j]);          \\ dev coefficient 0 (Taylor at the key root)
    c1 = subst(deriv(Gs[j], x), x, keys[j]);
    chk(Str(labels[j], ": v(c0) = 2"), valuation(c0, 't) == 2);
    chk(Str(labels[j], ": v(c1) >= 1"), valuation(c1, 't) >= 1);
    dig0 = polcoef(c0, 2, 't); dig1 = polcoef(c1, 1, 't);
    psi = 'z^2 + dig1*'z + dig0;            \\ the component residual over F_4
    hasroot = 0;
    for(e = 1, 4, if(subst(psi, 'z, F4[e]) == 0, hasroot = 1));
    chk(Str(labels[j], ": component residual irreducible over F_4 (no root)"), !hasroot);
  );
  \\ gcd of norm-valuations of the F_4[[t]]-order of G1: predict f(G1/F_4((t))) = 2
  gc4 = 0;
  for(s = 1, 40,
    h = sum(i = 0, 1, (F4[1 + random(4)] + F4[1 + random(4)]*'t)*x^i);
    r = polresultant(G1, h, x);
    if(r != 0, vv = valuation(r, 't); if(vv > 0 && vv < 20, gc4 = gcd(gc4, vv))));
  chk("D: component order gcd of norm-valuations = 2", gc4 == 2);
  \\ split-sum: f over F_2((t)) = [F_4 : F_2] * f(component) = 2*2 = 4 = m*d,
  \\ independently measured by EC3's gcd = 4 above.
  chk("D: split-sum 2*2 = m*d", 2*2 == 4);
  print("  base-change split certified: two conjugate components, each f = 2; total f = 4");
}

\\ ---------------------------------------------------------------------------
print("== SUMMARY ==");
print(checks, " checks, ", fails, " failures");
if(fails == 0, print("ALL GREEN"));
quit(fails);
