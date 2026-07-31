\\ O2a_order1_check.gp — falsifiers for the O-2a dictionary note (order <= 1 + order-2 instances)
\\ Run: gp -q O2a_order1_check.gp
\\
\\ F1: order-1 dictionary sweep. For random + structured monic f over Z read at p:
\\     compute the ORDER-1 OM data exactly as the dictionary note defines them
\\     (residue factorization; per repeated factor psi0: phi1 = canonical lift,
\\     phi1-adic development, lower hull of (j, v(b_j)), per side (e,h,ell),
\\     residual polynomial over F_{p^{f0}} via unit-part classes, factor it).
\\     If EVERY track is order-1 decided (all residual factors multiplicity 1),
\\     the predicted (e,f) multiset (Hensel leaves (1,f0) + Cor 1.20 leaves
\\     (e, f0*deg psi)) must EQUAL the ground truth from idealprimedec on the
\\     Q-irreducible factors (order maximal at p). Any mismatch falsifies the
\\     order <= 1 dictionary (Theorem 1 of the note).
\\ F2: ind1(f) <= ind_p(f) for ALL sampled f (GMN Thm 4.18(1) at r = 1), with
\\     ind1 = sum over repeated psi0 of f0*ind(N^-), ind(N) per GMN Def 4.12,
\\     and ind_p via the etale-algebra formula
\\     ind_p(f) = sum_i (v_p(disc g_i) - v_p(disc K_i))/2 + sum_{i<j} v_p(Res(g_i,g_j)).
\\ F3: order-2 families A: (x^2-p)^2 - p^(2k+1) x  -> predict irreducible (e,f)=(4,1);
\\     B (p=2): (phi1^2-2x)^2 - 2^(2k+1) phi1, phi1 = x^2+x+1 -> predict (e,f)=(4,2);
\\     both from the note's hand-derived two-level chains (invariant matching at order 2).

vpol(b, p) = if(b == 0, oo, vecmin(apply(c -> valuation(c, p), Vec(b))));

\\ phi-adic development of f: returns vector of digits [b_0, ..., b_m]
devel(f, phi) = {
  my(dig = [], g = f, dr);
  while(g != 0,
    dr = divrem(g, phi);
    dig = concat(dig, [dr[2]]);
    g = dr[1]);
  dig;
}

\\ lower convex hull of points [[x1,y1],...] with increasing x (all y finite):
\\ returns list of vertices
lhull(pts) = {
  my(st = List());
  for(i = 1, #pts,
    while(#st >= 2 &&
      (pts[i][2] - st[#st][2]) * (st[#st][1] - st[#st-1][1])
        <= (st[#st][2] - st[#st-1][2]) * (pts[i][1] - st[#st][1]),
      listpop(st));
    listput(st, pts[i]));
  Vec(st);
}

\\ order-1 data for one repeated track (psi0, a) of f at p.
\\ returns [decided, leaves, indN, cert] where leaves = vector of [e, f-res-deg],
\\ indN = GMN Def 4.12 index of the principal polygon, cert = # certified sides
\\ (T1 with e*g>=2 handled at selection level: a side is CERTIFIED here iff
\\  ell>=2 or (e>=2 && h>=2) -- the side-level T1/T2 test; used only for cert<=ind checks)
track1(f, p, psi0, a) = {
  my(phi1, dig, f0, pts, hull, sides, decided = 1, leaves = [], indN = 0, cert = 0,
     EHs = [], w, s, us, e, h, ell, run, rise, g, c, b, ht, R, fac, psi, mu, d2);
  f0 = poldegree(psi0);
  phi1 = lift(psi0); \\ canonical coefficientwise lift {0..p-1}
  dig = devel(f, phi1);
  \\ b_0 = 0 (phi1 | f over Q): -infty side; mark undecided, skip (rare)
  if(dig[1] == 0, return([0, [], 0, 0]));
  pts = [];
  for(j = 0, a,
    if(dig[j+1] != 0, pts = concat(pts, [[j, vpol(dig[j+1], p)]])));
  \\ v(b_a) must be 0 (psi0^a || fbar)
  if(pts[#pts] != [a, 0], error("polygon endpoint not at height 0"));
  hull = lhull(pts);
  \\ sides of the hull (all have negative slope since v(b_j)>=1 for j<a... not nec:
  \\ interior pts can be 0? no: v(b_j) >= 1 for j < a since psi0^a || fbar. keep all)
  w = ffgen(psi0 * Mod(1, p), 'w);
  for(i = 1, #hull - 1,
    s = hull[i][1]; us = hull[i][2];
    run = hull[i+1][1] - s; rise = us - hull[i+1][2];
    if(rise <= 0, error("non-negative slope side in principal part"));
    g = gcd(run, rise); e = run / g; h = rise / g; ell = g;
    \\ side index, GMN Def 4.12 (E = e*ell, H = h*ell, d = ell)
    d2 = (e*ell)*(h*ell) - e*ell - h*ell + ell;
    if(d2 % 2 != 0, error("odd 2*ind(S)"));
    indN += d2 / 2;
    if(ell >= 2 || (e >= 2 && h >= 2), cert += 1);
    EHs = concat(EHs, [[e*ell, h*ell]]);
    \\ residual polynomial over F_{p^f0}: on-side abscissas s + j*e, heights us - j*h
    R = 0;
    for(j = 0, ell,
      b = dig[s + j*e + 1];
      ht = us - j*h;
      if(b != 0 && vpol(b, p) == ht,
        c = subst(lift(Mod(b / p^ht, p)), variable(f), w);
        if(j == 0 && c == 0, error("c_0 = 0"));
        if(j == ell && c == 0, error("leading residual coeff = 0"));
        R += c * 'Z^j));
    if(poldegree(R, 'Z) != ell, error("residual degree != ell"));
    fac = factor(R);
    for(t = 1, matsize(fac)[1],
      psi = fac[t, 1]; mu = fac[t, 2];
      if(poldegree(psi, 'Z) < 1, next); \\ unit content
      if(mu == 1,
        leaves = concat(leaves, [[e, f0 * poldegree(psi, 'Z)]]),
        decided = 0)));
  \\ cross terms E_i H_j (i < j), slopes ordered increasing along the hull:
  \\ GMN orders sides by increasing slope lambda_1 < ... < lambda_g; hull gives
  \\ slopes increasing (less negative) left to right, matching.
  for(i = 1, #EHs, for(j = i+1, #EHs, indN += EHs[i][1] * EHs[j][2]));
  [decided, leaves, indN, cert];
}

\\ ground truth (e,f) multiset via idealprimedec on Q-factors (order maximal at p)
truthEF(f, p) = {
  my(fa = factor(f), out = [], g, K, dec);
  for(i = 1, matsize(fa)[1],
    g = fa[i, 1];
    if(fa[i, 2] != 1, error("f not squarefree over Q"));
    if(poldegree(g) == 1,
      out = concat(out, [[1, 1]]),
      K = nfinit([g, [p]]);
      dec = idealprimedec(K, p);
      for(j = 1, #dec, out = concat(out, [[dec[j].e, dec[j].f]]))));
  vecsort(out);
}

\\ etale-algebra index ind_p(f)
indP(f, p) = {
  my(fa = factor(f), gs = [], tot = 0, K, dK);
  for(i = 1, matsize(fa)[1], gs = concat(gs, [fa[i,1]]));
  for(i = 1, #gs,
    if(poldegree(gs[i]) >= 2,
      K = nfinit([gs[i], [p]]);
      dK = K.disc;
      tot += (valuation(poldisc(gs[i]), p) - valuation(dK, p)) / 2));
  for(i = 1, #gs, for(j = i+1, #gs,
    tot += valuation(polresultant(gs[i], gs[j]), p)));
  tot;
}

\\ one polynomial: run F1 + F2. returns [tested_ef, ok_ef, ok_ind]
checkpoly(f, p) = {
  my(n = poldegree(f), fm, decided = 1, pred = [], ind1 = 0, certTot = 0,
     psi0, a, r, tr, truth, ip);
  if(poldisc(f) == 0, return([0, 1, 1]));
  fm = factormod(f, p);
  for(i = 1, matsize(fm)[1],
    psi0 = fm[i, 1]; a = fm[i, 2];
    if(a == 1,
      pred = concat(pred, [[1, poldegree(psi0)]]),
      tr = track1(f, p, psi0, a);
      if(tr[1] == 0, decided = 0);
      pred = concat(pred, tr[2]);
      ind1 += poldegree(psi0) * tr[3];
      certTot += tr[4]));
  ip = indP(f, p);
  my(ok_ind = (ind1 <= ip));
  if(!ok_ind,
    print("IND VIOLATION p=", p, " f=", f, " ind1=", ind1, " indp=", ip));
  if(!decided, return([0, 1, ok_ind]));
  \\ degree checksum
  if(vecsum(apply(v -> v[1]*v[2], pred)) != n,
    print("DEGREE CHECKSUM FAIL p=", p, " f=", f); return([1, 0, ok_ind]));
  truth = truthEF(f, p);
  my(ok_ef = (vecsort(pred) == truth));
  if(!ok_ef,
    print("EF MISMATCH p=", p, " f=", f, " pred=", vecsort(pred), " truth=", truth));
  [1, ok_ef, ok_ind];
}

\\ random irreducible monic mod p of degree d
randirr(p, d) = {
  my(g);
  until(polisirreducible(g * Mod(1, p)),
    g = 'x^d + Pol(vector(d, i, random(p)), 'x));
  g;
}

main() = {
  my(tested = 0, decided_cnt = 0, ef_bad = 0, ind_bad = 0, res, f, n, psi0, rest, dr);
  setrand(20260731);
  \\ F1/F2 sweep
  foreach([2, 3, 5], p,
    for(n = 2, 6,
      \\ (i) plain random
      for(t = 1, 120,
        f = 'x^n + Pol(vector(n, i, random(p^5)), 'x);
        res = checkpoly(f, p);
        tested += 1; decided_cnt += res[1];
        ef_bad += (1 - res[2]); ind_bad += (1 - res[3]));
      \\ (ii) forced repeated residue factor: fbar = psi0^a * rest
      for(t = 1, 120,
        my(d0 = 1 + random(min(2, n\2)), a);
        a = 2 + random(max(1, n\d0 - 1));
        if(a * d0 > n, a = n \ d0);
        if(a < 2, next);
        psi0 = randirr(p, d0);
        rest = 'x^(n - a*d0) + Pol(vector(n - a*d0, i, random(p)), 'x);
        f = lift(Mod(psi0, p)^a * Mod(rest, p));
        f = 'x^n + Pol(Vec(Pol(vector(n,i,0),'x) + f - 'x^n), 'x); \\ keep monic deg n
        f = f + p * Pol(vector(n, i, random(p^4)), 'x);
        if(poldegree(f) != n, next);
        res = checkpoly(f, p);
        tested += 1; decided_cnt += res[1];
        ef_bad += (1 - res[2]); ind_bad += (1 - res[3]))));
  print("F1/F2: tested=", tested, " order1-decided=", decided_cnt,
        " ef-mismatch=", ef_bad, " ind-violation=", ind_bad);

  \\ F3 family A: (x^2-p)^2 - p^(2k+1) x -> predict multiset {(4,1)}
  my(badA = 0);
  foreach([2, 3, 5], p,
    for(k = 1, 3,
      f = ('x^2 - p)^2 - p^(2*k+1)*'x;
      if(truthEF(f, p) != [[4, 1]], badA += 1;
        print("F3A FAIL p=", p, " k=", k, " truth=", truthEF(f, p)))));
  print("F3 family A ((e,f)=(4,1) totally ramified): failures=", badA, "/9");

  \\ F3 family B: p=2, phi1 = x^2+x+1, f = (phi1^2-2x)^2 - 2^(2k+1) phi1 -> {(4,2)}
  my(badB = 0, phi1 = 'x^2 + 'x + 1);
  for(k = 1, 3,
    f = (phi1^2 - 2*'x)^2 - 2^(2*k+1)*phi1;
    if(truthEF(f, 2) != [[4, 2]], badB += 1;
      print("F3B FAIL k=", k, " truth=", truthEF(f, 2)));
    \\ dCert = 2 along the branch; check 2 <= ind_2(f)
    my(ip = indP(f, 2));
    if(ip < 2, badB += 1; print("F3B IND FAIL k=", k, " indp=", ip));
    print("F3B k=", k, ": truth=", truthEF(f, 2), " ind_2=", ip, " (dCert=2)"));
  print("F3 family B ((e,f)=(4,2) wild f0=2): failures=", badB, "/3");
}

main();
quit;
