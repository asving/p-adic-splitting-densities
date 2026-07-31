\\ O2a_rev2_check.gp — rev-2 falsifier F5 for the O-2a dictionary note.
\\ Covers the V10 justification gap G1 (exact phi1-divisibility / slope -oo side),
\\ the case the rev-1 sweep F1 explicitly SKIPPED (dig[1] == 0 -> early return).
\\
\\ Family: f = phi1 * g with ord_{psi0}(fbar) = a >= 2 and ord_{phi1}(f) = 1
\\ (separability forces ord_{phi1}(f) <= 1). Rev-2 (D3) claims: the FINITE
\\ principal part of N1^-(f) runs on abscissas [j0, a] (j0 = ord_{phi1}(f));
\\ the slope -oo side of length E_oo = j0 carries the exact factor phi1^{j0},
\\ which at j0 = 1 is Hensel-irreducible with (e, f) = (1, f0); ind(N) gains
\\ the term E_oo * H_fin (GMN Def 4.12 as transcribed in brief (L8)).
\\ Checks per sample:
\\   (i)  predicted (e,f) multiset (-oo leaf + finite-side Cor 1.20 leaves +
\\        Hensel leaves) vs idealprimedec ground truth, when order-1 decided;
\\   (ii) degree checksum;
\\   (iii) ind1(f) <= ind_p(f) WITH the E_oo*H_fin term included (sharper);
\\   (iv) #certified finite sides <= ind1(f)  (each certified side has
\\        ind(S) >= 1 by the note's lattice witnesses).
\\ Run: gp -q O2a_rev2_check.gp

vpol(b, p) = if(b == 0, oo, vecmin(apply(c -> valuation(c, p), Vec(b))));

devel(f, phi) = {
  my(dig = [], g = f, dr);
  while(g != 0,
    dr = divrem(g, phi);
    dig = concat(dig, [dr[2]]);
    g = dr[1]);
  dig;
}

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

\\ order-1 data for one repeated track (psi0, a) of f at p, j0-AWARE version.
\\ returns [decided, leaves, indN, cert]; handles j0 = ord_{phi1}(f) in {0, 1}
\\ (j0 >= 2 impossible for separable f: phi1^2 | f forces disc f = 0).
track1i(f, p, psi0, a) = {
  my(phi1, dig, f0, j0 = 0, pts, hull, decided = 1, leaves = [], indN = 0,
     cert = 0, EHs = [], Hfin, s, us, e, h, ell, run, rise, g, c, b, ht, R,
     fac, psi, mu, d2, w);
  f0 = poldegree(psi0);
  phi1 = lift(psi0);
  dig = devel(f, phi1);
  while(dig[j0+1] == 0, j0++);
  if(j0 > 1, error("j0 >= 2: f not separable?"));
  if(j0 > a, error("j0 > a impossible"));
  pts = [];
  for(j = j0, a,
    if(dig[j+1] != 0, pts = concat(pts, [[j, vpol(dig[j+1], p)]])));
  if(pts[#pts] != [a, 0], error("polygon endpoint not at height 0"));
  hull = lhull(pts);
  \\ -oo side booking: E_oo = j0, H_fin = ordinate of the first finite vertex
  Hfin = hull[1][2];
  indN += j0 * Hfin;
  if(j0 == 1, leaves = concat(leaves, [[1, f0]]));  \\ exact phi1: Hensel leaf
  w = ffgen(psi0 * Mod(1, p), 'w);
  for(i = 1, #hull - 1,
    s = hull[i][1]; us = hull[i][2];
    run = hull[i+1][1] - s; rise = us - hull[i+1][2];
    if(rise <= 0, error("non-negative slope side in principal part"));
    g = gcd(run, rise); e = run / g; h = rise / g; ell = g;
    d2 = (e*ell)*(h*ell) - e*ell - h*ell + ell;
    if(d2 % 2 != 0, error("odd 2*ind(S)"));
    indN += d2 / 2;
    if(ell >= 2 || (e >= 2 && h >= 2), cert += 1);
    EHs = concat(EHs, [[e*ell, h*ell]]);
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
      if(poldegree(psi, 'Z) < 1, next);
      if(mu == 1,
        leaves = concat(leaves, [[e, f0 * poldegree(psi, 'Z)]]),
        decided = 0)));
  for(i = 1, #EHs, for(j = i+1, #EHs, indN += EHs[i][1] * EHs[j][2]));
  [decided, leaves, indN, cert];
}

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

checkpoly5(f, p) = {
  my(n = poldegree(f), fm, decided = 1, pred = [], ind1 = 0, certTot = 0,
     psi0, a, tr, truth, ip, ok_ind, ok_cert, ok_ef = 1);
  if(poldisc(f) == 0, return([0, 1, 1, 1]));
  fm = factormod(f, p);
  for(i = 1, matsize(fm)[1],
    psi0 = fm[i, 1]; a = fm[i, 2];
    if(a == 1,
      pred = concat(pred, [[1, poldegree(psi0)]]),
      tr = track1i(f, p, psi0, a);
      if(tr[1] == 0, decided = 0);
      pred = concat(pred, tr[2]);
      ind1 += poldegree(psi0) * tr[3];
      certTot += tr[4]));
  ip = indP(f, p);
  ok_ind = (ind1 <= ip);
  if(!ok_ind,
    print("IND VIOLATION p=", p, " f=", f, " ind1=", ind1, " indp=", ip));
  ok_cert = (certTot <= ind1);
  if(!ok_cert,
    print("CERT VIOLATION p=", p, " f=", f, " cert=", certTot, " ind1=", ind1));
  if(!decided, return([0, 1, ok_ind, ok_cert]));
  if(vecsum(apply(v -> v[1]*v[2], pred)) != n,
    print("DEGREE CHECKSUM FAIL p=", p, " f=", f); return([1, 0, ok_ind, ok_cert]));
  truth = truthEF(f, p);
  ok_ef = (vecsort(pred) == truth);
  if(!ok_ef,
    print("EF MISMATCH p=", p, " f=", f, " pred=", vecsort(pred), " truth=", truth));
  [1, ok_ef, ok_ind, ok_cert];
}

randirr(p, d) = {
  my(g);
  until(polisirreducible(g * Mod(1, p)),
    g = 'x^d + Pol(vector(d, i, random(p)), 'x));
  g;
}

main() = {
  my(tested = 0, decided_cnt = 0, ef_bad = 0, ind_bad = 0, cert_bad = 0,
     skipped = 0, res, f, phi1, g0, psi0, rest, d0, ap, dr);
  setrand(20260801);
  foreach([2, 3, 5], p,
    for(n = 3, 7,
      for(t = 1, 60,
        \\ pick psi0 (deg d0), extra multiplicity ap >= 1: a = 1 + ap >= 2
        d0 = 1 + random(2);
        if((1 + 2)*d0 > n, d0 = 1);   \\ ensure room for ap up to 2
        ap = 1 + random(2);
        while((1 + ap)*d0 > n, ap--);
        if(ap < 1, skipped++; next);
        psi0 = randirr(p, d0);
        \\ rest: monic deg n - d0 - ap*d0 over F_p with psi0 nmid rest
        my(dr0 = n - d0 - ap*d0, restp);
        if(dr0 == 0, restp = 1,
          until(Mod(restp, p) % Mod(psi0, p) != 0,
            restp = 'x^dr0 + Pol(vector(dr0, i, random(p)), 'x)));
        \\ g = lift(psi0^ap * rest) + p * noise  (monic, deg n - d0)
        g0 = lift(Mod(psi0, p)^ap * Mod(restp, p));
        g0 = g0 + p * Pol(vector(n - d0, i, random(p^3)), 'x);
        phi1 = psi0;   \\ integer poly, IS the canonical lift of its reduction
        f = phi1 * g0;
        if(poldisc(f) == 0, skipped++; next);
        \\ sanity: ord_{phi1}(f) = 1 exactly (g0 not divisible by phi1)?
        \\ handled inside track1i (it recomputes j0; j0 = 0 samples are fine too)
        res = checkpoly5(f, p);
        tested += 1; decided_cnt += res[1];
        ef_bad += (1 - res[2]); ind_bad += (1 - res[3]); cert_bad += (1 - res[4]))));
  print("F5 (exact phi1-divisibility / slope -oo): tested=", tested,
        " decided=", decided_cnt, " skipped=", skipped);
  print("   ef-mismatch=", ef_bad, " ind-violation=", ind_bad,
        " cert-violation=", cert_bad);
  \\ hand corner: p = 3, f = x^2 + 3x  (j0 = 1 = a - 1, ind1 = indp = 1)
  my(r2 = checkpoly5('x^2 + 3*'x, 3));
  print("corner x^2+3x @ p=3: [decided, ef, ind, cert] = ", r2);
}

main();
quit;
