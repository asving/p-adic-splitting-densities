p = 3;
certif(f) =
{
  my(fac = factorpadic(f, p, 50), out = []);
  for (i = 1, #fac[,1],
    my(g = fac[i,1], d = poldegree(g));
    if (d == 1, out = concat(out, [[1,1]]),
      my(vd = valuation(poldisc(g), p));
      if (vd % 2 == 1, out = concat(out, [[2,1]]), out = concat(out, [[1,2]]))));
  vecsort(out);
}
stable_key(b, c, N) =
{
  my(f0 = x^2 + b*x + c, k0 = certif(f0), pN = p^N, ok = 1);
  for (i = 1, 5,
    my(f = x^2 + (b + pN*(1+random(80)))*x + (c + pN*(1+random(80))));
    if (certif(f) != k0, ok = 0; break));
  if (ok, Str([k0, min(valuation(poldisc(x^2 + b*x + c), p), 2*N)]), 0);
}
runlevel(N) =
{
  my(pN = p^N, M = Map());
  for (b = 0, pN-1,
    for (c = 0, pN-1,
      my(k = stable_key(b, c, N));
      if (k != 0,
        my(cur = 0);
        if (mapisdefined(M, k), cur = mapget(M, k));
        mapput(M, k, cur + 1))));
  print("=== N = ", N, " ===");
  my(mk = Mat(M));
  for (i = 1, matsize(mk)[1], print("  ", mk[i,1], " -> ", mk[i,2]));
}
for (N = 2, 4, runlevel(N));
quit
