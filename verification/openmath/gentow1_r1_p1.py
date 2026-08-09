#!/usr/bin/env python3
# gentow1_r1_p1.py -- GENTOW1 r1 (m-1 repair): score the sealed P-1
# prediction on the FIVE BASE KEYS Phi2 of gentow1_checks.py's
# families.
#
# PROVENANCE. gentow1_checks.py was sealed at commit 982abe7 with
# docstring prediction
#   P-1 (KEY): Phi2 irreducible with single prime (e,f) = (e1e2,f1f2);
#     nfeltval: v(x) = e2h/(e1e2)-normalized, v(Phi') = u2 pr-units.
# but no scored runner row exercised the BASE keys' ef (the GP-EF
# rows score the 8 REFINED keys only), as GENTOW1 passPE1 m-1
# (report @ 606e85c) recorded. This supplement scores P-1 directly.
# The sealed runner and its output are BYTE-UNTOUCHED; the keys here
# are transcribed from GENTOW1_PROOF S1's table (independent of the
# sealed runner's constructors -- a decorrelated leg).
#
# PER FAMILY (constants from GENTOW1_PROOF S1; h = 1, f1 = 1, d = 1):
#   (a) factorpadic(Phi2, p, 500): ONE row, multiplicity 1, degree D2
#       -> Phi2 irreducible over Qp;
#   (b) nfinit + idealprimedec: ONE prime with (e, f) = (e1e2, f1f2);
#   (c) nfeltval(x)  * e1   = h  * pr.e  (v(x) at the composed node);
#   (d) nfeltval(Phi') * e1e2 = u2 * pr.e (v(Phi') = u2 pr-units).
# All five committed families sit at eta = 1 (q = 2: Phi' = x^2-2;
# q = 3: Phi' = x^2-3), where the gauge-naive and corrected chat_t
# displays coincide (GENHN dated erratum 59c1966) -- P-1 as sealed is
# a base-key check, not a gauge tooth; the eta != 1 base-key ef row
# lives in gentow1_pe1_fresh.py (ef(Phi2^C) = {(2,2)} at F1).

import subprocess
import sys

# name, p, e1, e2, f2, u2, Phi', Phi2   (h = 1, f1 = 1, mu2 = 2)
FAMS = [
    ('FAM-A5', 2, 2, 2, 1, 5, 'x^2-2', '(x^2-2)^2-4*x'),
    ('FAM-A7', 2, 2, 2, 1, 7, 'x^2-2', '(x^2-2)^2-8*x'),
    ('FAM-B',  2, 2, 1, 2, 3, 'x^2-2', '(x^2-2)^2-2*x*(x^2-2)-8'),
    ('FAM-C',  2, 2, 3, 1, 7, 'x^2-2', '(x^2-2)^3-8*x'),
    ('FAM-D',  3, 2, 1, 2, 3, 'x^2-3', '(x^2-3)^2+27'),
]

HDR = 'default(parisizemax, 4000000000);\n'
JOB = ('my(f = {PHI2}, p = {p}, F = factorpadic(f, p, 500),'
       ' nf = nfinit([f, [p]]), dec = idealprimedec(nf, p),'
       ' pr = dec[1]);'
       ' print("{name} ", matsize(F)[1], " ",'
       ' vecmax(vector(matsize(F)[1], i, F[i,2])), " ",'
       ' poldegree(liftall(F[1,1])), " ", #dec, " ",'
       ' pr.e, " ", pr.f, " ",'
       ' nfeltval(nf, Mod(x, f), pr), " ",'
       ' nfeltval(nf, Mod({PHI1}, f), pr));')


def main():
    src = HDR + '\n'.join(
        JOB.format(name=n, p=p, PHI1=P1, PHI2=P2)
        for (n, p, e1, e2, f2, u2, P1, P2) in FAMS) + '\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=600)
    if out.returncode != 0:
        print(out.stderr)
        sys.exit(2)
    rows = {}
    for line in out.stdout.splitlines():
        w = line.split()
        if len(w) == 9 and w[0].startswith('FAM'):
            rows[w[0]] = [int(z) for z in w[1:]]
    checks = viol = 0

    def chk(tag, ok, msg):
        nonlocal checks, viol
        checks += 1
        if not ok:
            viol += 1
            print('VIOLATION [%s] %s' % (tag, msg))

    for (n, p, e1, e2, f2, u2, P1, P2) in FAMS:
        h, f1 = 1, 1
        nfac, mult, deg1, ndec, e, f, vx, vphi = rows[n]
        D2, m = e1 * f1 * e2 * f2, e1 * e2
        chk('P1-IRR', nfac == 1 and mult == 1 and deg1 == D2,
            '%s factorpadic %s/%s/%s want 1/1/%d'
            % (n, nfac, mult, deg1, D2))
        chk('P1-EF', ndec == 1 and (e, f) == (m, f1 * f2),
            '%s dec %s (e,f)=(%s,%s) want 1 (%d,%d)'
            % (n, ndec, e, f, m, f1 * f2))
        chk('P1-VX', vx * e1 == h * e,
            '%s v(x)=%s: e1*v(x)=%s want h*pr.e=%s'
            % (n, vx, vx * e1, h * e))
        chk('P1-VPHI', vphi * m == u2 * e,
            '%s v(Phi1)=%s: e1e2*v=%s want u2*pr.e=%s'
            % (n, vphi, vphi * m, u2 * e))
        print('%s: factorpadic 1 row x1 deg %d; 1 prime (e,f)=(%d,%d);'
              ' v(x)=%d v(Phi1)=%d [all as P-1]' % (n, D2, e, f, vx, vphi))
    print('P-1 SCORED: %d checks, %d violations -- %s'
          % (checks, viol, 'GREEN' if viol == 0 else 'RED'))
    sys.exit(0 if viol == 0 else 1)


if __name__ == '__main__':
    main()
