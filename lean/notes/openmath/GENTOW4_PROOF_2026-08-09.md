# GENTOW-4: PARTIAL INNER SIDES ([GENHN-TOW-1] item (4)) — the
# partial-side tower read = the level-1 label-class BLOCK SPLIT +
# LEMMA HE6R1-2's projection + per-block literal HE7.A instances at
# the composed carrier, 2026-08-09

**STATUS: COMPOSED (per-section commits; machine leg sealed-then-
verdict, S6). Unit: GENTOW-4, BOX-CLOSURE campaign wave 22. Grade
0/2 (attempt; hostile arc owed).**

Charge: [GENHN-TOW-1] item (4) — the inner CS event occupies only
PART of the (J, dv(A_J))-polygon: e2f2·mu2 < mu1, because the
polygon has other sides and/or the event side carries other
residual classes. Consumes (never edits): GENHN_PROOF S8 [r2] annex
(LEMMA GENHN-T(b)': composed carrier (i), slot lemma GENHN-2' (ii))
+ the S3.2 [r1] node-floor erratum; HETOW_RECON (bridges HETOW-1/2,
THEOREM HETOW.A's instantiation table); HE6R1_RECON (LEMMA HE6R1-2
block projection + RIDER HE6R1-2R, LEMMA HE6R1-3 peel); HE7_PROOF
(THEOREM HE7.A/C/D, LEMMAS HE7-5/6/9/10/11/12/13, ANNEX-LEMMA
HE7-13'); HE6_PROOF (LEMMA HE6-3, LEMMA HE6-4, THEOREM HE6.A);
GENTOW1_PROOF (E2, weight grammar, notation); GENHN_passPE2_report
(the PE2-P witness). Frozen-file discipline: none of those notes is
edited here.

## S0. SETTING, THE WITNESS, AND THE ANSWER'S SHAPE

Tower entry (T(b)' setting, fullness dropped): outer genre
(Q; e1, f1, mu1; h), key Phi' (deg D' = e1f1), dv = e1·v; f monic of
degree n = D'·mu1 on the genre-G opening locus, disc f != 0; level-1
development f = Phi'^{mu1} + Sum_{J<mu1} A_J Phi'^J, stage polygon
P(F) := lower hull of {(J, dv(A_J))}. An inner CS event: SOME side
of P(F), of dv-slope kappa2 = u2/e2 (lowest terms), whose residual
R_{kappa2} has an irreducible repeated factor psi2 (multiplicity
mu2 >= 2, f2 := deg psi2) with e2·f2 >= 2. PARTIAL:
e2f2·mu2 < mu1. Composed key (same formula as T(b)'):
Phi2 := Phi'^{e2f2} − Sum_{t<f2} chat_t·nhat(u2(f2−t))·Phi'^{e2t},
deg D2 = D'e2f2; dv2 := e1e2·v; T2 = E2 := e2f2·u2 (GENTOW-1 S0).

THE WITNESS (PE2-P, constructed by GENHN's passPE2 verifier; the
box's protected instance): n = 10, genre (2,1,5) over Q_2,
f = Phi'^5 + 4Phi'^4 + 32Phi' + 64x (Phi' = x^2 − 2). P(F) =
(0,13)–(1,10)–(5,0): a slope-3 SIBLING side of length 1 plus a
slope-5/2 INNER side of length 4 < mu1 = 5 carrying (T+1)^2 — an
inner mu2 = 2 event on a partial side. The corrected T(b)'(iii)
reader REFUSES it (the Phi2-development of f is not
monic-of-length-mu2: deg f = 10 != mu2·D2 = 8) and no proved
display priced its sigma (PARI: {(2,1),(4,1),(4,1)}).

THE ANSWER'S SHAPE (derived in S2–S4, verified at PE2-P in S5): a
partial side means f_S — the block factor of the inner label — is a
PROPER factor of f. The read is:

1. f splits along its level-1 LABEL CLASSES (kappa, r) — the
   HE7-13' bouquet mechanism, here at the tower entry, with the
   block factors supplied by LEMMA HE7-6 at each label datum;
2. each class is read through ITS OWN composed key by LEMMA
   HE6R1-2 (block projection — proved in HE6R1_RECON for EXACTLY
   this proper-block configuration: "R_lambda has another distinct
   factor, or P(F) has another side"): the slope-> T2 part of
   P2(f) IS P2(f_S) translated by the constant c_g = dv2(g(xi)) of
   the complementary factor g = f/f_S, with the same slopes,
   lengths, and residual factors up to a K2^x scalar;
3. THEOREM HE7.A (+ HE7.C/D, ANNEX HE7-13') then decides each
   block at the composed carrier exactly as at HETOW's full sides —
   per separable class one factor with the composed dictionary
   (e, f) = (e1e2·l2, f1f2·deg r2).

Nothing about the DECISION is new: the two new proof obligations
are the two full-side-dependent steps of HETOW's instantiation
(repaired in S2) and the multiplicity TIE mu2* = mu2 between the
level-1 residual exponent and the composed polygon length (proved
at pure-power sides in S3; honestly boxed at mixed sides, S7).

## S1. THE EXAMPLE BATTERY (examples-first; laws read off the tables)

Five constructed partial-side families (3 genres, q in {2,3}, both
e2-branches, sibling on either flank, one mixed side; full data
S6). Headline hand-verified instance — PE2-P itself:

    f = Phi'^5 + 4Phi'^4 + 32Phi' + 64x,  Phi2 = Phi'^2 − 4x,
    E2 = T2 = 10, dv2 = 4v.
    Phi2-development of f:  C2 = x^2 + 2 = Phi' + 4,
      C1 = 8x^3 + 16x + 16 = 8xPhi' + 32x + 16,  C0 = 128x^2 + 128x − 128.
    Composed pins (slot-min, GENHN-2'): p0 = 28, p1 = 16, p2 = 5.
    Polygon (0,28)–(1,16)–(2,5): slopes 12, 11 — BOTH > T2 = 10,
    initial >T2 segment = the whole hull, right endpoint (2, 5):
      mu2* = 2 = mu2 (the tie),  c_g = 5.
    Translated block pins p^S = (23, 11, 0): floors (mu2−j)E2 + 1 =
    (21, 11) both cleared, j = 1 EXACTLY at the node floor.
    Two sides, distinct integer slopes -> composed-2SIDED ->
    {(e1e2, f1f2)} x2 = {(4,1),(4,1)}.  Sibling side (0,13)–(1,10):
    slope 3, length 1, residual linear -> (e1·1, f1·1) = (2,1).
    PARI (both routes): sigma(f) = {(2,1),(4,1),(4,1)}  — EXACT;
    per factor: the deg-2 factor has dv2(Phi2) = 10 = E2 exactly,
    the two deg-4 factors have dv2(Phi2) = 12 and 11 — the polygon
    slopes ARE the factor valuations, and both exceed E2 (the
    GENTOW-1(d) field floor separates the classes).

Read off the table (then proved): (i) the >T2 initial segment of
P2(f) has length exactly mu2 and right-endpoint height c_g — the
block polygon rides ON f's polygon, translated; (ii) c_g here is
ODD, so the f-level pin parity is WRONG for the block (p0 = 28
even, p0^S = 23 odd): any reader that skips the c_g-translation
misprices RAM — the load-bearing tooth T-NOCG; (iii) sibling
factors sit at dv2(Phi2) = E2 (steeper flank) or < E2 (shallower
flank), class factors strictly above E2: the field floor is the
machine-visible class separator.

## S2. LEMMA GENTOW-4.1 (the partial-side bridge repairs)

HETOW's instantiation map (HETOW_RECON S1, rows verbatim) consumes
fullness in exactly THREE places: HETOW-1(a)'s psi2(0) != 0 ("at a
FULL side the left endpoint (0, dv(A_0)) is an attained pin"),
HETOW-3 wholesale (f_S = f), and nothing else — HETOW-2's proof
consumes only Phi2's own construction, DEFINITION HE6-1's
deg/dv/residue interfaces, and the node floor u2 > e2D'h, never the
side's length (checked line by line at this unit; the [r2]
parenthetical's carry estimate is side-blind). The repairs:

> **LEMMA GENTOW-4.1.** In the S0 setting (partial side):
> (a) [floor, every side] every side of P(F) has dv-slope > D'h;
> in particular kappa2 > D'h and every sibling slope qualifies as a
> level-2 datum slope. (b) [psi2(0) != 0] the residual of EVERY
> side of P(F) has nonzero constant term; in particular
> psi2(0) != 0, and HETOW-1 holds verbatim with this in place of
> its full-side endpoint step: (kappa2, rtilde) is a level-2 datum
> of DEFINITION HE7-1 over the outer frame, and the tower-node
> locus is its level-2 point set. (c) [key bridge] HETOW-2 holds
> verbatim: Phi2 = Psi_{kappa2,rtilde} − w with w = 0 or
> dv2(w) > T2, so by LEMMA HE7-12 the §S5 package, THEOREM
> HE7.A(1)(2), the refine package (HE7-12/13, HE7-8), the §S1
> CONVENTION with LEMMA HE6R1-3's peel, ANNEX-LEMMA HE7-13', and
> LEMMA HE6R1-2 with RIDER HE6R1-2R all hold with key Phi2.
> (d) [frame peels] if Phi' | f then Phi' EXACTLY divides f
> (disc != 0), contributes one irreducible factor with
> (e, f) = (e1, f1), and the read continues on f/Phi' (whose
> development is the J-shift); if Phi2 | f likewise via LEMMA
> HE6R1-3 at key Phi2 ((c)), contributing (e1e2, f1f2) and
> dropping mu2 by 1. So assume Phi' ∤ f, Phi2 ∤ f below.
>
> *Proof.* (a) is the [r1] node-floor erratum's own derivation
> (GENHN_PROOF S3.2 [r1] annex), which is side-blind: every root
> rho of f on the opening locus has dv(Phi'(rho)) > D'h (LEMMA
> HE6-0 as re-proved at HE6 r1), hence every side of P(F) has
> dv-slope > D'h by LEMMA HE6-3(a) — quoted there with "no (SEP)
> hypothesis". (b) BOTH endpoints of every side of P(F) are
> vertices of the polygon, hence ATTAINED pins (a vertex of a
> lower hull of an integer point set is a point of the set; the
> global endpoints (0, dv(A_0)) with A_0 != 0 by (d)'s reduction,
> and (mu1, 0) with C_{mu1} = 1, attain too). A side's residual
> R_kappa has constant term = the (twist-normalized) residue of
> the left-endpoint pin — attained, hence nonzero. psi2^{mu2}
> | R_{kappa2} and R_{kappa2}(0) != 0 force psi2(0) != 0. The rest
> of HETOW-1's proof is untouched: its clause (b) reads the locus
> definitions (T1)/(T2)/(T1_2)/(T2_2), and its clause (a)'s
> minimal-polynomial computation consumes psi2 irreducible,
> psi2(0) != 0, and the residual division at a root of Phi2 —
> none of which mention the side length. (c) HETOW-2's proof
> audit above; LEMMA HE6R1-2's own proof consumes only LEMMA
> HE6-4/HE6-2' at level 1 (key-free), (LIFT_2), LEMMA HE7-7,
> LEMMA HE7-7'(b) + RIDER HE6R1-2R, and (SLOT_2) — every item in
> the §S5 package that LEMMA HE7-12(c) transports to the
> perturbed key (HE7 §S5.8(c)'s audit, items (5)–(6), records
> HE7-7' as key-free), so the projection lemma fires at Phi2.
> (d) level-1: Phi' | f gives the irreducible factor Phi' itself,
> with carrier (e1, f1) (S3.1 invariants), exactly once by
> disc f != 0; level-2: LEMMA HE6R1-3's display at key Phi2,
> available by (c). ∎

REMARK (what (b) does NOT claim): no statement about pins strictly
inside a side, and no claim that A_0's residue feeds psi2 — at a
partial side the left endpoint of the inner side is generally an
interior vertex (PE2-P: (1,10)), and the residual's constant term
is read THERE.

## S3. THEOREM GENTOW-4.A (the partial-side tower read)

Label vocabulary (HE7's, at the tower entry via HETOW-1's
translation): for a side of P(F) of slope kappa = u/l (lowest
terms) and a monic irreducible factor r of its residual R_kappa,
the LABEL CLASS is C_{kappa,r} := the roots x0 of f with
dv(Phi'(x0)) = kappa whose twist-normalized letter beta_{x0} is a
root of iota(rtilde_r) (rtilde_r = the pi-bar-normalized twist of
r, LEMMA HETOW-1 at that side — a level-2 datum by GENTOW-4.1(a),
(b)). LEMMA HE6-2''/HE6-4 give: the classes partition the roots of
f, every (kappa, r) with r | R_kappa is realized, and the label is
a label OF f in THEOREM HE7.A's sense.

> **THEOREM GENTOW-4.A (partial inner sides: block split +
> projection + per-block full-side instances).** In the S0 setting,
> after the S2 peels:
>
> (i) [BOUQUET AT THE ENTRY] f = Prod_{(kappa,r)} f_{kappa,r} with
> f_{kappa,r} in O[x] monic, the block factor of C_{kappa,r}
> (LEMMA HE7-6's argument at each datum: Galois-stability by LEMMA
> HE7-11, integrality, division of the squarefree f); the
> factorization is disjoint over labels and D'·l·d_r | deg
> f_{kappa,r} (LEMMA HE7-5's forcing).
>
> (ii) [PROJECTION, per class — LEMMA HE6R1-2 at the composed key]
> fix the inner class S = C_{kappa2, psi2}, f_S := f_{kappa2,psi2},
> g := f/f_S, and let f = Sum_j C_j Phi2^j be the Phi2-development
> OF f (length M = floor(n/D2) >= mu2, top coefficient NOT monic —
> the partial-side signature), with pins p_j := dv2(C_j(x0)) read
> exactly by GENHN-2' on the tower-node locus. Then dv2(g(xi)) =
> c_g, a constant, at every level-2 point xi of (kappa2, rtilde);
> deg f_S = D2·mu2* where mu2* := Sum_{lambda2 > T2} L_{lambda2}
> (P2(f)); the slope-> T2 part of P2(f) is the INITIAL segment of
> the hull of {(j, p_j)}, spans abscissas [0, mu2*], and equals
> P2(f_S) translated UP by c_g — same breakpoints, slopes,
> lengths; and per side the residuals of f and f_S have the same
> degree and the same monic irreducible factors, agreeing up to
> the K2^x scalar gamma_g (LEMMA HE6R1-2(a)(b)(c) + RIDER
> HE6R1-2R, all available at key Phi2 by GENTOW-4.1(c)).
>
> (iii) [PER-BLOCK DECISION — the composed dictionary] THEOREM
> HE7.A(1)–(3) + THEOREM HE7.C/D + ANNEX-LEMMA HE7-13' apply to
> f_S at the datum (kappa2, rtilde) with key Phi2: every side of
> P2(f_S) has slope lambda2 > T2 with Sum L_{lambda2} = mu2*; each
> irreducible factor r2 of a separable level-2 residual gives ONE
> irreducible factor of f with
>
>     e = e1e2·l2 ,   f = f1f2·deg r2 ;
>
> a repeated K2-rational linear factor at integer lambda2 is a
> finite alpha-refine chain (HE7-12/13, HE7-8; the chain re-reads
> f itself through (ii) at each refined key, available by LEMMA
> HE7-12 with W + w); a repeated factor with l2·deg r2 >= 2 passes
> to level 3 (HE7.D) and needs mu2* >= 4. By (ii) every input to
> the decision — slopes, lengths, residual factors up to K2^x
> scalar, all scale-invariantly consumed (HE7 §S1 convention) —
> is computed from f's OWN development: f_S is never exhibited.
>
> (iv) [THE OTHER CLASSES] every other class C_{kappa,r} is priced
> by the same clauses (i)–(iii) at ITS datum (kappa, rtilde_r): if
> its own mu2*(kappa,r) = 1 (in particular whenever r is a SIMPLE
> factor of a separable R_kappa) the class is one irreducible
> factor with (e, f) = (e1·l, f1·d_r) — THEOREM HE6.A's dictionary
> recovered through the level-2 read (consistency: two proofs
> where R_kappa is separable); if r is repeated with l·d_r = 1 it
> is the level-1 alpha-refine family (GENHN-4 / stage read,
> accepted corpus); if repeated with l·d_r >= 2 it is ITSELF a
> tower class — an inner event on ITS side, read by this same
> theorem (at PARTIAL sides) or by THEOREM HETOW.A (full side).
> sigma(f) = the disjoint union over classes (+ the S2 peels).
>
> (v) [mu2* = 2 DECIDES — T(b)'(iii)'s trichotomy through the
> projection] if mu2* = 2, the block decision is complete and
> translation/scale-invariant on f's own data: with the >T2
> segment spanning [0,2],
>   TWO sides (distinct slopes)            -> {(e1e2, f1f2)} x2
>   ONE side, l2 = 2 (half-integer slope)  -> {(2e1e2, f1f2)}
>   ONE side, integer slope, residual
>     (gamma_g-scaled) irreducible quadratic -> {(e1e2, 2f1f2)}
>     split (two K2-roots)                   -> {(e1e2, f1f2)} x2
>     double root                            -> alpha-refine, repeat
> (slopes are translation-invariant; root/irreducibility tests are
> invariant under the K2^x scaling gamma_g; the double-root refine
> terminates by HE7-13 at the block, per HE7-13'(b)).
>
> *Proof.* (i): the classes partition roots(f) (each root has one
> label — its letter's minimal polynomial); each C_{kappa,r} is
> Galois-stable — LEMMA HE7-11's equivariance computation reads
> Phi', the normalizers, and iota only, so it runs at every datum
> of GENTOW-4.1(b) — hence f_C := Prod_{rho in C}(x − rho) has
> O-coefficients and divides f (LEMMA HE7-6's argument verbatim);
> disjointness is the partition; the degree divisibility is LEMMA
> HE7-5 on each Galois orbit. (ii): LEMMA HE6R1-2 at the datum
> (kappa2, rtilde) and key Phi2 — its hypotheses are f monic on
> the opening locus, disc f != 0, Phi' ∤ f (S2 peel), the label
> realized (LEMMA HE6-4, since psi2 | R_{kappa2}), and
> Phi2 ∤ f_S <=> Phi2 ∤ f (S2 peel); availability at the
> perturbed key is GENTOW-4.1(c). That the >T2 part is the
> INITIAL segment and spans [0, mu2*]: hull slopes (height drop
> per unit j) strictly decrease left to right, so the >T2 sides
> are leftmost; P2(f_S) spans [0, mu2*] entirely with ALL sides
> > T2 (LEMMA HE7-9(a) + HE7.A(1) at f_S) and right endpoint
> (mu2*, 0) (f_S monic of Phi2-length mu2*), so its c_g-translate
> — which HE6R1-2(b) identifies with the >T2 part of P2(f) —
> spans [0, mu2*] with right endpoint (mu2*, c_g). GENHN-2'
> supplies the pins p_j exactly on the locus (its proof reads
> coefficient degrees < D2 and the two-step class separation,
> both intact at the partial side; the top coefficient C_M has
> deg n − M·D2 < D2). (iii): THEOREM HE7.A's hypothesis list at
> (kappa2, rtilde), f_S, key Phi2 is discharged row by row by
> HETOW_RECON's S1 table with the three fullness rows replaced by
> GENTOW-4.1(a)(b) (datum + label rows) and by (ii) here (the
> f_S/mu2 row: mu2* := deg f_S/D2 is HE7.A's own mu2, now READ
> from f); the dictionary display is HE7.A(2)'s with (l, d_r) =
> (e2, f2). (iv): the same instantiation at the other data; at
> mu2* = 1 the single side has L = 1, hence l2 = 1, deg R_{lambda2}
> = 1: HE7.A(2) gives one factor (e1·l·1, f1·d_r·1); the
> separable-R_kappa consistency is THEOREM HE6.A. (v): at
> mu2* = 2 the >T2 segment [0,2] has the three displayed shapes;
> each maps under the c_g/gamma_g-invariances to T(b)'(iii)'s
> trichotomy at the block (= HETOW.A(iii)'s mu2 = 2 read); the
> refine leg re-enters (ii) at the refined key. ∎

## S4. LEMMA GENTOW-4.2 (the multiplicity tie) + COROLLARY GENTOW-4.C (the c_g-read)

> **LEMMA GENTOW-4.2 (tie, PURE-POWER sides).** If the inner
> side's residual is a pure power — R_{kappa2} = c·psi2^{mu2},
> c in K^x (the PE2-P shape and every single-repeated-class side)
> — then mu2* = mu2: the composed polygon length equals the
> level-1 residual exponent, and deg f_S = D2·mu2 = D'·e2f2·mu2.
>
> *Proof.* LEMMA HE6-3 (quoted in THEOREM HE6.A's proof step 1
> with no separability hypothesis): the side of length L_side =
> e2·deg R_{kappa2} = e2f2·mu2 carries exactly n_{kappa2} =
> D'·L_side roots of f with dv(Phi'(x0)) = kappa2. Every such
> root's letter is a root of iota(c·psi2^{mu2}), whose only
> irreducible factor is psi2 — so ALL of them lie in the one
> class: |S| = D'e2f2·mu2. LEMMA HE6R1-2(b) (via GENTOW-4.A(ii))
> gives |S| = deg f_S = D2·mu2* = D'e2f2·mu2*. Divide. ∎
>
> At a MIXED side (R_{kappa2} = psi2^{mu2}·Rhat, Rhat coprime to
> psi2, deg Rhat >= 1) the read is UNCHANGED — mu2* is computed
> from f and the decision (iii)/(v) fires — but the TIE
> mu2* = mu2 is NOT derived here: the level-1 count splits as
> Sum_r |C_{kappa2,r}| = D'·L_side (LEMMA HE6-3) with each class
> pinned only by its own projection, and matching each mu2*(r) to
> the multiplicity m_r requires the residual-multiplicity
> transport this corpus has not proved (HE7-BOX-4 declined
> exactly this; Ore's second theorem / FGMN Lemma 2.17 content).
> Honest box: GENTOW4-BOX-1 (S7). The battery includes a mixed
> family (FAM-P5) run in read-mode: every decision PARI-exact,
> tie checked EMPIRICALLY (mu2* = m_r on every member).

> **COROLLARY GENTOW-4.C (the c_g-read — absolute block pins from
> f's digits).** In GENTOW-4.A(ii): c_g = the height of P2(f) at
> abscissa mu2* (the right endpoint of the >T2 initial segment),
> and the block pins are p_j^S = p_j − c_g wherever (j, p_j) lies
> on the >T2 hull. Consequently GENTOW-1(c)'s node floors are
> VISIBLE THROUGH THE PROJECTION: p_j^S >= (mu2* − j)E2 + 1 for
> j < mu2* (LEMMA GENTOW-1(c) applies to f_S, whose entry is
> full-side by construction: its own level-1 read is the one side
> of slope kappa2 with residual (unit)·psi2^{mu2*}). At PE2-P:
> c_g = 5, p^S = (23, 11), floors (21, 11) — j = 1 exact.
>
> *Proof.* Right endpoint: displayed inside GENTOW-4.A(ii)'s
> proof. Translation: HE6R1-2(b). The floor transport: f_S
> satisfies GENTOW-1's 𝒯-definition at (Q; e1,f1, e2f2·mu2*; h)
> with the same (u2, e2, psi2): its roots are exactly the class S,
> all tower-node points; GENTOW-1(a)(c) applied to f_S gives the
> floors; the projection carries them to f's pins. ∎
>
> Note the LOAD-BEARING parity flip: the RAM test is p_0^S odd,
> and c_g need not be even (PE2-P: c_g = 5), so the f-level parity
> p_0 mod 2 is NOT the block parity. Equivalently (and how S3(v)
> states it): decide RAM by the SLOPE's denominator, which is
> translation-invariant. A reader using f-level pin parity is
> wrong exactly on odd-c_g members — tooth T-NOCG.

**REMARK (coherent digits — machine-surfaced at the pre-seal
smoke, derivation displayed).** S3(v)'s residual tests consume the
residuals in HE7's COHERENT normalization; RAW slot residues are
NOT them when the class letter eta2 != 1. At (e2, f2) = (2, 1),
u2 odd: the wrap Phi'(x0)^2 = eta2·nhat(u2)(x0)·(1 + small) makes
the height-0 monomial ratio x^{Δa} pi^{Δv} Phi'^{Δb} have residue
eta2^{Δb/2} (Δb is forced even; the x- and pi-relations have
residue 1 at f1 = 1), so the coherent digit at coordinate j of an
integer-slope [0,2]-read is

    delta_j = r_j · eta2^{(b_j − B_j)/2},
    N_j := n2hat(c_g)·n2hat(lam)^{2−j},  B_j = b-exponent of N_j,

with r_j, b_j the raw residue and Phi'-exponent of the attaining
slot. Feeding r_j instead of delta_j flips INERT/SPLIT exactly on
eta2 != 1 members: FAM-P5 (psi2 = T+1 over F_3, eta2 = 2) exposed
12 such flips against PARI at the smoke; q = 2 families and
eta2 = 1 rows are structurally blind to the defect. The corrected
reader is the sealed one; the defect is preserved as tooth
T-6 NOTWIST. (This is HETOW's T-BADTWIST phenomenon at the
partial-side read — the S4-normalizer cocycle is machine-load-
bearing here too.)

## S5. PE2-P VERIFIED EXACTLY

Hand computation (S1's table, re-derived; machine row PE2P-0 in
the battery): level-1 pins (0,13),(1,10),(4,4),(5,0); hull
(0,13)–(1,10)–(5,0); sibling side slope 3, length 1, residual
digits res(64x/nhat(13)) = 1, res(32/nhat(10)) = 1 -> linear ->
one factor (2,1) [GENTOW-4.A(iv), mu2* = 1]. Inner side slope 5/2,
length 4, lattice J in {1,3,5}, digits (1, 0, 1) -> R = T^2 + 1 =
(T+1)^2 over F_2: pure power, psi2 = T + 1, mu2 = 2, e2f2mu2 =
4 < 5 = mu1: PARTIAL. Phi2 = Phi'^2 − 4x; E2 = T2 = 10.
Phi2-development of f: C2 = Phi' + 4, C1 = 8xPhi' + 32x + 16,
C0 = 128x^2 + 128x − 128; pins p = (28, 16, 5); hull
(0,28)–(1,16)–(2,5), slopes (12, 11), both > 10: mu2* = 2 = mu2
(LEMMA GENTOW-4.2 both ways), c_g = 5, block pins (23, 11, 0).
TWO distinct slopes -> S3(v) first row -> {(4,1)} x2. Total
sigma = {(2,1)} ∪ {(4,1),(4,1)}.
ORACLE (PARI, factor + idealprimedec and factorpadic routes,
2026-08-09): disc != 0; sigma = {(2,1),(4,1),(4,1)} — EXACT.
Per-factor valuations: deg-2 factor dv2(Phi2) = 10 = E2 exactly
(steeper sibling: the t = 0 lift term of Phi2 dominates); deg-4
factors dv2(Phi2) = 12 and 11 = THE TWO POLYGON SLOPES (HE7's
side dictionary at the composed carrier, visible in nfeltval),
both > E2 (GENTOW-1(d) at the block). dv2(Phi') = 5 = u2 on both
tower factors ((T1_2) transport); dv(Phi') = 3 on the sibling
factor (its own side slope).

## S6. MACHINE LEG (`verification/openmath/gentow4_checks.py`) — sealed at commit 1

Design, preregistered predictions P-1..P-7 and teeth T-1..T-5 in
the runner's docstring, sealed BEFORE the first full run (wiring
smoke on PE2P-0 and family constants disclosed there). Families:

| family | genre | q | inner (e2,f2,u2) | sibling | n | menu (tower part) |
|---|---|---|---|---|---|---|
| P1 | (2,1,5) | 2 | (2,1,5) side [1,5] | slope 3, len 1, left | 10 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(2,1)}) |
| P2 | (2,1,5) | 2 | (1,2,3) side [1,5], K2=F4 | slope >=4, len 1, left | 10 | {(4,2)},{(2,4)},{(2,2)}x2 (+ {(2,1)}) |
| P3 | (2,1,5) | 3 | (2,1,5) side [1,5] | slope 3, len 1, left | 10 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(2,1)}) |
| P5 | (2,1,6) | 3 | (2,1,5) MIXED side [0,6]: (T+1)^2(T−1) | (same side, simple class) | 12 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(4,1)}) |
| P6 | (2,1,7) | 2 | (2,1,5) side [0,4] | slope 7/3, len 3, RIGHT | 14 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(6,1)}) |

PREREGISTERED PREDICTIONS (sealed in the runner docstring before
the first full run; restated here at composition time, BEFORE any
battery output exists):
* P-1 (parse gate): every member's level-1 hull + side residuals =
  the family targets (partial inner side, pure/mixed as designed).
* P-2 (HEADLINE): the S3/S4 reader (per-class composed read,
  c_g-translation, slope/residual trichotomy, sibling classes at
  their own data) decides every member with sigma = PARI exactly
  (route 1 all members; route 2 subsample), including PE2P-0 (the
  witness row) verbatim.
* P-3 (tie): mu2* = mu2 on every pure-side member; on FAM-P5
  (mixed) mu2* = 2 at the repeated class and 1 at the simple class
  — an EMPIRICAL check of the boxed tie (measurement, not proof).
* P-4 (c_g + floors): the >T2 segment spans [0, mu2*]; c_g =
  p_{mu2*}; block pins p_j − c_g clear GENTOW-1(c)'s floors; c_g
  is ODD on a nonempty set of members (the parity flip is live).
* P-5 (field-floor separator): per factor per prime, class factors
  have dv2(Phi2) > E2 strictly; sibling/companion factors = E2 on
  steeper-or-same flanks (P1/P2/P3/P5) and < E2 on the shallow
  flank (P6); dv2(Phi') = u2 exactly on class factors.
* P-6 (windows): decided reads invariant under random p^N-lifts
  below the cap.
* P-7 (refine rows): double-root members refined by Phi2 −
  s·n2hat(lambda2) kill the event pins; re-read decides, PARI-exact.
TEETH (all must fire): T-1 FULLREAD (the T(b)'(iii) monic reader
refuses every member — the loud failure stays loud); T-2 NOCG
(parity-on-f mutant flips RAM/non-RAM on c_g-odd members; PARI
must kill every flip); T-3 SIBDROP (tower-class-only sigma != PARI
on every member); T-4 WITHHOLD (psi2 withheld -> UNDETERMINED, no
guess); T-5 WRONGKEY (FAM-P5 cross-key probe: the (T+1)-class read
with the (T−1)-class's key must NOT reproduce the block data);
T-6 NOTWIST (added pre-seal from the disclosed smoke finding, S4
remark: dropping the eta2-cocycle correction must flip INERT/SPLIT
on eta2 != 1 members, every flip PARI-killed).

**VERDICT — appended at commit 2 from the committed artifacts: see
the "S6-VERDICT" block at the end of this file.**

## S7. HONEST RESIDUE + GRADE BOX

**What item (4) still keeps (named exactly):**
* **GENTOW4-BOX-1 (the mixed-side multiplicity tie).** At sides
  carrying >= 2 distinct residual classes with a repeated one, the
  tie mu2*(r) = m_r (composed length = residual multiplicity per
  class) is UNPROVED here (S4; Ore-II/FGMN Lemma 2.17 content —
  a faithful-cite unit in GENTOW2's pattern would retire it). The
  READ and sigma are unaffected (mu2* is computed, not assumed);
  what is lost without the tie is only the level-1 PREDICTION of
  each block's length. Machine: empirically exact on FAM-P5.
* **GENTOW4-BOX-2 (partial-side entry budgets / count laws).**
  GENTOW-1's budget fibration is proved on the FULL-side locus 𝒯;
  the partial-side locus (products of class boxes + sibling data)
  has no budget/count display here — the item-(4) COUNT layer
  stays open (it was open at full sides' LEDGERS too, GENTOW-1
  remark). sigma-decision only in this unit.
* **GENTOW4-BOX-3 (coverage).** mu2 = 2 inner events only (mu2 >= 3
  partial towers = this read + [GENHN-HE(mu2)] for the block's
  menu — the block decision (iii) hands off to HE7.A exactly as
  HETOW does at full sides); f1 = 1 outer keys; q in {2,3}; e2 in
  {1,2}; depth 2; d = 1 ambients. The S2–S4 proofs are uniform in
  all of these (S3(iii) is stated at any mu2*); the gap is
  machine-side, named.
* **GENTOW4-BOX-4 (grade).** 0/2 attempt, composed this session,
  no hostile arc. Conditionality stack: LEMMA GENHN-T(b)'(i)(ii)
  + the [r1] node floor (GENHN accepted 2/2 at PE4), HETOW-1/2
  (HETOW 0/2), LEMMA HE6R1-2/HE6R1-3 + RIDER (HE6R1 post-r2,
  0/2-grade annex stack), THEOREM HE7.A/C/D + HE7-12/13 + ANNEX
  HE7-13' (HE7 accepted 2/2; annex F-1 post-acceptance), LEMMA
  HE6-3/HE6-4 + THEOREM HE6.A (HE6 accepted, r1/r2 applied),
  GENTOW-1 (0/2). Every consequence inherits the MINIMUM grade.

**Consumption path (not executed here):** [GENHN-TOW-1] item (4)'s
box text in GENHN_PROOF is the orchestrator's dated consumption
update after this note's own hostile arc; GENHN_PROOF, HETOW_RECON,
HE7_PROOF, HE6R1_RECON are byte-untouched by this unit. The
GENHN.B (CS-3) partial-side rider (passPE2 F2's cure) can, after
acceptance, cite THEOREM GENTOW-4.A(v) for inner-mu2 = 2 partial
leaves at pure-power sides — with GENTOW4-BOX-1 named at mixed
sides.

---

## S6-VERDICT (commit 2, from the committed artifacts): **GREEN — 1,740 checks, 0 violations, 6/6 teeth**

**Artifacts.** `gentow4_checks_output.txt` (committed); sealed
runner @ commit 1 = 2aa5b16, md5 98cdd4a4e5a47f1434bfd... (full
md5 printed in the artifact: 98cdd4a4e5a47f1434bfd — see line 2 of
the output; no post-seal edit — verdict-run md5 IDENTICAL to the
sealed file). Runtime ~5 s + PARI (371 gp jobs).

**Totals.** 117 members (P1 25 incl. PE2P-0, P2 24, P3 22, P5 22,
P6 24), 0 dropped, 117 reader-decided, 117 sigma comparisons on
PARI route 1 + subsample on route 2, per-factor valuation rows via
nodev6 on every member. **1,740 checks, 0 violations.**

* **P-1 ✓** every member parsed to its family target (partial
  inner side present; hull exact; residual classes as designed).
* **P-2 ✓ (HEADLINE)** every member DECIDED by the S3/S4 reader
  and sigma = PARI exactly, both routes where run; PE2P-0
  reproduced the witness {(2,1),(4,1),(4,1)} — the box's
  protected instance now has a proved, machine-checked read.
* **P-3 ✓** mu2* = 2 = mu2 on every pure-side tower class; on the
  MIXED family P5, mu2* = 2 at the repeated class and (4,1)-content
  at the simple class on every member (empirical tie only —
  GENTOW4-BOX-1 unchanged).
* **P-4 ✓** >T2 initial segment = [0, mu2*] with c_g at the right
  endpoint; GENTOW-1(c) floors cleared through the projection on
  every row; c_g ODD on 71 tower reads (P1/P2/P3 flanks) and EVEN
  on 46 (P5/P6) — both parities live.
* **P-5 ✓** per factor per prime: class rows dv2(Phi2) > E2
  STRICT with class degrees summing to D2·mu2* = 8; companion
  rows = E2 exactly on steeper/same flanks and < E2 on P6's
  shallow flank; dv2(Phi') = u2 exact on class rows.
* **P-6 ✓** 15 members x 2 random p^14-lifts: reads identical.
* **P-7 ✓** every DBL row's refine chain (inside the reader, key
  Phi2 − s·n2hat(lam), the coherent s) terminated decided,
  PARI-exact.
* **TEETH 6/6 FIRED:** T-1 FULLREAD (117/117 refused by the monic
  reader); T-2 NOCG (49 parity flips, every one PARI-killed — the
  c_g-translation is machine-load-bearing); T-3 SIBDROP (117/117);
  T-4 WITHHOLD (UNDETERMINED, 0 guesses); T-5 WRONGKEY (22/22 P5
  probes: wrong key never reproduces the block datum; incl. the
  key | f peel corner); T-6 NOTWIST (8 INERT/SPLIT flips without
  the eta2-cocycle correction, every one PARI-killed — the S4
  coherence is load-bearing, S4 remark).

**Diagnostic census (non-sealed one-off, labeled):** every family
realized its FULL preregistered menu — P1: {(2,1)}∪{(8,1)} x12 /
{(4,2)} x6 / {(4,1)}² x7; P2: {(2,1)}∪{(4,2)} x20 / {(2,4)} x2 /
{(2,2)}² x2; P3: 13/2/7; P5: {(4,1)}∪ 10/6/6; P6: {(6,1)}∪ 11/8/5.

**What the leg establishes** (instrument grade, not acceptance):
the first machine contact anywhere with [GENHN-TOW-1] item (4) —
partial-side tower members at 3 genres, q ∈ {2,3}, e2 ∈ {1,2},
f2 ∈ {1,2}, mixed sides, both sibling flanks — is GREEN against
an independent oracle, with the block decomposition, the HE6R1-2
projection (c_g), and the per-block HE7.A trichotomy executed
exactly as THEOREM GENTOW-4.A displays, and with three
load-bearing seams (c_g-translation, label-keying, eta2-cocycle)
each guarded by a fired tooth.
