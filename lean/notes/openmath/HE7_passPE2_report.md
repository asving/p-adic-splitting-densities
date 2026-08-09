# HE7 passPE2 — hostile verification report (fresh context, zero prior stake)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 3 MINOR (+2 remarks). Nothing at
GAP-or-worse survived my verification attempts. Machine leg: all seven §S11
pins byte-identical worktree = HEAD = r2 83ced80 = leg 1811605; isolated
re-run of `he7r2_supp.py` GREEN (42/210/42/42/13, 0 violations, JSON
leaf-diff = timing only); the 42-vs-41 recount independently reproduced from
the frozen artifact. Fresh route GREEN: a sealed-then-run CONSTRUCTED
α-refine family at the d_r = 2 frame (K₂ = F_{p²} proper, 634 members,
0 violations, σ == PARI 634/634) — the first machine exercise of
LEMMAS HE7-12/HE7-13 with d_r ≥ 2 anywhere, including the first-ever
2-step refine chains (4 members) — plus a 1,056-config exact polytope leg
for (S5.8.1) at frames incl. d_r = 3 and f₁ ∈ {2,3}. Per HE7-BOX-1 [r2],
the 2-clean count STARTS: attempt grade moves 0/2 → 1/2.**

Target: `lean/notes/openmath/HE7_PROOF_2026-08-08.md` at HEAD (r2 complete
at 83ced80 + machine leg 1811605; arc seal 1956151 → verdict 4c42f9d → r1
aafb481/d58680e/2970615 → PE1 5c98481/7b66364 → r2). Prior report
`HE7_passPE1_report.md` read first; its routes not re-walked. Prime surface:
§S5.8 (LEMMAS HE7-12/HE7-13 — the r2 new math, never attacked), the r2
wirings at THEOREM HE7.A(3) / LEMMA HE7-8 / §S8 row 5, the F-2/F-3/F-4
display repairs, and the §S11 [r2] leg + disclosures. Protocol:
quote-and-classify, fix nothing.

Attack order executed: (1) LEMMA HE7-12 re-derived from the slot data —
(S5.8.1) re-derived line by line, adversarial (δ, ε₀, ε₁) hunt on all
strata incl. PE1 F-2's middle band; clause (b)'s exact-value claim; clause
(c) audited item-by-item (7 of the 11 re-walked at their §S5 use sites);
clause (d)'s chain fold. (2) LEMMA HE7-13's residue-match derivation and its
(LIFT₂) dependence post-refinement. (3) The r2 display alignment against
the sealed runner's `lift2`. (4) The 42-recount from the frozen JSON.
(5) The r2-touched sites S2/S5.2/S6/S7/S8/S9/S11 for collateral damage.
(6) Free hunt + instrument audits + fresh route.

---

## FINDINGS

### F-1 [MINOR] HE7-12(d)'s "covered by ONE instance of (a)–(c)" needs
### W ≠ 0, which is true but underived

**Location:** §S5.8, LEMMA HE7-12 clause (d).

**Quote:** "if w₁, …, w_j each have degree < D″ and slot value > T₂ then
W := w₁ + ⋯ + w_j has deg W < D″ and dv₂(W) ≥ min_i dv₂(w_i) > T₂ (the
slot-min is ultrametric slotwise), so every iterate Ψ − W of a refine chain
is covered by ONE instance of (a)–(c)."

LEMMA HE7-12's hypothesis is "w ∈ O[x], **w ≠ 0**", and clause (d) never
shows W ≠ 0 (ultrametric ≥-bounds allow total cancellation in general). In
a genuine refine chain W ≠ 0 always: dv₂(w_i) = λ₂^{(i)} are pairwise
distinct by LEMMA HE7-13's strict increase (inductively available at each
step), so the slot-min of the sum is attained uniquely and
dv₂(W) = λ₂^{(0)} < ∞ exactly — one classical-ultrametric line. And even at
W = 0 the conclusion cannot fail (Ψ − 0 = Ψ carries §S5 itself, exactly how
LEMMA HE7-13's own statement handles its "W = 0 or as in LEMMA HE7-12(d)"
case). Failure scenario: none for the mathematics; a maximally literal
reader of (d) alone lacks the W ≠ 0 warrant to invoke (a)–(c). Display
completeness only.

### F-2 [MINOR] LEMMA HE7-8's [r2] hypothesis-matching sentence overreaches
### when a peel fires MID-chain (μ₂ ≥ 3 only; vacuous at every certified
### degree)

**Location:** §S7, LEMMA HE7-8's [r2] box; consumed at THEOREM HE7.A(3)
and §S8 row 5.

**Quote:** "**[r2, HE7-PE1 F-1] The hypothesis set is the read's ACTUAL
configuration, derived rather than presumed:** … and the strictly
increasing slope clause λ₂^{(0)} < λ₂^{(1)} < ⋯ is LEMMA HE7-13, so an
infinite chain of the read really has the properties this lemma refutes."

LEMMA HE7-8's hypothesis fixes ONE f_S and ONE μ₂ along the whole infinite
chain. A read chain can interleave peels (LEMMA HE7-13 itself routes "after
the peel of LEMMA HE6R1-3 at Ψ̃^{(1)}, if it fires"), and a peel replaces
f_S by f_S′ and drops μ₂ by 1 — so a peel-interleaved infinite chain does
NOT literally have the boxed sentence's properties. The conclusion
(finiteness) still holds by displayed material plus one pigeonhole
sentence: peels number ≤ μ₂ − 1 (each drops μ₂ ≥ 2 → μ₂ − 1, and μ₂ = 1 is
decided), so an infinite chain has an infinite constant-μ₂ tail on a fixed
f_S^{(seg)} with disc ≠ 0 (a factor of the separable f), which LEMMA HE7-8
refutes; equivalently, THEOREM HE7.C's tree argument already books a peel
as a strictly-μ-decreasing step. Vacuous wherever the note certifies: at
μ₂ = 2 (n = 8, the whole sealed battery) a peel forces μ₂′ = 1 and ENDS the
chain — consistent with the machine record (46 observed refine firings
across all legs incl. mine, zero mid-chain peels). Statement-display
overreach with an in-toolkit repair, no consumer broken.

### F-3 [MINOR] §S11 [r2]'s "B2 … (S5.8.1) … 210/210" is quantitatively
### vacuous on the δ = ∞ stratum for 41 of 42 members (undisclosed)

**Location:** §S11 [r2] (the slot-domination leg paragraph) and the §S5.8
machine-confirmation paragraph.

**Quote:** "**B2** the off-disk inequality (S5.8.1) in resultant-sum form
plus the invariance conclusion …, on five off-disk strata per member
covering all three offset cases of the lemma (δ = ∞; …) — **210/210**".

In `he7r2_supp.py` the quantitative half is skipped when Res(g, w) = 0
(`if a_w < BIG and …`). On the δ = ∞ stratum g = Φ′ this fires whenever
λ₂ is odd, since then s₀ = s(λ₂) = 1 and w = c·nrm(m₀)·Φ′ is divisible by
Φ′. My probe over the regenerated 42: λ₂ ∈ {11, 15} (odd, w ∝ Φ′,
quantitative half vacuous) on 41 members; λ₂ = 12 on exactly 1. So
"210/210" = 210 stratum passes of which the δ = ∞ inequality was actually
TESTED on 1 member (the other 41 mathematically trivial there:
dv₂(w(ξ)) = ∞, and invariance was still genuinely checked on all).
Mathematically harmless — no false claim about the lemma — but the
machine-sentence lets a reader believe 210 nontrivial inequality
instances. My fresh leg re-verified the stratum non-vacuously (Res(Φ′,w)≠0
on the majority of 634 members, all green). Disclosure nit only.

---

## REMARKS (not findings)

* **R-a.** `he7r2_supp.py` B3 silently skips the HE7-9(b) identity when the
  refined key divides f (`if dv2s1[0] < BIG`); the skip never fired on the
  42 (all a_f1 finite), and my fresh leg's identical guard never fired on
  634. Accountability preserved by the strict-increase check either way.
* **R-b.** B1's (LIFT₂)-contract check verifies the sealed `lift2` output
  through `dv2`/`res2` (independent of `lift2`'s internals but from the
  same module) — mild same-instrument coupling; my fresh leg re-implements
  both sides independently and agrees.

---

## CLEAN CHARGES (attacked and survived)

1. **(S5.8.1) re-derived from scratch and adversarially probed.** The two
   loss terms re-derived: level-1 coefficients lose ≤ (D′−1)ε₀ each (i ≤
   D′−1), ℓ-scaled to ℓ(D′−1)ε₀; slot factors lose ≤ (ℓd_r−1)ε₁ (s ≤
   ℓd_r−1); Ψ's off-disk value T₂ − ℓd_r·ε₁ from HE7-4 with ε = 0 (a
   non-level-2 point with δ = λ and root residue is impossible: HE6-0
   forces δ ≤ D′h < λ off (T1)/(T2)); subtraction gives the display
   EXACTLY. Positivity: the case split is exhaustive, and the adversarial
   region "ε₀ > 0 with ε₁ small" is EMPTY — ε₀ > 0 forces dv ξ < h, hence
   (T1) fails, hence δ = D′(h−ε₀) by HE6-0, hence ε₁ = ℓ(λ−D′h) + ℓD′ε₀ ≥
   ℓD′ε₀ > ℓ(D′−1)ε₀; the middle band D′h < δ < λ forces ε₀ = 0 (δ > D′h
   is impossible off (T1)/(T2)) and consumes only ε₁ > 0 — PE1 F-2's
   counter-band cannot re-enter. Machine: 3,170 stratum checks (fresh) +
   1,056 exact polytope configs (frames incl. d_r = 3, f₁ = 2, 3) all
   positive.
2. **HE7-12(b)'s exact-value clause**: (SLOT₂) applies verbatim (deg w <
   D″, w ≠ 0 hypotheses present); ν ∈ ℤ so n₂(ν) is defined; c_w =
   Σγ_tβ^t ∈ K₂ ∖ {0} by (SLOT₂)(b)'s no-cancellation (K-basis argument),
   ξ-independent. Fresh leg: res₂(w, λ₂) = s₂ on 634/634 incl. 520 with
   s₂ ∉ K.
3. **HE7-12(c) audited at 7 of its 11 items** against the actual §S5
   proofs: (item 3) S5.3 consumes from HE7-4 exactly the off-disk value
   formula + the disk criterion — both = (a)+(b); no §S5 site consumes
   HE7-4's on-disk excess form (checked HE7-7, HE7-7′, HE7-9/10, HE6R1-3's
   peel); (item 5) the key enters Step 1 only through δ₂ and its off-disk
   formula; (item 6) developments in the monic degree-D″ refined key have
   deg < D″ coefficients, so (SLOT₂) applies; (item 2) the C_t are
   key-free (LIFT₂) objects; (item 8) r₂,₀ of degree μ₂+1 is key-free;
   (item 11) a root of Ψ^{(w)} has dv₂ = ∞ > T₂, is a level-2 point by
   (b), so HE6R1-3's proof runs verbatim and the (e,f) sandwich forces
   irreducibility; (item 4) HE7-5 uses only v(key(ρ)) ∈ (1/e)ℤ + unit
   residues. All hold with the SAME proofs, as claimed.
4. **HE7-12(d)'s degree and slot-min claims**: sums of deg < D″ polys have
   deg < D″ even across different iterates (the w_i are all (LIFT₂)
   outputs at ONE frame); slotwise ultrametric subadditivity re-derived
   (development of a sum = sum of developments; dv ultrametric per level-1
   coefficient); the ≥ min direction is the needed one. (The W ≠ 0 nit is
   F-1.)
5. **LEMMA HE7-13 re-derived.** The single-side count n_{λ₂} = D″μ₂ =
   deg f_S (HE7-9(b), (SEP)-free) forces EVERY root's label; HE7-7″ +
   R₂ = (Z−s₂)^{μ₂} forces β₂,ρ = ι_ρ^{(2)}(s₂); s₂ ≠ 0 from the attaining
   j = 0 endpoint (A₀ ≠ 0 under the standing convention); (‡₂) at k = λ₂ >
   T₂ re-checked via §S4.3's chain; the residue match kills the leading
   residue so dv₂(Ψ̃^{(1)}(ρ)) > λ₂ (n₂(λ₂)(ρ) exact at level-2 points).
   **(LIFT₂) needs no per-iterate re-proof: its statement never mentions
   the key** (it is about C ∈ O[x], the Φ′-slots and the level-2 points,
   all refine-invariant), so surjectivity + the residue contract are
   available at EVERY iterate on the ORIGINAL frame data; the refined key
   enters only through the polygon/label package, which is HE7-12(c).
   Machine: strict increase + HE7-9(b) at the refined key 42/42 (sealed
   enumeration) + 634/634 (fresh, d_r = 2), and the wrong-residue tooth
   (residue s₂′ ≠ s₂ gives dv₂-sum EXACTLY 8λ₂, no increase) fired
   634/634 — the residue match is machine-load-bearing.
6. **The display alignment (attack item 3).** The sealed runner's refine
   subtracts `fr.lift2(lam2, s2)` = c·π^{⌊m₀/2⌋}x^{m₀ mod 2}·Φ′^{s₀},
   degree ≤ 1 + 2s₀ ≤ 3 < D″ — the note's [r2] displayed w (a (LIFT₂)
   polynomial), NOT the pre-r2 "ŝ₂·n₂(λ₂)" (as a literal power product
   x^{m₀}Φ′^{s₀} of degree 5 ≥ D″ at λ₂ = 11 it would not even be a
   HE7-12-eligible perturbation). Note and instrument now display the same
   object; slot value and residue verified 42/42 + 634/634.
7. **The 42-vs-41 recount (attack item 4).** Independently recomputed from
   the frozen `he7_checks_results.json`: refine histograms sum to 42
   (9+1+5+0+0+5+0+0+3+8+6+2+3), every entry under key '1' (no multi-step
   member), member counts matching Q1's table row-for-row. The r2
   disclosure is exact; no other stale "41" survives in the note (grep:
   both remaining "41"s are the disclosure sentences).
8. **F-3 (PE1) integer-floor repairs**: S2's chain now "μ₂ ≤ ⌊μ/2⌋ ≤ 3
   since μ₂ ∈ ℤ_{≥1}" and HE7.B(i)'s "⌊7/2⌋ = 3", "⌊15/2⌋ = 7 … μ ∈ ℤ" —
   arithmetic correct, conclusions unchanged.
9. **F-4 (PE1) index repair**: HE7.D's (LIFT_i) has residues in K_{i+1}
   (bound₁ = (D′−1)h at i = 0, bound₂ = (‡₂) at i = 1, recursion checked);
   a refine at the level-i node needs K_i, i.e. (LIFT_{i−1}); the level-2
   instance (LIFT_{i−1}) = (LIFT_1) = (LIFT₂) with residues in K₂ matches
   HE7.A(3)'s display. Consistent everywhere.
10. **F-2 (PE1) repair at (S5.2)**: the corrected split is exactly the two
    clauses the S5.3 case analysis and (S5.8.1)'s positivity consume
    (ε₁ > 0 vs ε₁ = 0 at ε₀ = 0); the middle-band counter-instance is
    displayed; §S6's cascade uses the corrected form (δ_j < λ_j ⟹
    ε_j > 0). No consumer of the false half found (searched).
11. **S8 row 5 + the r2 wiring**: "α-refine (LEMMAS HE7-12/13 + HE7-8
    [r2]) → one of the above" — the four polygon rows and the sixth-row
    peel are licensed at the refined key by HE7-12(c) items (5)(6)(11);
    the [r2] paragraph's claim "displayed mathematics, not a pointer" is
    now accurate.
12. **§S9 [r2] honesty**: the box correctly keeps attempt grade 0/2
    post-r2 and names PE1's verdict; the "what is proved here" list adds
    §S5.8 without upgrading any conditionality; HE7-BOX-2's coverage
    sentence remains accurate (my fresh leg partially discharges the
    d_r ≥ 2 refine hole it names — everything-block, char 0 only,
    disclosed).

---

## MACHINE LEG (integrity)

* **Pins.** All seven files byte-identical at worktree = HEAD = r2 83ced80
  = machine-leg 1811605: `he7_checks.py` 688adbe88447…, output
  b2d095a2556a…, results f5bedab2ecda…, `he7r1_supp.py` 24ece42e4538…,
  `he7r2_supp.py` 71bb6202f72c…, its output 1e787536254c…, its results
  f45b5ab1e3b5…. §S11's displayed pins all match; `he7r2_supp.py`'s
  in-run pins (he7_checks 688a…, results f5be…, he6_checks 321f…,
  he7r1_supp 24ec…) verified.
* **Isolated re-run** (`/tmp/he7_pe2_sandbox`, committed artifacts
  untouched): GREEN, exit 0, 3.7 s, checks {B1 42, B2 210, B3 42, B4 42,
  B5 13}, 0 violations; results-JSON leaf-diff vs committed = {secs} only;
  output ex-timing IDENTICAL. Row parameters in `he7r2_supp.py` verified
  verbatim against the sealed `he7_checks.main()` (13 rows, W/cap/s all
  equal), and the B5 key (ring, s, u) is injective across the rows.
* **Instrument audit.** B2's bound is literally (S5.8.1) with ν = λ₂; the
  five strata's hardcoded (ε₀, ε₁) re-derived from the geometry and
  correct (incl. the F-2 middle band κ = (2u−1)/4, ε₁ = 1/2); B3 computes
  the HE7-9(b) identity from an independently recomputed hull AT the
  refined key — the PE1 F-1 gap is exercised, not assumed. Two niches
  found: F-3 (δ = ∞ quantitative vacuity) and R-a (peel-guard skip, never
  fired).

## FRESH ROUTE (disclosed; differs from all five prior routes)

Prior: (a) sealed 1,587-member battery (ℓ = 2, d_r = 1; 42 refine members
by chance); (b) HE6R1's 682-member ℓ = 1/d_r = 2 battery (no refine
members); (c) r1's 8-member peel supp; (d) PE1's constructed n = 12,
μ₂ = 3 peel family (refine skipped); (e) r2's 42-member slot-geometry leg
(d_r = 1, K₂ = F_p). **This route: `verification/openmath/he7_pe2_fresh.py`
(sealed pre-run at c786364 with preregistered P1–P6 and a disclosed
2-member smoke; artifacts committed at b3ed01b) — a CONSTRUCTED α-refine
family at ℓ = 1, d_r = 2, K₂ = F_{p²}:** p ∈ {3,5}, λ = u ∈ {3,5},
r = Z²+b, Ψ = Φ′² + b·nrm(2u), members f = Ψ² + A₁Ψ + A₀ slot-built so the
level-2 polygon is the single side λ₂ ∈ {2u+1, 2u+2} with residual
(Z − s₂)², s₂ ranging over ALL of F_{p²}^× — including 520 members with
s₂ ∉ F_p, a refine residue in a PROPER extension, reachable by NO prior
leg. Independent instrument (no he6/he7 import; own arithmetic, Bareiss
resultants, reader from the note's text; cypari2 factor+nfinit+
idealprimedec oracle, char 0 only — disclosed).

**Result: 634 members (6 disc-0 discards), 0 violations.** Read confirms
the constructed side + residual 634/634; slot geometry 634/634; (S5.8.1)
resultant-sum inequality + EXACT off-disk value formula Σdv₂(Ψ(ξ)) =
deg g·(T₂ − 2ε₁) + invariance on five strata (δ = ∞ mostly non-vacuous
here; δ > λ; middle bands ε₁ = 1/2 AND ε₁ = 3/4 = the PE1 seed 9/4 at
u = 3; ε₀ = 1) — 3,170 checks; HE7-13 strict increase + HE7-9(b) at the
refined key 634/634; **σ == PARI 634/634** across genres {(4,2)} 542,
{(2,2),(2,2)} 54, {(2,4)} 38; within-class slot ties (the d_r = 2
(SLOT₂)(b) mechanism) live on 524 members; **the first multi-step refine
chains ever observed (4 members at chain length 2, exercising HE7-12(d)'s
fold W = w₀ + w₁ and HE7-13 along a genuine chain — all green)**; teeth:
wrong-residue w′ leaves the dv₂-sum EXACTLY flat 634/634, the lazy
dictionary (repeated residual misread as split) caught by PARI on 580
members. Plus the symbolic (S5.8.1) polytope leg: 1,056 exact-rational
admissible configs at 6 frames incl. (e₁,f₁,h,ℓ,d_r) = (3,2,2,3,3),
(2,3,1,2,3), (3,1,2,1,3) — d_r = 3 and f₁ ∈ {2,3}, HE7-BOX-2's
still-unexercised genres, symbolically — all positive.

## GRADE

0 CRITICAL, 0 GAP. The three MINORs are display/disclosure items whose
mathematical content I verified to be correct (F-1's W ≠ 0 holds and both
branches land the conclusion; F-2's finiteness survives via the note's own
tree bookkeeping, and the corner is vacuous at every certified degree;
F-3's vacuous stratum is mathematically trivial there and my fresh leg
verified it non-vacuously). LEMMAS HE7-12/HE7-13 SURVIVE hostile
re-derivation, adversarial configuration hunting, a bit-identical isolated
re-run, and a genuinely new machine frame. **This pass is CLEAN: per
HE7-BOX-1 [r2] the 2-clean count starts — attempt grade 0/2 → 1/2.** Owed
next: one more fresh hostile pass (PE3) for 2/2; the three MINORs can ride
along in any future edit round without resetting the count (they are not
statement-level).
