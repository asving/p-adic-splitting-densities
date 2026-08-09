# HETOW passPE2 — hostile verification report (fresh context)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 3 MINOR.** The [r1] wrap-cocycle
repair HELD under independent re-derivation and under a five-frame
fresh route (first multi-wrap f₂ = 3, first η ≠ 1 × e₂ = 2, first
η ≠ 1 × f₁ = 2 two-digit (LIFT), ord(η) ∈ {5, 6, 8}, first non-prime
q = 4): 20/20 dual-route PARI σ jobs at the preregistered values, the
letter clause machine-confirmed on both sides of the seam at three
frames, the F-2 accounting identity verified at r′ = e₁−2 maximal, and
the F₄[[t]] construction oracle GREEN. Nothing at GAP-or-worse
survives this pass: per the arc rule the tower σ-closure counter moves
0/2 → 1/2. The pass also surfaced a σ-BLIND face of the seam (frame V:
the gauge-naive key has the CARRIER's σ, wrong letter) — recorded
under F-B, MINOR because the note's records are frame-derived and the
letter clause is what the theorem states.

Target: `lean/notes/openmath/HETOW_RECON_2026-08-09.md` @ HEAD
(r1 landed at d0d3ca6/5335ae3; arc seal → PE1 (1C+2G+2m) → r1).
Protocol: quote-and-classify, fix nothing. Verifier legs: independent
re-derivation of the wrap cocycle, the corrected key, HETOW-1/2 as
restated, the GENHN erratum's scope claim; machine-leg integrity
(pins + isolated re-run + tautology audit); fresh-route instruments
`hetow_pe2_fresh.py` (frames V/U/S/R, dual PARI routes) and
`hetow_pe2_freshT.py` (frame T, non-prime q = 4, construction oracle),
sealed at 7151fd8 — frames disjoint from the sealed battery (η = 1),
PE1's X/Y, r1's Z/W.

---

## ATTACK 1 — the [r1] corrected key, re-derived (HELD)

Re-derivation, independent of the note's text, from
n̂(k) = x^{i(k)}π^{a(k)}, 0 ≤ i(k) < e₁, i(k)h + a(k)e₁ = k:

* i(a)+i(b) = i(a+b) + e₁·wrap and height additivity force
  a(a)+a(b) = a(a+b) − h·wrap, so n̂(a)n̂(b) = n̂(a+b)·(x^{e₁}/π^h)^{wrap}
  and Q(a+b) = Q(a)+Q(b)+wrap — the preamble's two displays ✓.
* Telescoping: (f₂−t)i(u₂) = i((f₂−t)u₂) + e₁W(t) with
  W(t) = ⌊(f₂−t)i(u₂)/e₁⌋ (both sides ≡ mod e₁, range pin) — the two
  W displays ✓; res(n̂(k)/ϖ^k) = η^{−Q(k)} from ϖ^k = n̂(k)(x^{e₁}/π^h)^{Q(k)} ✓.
* (LIFT): each basis monomial of L_k(c) is n̂(k)·(x^{e₁}/π^h)^j —
  exact height k, x-degree ≤ D′−1, ϖ-residue c·η^{−Q(k)}; π-exponent
  availability a(k) ≥ (f₁−1)h ⟺ k ≥ (D′−1)h ✓ from the node floor.
  Hence the corrected slot coefficient −L_{(f₂−t)u₂}(c_t·η^{W(t)}) has
  ϖ-residue −c_t·η^{−(f₂−t)Q} = r̃'s t-coefficient — HETOW-1(c) ✓;
  the gauge-naive residue −c_t·η^{−(f₂−t)Q−W(t)} ✓.
* HETOW-1(a): η^{−Qf₂}ψ₂(η^QZ) expanded ✓ (t-coefficient
  −c_tη^{−(f₂−t)Q}); (b) is pointwise (single height u₂ normalized, no
  normalizer product) — wrap-free ✓.
* Frame X recomputed by hand: naive slot poly (Z+1)², corrected
  = minpoly(β) = Z²+2Z+2 — matches the note and the supp artifacts;
  frames Z/W hand-checked the same way (keys, r̃ = Z²+3Z+4, naive
  (Z+1)(Z+2)) — the S7 record's exact values verified.

**Sole-definition restatement sweep (does anything downstream still
consume the OLD slot-residue definition?): NO consumer found.** The §S1
r̃-row and Ψ-row point at HETOW-1/HETOW-2 [r1]; the pins row and (SLOT₂)
row are height-level (unit-blind); HETOW-3(b)'s residual transport
ι(R_{κ₂}) = ι(r̃^{μ₂}) is computed against side-COHERENT normalizers
(powers n̂(u₂)^m), whose ϖ-discrepancy is exactly geometric
(η^{−mQ}, since Q(mu₂) = mQ(u₂) + ⌊mi(u₂)/e₁⌋ telescopes the wrap into
the power) — re-derived: η^{−Qf₂μ₂}·ψ₂(η^QZ)^{μ₂} = r̃^{μ₂}, so the
wrap CANNOT bite the side-residual row, only the per-height key
display — which is what [r1] corrected. HETOW.A(i) reads at the
corrected key ✓; the μ₂ = 3 exclusion, n_min = 12, menus, termination
rows are label-level and wrap-free (PE1's clean charges re-confirmed
where re-derived).

## ATTACK 2 — HETOW-2's F-2 tail accounting as landed (core HELD; one exemplar/corner slip → finding F-A)

Re-derived: reduction step x^{D′+r′} = x^{r′}(Φ′ − tail) with dv(tail)
= D′h exact (constant-term pin); moved piece raises slot value by
EXACTLY u₂ − e₂D′h ≥ 1 with x-degree r′ ≤ e₁−2 < D′ (inert);
stationary piece stays at value ≥ (= at tail's attaining part), r′
drops per iteration; value-T₂ material only at slots e₂t exact-height;
exact-height residue preserved pointwise via the Ô[x] identity + the
moved summand's strictly larger value; above-height and moved material
prices at ≥ T₂ + min(e₂, u₂ − e₂D′h). All checks out; the machine leg
verifies the identity at r′ = e₁−2 = 1 MAXIMAL on frame R (G5) and the
slot exactness ties (G6). The residue-unchanged mechanism is sound.

The slip (F-A below): the paragraph's illustrative object and its
"either way" closure overreach at one corner — see FINDINGS.

## ATTACK 3 — the GENHN dated erratum's scope claim (HELD, with machine spot-verification at fresh wrap frames)

The erratum's corrected display (`GENHN_PROOF` dated append,
ĉ_t := lift(c_t·η^{W(t)}), per digit at f₁ ≥ 2 the (LIFT) output)
matches HETOW [r1]'s key exactly ✓. "Proof mechanism unaffected"
spot-verified against T(b)′'s displayed proof:
* (i)'s side-residual step: computed through S4's coherent normalizers
  = powers of n̂(u₂); res(corrected coefficient / n̂(u₂)^{f₂−t}) =
  c_t·η^{W(t)}·η^{−W(t)} = c_t — the wrap absorbs and the side residual
  is exactly ψ₂; the letter clause ψ₂(η₂(ξ)) = 0 follows ✓ (and is
  equivalent to HETOW-1's r̃(β_ξ) = 0 via β = η^{−Q}η₂).
* the polygon/clearance computation (L1216–1226): uses only monomial
  HEIGHTS (u₂(f₂−t) = e₁a + ih), which the η^{W(t)}-correction does not
  move — unit-blind as claimed ✓.
* (ii) slot lemma and (iii) trichotomy at a wrap-corrected frame from
  the display side: machine legs G6 (exactness ties) and G3 (the μ₂ = 2
  composed trichotomy menu at frame V) — see fresh route.
* GENHN's own committed tower contact: `genhnr2_supp.py` frames at
  q = 2 (η = 1 forcibly) — checked; the erratum's claim that committed
  artifacts are untouched is correct (byte-frozen files verified below).

## ATTACK 4 — the gauge-axis box + battery-blindness disclosure (HELD; one omission → finding F-C)

HETOW-BOX-3 [r1] now names the η = 1 gauge of both battery frames —
verified against the sealed runner (`hetow_checks.py` docstring: frames
Φ′ = x² − p, "eta = 1 ... INVISIBLE at this frame"); the positive
coverage sentence pins the η ≠ 1 contact to "three frames, f₂ = 2 with
f₁ = 1" ✓; the withdrawn "uniform in all of these" line is recorded as
withdrawn ✓; §S6 P2 carries the [r1] gauge caveat ✓; the NOT-exercised
list names η ≠ 1 × {f₁ ≥ 2, e₂ ≥ 2} ✓. Omission: the f₂ ≥ 3 multi-wrap
axis (F-C below).

---

## FINDINGS

### F-A — MINOR — HETOW-2's F-2 robustness paragraph: the exemplar breaks its own residue premise at f₁ ≥ 2, and the "either way" closure overreaches at the (e₂ = 1, t = f₂−1) corner

**Quote (§S2, LEMMA HETOW-2 proof):** "If a slot coefficient is instead
presented with x-degree ≥ D′ (e.g. a plain product ĉ_t·n̂ of a
degree-≤ D′−1 lift by the x-monomial, x-degree up to D′ + e₁ − 2),
reduce mod Φ′. … slot e₂t's exact-height residue after reduction equals
the unreduced coefficient's, = r̃'s t-coefficient (HETOW-1(c)) … Either
way LEMMA HE7-12 [r2, r3] applies."

**Two defects, neither consumed in-repo.** (i) At f₁ ≥ 2 a degree-< D′
polynomial times n̂(k) has exact-height-k part spanning only ONE
η-digit (heights of the other digits differ by e₁h-multiples), so a
"plain lift" of a K-letter c_t ∉ F_Q does not carry residue c_t at all
— the paragraph's premise "the unreduced coefficient's [residue] =
r̃'s t-coefficient" restricts its scope to presentations of the
CORRECTED key with above-height junk, and the "e.g." object (echoing
GENHN's retired display) is outside that scope. (ii) at e₂ = 1,
t = f₂−1 with coefficient x-degree ≥ D′, the moved piece x^{r′}π^{·}Φ′
lands at slot e₂t + 1 = e₂f₂ — THE LEADING SLOT — so w acquires an
x-degree-≥ D″ term, violating LEMMA HE7-12's hypothesis "deg w < D″"
(HE7_PROOF §S5.8, quoted: "w ∈ O[x], w ≠ 0, with deg w < D″"), and the
presented polynomial is not monic of degree D″. **Failure scenario:**
a later unit at f₁ ≥ 2, e₂ = 1 cites this paragraph to feed a
plain-product-presented key into HE7-12; the lemma's hypotheses fail
and the §S5 package does not transport. **Why MINOR:** LEMMA HETOW-2's
STATEMENT pins Φ₂ to the wrap-corrected (LIFT) display, for which the
F-4 paragraph proves w = 0 — the F-2 paragraph is declared
representation-independence robustness, and both in-repo consumers
(HETOW.A(i); the GENHN erratum's corrected display) pin the (LIFT)
form. No traced consumer reaches the corner.

### F-B — MINOR — the preamble's "W(t) is non-linear in t, so no K₂^×-rescale absorbs it" is false at f₂ = 2, where every r1 machine frame sits; the true mechanism there is the W(f₂−1) = 0 pin — and the seam can be σ-BLIND (fresh frame V)

**Quote (§S2 preamble):** "W(t) is non-linear in t, so no K₂^×-rescale
absorbs it."

**The defect.** On t ∈ {0, 1} (f₂ = 2 — frames X, Z, W, i.e. every
machine contact the note cites) any function is affine, so the quoted
reason is empty there; non-absorbability at those frames follows
instead from W(f₂−1) = ⌊i(u₂)/e₁⌋ = 0 pinned against the monic
normalization (a rescale λ^{−f₂}r̃(λZ) needs η^{−W(t)} = λ^{t−f₂};
t = f₂−1 with c_{f₂−1} ≠ 0 forces λ = 1). When c_{f₂−1} = 0 an affine
wrap CAN be a rescale (e.g. ψ₂ = Z² − c₀ with η a square), keeping the
naive slot polynomial irreducible. **Verified consequence (fresh frame
V, f₂ = 3):** the naive slot polynomial can be irreducible even
non-absorbably — PARI σ(naive) = {(2,3)} = the carrier σ on both
oracle routes, while ψ₂(η₂(ξ)) ≠ 0 at the naive key's roots (nfmodpr):
the wrap seam exists with NO σ-visible symptom; only the letter clause
detects it. **Failure scenario:** a regression tooth built as
"σ(naive) ≠ σ(corrected)" (the shape the r1 record's 3/3 teeth
suggest) is ported to a frame like V and passes on the broken key.
**Why MINOR:** the note's teeth and records are all frame-derived (no
false record sentence); the sentence is a justification whose
conclusion holds at every checked wrap-live frame by the one-line
W(f₂−1) = 0 argument; at f₂ ≥ 3 the stated mechanism is real
(W = (1,1,0) at frame V is genuinely non-affine).

### F-C — MINOR — HETOW-BOX-3 [r1]'s NOT-exercised list omits the f₂ ≥ 3 multi-wrap axis

The box's positive sentence pins the η ≠ 1 contact to "three frames,
f₂ = 2 with f₁ = 1", but the NOT-exercised list (μ₂ ≥ 4, e₂f₂ ≥ 4,
f₁ ≥ 2, η ≠ 1 × {f₁ ≥ 2, e₂ ≥ 2}, organic refines) does not name
f₂ ≥ 3 — the regime where the wrap correction first uses TWO live
η^{W(t)} units and W is genuinely non-affine, i.e. the untested part
of the [r1] mechanism itself. **Failure scenario:** an acceptance
reader auditing the list axis-by-axis concludes the corrected
prescription's t-dependence has machine support, when every contacted
frame used a single wrap unit. Substantively mooted by this pass
(frame V, f₂ = 3, GREEN incl. the forced {(6,3)} μ₂ = 3 row), so the
residue is disclosure-completeness only. MINOR.

---

## MACHINE LEG (pins, isolated re-run, tautology audit)

* **Pins exact.** `hetowr1_supp.py` md5 dcb8452f… byte-identical at
  seal commit d0d3ca6 and HEAD; artifacts md5 b52eb226…/58f1ce0c… as
  recorded in §S7 and the 5335ae3 commit message.
* **Isolated re-run** (`/tmp/hetow_pe2_iso`, runner staged from
  d0d3ca6, fresh dir): **GREEN, 29 gp jobs + 15 exact checks, 0
  violations, dual routes 29/29** — output content-identical to the
  committed artifact modulo the timing line (21.4s vs 21.3s; a genuine
  re-execution), results JSON byte-identical (md5 58f1ce0c…).
* **PE1-era freeze.** `hetow_checks.py` md5 31935fe8… (= PE1 report's
  pin); battery artifacts and `hetow_pe1_fresh.py` + artifacts
  byte-unchanged from 3e19eba to HEAD (git diff empty).
* **Tautology audit of the supp runner.** Zero reader imports
  (verified by reading all 302 lines); the E-legs' two sides come from
  different algebraic routes inside the runner (integer-polynomial slot
  residues vs F_{p²} minpoly search) and I re-derived all six key
  polynomials and all three minpoly/naive-poly pairs BY HAND — exact
  match; the G-legs are adjudicated by the external gp binary on two
  routes per job. The G3/G4 member pin arithmetic (slopes 20/3, 7.5/7
  hull, 31/3, 23/2/11 hull) re-derived by hand — the preregistered
  forced shapes are the correct consequences of HE7.A(2) at those pins.
  Non-tautological.

## FRESH ROUTE (instruments sealed at 7151fd8; artifacts committed with this report)

`hetow_pe2_fresh.py` (dual PARI routes on every σ job; md5 6600588f…,
output c568444d…, results d9e0e835…) + `hetow_pe2_freshT.py`
(construction oracle; d2344a65…/4568a280…/55fd8137…). Frames disjoint
from the sealed battery (η = 1), PE1's X/Y, r1's Z/W.

* **FRAME V (p = 7, f₂ = 3, ord(η) = 6)** — the first multi-wrap
  contact anywhere (W = (1,1,0), two live wrap units, genuinely
  non-affine): corrected key σ = {(2,3)} both routes; slot residues =
  minpoly(β) = Z³+5Z²+4Z+5 exactly; BOTH W-telescoping identities
  (heights 6 and 9) exact. **The σ-blind seam:** naive key σ = {(2,3)}
  TOO (preregistered), while nfmodpr shows ψ₂(η₂(ξ)) ≠ 0 and the
  η₂-form naive polynomial Z³+Z²+5Z+3 vanishing at its roots — the
  letter tooth fires where no σ tooth exists. μ₂ = 2 trichotomy from
  GENHN-T(b)′(iii)'s display side: RAM {(4,3)} 2/2 forced, 2SIDED
  {(2,3),(2,3)} 2/2 forced, INERT-family 4/4 in the 3-menu (both
  {(2,6)} and split realized); μ₂ = 3 3RAM {(6,3)} forced — the first
  f₂ = 3 tower members anywhere.
* **FRAME U (p = 11, ord(η) = 5)** — corrected {(2,2)}, residues =
  minpoly(β) = Z²+4Z+9; naive tooth {(2,1),(2,1)} as derived.
* **FRAME S (p = 3, e₂ = 2, u₂ = 5)** — the first η ≠ 1 × e₂ ≥ 2
  contact (a BOX-3 unexercised axis), twist-trivial (η^Q = 1) but
  wrap-live — isolating the wrap from the β-twist: corrected {(4,2)},
  residues = ψ₂ exactly as the trivial-twist minpoly predicts; naive
  slot poly (Z+2)², naive σ = {(8,1)} ≠ {(4,2)} (INFO shape). First
  e₂f₂ = 4 members: μ₂ = 2 RAM {(8,2)} forced (dv₂ = 41 via the
  b-odd Φ′-monomial), integer-λ₂ menu 2/2 ({(4,4)}).
* **FRAME R (p = 5, f₁ = 2, e₁ = 3, ord(η) = 8, Φ′ = x⁶ − 50)** —
  the first η ≠ 1 × f₁ ≥ 2 contact and the first two-digit (LIFT)
  (L₁₆(3+4ω) = 9375x + 2500x⁴, both monomials exact-height 16):
  corrected {(3,4)} both routes; F₂₅-exact slot residues = minpoly(β)
  = Z²+3Z+(4+4ω); naive tooth {(3,2),(3,2)} exactly as derived from
  the split of Z²+3Z+(4+2ω); letters [1,0,1]/[0,1,1] (ψ₂ vanishes at
  the corrected key's roots, the η₂-form naive poly at the naive's).
  **F-2 leg at r′ = e₁−2 = 1 MAXIMAL:** v_pr(x₀) = 1, v_pr(Φ′(x₀)) =
  8, v_pr(x₀⁷) = 7, v_pr(x₀⁷ − 50x₀) = 9 — the overflow monomial and
  the stationary piece 50x share the height-7 residue with the moved
  piece strictly above, the exact Ô[x]-identity mechanics of the [r1]
  accounting. **GENHN-2′ ties:** digit-tie and letter-tie sums at
  dv₂ = 16 exact 4/4 — the slot lemma's independence clause at a wrap
  frame.
* **FRAME T (q = 4, F₄[[t]], e₁ = 3, η = g of order 3)** — the first
  non-prime-q wrap contact: exact-F₄ slot residues = r̃ = Z²+g²Z+g²
  = minpoly(g²η₂); naive N = (Z+1)(Z+g) split. Construction oracle
  (Hensel bound v > 30 ≫ 2v(dK/dt) = 10 + Frobenius prefix-fixing):
  corrected key — exactly 2 constrained branches, w₂ = g·η₂ for the
  two ψ₂-roots, BOTH outside F₄ ⟹ f = 2, e = 3, irreducible {(3,2)};
  naive key — 2 branches with every coefficient in F₄ ⟹ REDUCIBLE
  (an f = 1 cubic factor certified); the letter clause read off the
  SOLVED branches, not imposed.
* **Instrument errata (disclosed in the runners' docstrings, same
  class as PE1's disclosed minpoly-of-β slip):** the sealed prereg
  transcribed the naive key's letter polynomial in the β-variable at
  three sub-checks where the jobs compute the η₂-letter (η₂ = η^Q β);
  first run: all 20 σ jobs, corrected-key letters, valuations, ties
  GREEN, the ψ₂-seam entries GREEN, only those three value slots
  missed; corrected η₂-forms derived by hand (V: Z³+Z²+5Z+3 =
  η^{3Q}r̂(η^{−Q}Z); R: const 1+3ω; T: w₂ ∈ g·roots(Z²+Z+1)) and the
  re-run is the committed artifact. Frame T's raw branch count also
  carried a free 16² tail (the last two coefficients' constraints sit
  past the solve window) — scored on the constrained prefix. Neither
  defect touches a note-derived prediction.
* **Verdict of the leg: GREEN — 20 dual-route σ jobs (routes agreeing
  20/20), 4 letter jobs, 10 exact valuations, 21 exact residue/branch
  checks, 0 violations on the committed run.**

## CLEAN CHARGES (attacked and held)

1. The wrap cocycle, the telescoped W(t), the (LIFT) residue formula,
   and HETOW-1(a)(b)(c) as restated — re-derived independently and
   machine-confirmed at 5 fresh frames (attack 1).
2. The sole-definition restatement — no traced downstream clause
   consumes the old slot-residue definition (S1 rows, HETOW-3, §S3
   menus, §S5–S7 records all checked; HETOW-3(b)'s side-residual
   transport shown wrap-immune because side-coherent normalizers are
   powers of one monomial, discrepancy geometric η^{−mQ}).
3. HETOW-2's F-4 pinned (LIFT) form: no overflow at any f₁ (degree
   bound i(k) + e₁(f₁−1) ≤ D′−1 re-derived; frame R realizes the
   two-digit case, degrees 1 and 4 < 6) — w = 0 branch sound.
4. The F-2 accounting core: value monotone, exact raise u₂ − e₂D′h,
   T₂-material exact-height at slots e₂t only, residue-unchanged via
   the Ô[x] identity (machine-exact at frame R, r′ maximal).
5. The GENHN erratum's scope sentence: S4-coherent-normalizer residual
   re-derived at the corrected key (wrap absorbs, side residual = ψ₂);
   polygon/clearance step height-only; T(b)′(iii)'s trichotomy
   machine-realized at a wrap frame (frame V, all three σ-blocks);
   committed genhnr2/battery artifacts byte-frozen as claimed.
6. HETOW-BOX-3 [r1]'s positive-coverage sentences match the artifacts
   (battery η = 1 verified in the sealed runner's docstring; supp =
   three f₂ = 2, f₁ = 1 frames); the withdrawn uniformity sentence is
   genuinely withdrawn; §S6 P2 carries the gauge caveat.
7. §S7's supp record: census 29 = 6 + 16 + 7 re-added; 15 exact
   checks; keys/r̃/naive-polys for frames X/Z/W re-derived by hand;
   G3/G4 pin arithmetic (hulls 20/3, 15/2+7, 31/3, 23/2+11)
   re-derived — forced-row predictions correct consequences.

## GRADE LINE

**CLEAN (0C / 0G / 3m).** F-A (F-2 robustness paragraph: exemplar
outside its own residue premise at f₁ ≥ 2; "either way HE7-12 applies"
overreaches at the e₂ = 1 leading-slot corner where deg w < D″ fails —
no in-repo consumer), F-B ("non-linear in t" justification false at
f₂ = 2; σ-blind seam face surfaced at frame V — letter clause is the
sound formulation and it is what the note proves), F-C (BOX-3
NOT-exercised list omits f₂ ≥ 3 — mooted in substance by this pass).
The machine leg is intact (pins exact; isolated supp re-run GREEN
29/0 content-identical mod timing; PE1-era artifacts byte-frozen).
Per the arc: the tower σ-closure counter moves **0/2 → 1/2**; one
further CLEAN pass on a fresh surface is required for acceptance.
Repair-round suggestions for the MINORs (fix nothing here): scope the
F-2 paragraph to junk-augmented presentations of the corrected key
and drop the plain-product exemplar; replace "non-linear in t" with
the W(f₂−1) = 0 monic-pin argument and record the σ-blind face; add
f₂ ≥ 3 to BOX-3 (now with frame V's coverage on record).
