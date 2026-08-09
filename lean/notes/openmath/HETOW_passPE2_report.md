# HETOW passPE2 — hostile verification report (fresh context)

**VERDICT: PENDING (fresh-route battery running; verdict line finalized
at the artifacts commit — this skeleton committed per survival
discipline).**

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

(filled at the artifacts commit)

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

(verdict filled at the artifacts commit)

## GRADE LINE

(filled at the artifacts commit)
