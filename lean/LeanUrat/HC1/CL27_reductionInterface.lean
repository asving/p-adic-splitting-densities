/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL27_reductionInterface — the ℤ_[p][x] → 𝔽_p[x] reduction interface (BP5 CL-27)

**Unit CL-27** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4, NEW at
REVISION 2, findings 4 + 5; risk R-2): the named vocabulary between `ℤ_[p][x]` and
CL-11's `𝔽_p[x]` positional-uniqueness statement, consumed by CL-12 (NCL).

**Deliverables.**
* (a) DE-PRIVATIZED COPIES — all PROVED but `private` at HEAD; the prover COPIES the
  proofs, never re-derives: `digLift_ne` (ScratchC6:244), `digLift_spec`
  (C2_TYPa:144), `digLift_deg` (C2_TYPa:187 — `inC` IS the degree bound,
  Moves/Defs.lean:67), `gaussVal_digLift_zero` (the ScratchC6:327 step: `wPrev = 0`
  + the base pin `T.base.1.1`), `mono_ne` (ScratchC6:307), `t4_slotBound_mul`
  (T4_slotMinHt.lean:255 — the EXACT key-degree ratio law; `slotBound` is
  ℕ-DIVISION-defined at DefsTower.lean:153, so exactness is a real lemma resting on
  `t4_deg_dvd_step`, not `rfl`).
* (b) THE MOD-p TRANSPORT `red := Polynomial.map PadicInt.toZMod`: `red_monic_deg`
  (Mathlib `Polynomial.Monic.map` + monic degree preservation), `red_ratio_law`
  ((a) + monicity), `red_p_pow_zero` (`red (C (p^k)) = 0` for `1 ≤ k`),
  `red_digLift_ne` (from `gaussVal_digLift_zero`: gaussVal = the min coefficient
  valuation, Moves/L1_gaussVal.lean:31, so SOME coefficient is a unit and survives
  `PadicInt.toZMod`), `red_digLift_deg` (digLift_deg + map-degree-≤ + monic full
  degree; **R-2 on record: the reduced digit degree may DROP — CL-11 is stated to
  tolerate `deg d̄ < deg Φ̄₀` with NO lower bound, and this interface must NOT
  strengthen it**).
* (c) THE FACTOR-OUT KIT (REVISION-2 route: no division operator, no quotient ring
  beyond mod p): `slotCoeff_factor` (finsum-to-Finset.sum normalization on the
  finite support, then `Σ_c digLift(y c)·C(p^{l c})·∏Φ^{s c} =
  C(p^{l_min})·Σ_c digLift(y c)·C(p^{l c − l_min})·∏Φ^{s c}`), `C_p_pow_ne`
  (+ IsDomain cancellation in `ℤ_[p][x]` = Mathlib `mul_ne_zero_iff`, no new lemma).
* (d) SURVIVOR DISTINCTNESS: `coord_eq_of_ht_l_eq` — block-mates with equal height
  and equal p-level have equal slot vectors, hence are equal. EXTRACTED from T9(b)'s
  numeric kernel (`mr_inj_top` + the ht-to-baseIdx step, private at HEAD); T9's
  public `(baseIdx, l)`-injectivity alone is NOT sufficient — the
  equal-ht-to-equal-baseIdx step lives inside the kernel. SPLIT RULE: if (d) exceeds
  ~40 proof lines the prover spins it off as CL-27a.

**E-phase resolutions recorded.**
* "each a named public lemma in the NCL file" is resolved to THIS unit's own file
  (CL-27 has no deps and runs parallel with CL-10; CL-12 imports it) — the "NCL
  file" reading that would place them in CL-12's file contradicts the blueprint's
  own dependency spine (CL-27 → CL-12).
* `slotCoeff_factor` is stated with the exact hypotheses the identity consumes:
  finite support, block-b support (`∀ c, y c ≠ 0 → blk c = b` — implied by the NCL
  site's level-set support), and `l_min ≤ l` on the support (ℕ-subtraction
  exactness); the sum is over `hfin.toFinset` (T4's own normalization shape).
  Attainment of `l_min` is NOT needed for the factoring identity — it enters only
  at CL-12 (survivor nonemptiness).
* `red_digLift_ne` is stated on `digLift` directly (the form CL-12 consumes) with
  the gaussVal mechanism recorded here rather than as a hypothesis.
* Degree forms: `natDegree` for the monic ratio laws (matching `t4_slotBound_mul`),
  `degree` (WithBot) for the digit bounds (matching `digLift_deg`, and correct junk
  behavior at `digLift 0 = 0`).

**Deps.** none (parallel with CL-10; consumed by CL-12; independent of CL-11).
difficulty: routine-opus (copies + Mathlib plumbing; (d) is the one extraction with
content). Size: ~110. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## (a) De-privatized copies (all PROVED at HEAD inside their owner files) -/

/-- CL-27(a): nonzero digits have nonzero lifts (copy of ScratchC6's private
`digLift_ne`; via the base `hS6a` coset realizer). -/
theorem digLift_ne (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    T.digLift y ≠ 0 := by
  sorry

/-- CL-27(a): the digit lift is a genuine base realizer — nonzero, a coefficient
(`inC Φ₀`), parent weight 0, residue `C(digit)·T⁰` (copy of C2_TYPa's private
`digLift_spec`). -/
theorem digLift_spec (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    T.digLift y ≠ 0 ∧ inC (T.stg 0).Φ (T.digLift y) ∧ (T.stg 0).wPrev (T.digLift y) = 0 ∧
      (T.stg 0).R (T.digLift y)
        = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) *
            LaurentPolynomial.T 0 := by
  sorry

/-- CL-27(a): the digit-lift degree bound `deg (digLift y) < deg Φ₀` (copy of
C2_TYPa's private `digLift_deg`; `inC` IS the degree bound, junk-true at `y = 0`). -/
theorem digLift_deg (T : Tower p F) (y : ↥(T.stg 0).FQ) :
    (T.digLift y).degree < (T.stg 0).Φ.degree := by
  sorry

/-- CL-27(a): the digit lift has Gauss valuation 0 — `wPrev = 0` read through the
base pin `T.base.1.1` (the ScratchC6:327 step, named). Some coefficient of
`digLift y` is therefore a `ℤ_[p]`-unit. -/
theorem gaussVal_digLift_zero (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    gaussVal (T.digLift y) = 0 := by
  sorry

/-- CL-27(a): basis monomials never vanish (copy of ScratchC6's private `mono_ne`;
`C(p^l)·∏Φ^s` with `p ≠ 0` and monic keys). -/
theorem mono_ne (T : Tower p F) (c : T.Coord) : T.mono c ≠ 0 := by
  sorry

/-- CL-27(a): the slot bound is EXACT — `slotBound r · deg Φ_r = deg Φ_{r+1}` (copy
of T4_slotMinHt's private `t4_slotBound_mul`; rests on the per-move degree
divisibility `t4_deg_dvd_step`, since `slotBound` is ℕ-division-defined). -/
theorem t4_slotBound_mul (T : Tower p F) (r : Fin T.K) :
    T.slotBound r * (T.stg r.castSucc).Φ.natDegree = (T.stg r.succ).Φ.natDegree := by
  sorry

/-! ## (b) The mod-p transport -/

/-- CL-27(b): the coefficientwise mod-p reduction `ℤ_[p][x] → 𝔽_p[x]` — Mathlib's
`Polynomial.map` along `PadicInt.toZMod` (a ring hom, so it transports sums and
products; the whole REVISION-2 route needs no other quotient). -/
noncomputable def red (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] → Polynomial (ZMod p) :=
  Polynomial.map (PadicInt.toZMod)

/-- CL-27(b): reduction preserves monicity and (for monic inputs) the exact degree. -/
theorem red_monic_deg (Φ : Polynomial ℤ_[p]) (hΦ : Φ.Monic) :
    (red p Φ).Monic ∧ (red p Φ).natDegree = Φ.natDegree := by
  sorry

/-- CL-27(b): the exact key-degree ratio law survives reduction —
`deg (red Φ_{r+1}) = slotBound r · deg (red Φ_r)` (from `t4_slotBound_mul` +
`red_monic_deg`). This is CL-11's ratio hypothesis at `K₀ = 𝔽_p`. -/
theorem red_ratio_law (T : Tower p F) (r : Fin T.K) :
    (red p (T.stg r.succ).Φ).natDegree
      = T.slotBound r * (red p (T.stg r.castSucc).Φ).natDegree := by
  sorry

/-- CL-27(b): positive p-powers die under reduction — `red (C (p^k)) = 0` for
`1 ≤ k` (this is what kills the `l > l_min` terms in CL-12). -/
theorem red_p_pow_zero (k : ℕ) (hk : 1 ≤ k) :
    red p (Polynomial.C ((p : ℤ_[p]) ^ k)) = 0 := by
  sorry

/-- CL-27(b): reduced digit lifts are nonzero — `gaussVal (digLift y) = 0`
(`gaussVal_digLift_zero`) means SOME coefficient is a `ℤ_[p]`-unit, which survives
`PadicInt.toZMod`. This is CL-11's nonzero-digit hypothesis at `K₀ = 𝔽_p`. -/
theorem red_digLift_ne (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    red p (T.digLift y) ≠ 0 := by
  sorry

/-- CL-27(b): the reduced digit-degree bound `deg (red (digLift y)) < deg (red Φ₀)`
(digLift_deg + map-degree-≤ + monic full degree on the right). **R-2**: the LEFT
degree may genuinely DROP below `deg (digLift y)`; CL-11 tolerates any drop and this
statement must never be strengthened to degree preservation. -/
theorem red_digLift_deg (T : Tower p F) (y : ↥(T.stg 0).FQ) :
    (red p (T.digLift y)).degree < (red p (T.stg 0).Φ).degree := by
  sorry

/-! ## (c) The factor-out kit (no division operator, no `ZMod (p^{l+1})`) -/

/-- CL-27(c): `C (p^k) ≠ 0` in `ℤ_[p][x]` — the cancellation partner for the
IsDomain step (`mul_ne_zero_iff`) of CL-12. -/
theorem C_p_pow_ne (k : ℕ) :
    (Polynomial.C ((p : ℤ_[p]) ^ k) : Polynomial ℤ_[p]) ≠ 0 := by
  sorry

/-- CL-27(c): the factor-out identity. For a finitely supported block-`b` digit
assignment whose p-levels all sit at or above `lmin`, the slot coefficient
normalizes from its finsum to the Finset sum and factors as
`C(p^{lmin}) · Σ_c digLift(y c)·C(p^{l c − lmin})·∏_r Φ_r^{slot c r}`
(ℕ-subtraction exact under `hlmin`). Attainment of `lmin` is NOT hypothesized —
it enters only at the CL-12 application (survivor nonemptiness). -/
theorem slotCoeff_factor (T : Tower p F) (b : ℕ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hfin : (Function.support y).Finite)
    (hblk : ∀ c : T.Coord, y c ≠ 0 → T.blk c = b)
    (lmin : ℕ) (hlmin : ∀ c : T.Coord, y c ≠ 0 → lmin ≤ c.l) :
    T.slotCoeff b y
      = Polynomial.C ((p : ℤ_[p]) ^ lmin) *
          ∑ c ∈ hfin.toFinset,
            T.digLift (y c) *
              (Polynomial.C ((p : ℤ_[p]) ^ (c.l - lmin)) * ∏ r, (T.stg r).Φ ^ c.slot r) := by
  sorry

/-! ## (d) Survivor distinctness -/

/-- CL-27(d): block-mates with equal height and equal p-level are EQUAL — the
extraction of T9(b)'s numeric kernel (equal ht + equal l ⇒ equal baseIdx via the
κ-arithmetic, then `mr_inj_top` pins the slot vectors; T9's public
`(baseIdx, l)`-injectivity alone does not carry the ht-to-baseIdx step). Gives
CL-12's survivor DISTINCTNESS: distinct level-set coordinates at the same `l` have
distinct slot vectors. -/
theorem coord_eq_of_ht_l_eq (T : Tower p F) {c c' : T.Coord}
    (hblk : T.blk c = T.blk c') (hht : T.ht c = T.ht c') (hl : c.l = c'.l) :
    c = c' := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.slotCoeff_factor
#print axioms LeanUrat.HC1.coord_eq_of_ht_l_eq
