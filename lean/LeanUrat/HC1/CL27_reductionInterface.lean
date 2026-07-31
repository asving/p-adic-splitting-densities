/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_liftWeight

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

**PROVER NOTES (as-built, 2026-07-30).**
* Two proof-time imports added (`Moves.L3_liftMonic`, `Moves.L3_liftWeight`) — the
  CL-13 E-phase precedent ("statement needs only DefsCar; the prover adds
  proof-time imports").
* (d) exceeded the ~40-line split budget, but a separate CL-27a FILE would be a new
  statement outside the fence; instead the kernel is decomposed into named PRIVATE
  helpers in-file (`cl27_mr_*` = T9(b)'s numeric kernel copied; `cl27_ND` = the
  ℕ-valued lattice heights `strTop·κ_r`; `cl27_ND_step` = the mixed-radix step law,
  increment case from IAug + `L3_liftWeight`, recentering case from the ultrametric)
  — recorded here in lieu of the spin-off.
* The step law `slotBound r · ND r ≤ ND (r+1)` is the ONE new mathematical content:
  at an increment it is `e·g·h·e′ < h′`, i.e. (I-aug) `h′ > e′·w(Φ̂)` read through
  `w(Φ̂) = e·h·g` (L3_liftWeight); at a recentering it is `h ≤ h′` from
  `w′(Φ−t) ≥ min(w Φ, w t) = h` (the ultrametric + `w(t) = w(Φ)`).

**Deps.** none (parallel with CL-10; consumed by CL-12; independent of CL-11).
difficulty: routine-opus (copies + Mathlib plumbing; (d) is the one extraction with
content). Size: ~110. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Private helpers for (a): the digit-lift spec (C2_TYPa's private toolkit, copied) -/

/-- Constants are coefficients at every stage key (C2_TYPa's private `degC_lt'`). -/
private lemma cl27_degC_lt (σ : Stage p F) (c : ℤ_[p]) : (Polynomial.C c).degree < σ.Φ.degree := by
  have h1 : (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
  have h2 : (0 : WithBot ℕ) < σ.Φ.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by have := σ.hdeg; omega)
  exact lt_of_le_of_lt h1 h2

/-- `gaussVal 1 = 0` (ScratchC6's private `gaussVal_one`, copied). -/
private lemma cl27_gaussVal_one : gaussVal (1 : Polynomial ℤ_[p]) = 0 := by
  have h10 : (1 : ℤ_[p]) ≠ 0 := one_ne_zero
  have hsupp : (1 : Polynomial ℤ_[p]).support = {0} := by
    rw [← Polynomial.C_1, Polynomial.support_C h10]
  unfold gaussVal
  have hne : (1 : Polynomial ℤ_[p]).support.Nonempty :=
    ⟨0, by rw [hsupp]; exact Finset.mem_singleton_self 0⟩
  rw [dif_pos hne]
  have hval : ((1 : Polynomial ℤ_[p]).support).inf' hne
        (fun i => (((1 : Polynomial ℤ_[p]).coeff i).valuation : ℤ))
      = (((1 : Polynomial ℤ_[p]).coeff 0).valuation : ℤ) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (by rw [hsupp]; exact Finset.mem_singleton_self 0)
    · apply Finset.le_inf'
      intro b hb
      rw [hsupp, Finset.mem_singleton] at hb
      rw [hb]
  rw [hval, Polynomial.coeff_one_zero, PadicInt.valuation_one]
  norm_num

/-- `digLift 0 = 0` (C2_TYPa's private `digLift_zero`, copied). -/
private lemma cl27_digLift_zero (T : Tower p F) : T.digLift 0 = 0 := by
  rw [Tower.digLift, dif_neg]
  rintro ⟨B, hB0, -, -, hR⟩
  apply (T.stg 0).hRne B hB0
  rw [hR]
  have h0 : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := Subtype.ext (by simp)
  rw [h0, map_zero, zero_mul]

/-- The full digit-lift spec at nonzero digits (C2_TYPa's private `digLift_spec`,
copied; both public forms below read off it). -/
private lemma cl27_digLift_spec (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    T.digLift y ≠ 0 ∧ inC (T.stg 0).Φ (T.digLift y) ∧ (T.stg 0).wPrev (T.digLift y) = 0 ∧
      (T.stg 0).R (T.digLift y)
        = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) *
            LaurentPolynomial.T 0 := by
  have hex : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg 0).Φ B ∧ (T.stg 0).wPrev B = 0 ∧
      (T.stg 0).R B = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) *
        LaurentPolynomial.T 0 := by
    -- 0 ∈ weightSet via the coefficient 1
    have h1ne : (1 : Polynomial ℤ_[p]) ≠ 0 := one_ne_zero
    have h1C : inC (T.stg 0).Φ (1 : Polynomial ℤ_[p]) := by
      show (1 : Polynomial ℤ_[p]).degree < _
      rw [← Polynomial.C_1]
      exact cl27_degC_lt (T.stg 0) 1
    have h0mem : (0 : ℤ) ∈ (T.stg 0).weightSet := by
      have hmem := (T.stg 0).hWS 1 h1ne h1C
      rwa [T.base.1.1 1 h1ne, cl27_gaussVal_one] at hmem
    -- the digit as a unit of the current residue field
    have hyF : (y : F) ≠ 0 := by
      intro h
      exact hy (Subtype.ext h)
    have hkne : (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) ≠ 0 := by
      intro h
      exact hyF (congrArg Subtype.val h)
    -- V5 coset form: at the base stage K = FQ, so the coset base b is absorbed by c := y·b⁻¹
    obtain ⟨b, hb⟩ := (T.stg 0).hS6a 0 h0mem
    have hKFQ : (T.stg 0).K = (T.stg 0).FQ := T.base.1.2.2
    set cy : (↥(T.stg 0).K)ˣ :=
      Units.mk0 (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) hkne with hcy
    have hbinv : (((cy * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F) ∈ (T.stg 0).FQ :=
      (le_of_eq hKFQ) ((cy * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K).2
    obtain ⟨B, hB0, hBC, hBw, hBR⟩ := hb (cy * b⁻¹) hbinv
    rw [inv_mul_cancel_right, hcy] at hBR
    refine ⟨B, hB0, hBC, hBw, ?_⟩
    simpa using hBR
  rw [Tower.digLift, dif_pos hex]
  exact hex.choose_spec

/-! ## (a) De-privatized copies (all PROVED at HEAD inside their owner files) -/

/-- CL-27(a): nonzero digits have nonzero lifts (copy of ScratchC6's private
`digLift_ne`; via the base `hS6a` coset realizer). -/
theorem digLift_ne (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    T.digLift y ≠ 0 :=
  (cl27_digLift_spec T y hy).1

/-- CL-27(a): the digit lift is a genuine base realizer — nonzero, a coefficient
(`inC Φ₀`), parent weight 0, residue `C(digit)·T⁰` (copy of C2_TYPa's private
`digLift_spec`). -/
theorem digLift_spec (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    T.digLift y ≠ 0 ∧ inC (T.stg 0).Φ (T.digLift y) ∧ (T.stg 0).wPrev (T.digLift y) = 0 ∧
      (T.stg 0).R (T.digLift y)
        = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) *
            LaurentPolynomial.T 0 :=
  cl27_digLift_spec T y hy

/-- CL-27(a): the digit-lift degree bound `deg (digLift y) < deg Φ₀` (copy of
C2_TYPa's private `digLift_deg`; `inC` IS the degree bound, junk-true at `y = 0`). -/
theorem digLift_deg (T : Tower p F) (y : ↥(T.stg 0).FQ) :
    (T.digLift y).degree < (T.stg 0).Φ.degree := by
  by_cases hy : y = 0
  · rw [hy, cl27_digLift_zero T, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr
      (fun h => (T.stg 0).hmonic.ne_zero (Polynomial.degree_eq_bot.mp h))
  · exact (cl27_digLift_spec T y hy).2.1

/-- CL-27(a): the digit lift has Gauss valuation 0 — `wPrev = 0` read through the
base pin `T.base.1.1` (the ScratchC6:327 step, named). Some coefficient of
`digLift y` is therefore a `ℤ_[p]`-unit. -/
theorem gaussVal_digLift_zero (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    gaussVal (T.digLift y) = 0 := by
  have hf : T.digLift y ≠ 0 := digLift_ne T hy
  have hwP : (T.stg 0).wPrev (T.digLift y) = 0 := (cl27_digLift_spec T y hy).2.2.1
  rw [← T.base.1.1 _ hf]
  exact hwP

/-- CL-27(a): basis monomials never vanish (copy of ScratchC6's private `mono_ne`;
`C(p^l)·∏Φ^s` with `p ≠ 0` and monic keys). -/
theorem mono_ne (T : Tower p F) (c : T.Coord) : T.mono c ≠ 0 := by
  rw [Tower.mono]
  refine mul_ne_zero ?_ ?_
  · rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ PadicInt.prime_p.ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero)

/-- Degree divisibility per move (copy of T4's private `t4_deg_dvd_step`):
`deg Φ_m ∣ deg Φ_{m+1}` (increment: `deg Φ̂ = e·g·deg Φ`; recentering: degree
unchanged). -/
private lemma cl27_deg_dvd_step (T : Tower p F) (m : ℕ) (hm : m < T.K) :
    (T.stg ⟨m, Nat.lt_succ_of_lt hm⟩).Φ.natDegree ∣ (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).Φ.natDegree := by
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.castSucc).Φ.natDegree ∣ (T.stg k.succ).Φ.natDegree
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core _ =>
    have hkey := core.base.child_key
    have hdeg := (L3_liftMonic (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
    rw [hkey, hdeg]
    exact ⟨(T.stg k.castSucc).e * g, by ring⟩
  | recenter cc tt core _ =>
    obtain ⟨_, _, _, htt, _, _, _, hΦ', _, _, _, _, _, _⟩ := core.base
    rw [hΦ']
    have hne1 : (T.stg k.castSucc).Φ - tt ≠ 0 := by rw [← hΦ']; exact (T.stg k.succ).hmonic.ne_zero
    have hne2 : (T.stg k.castSucc).Φ ≠ 0 := (T.stg k.castSucc).hmonic.ne_zero
    have hdegeq : ((T.stg k.castSucc).Φ - tt).degree = (T.stg k.castSucc).Φ.degree :=
      Polynomial.degree_sub_eq_left_of_degree_lt htt
    have hnd : ((T.stg k.castSucc).Φ - tt).natDegree = (T.stg k.castSucc).Φ.natDegree := by
      rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
      exact_mod_cast hdegeq
    rw [hnd]

/-- CL-27(a): the slot bound is EXACT — `slotBound r · deg Φ_r = deg Φ_{r+1}` (copy
of T4_slotMinHt's private `t4_slotBound_mul`; rests on the per-move degree
divisibility `t4_deg_dvd_step`, since `slotBound` is ℕ-division-defined). -/
theorem t4_slotBound_mul (T : Tower p F) (r : Fin T.K) :
    T.slotBound r * (T.stg r.castSucc).Φ.natDegree = (T.stg r.succ).Φ.natDegree := by
  have hcs : (⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ : Fin (T.K + 1)) = r.castSucc := Fin.ext rfl
  have hsc : (⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ : Fin (T.K + 1)) = r.succ := Fin.ext rfl
  have hdvd := cl27_deg_dvd_step T r.val r.isLt
  rw [hcs, hsc] at hdvd
  unfold Tower.slotBound
  exact Nat.div_mul_cancel hdvd

/-! ## (b) The mod-p transport -/

/-- CL-27(b): the coefficientwise mod-p reduction `ℤ_[p][x] → 𝔽_p[x]` — Mathlib's
`Polynomial.map` along `PadicInt.toZMod` (a ring hom, so it transports sums and
products; the whole REVISION-2 route needs no other quotient). -/
noncomputable def red (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] → Polynomial (ZMod p) :=
  Polynomial.map (PadicInt.toZMod)

/-- CL-27(b): reduction preserves monicity and (for monic inputs) the exact degree. -/
theorem red_monic_deg (Φ : Polynomial ℤ_[p]) (hΦ : Φ.Monic) :
    (red p Φ).Monic ∧ (red p Φ).natDegree = Φ.natDegree := by
  exact ⟨hΦ.map _, hΦ.natDegree_map _⟩

/-- CL-27(b): the exact key-degree ratio law survives reduction —
`deg (red Φ_{r+1}) = slotBound r · deg (red Φ_r)` (from `t4_slotBound_mul` +
`red_monic_deg`). This is CL-11's ratio hypothesis at `K₀ = 𝔽_p`. -/
theorem red_ratio_law (T : Tower p F) (r : Fin T.K) :
    (red p (T.stg r.succ).Φ).natDegree
      = T.slotBound r * (red p (T.stg r.castSucc).Φ).natDegree := by
  rw [(red_monic_deg (T.stg r.succ).Φ (T.stg r.succ).hmonic).2,
      (red_monic_deg (T.stg r.castSucc).Φ (T.stg r.castSucc).hmonic).2]
  exact (t4_slotBound_mul T r).symm

/-- CL-27(b): positive p-powers die under reduction — `red (C (p^k)) = 0` for
`1 ≤ k` (this is what kills the `l > l_min` terms in CL-12). -/
theorem red_p_pow_zero (k : ℕ) (hk : 1 ≤ k) :
    red p (Polynomial.C ((p : ℤ_[p]) ^ k)) = 0 := by
  rw [red, Polynomial.map_C]
  have hp : (PadicInt.toZMod ((p : ℤ_[p]) ^ k) : ZMod p) = 0 := by
    rw [map_pow]
    have h1 : (PadicInt.toZMod (p : ℤ_[p]) : ZMod p) = ((p : ℕ) : ZMod p) := by
      exact_mod_cast map_natCast (PadicInt.toZMod (p := p)) p
    rw [h1, ZMod.natCast_self, zero_pow (by omega)]
  rw [hp, Polynomial.C_0]

/-- CL-27(b): reduced digit lifts are nonzero — `gaussVal (digLift y) = 0`
(`gaussVal_digLift_zero`) means SOME coefficient is a `ℤ_[p]`-unit, which survives
`PadicInt.toZMod`. This is CL-11's nonzero-digit hypothesis at `K₀ = 𝔽_p`. -/
theorem red_digLift_ne (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    red p (T.digLift y) ≠ 0 := by
  have hf : T.digLift y ≠ 0 := digLift_ne T hy
  have hgv : gaussVal (T.digLift y) = 0 := gaussVal_digLift_zero T hy
  -- extract a valuation-0 (unit) coefficient from the attained inf'
  have hne : (T.digLift y).support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [gaussVal, dif_pos hne] at hgv
  obtain ⟨i, hi, hival⟩ := Finset.exists_mem_eq_inf' hne
    (fun i => (((T.digLift y).coeff i).valuation : ℤ))
  have hv0 : ((T.digLift y).coeff i).valuation = 0 := by
    have := hival ▸ hgv
    exact_mod_cast this
  have hci : (T.digLift y).coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  -- a valuation-0 nonzero element is a unit, hence survives `toZMod`
  have hnorm : ‖(T.digLift y).coeff i‖ = 1 := by
    rw [PadicInt.norm_eq_zpow_neg_valuation hci, hv0]
    norm_num
  have hunit : IsUnit ((T.digLift y).coeff i) := PadicInt.isUnit_iff.mpr hnorm
  intro hred
  have hcoeff0 : PadicInt.toZMod ((T.digLift y).coeff i) = 0 := by
    have := congrArg (fun q => Polynomial.coeff q i) hred
    simpa [red, Polynomial.coeff_map] using this
  have hker : (T.digLift y).coeff i ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hcoeff0
  rw [PadicInt.ker_toZMod] at hker
  exact (IsLocalRing.mem_maximalIdeal _).mp hker hunit

/-- CL-27(b): the reduced digit-degree bound `deg (red (digLift y)) < deg (red Φ₀)`
(digLift_deg + map-degree-≤ + monic full degree on the right). **R-2**: the LEFT
degree may genuinely DROP below `deg (digLift y)`; CL-11 tolerates any drop and this
statement must never be strengthened to degree preservation. -/
theorem red_digLift_deg (T : Tower p F) (y : ↥(T.stg 0).FQ) :
    (red p (T.digLift y)).degree < (red p (T.stg 0).Φ).degree := by
  have h1 : (red p (T.digLift y)).degree ≤ (T.digLift y).degree :=
    Polynomial.degree_map_le
  have h2 : (red p (T.stg 0).Φ).degree = (T.stg 0).Φ.degree :=
    (T.stg 0).hmonic.degree_map _
  rw [h2]
  exact lt_of_le_of_lt h1 (digLift_deg T y)

/-! ## (c) The factor-out kit (no division operator, no `ZMod (p^{l+1})`) -/

/-- CL-27(c): `C (p^k) ≠ 0` in `ℤ_[p][x]` — the cancellation partner for the
IsDomain step (`mul_ne_zero_iff`) of CL-12. -/
theorem C_p_pow_ne (k : ℕ) :
    (Polynomial.C ((p : ℤ_[p]) ^ k) : Polynomial ℤ_[p]) ≠ 0 := by
  rw [Ne, Polynomial.C_eq_zero]
  exact pow_ne_zero _ PadicInt.prime_p.ne_zero

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
  -- Step 1: normalize the finsum to the Finset sum over the support
  have hnorm : T.slotCoeff b y = ∑ c ∈ hfin.toFinset, T.digLift (y c) * T.mono c := by
    have hsub : ({c : T.Coord | T.blk c = b}
        ∩ Function.support fun c => T.digLift (y c) * T.mono c) ⊆ Function.support y := by
      rintro c ⟨-, hc⟩
      by_contra h0
      have hy0 : y c = 0 := Function.notMem_support.mp h0
      exact Function.mem_support.mp hc
        (by show T.digLift (y c) * T.mono c = 0; rw [hy0, cl27_digLift_zero T, zero_mul])
    have hfin' : ({c : T.Coord | T.blk c = b}
        ∩ Function.support fun c => T.digLift (y c) * T.mono c).Finite :=
      hfin.subset hsub
    rw [Tower.slotCoeff, finsum_mem_eq_sum _ hfin']
    apply Finset.sum_subset
    · intro c hc
      rw [Set.Finite.mem_toFinset] at hc ⊢
      exact hsub hc
    · intro c hcS hcn
      by_contra hne
      apply hcn
      rw [Set.Finite.mem_toFinset] at hcS ⊢
      refine ⟨?_, Function.mem_support.mpr hne⟩
      have hyc : y c ≠ 0 := Function.mem_support.mp hcS
      exact hblk c hyc
  -- Step 2: factor `C(p^lmin)` out of every term
  rw [hnorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hyc : y c ≠ 0 := Function.mem_support.mp (Set.Finite.mem_toFinset hfin |>.mp hc)
  have hlc : lmin + (c.l - lmin) = c.l := Nat.add_sub_cancel' (hlmin c hyc)
  have hpow : ((p : ℤ_[p]) ^ c.l) = (p : ℤ_[p]) ^ lmin * (p : ℤ_[p]) ^ (c.l - lmin) := by
    rw [← pow_add, hlc]
  rw [Tower.mono, hpow, map_mul]
  ring

/-! ## Private helpers for (d): T9(b)'s numeric kernel + the κ-lattice step law -/

/-- Prefix bound (T9's private `mr_prefix_lt`, copied): the base-`D` value of the
first `n` digits (each `a r < c r`) is `< D n`. -/
private lemma cl27_mr_prefix_lt (D c a : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) :
    ∀ n, (∀ r, r < n → a r < c r) → (∀ r, r < n → c r * D r ≤ D (r + 1)) →
      ∑ r ∈ Finset.range n, a r * D r < D n := by
  intro n
  induction n with
  | zero =>
      intro _ _
      simp only [Finset.range_zero, Finset.sum_empty]
      exact hD 0
  | succ m ih =>
      intro hb hstep
      rw [Finset.sum_range_succ]
      have hpre : ∑ r ∈ Finset.range m, a r * D r < D m :=
        ih (fun r hr => hb r (Nat.lt_succ_of_lt hr)) (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      have ham : a m + 1 ≤ c m := hb m (Nat.lt_succ_self m)
      calc ∑ r ∈ Finset.range m, a r * D r + a m * D m
          < D m + a m * D m := by omega
        _ = (a m + 1) * D m := by ring
        _ ≤ c m * D m := by gcongr
        _ ≤ D (m + 1) := hstep m (Nat.lt_succ_self m)

/-- Injectivity on a fully-bounded prefix (T9's private `mr_inj_prefix`, copied). -/
private lemma cl27_mr_inj_prefix (D c a b : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) :
    ∀ n, (∀ r, r < n → a r < c r) → (∀ r, r < n → b r < c r) →
      (∀ r, r < n → c r * D r ≤ D (r + 1)) →
      ∑ r ∈ Finset.range n, a r * D r = ∑ r ∈ Finset.range n, b r * D r →
      ∀ r, r < n → a r = b r := by
  intro n
  induction n with
  | zero => intro _ _ _ _ r hr; exact absurd hr (Nat.not_lt_zero r)
  | succ m ih =>
      intro ha hb hstep hsum r hr
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
      have hpa : ∑ r ∈ Finset.range m, a r * D r < D m :=
        cl27_mr_prefix_lt D c a hD m (fun r hr => ha r (Nat.lt_succ_of_lt hr))
          (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      have hpb : ∑ r ∈ Finset.range m, b r * D r < D m :=
        cl27_mr_prefix_lt D c b hD m (fun r hr => hb r (Nat.lt_succ_of_lt hr))
          (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      set Pa := ∑ r ∈ Finset.range m, a r * D r with hPadef
      set Pb := ∑ r ∈ Finset.range m, b r * D r with hPbdef
      have hDm : 0 < D m := hD m
      have hPaeq : (Pa + a m * D m) % D m = Pa := by
        rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpa
      have hPbeq : (Pb + b m * D m) % D m = Pb := by
        rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpb
      have hmod : Pa = Pb := by rw [← hPaeq, ← hPbeq, hsum]
      have hamm : a m * D m = b m * D m := by omega
      have ham : a m = b m := Nat.eq_of_mul_eq_mul_right hDm hamm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · exact ih (fun r hr => ha r (Nat.lt_succ_of_lt hr))
              (fun r hr => hb r (Nat.lt_succ_of_lt hr))
              (fun r hr => hstep r (Nat.lt_succ_of_lt hr)) hmod r hlt
      · subst heq; exact ham

/-- Top-peel injectivity (T9's private `mr_inj_top`, copied): positions `0..n-1`
bounded, position `n` free; equal base-`D` value forces agreement on all of `0..n`. -/
private lemma cl27_mr_inj_top (D c a b : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) (n : ℕ)
    (ha : ∀ r, r < n → a r < c r) (hb : ∀ r, r < n → b r < c r)
    (hstep : ∀ r, r < n → c r * D r ≤ D (r + 1))
    (hsum : ∑ r ∈ Finset.range (n + 1), a r * D r = ∑ r ∈ Finset.range (n + 1), b r * D r) :
    ∀ r, r ≤ n → a r = b r := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
  have hpa : ∑ r ∈ Finset.range n, a r * D r < D n := cl27_mr_prefix_lt D c a hD n ha hstep
  have hpb : ∑ r ∈ Finset.range n, b r * D r < D n := cl27_mr_prefix_lt D c b hD n hb hstep
  set Pa := ∑ r ∈ Finset.range n, a r * D r with hPadef
  set Pb := ∑ r ∈ Finset.range n, b r * D r with hPbdef
  have hDn : 0 < D n := hD n
  have hPaeq : (Pa + a n * D n) % D n = Pa := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpa
  have hPbeq : (Pb + b n * D n) % D n = Pb := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpb
  have hmod : Pa = Pb := by rw [← hPaeq, ← hPbeq, hsum]
  have hamm : a n * D n = b n * D n := by omega
  have han : a n = b n := Nat.eq_of_mul_eq_mul_right hDn hamm
  intro r hr
  rcases hr.lt_or_eq with hlt | heq
  · exact cl27_mr_inj_prefix D c a b hD n ha hb hstep hmod r hlt
  · subst heq; exact han

/-- `strAux` recursion at an in-range index (T4's private `t4_strAux_succ`, copied). -/
private lemma cl27_strAux_succ (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    T.strAux (k + 1) = T.strAux k * (T.stg ⟨k, hk⟩).e := by
  have h : T.strAux (k + 1)
      = T.strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) := rfl
  rw [h, dif_pos hk]

private lemma cl27_strAux_pos (T : Tower p F) (k : ℕ) : 0 < T.strAux k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ n ih =>
    by_cases hc : n < T.K + 1
    · rw [cl27_strAux_succ T n hc]
      exact Nat.mul_pos ih (by have := (T.stg ⟨n, hc⟩).he; omega)
    · have h : T.strAux (n + 1)
          = T.strAux n * (if h : n < T.K + 1 then (T.stg ⟨n, h⟩).e else 1) := rfl
      rw [h, dif_neg hc, mul_one]; exact ih

private lemma cl27_strTop_eq (T : Tower p F) : T.strTop = T.strAux (T.K + 1) := by
  rw [cl27_strAux_succ T T.K (Nat.lt_succ_self _)]; rfl

/-- `strAux` divides along the chain. -/
private lemma cl27_strAux_dvd (T : Tower p F) (a : ℕ) :
    ∀ b, a ≤ b → T.strAux a ∣ T.strAux b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact dvd_refl _
  | succ n hn ih =>
    have h : T.strAux (n + 1)
        = T.strAux n * (if h : n < T.K + 1 then (T.stg ⟨n, h⟩).e else 1) := rfl
    rw [h]
    exact Dvd.dvd.mul_right ih _

/-- The ℕ-valued lattice height of one κ-place: `ND r = h_r · (strTop / STR_{r+1})`
(= `strTop·κ_r`, an integer by the stretch-divisibility chain); junk 1 beyond K. -/
private noncomputable def cl27_ND (T : Tower p F) (r : ℕ) : ℕ :=
  if h : r < T.K + 1 then (T.stg ⟨r, h⟩).h * (T.strAux (T.K + 1) / T.strAux (r + 1)) else 1

/-- The extended slot-bound radices (T9's shape): `slotBound` inside, junk 1 beyond. -/
private noncomputable def cl27_cb (T : Tower p F) (r : ℕ) : ℕ :=
  if h : r < T.K then T.slotBound ⟨r, h⟩ else 1

private lemma cl27_ND_pos (T : Tower p F) (r : ℕ) : 1 ≤ cl27_ND T r := by
  rw [cl27_ND]
  by_cases h : r < T.K + 1
  · rw [dif_pos h]
    have hh := (T.stg ⟨r, h⟩).hh
    have hdvd : T.strAux (r + 1) ∣ T.strAux (T.K + 1) := cl27_strAux_dvd T (r + 1) (T.K + 1) (by omega)
    have hpos : 0 < T.strAux (T.K + 1) / T.strAux (r + 1) :=
      Nat.div_pos (Nat.le_of_dvd (cl27_strAux_pos T _) hdvd) (cl27_strAux_pos T _)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [dif_neg h]

/-- `ND` is `strTop·κ` as rationals (the exact-division cast). -/
private lemma cl27_ND_cast (T : Tower p F) (r : Fin (T.K + 1)) :
    ((cl27_ND T r.val : ℕ) : ℚ) = (T.strTop : ℚ) * T.kappa r := by
  have hlt : r.val < T.K + 1 := r.isLt
  rw [cl27_ND, dif_pos hlt]
  have hdvd : T.strAux (r.val + 1) ∣ T.strAux (T.K + 1) :=
    cl27_strAux_dvd T (r.val + 1) (T.K + 1) (by omega)
  have hM : (T.strAux (T.K + 1) / T.strAux (r.val + 1)) * T.strAux (r.val + 1)
      = T.strAux (T.K + 1) := Nat.div_mul_cancel hdvd
  have hstgr : T.stg ⟨r.val, hlt⟩ = T.stg r := by congr 1
  have hstr1 : T.strAux (r.val + 1) = T.str r * (T.stg r).e := by
    rw [show T.str r = T.strAux r.val from rfl, ← hstgr]
    exact cl27_strAux_succ T r.val hlt
  have hSpos : (0 : ℚ) < (T.strAux (r.val + 1) : ℚ) := by
    exact_mod_cast cl27_strAux_pos T (r.val + 1)
  have hden : ((T.stg r).e : ℚ) * (T.str r : ℚ) ≠ 0 := by
    have he := (T.stg r).he
    have hstr : 0 < T.str r := cl27_strAux_pos T r.val
    positivity
  -- clear the denominator: both sides times strAux (r+1) ≠ 0
  apply mul_right_cancel₀ (ne_of_gt hSpos)
  have hNat : (T.stg ⟨r.val, hlt⟩).h * (T.strAux (T.K + 1) / T.strAux (r.val + 1))
        * T.strAux (r.val + 1)
      = T.strAux (T.K + 1) * (T.stg ⟨r.val, hlt⟩).h := by
    rw [mul_assoc, hM]; ring
  have hL : (((T.stg ⟨r.val, hlt⟩).h * (T.strAux (T.K + 1) / T.strAux (r.val + 1)) : ℕ) : ℚ)
        * (T.strAux (r.val + 1) : ℚ)
      = (T.strAux (T.K + 1) : ℚ) * ((T.stg ⟨r.val, hlt⟩).h : ℚ) := by
    exact_mod_cast hNat
  have hR : (T.strTop : ℚ) * T.kappa r * (T.strAux (r.val + 1) : ℚ)
      = (T.strAux (T.K + 1) : ℚ) * ((T.stg ⟨r.val, hlt⟩).h : ℚ) := by
    have hcast : (T.strAux (r.val + 1) : ℚ) = ((T.stg r).e : ℚ) * (T.str r : ℚ) := by
      rw [hstr1]; push_cast; ring
    rw [Tower.kappa, cl27_strTop_eq T, hcast, hstgr]
    calc (T.strAux (T.K + 1) : ℚ) * (((T.stg r).h : ℚ) / (((T.stg r).e : ℚ) * (T.str r : ℚ)))
          * (((T.stg r).e : ℚ) * (T.str r : ℚ))
        = (T.strAux (T.K + 1) : ℚ)
          * ((((T.stg r).h : ℚ) / (((T.stg r).e : ℚ) * (T.str r : ℚ)))
            * (((T.stg r).e : ℚ) * (T.str r : ℚ))) := by ring
      _ = (T.strAux (T.K + 1) : ℚ) * ((T.stg r).h : ℚ) := by
          rw [div_mul_cancel₀ _ hden]
  exact hL.trans hR.symm

/-- **The mixed-radix step law on the κ-lattice** — the one new content of (d):
`slotBound r · ND r ≤ ND (r+1)`. Increment: (I-aug) `h′ > e′·w(Φ̂)` with
`w(Φ̂) = e·h·g` (L3_liftWeight) and `slotBound = e·g`; recentering:
`slotBound = 1`, `e′ = 1`, and `h ≤ h′` by the ultrametric. -/
private lemma cl27_ND_step (T : Tower p F) (r : ℕ) (hr : r < T.K) :
    cl27_cb T r * cl27_ND T r ≤ cl27_ND T (r + 1) := by
  have hr1 : r < T.K + 1 := Nat.lt_succ_of_lt hr
  have hr2 : r + 1 < T.K + 1 := by omega
  rw [cl27_cb, dif_pos hr, cl27_ND, cl27_ND, dif_pos hr1, dif_pos hr2]
  -- the exact-division bookkeeping: M_r = e_{r+1} · M_{r+1}
  set A := T.strAux (T.K + 1) with hA
  set Mr := A / T.strAux (r + 1) with hMr
  set Mr1 := A / T.strAux (r + 2) with hMr1
  have hdvd2 : T.strAux (r + 2) ∣ A := cl27_strAux_dvd T (r + 2) (T.K + 1) (by omega)
  have hstr2 : T.strAux (r + 2) = T.strAux (r + 1) * (T.stg ⟨r + 1, hr2⟩).e :=
    cl27_strAux_succ T (r + 1) hr2
  have hMfact : Mr = (T.stg ⟨r + 1, hr2⟩).e * Mr1 := by
    have hA2 : A = T.strAux (r + 2) * Mr1 := (Nat.mul_div_cancel' hdvd2).symm
    have hA1 : A = T.strAux (r + 1) * ((T.stg ⟨r + 1, hr2⟩).e * Mr1) := by
      rw [hA2, hstr2]; ring
    rw [hMr, hA1]
    exact Nat.mul_div_cancel_left _ (cl27_strAux_pos T (r + 1))
  -- reduce to the per-move inequality `slotBound·h·e′ ≤ h′`
  have hkey : T.slotBound ⟨r, hr⟩ * (T.stg ⟨r, hr1⟩).h * (T.stg ⟨r + 1, hr2⟩).e
      ≤ (T.stg ⟨r + 1, hr2⟩).h := by
    set k : Fin T.K := ⟨r, hr⟩ with hk
    have hcs : (⟨r, hr1⟩ : Fin (T.K + 1)) = k.castSucc := Fin.ext rfl
    have hsc : (⟨r + 1, hr2⟩ : Fin (T.K + 1)) = k.succ := Fin.ext rfl
    rw [hcs, hsc]
    have hdpos : 0 < (T.stg k.castSucc).Φ.natDegree := (T.stg k.castSucc).hdeg
    cases T.move k with
    | inc ψ g Φhat e' h' zbar hyp core _ =>
      -- slotBound = e·g via the exact lift degree
      have hkey := core.base.child_key
      have hdeg := (L3_liftMonic (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
      have hsb : T.slotBound k = (T.stg k.castSucc).e * g := by
        unfold Tower.slotBound
        rw [hkey, hdeg]
        exact Nat.mul_div_cancel _ hdpos
      have hΦne : Φhat ≠ 0 := by
        rw [← hkey]; exact (T.stg k.succ).hmonic.ne_zero
      have hw := L3_liftWeight (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift hΦne
      have hIA : ((h' : ℤ)) > (e' : ℤ) * (((T.stg k.castSucc).e : ℤ) * (T.stg k.castSucc).h * g) := by
        rw [← hw]; exact hyp.hiaug
      have he' : (T.stg k.succ).e = e' := core.base.child_e
      have hh' : (T.stg k.succ).h = h' := core.base.child_h
      rw [hsb, he', hh']
      have hZ : (((T.stg k.castSucc).e * g * (T.stg k.castSucc).h * e' : ℕ) : ℤ) < (h' : ℤ) := by
        calc (((T.stg k.castSucc).e * g * (T.stg k.castSucc).h * e' : ℕ) : ℤ)
            = (e' : ℤ) * (((T.stg k.castSucc).e : ℤ) * (T.stg k.castSucc).h * g) := by
              push_cast; ring
          _ < h' := hIA
      exact le_of_lt (by exact_mod_cast hZ)
    | recenter cc tt core _ =>
      obtain ⟨he1, he'1, hcc, htt, httne, hwtt, hRtt, hΦ', hweq, hwPeq, hKeq, hFQeq, hWSeq, hdig⟩ :=
        core.base
      -- slotBound = 1: the recentered key keeps the degree
      have hne1 : (T.stg k.castSucc).Φ - tt ≠ 0 := by
        rw [← hΦ']; exact (T.stg k.succ).hmonic.ne_zero
      have hne2 : (T.stg k.castSucc).Φ ≠ 0 := (T.stg k.castSucc).hmonic.ne_zero
      have hdegeq : ((T.stg k.castSucc).Φ - tt).degree = (T.stg k.castSucc).Φ.degree :=
        Polynomial.degree_sub_eq_left_of_degree_lt htt
      have hnd : ((T.stg k.castSucc).Φ - tt).natDegree = (T.stg k.castSucc).Φ.natDegree := by
        rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
        exact_mod_cast hdegeq
      have hsb : T.slotBound k = 1 := by
        unfold Tower.slotBound
        rw [hΦ', hnd]
        exact Nat.div_self hdpos
      -- h ≤ h′ by the ultrametric at the recentered key
      have hw1 : (T.stg k.castSucc).w 1 = 0 := by
        have hw := (T.stg k.castSucc).hwmul 1 1 one_ne_zero one_ne_zero
        rw [mul_one] at hw; omega
      have hCn1 : (Polynomial.C (-1 : ℤ_[p])) ≠ 0 := by
        rw [Polynomial.C_ne_zero]; norm_num
      have hwCn1 : (T.stg k.castSucc).w (Polynomial.C (-1 : ℤ_[p])) = 0 := by
        have hw := (T.stg k.castSucc).hwmul (Polynomial.C (-1)) (Polynomial.C (-1)) hCn1 hCn1
        rw [← Polynomial.C_mul] at hw
        have he : ((-1 : ℤ_[p]) * (-1)) = 1 := by ring
        rw [he, Polynomial.C_1, hw1] at hw
        omega
      have hwneg : (T.stg k.castSucc).w (-tt) = (T.stg k.castSucc).w tt := by
        have hfact : -tt = Polynomial.C (-1 : ℤ_[p]) * tt := by
          rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
        rw [hfact, (T.stg k.castSucc).hwmul _ tt hCn1 httne, hwCn1, zero_add]
      have hwsum : min ((T.stg k.castSucc).w (T.stg k.castSucc).Φ)
          ((T.stg k.castSucc).w (-tt))
          ≤ (T.stg k.castSucc).w ((T.stg k.castSucc).Φ + -tt) := by
        apply (T.stg k.castSucc).hwult _ _ hne2 (neg_ne_zero.mpr httne)
        rw [← sub_eq_add_neg]
        exact hne1
      rw [hwneg, hwtt, (T.stg k.castSucc).hwΦ, min_self, ← sub_eq_add_neg] at hwsum
      have hwchild : (T.stg k.succ).w ((T.stg k.castSucc).Φ - tt) = (T.stg k.succ).h := by
        rw [← hΦ']
        exact (T.stg k.succ).hwΦ
      rw [hweq] at hwchild
      rw [hwchild] at hwsum
      have hhle : (T.stg k.castSucc).h ≤ (T.stg k.succ).h := by exact_mod_cast hwsum
      rw [hsb, he'1, one_mul, mul_one]
      exact hhle
  calc T.slotBound ⟨r, hr⟩ * ((T.stg ⟨r, hr1⟩).h * Mr)
      = (T.slotBound ⟨r, hr⟩ * (T.stg ⟨r, hr1⟩).h * (T.stg ⟨r + 1, hr2⟩).e) * Mr1 := by
        rw [hMfact]; ring
    _ ≤ (T.stg ⟨r + 1, hr2⟩).h * Mr1 := Nat.mul_le_mul_right _ hkey

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
  -- Step 1: from equal heights and equal p-levels, equal κ-sums
  have hkap : ∑ r, (c.slot r : ℚ) * T.kappa r = ∑ r, (c'.slot r : ℚ) * T.kappa r := by
    have h1 := hht
    rw [Tower.ht, Tower.ht, hl] at h1
    linarith
  -- Step 2: multiply through by strTop and convert to the ℕ-valued ND places
  have hND : ∑ r : Fin (T.K + 1), (c.slot r : ℚ) * ((cl27_ND T r.val : ℕ) : ℚ)
      = ∑ r : Fin (T.K + 1), (c'.slot r : ℚ) * ((cl27_ND T r.val : ℕ) : ℚ) := by
    have h2 : ∑ r : Fin (T.K + 1), (c.slot r : ℚ) * ((T.strTop : ℚ) * T.kappa r)
        = ∑ r : Fin (T.K + 1), (c'.slot r : ℚ) * ((T.strTop : ℚ) * T.kappa r) := by
      have hl2 : (T.strTop : ℚ) * ∑ r, (c.slot r : ℚ) * T.kappa r
          = (T.strTop : ℚ) * ∑ r, (c'.slot r : ℚ) * T.kappa r := by rw [hkap]
      rw [Finset.mul_sum, Finset.mul_sum] at hl2
      calc ∑ r : Fin (T.K + 1), (c.slot r : ℚ) * ((T.strTop : ℚ) * T.kappa r)
          = ∑ r : Fin (T.K + 1), (T.strTop : ℚ) * ((c.slot r : ℚ) * T.kappa r) := by
            apply Finset.sum_congr rfl; intro r _; ring
        _ = ∑ r : Fin (T.K + 1), (T.strTop : ℚ) * ((c'.slot r : ℚ) * T.kappa r) := hl2
        _ = ∑ r : Fin (T.K + 1), (c'.slot r : ℚ) * ((T.strTop : ℚ) * T.kappa r) := by
            apply Finset.sum_congr rfl; intro r _; ring
    calc ∑ r : Fin (T.K + 1), (c.slot r : ℚ) * ((cl27_ND T r.val : ℕ) : ℚ)
        = ∑ r : Fin (T.K + 1), (c.slot r : ℚ) * ((T.strTop : ℚ) * T.kappa r) := by
          apply Finset.sum_congr rfl; intro r _; rw [cl27_ND_cast T r]
      _ = ∑ r : Fin (T.K + 1), (c'.slot r : ℚ) * ((T.strTop : ℚ) * T.kappa r) := h2
      _ = ∑ r : Fin (T.K + 1), (c'.slot r : ℚ) * ((cl27_ND T r.val : ℕ) : ℚ) := by
          apply Finset.sum_congr rfl; intro r _; rw [cl27_ND_cast T r]
  -- Step 3: descend to a ℕ equation on range-sums
  have hNat : ∑ r ∈ Finset.range (T.K + 1),
        (if h : r < T.K + 1 then c.slot ⟨r, h⟩ else 0) * cl27_ND T r
      = ∑ r ∈ Finset.range (T.K + 1),
        (if h : r < T.K + 1 then c'.slot ⟨r, h⟩ else 0) * cl27_ND T r := by
    have hconv : ∀ d : T.Coord,
        ((∑ r ∈ Finset.range (T.K + 1),
          (if h : r < T.K + 1 then d.slot ⟨r, h⟩ else 0) * cl27_ND T r : ℕ) : ℚ)
        = ∑ r : Fin (T.K + 1), (d.slot r : ℚ) * ((cl27_ND T r.val : ℕ) : ℚ) := by
      intro d
      push_cast
      rw [← Fin.sum_univ_eq_sum_range
        (fun r => ((if h : r < T.K + 1 then d.slot ⟨r, h⟩ else 0 : ℕ) : ℚ) * ((cl27_ND T r : ℕ) : ℚ)) (T.K + 1)]
      apply Finset.sum_congr rfl
      intro i _
      rw [dif_pos i.isLt]
    have hq := hND
    rw [← hconv c, ← hconv c'] at hq
    exact_mod_cast hq
  -- Step 4: mixed-radix injectivity pins the slot vectors
  have hD : ∀ r, 1 ≤ cl27_ND T r := cl27_ND_pos T
  have hstep : ∀ r, r < T.K → cl27_cb T r * cl27_ND T r ≤ cl27_ND T (r + 1) :=
    fun r hr => cl27_ND_step T r hr
  have haC : ∀ r, r < T.K →
      (if h : r < T.K + 1 then c.slot ⟨r, h⟩ else 0) < cl27_cb T r := by
    intro r hr
    have hr1 : r < T.K + 1 := Nat.lt_succ_of_lt hr
    rw [cl27_cb, dif_pos hr, dif_pos hr1]
    have hcs : (⟨r, hr⟩ : Fin T.K).castSucc = (⟨r, hr1⟩ : Fin (T.K + 1)) := rfl
    have := c.slot_lt ⟨r, hr⟩
    rwa [hcs] at this
  have haC' : ∀ r, r < T.K →
      (if h : r < T.K + 1 then c'.slot ⟨r, h⟩ else 0) < cl27_cb T r := by
    intro r hr
    have hr1 : r < T.K + 1 := Nat.lt_succ_of_lt hr
    rw [cl27_cb, dif_pos hr, dif_pos hr1]
    have hcs : (⟨r, hr⟩ : Fin T.K).castSucc = (⟨r, hr1⟩ : Fin (T.K + 1)) := rfl
    have := c'.slot_lt ⟨r, hr⟩
    rwa [hcs] at this
  have hslots := cl27_mr_inj_top (cl27_ND T) (cl27_cb T)
    (fun r => if h : r < T.K + 1 then c.slot ⟨r, h⟩ else 0)
    (fun r => if h : r < T.K + 1 then c'.slot ⟨r, h⟩ else 0)
    hD T.K haC haC' hstep hNat
  have hslot : c.slot = c'.slot := by
    funext i
    have hi : (i : ℕ) < T.K + 1 := i.2
    have hle : (i : ℕ) ≤ T.K := Nat.lt_succ_iff.mp hi
    have hik := hslots (i : ℕ) hle
    rw [dif_pos hi, dif_pos hi] at hik
    exact hik
  -- Step 5: assemble `Coord` equality (proof field irrelevant)
  obtain ⟨l, s, hs⟩ := c
  obtain ⟨l', s', hs'⟩ := c'
  replace hl : l = l' := hl
  replace hslot : s = s' := hslot
  subst hl
  subst hslot
  rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.slotCoeff_factor
#print axioms LeanUrat.HC1.coord_eq_of_ht_l_eq
