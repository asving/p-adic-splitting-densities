/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpTypeChainLeaves
import LeanUrat.OM.QpTypeH3

/-!
# QpTypeLeafMasters — the general-(H, m, k) leaf masters and the tail-generic step decode
(Wild Wave 6c task A, `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §1, §2-W6c-a)

The W6c goal is faithfulness in EVERY fiber of the full n = 2 model. This module supplies
the AXIOM-FREE analytic payload at all parameters (the blueprint's five masters, §1.1, plus
the §1.2 step decode), generalizing the banked depth-1 / H ∈ {1,3} anchors:

* `stepDecode_general` — **the tail-generic general-`m` step decode** (blueprint §1.2): a
  genuine monic quadratic whose box pair at staircase frame `(L₀, L₁)` (with `2m ≤ L₀`,
  `m ≤ L₁`, `L₀ ≤ L₁`) satisfies `ChainPair (m :: ms') leaf` yields the genuine recentered
  monic quadratic `g` with `f(p^m·y + ĉp^m) = p^{2m}·g(y)` whose box at the child frame
  `(L₀ − 2m, L₁ − m)` satisfies `ChainPair ms' leaf` — the tail rides through the
  `descendPair` box match for free. Generalizes `QpTypeChainLeaves.chainStep_decode`
  (`m = 1`, `ms' = []`).
* `leafRam_master_irreducible` / `leafRam_master_forced` — **the (R) ram master, ALL odd
  `H`** (blueprint §1.1 (R)): `g = y² + b₁y + b₀` with `b₀ = p^H·u` (`ū ≠ 0`, so
  `v(b₀) = H` exact), `p^{(H+1)/2} ∣ b₁`, `H` odd, is irreducible over ℚ_p (the two-root
  valuation-parity contradiction of `QpTypeH3.wildH3_irreducible'`, `3` replaced by odd `H`)
  and EVERY `LocalFactorData` bundle carries `(e, f) = (2, 1)` (the ϖ-order parity argument
  of `QpTypeH3.ef_of_wildH3`, `3` replaced by odd `H`, pure DVR divisibility).
* `leafInert_master_irreducible` / `leafInert_master_forced` — **the (I) inert master, ALL
  `m ≥ 0`** (blueprint §1.1 (I)): `b₀ = p^{2m}·w₀`, `b₁ = p^m·w₁` with root-free residual
  pair `(w̄₀, w̄₁) ∈ noRootPairs` gives irreducibility and every-bundle `(e, f) = (1, 2)` —
  the general-`m` rescale relation `g(p^m·z) = p^{2m}·h(z)` (`leafInert_rescale`) transports
  to/from `h = z² + w₁z + w₀`, where the landed `ef_of_inert_quadratic` /
  `inert_irreducible_Qp` fire; the bundle pullback is the landed `compData` at the inverted
  affine data (the `chainGate_ef_forced` pattern at `a = p^m`, `c = 0`). At `m = 0` the
  rescale is trivial — the (I0) order-0 instance comes for free.
* `leafSplit_master_hasType` — **the (S) split master, ALL `k ≥ 0`** (blueprint §1.1 (S)):
  `b₁ = p^k·w₁` (`w̄₁ ≠ 0`) and `p^{2k+1} ∣ b₀` yield a GENUINE ℚ_p-factorization
  certificate of type `{(1,1),(1,1)}` — Hensel at the two distinct simple residual roots of
  `h̄ = z(z + w̄₁)` (the landed `split_two_roots`/`pairFactorization`), transported by the
  PROVED `qpType_translate_rescale` machinery at `a = p^k`, `c = 0`. `k = 0` and `b₀ = 0`
  both work (the (S0) order-0 instance is the `k = 0` boundary case).
* `leafFiber_ram_forced` / `leafFiber_inert_forced` / `leafFiber_split_hasType` — **the
  box-decode wrappers** tying the masters to the `LeafPair` fibers: membership of the box
  pair of a genuine monic quadratic in the leaf digit fiber (frame `leafNeed ≤ L₀ ≤ L₁`)
  decodes (`dvd_of_box_dvd` + the digit→residue bridge `box_digit_toZMod`) to the genuine
  master hypotheses and concludes the corresponding master conclusions.

Leaf module discipline: **no axiom, no `sorry`** — every declaration core-only (AxCheck at
bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.QpTypeLeafMasters

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu LeanUrat.OM.CellCard
open LeanUrat.OM.QpTypeChain LeanUrat.OM.QpTypeChainLeaves

/-! ## Block 1 — the tail-generic general-`m` step decode (blueprint §1.2) -/

section StepDecode

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The tail-generic step decode at head slope `m`** (blueprint §1.2, the displayed
statement): if the box pair of a genuine monic quadratic `f` at staircase frame `(L₀, L₁)`
(with `2m ≤ L₀`, `m ≤ L₁`, `L₀ ≤ L₁`) satisfies `ChainPair (m :: ms') leaf`, there are
`ĉ ∈ ℕ` (the stratum's existential unit digit) and a genuine monic quadratic `g` with the
step relation `f(p^m·y + ĉp^m) = p^{2m}·g(y)` whose box pair at the child frame
`(L₀ − 2m, L₁ − m)` satisfies `ChainPair ms' leaf` — the tail (arbitrary `ms'`) transports
through the `descendPair` box match definitionally. Generalizes
`QpTypeChainLeaves.chainStep_decode` (`m = 1`, `ms' = []`).

The frame hypothesis `L₀ ≤ L₁` (not just `2m ≤ L₀`, `m ≤ L₁`) is REQUIRED: the
`descendPair` transport reads the `b₁`-slot into the child `b₀`-slot at level `L₀ − 2m`,
which the level-`L₁` box only determines when `L₀ − 2m ≤ L₁ − m`. Along the unwind the
staircase invariant `L₀ ≤ L₁` supplies it. -/
theorem stepDecode_general {m L₀ L₁ : ℕ} (_hm : 1 ≤ m) (h2m : 2 * m ≤ L₀) (hm1 : m ≤ L₁)
    (hL01 : L₀ ≤ L₁) (ms' : List ℕ) (leaf : ChainMenu.ChainLeaf)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainPair p (m :: ms') leaf L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    ∃ (ĉ : ℕ) (g : ℤ_[p][X]) (_ : g.Monic), g.natDegree = 2 ∧
      f.comp (C ((p : ℤ_[p]) ^ m) * X + C ((ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ m))
        = C ((p : ℤ_[p]) ^ (2 * m)) * g ∧
      ChainMenu.ChainPair p ms' leaf (L₀ - 2 * m) (L₁ - m)
        (PadicInt.toZModPow (L₀ - 2 * m) (g.coeff 0),
          PadicInt.toZModPow (L₁ - m) (g.coeff 1)) := by
  simp only [ChainMenu.ChainPair] at hfib
  obtain ⟨c, hstep, htail⟩ := hfib
  simp only [RecenterBox.StratumPair, RecenterBox.CoordCond] at hstep
  obtain ⟨⟨hd0, -⟩, ⟨hd1, -⟩⟩ := hstep
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p h2m hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p hm1 hd1
  set ĉ : ℕ := ((c : ZMod p)).val with hĉ
  set b₁ : ℤ_[p] := w₁ + 2 * (ĉ : ℤ_[p]) with hb₁
  set b₀ : ℤ_[p] := w₀ + (ĉ : ℤ_[p]) * w₁ + (ĉ : ℤ_[p]) ^ 2 with hb₀
  set g : ℤ_[p][X] := X ^ 2 + C b₁ * X + C b₀ with hgdef
  have hg : g.Monic := by
    rw [hgdef]
    monicity!
  have hgdeg : g.natDegree = 2 := by
    rw [hgdef]
    compute_degree!
  have hg0 : g.coeff 0 = b₀ := by
    rw [hgdef]
    simp
  have hg1 : g.coeff 1 = b₁ := by
    rw [hgdef]
    simp
  have hrel : f.comp (C ((p : ℤ_[p]) ^ m) * X + C ((ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ m))
      = C ((p : ℤ_[p]) ^ (2 * m)) * g := by
    conv_lhs => rw [monic_quadratic_eq p hf hdeg]
    rw [hw₀, hw₁, hgdef, hb₀, hb₁]
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_add, map_mul, map_pow, map_ofNat]
    ring
  have hdesc : ChainMenu.descendPair p m ĉ
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))
      = (PadicInt.toZModPow (L₀ - 2 * m) b₀, PadicInt.toZModPow (L₁ - m) b₁) := by
    unfold ChainMenu.descendPair
    refine Prod.ext ?_ ?_
    · show ((((PadicInt.toZModPow L₀ (f.coeff 0)).val / p ^ (2 * m) : ℕ))
          : ZMod (p ^ (L₀ - 2 * m)))
        + (ĉ : ZMod (p ^ (L₀ - 2 * m)))
            * (((PadicInt.toZModPow L₁ (f.coeff 1)).val / p ^ m : ℕ)
                : ZMod (p ^ (L₀ - 2 * m)))
        + (ĉ : ZMod (p ^ (L₀ - 2 * m))) ^ 2 = PadicInt.toZModPow (L₀ - 2 * m) b₀
      rw [hw₀, hw₁, box_shift_cast p h2m (le_refl _),
        box_shift_cast p hm1 (show L₀ - 2 * m ≤ L₁ - m by omega),
        hb₀, map_add, map_add, map_mul, map_pow, map_natCast]
    · show (((PadicInt.toZModPow L₁ (f.coeff 1)).val / p ^ m : ℕ) : ZMod (p ^ (L₁ - m)))
        + 2 * (ĉ : ZMod (p ^ (L₁ - m))) = PadicInt.toZModPow (L₁ - m) b₁
      rw [hw₁, box_shift_cast p hm1 (le_refl _),
        hb₁, map_add, map_mul, map_natCast, map_ofNat]
  rw [hdesc] at htail
  rw [← hg0, ← hg1] at htail
  exact ⟨ĉ, g, hg, hgdeg, hrel, htail⟩

end StepDecode

/-! ## Block 2 — unit-digit decode helpers -/

section UnitDigit

variable (p : ℕ) [hp : Fact p.Prime]

/-- A nonzero mod-`p` residue makes the element a UNIT of `ℤ_[p]`. -/
theorem isUnit_of_toZMod_ne {u : ℤ_[p]} (hu : PadicInt.toZMod u ≠ 0) : IsUnit u := by
  have hpu : ¬ (p : ℤ_[p]) ∣ u := fun hd => hu ((toZMod_eq_zero_iff p u).mpr hd)
  rw [PadicInt.isUnit_iff]
  rcases lt_or_eq_of_le (PadicInt.norm_le_one u) with hlt | he
  · exact absurd ((PadicInt.norm_lt_one_iff_dvd u).mp hlt) hpu
  · exact he

/-- A nonzero mod-`p` residue pins the valuation to `0`. -/
theorem valuation_eq_zero_of_toZMod_ne {u : ℤ_[p]} (hu : PadicInt.toZMod u ≠ 0) :
    u.valuation = 0 := by
  have hpu : ¬ (p : ℤ_[p]) ∣ u := fun hd => hu ((toZMod_eq_zero_iff p u).mpr hd)
  have hu0 : u ≠ 0 := fun h0 => hu (by rw [h0, map_zero])
  by_contra hne
  have h1 : 1 ≤ u.valuation := by omega
  have hmem := (PadicInt.mem_span_pow_iff_le_valuation u hu0 1).mpr h1
  rw [pow_one, Ideal.mem_span_singleton] at hmem
  exact hpu hmem

end UnitDigit

/-! ## Block 3 — the RAM master (R): all odd heights `H`
(the H = 3 anchors `QpTypeH3.wildH3_irreducible'` / `ef_of_wildH3`, `3` replaced by odd `H`,
arithmetic by `omega`) -/

section RamMaster

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The (R) ram master, irreducibility leg (blueprint §1.1 (R)), all odd `H`.**
`g = y² + b₁y + b₀` over `ℤ_[p]` with `b₀ = p^H·u` (`ū ≠ 0`, i.e. `v(b₀) = H` exact),
`p^{(H+1)/2} ∣ b₁`, `H` odd, is irreducible over ℚ_p.

Route (the `QpTypeH3.wildH3_irreducible'` two-root argument, NO Newton polygon):
reducibility of the monic quadratic over the fraction field transfers to `ℤ_[p]` (Gauss),
where it means `b₀ = c₁·c₂`, `b₁ = c₁ + c₂`; then `v(c₁) + v(c₂) = H`, WLOG
`v(c₁) ≤ v(c₂)`, so `2·v(c₁) ≤ H` gives `v(c₁) ≤ (H−1)/2` and `v(c₂) ≥ (H+1)/2 > v(c₁)`
(`H` odd); the ultrametric pins `v(b₁) = v(c₁) ≤ (H−1)/2 < (H+1)/2`, contradicting
`p^{(H+1)/2} ∣ b₁`. (`b₁ = 0` is impossible: `c₂ = −c₁` would force `2·v(c₁) = H`, even.) -/
theorem leafRam_master_irreducible {H : ℕ} (hodd : Odd H) {b₀ b₁ u : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ H * u) (hu : PadicInt.toZMod u ≠ 0)
    (hb₁ : (p : ℤ_[p]) ^ ((H + 1) / 2) ∣ b₁) :
    Irreducible ((X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p])) := by
  have hH2 : H % 2 = 1 := Nat.odd_iff.mp hodd
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hu0 : u ≠ 0 := fun h0 => hu (by rw [h0, map_zero])
  have hvu : u.valuation = 0 := valuation_eq_zero_of_toZMod_ne p hu
  have hb₀ne : b₀ ≠ 0 := by
    rw [hb₀]
    exact mul_ne_zero (pow_ne_zero _ hpz) hu0
  have hval0 : b₀.valuation = H := by
    rw [hb₀, PadicInt.valuation_p_pow_mul H u hu0, hvu]
    omega
  have hm : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).Monic := by monicity!
  have hd2 : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hc0 : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).coeff 0 = b₀ := by simp
  have hc1 : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).coeff 1 = b₁ := by simp
  have hirr : Irreducible (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]) := by
    by_contra hred
    obtain ⟨c₁, c₂, hmul, hadd⟩ := (hm.not_irreducible_iff_exists_add_mul_eq_coeff hd2).mp hred
    rw [hc0] at hmul
    rw [hc1] at hadd
    -- both roots are nonzero and their valuations sum to H
    have hc1ne : c₁ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hmul
      exact hb₀ne hmul
    have hc2ne : c₂ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hmul
      exact hb₀ne hmul
    have hsum : c₁.valuation + c₂.valuation = H := by
      rw [← PadicInt.valuation_mul hc1ne hc2ne, ← hmul, hval0]
    -- b₁ = c₁ + c₂ ≠ 0 (else 2·v(c₁) = H — parity)
    have hne : c₁ + c₂ ≠ 0 := by
      intro hz
      have h2 : c₂ = -c₁ := eq_neg_of_add_eq_zero_right hz
      rw [h2, QpType.valuation_neg] at hsum
      omega
    -- v(b₁) ≥ (H+1)/2 from the divisibility
    have hv1 : (H + 1) / 2 ≤ (c₁ + c₂).valuation := by
      have hna : b₁ ≠ 0 := by
        rw [hadd]
        exact hne
      have hm2 := (PadicInt.mem_span_pow_iff_le_valuation b₁ hna ((H + 1) / 2)).mp
        (Ideal.mem_span_singleton.mpr hb₁)
      rwa [hadd] at hm2
    -- the symmetric core: the smaller-valuation root pins v(c₁ + c₂) ≤ (H−1)/2
    have key : ∀ a b : ℤ_[p], a ≠ 0 → a + b ≠ 0 →
        a.valuation + b.valuation = H → a.valuation ≤ b.valuation →
        (H + 1) / 2 ≤ (a + b).valuation → False := by
      intro a b ha hab hs hle hv
      -- a = (a + b) + (−b): min(v(a+b), v(b)) ≤ v(a) ≤ (H−1)/2, but both arms are ≥ (H+1)/2
      have h' : a = (a + b) + (-b) := by ring
      have hmin : min (a + b).valuation (-b).valuation ≤ a.valuation := by
        have hh := PadicInt.le_valuation_add (x := a + b) (y := -b) (by rw [← h']; exact ha)
        rwa [← h'] at hh
      rw [QpType.valuation_neg] at hmin
      omega
    rcases le_total c₁.valuation c₂.valuation with hle | hle
    · exact key c₁ c₂ hc1ne hne hsum hle hv1
    · exact key c₂ c₁ hc2ne (by rwa [add_comm]) (by omega) hle
        (by rw [add_comm c₂ c₁]; exact hv1)
  exact (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr

/-- **The (R) ram master, `(e, f)`-forcing leg (blueprint §1.1 (R)), all odd `H`.** For
`g = y² + b₁y + b₀` with `b₀ = p^H·u` (`ū ≠ 0`), `p^{(H+1)/2} ∣ b₁`, `H` odd, EVERY
local-factor bundle `D : LocalFactorData p g` has `(e, f) = (2, 1)`.

Route (the `QpTypeH3.ef_of_wildH3` parity argument, `3` replaced by odd `H`): the
fundamental identity `e·f = [L:ℚ_p] = 2` leaves `e ∈ {1, 2}`; `e = 1` is refuted by
PARITY. With `algebraMap p = u_p·ϖ` (`e = 1`), the descended root `y = u_y·ϖᵏ` of
`y² = −(b₀ + b₁·y)` gives ϖ-order exactly `H` on `b₀`, `≥ (H+1)/2 + k` on `b₁·y`, and
exactly `2k` on `y²`: for `2k < H` the RHS is divisible by `ϖ^{2k+1}` but the LHS is not
(`QpTypeH3.not_pow_succ_dvd_unit_mul_pow`); for `2k > H` (forced by parity from `2k ≥ H`)
the RHS gives `ϖ^{H+1} ∣ (unit)·ϖ^H` — likewise impossible. Pure divisibility in the DVR.

**Honest scope**: the bundle slot `D` is exactly the existence content `om_leaf_faithful`
carries (mathlib at the pin cannot construct a bundle for a wild quadratic); this theorem
GUARDS the payload of any carried bundle. -/
theorem leafRam_master_forced {H : ℕ} (hodd : Odd H) {b₀ b₁ u : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ H * u) (hu : PadicInt.toZMod u ≠ 0)
    (hb₁ : (p : ℤ_[p]) ^ ((H + 1) / 2) ∣ b₁)
    (D : QpType.LocalFactorData p (X ^ 2 + C b₁ * X + C b₀)) :
    QpType.eOf p D = 2 ∧ QpType.fOf p D = 1 := by
  have hH2 : H % 2 = 1 := Nat.odd_iff.mp hodd
  letI := D.fieldL
  letI := D.algQL
  letI := D.algZL
  letI := D.towerZQL
  letI := D.crO
  letI := D.domO
  letI := D.dvrO
  letI := D.algZO
  letI := D.algOL
  letI := D.towerZOL
  letI := D.intClosure
  letI := D.liesOver
  have hg : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).Monic := by monicity!
  have hgdeg : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  -- the instance stack for the fundamental identity
  haveI hFD : FiniteDimensional ℚ_[p] D.L :=
    FiniteDimensional.of_finrank_pos (by rw [D.finrank_eq, hgdeg]; omega)
  haveI : IsFractionRing D.O D.L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] D.L D.O
  haveI : Module.Finite ℤ_[p] D.O := IsIntegralClosure.finite ℤ_[p] ℚ_[p] D.L D.O
  -- the root of g in L descends to O
  obtain ⟨x, hxroot, -⟩ := D.hasRoot
  rw [Polynomial.aeval_map_algebraMap] at hxroot
  have hxint : IsIntegral ℤ_[p] x := ⟨_, hg, by rwa [Polynomial.aeval_def] at hxroot⟩
  obtain ⟨y, hy⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := D.O) (R := ℤ_[p]) (B := D.L)).mp hxint
  have hyroot : Polynomial.aeval y (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]) = 0 := by
    apply IsIntegralClosure.algebraMap_injective D.O ℤ_[p] D.L
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hy]
    exact hxroot
  have hyq : y ^ 2 + algebraMap ℤ_[p] D.O b₁ * y + algebraMap ℤ_[p] D.O b₀ = 0 := by
    simpa [map_add, map_mul, map_pow] using hyroot
  -- injectivity of ℤ_[p] → O
  have hinjL : Function.Injective (algebraMap ℤ_[p] D.L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] D.L]
    exact (algebraMap ℚ_[p] D.L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have hinj : Function.Injective (algebraMap ℤ_[p] D.O) := by
    intro a b hab
    apply hinjL
    rw [IsScalarTower.algebraMap_eq ℤ_[p] D.O D.L, RingHom.comp_apply, RingHom.comp_apply, hab]
  have hfp0 : algebraMap ℤ_[p] D.O (p : ℤ_[p]) ≠ 0 := by
    intro h
    exact (PadicInt.prime_p (p := p)).ne_zero (hinj (by rw [h, map_zero]))
  -- coefficient data: b₀ = p^H·u (u a UNIT), b₁ = p^{(H+1)/2}·b
  have hu0 : u ≠ 0 := fun h0 => hu (by rw [h0, map_zero])
  have hUu : IsUnit u := isUnit_of_toZMod_ne p hu
  obtain ⟨b, hb⟩ := hb₁
  have hb₀ne : b₀ ≠ 0 := by
    rw [hb₀]
    exact mul_ne_zero (pow_ne_zero _ (by
      exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero : (p : ℤ_[p]) ≠ 0)) hu0
  -- the DVR uniformizer and the decomposition of p
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.O
  obtain ⟨E, up, hpE⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfp0 hϖ
  -- e = E: map(p·ℤ_p) = m_O^E by the decomposition, ramificationIdx = E by spec
  have hassoc : Associated (algebraMap ℤ_[p] D.O (p : ℤ_[p])) (ϖ ^ E) :=
    Associated.symm ⟨up, by rw [mul_comm (ϖ ^ E) (up : D.O)]; exact hpE.symm⟩
  have hspan : Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p])
      = maximalIdeal D.O ^ E := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hgt : ¬ Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p])
      ≤ maximalIdeal D.O ^ (E + 1) := by
    rw [hspan, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
    intro hdvd
    have hle := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hdvd
    rw [hϖ.addVal_pow, hϖ.addVal_pow] at hle
    have : E + 1 ≤ E := by exact_mod_cast hle
    omega
  have he_val : QpType.eOf p D = E := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = E
    exact Ideal.ramificationIdx_spec (le_of_eq hspan) hgt
  -- the fundamental identity e·f = [L:ℚ_p] = 2
  have hbot : maximalIdeal ℤ_[p] ≠ ⊥ := by
    intro hbb
    have hpmem : (p : ℤ_[p]) ∈ (⊥ : Ideal ℤ_[p]) := by
      rw [← hbb, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    exact (PadicInt.prime_p (p := p)).ne_zero (Ideal.mem_bot.mp hpmem)
  have hef : QpType.eOf p D * QpType.fOf p D = 2 := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) *
      Ideal.inertiaDeg (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = 2
    rw [Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := D.O) (K := ℚ_[p]) (L := D.L)
      hbot, D.finrank_eq, hgdeg]
  -- y ≠ 0, decomposed as u_y·ϖᵏ
  have hy0 : y ≠ 0 := by
    intro h0y
    rw [h0y] at hyq
    have hz : algebraMap ℤ_[p] D.O b₀ = 0 := by simpa using hyq
    exact hb₀ne (hinj (by rw [hz, map_zero]))
  obtain ⟨k, uy, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  -- THE PARITY REFUTATION of E = 1 (general odd H)
  have hEne1 : E ≠ 1 := by
    intro hE1
    rw [hE1, pow_one] at hpE
    -- B₀ = c₀·ϖ^H with c₀ a unit
    set c₀ : D.O := algebraMap ℤ_[p] D.O u * (up : D.O) ^ H with hc₀def
    have hc₀ : IsUnit c₀ := (hUu.map (algebraMap ℤ_[p] D.O)).mul (up.isUnit.pow H)
    have hb₀O : algebraMap ℤ_[p] D.O b₀ = algebraMap ℤ_[p] D.O ((p : ℤ_[p]) ^ H * u) :=
      congrArg (algebraMap ℤ_[p] D.O) hb₀
    have hA0 : algebraMap ℤ_[p] D.O b₀ = c₀ * ϖ ^ H := by
      rw [hb₀O, map_mul, map_pow, hpE, hc₀def]
      ring
    have hb₁O : algebraMap ℤ_[p] D.O b₁
        = algebraMap ℤ_[p] D.O ((p : ℤ_[p]) ^ ((H + 1) / 2) * b) :=
      congrArg (algebraMap ℤ_[p] D.O) hb
    have hA1y : algebraMap ℤ_[p] D.O b₁ * y
        = (algebraMap ℤ_[p] D.O b * (up : D.O) ^ ((H + 1) / 2) * (uy : D.O))
          * ϖ ^ ((H + 1) / 2 + k) := by
      rw [hb₁O, map_mul, map_pow, hpE, hyk, pow_add]
      ring
    have hy2 : y ^ 2 = ((uy : D.O)) ^ 2 * ϖ ^ (2 * k) := by
      rw [hyk, mul_pow, ← pow_mul, mul_comm k 2]
    rcases Nat.lt_or_ge (2 * k) H with hk | hk
    · -- 2k < H: ϖ^{2k+1} divides B₀ (order H) and B₁y (order ≥ (H+1)/2 + k), hence y² (order 2k)
      have hdA0 : ϖ ^ (2 * k + 1) ∣ algebraMap ℤ_[p] D.O b₀ := by
        rw [hA0]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hdA1 : ϖ ^ (2 * k + 1) ∣ algebraMap ℤ_[p] D.O b₁ * y := by
        rw [hA1y]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hkey : y ^ 2 = -(algebraMap ℤ_[p] D.O b₀ + algebraMap ℤ_[p] D.O b₁ * y) := by
        linear_combination hyq
      have hdy2 : ϖ ^ (2 * k + 1) ∣ ((uy : D.O)) ^ 2 * ϖ ^ (2 * k) := by
        rw [← hy2, hkey]
        exact dvd_neg.mpr (dvd_add hdA0 hdA1)
      exact QpTypeH3.not_pow_succ_dvd_unit_mul_pow hϖ (uy.isUnit.pow 2) (2 * k) hdy2
    · -- 2k ≥ H, hence 2k ≥ H + 1 by parity: ϖ^{H+1} divides y² and B₁y, hence B₀ = c₀·ϖ^H
      have hdy2 : ϖ ^ (H + 1) ∣ y ^ 2 := by
        rw [hy2]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hdA1 : ϖ ^ (H + 1) ∣ algebraMap ℤ_[p] D.O b₁ * y := by
        rw [hA1y]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hkey : algebraMap ℤ_[p] D.O b₀
          = -(algebraMap ℤ_[p] D.O b₁ * y + y ^ 2) := by
        linear_combination hyq
      have hdA0 : ϖ ^ (H + 1) ∣ c₀ * ϖ ^ H := by
        rw [← hA0, hkey]
        exact dvd_neg.mpr (dvd_add hdA1 hdy2)
      exact QpTypeH3.not_pow_succ_dvd_unit_mul_pow hϖ hc₀ H hdA0
  -- conclude: E ∣ 2 and E ≠ 1 force E = 2, then f = 1
  have hE2 : E = 2 := by
    have hdvd : E ∣ 2 := ⟨QpType.fOf p D, by rw [← he_val]; exact hef.symm⟩
    rcases Nat.prime_two.eq_one_or_self_of_dvd E hdvd with h | h
    · exact absurd h hEne1
    · exact h
  have hff : 2 * QpType.fOf p D = 2 := by
    calc 2 * QpType.fOf p D = QpType.eOf p D * QpType.fOf p D := by rw [he_val, hE2]
      _ = 2 := hef
  exact ⟨he_val.trans hE2, by omega⟩

end RamMaster

/-! ## Block 4 — the INERT master (I): all `m ≥ 0` -/

section InertMaster

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The general-`m` rescale relation** (blueprint §1.1 (I)/(S) shared step):
`g(p^m·z) = p^{2m}·h(z)` for `g = y² + b₁y + b₀` with `b₀ = p^{2m}·w₀`, `b₁ = p^m·w₁` and
`h = z² + w₁z + w₀`. At `m = 0` this is the trivial rescale. -/
theorem leafInert_rescale (m : ℕ) {b₀ b₁ w₀ w₁ : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ (2 * m) * w₀) (hb₁ : b₁ = (p : ℤ_[p]) ^ m * w₁) :
    (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).comp (C ((p : ℤ_[p]) ^ m) * X + C 0)
      = C (((p : ℤ_[p]) ^ m) ^ 2) * (X ^ 2 + C w₁ * X + C w₀) := by
  rw [hb₀, hb₁]
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.C_comp, map_mul, map_pow, Polynomial.C_0]
  ring

/-- **The (I) inert master, irreducibility leg (blueprint §1.1 (I)), all `m ≥ 0`.**
`g = y² + b₁y + b₀` with `b₀ = p^{2m}·w₀`, `b₁ = p^m·w₁` and root-free residual pair
`(w̄₀, w̄₁) ∈ noRootPairs` is irreducible over ℚ_p: the rescaled `h = z² + w₁z + w₀` is
irreducible (`inert_irreducible_Qp`, root-free reduction) and irreducibility transfers
along the affine substitution `a = p^m`, `c = 0` (`irreducible_comp_linear_iff`). -/
theorem leafInert_master_irreducible (m : ℕ) {b₀ b₁ w₀ w₁ : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ (2 * m) * w₀) (hb₁ : b₁ = (p : ℤ_[p]) ^ m * w₁)
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenu.noRootPairs p) :
    Irreducible ((X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p])) := by
  have hrel := leafInert_rescale p m hb₀ hb₁
  have hhirr := inert_irreducible_Qp p hmem
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hpQ : (algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ m) ≠ 0 :=
    algebraMap_ne_zero p (pow_ne_zero _ hpz)
  have hrelQ : ((X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p])).comp
      (C ((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ m)) * X + C ((algebraMap ℤ_[p] ℚ_[p]) 0))
        = C (((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ m)) ^ 2)
            * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p]) := by
    have hmc := congrArg (Polynomial.map (algebraMap ℤ_[p] ℚ_[p])) hrel
    rw [Polynomial.map_comp] at hmc
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_zero, map_pow, map_zero] at hmc ⊢
    exact hmc
  have hiff := irreducible_comp_linear_iff ((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ m)) hpQ
    ((algebraMap ℤ_[p] ℚ_[p]) 0)
    ((X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p]))
  rw [hrelQ, irreducible_C_mul_iff (pow_ne_zero _ hpQ)] at hiff
  exact hiff.mp hhirr

/-- **The (I) inert master, `(e, f)`-forcing leg (blueprint §1.1 (I)), all `m ≥ 0`.** For
`g = y² + b₁y + b₀` with `b₀ = p^{2m}·w₀`, `b₁ = p^m·w₁` and root-free residual pair, EVERY
local-factor bundle `D : LocalFactorData p g` has `(e, f) = (1, 2)`: pull the bundle back to
the rescaled root-free-residual quadratic `h = z² + w₁z + w₀` via `compData` at the inverted
affine data (`a' = p^m`, `c' = 0` — the `chainGate_ef_forced`/`chainInert_ef_forced`
pattern), where `ef_of_inert_quadratic` forces `(1, 2)`; `efOf_compData` transports back. -/
theorem leafInert_master_forced (m : ℕ) {b₀ b₁ w₀ w₁ : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ (2 * m) * w₀) (hb₁ : b₁ = (p : ℤ_[p]) ^ m * w₁)
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenu.noRootPairs p)
    (D : QpType.LocalFactorData p (X ^ 2 + C b₁ * X + C b₀)) :
    QpType.eOf p D = 1 ∧ QpType.fOf p D = 2 := by
  have hrel := leafInert_rescale p m hb₀ hb₁
  set ρ : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] with hρ
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hpQ : ρ ((p : ℤ_[p]) ^ m) ≠ 0 := by
    intro h0
    have hpm : ((p : ℤ_[p]) ^ m) = 0 :=
      IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [← hρ, h0, map_zero])
    exact pow_ne_zero m hpz hpm
  have hrelQ : ((X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map ρ).comp
      (C (ρ ((p : ℤ_[p]) ^ m)) * X + C (ρ 0))
        = C ((ρ ((p : ℤ_[p]) ^ m)) ^ 2)
            * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map ρ := by
    have hmc := congrArg (Polynomial.map ρ) hrel
    rw [Polynomial.map_comp] at hmc
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_zero, map_pow, map_zero] at hmc ⊢
    exact hmc
  set a' : ℚ_[p] := ρ ((p : ℤ_[p]) ^ m) with ha'
  set c' : ℚ_[p] := ρ 0 with hc'
  have hqcomp : (C a' * X + C c').comp (C a'⁻¹ * X + C (-(c' / a')) : ℚ_[p][X]) = X := by
    rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      Polynomial.C_comp]
    rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hpQ, Polynomial.C_1, one_mul,
      ← Polynomial.C_mul, add_assoc, ← Polynomial.C_add]
    have hz : a' * -(c' / a') + c' = 0 := by
      field_simp
      ring
    rw [hz, Polynomial.C_0, add_zero]
  have hhQcomp : ((X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map ρ).comp
      (C a'⁻¹ * X + C (-(c' / a')))
        = C ((a' ^ 2)⁻¹) * (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map ρ := by
    have hheq : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map ρ
        = C ((a' ^ 2)⁻¹)
            * ((X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).map ρ).comp (C a' * X + C c') := by
      rw [hrelQ, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (pow_ne_zero _ hpQ),
        Polynomial.C_1, one_mul]
    rw [hheq, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc, hqcomp,
      Polynomial.comp_X]
  have hhdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hgdeg : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hdeg2 : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree
      = (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).natDegree := by
    rw [hhdeg, hgdeg]
  have hef12 := ef_of_inert_quadratic p hmem
    (compData p a'⁻¹ (-(c' / a')) ((a' ^ 2)⁻¹) (inv_ne_zero hpQ) hdeg2 hhQcomp D)
  have hkey := efOf_compData p a'⁻¹ (-(c' / a')) ((a' ^ 2)⁻¹) (inv_ne_zero hpQ)
    hdeg2 hhQcomp D
  have hpair : QpType.efOf p D = (1, 2) := by
    rw [← hkey]
    unfold QpType.efOf
    rw [hef12.1, hef12.2]
  unfold QpType.efOf at hpair
  rw [Prod.mk.injEq] at hpair
  exact hpair

end InertMaster

/-! ## Block 5 — the SPLIT master (S): all `k ≥ 0` (`b₀ = 0` admitted) -/

section SplitMaster

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The (S) split master (blueprint §1.1 (S)), all `k ≥ 0` — the axiom-free faithfulness
certificate.** `g = y² + b₁y + b₀` with `b₁ = p^k·w₁` (`w̄₁ ≠ 0`, so `v(b₁) = k` exact) and
`p^{2k+1} ∣ b₀` (`b₀ = 0` allowed) HAS a genuine ℚ_p-factorization certificate of type
`{(1,1),(1,1)}`: the rescaled `h = z² + w₁z + w₀` (`w₀ = b₀/p^{2k} ∈ (p)`) has split
separable reduction `z(z + w̄₁)` with two distinct simple roots; Hensel lifts them
(`split_two_roots`), each linear factor carries the proved degree-1 bundle
(`pairFactorization`), and the PROVED transport `translateFactorization` at `a = p^k`,
`c = 0` carries the certificate to `g` with the same `qpType` (`ChainMenu.splitType2`). -/
theorem leafSplit_master_hasType (k : ℕ) {b₀ b₁ w₁ : ℤ_[p]}
    (hb₁ : b₁ = (p : ℤ_[p]) ^ k * w₁) (hw₁ : PadicInt.toZMod w₁ ≠ 0)
    (hb₀ : (p : ℤ_[p]) ^ (2 * k + 1) ∣ b₀) :
    ∃ F : QpType.QpFactorization p (X ^ 2 + C b₁ * X + C b₀),
      QpType.qpType p F = ChainMenu.splitType2 := by
  obtain ⟨t, ht⟩ := hb₀
  set w₀ : ℤ_[p] := (p : ℤ_[p]) * t with hw₀def
  have hb₀' : b₀ = (p : ℤ_[p]) ^ (2 * k) * w₀ := by
    rw [ht, hw₀def]
    ring
  have hw₀mem : w₀ ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, hw₀def]
    exact dvd_mul_right _ _
  obtain ⟨r₁, r₂, hne, hfac⟩ := split_two_roots p hw₀mem hw₁
  have hrel := leafInert_rescale p k hb₀' hb₁
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hpne : ((p : ℤ_[p]) ^ k) ≠ 0 := pow_ne_zero _ hpz
  have hhdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hrel' : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).comp (C ((p : ℤ_[p]) ^ k) * X + C 0)
      = C (((p : ℤ_[p]) ^ k) ^ (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree)
        * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) := by
    rw [hhdeg]
    exact hrel
  refine ⟨translateFactorization p ((p : ℤ_[p]) ^ k) 0 hpne hrel'
    (pairFactorization p r₁ r₂ hfac), ?_⟩
  rw [qpType_translateFactorization p ((p : ℤ_[p]) ^ k) 0 hpne hrel'
    (pairFactorization p r₁ r₂ hfac)]
  exact qpType_pairFactorization p r₁ r₂ hfac

end SplitMaster

/-! ## Block 6 — the box-decode wrappers: `LeafPair` fibers → master conclusions -/

section LeafFiber

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The ram-leaf fiber wrapper**: a genuine monic quadratic whose box pair at frame
`(L₀, L₁)` (`leafNeed (ram H) = H + 1 ≤ L₀ ≤ L₁`) lies in the `LeafPair (ram H)` digit
fiber, with `H` odd (supplied by the menu's `leafOK`), is irreducible over ℚ_p and every
bundle carries `(e, f) = (2, 1)` — decode by `dvd_of_box_dvd` at heights `H` (with
`box_digit_toZMod` for the exactness digit) and `(H+1)/2 ≤ L₁`, then the (R) master. -/
theorem leafFiber_ram_forced {H L₀ L₁ : ℕ} (hodd : Odd H)
    (hL₀ : ChainMenu.leafNeed (ChainMenu.ChainLeaf.ram H) ≤ L₀) (hL01 : L₀ ≤ L₁)
    {g : ℤ_[p][X]} (hg : g.Monic) (hdeg : g.natDegree = 2)
    (hfib : ChainMenu.LeafPair p (ChainMenu.ChainLeaf.ram H) L₀ L₁
      (PadicInt.toZModPow L₀ (g.coeff 0), PadicInt.toZModPow L₁ (g.coeff 1))) :
    Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))
      ∧ ∀ D : QpType.LocalFactorData p g, QpType.eOf p D = 2 ∧ QpType.fOf p D = 1 := by
  have hneed : H + 1 ≤ L₀ := hL₀
  simp only [ChainMenu.LeafPair] at hfib
  obtain ⟨⟨hd0, hdig⟩, hd1⟩ := hfib
  obtain ⟨u, hu⟩ := dvd_of_box_dvd p (show H ≤ L₀ by omega) hd0
  have hune : PadicInt.toZMod u ≠ 0 := by
    intro h0
    refine hdig ?_
    rw [hu, box_digit_toZMod p (show H + 1 ≤ L₀ by omega) u]
    exact h0
  have hb₁ : (p : ℤ_[p]) ^ ((H + 1) / 2) ∣ g.coeff 1 :=
    dvd_of_box_dvd p (show (H + 1) / 2 ≤ L₁ by omega) hd1
  have hgeq : g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := monic_quadratic_eq p hg hdeg
  constructor
  · rw [hgeq]
    exact leafRam_master_irreducible p hodd hu hune hb₁
  · rw [hgeq]
    exact fun D => leafRam_master_forced p hodd hu hune hb₁ D

/-- **The inert-leaf fiber wrapper**: a genuine monic quadratic whose box pair at frame
`(L₀, L₁)` (`leafNeed (inert m) = 2m + 1 ≤ L₀ ≤ L₁`) lies in the `LeafPair (inert m)` digit
fiber is irreducible over ℚ_p and every bundle carries `(e, f) = (1, 2)` — decode by
`dvd_of_box_dvd` at heights `2m ≤ L₀`, `m ≤ L₁` and the digit→residue bridge
`box_digit_toZMod` for the `noRootPairs` membership, then the (I) master. -/
theorem leafFiber_inert_forced {m L₀ L₁ : ℕ}
    (hL₀ : ChainMenu.leafNeed (ChainMenu.ChainLeaf.inert m) ≤ L₀) (hL01 : L₀ ≤ L₁)
    {g : ℤ_[p][X]} (hg : g.Monic) (hdeg : g.natDegree = 2)
    (hfib : ChainMenu.LeafPair p (ChainMenu.ChainLeaf.inert m) L₀ L₁
      (PadicInt.toZModPow L₀ (g.coeff 0), PadicInt.toZModPow L₁ (g.coeff 1))) :
    Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))
      ∧ ∀ D : QpType.LocalFactorData p g, QpType.eOf p D = 1 ∧ QpType.fOf p D = 2 := by
  have hneed : 2 * m + 1 ≤ L₀ := hL₀
  simp only [ChainMenu.LeafPair] at hfib
  obtain ⟨hd0, hd1, hmem⟩ := hfib
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p (show 2 * m ≤ L₀ by omega) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show m ≤ L₁ by omega) hd1
  have hdig0 : digit p L₀ (2 * m) (PadicInt.toZModPow L₀ (g.coeff 0))
      = PadicInt.toZMod w₀ := by
    rw [hw₀]
    exact box_digit_toZMod p (show 2 * m + 1 ≤ L₀ by omega) w₀
  have hdig1 : digit p L₁ m (PadicInt.toZModPow L₁ (g.coeff 1)) = PadicInt.toZMod w₁ := by
    rw [hw₁]
    exact box_digit_toZMod p (show m + 1 ≤ L₁ by omega) w₁
  rw [hdig0, hdig1] at hmem
  have hgeq : g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := monic_quadratic_eq p hg hdeg
  constructor
  · rw [hgeq]
    exact leafInert_master_irreducible p m hw₀ hw₁ hmem
  · rw [hgeq]
    exact fun D => leafInert_master_forced p m hw₀ hw₁ hmem D

/-- **The split-leaf fiber wrapper — axiom-free existence**: a genuine monic quadratic whose
box pair at frame `(L₀, L₁)` (`L₀ ≤ L₁`; the readability gate `2k + 1 ≤ L₀` is INSIDE
`LeafPair (split k)`) lies in the `LeafPair (split k)` digit fiber HAS a genuine
ℚ_p-factorization certificate of type `{(1,1),(1,1)}` — decode by `dvd_of_box_dvd` at
heights `2k + 1 ≤ L₀`, `k ≤ L₁` (with `not_dvd_of_box_digit_ne` for the exactness digit),
then the (S) master. This is the `om_leaf_faithful` conclusion ITSELF at this leaf, no
axiom. -/
theorem leafFiber_split_hasType {k L₀ L₁ : ℕ} (hL01 : L₀ ≤ L₁)
    {g : ℤ_[p][X]} (hg : g.Monic) (hdeg : g.natDegree = 2)
    (hfib : ChainMenu.LeafPair p (ChainMenu.ChainLeaf.split k) L₀ L₁
      (PadicInt.toZModPow L₀ (g.coeff 0), PadicInt.toZModPow L₁ (g.coeff 1))) :
    ∃ F : QpType.QpFactorization p g, QpType.qpType p F = ChainMenu.splitType2 := by
  simp only [ChainMenu.LeafPair] at hfib
  obtain ⟨hgate, hd0, hd1, hdig⟩ := hfib
  have hb₀ : (p : ℤ_[p]) ^ (2 * k + 1) ∣ g.coeff 0 :=
    dvd_of_box_dvd p (show 2 * k + 1 ≤ L₀ from hgate) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show k ≤ L₁ by omega) hd1
  have hw₁ne : PadicInt.toZMod w₁ ≠ 0 := by
    intro h0
    exact not_dvd_of_box_digit_ne p (show k + 1 ≤ L₁ by omega)
      (by rw [← hw₁]; exact hdig) ((toZMod_eq_zero_iff p w₁).mp h0)
  have hgeq : g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := monic_quadratic_eq p hg hdeg
  rw [hgeq]
  exact leafSplit_master_hasType p k hw₁ hw₁ne hb₀

end LeafFiber

/-! ## Block 7 — axiom census (this module declares NO axiom; everything must be core-only) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeLeafMasters.stepDecode_general
#print axioms LeanUrat.OM.QpTypeLeafMasters.isUnit_of_toZMod_ne
#print axioms LeanUrat.OM.QpTypeLeafMasters.valuation_eq_zero_of_toZMod_ne
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafRam_master_irreducible
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafRam_master_forced
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafInert_rescale
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafInert_master_irreducible
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafInert_master_forced
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafSplit_master_hasType
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafFiber_ram_forced
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafFiber_inert_forced
#print axioms LeanUrat.OM.QpTypeLeafMasters.leafFiber_split_hasType

end AxCheck

end LeanUrat.OM.QpTypeLeafMasters
