/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.QpTypeEisenstein
import LeanUrat.OM.QpTypeChain

/-!
# QpTypeChainLeaves — axiom-free anchors for the INERT and SPLIT depth-1 chain leaves

Closes guardian audit #5's named follow-up: the W5c machine anchors covered only the `ram`
chain leaf (`OM/QpTypeChain.lean`); the `inert`/`split` chain payloads were cite-trusted.
This module machine-guards BOTH remaining n = 2 chain payload types, end-to-end, no axiom:

* **Shared step decode** (`chainStep_decode`): leaf-generic depth-1 fiber decode — membership
  of a genuine monic quadratic in the `ChainCell [1] leaf` box fiber yields the genuine
  recentered monic quadratic `g` with `f(p·y + ĉp) = p²·g(y)` whose box at the child staircase
  frame `(N−2, N−1)` satisfies the leaf digit conditions (factored from the ram-leaf anchor's
  `chainGateFiber_decode`).
* **The digit→residue bridge** (`box_digit_toZMod`): the height-`k` box digit of `p^k·w` IS
  `PadicInt.toZMod w` — the missing decode step from `noRootPairs` digit membership to a
  genuine mod-`p` residual statement.
* **The INERT anchor** (`chainInertFiber_decode` → `chainInert_irreducible` +
  `chainInert_ef_forced`): the depth-1 inert-leaf fiber forces the twice-rescaled
  `h = z² + w₁z + w₀` to have ROOT-FREE (hence irreducible, hence separable) reduction mod `p`;
  `f` is then IRREDUCIBLE over ℚ_p (root-free ⟹ irreducible reduction ⟹
  `Monic.irreducible_of_irreducible_map` ⟹ Gauss), and EVERY `LocalFactorData` bundle on `f`
  carries `efOf = (1, 2)` — BOTH coordinates, via the master theorem `ef_of_inert_quadratic`:
  the fundamental identity `e·f = 2`
  (`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`) plus the residue leg `f ≠ 1`
  (a degree-1 residue extension hands the root-free residual quadratic a root — contradiction).
* **The SPLIT anchor** (`chainSplitFiber_decode` → `chainSplit_hasType` +
  `chainSplit_not_irreducible`): the depth-1 split-leaf fiber forces `h = z² + w₁z + w₀` with
  UNIT `w₁` and `w₀ ∈ (p)` — separable SPLIT reduction `z(z + w̄₁)` with two distinct simple
  roots; mathlib `hensels_lemma` (at the two residual roots `0` and `−w̄₁`) lifts them to
  `r₁ ≠ r₂` in `ℤ_[p]` with `h = (z−r₁)(z−r₂)`; each linear factor carries the PROVED degree-1
  bundle (`linearFactorData`, `efOf = (1,1)`), and the PROVED affine transport
  (`QpTypeChain.translateFactorization`) carries the certificate back to `f`. So
  `chainSplit_hasType` is the `om_leaf_faithful` conclusion ITSELF at this leaf — a genuine
  `QpFactorization` of type `{(1,1),(1,1)}`, axiom-free — strictly stronger than a mutation
  guard. `chainSplit_not_irreducible` is the refuter the singleton-type mutations hit.
* **Witnesses**: `chainInertPoly = X² + 12` and `chainSplitPoly = X² + 28` over `ℤ_[2]` at
  `N = 5` inhabit the two fibers (`chainInertFiber_nonempty` / `chainSplitFiber_nonempty`),
  and the two shapes are on the Wave-5 menu at their keyed types
  (`chainInert_mem_omMenu5` / `chainSplit_mem_omMenu5`) — so the mutation probes (evidence
  block below) genuinely fire.

Leaf module discipline: **no axiom, no `sorry`** — every declaration core-only (AxCheck at
bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.QpTypeChainLeaves

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu LeanUrat.OM.CellCard
open LeanUrat.OM.QpTypeChain

/-! ## Block 1 — the box-digit → mod-p residue bridge -/

section Bridge

variable (p : ℕ) [hp : Fact p.Prime]

/-- `toZMod` reads off any level-`L ≥ 1` box: the mod-`p` residue of `w` is the ℕ-cast of the
level-`L` representative. -/
theorem toZMod_eq_val_toZModPow {L : ℕ} (hL : 1 ≤ L) (w : ℤ_[p]) :
    PadicInt.toZMod w = (((PadicInt.toZModPow L w).val : ℕ) : ZMod p) := by
  have hval : (((PadicInt.toZModPow L w).val : ℕ) : ZMod (p ^ L)) = PadicInt.toZModPow L w :=
    ZMod.natCast_rightInverse _
  have hker : w - (((PadicInt.toZModPow L w).val : ℕ) : ℤ_[p])
      ∈ RingHom.ker (PadicInt.toZModPow (p := p) L) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hval, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨u, hu⟩ := hker
  have hw : w = (((PadicInt.toZModPow L w).val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ L * u := by
    linear_combination hu
  conv_lhs => rw [hw]
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast, ZMod.natCast_self,
    zero_pow (by omega : L ≠ 0), zero_mul, add_zero]

/-- **The digit→residue bridge**: the height-`k` box digit of `p^k·w` at any level
`L ≥ k + 1` IS the genuine mod-`p` residue `toZMod w`. -/
theorem box_digit_toZMod {L k : ℕ} (hk : k + 1 ≤ L) (w : ℤ_[p]) :
    digit p L k (PadicInt.toZModPow L ((p : ℤ_[p]) ^ k * w)) = PadicInt.toZMod w := by
  have hmap : PadicInt.toZModPow L ((p : ℤ_[p]) ^ k * w)
      = (p : ZMod (p ^ L)) ^ k * PadicInt.toZModPow L w := by
    rw [map_mul, map_pow, map_natCast]
  show (((PadicInt.toZModPow L ((p : ℤ_[p]) ^ k * w)).val / p ^ k : ℕ) : ZMod p)
      = PadicInt.toZMod w
  rw [hmap, val_pow_mul p (show k ≤ L by omega),
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k),
    natCast_mod_eq (dvd_pow_self p (show L - k ≠ 0 by omega)),
    ← toZMod_eq_val_toZModPow p (show 1 ≤ L by omega) w]

/-- The mod-`p` residue vanishes exactly on the divisibility locus. -/
theorem toZMod_eq_zero_iff (w : ℤ_[p]) : PadicInt.toZMod w = 0 ↔ (p : ℤ_[p]) ∣ w := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

end Bridge

/-! ## Block 2 — the shared depth-1 step decode and the composed rescale relation -/

section StepDecode

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The depth-1 chain step decode** (leaf-generic; factored from the ram-leaf anchor
`QpTypeChain.chainGateFiber_decode`): membership of a genuine monic quadratic in the
`ChainCell [1] leaf` box fiber at level `N ≥ 2` yields a genuine recentered monic quadratic
`g` with `f(p·y + ĉp) = p²·g(y)` whose BOX at the child staircase frame `(N − 2, N − 1)`
satisfies the leaf digit conditions. -/
theorem chainStep_decode {N : ℕ} (hN0 : 0 < N) (hN2 : 2 ≤ N) (leaf : ChainMenu.ChainLeaf)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] leaf (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    ∃ (c₀ : ℤ_[p]) (g : ℤ_[p][X]) (_ : g.Monic), g.natDegree = 2 ∧
      f.comp (C (p : ℤ_[p]) * X + C c₀) = C ((p : ℤ_[p]) ^ 2) * g ∧
      ChainMenu.LeafPair p leaf (N - 2 * 1) (N - 1)
        (PadicInt.toZModPow (N - 2 * 1) (g.coeff 0), PadicInt.toZModPow (N - 1) (g.coeff 1)) := by
  have hcoeff : ∀ i, ((PadicLift.toBox p 2 N hN0 f hf hdeg).1).coeff i
      = PadicInt.toZModPow N (f.coeff i) := by
    intro i
    rw [PadicLift.toBox_val, Polynomial.coeff_map]
  have hfib' : ChainMenu.ChainPair p [1] leaf N N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1)) := by
    have h := hfib
    unfold ChainMenu.ChainCell at h
    rwa [hcoeff 0, hcoeff 1] at h
  simp only [ChainMenu.ChainPair] at hfib'
  obtain ⟨c, hstep, hleaf⟩ := hfib'
  simp only [RecenterBox.StratumPair, RecenterBox.CoordCond] at hstep
  obtain ⟨⟨hd0, -⟩, ⟨hd1, -⟩⟩ := hstep
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p (show 2 * 1 ≤ N by omega) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show 1 ≤ N by omega) hd1
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
  have hrel : f.comp (C (p : ℤ_[p]) * X + C ((ĉ : ℤ_[p]) * p)) = C ((p : ℤ_[p]) ^ 2) * g := by
    conv_lhs => rw [monic_quadratic_eq p hf hdeg]
    rw [hw₀, hw₁, hgdef, hb₀, hb₁]
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_add, map_mul, map_pow, map_ofNat]
    push_cast
    ring
  have hdesc : ChainMenu.descendPair p 1 ĉ
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))
      = (PadicInt.toZModPow (N - 2 * 1) b₀, PadicInt.toZModPow (N - 1) b₁) := by
    unfold ChainMenu.descendPair
    refine Prod.ext ?_ ?_
    · show ((((PadicInt.toZModPow N (f.coeff 0)).val / p ^ (2 * 1) : ℕ))
          : ZMod (p ^ (N - 2 * 1)))
        + (ĉ : ZMod (p ^ (N - 2 * 1)))
            * (((PadicInt.toZModPow N (f.coeff 1)).val / p ^ 1 : ℕ) : ZMod (p ^ (N - 2 * 1)))
        + (ĉ : ZMod (p ^ (N - 2 * 1))) ^ 2 = PadicInt.toZModPow (N - 2 * 1) b₀
      rw [hw₀, hw₁, box_shift_cast p (show 2 * 1 ≤ N by omega) (le_refl _),
        box_shift_cast p (show 1 ≤ N by omega) (show N - 2 * 1 ≤ N - 1 by omega),
        hb₀, map_add, map_add, map_mul, map_pow, map_natCast]
    · show (((PadicInt.toZModPow N (f.coeff 1)).val / p ^ 1 : ℕ) : ZMod (p ^ (N - 1)))
        + 2 * (ĉ : ZMod (p ^ (N - 1))) = PadicInt.toZModPow (N - 1) b₁
      rw [hw₁, box_shift_cast p (show 1 ≤ N by omega) (le_refl _),
        hb₁, map_add, map_mul, map_natCast, map_ofNat]
  rw [hdesc] at hleaf
  rw [← hg0, ← hg1] at hleaf
  exact ⟨(ĉ : ℤ_[p]) * p, g, hg, hgdeg, hrel, hleaf⟩

/-- **The composed recenter–rescale relation**: the step recentering
`f(p·y + c₀) = p²·g(y)` composed with the leaf rescale `g(p·z) = p²·h(z)` (available whenever
`p² ∣ g₀` and `p ∣ g₁`) gives the single affine relation `f(p²·z + c₀) = (p²)²·h(z)` for
`h = z² + w₁z + w₀`. -/
theorem composite_rescale {f g : ℤ_[p][X]} (hg : g.Monic) (hgdeg : g.natDegree = 2)
    {c₀ w₀ w₁ : ℤ_[p]}
    (hrel : f.comp (C (p : ℤ_[p]) * X + C c₀) = C ((p : ℤ_[p]) ^ 2) * g)
    (h0 : g.coeff 0 = (p : ℤ_[p]) ^ 2 * w₀) (h1 : g.coeff 1 = (p : ℤ_[p]) ^ 1 * w₁) :
    f.comp (C ((p : ℤ_[p]) ^ 2) * X + C c₀)
      = C (((p : ℤ_[p]) ^ 2) ^ 2) * (X ^ 2 + C w₁ * X + C w₀) := by
  have hB : (C ((p : ℤ_[p]) ^ 2) * X + C c₀ : ℤ_[p][X])
      = (C (p : ℤ_[p]) * X + C c₀).comp (C (p : ℤ_[p]) * X) := by
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      map_pow]
    ring
  rw [hB, ← Polynomial.comp_assoc, hrel, Polynomial.mul_comp, Polynomial.C_comp]
  conv_lhs => rw [monic_quadratic_eq p hg hgdeg, h0, h1]
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.C_comp, map_mul, map_pow]
  ring

end StepDecode

/-! ## Block 3 — the two leaf decodes -/

section LeafDecode

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The inert-leaf decode**: the depth-1 `inert 1` chain fiber at level `N ≥ 5` yields the
composed affine relation `f(p²·z + c₀) = (p²)²·h(z)`, `h = z² + w₁z + w₀`, with ROOT-FREE
residual pair `(w̄₀, w̄₁) ∈ noRootPairs` — the genuine mod-`p` separable-irreducible condition,
decoded from the box digits. -/
theorem chainInertFiber_decode {N : ℕ} (hN0 : 0 < N) (hN5 : 5 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.inert 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    ∃ (c₀ w₀ w₁ : ℤ_[p]),
      f.comp (C ((p : ℤ_[p]) ^ 2) * X + C c₀)
        = C (((p : ℤ_[p]) ^ 2) ^ 2) * (X ^ 2 + C w₁ * X + C w₀) ∧
      (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenu.noRootPairs p := by
  obtain ⟨c₀, g, hg, hgdeg, hrel, hleaf⟩ :=
    chainStep_decode p hN0 (by omega) (ChainMenu.ChainLeaf.inert 1) hf hdeg hfib
  simp only [ChainMenu.LeafPair] at hleaf
  obtain ⟨hd0, hd1, hmem⟩ := hleaf
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p (show 2 * 1 ≤ N - 2 * 1 by omega) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show 1 ≤ N - 1 by omega) hd1
  have hdig0 : digit p (N - 2 * 1) (2 * 1)
      (PadicInt.toZModPow (N - 2 * 1) (g.coeff 0)) = PadicInt.toZMod w₀ := by
    rw [hw₀]
    exact box_digit_toZMod p (show 2 * 1 + 1 ≤ N - 2 * 1 by omega) w₀
  have hdig1 : digit p (N - 1) 1
      (PadicInt.toZModPow (N - 1) (g.coeff 1)) = PadicInt.toZMod w₁ := by
    rw [hw₁]
    exact box_digit_toZMod p (show 1 + 1 ≤ N - 1 by omega) w₁
  rw [hdig0, hdig1] at hmem
  exact ⟨c₀, w₀, w₁, composite_rescale p hg hgdeg hrel hw₀ hw₁, hmem⟩

/-- **The split-leaf decode**: the depth-1 `split 1` chain fiber at level `N ≥ 5` yields the
composed affine relation `f(p²·z + c₀) = (p²)²·h(z)`, `h = z² + w₁z + w₀`, with `w₀ ∈ (p)`
and UNIT `w₁` (`w̄₁ ≠ 0`) — the genuine two-distinct-simple-residual-roots condition. -/
theorem chainSplitFiber_decode {N : ℕ} (hN0 : 0 < N) (hN5 : 5 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.split 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    ∃ (c₀ w₀ w₁ : ℤ_[p]),
      f.comp (C ((p : ℤ_[p]) ^ 2) * X + C c₀)
        = C (((p : ℤ_[p]) ^ 2) ^ 2) * (X ^ 2 + C w₁ * X + C w₀) ∧
      w₀ ∈ maximalIdeal ℤ_[p] ∧ PadicInt.toZMod w₁ ≠ 0 := by
  obtain ⟨c₀, g, hg, hgdeg, hrel, hleaf⟩ :=
    chainStep_decode p hN0 (by omega) (ChainMenu.ChainLeaf.split 1) hf hdeg hfib
  simp only [ChainMenu.LeafPair] at hleaf
  obtain ⟨-, hd0, hd1, hdig⟩ := hleaf
  obtain ⟨t, ht⟩ := dvd_of_box_dvd p (show 2 * 1 + 1 ≤ N - 2 * 1 by omega) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show 1 ≤ N - 1 by omega) hd1
  refine ⟨c₀, (p : ℤ_[p]) * t, w₁, ?_, ?_, ?_⟩
  · refine composite_rescale p hg hgdeg hrel ?_ hw₁
    rw [ht]
    ring
  · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  · intro h0
    exact not_dvd_of_box_digit_ne p (show 1 + 1 ≤ N - 1 by omega)
      (by rw [← hw₁]; exact hdig) ((toZMod_eq_zero_iff p w₁).mp h0)

end LeafDecode

/-! ## Block 4 — the INERT anchor: irreducibility and the full `(e, f) = (1, 2)` payload -/

section InertAnchor

variable (p : ℕ) [hp : Fact p.Prime]

/-- The root-free residual pair makes the mod-`p` reduction of `z² + w₁z + w₀` IRREDUCIBLE
over `F_p`: a reducible monic quadratic splits as `(z + c₁)(z + c₂)` and exhibits the root
`−c₁`. -/
theorem residual_irreducible {w₀ w₁ : ℤ_[p]}
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenu.noRootPairs p) :
    Irreducible ((X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map (PadicInt.toZMod (p := p))) := by
  have hnr := (ChainMenu.mem_noRootPairs p).mp hmem
  have hmap : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map (PadicInt.toZMod (p := p))
      = X ^ 2 + C (PadicInt.toZMod w₁) * X + C (PadicInt.toZMod w₀) := by
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
  rw [hmap]
  have hm : (X ^ 2 + C (PadicInt.toZMod w₁) * X + C (PadicInt.toZMod w₀)
      : (ZMod p)[X]).Monic := by
    monicity!
  have hd2 : (X ^ 2 + C (PadicInt.toZMod w₁) * X + C (PadicInt.toZMod w₀)
      : (ZMod p)[X]).natDegree = 2 := by
    compute_degree!
  by_contra hni
  obtain ⟨c₁, c₂, hc0, hc1⟩ := (hm.not_irreducible_iff_exists_add_mul_eq_coeff hd2).mp hni
  have h0 : (X ^ 2 + C (PadicInt.toZMod w₁) * X + C (PadicInt.toZMod w₀)
      : (ZMod p)[X]).coeff 0 = PadicInt.toZMod w₀ := by
    simp
  have h1 : (X ^ 2 + C (PadicInt.toZMod w₁) * X + C (PadicInt.toZMod w₀)
      : (ZMod p)[X]).coeff 1 = PadicInt.toZMod w₁ := by
    simp
  rw [h0] at hc0
  rw [h1] at hc1
  refine hnr (-c₁) ?_
  show (-c₁) ^ 2 + PadicInt.toZMod w₁ * (-c₁) + PadicInt.toZMod w₀ = 0
  rw [hc0, hc1]
  ring

/-- **Inert master irreducibility**: root-free reduction ⟹ irreducible over ℚ_p
(irreducible reduction lifts along the monic `Monic.irreducible_of_irreducible_map`, then
Gauss's lemma transfers to the fraction field). -/
theorem inert_irreducible_Qp {w₀ w₁ : ℤ_[p]}
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenu.noRootPairs p) :
    Irreducible ((X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p])) := by
  have hm : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).Monic := by monicity!
  have hZ : Irreducible (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) :=
    hm.irreducible_of_irreducible_map (PadicInt.toZMod (p := p)) _
      (residual_irreducible p hmem)
  exact (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hZ

/-- **The unramified-quadratic `(e, f)` theorem (master form, axiom-free).** For
`h = z² + w₁z + w₀` over `ℤ_[p]` with ROOT-FREE mod-`p` residual pair, EVERY local-factor
bundle `D : LocalFactorData p h` has `(e, f) = (1, 2)`: the fundamental identity `e·f = 2`
(via `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` on the bundle's pinned integral
closure) plus the residue leg `f ≠ 1` — a degree-1 residue extension puts the residue `ȳ` of
the integral root in the image of `F_p`, handing the root-free residual quadratic a root. -/
theorem ef_of_inert_quadratic {w₀ w₁ : ℤ_[p]}
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenu.noRootPairs p)
    (D : QpType.LocalFactorData p (X ^ 2 + C w₁ * X + C w₀)) :
    QpType.eOf p D = 1 ∧ QpType.fOf p D = 2 := by
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
  have hg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).Monic := by monicity!
  have hgdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  haveI hFD : FiniteDimensional ℚ_[p] D.L :=
    FiniteDimensional.of_finrank_pos (by rw [D.finrank_eq, hgdeg]; omega)
  haveI : IsFractionRing D.O D.L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] D.L D.O
  haveI : Module.Finite ℤ_[p] D.O := IsIntegralClosure.finite ℤ_[p] ℚ_[p] D.L D.O
  -- the fundamental identity e·f = [L : ℚ_p] = 2
  have hbot : maximalIdeal ℤ_[p] ≠ ⊥ := by
    intro hb
    have hpmem : (p : ℤ_[p]) ∈ (⊥ : Ideal ℤ_[p]) := by
      rw [← hb, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    exact (PadicInt.prime_p (p := p)).ne_zero (Ideal.mem_bot.mp hpmem)
  have hef : QpType.eOf p D * QpType.fOf p D = 2 := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) *
      Ideal.inertiaDeg (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = 2
    rw [Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := D.O) (K := ℚ_[p]) (L := D.L)
      hbot, D.finrank_eq, hgdeg]
  -- the residue leg: f ≠ 1
  have hf1 : QpType.fOf p D ≠ 1 := by
    intro h1
    -- the root of h descends to the integral closure O
    obtain ⟨x, hxroot, -⟩ := D.hasRoot
    rw [Polynomial.aeval_map_algebraMap] at hxroot
    have hxint : IsIntegral ℤ_[p] x := ⟨_, hg, by rwa [Polynomial.aeval_def] at hxroot⟩
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := D.O) (R := ℤ_[p]) (B := D.L)).mp hxint
    have hyroot : Polynomial.aeval y (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) = 0 := by
      apply IsIntegralClosure.algebraMap_injective D.O ℤ_[p] D.L
      rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hy]
      exact hxroot
    have hyq : y ^ 2 + algebraMap ℤ_[p] D.O w₁ * y + algebraMap ℤ_[p] D.O w₀ = 0 := by
      simpa [map_add, map_mul, map_pow] using hyroot
    -- f = 1 ⟹ the residue extension is trivial ⟹ ȳ comes from ℤ_[p]
    haveI : Nontrivial (D.O ⧸ maximalIdeal D.O) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
    have hfin : Module.finrank (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (D.O ⧸ maximalIdeal D.O) = 1 := by
      rw [← Ideal.inertiaDeg_algebraMap]
      exact h1
    letI : Field (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) := Ideal.Quotient.field _
    have hbt : (⊥ : Subalgebra (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (D.O ⧸ maximalIdeal D.O)) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one hfin
    have hytop : Ideal.Quotient.mk (maximalIdeal D.O) y
        ∈ (⊥ : Subalgebra (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (D.O ⧸ maximalIdeal D.O)) := by
      rw [hbt]
      exact Algebra.mem_top
    rw [Algebra.mem_bot] at hytop
    obtain ⟨ā, hā⟩ := hytop
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ā
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hā
    have hzmem : y - algebraMap ℤ_[p] D.O a ∈ maximalIdeal D.O := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hā, sub_self]
    -- the residual quadratic value at a lands in m_O, hence in (p), hence w̄'s have root ā
    have hkey : algebraMap ℤ_[p] D.O (a ^ 2 + w₁ * a + w₀)
        = -((y - algebraMap ℤ_[p] D.O a)
            * ((y - algebraMap ℤ_[p] D.O a) + 2 * algebraMap ℤ_[p] D.O a
              + algebraMap ℤ_[p] D.O w₁)) := by
      rw [map_add, map_add, map_mul, map_pow]
      linear_combination hyq
    have hval : algebraMap ℤ_[p] D.O (a ^ 2 + w₁ * a + w₀) ∈ maximalIdeal D.O := by
      rw [hkey]
      exact neg_mem (Ideal.mul_mem_right _ _ hzmem)
    have hpull : a ^ 2 + w₁ * a + w₀ ∈ maximalIdeal ℤ_[p] := by
      rw [Ideal.LiesOver.over (P := maximalIdeal D.O) (p := maximalIdeal ℤ_[p]),
        Ideal.under_def, Ideal.mem_comap]
      exact hval
    have h0 : PadicInt.toZMod (a ^ 2 + w₁ * a + w₀) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      exact hpull
    have hnr := (ChainMenu.mem_noRootPairs p).mp hmem
    refine hnr (PadicInt.toZMod a) ?_
    show PadicInt.toZMod a ^ 2 + PadicInt.toZMod w₁ * PadicInt.toZMod a
      + PadicInt.toZMod w₀ = 0
    rw [← h0, map_add, map_add, map_mul, map_pow]
  -- conclude: e·f = 2 with f ≠ 1 forces (e, f) = (1, 2)
  have hfdvd : QpType.fOf p D ∣ 2 := Dvd.intro_left _ hef
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hfdvd with h | h
  · exact absurd h hf1
  · refine ⟨?_, h⟩
    rw [h] at hef
    omega

/-- **Inert anchor leg (i) — irreducibility**: the depth-1 inert-leaf chain fiber forces `f`
IRREDUCIBLE over ℚ_p, axiom-free (kills the split-type mutation at this leaf). -/
theorem chainInert_irreducible {N : ℕ} (hN0 : 0 < N) (hN5 : 5 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.inert 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  obtain ⟨c₀, w₀, w₁, hrel, hmem⟩ := chainInertFiber_decode p hN0 hN5 hf hdeg hfib
  have hhirr := inert_irreducible_Qp p hmem
  have hpQ : (algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ 2) ≠ 0 := by
    intro h0
    have hp2 : ((p : ℤ_[p]) ^ 2) = 0 :=
      IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [h0, map_zero])
    exact pow_ne_zero 2
      (by exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero : (p : ℤ_[p]) ≠ 0) hp2
  have hrelQ : (f.map (algebraMap ℤ_[p] ℚ_[p])).comp
      (C ((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ 2)) * X + C ((algebraMap ℤ_[p] ℚ_[p]) c₀))
        = C (((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ 2)) ^ 2)
            * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map (algebraMap ℤ_[p] ℚ_[p]) := by
    have hmc := congrArg (Polynomial.map (algebraMap ℤ_[p] ℚ_[p])) hrel
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_C, map_pow] at hmc
    exact hmc
  have hiff := irreducible_comp_linear_iff ((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ 2)) hpQ
    ((algebraMap ℤ_[p] ℚ_[p]) c₀) (f.map (algebraMap ℤ_[p] ℚ_[p]))
  rw [hrelQ, irreducible_C_mul_iff (pow_ne_zero _ hpQ)] at hiff
  exact hiff.mp hhirr

/-- **Inert anchor leg (ii) — the full (e,f) payload**: the depth-1 inert-leaf chain fiber
forces `efOf = (1, 2)` for EVERY `LocalFactorData` bundle on `f` — axiom-free (bundle
transport to the twice-rescaled root-free-residual quadratic + `ef_of_inert_quadratic`).
Type `{(1,2)}` pinned in BOTH coordinates: the fine-(e,f)-swap/ram mutation at this leaf is
machine-refutable. -/
theorem chainInert_ef_forced {N : ℕ} (hN0 : 0 < N) (hN5 : 5 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.inert 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg))
    (D : QpType.LocalFactorData p f) :
    QpType.efOf p D = (1, 2) := by
  obtain ⟨c₀, w₀, w₁, hrel, hmem⟩ := chainInertFiber_decode p hN0 hN5 hf hdeg hfib
  set ρ : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] with hρ
  have hpQ : ρ ((p : ℤ_[p]) ^ 2) ≠ 0 := by
    intro h0
    have hp2 : ((p : ℤ_[p]) ^ 2) = 0 :=
      IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [← hρ, h0, map_zero] )
    exact pow_ne_zero 2
      (by exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero : (p : ℤ_[p]) ≠ 0) hp2
  have hrelQ : (f.map ρ).comp (C (ρ ((p : ℤ_[p]) ^ 2)) * X + C (ρ c₀))
      = C ((ρ ((p : ℤ_[p]) ^ 2)) ^ 2) * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map ρ := by
    have hmc := congrArg (Polynomial.map ρ) hrel
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_C, map_pow] at hmc
    exact hmc
  set a' : ℚ_[p] := ρ ((p : ℤ_[p]) ^ 2) with ha'
  set c' : ℚ_[p] := ρ c₀ with hc'
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
      (C a'⁻¹ * X + C (-(c' / a'))) = C ((a' ^ 2)⁻¹) * f.map ρ := by
    have hheq : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).map ρ
        = C ((a' ^ 2)⁻¹) * (f.map ρ).comp (C a' * X + C c') := by
      rw [hrelQ, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (pow_ne_zero _ hpQ),
        Polynomial.C_1, one_mul]
    rw [hheq, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc, hqcomp,
      Polynomial.comp_X]
  have hhdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hdeg2 : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = f.natDegree := by
    rw [hhdeg, hdeg]
  have hef12 := ef_of_inert_quadratic p hmem
    (compData p a'⁻¹ (-(c' / a')) ((a' ^ 2)⁻¹) (inv_ne_zero hpQ) hdeg2 hhQcomp D)
  have hkey := efOf_compData p a'⁻¹ (-(c' / a')) ((a' ^ 2)⁻¹) (inv_ne_zero hpQ)
    hdeg2 hhQcomp D
  rw [← hkey]
  unfold QpType.efOf
  rw [hef12.1, hef12.2]

end InertAnchor

/-! ## Block 5 — the SPLIT anchor: Hensel roots, degree-1 bundles, and the axiom-free
faithfulness certificate -/

section SplitAnchor

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The Hensel split**: `h = z² + w₁z + w₀` with UNIT `w₁` (`w̄₁ ≠ 0`) and `w₀ ∈ (p)` has
two DISTINCT roots in `ℤ_[p]` (`r₁ ≡ 0`, `r₂ ≡ −w₁` mod `p`) and factors into the two monic
linears: mathlib `hensels_lemma` at the two simple residual roots, then Vieta. -/
theorem split_two_roots {w₀ w₁ : ℤ_[p]} (h0 : w₀ ∈ maximalIdeal ℤ_[p])
    (h1 : PadicInt.toZMod w₁ ≠ 0) :
    ∃ r₁ r₂ : ℤ_[p], r₁ ≠ r₂ ∧
      (X - C r₁) * (X - C r₂) = (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) := by
  -- norms: ‖w₀‖ < 1, ‖w₁‖ = 1
  have hw₀lt : ‖w₀‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h0
  have hw₁ne : ¬ (p : ℤ_[p]) ∣ w₁ := fun hdvd => h1 ((toZMod_eq_zero_iff p w₁).mpr hdvd)
  have hw₁norm : ‖w₁‖ = 1 := by
    rcases lt_or_eq_of_le (PadicInt.norm_le_one w₁) with hlt | he
    · exact absurd ((PadicInt.norm_lt_one_iff_dvd w₁).mp hlt) hw₁ne
    · exact he
  -- evaluations of F and its derivative at the two residual roots
  set F : ℤ_[p][X] := X ^ 2 + C w₁ * X + C w₀ with hF
  have hFd : Polynomial.derivative F = C 2 * X + C w₁ := by
    rw [hF]
    rw [Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.derivative_X_pow]
    norm_num
  have hF0 : Polynomial.aeval (0 : ℤ_[p]) F = w₀ := by
    rw [hF]
    simp
  have hFd0 : Polynomial.aeval (0 : ℤ_[p]) (Polynomial.derivative F) = w₁ := by
    rw [hFd]
    simp
  have hFm : Polynomial.aeval (-w₁) F = w₀ := by
    rw [hF]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hFdm : Polynomial.aeval (-w₁) (Polynomial.derivative F) = -w₁ := by
    rw [hFd]
    simp only [map_add, map_mul, map_ofNat, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  -- Hensel at a = 0: the root r₁ ≡ 0 (mod p)
  obtain ⟨r₁, hr₁root, hr₁close, -, -⟩ := hensels_lemma (F := F) (a := (0 : ℤ_[p]))
    (by rw [hF0, hFd0, hw₁norm]; simpa using hw₀lt)
  -- Hensel at a = -w₁: the root r₂ ≡ -w₁ (mod p)
  obtain ⟨r₂, hr₂root, hr₂close, -, -⟩ := hensels_lemma (F := F) (a := -w₁)
    (by rw [hFm, hFdm, norm_neg, hw₁norm]; simpa using hw₀lt)
  -- residues: r̄₁ = 0, r̄₂ = -w̄₁ ≠ 0, so r₁ ≠ r₂
  have hr₁res : PadicInt.toZMod r₁ = 0 := by
    rw [toZMod_eq_zero_iff, ← PadicInt.norm_lt_one_iff_dvd]
    have hc := hr₁close
    rw [hFd0, hw₁norm] at hc
    simpa using hc
  have hr₂res : PadicInt.toZMod r₂ = -PadicInt.toZMod w₁ := by
    have hmem : PadicInt.toZMod (r₂ + w₁) = 0 := by
      rw [toZMod_eq_zero_iff, ← PadicInt.norm_lt_one_iff_dvd]
      have hc := hr₂close
      rw [hFdm, norm_neg, hw₁norm] at hc
      simpa [sub_neg_eq_add] using hc
    rw [map_add] at hmem
    exact eq_neg_of_add_eq_zero_left hmem
  have hne : r₁ ≠ r₂ := by
    intro he
    apply h1
    have h' : PadicInt.toZMod r₂ = 0 := by
      rw [← he]
      exact hr₁res
    rw [hr₂res] at h'
    exact neg_eq_zero.mp h'
  -- Vieta: the two scalar root equations pin the coefficients
  have he₁ : r₁ ^ 2 + w₁ * r₁ + w₀ = 0 := by
    have h := hr₁root
    rw [hF] at h
    simpa [map_add, map_mul, map_pow] using h
  have he₂ : r₂ ^ 2 + w₁ * r₂ + w₀ = 0 := by
    have h := hr₂root
    rw [hF] at h
    simpa [map_add, map_mul, map_pow] using h
  have hsum : w₁ = -(r₁ + r₂) := by
    have hfac : (r₁ - r₂) * (r₁ + r₂ + w₁) = 0 := by
      linear_combination he₁ - he₂
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact absurd (sub_eq_zero.mp hc) hne
    · linear_combination hc
  have hprod : w₀ = r₁ * r₂ := by
    linear_combination he₁ - r₁ * hsum
  refine ⟨r₁, r₂, hne, ?_⟩
  rw [hF, hsum, hprod]
  simp only [map_neg, map_add, map_mul]
  ring

/-- **The degree-1 bundle** for a monic linear factor `X − C r`: `L = ℚ_[p]`, `O = ℤ_[p]`
(every instance field discharged from mathlib, as in `QpType.trivialFactorData`). -/
noncomputable def linearFactorData (r : ℤ_[p]) : QpType.LocalFactorData p (X - C r) where
  L := ℚ_[p]
  fieldL := inferInstance
  algQL := inferInstance
  algZL := inferInstance
  towerZQL := inferInstance
  finrank_eq := by
    rw [Polynomial.natDegree_X_sub_C, Module.finrank_self]
  hasRoot := ⟨algebraMap ℤ_[p] ℚ_[p] r, by simp, Subsingleton.elim _ _⟩
  O := ℤ_[p]
  crO := inferInstance
  domO := inferInstance
  dvrO := inferInstance
  algZO := inferInstance
  algOL := inferInstance
  towerZOL := inferInstance
  intClosure := inferInstance
  liesOver := ⟨by simp [Ideal.under]⟩

/-- The degree-1 bundle is unramified: `e = 1` (as for the witness bundle). -/
theorem eOf_linearFactorData (r : ℤ_[p]) : QpType.eOf p (linearFactorData p r) = 1 := by
  show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p]) = 1
  have hle : Ideal.map (algebraMap ℤ_[p] ℤ_[p]) (maximalIdeal ℤ_[p])
      ≤ (maximalIdeal ℤ_[p]) ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
  have hgt : ¬ Ideal.map (algebraMap ℤ_[p] ℤ_[p]) (maximalIdeal ℤ_[p])
      ≤ (maximalIdeal ℤ_[p]) ^ 2 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow]
    intro hle2
    have hmem : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ 2} :=
      hle2 (Ideal.mem_span_singleton_self _)
    have h2 := (PadicInt.mem_span_pow_iff_le_valuation _ (PadicInt.prime_p).ne_zero 2).mp hmem
    rw [PadicInt.valuation_p] at h2
    omega
  exact Ideal.ramificationIdx_spec hle hgt

/-- The degree-1 bundle has trivial residue extension: `f = 1`. -/
theorem fOf_linearFactorData (r : ℤ_[p]) : QpType.fOf p (linearFactorData p r) = 1 := by
  haveI hLO : (maximalIdeal ℤ_[p]).LiesOver (maximalIdeal ℤ_[p]) := ⟨by simp [Ideal.under]⟩
  haveI : Nontrivial (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  show Ideal.inertiaDeg (maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p]) = 1
  rw [Ideal.inertiaDeg_algebraMap]
  letI : Algebra (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
    Ideal.Quotient.algebraOfLiesOver (maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p])
  exact QpType.finrank_self_of_algebraMap_bijective _ _
    (QpType.quotientSelf_algebraMap_bijective _ _ (fun y => ⟨y, rfl⟩))

/-- The degree-1 bundle pair is `(1, 1)` — for EVERY root `r`. -/
theorem efOf_linearFactorData (r : ℤ_[p]) : QpType.efOf p (linearFactorData p r) = (1, 1) := by
  unfold QpType.efOf
  rw [eOf_linearFactorData, fOf_linearFactorData]

/-- Any member of the two-element linear factor list is a linear `X − C r`. -/
theorem mem_pair_linear (r₁ r₂ : ℤ_[p]) {g : ℤ_[p][X]}
    (hg : g ∈ [X - C r₁, X - C r₂]) : ∃ r : ℤ_[p], g = X - C r := by
  rcases List.mem_pair.mp hg with h | h
  · exact ⟨r₁, h⟩
  · exact ⟨r₂, h⟩

/-- **The split-pair factorization certificate**: factors `[X − r₁, X − r₂]`, product `h`,
each factor monic, ℚ_p-irreducible (degree 1), carrying its degree-1 bundle. -/
noncomputable def pairFactorization (r₁ r₂ : ℤ_[p]) {h : ℤ_[p][X]}
    (hfac : (X - C r₁) * (X - C r₂) = h) : QpType.QpFactorization p h where
  factors := [X - C r₁, X - C r₂]
  prod_eq := by
    rw [List.prod_cons, List.prod_singleton]
    exact hfac
  monic := by
    intro g hg
    obtain ⟨r, rfl⟩ := mem_pair_linear p r₁ r₂ hg
    exact Polynomial.monic_X_sub_C r
  irred := by
    intro g hg
    obtain ⟨r, rfl⟩ := mem_pair_linear p r₁ r₂ hg
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Polynomial.irreducible_X_sub_C _
  data := fun g hg =>
    castData p (mem_pair_linear p r₁ r₂ hg).choose_spec.symm
      (linearFactorData p (mem_pair_linear p r₁ r₂ hg).choose)

/-- Every bundle the pair certificate carries reads `(1, 1)`. -/
theorem efOf_pairFactorization_data (r₁ r₂ : ℤ_[p]) {h : ℤ_[p][X]}
    (hfac : (X - C r₁) * (X - C r₂) = h) {g : ℤ_[p][X]}
    (hg : g ∈ (pairFactorization p r₁ r₂ hfac).factors) :
    QpType.efOf p ((pairFactorization p r₁ r₂ hfac).data g hg) = (1, 1) := by
  show QpType.efOf p (castData p (mem_pair_linear p r₁ r₂ hg).choose_spec.symm
    (linearFactorData p (mem_pair_linear p r₁ r₂ hg).choose)) = (1, 1)
  rw [efOf_castData, efOf_linearFactorData]

/-- **The pair certificate has the SPLIT type** `{(1,1),(1,1)}`. -/
theorem qpType_pairFactorization (r₁ r₂ : ℤ_[p]) {h : ℤ_[p][X]}
    (hfac : (X - C r₁) * (X - C r₂) = h) :
    QpType.qpType p (pairFactorization p r₁ r₂ hfac) = ChainMenu.splitType2 := by
  have hm₁ : (X - C r₁ : ℤ_[p][X]) ∈ (pairFactorization p r₁ r₂ hfac).factors :=
    List.mem_cons_self ..
  have hm₂ : (X - C r₂ : ℤ_[p][X]) ∈ (pairFactorization p r₁ r₂ hfac).factors :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hq : QpType.qpType p (pairFactorization p r₁ r₂ hfac)
      = ⟨([QpType.efOf p ((pairFactorization p r₁ r₂ hfac).data _ hm₁),
           QpType.efOf p ((pairFactorization p r₁ r₂ hfac).data _ hm₂)] : List (ℕ × ℕ))⟩ := rfl
  rw [hq, efOf_pairFactorization_data p r₁ r₂ hfac hm₁,
    efOf_pairFactorization_data p r₁ r₂ hfac hm₂]
  rfl

/-- **The split-leaf faithfulness theorem — AXIOM-FREE existence.** Any genuine monic
quadratic in the depth-1 split-leaf chain fiber HAS a genuine ℚ_p-factorization certificate
of type `{(1,1),(1,1)}`: Hensel roots + degree-1 bundles + the PROVED affine transport
`QpTypeChain.translateFactorization`. This is the `om_leaf_faithful` conclusion ITSELF at
this leaf, with no axiom — strictly stronger than a mutation guard. -/
theorem chainSplit_hasType {N : ℕ} (hN0 : 0 < N) (hN5 : 5 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.split 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = ChainMenu.splitType2 := by
  obtain ⟨c₀, w₀, w₁, hrel, hw₀, hw₁⟩ := chainSplitFiber_decode p hN0 hN5 hf hdeg hfib
  obtain ⟨r₁, r₂, hne, hfac⟩ := split_two_roots p hw₀ hw₁
  have hpne : ((p : ℤ_[p]) ^ 2) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero)
  have hhdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hrel' : f.comp (C ((p : ℤ_[p]) ^ 2) * X + C c₀)
      = C (((p : ℤ_[p]) ^ 2) ^ (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree)
        * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) := by
    rw [hhdeg]
    exact hrel
  refine ⟨translateFactorization p ((p : ℤ_[p]) ^ 2) c₀ hpne hrel'
    (pairFactorization p r₁ r₂ hfac), ?_⟩
  rw [qpType_translateFactorization p ((p : ℤ_[p]) ^ 2) c₀ hpne hrel'
    (pairFactorization p r₁ r₂ hfac)]
  exact qpType_pairFactorization p r₁ r₂ hfac

/-- A two-factor certificate refutes ℚ_p-irreducibility (both mapped factors are
non-units). -/
theorem not_irreducible_of_two_factors {f : ℤ_[p][X]} (F : QpType.QpFactorization p f)
    (hlen : F.factors.length = 2) : ¬ Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  intro hirr
  obtain ⟨g₁, g₂, hfac⟩ := List.length_eq_two.mp hlen
  have h1 : ¬ IsUnit (g₁.map (algebraMap ℤ_[p] ℚ_[p])) :=
    (F.irred g₁ (by rw [hfac]; exact List.mem_cons_self ..)).not_isUnit
  have h2 : ¬ IsUnit (g₂.map (algebraMap ℤ_[p] ℚ_[p])) :=
    (F.irred g₂ (by
      rw [hfac]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).not_isUnit
  have hmap : f.map (algebraMap ℤ_[p] ℚ_[p])
      = g₁.map (algebraMap ℤ_[p] ℚ_[p]) * g₂.map (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [← F.prod_eq, hfac]
    simp [Polynomial.map_mul]
  rcases hirr.isUnit_or_isUnit hmap with hu | hu
  · exact h1 hu
  · exact h2 hu

/-- **Split anchor (the irreducibility refuter)**: the depth-1 split-leaf chain fiber makes
`f` REDUCIBLE over ℚ_p — any singleton-type mutation (`{(2,1)}` or `{(1,2)}`) at this leaf
forces a single irreducible factor and machine-derives `False` against this theorem. -/
theorem chainSplit_not_irreducible {N : ℕ} (hN0 : 0 < N) (hN5 : 5 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.split 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    ¬ Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  obtain ⟨c₀, w₀, w₁, hrel, hw₀, hw₁⟩ := chainSplitFiber_decode p hN0 hN5 hf hdeg hfib
  obtain ⟨r₁, r₂, hne, hfac⟩ := split_two_roots p hw₀ hw₁
  have hpne : ((p : ℤ_[p]) ^ 2) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero)
  have hhdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hrel' : f.comp (C ((p : ℤ_[p]) ^ 2) * X + C c₀)
      = C (((p : ℤ_[p]) ^ 2) ^ (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree)
        * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) := by
    rw [hhdeg]
    exact hrel
  refine not_irreducible_of_two_factors p
    (translateFactorization p ((p : ℤ_[p]) ^ 2) c₀ hpne hrel'
      (pairFactorization p r₁ r₂ hfac)) ?_
  show (List.map (affLift ((p : ℤ_[p]) ^ 2) c₀)
    (pairFactorization p r₁ r₂ hfac).factors).length = 2
  rw [List.length_map]
  rfl

end SplitAnchor

/-! ## Block 6 — the two witnesses (`p = 2`, `N = 5`) and the menu memberships

`X² + 12` recentered at `x = 2 + 2y` is `y² + 2y + 4`; rescaled at `y = 2z` it is
`z² + z + 1` — the unique root-free monic quadratic over `F_2` (the inert leaf). Its box at
`N = 5`: stratum digits `v(a₀) = 2` exact with digit `1 = c̃²`, `v(a₁) ≥ 1`; leaf digits
`v(b₀) = 2` exact (digit 1), `v(b₁) = 1` exact (digit 1), residual pair `(1,1) ∈ noRootPairs`.

`X² + 28` recentered the same way is `y² + 2y + 8`; rescaled, `z² + z + 2` with SPLIT
reduction `z(z + 1)` (the split leaf; genuinely `X² + 28 = (X − 2√{−7})(X + 2√{−7})` over
`ℚ_2`, `−7 ≡ 1 mod 8` a square). Its box at `N = 5`: descended pair `(0, 2)` in frame
`(3, 4)` — `v(b₀) ≥ 3` by vanishing, `v(b₁) = 1` exact. -/

section Witness

/-- The inert-leaf witness polynomial `X² + 12` over `ℤ_[2]`. -/
noncomputable def chainInertPoly : Polynomial ℤ_[2] := X ^ 2 + C 12

theorem chainInertPoly_monic : chainInertPoly.Monic := by
  unfold chainInertPoly
  monicity!

theorem chainInertPoly_natDegree : chainInertPoly.natDegree = 2 := by
  unfold chainInertPoly
  compute_degree!

/-- The box of the inert witness at level `5` is `X² + C 12` over `ZMod 32`. -/
theorem toBox_chainInertPoly :
    ((PadicLift.toBox 2 2 5 (by norm_num) chainInertPoly chainInertPoly_monic
      chainInertPoly_natDegree).1)
      = (X ^ 2 + C 12 : (ZMod (2 ^ 5))[X]) := by
  rw [PadicLift.toBox_val]
  unfold chainInertPoly
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_ofNat]

/-- **The inert-leaf chain fiber is INHABITED** (`p = 2`, `N = 5`): the anchor theorems and
the mutation probes at this leaf genuinely fire. -/
theorem chainInertFiber_nonempty :
    ChainMenu.ChainCell 2 [1] (ChainMenu.ChainLeaf.inert 1)
      (PadicLift.toBox 2 2 5 (by norm_num) chainInertPoly chainInertPoly_monic
        chainInertPoly_natDegree) := by
  unfold ChainMenu.ChainCell
  rw [toBox_chainInertPoly]
  have hc0 : (X ^ 2 + C 12 : (ZMod (2 ^ 5))[X]).coeff 0 = 12 := by
    simp
  have hc1 : (X ^ 2 + C 12 : (ZMod (2 ^ 5))[X]).coeff 1 = 0 := by
    simp
  rw [hc0, hc1]
  show ChainMenu.ChainPair 2 [1] (ChainMenu.ChainLeaf.inert 1) 5 5 ((12 : ZMod (2 ^ 5)), 0)
  refine ⟨1, ?_, ?_⟩
  · -- StratumPair 2 5 5 1 1 (12, 0)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · -- LeafPair (inert 1) in the frame (3, 4) on descendPair
    show ChainMenu.LeafPair 2 (ChainMenu.ChainLeaf.inert 1) (5 - 2 * 1) (5 - 1)
      (ChainMenu.descendPair 2 1 (((1 : (ZMod 2)ˣ) : ZMod 2)).val ((12 : ZMod (2 ^ 5)), 0))
    refine ⟨?_, ?_, ?_⟩
    · decide
    · decide
    · rw [ChainMenu.mem_noRootPairs]
      decide

/-- The split-leaf witness polynomial `X² + 28` over `ℤ_[2]`. -/
noncomputable def chainSplitPoly : Polynomial ℤ_[2] := X ^ 2 + C 28

theorem chainSplitPoly_monic : chainSplitPoly.Monic := by
  unfold chainSplitPoly
  monicity!

theorem chainSplitPoly_natDegree : chainSplitPoly.natDegree = 2 := by
  unfold chainSplitPoly
  compute_degree!

/-- The box of the split witness at level `5` is `X² + C 28` over `ZMod 32`. -/
theorem toBox_chainSplitPoly :
    ((PadicLift.toBox 2 2 5 (by norm_num) chainSplitPoly chainSplitPoly_monic
      chainSplitPoly_natDegree).1)
      = (X ^ 2 + C 28 : (ZMod (2 ^ 5))[X]) := by
  rw [PadicLift.toBox_val]
  unfold chainSplitPoly
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_ofNat]

/-- **The split-leaf chain fiber is INHABITED** (`p = 2`, `N = 5`). -/
theorem chainSplitFiber_nonempty :
    ChainMenu.ChainCell 2 [1] (ChainMenu.ChainLeaf.split 1)
      (PadicLift.toBox 2 2 5 (by norm_num) chainSplitPoly chainSplitPoly_monic
        chainSplitPoly_natDegree) := by
  unfold ChainMenu.ChainCell
  rw [toBox_chainSplitPoly]
  have hc0 : (X ^ 2 + C 28 : (ZMod (2 ^ 5))[X]).coeff 0 = 28 := by
    simp
  have hc1 : (X ^ 2 + C 28 : (ZMod (2 ^ 5))[X]).coeff 1 = 0 := by
    simp
  rw [hc0, hc1]
  show ChainMenu.ChainPair 2 [1] (ChainMenu.ChainLeaf.split 1) 5 5 ((28 : ZMod (2 ^ 5)), 0)
  refine ⟨1, ?_, ?_⟩
  · -- StratumPair 2 5 5 1 1 (28, 0)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · -- LeafPair (split 1) in the frame (3, 4) on descendPair
    show ChainMenu.LeafPair 2 (ChainMenu.ChainLeaf.split 1) (5 - 2 * 1) (5 - 1)
      (ChainMenu.descendPair 2 1 (((1 : (ZMod 2)ˣ) : ZMod 2)).val ((28 : ZMod (2 ^ 5)), 0))
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Witness

section Membership

/-- The depth-1 `inert 1` chain shape is on the Wave-5 menu at `n = 2`, `σ = {(1,2)}`,
window `D = K = 1`. -/
theorem chainInert_mem_omMenu5 :
    ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.inert 1)
      ∈ ChainMenu.omMenu5 2 1 1 ChainMenu.inertType2 := by
  rw [ChainMenu.omMenu5, Finset.mem_union]
  right
  rw [ChainMenu.mem_chainShapes]
  refine ⟨rfl, [1], ChainMenu.ChainLeaf.inert 1, ?_, by simp, ?_, rfl⟩
  · rw [ChainMenu.mem_msMenu]
    refine ⟨by simp, ?_⟩
    intro m hm
    rw [List.mem_singleton] at hm
    omega
  · rw [ChainMenu.chainLeaves,
      if_neg (fun hcon => absurd (congrArg FactorizationType.data hcon) (by decide)),
      if_pos rfl, Finset.mem_image]
    exact ⟨1, by rw [Finset.mem_Icc]; omega, rfl⟩

/-- The depth-1 `split 1` chain shape is on the Wave-5 menu at `n = 2`,
`σ = {(1,1),(1,1)}`, window `D = K = 1`. -/
theorem chainSplit_mem_omMenu5 :
    ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.split 1)
      ∈ ChainMenu.omMenu5 2 1 1 ChainMenu.splitType2 := by
  rw [ChainMenu.omMenu5, Finset.mem_union]
  right
  rw [ChainMenu.mem_chainShapes]
  refine ⟨rfl, [1], ChainMenu.ChainLeaf.split 1, ?_, by simp, ?_, rfl⟩
  · rw [ChainMenu.mem_msMenu]
    refine ⟨by simp, ?_⟩
    intro m hm
    rw [List.mem_singleton] at hm
    omega
  · rw [ChainMenu.chainLeaves,
      if_neg (fun hcon => absurd (congrArg FactorizationType.data hcon) (by decide)),
      if_neg (fun hcon => absurd (congrArg FactorizationType.data hcon) (by decide)),
      if_pos rfl, Finset.mem_image]
    exact ⟨1, by rw [Finset.mem_Icc]; omega, rfl⟩

end Membership

/-! ## Block 7 — mutation probe evidence (machine-checked 2026-07-22, scratch NOT committed)

**The four cross-leaf mutations at the depth-1 inert/split chain leaves** — the re-scoped
axiom's hypotheses VERBATIM (over `ChainMenu.omMenu5` with `fiberOf5`), conclusion replaced by
(A) the SPLIT type at the INERT leaf, (B) the RAM type `{(2,1)}` at the INERT leaf,
(C) the RAM type at the SPLIT leaf, (D) the INERT type `{(1,2)}` at the SPLIT leaf — were
compiled against this module and `OM/OmLeafFaithful.lean`, and `lake env lean` accepted the
following scratch with zero errors: `False` DERIVES from each mutated axiom + the inhabited
fibers (`chainInertFiber_nonempty` / `chainSplitFiber_nonempty`, lifted to `fiberOf5` in the
scratch) + THIS module's AXIOM-FREE anchors (`chainInert_irreducible` +
`not_irreducible_of_two_factors` for (A); `chainInert_ef_forced` +
`QpTypeEisenstein.qpType_singleton_forces` for (B); `chainSplit_not_irreducible` for (C) and
(D)). The real `om_leaf_faithful` appears in NONE of the four refutation cones; the positive
check `inert_axiom_coherent` (real axiom + the proved irreducibility coexist at the inert
witness) consumes exactly core + the real axiom. With `OM/QpTypeChain.lean`'s two ram-leaf
probes, ALL THREE n = 2 chain payload types are now pinned against all cross-type mutations.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeChainLeaves

namespace LeanUrat.OM.QpTypeChainLeavesScratch

open Polynomial
open LeanUrat LeanUrat.OM

theorem chainInertFiber5_nonempty :
    OmLeafFaithful.fiberOf5 2 2 5 (by norm_num)
      (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.inert 1))
      QpTypeChainLeaves.chainInertPoly QpTypeChainLeaves.chainInertPoly_monic
      QpTypeChainLeaves.chainInertPoly_natDegree := by
  rw [OmLeafFaithful.fiberOf5_chain 2 2 5 (by norm_num) (ChainMenu.headOrd_chainLit _ _) _ _ _,
    ChainMenu.decodeMs_chainLit, ChainMenu.decodeLeaf_chainLit]
  exact QpTypeChainLeaves.chainInertFiber_nonempty

theorem chainSplitFiber5_nonempty :
    OmLeafFaithful.fiberOf5 2 2 5 (by norm_num)
      (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.split 1))
      QpTypeChainLeaves.chainSplitPoly QpTypeChainLeaves.chainSplitPoly_monic
      QpTypeChainLeaves.chainSplitPoly_natDegree := by
  rw [OmLeafFaithful.fiberOf5_chain 2 2 5 (by norm_num) (ChainMenu.headOrd_chainLit _ _) _ _ _,
    ChainMenu.decodeMs_chainLit, ChainMenu.decodeLeaf_chainLit]
  exact QpTypeChainLeaves.chainSplitFiber_nonempty

axiom om_leaf_faithful_MUTATED_inertsplit (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

theorem mutation_inertsplit_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_inertsplit 2 2 5 (by norm_num)
    ChainMenu.inertType2 (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.inert 1)) 1 1
    QpTypeChainLeaves.chainInert_mem_omMenu5 QpTypeChainLeaves.chainInertPoly
    QpTypeChainLeaves.chainInertPoly_monic QpTypeChainLeaves.chainInertPoly_natDegree
    chainInertFiber5_nonempty
  have hirr : Irreducible (QpTypeChainLeaves.chainInertPoly.map (algebraMap ℤ_[2] ℚ_[2])) :=
    QpTypeChainLeaves.chainInert_irreducible 2 (by norm_num) (by norm_num)
      QpTypeChainLeaves.chainInertPoly_monic QpTypeChainLeaves.chainInertPoly_natDegree
      QpTypeChainLeaves.chainInertFiber_nonempty
  have hlen : F.factors.length = 2 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  exact QpTypeChainLeaves.not_irreducible_of_two_factors 2 F hlen hirr

axiom om_leaf_faithful_MUTATED_inertram (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

theorem mutation_inertram_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_inertram 2 2 5 (by norm_num)
    ChainMenu.inertType2 (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.inert 1)) 1 1
    QpTypeChainLeaves.chainInert_mem_omMenu5 QpTypeChainLeaves.chainInertPoly
    QpTypeChainLeaves.chainInertPoly_monic QpTypeChainLeaves.chainInertPoly_natDegree
    chainInertFiber5_nonempty
  obtain ⟨hmem, hef⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((2 : ℕ), (1 : ℕ)) hF
  have hef2 : QpType.efOf 2 (F.data QpTypeChainLeaves.chainInertPoly hmem) = (1, 2) :=
    QpTypeChainLeaves.chainInert_ef_forced 2 (by norm_num) (by norm_num)
      QpTypeChainLeaves.chainInertPoly_monic QpTypeChainLeaves.chainInertPoly_natDegree
      QpTypeChainLeaves.chainInertFiber_nonempty
      (F.data QpTypeChainLeaves.chainInertPoly hmem)
  rw [hef] at hef2
  exact absurd hef2 (by decide)

axiom om_leaf_faithful_MUTATED_splitram (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

theorem mutation_splitram_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_splitram 2 2 5 (by norm_num)
    ChainMenu.splitType2 (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.split 1)) 1 1
    QpTypeChainLeaves.chainSplit_mem_omMenu5 QpTypeChainLeaves.chainSplitPoly
    QpTypeChainLeaves.chainSplitPoly_monic QpTypeChainLeaves.chainSplitPoly_natDegree
    chainSplitFiber5_nonempty
  obtain ⟨hmem, -⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((2 : ℕ), (1 : ℕ)) hF
  exact QpTypeChainLeaves.chainSplit_not_irreducible 2 (by norm_num) (by norm_num)
    QpTypeChainLeaves.chainSplitPoly_monic QpTypeChainLeaves.chainSplitPoly_natDegree
    QpTypeChainLeaves.chainSplitFiber_nonempty
    (F.irred QpTypeChainLeaves.chainSplitPoly hmem)

axiom om_leaf_faithful_MUTATED_splitinert (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (2 : ℕ))}⟩ : FactorizationType)

theorem mutation_splitinert_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_splitinert 2 2 5 (by norm_num)
    ChainMenu.splitType2 (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.split 1)) 1 1
    QpTypeChainLeaves.chainSplit_mem_omMenu5 QpTypeChainLeaves.chainSplitPoly
    QpTypeChainLeaves.chainSplitPoly_monic QpTypeChainLeaves.chainSplitPoly_natDegree
    chainSplitFiber5_nonempty
  obtain ⟨hmem, -⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((1 : ℕ), (2 : ℕ)) hF
  exact QpTypeChainLeaves.chainSplit_not_irreducible 2 (by norm_num) (by norm_num)
    QpTypeChainLeaves.chainSplitPoly_monic QpTypeChainLeaves.chainSplitPoly_natDegree
    QpTypeChainLeaves.chainSplitFiber_nonempty
    (F.irred QpTypeChainLeaves.chainSplitPoly hmem)

theorem inert_axiom_coherent :
    ∃ (f0 : Polynomial ℤ_[2]) (F : QpType.QpFactorization 2 f0),
      QpType.qpType 2 F = ChainMenu.inertType2 ∧
      Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) := by
  obtain ⟨F, hF⟩ := OmLeafFaithful.om_leaf_faithful 2 2 5 (by norm_num) ChainMenu.inertType2
    (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.inert 1)) 1 1
    QpTypeChainLeaves.chainInert_mem_omMenu5 QpTypeChainLeaves.chainInertPoly
    QpTypeChainLeaves.chainInertPoly_monic QpTypeChainLeaves.chainInertPoly_natDegree
    chainInertFiber5_nonempty
  exact ⟨QpTypeChainLeaves.chainInertPoly, F, hF,
    QpTypeChainLeaves.chainInert_irreducible 2 (by norm_num) (by norm_num)
      QpTypeChainLeaves.chainInertPoly_monic QpTypeChainLeaves.chainInertPoly_natDegree
      QpTypeChainLeaves.chainInertFiber_nonempty⟩

end LeanUrat.OM.QpTypeChainLeavesScratch

#print axioms LeanUrat.OM.QpTypeChainLeavesScratch.mutation_inertsplit_refuted
#print axioms LeanUrat.OM.QpTypeChainLeavesScratch.mutation_inertram_refuted
#print axioms LeanUrat.OM.QpTypeChainLeavesScratch.mutation_splitram_refuted
#print axioms LeanUrat.OM.QpTypeChainLeavesScratch.mutation_splitinert_refuted
#print axioms LeanUrat.OM.QpTypeChainLeavesScratch.inert_axiom_coherent
```

`lake env lean` output on the scratch (2026-07-22): NO errors; exactly the five info lines

```
'LeanUrat.OM.QpTypeChainLeavesScratch.mutation_inertsplit_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeChainLeavesScratch.om_leaf_faithful_MUTATED_inertsplit]
'LeanUrat.OM.QpTypeChainLeavesScratch.mutation_inertram_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeChainLeavesScratch.om_leaf_faithful_MUTATED_inertram]
'LeanUrat.OM.QpTypeChainLeavesScratch.mutation_splitram_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeChainLeavesScratch.om_leaf_faithful_MUTATED_splitram]
'LeanUrat.OM.QpTypeChainLeavesScratch.mutation_splitinert_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeChainLeavesScratch.om_leaf_faithful_MUTATED_splitinert]
'LeanUrat.OM.QpTypeChainLeavesScratch.inert_axiom_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.OmLeafFaithful.om_leaf_faithful]
```

i.e. `False` follows from each MUTATED axiom + Lean core + PROVED theorems alone — the real
`om_leaf_faithful` appears in none of the four refutation cones. -/

/-! ## Block 8 — axiom census (this module declares NO axiom; everything must be core-only) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeChainLeaves.toZMod_eq_val_toZModPow
#print axioms LeanUrat.OM.QpTypeChainLeaves.box_digit_toZMod
#print axioms LeanUrat.OM.QpTypeChainLeaves.toZMod_eq_zero_iff
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainStep_decode
#print axioms LeanUrat.OM.QpTypeChainLeaves.composite_rescale
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainInertFiber_decode
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainSplitFiber_decode
#print axioms LeanUrat.OM.QpTypeChainLeaves.residual_irreducible
#print axioms LeanUrat.OM.QpTypeChainLeaves.inert_irreducible_Qp
#print axioms LeanUrat.OM.QpTypeChainLeaves.ef_of_inert_quadratic
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainInert_irreducible
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainInert_ef_forced
#print axioms LeanUrat.OM.QpTypeChainLeaves.split_two_roots
#print axioms LeanUrat.OM.QpTypeChainLeaves.linearFactorData
#print axioms LeanUrat.OM.QpTypeChainLeaves.eOf_linearFactorData
#print axioms LeanUrat.OM.QpTypeChainLeaves.fOf_linearFactorData
#print axioms LeanUrat.OM.QpTypeChainLeaves.efOf_linearFactorData
#print axioms LeanUrat.OM.QpTypeChainLeaves.mem_pair_linear
#print axioms LeanUrat.OM.QpTypeChainLeaves.pairFactorization
#print axioms LeanUrat.OM.QpTypeChainLeaves.efOf_pairFactorization_data
#print axioms LeanUrat.OM.QpTypeChainLeaves.qpType_pairFactorization
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainSplit_hasType
#print axioms LeanUrat.OM.QpTypeChainLeaves.not_irreducible_of_two_factors
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainSplit_not_irreducible
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainInertPoly
#print axioms LeanUrat.OM.QpTypeChainLeaves.toBox_chainInertPoly
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainInertFiber_nonempty
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainSplitPoly
#print axioms LeanUrat.OM.QpTypeChainLeaves.toBox_chainSplitPoly
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainSplitFiber_nonempty
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainInert_mem_omMenu5
#print axioms LeanUrat.OM.QpTypeChainLeaves.chainSplit_mem_omMenu5

end AxCheck

end LeanUrat.OM.QpTypeChainLeaves
