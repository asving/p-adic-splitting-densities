/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpTypeLeafMasters
import LeanUrat.OM.SeriesAssembly

/-!
# QpTypeChainAll — the chain unwind and the translate reduction
(Wild Wave 6c task B, `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §1.2, §1.3, §2-W6c-b;
blueprint Codex-verified)

Wave 6c task A (`OM/QpTypeLeafMasters.lean`) supplied the general-parameter leaf masters and
the tail-generic step decode. This module composes them into the ALL-DEPTH, ALL-TRANSLATE
faithfulness payloads for every chain fiber the full `n = 2` model counts:

**Section 1 (general prime `p`) — the unwind (§1.2).**
* `chainUnwind` — by induction on the slope list `ms` (entries ≥ 1, additive budget
  `2·Σms + leafNeed ≤ L₀ ≤ L₁`): a genuine monic quadratic whose box pair satisfies
  `ChainPair ms leaf L₀ L₁` decodes to a genuine monic quadratic `g` at the final frame
  `(L₀ − 2Σms, L₁ − Σms)` in the `LeafPair leaf` fiber, connected to `f` by the SINGLE
  composed affine relation `f.comp (C p^Σms·X + C c) = C p^{2Σms}·g` — one relation covers
  all downstream transports. Each step is `stepDecode_general`; steps compose by the affine
  composition identity `comp_affine_comp`.
* `chainFiber_split_hasType` — chain fiber ending in `split k`: an AXIOM-FREE genuine
  certificate `∃ F, qpType = {(1,1),(1,1)}` (leaf master + the proved
  `qpType_translate_rescale` UP the composed relation).
* `chainFiber_ram_forced` / `chainFiber_inert_forced` — chain fibers ending in `ram H`
  (`H` odd) / `inert m`: `f` is irreducible over ℚ_p and EVERY `LocalFactorData` bundle
  carries `(2,1)` / `(1,2)` — irreducibility ascends along the relation
  (`irreducible_of_affine_rel`), the forcing descends by BUNDLE PULLBACK at the inverted
  affine data (`ef_forced_of_affine_rel`, the landed `compData`/`chainGate_ef_forced`
  pattern).

**Section 2 (`p = M9.realP = 2`, `SeriesAssembly`-facing) — the translate reduction (§1.3).**
* `transBox_comp` — the translate commutation: the box pair of the genuine translate
  `f(x + ĉ)` IS `SeriesAssembly.transMap ĉ N` of the box pair of `f`; with
  `transChain_fiber_iff`, the `TransChain` fiber of `f` is DEFINITIONALLY the `ChainPair`
  fiber of `f(x + ĉ)` — translate coverage is DERIVED, not imported ((P4d) discipline: the
  paper states no translation form, so none enters any axiom).
* `transChainFiber_split_hasType` / `transChainFiber_ram_forced` /
  `transChainFiber_inert_forced` — the Section-1 conclusions at EVERY residue translate
  `ĉ`, transported back to `f` along the pure translation (`a = 1`).
* `sepSplitCell_hasType` / `sepInertCell_forced` — the order-0 separable cells
  (`SepSplitCell`/`SepInertCell` digit reads at `p = 2`): the (S0)/(I0) masters fire at
  `k = 0`/`m = 0` after the box-digit decode (`noRootPairs 2` membership at the odd–odd
  pair by `decide`).

Leaf module discipline: **no axiom, no `sorry`** — every declaration core-only (AxCheck at
bottom); any `om_leaf_faithful` appearance in a footprint is a FAILURE.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.QpTypeChainAll

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu LeanUrat.OM.CellCard
open LeanUrat.OM.QpTypeChain LeanUrat.OM.QpTypeChainLeaves LeanUrat.OM.QpTypeLeafMasters

/-! ## Block 1 — the affine composition identity (any commutative semiring) -/

section AffineComp

variable {R : Type*} [CommSemiring R]

/-- Composing two affine substitutions: `(A·x + B) ∘ (A'·y + B') = (A·A')·y + (A·B' + B)`. -/
theorem affine_comp_affine (A B A' B' : R) :
    ((C A * X + C B : R[X]).comp (C A' * X + C B'))
      = C (A * A') * X + C (A * B' + B) := by
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.C_mul, Polynomial.C_add]
  ring

/-- **The step-composition identity** (the unwind's engine): two nested affine substitutions
of `f` collapse to the single affine substitution at the composed data. -/
theorem comp_affine_comp (f : R[X]) (A B A' B' : R) :
    (f.comp (C A * X + C B)).comp (C A' * X + C B')
      = f.comp (C (A * A') * X + C (A * B' + B)) := by
  rw [Polynomial.comp_assoc, affine_comp_affine]

end AffineComp

/-! ## Block 2 — the genuine translate `f(x + c)` in monic-quadratic normal form -/

section Translate

variable (p : ℕ) [hp : Fact p.Prime]

/-- The genuine translate of a monic quadratic, in normal form:
`f(x + c) = x² + (a₁ + 2c)x + (a₀ + c·a₁ + c²)`. -/
theorem comp_translate_eq {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2) (c : ℤ_[p]) :
    f.comp (X + C c)
      = X ^ 2 + C (f.coeff 1 + 2 * c) * X + C (f.coeff 0 + c * f.coeff 1 + c ^ 2) := by
  conv_lhs => rw [monic_quadratic_eq p hf hdeg]
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.C_comp, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The genuine translate of a monic quadratic is monic. -/
theorem comp_translate_monic {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (c : ℤ_[p]) : (f.comp (X + C c)).Monic := by
  rw [comp_translate_eq p hf hdeg c]
  monicity!

/-- The genuine translate of a monic quadratic has degree 2. -/
theorem comp_translate_natDegree {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (c : ℤ_[p]) : (f.comp (X + C c)).natDegree = 2 := by
  rw [comp_translate_eq p hf hdeg c]
  compute_degree!

/-- Constant coefficient of the translate: `a₀ + c·a₁ + c²`. -/
theorem comp_translate_coeff_zero {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (c : ℤ_[p]) : (f.comp (X + C c)).coeff 0 = f.coeff 0 + c * f.coeff 1 + c ^ 2 := by
  rw [comp_translate_eq p hf hdeg c]
  generalize f.coeff 1 + 2 * c = b₁
  generalize f.coeff 0 + c * f.coeff 1 + c ^ 2 = b₀
  simp

/-- Linear coefficient of the translate: `a₁ + 2c`. -/
theorem comp_translate_coeff_one {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (c : ℤ_[p]) : (f.comp (X + C c)).coeff 1 = f.coeff 1 + 2 * c := by
  rw [comp_translate_eq p hf hdeg c]
  generalize f.coeff 1 + 2 * c = b₁
  generalize f.coeff 0 + c * f.coeff 1 + c ^ 2 = b₀
  simp

/-- **The pure-translation transport relation** (`a = 1`), in the exact
`qpType_translate_rescale` input form `f.comp (C a·X + C c) = C (a^{deg g})·g` with
`g = f(x + c)`. -/
theorem translate_rel (f : ℤ_[p][X]) (c : ℤ_[p]) :
    f.comp (C (1 : ℤ_[p]) * X + C c)
      = C ((1 : ℤ_[p]) ^ (f.comp (X + C c)).natDegree) * f.comp (X + C c) := by
  rw [one_pow, Polynomial.C_1, one_mul, one_mul]

end Translate

/-! ## Block 3 — the transport toolkit along a single affine relation
`f.comp (C a·X + C c) = C γ·g`: the mapped relation, irreducibility UP, `(e,f)`-forcing DOWN
(bundle pullback at the inverted affine data — the landed `compData`/`chainGate_ef_forced`
pattern at general `(a, c, γ)`). -/

section Transport

variable (p : ℕ) [hp : Fact p.Prime]

/-- The affine relation maps to ℚ_p coefficient-wise. -/
theorem map_affine_rel {f g : ℤ_[p][X]} {a c γ : ℤ_[p]}
    (hrel : f.comp (C a * X + C c) = C γ * g) :
    (f.map (algebraMap ℤ_[p] ℚ_[p])).comp
        (C ((algebraMap ℤ_[p] ℚ_[p]) a) * X + C ((algebraMap ℤ_[p] ℚ_[p]) c))
      = C ((algebraMap ℤ_[p] ℚ_[p]) γ) * g.map (algebraMap ℤ_[p] ℚ_[p]) := by
  have hmc := congrArg (Polynomial.map (algebraMap ℤ_[p] ℚ_[p])) hrel
  rw [Polynomial.map_comp] at hmc
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X] at hmc
  exact hmc

/-- **Irreducibility ascends** along the affine relation (`a ≠ 0`, `γ ≠ 0`): if the inner
`g` is irreducible over ℚ_p, so is `f` — the affine substitution is an algebra automorphism
of `ℚ_p[X]` and the constant `C γ` is a unit. -/
theorem irreducible_of_affine_rel {f g : ℤ_[p][X]} {a c γ : ℤ_[p]} (ha : a ≠ 0) (hγ : γ ≠ 0)
    (hrel : f.comp (C a * X + C c) = C γ * g)
    (hgirr : Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  have haQ : (algebraMap ℤ_[p] ℚ_[p]) a ≠ 0 := algebraMap_ne_zero p ha
  have hγQ : (algebraMap ℤ_[p] ℚ_[p]) γ ≠ 0 := algebraMap_ne_zero p hγ
  have hrelQ := map_affine_rel p hrel
  have hiff := irreducible_comp_linear_iff ((algebraMap ℤ_[p] ℚ_[p]) a) haQ
    ((algebraMap ℤ_[p] ℚ_[p]) c) (f.map (algebraMap ℤ_[p] ℚ_[p]))
  rw [hrelQ, irreducible_C_mul_iff hγQ] at hiff
  exact hiff.mp hgirr

/-- **`(e,f)`-forcing descends by bundle pullback** along the affine relation: an arbitrary
`LocalFactorData` bundle on `f` pulls back to a bundle on `g` via `compData` at the INVERTED
affine data `(a'⁻¹, −c'/a', γ'⁻¹)` with `L`, `O` literally unchanged (`efOf_compData` is
`rfl`), so an every-bundle `(e₀, f₀)` forcing on `g` forces the same pair on every bundle of
`f`. -/
theorem ef_forced_of_affine_rel {f g : ℤ_[p][X]} {a c γ : ℤ_[p]} (ha : a ≠ 0) (hγ : γ ≠ 0)
    (hdegeq : g.natDegree = f.natDegree)
    (hrel : f.comp (C a * X + C c) = C γ * g) {e₀ f₀ : ℕ}
    (hforce : ∀ Dg : QpType.LocalFactorData p g,
      QpType.eOf p Dg = e₀ ∧ QpType.fOf p Dg = f₀)
    (D : QpType.LocalFactorData p f) :
    QpType.eOf p D = e₀ ∧ QpType.fOf p D = f₀ := by
  set ρ : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] with hρ
  have haQ : ρ a ≠ 0 := algebraMap_ne_zero p ha
  have hγQ : ρ γ ≠ 0 := algebraMap_ne_zero p hγ
  have hrelQ : (f.map ρ).comp (C (ρ a) * X + C (ρ c)) = C (ρ γ) * g.map ρ :=
    map_affine_rel p hrel
  set a' : ℚ_[p] := ρ a with ha'
  set c' : ℚ_[p] := ρ c with hc'
  set γ' : ℚ_[p] := ρ γ with hγ'
  have hqcomp : (C a' * X + C c').comp (C a'⁻¹ * X + C (-(c' / a')) : ℚ_[p][X]) = X := by
    rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      Polynomial.C_comp]
    rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ haQ, Polynomial.C_1, one_mul,
      ← Polynomial.C_mul, add_assoc, ← Polynomial.C_add]
    have hz : a' * -(c' / a') + c' = 0 := by
      field_simp
      ring
    rw [hz, Polynomial.C_0, add_zero]
  have hgQcomp : (g.map ρ).comp (C a'⁻¹ * X + C (-(c' / a')))
      = C (γ'⁻¹) * f.map ρ := by
    have hgeq : g.map ρ = C (γ'⁻¹) * (f.map ρ).comp (C a' * X + C c') := by
      rw [hrelQ, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hγQ, Polynomial.C_1, one_mul]
    rw [hgeq, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc, hqcomp,
      Polynomial.comp_X]
  have hef := hforce (compData p a'⁻¹ (-(c' / a')) (γ'⁻¹) (inv_ne_zero haQ) hdegeq hgQcomp D)
  have hkey := efOf_compData p a'⁻¹ (-(c' / a')) (γ'⁻¹) (inv_ne_zero haQ) hdegeq hgQcomp D
  have hpair : QpType.efOf p D = (e₀, f₀) := by
    rw [← hkey]
    unfold QpType.efOf
    rw [hef.1, hef.2]
  unfold QpType.efOf at hpair
  rw [Prod.mk.injEq] at hpair
  exact hpair

end Transport

/-! ## Block 4 — box residue helpers (mod-`p` reads off any level-`≥ 1` box) -/

section BoxResidue

variable (p : ℕ) [hp : Fact p.Prime]

/-- Genuine divisibility pushes to the box: `p ∣ w` in `ℤ_[p]` forces `p ∣` the level-`N`
box value (`1 ≤ N`). -/
theorem box_dvd_of_dvd {N : ℕ} (hN : 1 ≤ N) {w : ℤ_[p]} (h : (p : ℤ_[p]) ∣ w) :
    p ∣ (PadicInt.toZModPow N w).val := by
  obtain ⟨t, rfl⟩ := h
  have hmap : PadicInt.toZModPow N ((p : ℤ_[p]) * t)
      = (p : ZMod (p ^ N)) * PadicInt.toZModPow N t := by
    rw [map_mul, map_natCast]
  have hval := val_pow_mul p (show 1 ≤ N from hN) (PadicInt.toZModPow N t)
  rw [pow_one, pow_one] at hval
  rw [hmap, hval]
  exact Dvd.intro _ rfl
/-- A non-divisible box value certifies a nonzero mod-`p` residue: the contrapositive decode
of the order-0 cells' `¬ p ∣ val` digit conditions. -/
theorem toZMod_ne_of_box_not_dvd {N : ℕ} (hN : 1 ≤ N) {w : ℤ_[p]}
    (h : ¬ p ∣ (PadicInt.toZModPow N w).val) : PadicInt.toZMod w ≠ 0 :=
  fun h0 => h (box_dvd_of_dvd p hN ((toZMod_eq_zero_iff p w).mp h0))

end BoxResidue

/-! ## Block 5 — the chain unwind (blueprint §1.2, the Proposition) -/

section Unwind

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The chain unwind** (blueprint §1.2 Proposition): a genuine monic quadratic whose box
pair at staircase frame `(L₀, L₁)` (additive budget `2·Σms + leafNeed leaf ≤ L₀`, staircase
invariant `L₀ ≤ L₁`) satisfies `ChainPair ms leaf` decodes — by induction on `ms`, each step
`stepDecode_general`, steps composed by `comp_affine_comp` — to a genuine monic quadratic `g`
whose box pair at the FINAL frame `(L₀ − 2Σms, L₁ − Σms)` satisfies `LeafPair leaf`, with the
SINGLE composed affine relation

  `f.comp (C p^Σms·X + C c) = C p^{2Σms}·g`

carrying all downstream transports (certificates UP via `qpType_translate_rescale`,
irreducibility UP via `irreducible_of_affine_rel`, every-bundle forcing DOWN via
`ef_forced_of_affine_rel`). Below the budget the fiber is empty
(`ChainMenu.chainPair_empty`), so the budget hypothesis loses no fibers. -/
theorem chainUnwind (leaf : ChainMenu.ChainLeaf) (ms : List ℕ) (hms : ∀ m ∈ ms, 1 ≤ m)
    {L₀ L₁ : ℕ} (hbud : 2 * ms.sum + ChainMenu.leafNeed leaf ≤ L₀) (hL01 : L₀ ≤ L₁)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainPair p ms leaf L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    ∃ (c : ℤ_[p]) (g : ℤ_[p][X]) (_ : g.Monic), g.natDegree = 2 ∧
      f.comp (C ((p : ℤ_[p]) ^ ms.sum) * X + C c)
        = C ((p : ℤ_[p]) ^ (2 * ms.sum)) * g ∧
      ChainMenu.LeafPair p leaf (L₀ - 2 * ms.sum) (L₁ - ms.sum)
        (PadicInt.toZModPow (L₀ - 2 * ms.sum) (g.coeff 0),
          PadicInt.toZModPow (L₁ - ms.sum) (g.coeff 1)) := by
  induction ms generalizing L₀ L₁ f with
  | nil =>
      refine ⟨0, f, hf, hdeg, ?_, ?_⟩
      · simp only [List.sum_nil, mul_zero, pow_zero, Polynomial.C_1, Polynomial.C_0,
          one_mul, add_zero, Polynomial.comp_X]
      · exact hfib
  | cons m ms' ih =>
      rw [List.sum_cons] at hbud
      have hm : 1 ≤ m := hms m List.mem_cons_self
      obtain ⟨ĉ, g, hg, hgdeg, hrel₁, htail⟩ :=
        stepDecode_general p hm (by omega) (by omega) hL01 ms' leaf hf hdeg hfib
      have hms' : ∀ m' ∈ ms', 1 ≤ m' := fun m' hm' => hms m' (List.mem_cons_of_mem m hm')
      obtain ⟨c', gl, hgl, hgldeg, hrel₂, hleaf⟩ :=
        ih hms' (L₀ := L₀ - 2 * m) (L₁ := L₁ - m) (by omega) (by omega) hg hgdeg htail
      rw [List.sum_cons,
        show L₀ - 2 * (m + ms'.sum) = L₀ - 2 * m - 2 * ms'.sum from by omega,
        show L₁ - (m + ms'.sum) = L₁ - m - ms'.sum from by omega]
      refine ⟨(p : ℤ_[p]) ^ m * c' + (ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ m, gl, hgl, hgldeg, ?_, hleaf⟩
      calc f.comp (C ((p : ℤ_[p]) ^ (m + ms'.sum)) * X
              + C ((p : ℤ_[p]) ^ m * c' + (ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ m))
          = (f.comp (C ((p : ℤ_[p]) ^ m) * X + C ((ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ m))).comp
              (C ((p : ℤ_[p]) ^ ms'.sum) * X + C c') := by
            rw [comp_affine_comp, pow_add]
        _ = (C ((p : ℤ_[p]) ^ (2 * m)) * g).comp
              (C ((p : ℤ_[p]) ^ ms'.sum) * X + C c') := by
            rw [hrel₁]
        _ = C ((p : ℤ_[p]) ^ (2 * m))
              * (g.comp (C ((p : ℤ_[p]) ^ ms'.sum) * X + C c')) := by
            rw [Polynomial.mul_comp, Polynomial.C_comp]
        _ = C ((p : ℤ_[p]) ^ (2 * m)) * (C ((p : ℤ_[p]) ^ (2 * ms'.sum)) * gl) := by
            rw [hrel₂]
        _ = C ((p : ℤ_[p]) ^ (2 * (m + ms'.sum))) * gl := by
            rw [← mul_assoc, ← Polynomial.C_mul, ← pow_add,
              show 2 * m + 2 * ms'.sum = 2 * (m + ms'.sum) from by omega]

end Unwind

/-! ## Block 6 — the per-leaf conclusions at `c = 0`, every depth (blueprint §1.2 Corollary) -/

section ChainFiber

variable (p : ℕ) [hp : Fact p.Prime]

/-- **All-depth split fiber ⟹ genuine certificate, AXIOM-FREE** (blueprint §1.2 Corollary,
`split k` leg): unwind, fire the (S) split master at the final frame, transport the
certificate UP through the single composed relation. -/
theorem chainFiber_split_hasType {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) {k L₀ L₁ : ℕ}
    (hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.split k) ≤ L₀)
    (hL01 : L₀ ≤ L₁)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainPair p ms (ChainMenu.ChainLeaf.split k) L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = ChainMenu.splitType2 := by
  obtain ⟨c, g, hg, hgdeg, hrel, hleaf⟩ :=
    chainUnwind p (ChainMenu.ChainLeaf.split k) ms hms hbud hL01 hf hdeg hfib
  have hL01' : L₀ - 2 * ms.sum ≤ L₁ - ms.sum := by omega
  obtain ⟨Fg, hFg⟩ := leafFiber_split_hasType p hL01' hg hgdeg hleaf
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hrel' : f.comp (C ((p : ℤ_[p]) ^ ms.sum) * X + C c)
      = C (((p : ℤ_[p]) ^ ms.sum) ^ g.natDegree) * g := by
    rw [hgdeg, ← pow_mul, Nat.mul_comm ms.sum 2]
    exact hrel
  obtain ⟨F, hF⟩ := qpType_translate_rescale p ((p : ℤ_[p]) ^ ms.sum) c
    (pow_ne_zero _ hpz) hrel' Fg
  exact ⟨F, hF.trans hFg⟩

/-- **All-depth ram fiber ⟹ irreducible + every-bundle `(2,1)`** (blueprint §1.2 Corollary,
`ram H` leg, `H` odd): unwind, fire the (R) ram master at the final frame, transport
irreducibility UP and pull every bundle of `f` BACK through the composed relation. -/
theorem chainFiber_ram_forced {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) {H L₀ L₁ : ℕ}
    (hodd : Odd H)
    (hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.ram H) ≤ L₀)
    (hL01 : L₀ ≤ L₁)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainPair p ms (ChainMenu.ChainLeaf.ram H) L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p]))
      ∧ ∀ D : QpType.LocalFactorData p f, QpType.eOf p D = 2 ∧ QpType.fOf p D = 1 := by
  obtain ⟨c, g, hg, hgdeg, hrel, hleaf⟩ :=
    chainUnwind p (ChainMenu.ChainLeaf.ram H) ms hms hbud hL01 hf hdeg hfib
  have hneed : ChainMenu.leafNeed (ChainMenu.ChainLeaf.ram H) ≤ L₀ - 2 * ms.sum := by omega
  have hL01' : L₀ - 2 * ms.sum ≤ L₁ - ms.sum := by omega
  obtain ⟨hgirr, hgforce⟩ := leafFiber_ram_forced p hodd hneed hL01' hg hgdeg hleaf
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  refine ⟨irreducible_of_affine_rel p (pow_ne_zero _ hpz) (pow_ne_zero _ hpz) hrel hgirr,
    fun D => ef_forced_of_affine_rel p (pow_ne_zero _ hpz) (pow_ne_zero _ hpz)
      (by rw [hgdeg, hdeg]) hrel hgforce D⟩

/-- **All-depth inert fiber ⟹ irreducible + every-bundle `(1,2)`** (blueprint §1.2
Corollary, `inert m` leg): unwind, fire the (I) inert master at the final frame, transport
as in the ram leg. -/
theorem chainFiber_inert_forced {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) {m L₀ L₁ : ℕ}
    (hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.inert m) ≤ L₀)
    (hL01 : L₀ ≤ L₁)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainPair p ms (ChainMenu.ChainLeaf.inert m) L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p]))
      ∧ ∀ D : QpType.LocalFactorData p f, QpType.eOf p D = 1 ∧ QpType.fOf p D = 2 := by
  obtain ⟨c, g, hg, hgdeg, hrel, hleaf⟩ :=
    chainUnwind p (ChainMenu.ChainLeaf.inert m) ms hms hbud hL01 hf hdeg hfib
  have hneed : ChainMenu.leafNeed (ChainMenu.ChainLeaf.inert m) ≤ L₀ - 2 * ms.sum := by omega
  have hL01' : L₀ - 2 * ms.sum ≤ L₁ - ms.sum := by omega
  obtain ⟨hgirr, hgforce⟩ := leafFiber_inert_forced p hneed hL01' hg hgdeg hleaf
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  refine ⟨irreducible_of_affine_rel p (pow_ne_zero _ hpz) (pow_ne_zero _ hpz) hrel hgirr,
    fun D => ef_forced_of_affine_rel p (pow_ne_zero _ hpz) (pow_ne_zero _ hpz)
      (by rw [hgdeg, hdeg]) hrel hgforce D⟩

end ChainFiber

/-! ## Block 7 — the translate reduction at `p = M9.realP = 2` (blueprint §1.3):
`TransChain` fibers of `f` ARE `ChainPair` fibers of the genuine translate `f(x + ĉ)` -/

section TranslateReduction

/-- The general-`ĉ` first coordinate of `SeriesAssembly.transMap`: `a₀ + ĉa₁ + ĉ²` (the
`ĉ ∈ {0, 1}` instances are `transMap_zero`/`transMap_one_fst`). -/
theorem transMap_fst (c N : ℕ) (a : SeriesAssembly.pairBox N) :
    (SeriesAssembly.transMap c N a).1
      = a.1 + (c : ZMod (M9.realP ^ N)) * a.2 + (c : ZMod (M9.realP ^ N)) ^ 2 := by
  show a.1 + ((c : ℕ) : ZMod (M9.realP ^ N))
      * (ZMod.castHom (pow_dvd_pow M9.realP (le_refl N)) (ZMod (M9.realP ^ N)) a.2)
      + ((c : ℕ) : ZMod (M9.realP ^ N)) ^ 2
    = a.1 + (c : ZMod (M9.realP ^ N)) * a.2 + (c : ZMod (M9.realP ^ N)) ^ 2
  rw [SeriesAssembly.castHom_pow_self_apply]

/-- **The translate commutation** (blueprint §1.3 Lemma): the box pair of the genuine
translate `f(x + ĉ)` is `transMap ĉ N` of the box pair of `f` — the box-level translate is
matched by the genuine translate, coefficient-wise through the ring hom `toZModPow N`. -/
theorem transBox_comp {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (ĉ N : ℕ) :
    (PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[M9.realP]))).coeff 0),
      PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[M9.realP]))).coeff 1))
      = SeriesAssembly.transMap ĉ N
          (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1)) := by
  refine Prod.ext ?_ ?_
  · show PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[M9.realP]))).coeff 0)
      = (SeriesAssembly.transMap ĉ N
          (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))).1
    rw [comp_translate_coeff_zero M9.realP hf hdeg, transMap_fst,
      map_add, map_add, map_mul, map_pow, map_natCast]
  · show PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[M9.realP]))).coeff 1)
      = (SeriesAssembly.transMap ĉ N
          (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))).2
    rw [comp_translate_coeff_one M9.realP hf hdeg, SeriesAssembly.transMap_snd,
      map_add, map_mul, map_natCast, map_ofNat]

/-- **The translate reduction** (blueprint §1.3 Reduction): the `TransChain ĉ` fiber of `f`
is DEFINITIONALLY the `c = 0` chain fiber of the genuine translate `f(x + ĉ)` — unfold
`TransChain`, rewrite by the commutation `transBox_comp`. -/
theorem transChain_fiber_iff (ms : List ℕ) (leaf : ChainMenu.ChainLeaf)
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2) (ĉ N : ℕ) :
    SeriesAssembly.TransChain ĉ ms leaf N
        (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))
      ↔ ChainMenu.ChainPair M9.realP ms leaf N N
          (PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[M9.realP]))).coeff 0),
            PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[M9.realP]))).coeff 1)) := by
  unfold SeriesAssembly.TransChain
  rw [← transBox_comp hf hdeg ĉ N]

end TranslateReduction

/-! ## Block 8 — the all-translate per-leaf conclusions at `p = 2` (blueprint §1.3):
Section-1 conclusions on `g = f(x + ĉ)`, transported back to `f` at `a = 1` -/

section TransChainFiber

/-- **All-translate all-depth split fiber ⟹ genuine certificate, AXIOM-FREE**: reduce to
the `c = 0` fiber of `g = f(x + ĉ)` (`transChain_fiber_iff`), apply the Section-1 split
conclusion to `g`, transport the certificate back to `f` along the pure translation
(`qpType_translate_rescale` at `a = 1`, `c = ĉ`). -/
theorem transChainFiber_split_hasType {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) {k ĉ N : ℕ}
    (hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.split k) ≤ N)
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.TransChain ĉ ms (ChainMenu.ChainLeaf.split k) N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ F : QpType.QpFactorization M9.realP f,
      QpType.qpType M9.realP F = ChainMenu.splitType2 := by
  have hg : (f.comp (X + C (ĉ : ℤ_[M9.realP]))).Monic :=
    comp_translate_monic M9.realP hf hdeg _
  have hgdeg : (f.comp (X + C (ĉ : ℤ_[M9.realP]))).natDegree = 2 :=
    comp_translate_natDegree M9.realP hf hdeg _
  have hfib' := (transChain_fiber_iff ms (ChainMenu.ChainLeaf.split k) hf hdeg ĉ N).mp hfib
  obtain ⟨Fg, hFg⟩ := chainFiber_split_hasType M9.realP hms hbud le_rfl hg hgdeg hfib'
  obtain ⟨F, hF⟩ := qpType_translate_rescale M9.realP 1 (ĉ : ℤ_[M9.realP]) one_ne_zero
    (translate_rel M9.realP f (ĉ : ℤ_[M9.realP])) Fg
  exact ⟨F, hF.trans hFg⟩

/-- **All-translate all-depth ram fiber ⟹ irreducible + every-bundle `(2,1)`**: reduce to
`g = f(x + ĉ)`, fire the Section-1 ram conclusion, transport back at `a = 1` (irreducibility
UP, bundle pullback DOWN). -/
theorem transChainFiber_ram_forced {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) {H ĉ N : ℕ}
    (hodd : Odd H)
    (hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.ram H) ≤ N)
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.TransChain ĉ ms (ChainMenu.ChainLeaf.ram H) N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    Irreducible (f.map (algebraMap ℤ_[M9.realP] ℚ_[M9.realP]))
      ∧ ∀ D : QpType.LocalFactorData M9.realP f,
          QpType.eOf M9.realP D = 2 ∧ QpType.fOf M9.realP D = 1 := by
  have hg : (f.comp (X + C (ĉ : ℤ_[M9.realP]))).Monic :=
    comp_translate_monic M9.realP hf hdeg _
  have hgdeg : (f.comp (X + C (ĉ : ℤ_[M9.realP]))).natDegree = 2 :=
    comp_translate_natDegree M9.realP hf hdeg _
  have hfib' := (transChain_fiber_iff ms (ChainMenu.ChainLeaf.ram H) hf hdeg ĉ N).mp hfib
  obtain ⟨hgirr, hgforce⟩ := chainFiber_ram_forced M9.realP hms hodd hbud le_rfl hg hgdeg hfib'
  have hrel1 : f.comp (C (1 : ℤ_[M9.realP]) * X + C (ĉ : ℤ_[M9.realP]))
      = C (1 : ℤ_[M9.realP]) * f.comp (X + C (ĉ : ℤ_[M9.realP])) := by
    rw [Polynomial.C_1, one_mul, one_mul]
  refine ⟨irreducible_of_affine_rel M9.realP one_ne_zero one_ne_zero hrel1 hgirr,
    fun D => ef_forced_of_affine_rel M9.realP one_ne_zero one_ne_zero
      (by rw [hgdeg, hdeg]) hrel1 hgforce D⟩

/-- **All-translate all-depth inert fiber ⟹ irreducible + every-bundle `(1,2)`**: as the
ram leg, at the (I) conclusion. -/
theorem transChainFiber_inert_forced {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) {m ĉ N : ℕ}
    (hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.inert m) ≤ N)
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.TransChain ĉ ms (ChainMenu.ChainLeaf.inert m) N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    Irreducible (f.map (algebraMap ℤ_[M9.realP] ℚ_[M9.realP]))
      ∧ ∀ D : QpType.LocalFactorData M9.realP f,
          QpType.eOf M9.realP D = 1 ∧ QpType.fOf M9.realP D = 2 := by
  have hg : (f.comp (X + C (ĉ : ℤ_[M9.realP]))).Monic :=
    comp_translate_monic M9.realP hf hdeg _
  have hgdeg : (f.comp (X + C (ĉ : ℤ_[M9.realP]))).natDegree = 2 :=
    comp_translate_natDegree M9.realP hf hdeg _
  have hfib' := (transChain_fiber_iff ms (ChainMenu.ChainLeaf.inert m) hf hdeg ĉ N).mp hfib
  obtain ⟨hgirr, hgforce⟩ := chainFiber_inert_forced M9.realP hms hbud le_rfl hg hgdeg hfib'
  have hrel1 : f.comp (C (1 : ℤ_[M9.realP]) * X + C (ĉ : ℤ_[M9.realP]))
      = C (1 : ℤ_[M9.realP]) * f.comp (X + C (ĉ : ℤ_[M9.realP])) := by
    rw [Polynomial.C_1, one_mul, one_mul]
  refine ⟨irreducible_of_affine_rel M9.realP one_ne_zero one_ne_zero hrel1 hgirr,
    fun D => ef_forced_of_affine_rel M9.realP one_ne_zero one_ne_zero
      (by rw [hgdeg, hdeg]) hrel1 hgforce D⟩

end TransChainFiber

/-! ## Block 9 — the order-0 separable cell masters at `p = 2` (blueprint §1.1 (S0)/(I0)):
digit decode + the `k = 0` / `m = 0` boundary instances of the (S)/(I) masters -/

section SepCells

/-- **The order-0 split cell has the genuine certificate, AXIOM-FREE** ((S0) = (S) at
`k = 0`): `SepSplitCell` reads `2 ∣ a₀`, `2 ∤ a₁` off the level-`N ≥ 1` box; decode to
genuine (`dvd_of_box_dvd` / the residue bridge) and fire `leafSplit_master_hasType` at
`k = 0` (`b₁ = 2⁰·a₁` a unit, `2^{2·0+1} = 2 ∣ a₀`). -/
theorem sepSplitCell_hasType {N : ℕ} (hN : 1 ≤ N) {f : Polynomial ℤ_[M9.realP]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.SepSplitCell N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ F : QpType.QpFactorization M9.realP f,
      QpType.qpType M9.realP F = ChainMenu.splitType2 := by
  obtain ⟨hd0, hd1⟩ := hfib
  have hb₀1 : (M9.realP : ℤ_[M9.realP]) ^ 1 ∣ f.coeff 0 :=
    dvd_of_box_dvd M9.realP hN (by rw [pow_one]; exact hd0)
  have hb₀ : (M9.realP : ℤ_[M9.realP]) ^ (2 * 0 + 1) ∣ f.coeff 0 := hb₀1
  have hw₁ : PadicInt.toZMod (f.coeff 1) ≠ 0 := toZMod_ne_of_box_not_dvd M9.realP hN hd1
  have hb₁ : f.coeff 1 = (M9.realP : ℤ_[M9.realP]) ^ 0 * f.coeff 1 := by
    rw [pow_zero, one_mul]
  rw [monic_quadratic_eq M9.realP hf hdeg]
  exact leafSplit_master_hasType M9.realP 0 hb₁ hw₁ hb₀

/-- **The order-0 inert cell forces irreducible + every-bundle `(1,2)`** ((I0) = (I) at
`m = 0`): `SepInertCell` reads `2 ∤ a₀`, `2 ∤ a₁`; both residues are the nonzero digit `1`
of `F₂`, and `z² + z + 1` is root-free (`noRootPairs 2` membership by `decide`), so the (I)
master fires at `m = 0`. -/
theorem sepInertCell_forced {N : ℕ} (hN : 1 ≤ N) {f : Polynomial ℤ_[M9.realP]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.SepInertCell N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    Irreducible (f.map (algebraMap ℤ_[M9.realP] ℚ_[M9.realP]))
      ∧ ∀ D : QpType.LocalFactorData M9.realP f,
          QpType.eOf M9.realP D = 1 ∧ QpType.fOf M9.realP D = 2 := by
  obtain ⟨hd0, hd1⟩ := hfib
  have hw₀ : PadicInt.toZMod (f.coeff 0) ≠ 0 := toZMod_ne_of_box_not_dvd M9.realP hN hd0
  have hw₁ : PadicInt.toZMod (f.coeff 1) ≠ 0 := toZMod_ne_of_box_not_dvd M9.realP hN hd1
  have hone : ∀ x : ZMod M9.realP, x ≠ 0 → x = 1 := by decide
  have hmem : (PadicInt.toZMod (f.coeff 0), PadicInt.toZMod (f.coeff 1))
      ∈ ChainMenu.noRootPairs M9.realP := by
    rw [ChainMenu.mem_noRootPairs]
    show ∀ r : ZMod M9.realP,
      r ^ 2 + PadicInt.toZMod (f.coeff 1) * r + PadicInt.toZMod (f.coeff 0) ≠ 0
    rw [hone _ hw₁, hone _ hw₀]
    decide
  have hb₀ : f.coeff 0 = (M9.realP : ℤ_[M9.realP]) ^ (2 * 0) * f.coeff 0 := by
    norm_num
  have hb₁ : f.coeff 1 = (M9.realP : ℤ_[M9.realP]) ^ 0 * f.coeff 1 := by
    rw [pow_zero, one_mul]
  constructor
  · rw [monic_quadratic_eq M9.realP hf hdeg]
    exact leafInert_master_irreducible M9.realP 0 hb₀ hb₁ hmem
  · rw [monic_quadratic_eq M9.realP hf hdeg]
    exact fun D => leafInert_master_forced M9.realP 0 hb₀ hb₁ hmem D

end SepCells

/-! ## Block 10 — axiom census (this module declares NO axiom; everything must be core-only:
`[propext, Classical.choice, Quot.sound]`. Any `om_leaf_faithful` appearance is a FAILURE.) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeChainAll.affine_comp_affine
#print axioms LeanUrat.OM.QpTypeChainAll.comp_affine_comp
#print axioms LeanUrat.OM.QpTypeChainAll.comp_translate_eq
#print axioms LeanUrat.OM.QpTypeChainAll.comp_translate_monic
#print axioms LeanUrat.OM.QpTypeChainAll.comp_translate_natDegree
#print axioms LeanUrat.OM.QpTypeChainAll.comp_translate_coeff_zero
#print axioms LeanUrat.OM.QpTypeChainAll.comp_translate_coeff_one
#print axioms LeanUrat.OM.QpTypeChainAll.translate_rel
#print axioms LeanUrat.OM.QpTypeChainAll.map_affine_rel
#print axioms LeanUrat.OM.QpTypeChainAll.irreducible_of_affine_rel
#print axioms LeanUrat.OM.QpTypeChainAll.ef_forced_of_affine_rel
#print axioms LeanUrat.OM.QpTypeChainAll.box_dvd_of_dvd
#print axioms LeanUrat.OM.QpTypeChainAll.toZMod_ne_of_box_not_dvd
#print axioms LeanUrat.OM.QpTypeChainAll.chainUnwind
#print axioms LeanUrat.OM.QpTypeChainAll.chainFiber_split_hasType
#print axioms LeanUrat.OM.QpTypeChainAll.chainFiber_ram_forced
#print axioms LeanUrat.OM.QpTypeChainAll.chainFiber_inert_forced
#print axioms LeanUrat.OM.QpTypeChainAll.transMap_fst
#print axioms LeanUrat.OM.QpTypeChainAll.transBox_comp
#print axioms LeanUrat.OM.QpTypeChainAll.transChain_fiber_iff
#print axioms LeanUrat.OM.QpTypeChainAll.transChainFiber_split_hasType
#print axioms LeanUrat.OM.QpTypeChainAll.transChainFiber_ram_forced
#print axioms LeanUrat.OM.QpTypeChainAll.transChainFiber_inert_forced
#print axioms LeanUrat.OM.QpTypeChainAll.sepSplitCell_hasType
#print axioms LeanUrat.OM.QpTypeChainAll.sepInertCell_forced

end AxCheck

end LeanUrat.OM.QpTypeChainAll
