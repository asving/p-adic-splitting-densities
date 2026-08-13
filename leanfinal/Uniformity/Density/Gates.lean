/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Statement
import Uniformity.Density.QuadCert

/-!
# Uniformity.Density.Gates — machine-checked gates on the genuine density

The verification target of Part 1: **do the definitions compute the densities we expect?**

* **G1 (`n = 1`, EXACT).** Every monic linear polynomial has type `⟨{(1,1)}⟩`, so every class at
  every level is decided and `genuineDensity O 1 ⟨{(1,1)}⟩ = 1` — exactly, over every complete
  DVR with finite residue field (`genuineDensity_linear_eq_one`). Every other type has density
  exactly `0` (`genuineDensity_one_of_ne`), so `n = 1` also gives an **exact σ-separation**
  (`gate_sigma_separation_one`).
* **G2 (`n = 2`, algebraic half).** A monic quadratic that splits into two monic linear factors
  has type `⟨{(1,1),(1,1)}⟩` (`typeOf_mul_linear`).
* **G3 (`n = 2`, LOWER BOUND, every `O`).** Hensel's lemma at a simple residue root shows the
  level-1 class `(a₀, a₁) ≡ (0, 1)` is split-decided, so
  `1 / q ^ 2 ≤ genuineDensity O 2 splitType` (`gate_split_lower`). At `q = 2` this reads
  `1/4 ≤ density(split)`; the W-11 corpus value is `q/(2(q+1)) = 1/3`. ✓ consistent.
* **G4 (`n = 2`, σ-separation).** The degree-1 type has density `0` at degree `2`
  (`genuineDensity_two_linType_eq_zero`), while split has density `≥ 1/q² > 0`; so the density
  genuinely depends on σ at `n = 2` as well (`gate_sigma_separation_two`).

Everything here is proved for an ARBITRARY complete DVR with finite residue field — the gates
are not `ℤ_[2]`-only. `gate_padic_two` instantiates G3 at `ℤ_[2]` for the concrete number.

**What is NOT here** (honest scope, see `notes/GENUINE_DENSITY_2026-08-13.md` §STATUS):
exact `n = 2` values, the inert/ramified lower bounds, and the matching upper bounds. Those
need the full order-0 census (all `q-1` split classes at level 1, plus Eisenstein and
irreducible-reduction certificates) — stated in the note as open targets.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

/-! ## 1. G1 — degree 1, exact -/

section DegreeOne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Every monic degree-1 polynomial over `O` has type `linType`. -/
theorem typeOf_monicPoly_one (a : Fin 1 → O) : typeOf (monicPoly a) = linType :=
  typeOf_of_natDegree_one (monicPoly_monic a) (monicPoly_natDegree a)

theorem decidedSet_one (N : ℕ) : decidedSet O 1 linType N = Set.univ := by
  ext c
  simp only [Set.mem_univ, iff_true]
  intro a _
  exact typeOf_monicPoly_one a

theorem decidedCount_one (N : ℕ) : decidedCount O 1 linType N = residueCard O ^ (1 * N) := by
  rw [decidedCount, decidedSet_one, Nat.card_congr (Equiv.Set.univ (Coeff O 1 N)), card_coeff]

theorem decidedSeq_one (N : ℕ) : decidedSeq O 1 linType N = 1 := by
  rw [decidedSeq, decidedCount_one, div_eq_one_iff_eq (qpow_ne _)]
  push_cast
  ring

/-- **G1 (exact).** The density of monic *linear* polynomials of the (unique possible) type
`{(1,1)}` is exactly `1`, over every complete DVR with finite residue field. -/
theorem genuineDensity_linear_eq_one : genuineDensity O 1 linType = 1 := by
  rw [genuineDensity]
  simp [decidedSeq_one]

/-- **G1 (exact, complement).** Every other type has density exactly `0` at degree 1. -/
theorem genuineDensity_one_of_ne {σ : FactorizationType} (hσ : σ ≠ linType) :
    genuineDensity O 1 σ = 0 := by
  have hempty : ∀ N, decidedSet O 1 σ N = ∅ := by
    intro N
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 1 N c
    exact hσ (((hc a ha).symm.trans (typeOf_monicPoly_one a)))
  have hzero : ∀ N, decidedSeq O 1 σ N = 0 := by
    intro N
    rw [decidedSeq, decidedCount, hempty N]
    simp
  rw [genuineDensity]
  simp [hzero]

/-- **G1 σ-separation (exact).** Two distinct degree-≤1 types get *different* densities: the
definition is genuinely σ-dependent, not a σ-discarding constant. -/
theorem gate_sigma_separation_one :
    genuineDensity O 1 linType ≠ genuineDensity O 1 splitType := by
  rw [genuineDensity_linear_eq_one, genuineDensity_one_of_ne splitType_ne_linType]
  norm_num

end DegreeOne

/-! ## 2. G2 — the split type of a product of two monic linear factors -/

section Split

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **G2.** A monic quadratic that factors into two monic linear factors has type
`{(1,1),(1,1)}` — the SPLIT type. -/
theorem typeOf_mul_linear (r s : O) : typeOf ((X - C r) * (X - C s)) = splitType := by
  have hr : (X - C r : Polynomial O).Monic := monic_X_sub_C r
  have hs : (X - C s : Polynomial O).Monic := monic_X_sub_C s
  have hrd : (X - C r : Polynomial O).natDegree = 1 := natDegree_X_sub_C r
  have hsd : (X - C s : Polynomial O).natDegree = 1 := natDegree_X_sub_C s
  have hF : IsMonicFactorization ((X - C r) * (X - C s)) {X - C r, X - C s} := by
    refine ⟨?_, by simp⟩
    intro g hg
    rcases Multiset.mem_cons.1 hg with rfl | hg
    · exact ⟨hr, irreducible_of_monic_natDegree_one hr hrd⟩
    · rw [Multiset.mem_singleton.1 hg]
      exact ⟨hs, irreducible_of_monic_natDegree_one hs hsd⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [splitType, efPair_of_natDegree_one hr hrd, efPair_of_natDegree_one hs hsd]

end Split

/-! ## 3. G3 — the `n = 2` lower bound, by Hensel at a simple residue root -/

section SplitLower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **Hensel's split certificate.** If `a₀ ∈ 𝔪` and `a₁` is a unit, the monic quadratic
`X² + a₁X + a₀` has a root `r ≡ 0 (mod 𝔪)`, hence factors into two monic linear factors, hence
has the SPLIT type. (Only one Hensel lift is needed: the second root is `-a₁ - r`.) -/
theorem typeOf_split_of_unit (a : Fin 2 → O) (h0 : a 0 ∈ maximalIdeal O) (h1 : IsUnit (a 1)) :
    typeOf (monicPoly a) = splitType := by
  obtain ⟨r, hr, -⟩ :=
    HenselianLocalRing.is_henselian (monicPoly a) (monicPoly_monic a) 0
      (by rw [monicPoly_two_eval]; simpa using h0)
      (by rw [monicPoly_two_deriv_eval]; simpa using h1)
  have hroot : r ^ 2 + a 0 + a 1 * r = 0 := by
    have := hr
    rwa [IsRoot, monicPoly_two_eval] at this
  have ha0 : a 0 = -(r ^ 2) - a 1 * r := by linear_combination hroot
  have hfac : monicPoly a = (X - C r) * (X - C (-(a 1) - r)) := by
    rw [monicPoly_two_expand, ha0]
    simp only [map_sub, map_neg, map_mul, map_pow]
    ring
  rw [hfac]
  exact typeOf_mul_linear r _

/-- The level-1 class `(a₀, a₁) ≡ (0, 1)` is SPLIT-decided: every lift has `a₀ ∈ 𝔪` and `a₁` a
unit, so `typeOf_split_of_unit` applies. -/
theorem split_decided_class :
    DecidedAt O 2 splitType 1 (proj O 2 1 ![0, 1]) := by
  intro b hb
  have hb0 : b 0 - (0 : O) ∈ (maximalIdeal O) ^ 1 := by
    have := congrFun hb 0
    rwa [proj, proj, Ideal.Quotient.eq] at this
  have hb1 : b 1 - (1 : O) ∈ (maximalIdeal O) ^ 1 := by
    have := congrFun hb 1
    rwa [proj, proj, Ideal.Quotient.eq] at this
  rw [pow_one] at hb0 hb1
  refine typeOf_split_of_unit b (by simpa using hb0) ?_
  by_contra hu
  have hmem : b 1 ∈ maximalIdeal O := mem_maximalIdeal _ |>.2 (mem_nonunits_iff.2 hu)
  have hone : (1 : O) ∈ maximalIdeal O := by
    have h := Ideal.sub_mem _ hmem hb1
    simpa using h
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hone)

/-- **G3 (lower bound, every `O`).** `1 / q ^ 2 ≤ genuineDensity O 2 splitType`. At `q = 2` this
is `1/4`; the W-11 corpus value of the split density is `q / (2(q+1)) = 1/3`. -/
theorem gate_split_lower :
    1 / (residueCard O : ℝ) ^ 2 ≤ genuineDensity O 2 splitType := by
  have hne : (decidedSet O 2 splitType 1).Nonempty := ⟨_, split_decided_class⟩
  have hpos : 0 < decidedCount O 2 splitType 1 := by
    rw [decidedCount]
    have : Nonempty (decidedSet O 2 splitType 1) := hne.to_subtype
    exact Nat.card_pos
  have hA : (1 : ℝ) ≤ (decidedCount O 2 splitType 1 : ℝ) := by exact_mod_cast hpos
  have hc : (0 : ℝ) < (residueCard O : ℝ) ^ 2 := qpow_pos (O := O) 2
  have h1 : 1 / (residueCard O : ℝ) ^ 2 ≤ decidedSeq O 2 splitType 1 := by
    rw [decidedSeq, show (2 : ℕ) * 1 = 2 from rfl, div_le_div_iff₀ hc hc]
    nlinarith [hA, hc]
  exact h1.trans (decidedSeq_le_genuineDensity 2 splitType 1)

/-- The `ℤ_[2]` instance of G3: the split density at the wild prime is at least `1/4`
(W-11's exact value there is `1/3`). -/
theorem gate_padic_two : 1 / (2 : ℝ) ^ 2 ≤ genuineDensity ℤ_[2] 2 splitType := by
  have := gate_split_lower (O := ℤ_[2])
  rwa [residueCard_padicInt 2] at this

end SplitLower

/-! ## 4. G4 — σ-separation at `n = 2` -/

section SepTwo

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- No monic *quadratic* has the degree-1 type `{(1,1)}`: a single irreducible factor of a
monic quadratic has degree 2, and its `(e,f)` pair is `(2/m, m)` with `1 ≤ m ≤ 2`
(`m = inertiaDegOf ≤ deg = 2` because `2 ∈ normValues`), never `(1,1)`. -/
theorem typeOf_monicPoly_two_ne_linType (a : Fin 2 → O) : typeOf (monicPoly a) ≠ linType := by
  intro h
  have hmonic := monicPoly_monic a
  have hdeg := monicPoly_natDegree a
  have hdata : (monicFactors (monicPoly a)).map efPair = {(1, 1)} := congrArg (·.data) h
  have hcard : Multiset.card (monicFactors (monicPoly a)) = 1 := by
    have := congrArg Multiset.card hdata
    simpa using this
  obtain ⟨g, hg⟩ := Multiset.card_eq_one.1 hcard
  have hspec := monicFactors_spec hmonic
  rw [hg] at hspec hdata
  have hgf : g = monicPoly a := by simpa using hspec.2
  have hgd : g.natDegree = 2 := by rw [hgf, hdeg]
  have hef : efPair g = (1, 1) := by simpa using hdata
  -- `e * f = deg g = 2`, but the type says `e = f = 1`
  have hmul : ramIndexOf g * inertiaDegOf g = g.natDegree :=
    ramIndexOf_mul_inertiaDegOf (hgf ▸ hmonic) (by omega)
  have h2 : inertiaDegOf g = 1 := (Prod.mk.injEq _ _ _ _ ▸ hef).2
  have h1 : ramIndexOf g = 1 := (Prod.mk.injEq _ _ _ _ ▸ hef).1
  rw [h1, h2, hgd] at hmul
  omega

/-- The degree-1 type has density exactly `0` among monic quadratics. -/
theorem genuineDensity_two_linType_eq_zero : genuineDensity O 2 linType = 0 := by
  have hempty : ∀ N, decidedSet O 2 linType N = ∅ := by
    intro N
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    exact typeOf_monicPoly_two_ne_linType a (hc a ha)
  have hzero : ∀ N, decidedSeq O 2 linType N = 0 := by
    intro N
    rw [decidedSeq, decidedCount, hempty N]
    simp
  rw [genuineDensity]
  simp [hzero]

/-- **G4 (σ-separation at `n = 2`).** At degree 2 the split type has strictly positive density
while the degree-1 type has density `0`: the density is genuinely σ-keyed at `n = 2`. -/
theorem gate_sigma_separation_two :
    genuineDensity O 2 linType < genuineDensity O 2 splitType := by
  rw [genuineDensity_two_linType_eq_zero]
  exact lt_of_lt_of_le (one_div_pos.2 (qpow_pos (O := O) 2)) (gate_split_lower (O := O))

end SepTwo

/-! ## 5. Sharpened lower bounds and the certified brackets (follow-up unit, 2026-08-13) -/

section Lowers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **One decided class is a density lower bound.** -/
theorem genuineDensity_ge_of_decided {n N : ℕ} {σ : FactorizationType} {c : Coeff O n N}
    (h : DecidedAt O n σ N c) :
    1 / (residueCard O : ℝ) ^ (n * N) ≤ genuineDensity O n σ := by
  have hpos : 0 < decidedCount O n σ N := by
    rw [decidedCount]
    have : Nonempty (decidedSet O n σ N) := ⟨⟨c, h⟩⟩
    exact Nat.card_pos
  have hA : (1 : ℝ) ≤ (decidedCount O n σ N : ℝ) := by exact_mod_cast hpos
  have hc : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos (O := O) _
  refine le_trans ?_ (decidedSeq_le_genuineDensity n σ N)
  rw [decidedSeq, div_le_div_iff₀ hc hc]
  nlinarith [hA, hc]

/-! ### Split, sharpened: all `q - 1` level-1 classes `(0, unit)` -/

/-- Every level-1 class with `a₀ ≡ 0` and `a₁` a unit is SPLIT-decided. -/
theorem split_decided_of_level_one {c : Coeff O 2 1} (h0 : c 0 = 0) (h1 : c 1 ≠ 0) :
    DecidedAt O 2 splitType 1 c := by
  intro b hb
  have hb0 : b 0 ∈ maximalIdeal O := by
    have h := congrFun hb 0
    rw [h0] at h
    have : b 0 ∈ (maximalIdeal O) ^ 1 := (Ideal.Quotient.eq_zero_iff_mem).1 h
    rwa [pow_one] at this
  have hb1 : IsUnit (b 1) := by
    by_contra hu
    refine h1 ?_
    have hmem : b 1 ∈ (maximalIdeal O) ^ 1 := by
      rw [pow_one]; exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
    have h := congrFun hb 1
    rw [← h]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
  exact typeOf_split_of_unit b hb0 hb1

theorem card_ne_zero_res_one : Nat.card {y : Res O 1 // y ≠ (0 : Res O 1)} = residueCard O - 1 := by
  classical
  haveI : Fintype (Res O 1) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq (0 : Res O 1),
    ← Nat.card_eq_fintype_card, card_res, pow_one]

theorem decidedCount_split_ge : residueCard O - 1 ≤ decidedCount O 2 splitType 1 := by
  rw [← card_ne_zero_res_one (O := O), decidedCount]
  refine Nat.card_le_card_of_injective
    (fun y => (⟨![0, y.1], split_decided_of_level_one (by simp) (by simpa using y.2)⟩ :
      decidedSet O 2 splitType 1)) ?_
  intro y z hyz
  have h : (![0, y.1] : Coeff O 2 1) = ![0, z.1] := Subtype.ext_iff.1 hyz
  exact Subtype.ext (by simpa using congrFun h 1)

/-- **G3-sharp.** `(q-1)/q² ≤ genuineDensity O 2 splitType` — the whole order-0 SEP-SPLIT
stratum at level 1 (W-11's SEP-SPLIT row in per-centre form). -/
theorem gate_split_lower_sharp :
    ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 2 ≤ genuineDensity O 2 splitType := by
  have hq1 : (1 : ℕ) ≤ residueCard O := le_trans one_le_two (two_le_residueCard O)
  have hcast : ((residueCard O - 1 : ℕ) : ℝ) = (residueCard O : ℝ) - 1 := by
    push_cast [Nat.cast_sub hq1]; ring
  have hA : ((residueCard O : ℝ) - 1) ≤ (decidedCount O 2 splitType 1 : ℝ) := by
    rw [← hcast]; exact_mod_cast decidedCount_split_ge (O := O)
  have hc : (0 : ℝ) < (residueCard O : ℝ) ^ 2 := qpow_pos (O := O) 2
  refine le_trans ?_ (decidedSeq_le_genuineDensity 2 splitType 1)
  rw [decidedSeq, show (2 : ℕ) * 1 = 2 from rfl, div_le_div_iff₀ hc hc]
  nlinarith [hA, hc]

/-! ### Ramified: the Eisenstein class at level 2 -/

/-- The level-2 class `(a₀, a₁) ≡ (π, 0)` is RAM-decided: every lift is Eisenstein. -/
theorem ram_decided_class {π : O} (hπ : Irreducible π) :
    DecidedAt O 2 ramType 2 (proj O 2 2 ![π, 0]) := by
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ maximalIdeal O := by rw [hm]; exact Ideal.mem_span_singleton_self π
  have hπm2 : π ∉ (maximalIdeal O) ^ 2 := by
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : π * 1 = π * (π * c) := by linear_combination hc
    have h2 : (1 : O) = π * c := mul_left_cancel₀ hπ.ne_zero h1
    exact hπ.not_isUnit ⟨⟨π, c, h2.symm, by rw [mul_comm]; exact h2.symm⟩, rfl⟩
  intro b hb
  have hb0 : b 0 - π ∈ (maximalIdeal O) ^ 2 := by
    have h := congrFun hb 0
    rw [proj, proj] at h
    have := (Ideal.Quotient.eq).1 h
    simpa using this
  have hb1 : b 1 - 0 ∈ (maximalIdeal O) ^ 2 := by
    have h := congrFun hb 1
    rw [proj, proj] at h
    have := (Ideal.Quotient.eq).1 h
    simpa using this
  have hsq : (maximalIdeal O) ^ 2 ≤ maximalIdeal O := Ideal.pow_le_self (by norm_num)
  refine typeOf_ram_of_eisenstein ?_ ?_ ?_
  · have : b 0 = (b 0 - π) + π := by ring
    rw [this]; exact Ideal.add_mem _ (hsq hb0) hπm
  · intro hmem
    refine hπm2 ?_
    have : π = b 0 - (b 0 - π) := by ring
    rw [this]; exact Ideal.sub_mem _ hmem hb0
  · simpa using hsq hb1

/-- **G5 (RAM lower bound, every `O`).** `1/q⁴ ≤ genuineDensity O 2 ramType`. -/
theorem gate_ram_lower : 1 / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 2 ramType := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h := genuineDensity_ge_of_decided (ram_decided_class hπ)
  simpa using h

end Lowers

/-! ### Inert: anisotropy over `ℤ_[p]`, checked by `decide` on the residue field -/

section Inert

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem mem_maximalIdeal_padic_iff (x : ℤ_[p]) :
    x ∈ maximalIdeal ℤ_[p] ↔ PadicInt.toZMod x = 0 := by
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker]

/-- Anisotropy over `ℤ_[p]` is a finite check on the residue field `ZMod p`. -/
theorem anisotropic_padic (a : Fin 2 → ℤ_[p])
    (h : ∀ x y : ZMod p,
      x ^ 2 - PadicInt.toZMod (a 1) * x * y + PadicInt.toZMod (a 0) * y ^ 2 = 0 →
        x = 0 ∧ y = 0) :
    Anisotropic a := by
  intro u v huv
  rw [mem_maximalIdeal_padic_iff, show quadForm a u v = u ^ 2 - a 1 * u * v + a 0 * v ^ 2 from rfl,
    map_add, map_sub, map_mul, map_mul, map_pow, map_mul, map_pow] at huv
  obtain ⟨h1, h2⟩ := h _ _ huv
  exact ⟨(mem_maximalIdeal_padic_iff _).2 h1, (mem_maximalIdeal_padic_iff _).2 h2⟩

/-- The level-1 class of `a` over `ℤ_[p]` is INERT-decided as soon as the reduced norm form is
anisotropic (a finite check on `ZMod p`). -/
theorem inert_decided_class_padic (a : Fin 2 → ℤ_[p])
    (h : ∀ x y : ZMod p,
      x ^ 2 - PadicInt.toZMod (a 1) * x * y + PadicInt.toZMod (a 0) * y ^ 2 = 0 →
        x = 0 ∧ y = 0) :
    DecidedAt ℤ_[p] 2 inertType 1 (proj ℤ_[p] 2 1 a) := by
  intro b hb
  refine typeOf_inert_of_anisotropic (anisotropic_padic b ?_)
  have hbi : ∀ i, PadicInt.toZMod (b i) = PadicInt.toZMod (a i) := by
    intro i
    have hh := congrFun hb i
    rw [proj, proj, Ideal.Quotient.eq, pow_one] at hh
    have h0 := (mem_maximalIdeal_padic_iff _).1 hh
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  rw [hbi 1, hbi 0]
  exact h

end Inert

/-! ### The certified two-sided brackets -/

section Bracket

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The bracket engine.** Lower bounds on the three degree-2 types turn, via
`sum_genuineDensity_le_one`, into upper bounds on each one. -/
theorem bracket_two {ls li lr : ℝ}
    (hs : ls ≤ genuineDensity O 2 splitType)
    (hi : li ≤ genuineDensity O 2 inertType)
    (hr : lr ≤ genuineDensity O 2 ramType) :
    (ls ≤ genuineDensity O 2 splitType ∧ genuineDensity O 2 splitType ≤ 1 - li - lr)
    ∧ (li ≤ genuineDensity O 2 inertType ∧ genuineDensity O 2 inertType ≤ 1 - ls - lr)
    ∧ (lr ≤ genuineDensity O 2 ramType ∧ genuineDensity O 2 ramType ≤ 1 - ls - li) := by
  classical
  have hsum : ∑ τ ∈ ({splitType, inertType, ramType} : Finset FactorizationType),
      genuineDensity O 2 τ ≤ 1 := sum_genuineDensity_le_one 2 _
  rw [Finset.sum_insert (by simp [splitType_ne_inertType, splitType_ne_ramType]),
    Finset.sum_insert (by simp [inertType_ne_ramType]), Finset.sum_singleton] at hsum
  exact ⟨⟨hs, by linarith⟩, ⟨hi, by linarith⟩, ⟨hr, by linarith⟩⟩

end Bracket

section BracketPadic

/-- The three level-certified lower bounds at `q = 2`. -/
theorem lowers_padic_two :
    (1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 splitType
    ∧ (1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 inertType
    ∧ (1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 2 ramType := by
  refine ⟨?_, ?_, ?_⟩
  · have h := gate_split_lower_sharp (O := ℤ_[2])
    rw [residueCard_padicInt 2] at h
    norm_num at h ⊢
    linarith
  · have h := genuineDensity_ge_of_decided
      (inert_decided_class_padic (p := 2) ![1, 1] (by
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, map_one]
        decide))
    rw [residueCard_padicInt 2] at h
    norm_num at h ⊢
    linarith
  · have h := gate_ram_lower (O := ℤ_[2])
    rw [residueCard_padicInt 2] at h
    norm_num at h ⊢
    linarith

/-- The three level-certified lower bounds at `q = 3`. -/
theorem lowers_padic_three :
    (2 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 splitType
    ∧ (1 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 inertType
    ∧ (1 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 2 ramType := by
  refine ⟨?_, ?_, ?_⟩
  · have h := gate_split_lower_sharp (O := ℤ_[3])
    rw [residueCard_padicInt 3] at h
    norm_num at h ⊢
    linarith
  · have h := genuineDensity_ge_of_decided
      (inert_decided_class_padic (p := 3) ![1, 0] (by
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, map_one, map_zero]
        decide))
    rw [residueCard_padicInt 3] at h
    norm_num at h ⊢
    linarith
  · have h := gate_ram_lower (O := ℤ_[3])
    rw [residueCard_padicInt 3] at h
    norm_num at h ⊢
    linarith

/-- **GATE BRACKET, q = 2.** Two-sided brackets for all three degree-2 types over `ℤ_[2]`.
W-11's exact values are `split = inert = ram = 1/3`, all inside these brackets
(`gate_bracket_w11_two`). -/
theorem gate_bracket_padic_two :
    ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 splitType
        ∧ genuineDensity ℤ_[2] 2 splitType ≤ 11 / 16)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 inertType
        ∧ genuineDensity ℤ_[2] 2 inertType ≤ 11 / 16)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 2 ramType
        ∧ genuineDensity ℤ_[2] 2 ramType ≤ 1 / 2) := by
  obtain ⟨hs, hi, hr⟩ := lowers_padic_two
  obtain ⟨⟨-, hs'⟩, ⟨-, hi'⟩, ⟨-, hr'⟩⟩ := bracket_two hs hi hr
  refine ⟨⟨hs, ?_⟩, ⟨hi, ?_⟩, ⟨hr, ?_⟩⟩ <;> linarith

/-- **GATE BRACKET, q = 3.** Two-sided brackets over `ℤ_[3]`. W-11's exact values are
`split = inert = 3/8`, `ram = 1/4` (`gate_bracket_w11_three`). -/
theorem gate_bracket_padic_three :
    ((2 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 splitType
        ∧ genuineDensity ℤ_[3] 2 splitType ≤ 71 / 81)
    ∧ ((1 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 inertType
        ∧ genuineDensity ℤ_[3] 2 inertType ≤ 62 / 81)
    ∧ ((1 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 2 ramType
        ∧ genuineDensity ℤ_[3] 2 ramType ≤ 2 / 3) := by
  obtain ⟨hs, hi, hr⟩ := lowers_padic_three
  obtain ⟨⟨-, hs'⟩, ⟨-, hi'⟩, ⟨-, hr'⟩⟩ := bracket_two hs hi hr
  refine ⟨⟨hs, ?_⟩, ⟨hi, ?_⟩, ⟨hr, ?_⟩⟩ <;> linarith

/-- **W-11 containment, q = 2**: `q/(2(q+1)) = 1/3` (split, inert) and `1/(q+1) = 1/3` (ram)
all lie strictly inside the certified brackets. -/
theorem gate_bracket_w11_two :
    ((1 : ℝ) / 4 ≤ 1 / 3 ∧ (1 : ℝ) / 3 ≤ 11 / 16)
    ∧ ((1 : ℝ) / 4 ≤ 1 / 3 ∧ (1 : ℝ) / 3 ≤ 11 / 16)
    ∧ ((1 : ℝ) / 16 ≤ 1 / 3 ∧ (1 : ℝ) / 3 ≤ 1 / 2) := by
  norm_num

/-- **W-11 containment, q = 3**: `q/(2(q+1)) = 3/8` (split, inert) and `1/(q+1) = 1/4` (ram)
all lie strictly inside the certified brackets. -/
theorem gate_bracket_w11_three :
    ((2 : ℝ) / 9 ≤ 3 / 8 ∧ (3 : ℝ) / 8 ≤ 71 / 81)
    ∧ ((1 : ℝ) / 9 ≤ 3 / 8 ∧ (3 : ℝ) / 8 ≤ 62 / 81)
    ∧ ((1 : ℝ) / 81 ≤ 1 / 4 ∧ (1 : ℝ) / 4 ≤ 2 / 3) := by
  norm_num

end BracketPadic

section AxCheck

-- Every gate must be Lean core ONLY (`propext`, `Classical.choice`, `Quot.sound`).
#print axioms Uniformity.Density.genuineDensity_linear_eq_one
#print axioms Uniformity.Density.genuineDensity_one_of_ne
#print axioms Uniformity.Density.gate_sigma_separation_one
#print axioms Uniformity.Density.typeOf_mul_linear
#print axioms Uniformity.Density.typeOf_split_of_unit
#print axioms Uniformity.Density.gate_split_lower
#print axioms Uniformity.Density.gate_padic_two
#print axioms Uniformity.Density.genuineDensity_two_linType_eq_zero
#print axioms Uniformity.Density.gate_sigma_separation_two
#print axioms Uniformity.Density.decidedSeq_tendsto
#print axioms Uniformity.Density.possibleSeq_tendsto
#print axioms Uniformity.Density.upperDensity_eq_of_drainage
#print axioms Uniformity.Density.genuineDensity_le_upperDensity
#print axioms Uniformity.Density.sum_genuineDensity_le_one
#print axioms Uniformity.Density.card_res
#print axioms Uniformity.Density.UniformityStatement.toPadic
-- follow-up unit (2026-08-13): the certificates and the brackets
#print axioms Uniformity.Density.norm_quad
#print axioms Uniformity.Density.typeOf_ram_of_eisenstein
#print axioms Uniformity.Density.typeOf_inert_of_anisotropic
#print axioms Uniformity.Density.gate_split_lower_sharp
#print axioms Uniformity.Density.gate_ram_lower
#print axioms Uniformity.Density.lowers_padic_two
#print axioms Uniformity.Density.lowers_padic_three
#print axioms Uniformity.Density.bracket_two
#print axioms Uniformity.Density.gate_bracket_padic_two
#print axioms Uniformity.Density.gate_bracket_padic_three
#print axioms Uniformity.Density.gate_bracket_w11_two
#print axioms Uniformity.Density.gate_bracket_w11_three

end AxCheck

end Uniformity.Density
