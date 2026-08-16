/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D24
import Uniformity.ChapB.B15

/-!
# Uniformity.ChapD.D25a — `(C6-lift)` clauses 1–2: integrality, degree, exact height

**Chapter D, NODE D.25**, first half (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1 gauge
layer; **SPLIT MANDATED → 2**, this file being `D25a` = clauses 1–2 plus the zero branch, and
`Uniformity.ChapD.D25b` = clauses 3–4). Amendments A-1 and A-D.1 govern; the SIGNATURE is the
A-D.1/D-D4 + D-D6 re-signed one (`π` explicit and first at every occurrence, the four clauses
spelled as the four sibling names). ENV-D4 — the concrete level-1 arena over the bundle.
Three signed declarations in this file.

*`(C6-lift)` properties on the live domain.* Under `hσ : ∀ a, residue O (σ a) = a`,
`hσ0 : σ 0 = 0`, `hπ : Irreducible π`, `he : 0 < e₁`, `hcop : Nat.Coprime h e₁`, `hf : 0 < f₁`
and the **live-domain hypothesis** `hM : e₁ * f₁ * h < M`:

1. **integrality exponents** (`liftC6_exp_nonneg`): `∀ r : Fin f₁, 0 ≤ aexp e₁ h M − r·h`, so
   D.24's `.toNat` is EXACT on the live domain — this is what licences reading `liftC6` at all;
2. **degree and exact height** (`liftC6_spec`, for `l ≠ 0`): `natDegree < e₁ * f₁` (`= D′`) and
   `suppVal X (liftC6 …) h e₁ = (M : ℕ∞)`. The `(u,ℓ) = (h,e₁)` cleared support value IS the
   corpus's `dv₁` — chapter B's B.14 at `φ = X`, read through B.15's `npHgt_X`;
3. **the zero branch** (`liftC6_zero`): `liftC6 π e₁ h σ M 0 = 0` (empty support, valuation
   `⊤`), which needs only `hσ0`.

Clauses 3 (the A6/GENTOW6 x-support pin) and 4 (`(C6-x-free)`) are `D25b`.

## The identification with `dv₁` (what clause 2 actually asserts)

`Uniformity.Density.Leaf.suppVal X L h e₁` unfolds to
`inf_{j ≤ L.natDegree} (e₁ • npHgt X L j + h·j)`, and at `φ = X` B.15's `npHgt_X` reads
`npHgt X L j = addVal O (L.coeff j)`. So the claim is: **every occupied slot of `L` has
`(h,e₁)`-weight exactly `M`**, and at least one slot is occupied. Slot `j = i(M) + e₁r` carries
`σ(λ_r)·π^{a(M)−rh}` with `σ(λ_r)` a unit (its residue is `λ_r ≠ 0`), so its weight is

  `e₁·(a(M) − rh) + h·(i(M) + e₁r) = e₁·a(M) + h·i(M) = M`

by D.13's exact-height identity — the `−e₁rh` and `+he₁r` cancel, which is the whole content of
the corpus's "every present term has weight `M` exactly". Unoccupied slots contribute
`e₁ • ⊤ + c = ⊤` (this is where `0 < e₁` is consumed) and cannot lower the infimum.

## Faithfulness

* *the live domain is a hypothesis, never a side condition.* `hM : e₁·f₁·h < M` is the corpus's
  `M > D′h` with `D′ = e₁f₁`. Below it the definition's `.toNat` truncates and NO lemma of this
  chapter reads `liftC6` — `EFF.T1.01`'s "No full `K₁`-slot is asserted at `k ≤ D′h`" is
  transcribed as the absence of any sub-domain lemma, not as a weaker statement here.
* *the `h = 0` corner needs no extra hypothesis* (blueprint PROOF step 1 flagged `hh : 0 < h`
  for the cross-read, §13 item 6): the clause-1 argument runs over `ℤ` as
  `(r·h)·e₁ + i(M)·h ≤ (f₁−1)·h·e₁ + (e₁−1)·h = e₁f₁h − h ≤ e₁f₁h < M`, whose every step is
  valid at `h = 0`. **`hh : 0 < h` is NOT needed and is NOT added** — the frozen signature
  stands as signed, and the §13 item-6 question is answered negatively.
* *four hypotheses of `liftC6_exp_nonneg` are not consumed* (`hπ`, `hf`, `hσ`, `hσ0`): the
  integrality of the π-exponents is pure exponent arithmetic. They are signed hypotheses of a
  frozen statement and are KEPT (the statement is not weakened); the unused-variable linter is
  switched off for that one declaration, on the B.15 precedent
  (`Uniformity.Density.Leaf.suppVal_X_iff` does exactly this with `hf`/`hn`).

DEPENDS: D.13 (`iexp`, `aexp`, `iexp_aexp_spec`) · D.24 (`liftC6`) · B.07/B.08 (`gaussVal`,
reached through B.11) · B.11 (`npHgt`) · B.14 (`suppVal`) · B.15 (`npHgt_X`) · mathlib
`Polynomial.finsetSum_coeff`, `Polynomial.coeff_C_mul_X_pow`,
`Polynomial.natDegree_sum_le_of_forall_le`, `Polynomial.natDegree_C_mul_X_pow_le`,
`Polynomial.le_natDegree_of_ne_zero`, `IsDiscreteValuationRing.addVal_mul`,
`IsDiscreteValuationRing.addVal_eq_zero_iff`, `Irreducible.addVal_pow`,
`IsLocalRing.notMem_maximalIdeal`, `IsLocalRing.residue_eq_zero_iff`, `ENat.mul_top` — all
name-verified at the v4.31.0 pin.

**PROOF.** The corpus's own steps (`EFF.T1.20`'s derivation, verbatim in substance), through
five private helpers that read `liftC6` slotwise (`coeff_liftC6`, `coeff_liftC6_at`,
`exists_of_coeff_ne_zero`, `isUnit_sigma`, `smul_top_add`):

1. Clause 1 over `ℤ`: multiply the goal `r·h ≤ a(M)` by `e₁ > 0` and use D.13's
   `i(M)h + a(M)e₁ = M` with `i(M) < e₁`, `r < f₁`, `e₁f₁h < M` — `nlinarith` from the two
   sign facts `(f₁−1−r)·h·e₁ ≥ 0` and `(e₁−1−i(M))·h ≥ 0`.
2. Degree: `natDegree_sum_le_of_forall_le` with the slot bound
   `i(M) + e₁r < e₁(r+1) ≤ e₁f₁`.
3. Exact height: `le_antisymm` on the `suppVal` infimum. `≤` exhibits the slot of any `r₀` with
   `λ_{r₀} ≠ 0` (in range by `le_natDegree_of_ne_zero`); `≥` splits each `j` on whether
   `L.coeff j = 0` (then the term is `⊤`) or not (then `j` is a slot and the term is exactly
   `M`, by the weight computation above cast through `nsmul_eq_mul`).
4. The zero branch is `simp [liftC6, hσ0]`.

SOURCE: `EFF.T1.20` (clauses 1–2 of the boxed `(C6-lift)` + derivation); `EFF.T1.30` (the A6
zero/nonzero split); `EFF.T1.25` (A1 row 1: `GENHN-LIFT` is "**Verbatim** on `M > D′h`: same
component formula, integrality, degree, exact height, and residue" — the OUT-interface).

**TEETH.** T1 §4.2 checks 1 (live-domain boundary), 7 and 10 → **Lean theorem** (this node);
the A1/A6 consumption regressions → §12 (retained; PARI-side). Nothing is `decide`-scored here
(an abstract bundle).

ENVIRONMENT: ENV-D4 (CHAP-B's ENV-A′ MINUS its `{π : O}` — per defect D-D4 every declaration
binds `π` itself, explicitly and first, exactly as D.24 does).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open IsLocalRing Polynomial IsDiscreteValuationRing

-- ENV-D4 (blueprint §0.1) = CHAP-B's ENV-A′, MINUS its `{π : O}`: per defect D-D4 the nodes of
-- this file bind `π` themselves, explicitly and first.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Slotwise read of `liftC6`: `Polynomial.coeff` commutes with the defining sum, and each
summand is a `C _ * X ^ _`. Private helper. -/
private theorem coeff_liftC6 (π : O) {f₁ : ℕ} (e₁ h : ℕ) (σ : ResidueField O → O) (M : ℕ)
    (l : Fin f₁ → ResidueField O) (j : ℕ) :
    (liftC6 π e₁ h σ M l).coeff j
      = ∑ r : Fin f₁, if j = iexp e₁ h M + e₁ * (r : ℕ)
          then σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat else 0 := by
  simp only [liftC6, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

/-- The coefficient AT a slot `i(M) + e₁r`: the sum collapses because `r ↦ i(M) + e₁r` is
injective for `0 < e₁` (distinct residues mod `e₁` — D.24's faithfulness note). Private
helper. -/
private theorem coeff_liftC6_at (π : O) {f₁ : ℕ} (e₁ h : ℕ) (he : 0 < e₁)
    (σ : ResidueField O → O) (M : ℕ) (l : Fin f₁ → ResidueField O) (r : Fin f₁) :
    (liftC6 π e₁ h σ M l).coeff (iexp e₁ h M + e₁ * (r : ℕ))
      = σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat := by
  rw [coeff_liftC6, Finset.sum_eq_single r]
  · simp
  · intro b _ hb
    refine if_neg fun heq => hb (Fin.ext ?_)
    exact (Nat.eq_of_mul_eq_mul_left he (Nat.add_left_cancel heq)).symm
  · intro hb
    exact absurd (Finset.mem_univ r) hb

/-- A nonzero coefficient of `liftC6` sits at a slot with a nonzero coordinate — the
contrapositive of the two ways a slot can vanish (off the lattice, or `σ 0 = 0`). Private
helper. -/
private theorem exists_of_coeff_ne_zero (π : O) {f₁ : ℕ} (e₁ h : ℕ)
    (σ : ResidueField O → O) (hσ0 : σ 0 = 0) (M : ℕ) (l : Fin f₁ → ResidueField O) {j : ℕ}
    (hj : (liftC6 π e₁ h σ M l).coeff j ≠ 0) :
    ∃ r : Fin f₁, j = iexp e₁ h M + e₁ * (r : ℕ) ∧ l r ≠ 0 := by
  by_contra hcon
  refine hj ?_
  rw [coeff_liftC6]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hjr : j = iexp e₁ h M + e₁ * (r : ℕ)
  · have hlr : l r = 0 := by
      by_contra hlr
      exact hcon ⟨r, hjr, hlr⟩
    rw [if_pos hjr, hlr, hσ0, zero_mul]
  · exact if_neg hjr

/-- A lifted nonzero coordinate is a unit: its residue is the coordinate itself, hence nonzero,
so it escapes the maximal ideal. Private helper. -/
private theorem isUnit_sigma {f₁ : ℕ} (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (l : Fin f₁ → ResidueField O) (r : Fin f₁)
    (hr : l r ≠ 0) : IsUnit (σ (l r)) := by
  refine notMem_maximalIdeal.mp fun hmem => hr ?_
  rw [← hσ (l r), residue_eq_zero_iff]
  exact hmem

/-- With `0 < ℓ`, an empty abscissa (`npHgt = ⊤`) contributes `⊤` to the `suppVal` infimum.
Private helper (B32b's, re-derived here: chapter B's copy is private to its own file). -/
private theorem smul_top_add {ℓ : ℕ} (hℓ : 0 < ℓ) (c : ℕ∞) : ℓ • (⊤ : ℕ∞) + c = ⊤ := by
  rw [nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 hℓ.ne'), top_add]

-- `hπ`, `hf`, `hσ` and `hσ0` are signed hypotheses of the frozen statement: clause 1 is pure
-- exponent arithmetic and consumes none of them. Kept, not removed (the statement is not
-- weakened) — the B.15 precedent (`suppVal_X_iff` with `hf`/`hn`).
set_option linter.unusedVariables false in
/-- **D.25 clause 1 — integrality of the π-exponents on the live domain** (`EFF.T1.20`).
On `M > D′h = e₁f₁h` every exponent `a(M) − rh` with `r < f₁` is nonnegative, so D.24's
`.toNat` is EXACT wherever anything is claimed.

⚠ The `h = 0` corner (blueprint §13 item 6) needs NO extra hypothesis: the whole argument is
`(r·h)·e₁ + i(M)·h ≤ e₁f₁h − h < M`, valid at every `h`. -/
theorem liftC6_exp_nonneg (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) :
    ∀ r : Fin f₁, 0 ≤ aexp e₁ h M - (r : ℕ) * h := by
  intro r
  obtain ⟨hlt, hid⟩ := iexp_aexp_spec e₁ h he hcop (M : ℤ)
  have hrf : ((r : ℕ) : ℤ) + 1 ≤ (f₁ : ℤ) := by exact_mod_cast r.2
  have hie : ((iexp e₁ h M : ℕ) : ℤ) + 1 ≤ (e₁ : ℤ) := by exact_mod_cast hlt
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have he0 : (0 : ℤ) < (e₁ : ℤ) := by exact_mod_cast he
  have hMc : (e₁ : ℤ) * f₁ * h < (M : ℤ) := by exact_mod_cast hM
  rw [sub_nonneg]
  refine le_of_mul_le_mul_right ?_ he0
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ (f₁:ℤ) - 1 - (r:ℕ)) hh0) he0.le,
    mul_nonneg (by linarith : (0:ℤ) ≤ (e₁:ℤ) - 1 - ((iexp e₁ h M : ℕ) : ℤ)) hh0]

/-- **D.25 clause 2, zero branch** (`EFF.T1.20`, `EFF.T1.30`): the lift of the zero coordinate
vector is the zero polynomial (empty support, valuation `⊤`). Only `hσ0 : σ 0 = 0` is
consumed. -/
theorem liftC6_zero (π : O) (e₁ h f₁ : ℕ) (σ : ResidueField O → O) (hσ0 : σ 0 = 0) (M : ℕ) :
    liftC6 π e₁ h σ M (0 : Fin f₁ → ResidueField O) = 0 := by
  simp [liftC6, hσ0]

/-- **D.25 clauses 1–2 — degree and exact height on the live domain** (`EFF.T1.20`).
For a nonzero coordinate vector on `M > D′h`, the lift has `natDegree < e₁f₁ = D′` and its
`(u,ℓ) = (h,e₁)` cleared support value — the corpus's `dv₁`, i.e. chapter B's `suppVal` at
`φ = X` (B.14/B.15) — is EXACTLY `M`: every occupied slot has weight
`e₁(a(M) − rh) + h(i(M) + e₁r) = e₁a(M) + h·i(M) = M`, and the distinct `x`-exponents prevent
any cancellation. -/
theorem liftC6_spec (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → ResidueField O) (hl : l ≠ 0) :
    (liftC6 π e₁ h σ M l).natDegree < e₁ * f₁
    ∧ Uniformity.Density.Leaf.suppVal Polynomial.X (liftC6 π e₁ h σ M l) h e₁ = (M : ℕ∞) := by
  have hlt : iexp e₁ h M < e₁ := (iexp_aexp_spec e₁ h he hcop (M : ℤ)).1
  have hid : (iexp e₁ h M : ℤ) * h + aexp e₁ h M * e₁ = (M : ℤ) :=
    (iexp_aexp_spec e₁ h he hcop (M : ℤ)).2
  have hnn := liftC6_exp_nonneg π e₁ h f₁ hπ he hf hcop σ hσ hσ0 M hM
  have hidx : ∀ r : Fin f₁, iexp e₁ h M + e₁ * (r : ℕ) < e₁ * f₁ := by
    intro r
    have h1 : e₁ * ((r : ℕ) + 1) ≤ e₁ * f₁ := Nat.mul_le_mul_left _ r.2
    have h2 : iexp e₁ h M + e₁ * (r : ℕ) < e₁ * ((r : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    omega
  -- the slot weight: `e₁·(a(M) − rh) + h·(i(M) + e₁r) = e₁·a(M) + h·i(M) = M`
  have hweight : ∀ r : Fin f₁,
      e₁ * (aexp e₁ h M - (r : ℕ) * h).toNat + h * (iexp e₁ h M + e₁ * (r : ℕ)) = M := by
    intro r
    have hn : (((aexp e₁ h M - (r : ℕ) * h).toNat : ℕ) : ℤ) = aexp e₁ h M - ((r : ℕ) : ℤ) * h :=
      Int.toNat_of_nonneg (hnn r)
    have hz : ((e₁ * (aexp e₁ h M - (r : ℕ) * h).toNat
        + h * (iexp e₁ h M + e₁ * (r : ℕ)) : ℕ) : ℤ) = (M : ℤ) := by
      push_cast [hn]
      linarith [hid]
    exact_mod_cast hz
  have hunit : ∀ r : Fin f₁, l r ≠ 0 → IsUnit (σ (l r)) := fun r hr => isUnit_sigma σ hσ l r hr
  have hcoeffne : ∀ r : Fin f₁, l r ≠ 0 →
      (liftC6 π e₁ h σ M l).coeff (iexp e₁ h M + e₁ * (r : ℕ)) ≠ 0 := by
    intro r hr
    rw [coeff_liftC6_at π e₁ h he σ M l r]
    exact mul_ne_zero (hunit r hr).ne_zero (pow_ne_zero _ hπ.ne_zero)
  have haddval : ∀ r : Fin f₁, l r ≠ 0 →
      addVal O ((liftC6 π e₁ h σ M l).coeff (iexp e₁ h M + e₁ * (r : ℕ)))
        = (((aexp e₁ h M - (r : ℕ) * h).toNat : ℕ) : ℕ∞) := by
    intro r hr
    rw [coeff_liftC6_at π e₁ h he σ M l r, addVal_mul,
      addVal_eq_zero_iff.2 (hunit r hr), hπ.addVal_pow, zero_add]
  have hterm : ∀ r : Fin f₁, l r ≠ 0 →
      e₁ • Uniformity.Density.Leaf.npHgt Polynomial.X (liftC6 π e₁ h σ M l)
            (iexp e₁ h M + e₁ * (r : ℕ))
        + ((h * (iexp e₁ h M + e₁ * (r : ℕ)) : ℕ) : ℕ∞) = (M : ℕ∞) := by
    intro r hr
    rw [Uniformity.Density.Leaf.npHgt_X, haddval r hr, nsmul_eq_mul, ← Nat.cast_mul,
      ← Nat.cast_add, hweight r]
  refine ⟨?_, ?_⟩
  · have hdeg : (liftC6 π e₁ h σ M l).natDegree ≤ e₁ * f₁ - 1 := by
      simp only [liftC6]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
      refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
      have := hidx r
      omega
    have hpos : 0 < e₁ * f₁ := Nat.mul_pos he hf
    omega
  · obtain ⟨r₀, hr₀⟩ : ∃ r : Fin f₁, l r ≠ 0 := by
      by_contra hc
      apply hl
      funext r
      simp only [Pi.zero_apply]
      by_contra hlr
      exact hc ⟨r, hlr⟩
    simp only [Uniformity.Density.Leaf.suppVal]
    refine le_antisymm ?_ ?_
    · refine le_trans (Finset.inf_le (Finset.mem_range.2 ?_)) (le_of_eq (hterm r₀ hr₀))
      exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero (hcoeffne r₀ hr₀))
    · refine Finset.le_inf fun j _ => ?_
      by_cases hc : (liftC6 π e₁ h σ M l).coeff j = 0
      · rw [Uniformity.Density.Leaf.npHgt_X, hc, AddValuation.map_zero, smul_top_add he]
        exact le_top
      · obtain ⟨r, hjr, hr⟩ := exists_of_coeff_ne_zero π e₁ h σ hσ0 M l hc
        subst hjr
        exact le_of_eq (hterm r hr).symm

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.liftC6_exp_nonneg
#print axioms Uniformity.Density.Gauge.liftC6_zero
#print axioms Uniformity.Density.Gauge.liftC6_spec

end AxCheck
