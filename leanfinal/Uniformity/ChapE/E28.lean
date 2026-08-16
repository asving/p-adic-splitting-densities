/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E02
import Uniformity.ChapH.H51

/-!
# Uniformity.ChapE.E28 — rung class separation and the single-class minimum

**Chapter E, NODE E.28** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §6 — the slot layer at a
rung), ENV-E1 (the arithmetic arena: pure exponent bookkeeping, no local base `O`).

`(SLOT₂)` Step 2 / R1-b Step 2 at an arbitrary rung `R = (ℓ, g, u, T)` (E.01) — *"the `(e₁, f₁)`
pattern of GENHN-2 with `(e₁, f₁) ↦ (ℓ, d_r)`"*, i.e. H.51/H.52's content re-lettered:

* **`rung_class_sep`** — two slots in different classes mod `ℓ` can never produce the same term
  value: `ℓ·v + s·u ≠ ℓ·v′ + s′·u` whenever `s % ℓ ≠ s′ % ℓ`. Cross-class ties are impossible,
  which is what makes the slot minimum *exact* rather than merely attained.
* **`rung_min_class`** — inside the class of `s₀` (`ℓ·m₀ + s₀·u = k`, `s₀ < ℓ`), the slot
  `s = s₀ + ℓ·t` carries the value `k` iff its height is `w s = m₀ − t·u`, and this forces
  `t·u ≤ m₀` (so the criterion is honest in `ℕ`: the subtraction never truncates). Both
  conjuncts are proved from the single equation `w s + t·u = m₀`.

Together these are the two halves of the corpus's Step 2/Step 3 sentence: the minimizing slots
of a family `s ↦ ℓ·w s + s·u` all lie in ONE residue class `s₀ + ℓ·{0,…,g−1}` (nothing outside
that class can even tie, by `rung_class_sep`), and within the class the attainers are exactly
the slots meeting the height criterion (`rung_min_class`).

**WHERE THE COPRIMALITY ENTERS.** `rung_class_sep` is H.51's `class_sep` with the roles swapped:
H.51 separates `i·h mod e` under `Coprime h e`; here `(h, e) ↦ (u, ℓ)` and the hypothesis is
E.01's `hcop : Nat.Coprime u ℓ` field, so the tooth HE7-T-SLOT2TIE (`gcd(u, ℓ) ≠ 1` ⟹ classes
share heights and exactness fails) has a *structural* hypothesis, not a side condition. Since
the signed slot bound is `s < R.slotCount = ℓ·g` — NOT `s < ℓ` — H.51 is applied to the reduced
residues `s % ℓ`, `s′ % ℓ` (which are `< ℓ` because `1 ≤ ℓ`), and `Nat.mod_mul_mod` carries the
reduction through the multiplication by `u`.

The signed hypotheses `hs : s < R.slotCount`, `hs' : s' < R.slotCount` (in `rung_class_sep`) and
`hs₀ : s₀ < R.ℓ` (in `rung_min_class`) are carried but unconsumed: separation holds for ALL
`s, s′` in distinct classes mod `ℓ`, and the class criterion is a cancellation that never looks
at where `s₀` sits. The landed statements are the signed ones verbatim (see the
`linter.unusedVariables` notes); no strength is lost — the slot bounds are the consumers' data,
recorded in the signature because E.29 supplies them.

DEPENDS: E.01, E.02 (`slotCount`), **H.51** (`class_sep`) · mathlib `Nat.mul_add_mod`,
`Nat.mod_mul_mod`, `Nat.eq_of_mul_eq_mul_left`.

SOURCE: `EFF.HE7.11` (Step 2, verbatim: "`ℓ·dv(c_s) + s·u ≡ s·u (mod ℓ)`, and `s ↦ s·u mod ℓ`
is a bijection of `ℤ/ℓ` because `gcd(u, ℓ) = 1` … The minimum … is therefore attained inside a
single class `s₀ + ℓ·{0,…,d_r−1}` — exactly ℓ classes of exactly d_r slots each"; Step 3's
attaining criterion "iff `dv(c_{s₀+ℓt}) = m₀ − tu`"); `EFF.HE7.110` (Step 2, "twist-free …
verbatim").

TEETH: HE7-T-SLOT2TIE (fired: at `gcd(u, ℓ) ≠ 1` classes share heights and exactness fails) —
a Lean theorem here, with the tooth's hypothesis living in E.01's `hcop` field.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- `hs`/`hs'` are the consumers' slot bounds (E.29 supplies them); separation itself needs only
-- the class hypothesis `hmod`, so they are carried unconsumed.
set_option linter.unusedVariables false in
/-- **E.28 (i) — rung class separation** (`EFF.HE7.11` Step 2). Slots in distinct residue
classes mod `ℓ` never tie: `ℓ·v + s·u ≠ ℓ·v′ + s′·u`. This is H.51's `class_sep` with
`(h, e) ↦ (u, ℓ)`, run on the reduced residues. -/
theorem rung_class_sep (R : RungDatum) {s s' v v' : ℕ}
    (hs : s < R.slotCount) (hs' : s' < R.slotCount)
    (hmod : s % R.ℓ ≠ s' % R.ℓ) :
    R.ℓ * v + s * R.u ≠ R.ℓ * v' + s' * R.u := by
  intro heq
  -- reduce the tie mod `ℓ`: the `ℓ·v` carries drop out
  have h1 : s * R.u % R.ℓ = s' * R.u % R.ℓ := by
    have h0 : (R.ℓ * v + s * R.u) % R.ℓ = (R.ℓ * v' + s' * R.u) % R.ℓ := by rw [heq]
    rwa [Nat.mul_add_mod, Nat.mul_add_mod] at h0
  -- H.51 at `(h, e) ↦ (u, ℓ)`, applied to the reduced residues `s % ℓ`, `s' % ℓ`
  have hlt : s % R.ℓ < R.ℓ := Nat.mod_lt _ R.hℓ
  have hlt' : s' % R.ℓ < R.ℓ := Nat.mod_lt _ R.hℓ
  have hmul : (s % R.ℓ) * R.u % R.ℓ = (s' % R.ℓ) * R.u % R.ℓ := by
    rw [Nat.mod_mul_mod, Nat.mod_mul_mod]; exact h1
  exact hmod (Uniformity.Density.Induction.class_sep R.hcop hlt hlt' hmul)

-- `hs₀` is the class-representative bound the consumers carry (it is what makes `s₀` THE class
-- index); the cancellation below is valid for any `s₀`, so the hypothesis is unconsumed here.
set_option linter.unusedVariables false in
/-- **E.28 (ii) — the single-class attainment criterion** (`EFF.HE7.11` Step 3). With
`ℓ·m₀ + s₀·u = k` and `s = s₀ + ℓ·t`, the slot `s` carries the value `k` exactly when its height
is `w s = m₀ − t·u`; and the subtraction is honest, `t·u ≤ m₀`. -/
theorem rung_min_class (R : RungDatum) {s k m₀ s₀ t : ℕ}
    (hks : R.ℓ * m₀ + s₀ * R.u = k) (hs₀ : s₀ < R.ℓ)
    (hattain : s = s₀ + R.ℓ * t) (w : ℕ → ℕ)
    (hval : R.ℓ * w s + s * R.u = k) :
    w s = m₀ - t * R.u ∧ t * R.u ≤ m₀ := by
  subst hattain
  -- regroup: the slot's `s₀·u` matches the class value's, leaving `ℓ·(w s + t·u) = ℓ·m₀`
  have hgroup : R.ℓ * (w (s₀ + R.ℓ * t) + t * R.u) + s₀ * R.u = R.ℓ * m₀ + s₀ * R.u := by
    rw [hks]
    rw [← hval]; ring
  have hmul : R.ℓ * (w (s₀ + R.ℓ * t) + t * R.u) = R.ℓ * m₀ := Nat.add_right_cancel hgroup
  have hsum : w (s₀ + R.ℓ * t) + t * R.u = m₀ :=
    Nat.eq_of_mul_eq_mul_left R.hℓ hmul
  exact ⟨Nat.eq_sub_of_add_eq hsum, hsum ▸ Nat.le_add_left _ _⟩

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.rung_class_sep
#print axioms Uniformity.Density.Ladder.rung_min_class

end AxCheck
