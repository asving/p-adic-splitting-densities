/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C07

/-!
# Uniformity.ChapC.C08 — `dvOnSide_modEq`, `dvSideLen_eq`: argmin spacing and the length law

**Chapter C, NODE C.08** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). **ENV-C1**. Two signed declarations.

A `dv`-side at slope `−u/ℓ` **in lowest terms** carries its abscissae in a single residue class
mod `ℓ`: this is `EFF.HE6.10`'s *"sides have dv-slope `λ = u/ℓ` in lowest terms and length
`L_λ = ℓd_λ`"*, and it is what makes C.07's floored `ℕ`-division `dvSideDeg = dvSideLen / ℓ` exact.

* `dvOnSide_modEq F hℓ hcop hj hj'` — any two on-side abscissae satisfy `j ≡ j' [MOD ℓ]`.
* `dvSideLen_eq F hℓ hcop h` — hence `dvSideLen = ℓ * dvSideDeg`, with no `ℕ`-truncation.

## The proof, and the one place it is *shorter* than its level-1 twin

Both clauses replay B.17/B.20(d) one level up, with C.06's `dvHgt`/`dvSupp` in place of B.11's
`npHgt` and B.14's `suppVal`. The mechanism is the same three steps: two attained equalities give
`ℓ·H + u·j = ℓ·H' + u·j'` in `ℕ` (after naming the two finite heights), transport to `ℤ` turns
that into `(ℓ : ℤ) ∣ u·(j' − j)`, and `Nat.Coprime u ℓ` strips the `u`.

The twin B.17 needs a **finiteness hypothesis** `htop : suppVal φ f u ℓ ≠ ⊤`, because B.16's
`OnSide` is the bare attainment equation and an abscissa can attain `⊤ = ⊤`. C.07's `DvOnSide`
carries the finiteness guard `dvHgt F f j ≠ ⊤` in its own second conjunct (the deviation from
B.16 that C.07's header records), so C.08's signature needs no `htop` and the proof reads the
guard straight off `hj.2`/`hj'.2`. This is why B.17 is *replayed, not consumed* — the blueprint's
DEPENDS says so, for the different reason that B.17's constant is `suppVal`-specific.

## Signed-but-unconsumed hypotheses (kept, unweakened)

`hℓ : 0 < ℓ` is **not used** by either proof. In B.17 it is what makes `ℓ • ⊤ = ⊤` in step 1 —
the step `DvOnSide`'s guard already supplies here. Both statements are in fact true at `ℓ = 0`
(where `Nat.Coprime u 0` forces `u = 1`, the two equations collapse to `j = j'`, and
`j ≡ j' [MOD 0]` *is* `j = j'`; and `dvSideLen = ℓ * dvSideDeg` reads `0 = 0` because `0 ∣ n`
forces `n = 0`). Signatures are frozen (B.18's precedent for signed-but-unused side conditions),
so `hℓ` is kept and the file carries `set_option linter.unusedVariables false`.

## Helpers kept private

`dvOnSide_nat_eq` (B.17 step 2's analogue) and `dvOnSide_of_mem_dvSideSet` (B.20's
`onSide_of_mem_sideSet` analogue) are `private`: no landed chapter-C node names either, and
GC-6.5 forbids growing a node's public surface. The level-1 twins are public because B.19/B.20
consume them across files; should C.25/C.26/C.55 want the `Finset`-membership projection, that is
a RE-PLAN item, not a silent addition here.

**DEPENDS.** C.06 (`dvHgt`, `dvSupp`) · C.07 (`DvOnSide`, `dvSideSet`, `dvSideMin`, `dvSideMax`,
`dvSideDeg`, `dvSideLen`) · B.17 (the proof pattern, replayed not consumed) · B.20(d) (the
length-law template) — by committed node ID (GC-13(b)). Imports: `Uniformity.ChapC.C07`. Mathlib:
`WithTop.ne_top_iff_exists`, `Nat.isCoprime_iff_coprime`, `IsCoprime.dvd_of_dvd_mul_left`,
`Nat.modEq_iff_dvd`, `Nat.modEq_iff_dvd'`, `Nat.mul_div_cancel'`.

**PROOF.** The blueprint's three steps. (1) Name the two finite heights and clear the `ℕ∞`
equation to `ℕ`. (2) Coprimality gives `ℓ ∣ j' − j` — B.17 step 3, through `ℤ`. (3) `min'` and
`max'` are members of `dvSideSet`, hence on-side, so step 2 applies to them and the division
defining `dvSideDeg` is exact.

SOURCE: `EFF.HE6.10` (`L_λ = ℓ·d_λ`); B.17/B.20 (the level-1 twin whose proof is replayed).

**TEETH.** signed non-applicable (guarded numerically by the §13 frame audit); nothing here is
dischargeable at these binders anyway — an abstract `KeyFrame O π` and an abstract `f` offer no
numeral (the D7 consequence recorded at C.15).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helpers (B.17 step 2 and B.20's membership projection, one level up) -/

/-- **C.08 step 1–2 (private).** Once the two `dv`-heights are named as naturals `H`, `H'`, the
equality of the two cleared level supports is a plain `ℕ`-equation. No hypothesis on `u` or `ℓ`
is needed. B.17's `onSide_nat_eq`, at C.06's carrier. -/
private theorem dvOnSide_nat_eq {F : KeyFrame O π} {u ℓ : ℕ} {f : Polynomial O} {j j' H H' : ℕ}
    (hH : dvHgt F f j = (H : ℕ∞)) (hH' : dvHgt F f j' = (H' : ℕ∞))
    (hj : DvOnSide F f u ℓ j) (hj' : DvOnSide F f u ℓ j') :
    ℓ * H + u * j = ℓ * H' + u * j' := by
  have hja : dvSupp F f u ℓ = ℓ • dvHgt F f j + (u * j : ℕ∞) := hj.1
  have hjb : dvSupp F f u ℓ = ℓ • dvHgt F f j' + (u * j' : ℕ∞) := hj'.1
  have e : ℓ • (H : ℕ∞) + (u * j : ℕ∞) = ℓ • (H' : ℕ∞) + (u * j' : ℕ∞) := by
    rw [← hH, ← hH', ← hja, hjb]
  have e' : ((ℓ * H + u * j : ℕ) : ℕ∞) = ((ℓ * H' + u * j' : ℕ) : ℕ∞) := by
    push_cast
    simpa [nsmul_eq_mul] using e
  exact_mod_cast e'

/-- **C.08, auxiliary (private).** Membership in C.07's `dvSideSet` projects onto the `DvOnSide`
predicate. `dvSideSet` is a `Finset.filter` over `Finset.range (f.natDegree + 1)` with `Classical`
decidability, so this is `Finset.mem_filter` modulo that instance. B.20's
`onSide_of_mem_sideSet`, one level up. -/
private theorem dvOnSide_of_mem_dvSideSet {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  have hj' : j ∈ Finset.filter (DvOnSide F f u ℓ) (Finset.range (f.natDegree + 1)) := hj
  exact (Finset.mem_filter.mp hj').2

/-! ### The signed declarations -/

-- `hℓ` is a signed hypothesis of the frozen statement and is not consumed: `DvOnSide`'s own
-- finiteness guard replaces B.17's step-1 use of it (see the header). It is kept, unweakened.
set_option linter.unusedVariables false in
/-- **C.08 (a) — the `ℓ`-spacing of a `dv`-side.** Any two abscissae on the side of slope `−u/ℓ`
in lowest terms are congruent mod `ℓ`: the on-side abscissae are the lattice points `j₀ + ℓk` of
`EFF.HE6.10`, one level up from B.17. -/
theorem dvOnSide_modEq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} {j j' : ℕ} (hj : DvOnSide F f u ℓ j) (hj' : DvOnSide F f u ℓ j') :
    j ≡ j' [MOD ℓ] := by
  obtain ⟨H, hH⟩ := WithTop.ne_top_iff_exists.mp hj.2
  obtain ⟨H', hH'⟩ := WithTop.ne_top_iff_exists.mp hj'.2
  have key : ℓ * H + u * j = ℓ * H' + u * j' := dvOnSide_nat_eq hH.symm hH'.symm hj hj'
  have keyZ : (ℓ : ℤ) * (H : ℤ) + (u : ℤ) * (j : ℤ) = (ℓ : ℤ) * (H' : ℤ) + (u : ℤ) * (j' : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key
  have hdvd : (ℓ : ℤ) ∣ (u : ℤ) * ((j' : ℤ) - (j : ℤ)) := ⟨(H : ℤ) - (H' : ℤ), by linarith⟩
  have hcop' : IsCoprime (ℓ : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact Nat.modEq_iff_dvd.mpr (hcop'.dvd_of_dvd_mul_left hdvd)

-- `hℓ` is signed and unconsumed here too; it travels only into `dvOnSide_modEq`, which ignores it.
set_option linter.unusedVariables false in
/-- **C.08 (b) — the length law `L_λ = ℓ·d_λ`.** The `ℕ`-division defining C.07's `dvSideDeg` is
exact, because (a) makes `ℓ` divide `dvSideMax − dvSideMin`. B.20(d) (`sideMax_eq`) one level up,
in the `dvSideLen` form D5 determined. -/
theorem dvSideLen_eq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} (h : (dvSideSet F f u ℓ).Nonempty) :
    dvSideLen F f u ℓ h = ℓ * dvSideDeg F f u ℓ h := by
  have hmin : dvSideMin F f u ℓ h ∈ dvSideSet F f u ℓ := Finset.min'_mem _ _
  have hmax : dvSideMax F f u ℓ h ∈ dvSideSet F f u ℓ := Finset.max'_mem _ _
  have hle : dvSideMin F f u ℓ h ≤ dvSideMax F f u ℓ h := Finset.min'_le _ _ hmax
  have hdvd : ℓ ∣ dvSideMax F f u ℓ h - dvSideMin F f u ℓ h :=
    (Nat.modEq_iff_dvd' hle).mp
      (dvOnSide_modEq F hℓ hcop (dvOnSide_of_mem_dvSideSet hmin) (dvOnSide_of_mem_dvSideSet hmax))
  rw [dvSideLen, dvSideDeg, Nat.mul_div_cancel' hdvd]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dvOnSide_modEq
#print axioms Uniformity.Density.Tower.dvSideLen_eq

end AxCheck
