/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H01
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Uniformity.ChapH.H06 — the A2 refutation: the genre DATUM set is INFINITE

**Chapter H, NODE H.06** (`blueprint/CHAP-H_general_induction.md` §3). The second half of the
corrected `GENHN.CLASS`(ii). H.05 proves that at fixed degree `n` there are finitely many genre
*schemas* `(e₁, f₁, μ)`; this node proves that the *data* those schemas carry are genuinely
INFINITE, so the two readings of the clause are distinguishable.

Fix `Q = 2` and the schema `(e₁, f₁, μ) = (2, 1, 2)` (genre E at `n = 4`). Every odd slope
numerator `h = 2t + 1` gives an admissible datum — `gcd(2t+1, 2) = 1` is exactly oddness — and
distinct `t` give distinct data, so `genreE2 : ℕ → GenreDatum` is injective and the schema's fiber
is infinite.

DEPENDS: H.01.

SOURCE: `EFF.GENHN.07`, the A2 adjudication transcribed verbatim: *"GENHN.CLASS explicitly includes
`Q` and `h` in `G`, while its finiteness proof counts only discrete schemas
`(e_1,f_1,μ,entry-family)`. For fixed `n=4, Q=2`, every positive odd `h` gives a distinct datum
`(2; 2,1,2; h, entry)` once `N ≥ 2h+1`. Thus the declared data set is infinite."*

**⚠ WHY THIS NODE EXISTS** (blueprint). The corrected scope of `GENHN.CLASS`(ii) is only
*checkable* if both halves are landed: finitely many schemas (H.05) and infinitely many data (this
node). Landing only H.05 would leave the reader unable to tell the corrected clause from the
refuted one. The finiteness defect was found by a decorrelated-model audit, not by any battery row
(the battery sweeps fixed `(q, N, h)` while the counterexample is a family over `h`); this node is
the Lean-side confirmation of the refutation half, and it is unconditional.

**Repair record [A-H.1/D3].** The committed `hcop` field cited `Nat.coprime_two_right_iff_odd`,
which does not exist at the pin (`v4.31.0`); the lemma there is
`Nat.coprime_two_right : n.Coprime 2 ↔ Odd n` (`Mathlib/Data/Nat/Prime/Basic.lean`). The field is
landed in the repaired form `Nat.coprime_two_right.2 ⟨t, rfl⟩`. Stale-mathlib-name class, no
semantic content.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The genre-E datum at `Q = 2` with slope numerator `2t+1`. -/
def genreE2 (t : ℕ) : GenreDatum where
  Q := 2
  e₁ := 2
  f₁ := 1
  μ := 2
  h := 2 * t + 1
  hQ := le_refl 2
  he₁ := by omega
  hh := by omega
  hkey := by omega
  hmul := le_refl 2
  hcop := Nat.coprime_two_right.2 ⟨t, rfl⟩

/-- Distinct `t` give distinct genre data: the `h` fields `2t+1` already separate them. -/
theorem genreE2_injective : Function.Injective genreE2 := by
  intro s t hst
  have hh : (genreE2 s).h = (genreE2 t).h := congrArg GenreDatum.h hst
  simp only [genreE2] at hh
  omega

/-- **The A2 refutation**: the set of genre data over the single schema
`(Q, e₁, f₁, μ) = (2, 2, 1, 2)` is infinite. Hence `GENHN.CLASS`(ii)'s finiteness holds of the
SCHEMA set (H.05) and fails of the DATUM set. -/
theorem infinite_genreDatum_of_schema :
    {G : GenreDatum | G.Q = 2 ∧ G.e₁ = 2 ∧ G.f₁ = 1 ∧ G.μ = 2}.Infinite :=
  Set.infinite_of_injective_forall_mem genreE2_injective (fun _ => ⟨rfl, rfl, rfl, rfl⟩)

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.genreE2
#print axioms Uniformity.Density.Induction.genreE2_injective
#print axioms Uniformity.Density.Induction.infinite_genreDatum_of_schema

end AxCheck
