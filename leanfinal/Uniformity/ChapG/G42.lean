/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G34
import Uniformity.ChapG.G39
import Uniformity.ChapG.G41

/-!
# Uniformity.ChapG.G42 — `card_splitStratum`, the exact split half of an even stratum

**Chapter G, NODE G.42** (`blueprint/CHAP-G_base_cases_menus.md` §5, AMENDMENT §A-8.1). *The split
count at level `N = 2k+1+r`*:

  `2 · #(splitStratum π (2k+1+r) k) + q^(2k+2r+1) = q^(2k+2r+2)`,

the exact mirror of G.41's inert count. The two counts agree at every level and every `k` — and the
reason is visible in this file: both halves are `resClassSet` of a residual class, and the two
residual classes have the SAME cardinality `q(q−1)/2` over the residue field, because
`two_mul_card_sepPair` (G.39) and `two_mul_card_aniForm` (G.38) are literally the same equation
`2·#P + q = q·q`. G.43 turns that coincidence into the every-window identity
`decidedCount split N = decidedCount inert N`.

Everything mathematical happens in G.41's predicate-parametrised `stratum_eq_resClassSet`; this
node instantiates it with `P := {p | SepPair p}`, `Q := {p | AniForm p}`, `σ := splitType`,
`τ := inertType`, and the dichotomy absorbed the OTHER way round (`Or.symm`).

DEPENDS: G.34 (`exists_inert_lift`), G.39 (`SepPair`, `two_mul_card_sepPair`), G.41
(`stratum_eq_resClassSet`) · landed `splitStratum` (G.31), `sepPair_transInvariant`,
`sepPair_not_dblPair` (G.23R3), `card_resClassSet` (G.23R9), `sepPair_iff_exists_simple_root`,
`aniso_iff_aniForm` (G.23R12), `decidedAt_split_of_sep` (G.28), `decidedAt_inert_of_ani` (G.27),
`depth_type` (G.30), `exists_max_step`, `Tang_zero`, `splitType_ne_inertType`,
`splitType_ne_ramType`.

**PROOF.** Verbatim G.41 under the substitution `AniForm ↝ SepPair`,
`two_mul_card_aniForm ↝ two_mul_card_sepPair`, `aniForm_transInvariant ↝ sepPair_transInvariant`,
`aniForm_not_dblPair ↝ sepPair_not_dblPair`, `decidedAt_inert_of_ani ↝ decidedAt_split_of_sep`,
`aniso_iff_aniForm ↝ sepPair_iff_exists_simple_root`.

The ONE step that is not a literal transcription is `decidedSet_split_eq`'s "no centre of the lift
reaches depth `N`". G.41 got it from G.33 (`exists_split_lift`): a depth-`N` centre yields a
`splitType` lift, contradicting inert-decidedness. Here a `splitType` lift is exactly what
split-decidedness predicts, so the supplier must be G.33's TWIN, G.34 `exists_inert_lift` — a
depth-`N` centre also yields an `inertType` lift — and the contradiction is again
`splitType_ne_inertType`. (This is the G.33/G.34 pair the blueprint's original DEPENDS anticipated;
G.31 and G.41 each need only one of the two.)

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **The split half of an even stratum, in residual form.** -/
theorem splitStratum_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} (hN : 2 * k + 1 ≤ N) :
    splitStratum π N k = resClassSet π {p | SepPair p} k N := by
  refine stratum_eq_resClassSet hπ (Q := {p | AniForm p}) (τ := inertType) hN
    splitType_ne_inertType (fun _ hp => sepPair_not_dblPair hp) ?_ ?_ (fun _ h => h.symm)
  · intro a γ b₀ b₁ h0 h1 hp
    obtain ⟨z, hz, hs⟩ := (sepPair_iff_exists_simple_root hπ b₀ b₁).1 hp
    exact decidedAt_split_of_sep hπ hN h0 h1 hz hs
  · intro a γ b₀ b₁ h0 h1 hp
    exact decidedAt_inert_of_ani hπ hN h0 h1 ((aniso_iff_aniForm hπ b₀ b₁).2 hp)

/-- **The level-`N` partition, split half.** A class is `splitType`-decided at level `N` exactly
when it lies in one of the split halves of the even depth strata with `2k+1 ≤ N`.

The one place where the argument is NOT a literal transcription of G.41's: there, the step "no
centre of the lift reaches depth `N`" was got from G.33 (a depth-`N` centre produces a `splitType`
lift, contradicting inert-decidedness). Here a `splitType` lift is exactly what split-decidedness
predicts, so the supplier is G.33's twin G.34 `exists_inert_lift` instead, and the contradiction is
`splitType_ne_inertType`. -/
theorem decidedSet_split_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    decidedSet O 2 splitType N = ⋃ k ∈ Finset.range ((N + 1) / 2), splitStratum π N k := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    have hnt : ¬ ∃ γ, Tang π a N γ := by
      rintro ⟨γ, hγ⟩
      obtain ⟨b, hb, hbty⟩ := exists_inert_lift hπ hγ
      exact splitType_ne_inertType ((hc b (hb.trans ha)).symm.trans hbty)
    obtain ⟨t, htlt, hPt, hmax⟩ :=
      exists_max_step (Q := fun t => ∃ γ, Tang π a t γ) ⟨0, Tang_zero π a 0⟩ N hnt
    have hmem : c ∈ depthSet π N t := by
      refine ⟨?_, ?_⟩
      · obtain ⟨γ, hγ⟩ := hPt
        exact ⟨a, ha, γ, hγ⟩
      · rintro ⟨b, hb, γ', hγ'⟩
        exact hmax ⟨γ', tang_of_proj_eq hπ (by omega) (hb.trans ha.symm) hγ'⟩
    rcases depth_type hπ htlt hmem with ⟨j, hj, hd⟩ | ⟨k, hk, _⟩
    · exact absurd ((hc a ha).symm.trans (hd a ha)) splitType_ne_ramType
    · subst hk
      exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), hmem, hc⟩
  · intro hc
    obtain ⟨k, _, hmem⟩ := Set.mem_iUnion₂.1 hc
    exact hmem.2

/-- **G.42.** The exact split count at level `N = 2k+1+r`, in additive form:
`2·#(splitStratum) + q^(2k+2r+1) = q^(2k+2r+2)` — the same equation as G.41's inert count. -/
theorem card_splitStratum (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (splitStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2) := by
  rw [splitStratum_eq hπ (show 2 * k + 1 ≤ 2 * k + 1 + r by omega),
    card_resClassSet hπ sepPair_transInvariant k r]
  have h39 : 2 * Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O //
      SepPair p} + residueCard O = residueCard O * residueCard O :=
    two_mul_card_sepPair (IsLocalRing.ResidueField O)
  have hcast : Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O |
      SepPair p} = Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O //
      SepPair p} := rfl
  rw [hcast]
  set A := Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O // SepPair p}
  set q := residueCard O
  calc 2 * (A * q ^ (2 * k + 2 * r)) + q ^ (2 * k + 2 * r + 1)
      = (2 * A + q) * q ^ (2 * k + 2 * r) := by ring
    _ = (q * q) * q ^ (2 * k + 2 * r) := by rw [h39]
    _ = q ^ (2 * k + 2 * r + 2) := by ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.splitStratum_eq
#print axioms Uniformity.Density.Menu.decidedSet_split_eq
#print axioms Uniformity.Density.Menu.card_splitStratum

end AxCheck
