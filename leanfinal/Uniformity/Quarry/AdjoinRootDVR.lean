/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# `R[X]/(P)` as an unramified discrete valuation ring — QUARRY BACKPORT

**Provenance (quarry charter).** Backported from `vendor/FLT` (ImperialCollegeLondon/FLT), commit
`58f25c6f305e1cf794c7666f89adcd0375bcc047`, file
`FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean`, Apache-2.0 (the same licence as
mathlib and as this repo), **verified 2026-08-15**. Shortlist items **#5, #7, #3** of
`docs/VENDOR_QUARRY_MAP_2026-08-15.md` §5. Per-declaration source lines:

| declaration | FLT line |
|---|---:|
| `IsLocalRing.of_isMaximal_map_maximalIdeal` | `:69` |
| `AdjoinRoot.isMaximal_map_maximalIdeal` | `:105` |
| `AdjoinRoot.residueFieldEquiv` | `:81` |
| `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue` | `:121` |

**Dedup-audit statement.** All four declarations in this file are **NEW declarations in this
tree** (no declaration of any of these four names existed here before). For each one, name, binder
list and **statement are byte-for-byte FLT's** — not one statement had to change — and each
docstring is FLT's own text with a single parenthetical provenance line appended. Three of the four
(`IsLocalRing.of_isMaximal_map_maximalIdeal`, `AdjoinRoot.isMaximal_map_maximalIdeal`,
`AdjoinRoot.residueFieldEquiv`) are **verbatim moves**, proof term included. The fourth,
`AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`, is a **move with one
proof-term-only adaptation** (item 3 below). The remaining edits are the two file-level ones:

1. **Module-system header surgery** (file-level, forced). FLT's file opens with `module` /
   `public import X` / `@[expose] public section` and closes with the matching `end` — mathlib's
   post-4.32 module system. Our pin (Lean `v4.31.0`, mathlib `fabf563a`, 2026-06-15) predates it,
   so the header here is plain `import`s with no `public section` and no trailing `end`.
2. **Import pruning** (file-level, ours). FLT's file needs seven mathlib imports plus two
   FLT-local patch files for its full contents; these four declarations need only the four
   mathlib imports above. In particular **neither FLT-local file was needed**:
   `FLT/Mathlib/RingTheory/AdjoinRoot.lean` and `FLT/Mathlib/FieldTheory/SeparableDegree.lean`
   are used only by the declarations we deliberately skipped (`isSeparable_root`,
   `isSeparable_of_separable`, `exists_nonZeroDivisor_mul_eq_algebraMap`, `isFractionRing_map`,
   `Field.exists_monic_irreducible_adjoinRoot_algEquiv`, `IsLocalRing.exists_monic_map_residue_eq`,
   `IsDiscreteValuationRing.injective_of_not_maximalIdeal_le_ker`). Nothing was pulled in as an
   extra dependency, and no `lia` call occurs in the four proofs (FLT's `lia`s live in the skipped
   `AdjoinRoot.lean` patch file), so no `lia` → `omega` rewrite was needed either.
3. **`List.TFAE.out` re-indexing** (inside item 4's proof, forced; the only per-declaration edit).
   `FLT :138` reads `(IsDiscreteValuationRing.TFAE (AdjoinRoot P) hSnotfield).out 5 1` and
   `FLT :142` reads `(local_hom_TFAE _).out 3 1`; here they are `.out 4 0` and `.out 2 0`. At our
   rev `List.TFAE.out` is **0-indexed** — `Mathlib/Data/List/TFAE.lean:68` discharges its side
   goals from `l[n₁]? = some a` — whereas FLT's tree is **1-indexed**, so every index drops by
   exactly one. Two independent confirmations that this is an `.out` indexing change and not a
   change to either TFAE list: (a) both of FLT's pairs shift by the same `-1`, and (b) elsewhere in
   FLT, `FLT/Patching/Algebra.lean:319` writes `((local_hom_TFAE (f i)).out 1 3).mp
   (by infer_instance)`, which forces clause `1` to be the *class* `IsLocalHom f` — the head of
   that TFAE list, i.e. index `0` in our numbering. Concretely, at our rev
   `(IsDiscreteValuationRing.TFAE R h).out 4 0 : (maximalIdeal R).IsPrincipal ↔
   IsDiscreteValuationRing R` (`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean:210`) and
   `(local_hom_TFAE f).out 2 0 : (maximalIdeal R).map f ≤ maximalIdeal S ↔ IsLocalHom f`
   (`Mathlib/RingTheory/LocalRing/RingHom/Basic.lean:81`) — the two implications FLT's proof uses.
   This is a proof-term substitution only; the theorem statement is untouched.

Every other mathlib lemma the four proofs cite exists at our rev under FLT's own name, checked by
elaboration: the file compiles with no errors and no warnings.

**Why we took it** (survey §5 rows 3, 5, 7). Item 4 below,
`AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`, is **the inert leaf, classically**:
over *any* DVR `R`, irreducibility of `P̄` over the residue field implies `R[X]/(P)` is an
unramified discrete valuation ring with `e = 1` and residue field `(ResidueField R)[X]/(P̄)`. It
pairs with our landed `Uniformity.Density.typeOf_inert_of_irreducible_map` to give HYP.01's
inert-leaf faithfulness. It is also the **sorry-free** proof of exactly the statement that the
other quarry, `vendor/LocalClassFieldTheory`
(`DiscreteValuationRing/AdjoinRoot.lean:141`), only `sorry`s.

**Duplication to note, deliberately left unresolved.** `AdjoinRoot.isMaximal_map_maximalIdeal`
(item 2) **subsumes** this repo's `Uniformity.Density.isMaximal_map_maximalIdeal_adjoinRoot`
(`Uniformity/Density/InertLeaf.lean:71`): same mathematical statement, but ours assumes `O` is a
DVR (`[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]`) where FLT's assumes only
`[IsLocalRing A]`, and the two proofs differ (ours routes through
`PrincipalIdealRing.isMaximal_of_irreducible`, FLT's through
`quotAdjoinRootEquivQuotPolynomialQuot` and `Field.toIsField`). Resolving that duplication is the
orchestrator's call; nothing outside this file was touched.

The mathematical content, in FLT's own words: for a monic `P` over a discrete valuation ring `R`
with irreducible reduction, `S = R[X]/(P)` is a discrete valuation ring, unramified over `R`, with
fraction field `K[X]/(P)` and residue field `k[X]/(P̄)`.
-/

open IsLocalRing Polynomial

universe u

/-- An integral algebra `S` over a local ring `R` such that `𝔪_R · S` is a maximal ideal is
itself local, with maximal ideal `𝔪_R · S`: any maximal ideal of `S` contracts to `𝔪_R` by
integrality, hence contains `𝔪_R · S`, hence equals it.

(Quarry backport, verbatim; see the file header for provenance. FLT `:69`.) -/
theorem IsLocalRing.of_isMaximal_map_maximalIdeal {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hmax : ((maximalIdeal R).map (algebraMap R S)).IsMaximal) : IsLocalRing S :=
  of_unique_max_ideal ⟨(maximalIdeal R).map (algebraMap R S), hmax, fun M hM ↦ by
    have hc : (M.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hle : (maximalIdeal R).map (algebraMap R S) ≤ M := by
      rw [← eq_maximalIdeal hc]; exact Ideal.map_comap_le
    exact (hmax.eq_of_le hM.ne_top hle).symm⟩

/-- If the reduction of `P` modulo the maximal ideal of a local ring `A` is irreducible, then
`𝔪_A · A[X]/(P)` is a maximal ideal: the quotient by it is the field `(A/𝔪_A)[X]/(P̄)`.

(Quarry backport, verbatim; see the file header for provenance. FLT `:105`.) -/
theorem AdjoinRoot.isMaximal_map_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] {P : A[X]}
    (hirr : Irreducible (P.map (residue A))) :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot P))).IsMaximal := by
  have : Fact (Irreducible (P.map (residue A))) := ⟨hirr⟩
  rw [algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _
    ((quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal A) P).toMulEquiv.isField
      (Field.toIsField (AdjoinRoot (P.map (residue A)))))

/-- If `S = A[X]/(P)` is local with maximal ideal `𝔪_A · S`, then its residue field is
`(A/𝔪_A)[X]/(P mod 𝔪_A)`.

(Quarry backport, verbatim; see the file header for provenance. FLT `:81`.) -/
noncomputable def AdjoinRoot.residueFieldEquiv {A : Type*} [CommRing A] [IsLocalRing A]
    {P : A[X]} [IsLocalRing (AdjoinRoot P)]
    (hmax : maximalIdeal (AdjoinRoot P) = (maximalIdeal A).map (algebraMap A (AdjoinRoot P))) :
    ResidueField (AdjoinRoot P) ≃ₐ[A] AdjoinRoot (P.map (residue A)) :=
  (Ideal.quotientEquivAlgOfEq A hmax).trans (quotEquivQuotMap P (maximalIdeal A))

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- For a monic `P` over a discrete valuation ring `R` whose reduction is irreducible over the
residue field, `S = R[X]/(P)` is again a discrete valuation ring, *unramified* over `R`: its maximal
ideal is `𝔪_R · S` (residue field `(ResidueField R)[X]/(P̄)`), so `R → S` is a local
homomorphism.

(Quarry backport, verbatim; see the file header for provenance. FLT `:121`.) -/
theorem AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue
    {P : R[X]} [IsDomain (AdjoinRoot P)] (hPm : P.Monic) (hP0 : P.degree ≠ 0)
    (hirr : Irreducible (P.map (residue R))) :
    ((maximalIdeal R).map (algebraMap R (AdjoinRoot P))).IsMaximal ∧
      IsDiscreteValuationRing (AdjoinRoot P) ∧ IsLocalHom (algebraMap R (AdjoinRoot P)) := by
  have : Module.Finite R (AdjoinRoot P) := hPm.finite_adjoinRoot
  have : Algebra.IsIntegral R (AdjoinRoot P) := Algebra.IsIntegral.of_finite R _
  have hmS_max := isMaximal_map_maximalIdeal hirr
  have : IsLocalRing (AdjoinRoot P) := IsLocalRing.of_isMaximal_map_maximalIdeal hmS_max
  have hmaxS : maximalIdeal (AdjoinRoot P) = (maximalIdeal R).map (algebraMap R (AdjoinRoot P)) :=
    (IsLocalRing.eq_maximalIdeal hmS_max).symm
  have hinj : Function.Injective (algebraMap R (AdjoinRoot P)) := by
    rw [algebraMap_eq]; exact of.injective_of_degree_ne_zero hP0
  have hSnotfield : ¬ IsField (AdjoinRoot P) := fun hf ↦ IsDiscreteValuationRing.not_a_field R
    ((Ideal.map_eq_bot_iff_of_injective hinj).mp
      (hmaxS ▸ IsLocalRing.isField_iff_maximalIdeal_eq.mp hf))
  have : IsDiscreteValuationRing (AdjoinRoot P) :=
    -- adaptation: FLT's `.out 5 1` — its `List.TFAE.out` is 1-indexed, ours is 0-indexed
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hSnotfield).out 4 0).mp
      (hmaxS ▸ Submodule.IsPrincipal.map_ringHom _
        (IsPrincipalIdealRing.principal (maximalIdeal R)))
  exact ⟨hmS_max, inferInstance,
    -- adaptation: FLT's `.out 3 1`, same 1-indexed → 0-indexed shift
    ((local_hom_TFAE (algebraMap R (AdjoinRoot P))).out 2 0).mp (le_of_eq hmaxS.symm)⟩

/-! ## Axiom footprint

The four backported declarations must each rest on Lean core only
(`[propext, Classical.choice, Quot.sound]`); a regression here is a stop-the-line event. -/

#print axioms IsLocalRing.of_isMaximal_map_maximalIdeal
#print axioms AdjoinRoot.isMaximal_map_maximalIdeal
#print axioms AdjoinRoot.residueFieldEquiv
#print axioms AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue
