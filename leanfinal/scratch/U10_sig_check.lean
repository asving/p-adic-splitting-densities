import Uniformity.ChapH.H97
import Uniformity.ChapH.H97b
import Uniformity.ChapH.H98

/-!
Signature-only elaboration checks for U10.  The examples whose conclusion is `True` deliberately
check an intended declaration's complete type without claiming its proof.  The examples with a
mathematical conclusion are discharged only by already-landed declarations.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open Filter IsLocalRing Polynomial Topology

/-! U10.00: the historical H.97 hypothesis, verbatim. -/

def U10HRate110 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    Induction.RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)

example (_ : U10HRate110) : True := True.intro

example (hrate : U10HRate110) : InductionPackage 3 :=
  package_three_of_rate hrate

/-! U10.01--U10.10: the landed recurrence chain, checked at its public interfaces. -/

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

example (a : Fin 3 → O) :
    (∃ r : O, (monicPoly a).eval r = 0 ∧ IsUnit ((monicPoly a).derivative.eval r))
      ∨ Menu.NoRootCubic (resVec a)
      ∨ (∃ γ : O, resVec a = cubeCoeff (residue O γ)) :=
  cubic_structure a

example {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h0 : π ∣ b 0) (h0' : ¬ π ^ 2 ∣ b 0) (h1 : π ∣ b 1) (h2 : π ∣ b 2) :
    typeOf (monicPoly b) = c3ram :=
  typeOf_ram3_of_val_one hπ h0 h0' h1 h2

example {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ∣ b 1) (h1' : ¬ π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) :
    typeOf (monicPoly b) = c3linRam :=
  typeOf_linRam_of_val_one hπ h2 h1 h1' h0

example {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) (h0' : ¬ π ^ 3 ∣ b 0) :
    typeOf (monicPoly b) = c3ram :=
  typeOf_ram3_of_val_two hπ h2 h1 h0 h0'

example {π : O} (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O}
    (hγ : ∀ i, shiftVec a γ i ∈ maximalIdeal O)
    (hu : UndecidedAt O 3 (M + 3) (proj O 3 (M + 3) a)) :
    ∃ d : Fin 3 → O, shiftVec a γ 0 = π ^ 3 * d 0 ∧ shiftVec a γ 1 = π ^ 2 * d 1 ∧
      shiftVec a γ 2 = π * d 2 ∧ UndecidedAt O 3 M (proj O 3 M d) :=
  undecided_triple_step hπ hγ hu

example (M : ℕ) : Nat.card (MBox O M) = residueCard O ^ (3 * M + 3) :=
  card_mbox M

example (M : ℕ) (S : Set (Coeff O 3 M)) :
    Nat.card ((mtrunc (O := O) M) ⁻¹' S) * Nat.card (Coeff O 3 M)
      = Nat.card S * Nat.card (MBox O M) :=
  card_preimage_mtrunc M S

example {π : O} (hπ : Irreducible π) {a a' : Fin 3 → O} {N : ℕ} (hN : 1 ≤ N)
    {r : O} (hr : (monicPoly a).eval r = 0)
    (hu : IsUnit ((monicPoly a).derivative.eval r))
    (hcong : ∀ i, π ^ N ∣ (a' i - a i)) :
    ∃ r' : O, (monicPoly a').eval r' = 0 ∧ π ^ N ∣ (r' - r) :=
  exists_root_congr hπ hN hr hu hcong

example {π : O} (hπ : Irreducible π) {N : ℕ} (hN : 1 ≤ N) :
    Nat.card (undecidedSet O 3 N ∩ peelBranch (O := O) N : Set (Coeff O 3 N))
      ≤ residueCard O ^ (2 * N) :=
  card_undecidedPeel_le hπ hN

example {π : O} (hπ : Irreducible π) (M : ℕ) :
    Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
        Set (Coeff O 3 (M + 3)))
      ≤ residueCard O ^ 4 * undecidedCount O 3 M :=
  card_undecidedTriple_sharp hπ M

example {N : ℕ} (hN : 1 ≤ N) :
    undecidedSet O 3 N
      ⊆ (undecidedSet O 3 N ∩ peelBranch (O := O) N)
        ∪ (undecidedSet O 3 N ∩ tripleSet (O := O) N) :=
  undecidedSet_subset_sharp hN

example (M : ℕ) :
    undecidedCount O 3 (M + 3)
      ≤ residueCard O ^ (2 * (M + 3)) + residueCard O ^ 4 * undecidedCount O 3 M :=
  undecidedCount_three_recursion M

example : Induction.RateSpecies (residueCard O) 1 0 3 (undecidedSeq O 3) :=
  rate_three

example : Tendsto (fun N => undecidedSeq O 3 N) atTop (nhds 0) :=
  undecidedSeq_three_tendsto_zero

example (σ : FactorizationType) : UndecidedVanishes O 3 σ :=
  drainage_three σ

end DVR

example : DrainageAt 3 := drainageAt_three

/-! U10.11--U10.13: extra signatures needed only for H.97's literal `(1,1,0)` rate. -/

def U10LevelOneBound : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    undecidedCount O 3 1 ≤ residueCard O ^ 2

def U10LevelTwoBound : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    undecidedCount O 3 2 ≤ 2 * residueCard O ^ 4

def U10CountRate110 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (N : ℕ),
    1 ≤ N → undecidedCount O 3 N ≤ N * residueCard O ^ (2 * N)

example (_ : U10LevelOneBound) : True := True.intro
example (_ : U10LevelTwoBound) : True := True.intro
example (_ : U10CountRate110) : True := True.intro

/-! The type-correct H.98 application requires packages at every degree, not just at degree 3. -/

example (hp : ∀ n, InductionPackage n) : ∀ n, DrainageAt n :=
  drainage_of_package hp

end Uniformity.Density
