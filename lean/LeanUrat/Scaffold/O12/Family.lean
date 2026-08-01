/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Core
import LeanUrat.Scaffold.O12.Bookings
import LeanUrat.MovesU.U0b_splitTypeFintype

/-!
# Scaffold/O12/Family — GramOver, the 𝔅_n row families, Theorem 2 [BP_II units II-R1..R14]

Movement II row-family layer (blueprint `lean/blueprints/BP_II.md` §1.3; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.3, §5).

This file carries **unit II-R1**: the `GramOver` inductive (the grammar 𝒢 with leaves,
mirroring the landed `Gram` of `MovesU/O12PoleFree.lean`) plus the two induction walks
`GramOver.mono` and `Gram.gramOver`. Units II-R2..R14 extend this module.

**Unit II-R4** adds `lowerLegs` (the β-legs available to block e) and the
`BlockPresentation` structure (one block presented for the R-induction; this is the T-8
block structure, consumed as structure only).

**Unit II-R12** adds the concrete-family statement layer: `BnCoordinates`,
`BnCoordinates.Valid`, `BnMember`, `BnMember.booking`, together with the
§1.3-displayed definitions they consume — `massPatt` (definition half of II-R6),
`massPoly` (definition half of II-R7; the blueprint splits II-R7 into definition and
grammar proof), and `AllocDatum` (definition half of II-R9). The `gram_*`/`gramOver_*`
theorems of those units are NOT part of this unit and land with II-R6/R7/R9.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- The grammar 𝒢 with LEAVES: generated from a set S by (g1)–(g6) (brief §2.3).
Mirrors the landed `Gram` (O12PoleFree.lean) plus a leaf constructor — the leaves are
the lower blocks' solved entries in Theorem 2's induction. -/
inductive GramOver (S : Set Qq) : Qq → Prop
  | leaf {f : Qq} (h : f ∈ S) : GramOver S f
  | poly (P : Polynomial ℚ) : GramOver S (algebraMap (Polynomial ℚ) Qq P)
  | invS {s : Polynomial ℚ} (hs : s ∈ cycS) : GramOver S (algebraMap (Polynomial ℚ) Qq s)⁻¹
  | add {f g} : GramOver S f → GramOver S g → GramOver S (f + g)
  | mul {f g} : GramOver S f → GramOver S g → GramOver S (f * g)
  | neg {f} : GramOver S f → GramOver S (-f)
  | subst {f} (δ : ℕ+) : GramOver S f → GramOver S (MovesS.powSubst δ f)

/-- Leafless generation is generation over any leaf set: the landed grammar `Gram`
embeds into `GramOver S` constructor-for-constructor (induction walk, unit II-R1). -/
theorem Gram.gramOver {S : Set Qq} {f : Qq} (h : Gram f) : GramOver S f := by
  induction h with
  | poly P => exact GramOver.poly P
  | invS hs => exact GramOver.invS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.subst δ

/-- Monotonicity in the leaf set (induction walk, unit II-R1): enlarging S only
enlarges what 𝒢 generates. -/
theorem GramOver.mono {S T : Set Qq} (hST : S ⊆ T) {f} : GramOver S f → GramOver T f := by
  intro h
  induction h with
  | leaf hf => exact GramOver.leaf (hST hf)
  | poly P => exact GramOver.poly P
  | invS hs => exact GramOver.invS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.subst δ

/-- The β-legs available to block e: β_{e′}(σ′) for e′ < e (base changes are `subst`,
so δ needs no indexing here — brief §2.3(vi)). -/
def lowerLegs {n : ℕ} (β : ℕ → MovesU.SplittingType n → Qq) (e : ℕ) : Set Qq :=
  {g | ∃ e' < e, ∃ σ, g = β e' σ}

/-- One block of a 𝔅_n member, presented for the R-induction (brief §2.3(iv)+(vii)):
the aggregated verdict rows t_σ are 𝒢-generated over the lower solved entries, and the
block solves by division by the booking's ℛ-unit denominator. This structure IS the
T-8 block structure consumed "as structure only" (ROOT Step 5 consumes-list). -/
structure BlockPresentation (n : ℕ) (β : ℕ → MovesU.SplittingType n → Qq) (e : ℕ) where
  trow    : MovesU.SplittingType n → Qq
  htrow   : ∀ σ, GramOver (lowerLegs β e) (trow σ)
  u       : Qq
  hu      : u ≠ 0 ∧ MemRcyc u ∧ MemRcyc u⁻¹
  hsolve  : ∀ σ, β e σ = u⁻¹ * trow σ

/-- Family (ii): divisor-pattern mass m(π) = q^{−(E−e)}·N_π(q)·q^{−e}.
(Definition half of unit II-R6; `gram_massPatt` lands with II-R6.) -/
noncomputable def massPatt (e : ℕ) (Nπ : Polynomial ℚ) : Qq :=
  (qX ^ (blockE e - e))⁻¹ * algebraMap (Polynomial ℚ) Qq Nπ * (qX ^ e)⁻¹

/-- Family (iii): polygon-family mass m(κ, ρ⃗) — a finite sum over L6b(ii)'s
enumeration of (g3)-volumes times (g4)-closures (exponents c_j ≥ 1, from
`PolygonData`), times the (JC) shape factor ∏ P_{ρ_j}(q)·(q^{d_j}−q^{d_j−1})⁻¹. The
DEFINITION takes the enumeration data as finite lists; L6′ (unit II-M11) ties it to
the polygon cells. (Definition half of unit II-R7; `gram_massPoly` lands with II-R7.) -/
noncomputable def massPoly (e : ℕ) (enum : Finset (ℕ × ℕ))
    (cs : List ℕ+) (shape : List (Polynomial ℚ × ℕ+)) : Qq :=
  (∑ z ∈ enum, (qX ^ z.2)⁻¹) *
  (cs.map (fun c => (1 - (qX ^ (c : ℕ))⁻¹)⁻¹)).prod *
  (shape.map (fun z =>
    algebraMap (Polynomial ℚ) Qq z.1 *
      (qX ^ (z.2 : ℕ) - qX ^ ((z.2 : ℕ) - 1))⁻¹)).prod

/-- Family (iv), (O2) allocation adjustment datum: an allocation α : verdicts → ℚ[q]
with the mass identity Σ_σ α(σ) = q−1 as the value-side datum (Theorem 2 needs only
α(σ) ∈ ℚ[q]). (Definition half of unit II-R9; `gramOver_allocAdjust` lands with
II-R9.) -/
def AllocDatum (n : ℕ) : Type :=
  {α : MovesU.SplittingType n → Polynomial ℚ //
    ∑ σ, α σ = Polynomial.X - 1}   -- Σ_σ α_e(σ) = q − 1 (brief §2.3(iv))

/-- Raw §2.3 member coordinates: divisor masses, polygon masses, composition maps,
allocation data, weights, transitions, and the recursively specified rows.

**Honest scope (unit II-R12, from the blueprint's binding §1 scope declaration):**
the Movement II claim is about zeros/poles of the §2-defined family 𝔅_n; VALUE
correctness is OUTSIDE this movement (D-11/O-11, Movements IV–V). The composition
and allocation data below are MEMBER COORDINATES — data carried by the presented
family member, not conclusions or hypotheses about the project's realized tables.
The identification of realized tables with 𝔅_n is the named hypothesis row
`InstancePin` ((B-INST), §1.10), never an axiom. -/
structure BnCoordinates (n : ℕ) where
  system       : BookingSystem n
  pattData     : ℕ → Finset (Polynomial ℚ)
  polygonData  : ℕ → Finset (Finset (ℕ × ℕ) × List ℕ+ ×
    List (Polynomial ℚ × ℕ+))
  handoffs     : ℕ → List (ℕ × ℕ+)
  composition  : ∀ e, (∀ i : Fin (handoffs e).length,
    MovesU.SplittingType n) → MovesU.SplittingType n
  allocation   : ℕ → AllocDatum n
  weights      : ℕ → Finset Qq
  entries      : ℕ → Finset Qq

open scoped Classical in
/-- Intrinsic membership conditions for the concrete coordinates. These are
equations and support conditions defining §2.3 membership, not conclusions of
Theorem 2. The e = 1 corner is established from the concrete transition support and
hand-off descent carried here (via `BookingSystem`), not inferred merely from a
guarded kernel definition. -/
structure BnCoordinates.Valid {n : ℕ} (C : BnCoordinates n) : Prop where
  weight_gram : ∀ e g, g ∈ C.weights e → Gram g
  handoff_step :
    ∀ e x, x ∈ C.handoffs e →
      ∃ σ σ', C.system.step e σ x.1 σ'
  entries_eq :
    ∀ e, C.entries e =
      (C.weights e ∪
        (C.pattData e).image (massPatt e) ∪
        (C.polygonData e).image
          (fun z => massPoly e z.1 z.2.1 z.2.2))

/-- A proved presentation produced from the concrete coordinates.

**Honest scope (unit II-R12, from the blueprint's binding §1 scope declaration):**
T-8's block structure and T-3/T-6's event structure enter "as structure only" —
they are this structure's DATA (`blocks`, `coords.system`), not hypotheses about
realized tables. The composition/allocation data are member coordinates carried by
`coords`. The Movement II claim scoped by this structure is about zeros/poles of
the family 𝔅_n; VALUE correctness is outside (Movements IV–V), and realized-table
claims stay conditional on the named hypothesis row `InstancePin` ((B-INST)). -/
structure BnMember (n : ℕ) where
  coords   : BnCoordinates n
  valid    : coords.Valid
  β        : ℕ → MovesU.SplittingType n → Qq
  hbase    : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ)
  blocks   : ∀ e, 2 ≤ e → BlockPresentation n β e
  hblockU  : ∀ e (he : 2 ≤ e),
    (blocks e he).u = coords.system.booking.solveU e
  entries  : ℕ → Finset Qq
  entries_eq : entries = coords.entries
  hentries : ∀ e, ∀ g ∈ entries e,
    GramOver {f | ∃ e' ≤ e, ∃ σ, f = β e' σ} g

abbrev BnMember.booking {n : ℕ} (T : BnMember n) : Booking :=
  T.coords.system.booking

end LeanUrat.Scaffold
