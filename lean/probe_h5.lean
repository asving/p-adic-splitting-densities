/- H5 DISCHARGE compile probe (NOT a unit; deleted after probing).
Candidate verbatim statements for HDISCHARGE_H5.md, sorry-bodied. -/
import Mathlib
import LeanUrat.Scaffold.O12.Family
import LeanUrat.Scaffold.ValueSide.Hyps
import LeanUrat.MovesS.PowSubstOK

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType)
open LeanUrat.MovesS (OKat evalAt powSubst)
open LeanUrat.Scaffold

-- ## W1-a (PACK-iii kernel): the ℛ_cyc → OKat bridge
theorem memRcyc_mem_OKat {f : Qq} (hf : MemRcyc f) {q₀ : ℚ} (hq : 2 ≤ q₀) :
    f ∈ OKat q₀ := by
  sorry

-- ## W1-b (PACK-iii at the 𝔅_n rows): every member entry is evaluation-regular
theorem bnMember_entries_mem_OKat {n : ℕ} (T : BnMember n) :
    ∀ e, ∀ g ∈ T.entries e, ∀ q₀ : ℚ, 2 ≤ q₀ → g ∈ OKat q₀ := by
  sorry

-- ## W1-c (PACK-iii, legs): every solved leg is evaluation-regular
theorem bnMember_beta_mem_OKat {n : ℕ} (T : BnMember n) :
    ∀ e σ, ∀ q₀ : ℚ, 2 ≤ q₀ → T.β e σ ∈ OKat q₀ := by
  sorry

-- ## W1-d (PACK-i kernel): evalAt inverts units
theorem evalAt_inv {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀) (hfi : f⁻¹ ∈ OKat q₀)
    (hne : evalAt q₀ ⟨f, hf⟩ ≠ 0) :
    evalAt q₀ ⟨f⁻¹, hfi⟩ = (evalAt q₀ ⟨f, hf⟩)⁻¹ := by
  sorry

-- ## W2-a: per-block exit data (the family-(ii)/(iii) roster with hand-offs)
structure ExitData (n : ℕ) where
  idx : Type
  instF : Fintype idx
  mass : idx → Qq
  handoff : idx → List (ℕ × ℕ+)
  comp : ∀ F : idx,
    ((i : Fin (handoff F).length) → SplittingType n) → SplittingType n

attribute [instance] ExitData.instF

-- ## W2-b: the canonical unadjusted aggregate t_σ (D-11 r4 §2A.2's t_σ)
noncomputable def tRow {n : ℕ} (β : ℕ → SplittingType n → Qq)
    (E : ExitData n) (σ : SplittingType n) : Qq :=
  ∑ F : E.idx, rowOf β (E.mass F) (E.handoff F) (E.comp F) σ

-- ## W2-c: the booking-adjusted DISPLAYED row (O1 plain; O2′ re-feed; O3 scaling)
noncomputable def displayedRow {n : ℕ} (b : Booking) (e : ℕ)
    (β : ℕ → SplittingType n → Qq) (E : ExitData n)
    (σ : SplittingType n) : Qq :=
  match b with
  | Booking.O1 => tRow β E σ
  | Booking.O2 => tRow β E σ
  | Booking.O2r => tRow β E σ + kappa1 e * β e σ
  | Booking.O3 => qX ^ blockE e * (qX ^ blockE e - 1)⁻¹ * tRow β E σ

-- ## W2-d: the (RE) witness at a member (PACK-iv's typed carrier)
structure REWitness {n : ℕ} (T : BnMember n) where
  exits : ℕ → ExitData n
  handoff_lt : ∀ e, ∀ F : (exits e).idx, ∀ x ∈ (exits e).handoff F, x.1 < e
  booking_reentrant : T.booking ≠ Booking.O2
  base_total : ∀ e ≤ 1, (∑ σ : SplittingType n, T.β e σ) = 1
  trow_canonical : ∀ e (he : 2 ≤ e), (T.blocks e he).trow = tRow T.β (exits e)
  mass_complete : ∀ e, 2 ≤ e → e ≤ n →
    (∑ F : (exits e).idx, (exits e).mass F) = 1 - kappa0 e - kappa1 e

-- ## W3-a (telescoping, D-11 r4 §2A.2 step 1): Σ_σ of one exit row factorizes
theorem sum_rowOf {n : ℕ} (β : ℕ → SplittingType n → Qq)
    (m : Qq) (H : List (ℕ × ℕ+))
    (comp : ((i : Fin H.length) → SplittingType n) → SplittingType n) :
    (∑ σ : SplittingType n, rowOf β m H comp σ)
      = m * ∏ i : Fin H.length,
          (∑ σ' : SplittingType n, powSubst (H.get i).2 (β (H.get i).1 σ')) := by
  sorry

-- ## W3-b (the symbolic (ROW-Σ)(a), leaf §2A.2 steps 1–4 at ℚ(q) level):
theorem rowSigma_solved {n : ℕ} (T : BnMember n) (W : REWitness T) :
    ∀ e, e ≤ n → (∑ σ : SplittingType n, T.β e σ) = 1 := by
  sorry

-- ## W3-c (the symbolic (ROW-Σ)(b), per-booking displayed row totals):
theorem rowSigma_displayed_O1 {n : ℕ} (T : BnMember n) (W : REWitness T)
    (hb : T.booking = Booking.O1) {e : ℕ} (he2 : 2 ≤ e) (hen : e ≤ n) :
    (∑ σ : SplittingType n, displayedRow T.booking e T.β (W.exits e) σ)
      = 1 - kappa0 e - kappa1 e := by
  sorry

-- ## W4-a (clause-4 route-b constructor): the pack read off a member
noncomputable def packOfMember {n : ℕ} (T : BnMember n)
    (rowsOf : ℕ → Finset Qq) : ValueSide.AssembledPack n where
  Row := (e : Finset.Icc 1 n) × {g : Qq // g ∈ rowsOf e.1}
  instR := by
    sorry
  entry := fun r => r.2.1
  blockOf := fun r => r.1.1
  blockOf_pos := fun r => (Finset.mem_Icc.mp r.1.2).1
  blockOf_le := fun r => (Finset.mem_Icc.mp r.1.2).2

-- ## W4-b probe: ValueSide.PackCorrespondence is reachable + instantiable shape
open LeanUrat.Scaffold.ValueSide in
example {n : ℕ} (C : LeanUrat.MovesU.UCarriers n) (P : AssembledPack n)
    (R : PackReference n C P)
    (h1 : ∀ r : P.Row, P.entry r = R.intendedEntry r)
    (h2 : ∀ r : P.Row, P.blockOf r = R.intendedBlock r) :
    PackCorrespondence n C P R := ⟨h1, h2⟩

-- ## W4-c (the H5 typed bundle — the field-refinement target for h5_pack)
open LeanUrat.Scaffold.ValueSide in
structure H5PackTyped (n : ℕ) (C : LeanUrat.MovesU.UCarriers n)
    (P : AssembledPack n) (R : PackReference n C P)
    (T : BnMember n) : Prop where
  corr : PackCorrespondence n C P R
  re_profile : Nonempty (REWitness T)
  wsh : ∀ e, ∀ g ∈ T.entries e, ∀ q₀ : ℚ, 2 ≤ q₀ → g ∈ OKat q₀
  bdd : ∀ e σ (q₀ : ℚ), 2 ≤ q₀ → ∀ h : T.β e σ ∈ OKat q₀,
    evalAt q₀ ⟨T.β e σ, h⟩ ∈ Set.Icc (0 : ℚ) 1

end LeanUrat.Scaffold.HDischarge.H5
