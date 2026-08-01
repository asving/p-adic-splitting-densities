/- H7 DISCHARGE BLUEPRINT COMPILE PROBE — temporary file, DELETED before commit.
   Probes the verbatim unit statements of lean/blueprints/HDISCHARGE_H7.md against
   the built corpus (the BP_VI/BP_IV lesson: ill-typed verbatim statements block waves).
   `sorry` bodies are legal HERE ONLY (statement probe, not proof). -/
import LeanUrat.Scaffold.ValueSide.KCount

namespace LeanUrat.Scaffold.HDischarge.H7

open LeanUrat.Scaffold

-- ── carrier signature probes (reuse targets)
#check @LeanUrat.Scaffold.AdaptedCell
#check @LeanUrat.Scaffold.SmithStable
#check @LeanUrat.Scaffold.EngineSIBRow
#check @LeanUrat.Scaffold.sib_product_law
#check @LeanUrat.Scaffold.kcount_fiber_card
#check @LeanUrat.Scaffold.smithStable_of_detDivisorRows
#check @LeanUrat.Scaffold.card_domainProduct_finset

-- ── H7-A1 `SiteDatum` (the abstract realized-site record the rows quantify over)
structure SiteDatum (p n N : ℕ) [Fact p.Prime] where
  m : ℕ
  two_le_m : 2 ≤ m
  thr : ℕ
  rho : ℕ
  stratumCount : ℕ
  branchCount : Fin m → ℕ

/-- The D-8 guard at the site. -/
def InGuard {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  s.thr + 2 * s.rho ≤ N

-- ── H7-A2 `ITauPresents` (the (I-τ) row body over the K10a carrier)
def ITauPresents {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  ∃ A : AdaptedCell p n N,
    SmithStable A.toMulFiberData ∧
    A.toMulFiberData.ρ = s.rho ∧
    A.toMulFiberData.τ ≤ s.thr + s.rho ∧
    A.cellCount * p ^ A.sM = Nat.card A.Factor ∧
    A.cellCount = s.stratumCount ∧
    Nat.card A.Factor = ∏ j, s.branchCount j

-- ── H7-A3 `KLocCounts` (K-LOC count face over an abstract event carrier)
def KLocCounts {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (Events : Type) (joint : Events → ℕ) (single : Events → Fin s.m → ℕ) : Prop :=
  ∀ E : Events, joint E * s.stratumCount ^ (s.m - 1) = ∏ j, single E j

-- ── H7-B1 the K11 receipt (conformance constructor: rows ⟹ EngineSIBRow)
theorem engineSIBRow_of_rows {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (KLoc : Prop) (hK : KLoc) (hI : ITauPresents s) :
    EngineSIBRow p n N KLoc (ITauPresents s) s.stratumCount := by
  obtain ⟨A, hS, -, -, himg, hcnt, -⟩ := id hI
  exact ⟨hK, hI, ⟨A, hS, himg, hcnt⟩⟩

-- ── H7-B2 the stratum product law (Step-15 delivery through the carrier)
theorem stratum_product_law {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hI : ITauPresents s) :
    ∃ sM : ℕ, s.stratumCount * p ^ sM = ∏ j, s.branchCount j := by
  obtain ⟨A, _, _, _, himg, hcnt, hdom⟩ := hI
  exact ⟨A.sM, by rw [← hcnt, himg, hdom]⟩

-- ── H7-B3 pricing arithmetic (IT-3 guard headroom; pure omega)
theorem guard_read_headroom {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hg : InGuard s) {τ K emax : ℕ}
    (hτ : τ ≤ s.thr + s.rho) (hK : K ≤ s.thr + s.rho) (he : emax ≤ s.rho) :
    τ + emax ≤ N ∧ K + emax ≤ N := by
  unfold InGuard at hg
  omega

-- ── H7-C1 uniformity-mixing kernel (IT-4 sub-cell aggregation), statement probe
open Finset in
/-- Words uniform on each part of a partition (per-part multiplicity may vary)
    are uniform on the union. -/
theorem uniform_on_union {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W]
    [DecidableEq W] (P : Finset (Finset X)) (w : X → W)
    (hcover : ∀ x : X, ∃! C, C ∈ P ∧ x ∈ C)
    (hunif : ∀ C ∈ P, ∃ u : ℕ, ∀ ω : W, (C.filter (fun x => w x = ω)).card = u) :
    ∃ U : ℕ, ∀ ω : W, (univ.filter (fun x : X => w x = ω)).card = U := by
  sorry

open Finset in
/-- Exactly-uniform joint words on a product alphabet satisfy the (SIB) count
    identity for componentwise events (the positive twin of
    `MovesU.SibRouteA.sib_diag_break`). -/
theorem sib_of_uniform_words {X : Type*} [Fintype X] [DecidableEq X]
    {m : ℕ} {A : Fin m → Type*} [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    (w : X → ∀ j, A j) {U : ℕ}
    (hU : ∀ ω : ∀ j, A j, (univ.filter (fun x => w x = ω)).card = U)
    (E : ∀ j, Finset (A j)) :
    (univ.filter (fun x : X => ∀ j, w x j ∈ E j)).card
        * (Fintype.card X) ^ (m - 1)
      = ∏ j, (univ.filter (fun x : X => w x j ∈ E j)).card := by
  sorry

-- ── H7-C2 order-1 cofactor-unit transport (KL-1/KL-2 order-1 core), statement probe
/-- ω-blindness of coprime cofactors: multiplying by a `ψ`-coprime cofactor
    changes no `ψ`-power divisibility read (`ψ` irreducible over a field). -/
theorem pow_dvd_mul_iff_of_coprime_cofactor {F : Type*} [Field F]
    {ψ g : Polynomial F} (hψ : Irreducible ψ) (hg : ¬ ψ ∣ g)
    (f : Polynomial F) (k : ℕ) :
    ψ ^ k ∣ f * g ↔ ψ ^ k ∣ f := by
  sorry

-- ── H7-D1 order-0 non-vacuity gate (F1-shaped integers), statement probe
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def f1Datum : SiteDatum 5 4 8 where
  m := 2
  two_le_m := by norm_num
  thr := 3
  rho := 0
  stratumCount := 5 ^ 8
  branchCount := ![5 ^ 4, 5 ^ 4]

theorem gate_f1_iTau : ITauPresents f1Datum := by
  sorry

theorem gate_f1_guard : InGuard f1Datum := by
  unfold InGuard f1Datum
  norm_num

end LeanUrat.Scaffold.HDischarge.H7
