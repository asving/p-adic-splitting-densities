/-
HDISCHARGE_H7 §3.2 — `H7/Receipt.lean`: Tier-S plumbing (units H7-B; all
[probe-PROVED], round 2).  H7-B1 `engineSIBRow_of_rows`, H7-B2
`stratum_product_law`, H7-B3 `guard_read_headroom` — statements AND proofs
transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H7.md` §3.2
(compile-probe round 2, 2026-08-05).  TIER S THROUGHOUT: interface-fit only
(REV 2, review finding 15) — copies proofs into `EngineSIBRow` fields,
establishes NOTHING semantic; never cite this file as evidence for (H7).
-/
import LeanUrat.Scaffold.HDischarge.H7.Rows

namespace LeanUrat.Scaffold.HDischarge.H7

open LeanUrat.Scaffold

/-- H7-B1 [Tier S; probe-PROVED]: receipt PLUMBING — the H7 row shapes compose into
K11's `EngineSIBRow` with no re-key. Interface-fit only (REV 2, review finding 15):
`EngineSIBRow` treats the pair as opaque Props; this lemma copies proofs into fields
and establishes NOTHING semantic. -/
theorem engineSIBRow_of_rows {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (KLoc : Prop) (hK : KLoc) (hI : ITauShadow s) :
    EngineSIBRow p n N KLoc (ITauShadow s) s.stratumCount := by
  obtain ⟨A, hS, -, -, -, himg, hcnt, -⟩ := id hI
  exact ⟨hK, hI, ⟨A, hS, himg, hcnt⟩⟩

/-- H7-B2 [Tier S; probe-PROVED]: the Step-15 delivery SHAPE — the stratum product
law in roster indexing, extracted from the shadow row (H7-F1 workaround). -/
theorem stratum_product_law {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hI : ITauShadow s) :
    ∃ sM : ℕ, s.stratumCount * p ^ sM = ∏ j, s.branchCount j := by
  obtain ⟨A, -, -, -, -, himg, hcnt, hdom⟩ := hI
  exact ⟨A.sM, by rw [← hcnt, himg, hdom]⟩

/-- H7-B3 [Tier S; probe-PROVED]: IT-3 pricing arithmetic — in the D-8 guard range,
any pin `τ ≤ thr + ρ` and read depth `K ≤ thr + ρ` clear the `e_max ≤ ρ` ceiling
(the (A3) headroom of O-10 §4.3(a)). -/
theorem guard_read_headroom {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hg : InGuard s) {τ K emax : ℕ}
    (hτ : τ ≤ s.thr + s.rho) (hK : K ≤ s.thr + s.rho) (he : emax ≤ s.rho) :
    τ + emax ≤ N ∧ K + emax ≤ N := by
  unfold InGuard at hg
  omega

end LeanUrat.Scaffold.HDischarge.H7
