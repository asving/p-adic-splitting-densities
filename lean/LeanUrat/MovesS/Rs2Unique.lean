/-
Unit U-24b `rs2_unique_interp` (medium) — locus = the ALL-ACTIVE primes (R16(ii)).
moves_ref: "at all-active primes (cofinitely many — only finitely many primes are
roots of some not-identically-zero cell-size polynomial)" (S.4(ii)); RS.2's
"every β_{e,τ}(σ′) is ONE FIXED rational function" is claimed exactly there.
COORDINATE COVERAGE: at an all-active pool EVERY (e, τ) is active, so each
coordinate's identification set is ALL of S; the conclusion's family and
`ReadOffBundle`'s coverage quantify identically (e, τ, σ').  hyp: hread (the
per-pool (ii-c) burden, OPEN — provenance W-6).  deps: U-24a1, U-24a2, U-18b, U-27.

W4-SYNC DISCHARGE (2026-07-29): SCOPED HYPOTHESIS `L : LedgerIV T M` ADDED under
seam scoping authority — see the theorem docstring for the warrant; flagged for
orchestrator ratification; recorded in MANIFEST.json (units U-24b + conditionality).
-/
import LeanUrat.MovesS.ReadOff
import LeanUrat.MovesS.InterpUnique
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- U-24b (RS.2's fixedness): on an infinite all-active pool set `S`, any OK family
interpolating the measured `βmeas` equals `blockSolve` — "every β_{e,τ}(σ′) is ONE
FIXED rational function" (S.4(ii)).

SCOPED HYPOTHESIS `L : LedgerIV T M` (W4-SYNC discharge, 2026-07-29): the blueprint's
displayed binder list (MOVESS_LEAN_BLUEPRINT_2026-07-28.md, U-24b, Codex#4-8) omits
`L`, but its OWN dep line and sketch consume it — "deps: U-24a1, U-24a2, U-18b, U-27
· sketch: U-24a2 across S; U-18b uniqueness per coordinate over S" — and BOTH
U-24a1 (`active_solve_meas`) and U-24a2 (`interp_read_off`) carry `L : LedgerIV T M`
as an explicit binder (U-24a1's hyp line: "+ L (act_target + inactive_vanish give
SUBSYSTEM CLOSURE)").  Without `L` the identification `βmeas = active-subsystem
solve` behind `AVAgree`'s RHS is not available (the measured kernel `M.kstep` and
the evaluated symbolic kernel `Aℝ P` are tied only by `L.kstep_one`/`L.act_target`),
so the goal is unprovable as stated.  NOT a weakening to vacuity: `L` is the same
ledger every solve consumer in §2.D already carries (RS4Chain.L).  FLAGGED FOR
ORCHESTRATOR RATIFICATION. -/
theorem rs2_unique_interp {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (S : Set ℚ) (hS : S ⊆ allActivePools M) (hinf : S.Infinite)
    (B : RS1Bundle T M RB hdc hK) (L : LedgerIV T M) (hdet : DetHyp T RB hK)
    (hread : ReadOffBundle S hS B hdet)
    (f : ∀ e, e ∈ Finset.Icc 1 n → T.State e → Multiset T.VType → Qq)
    (hfok : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
      (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ S → f e he τ σ' ∈ OKat q₀)
    (hfin : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
      (σ' : Multiset T.VType) (q₀ : ℚ) (hq : q₀ ∈ S) (h_ent : ℕ),
      ((evalAt q₀ ⟨f e he τ σ', hfok e he τ σ' q₀ hq⟩ : ℚ) : ℝ)
        = B.βmeas e he h_ent τ σ' q₀) :
    ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (σ' : Multiset T.VType),
      f e he τ σ' = blockSolve T RB hdc hK hdet e he τ σ' := by
  intro e he τ σ'
  -- U-24a2 across S: at each q₀ ∈ S the pool is all-active, so τ ∈ Act and the
  -- bundle's AVAgree fires (h_ent := 0); `interp_read_off` reads the symbolic
  -- solve off as the measured `βmeas` there.
  have hloc : ∀ q₀ (hq : q₀ ∈ S),
      ∃ hok : blockSolve T RB hdc hK hdet e he τ σ' ∈ OKat q₀,
        ((evalAt q₀ ⟨blockSolve T RB hdc hK hdet e he τ σ', hok⟩ : ℚ) : ℝ)
          = B.βmeas e he 0 τ σ' q₀ := by
    intro q₀ hq
    have hact : M.activeState q₀ e τ := (hS hq).2 e he τ
    have hτA : τ ∈ (hread.pkg q₀ hq e he).Act :=
      ((hread.pkg q₀ hq e he).act_spec τ).mpr hact
    exact interp_read_off B L hdet he (hread.pkg q₀ hq e he) σ' 0 ⟨τ, hτA⟩
      (hread.read q₀ hq e he ⟨τ, hτA⟩ σ' 0)
  -- U-18b per coordinate over S: two OK interpolants of the same values agree.
  refine interp_unique S hinf _ _ (fun q₀ hq => hfok e he τ σ' q₀ hq)
    (fun q₀ hq => (hloc q₀ hq).choose) ?_
  intro q₀ hq
  have h1 := hfin e he τ σ' q₀ hq 0
  have h2 := (hloc q₀ hq).choose_spec
  exact_mod_cast h1.trans h2.symm

end LeanUrat.MovesS
