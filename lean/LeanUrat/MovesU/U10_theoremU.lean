/-
Unit U10.theoremU  (MovesU campaign)  [capstone — THE one structure-carrying theorem]
moves_ref: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
           prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p), and
           ρ_σ(p) IS the splitting density of type σ over ℤ_p — the undecided
           complement has mass 0 and the classifier verdicts are the true
           factorization types … Σ_σ R_σ = 1 identically in q (RS.4). … The
           quantifier 'for EVERY prime p' reads: every p satisfying (REG-p)."
deps: U6, U7, U11.
sketch: witness `R := S.R`. Checksum: `(inst 2 Nat.prime_two).L.rs4_checksum`
        (p-independent, any prime's ledger). Per p: clause (i) = U7 with
        `r := evalℝ S σ p`, bracket from U6 fired on the ledger's PROJECTIONS
        `L.finStack`/`L.solveStack`/`L.lowerStack` (D12 — no re-packing; `hp`
        supplies `NeZero p`, `1 < p`); clause (ii) = U11 applied to clause (i) +
        `L.cl10_vpsound` + `L.cl4_env_tendsto`; clause (iii) = `L.cl4_env_tendsto`.
        The conclusion split is the note's own (D10, ruling (B)); the ℤ_p reading
        of `trueType` is HC-2's declared pin (D9).
hypothesis_fields: the COMPLETE ledger — all cl-fields incl. the typed
        `cl10_vpsound`/`cl11`/`cl13`/`o3_teichmuller` + the operative fields — via
        `UInstance.L` at every prime, + explicit `RegP S` per adjudicated p.
        Nothing else. At a p failing (REG-p): NO CLAIM (D8).
-/
import Mathlib
import LeanUrat.MovesU.U6_un_bracket
import LeanUrat.MovesU.U7_squeeze
import LeanUrat.MovesU.U11_identification

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- THEOREM U (CONDITIONAL — on the COMPLETE capstone ledger, carried per prime by
    `UInstance`; SQ.4). "For each splitting type σ of degree n … there is ONE fixed
    rational function R_σ ∈ ℚ(q)" — the ∃ binds ONE family BEFORE the prime
    quantifier (F11); witness: S.R, so the fixed family is the solve's. At EVERY
    prime p satisfying (REG-p): ρ_σ(p) exists and equals the literal R_σ(p); the
    undecided complement has vanishing mass; the classifier verdicts ARE the true
    factorization types (F12). Σ_σ R_σ = 1 identically in ℚ(q). At a p failing
    (REG-p): NO CLAIM (D8). -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (S : SolveData n)
    (M : MenuData) (K : KernelStatements)   -- p-UNIFORM (F3-C2/G4): one M, one K, ∀ p
    (inst : ∀ p : ℕ, p.Prime → UInstance n S M K p) :
    ∃ R : SplittingType n → RatFunc ℚ,
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP S (inst p hp).D →
        -- (i) the classifier-keyed density (the note's ρ_σ(p) = R_σ(p), T_can-keyed)
        (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (ii) the identification corollary (U11; via cl10_vpsound : VPSound X):
        --     the TRUE-type density is the same limit — "ρ_σ(p) IS the splitting
        --     density of type σ"
        ∧ (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.trueDmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (iii) the undecided complement has mass 0
        ∧ Tendsto (inst p hp).X.env atTop (𝓝 0) := by
  -- Witness: the solve's fixed rational family. Checksum: RS.4 (p-independent). -/
  refine ⟨S.R, (inst 2 Nat.prime_two).L.rs4_checksum, ?_⟩
  intro p hp hreg
  set U := inst p hp with hU
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- clause (i): U7 squeeze, bracket from U6 on the ledger's slice projections.
  have hi : ∀ σ : SplittingType n,
      Tendsto (U.X.dmass σ) atTop (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ =>
    squeeze_limit U.X hp.one_lt (evalℝ ⟨S.R⟩ σ p) σ
      (fun N => un_bracket U.L.finStack U.L.solveStack U.L.lowerStack hreg hp σ N)
      U.L.cl4_env_tendsto
  -- clause (ii): U11 identification (VP-SOUND + env → 0); clause (iii): cl4_env_tendsto.
  exact ⟨hi, fun σ => identification U.X hp.one_lt (evalℝ ⟨S.R⟩ σ p) σ
      U.L.cl10_vpsound (hi σ) U.L.cl4_env_tendsto, U.L.cl4_env_tendsto⟩

end LeanUrat.MovesU
