/-
Unit U10.theoremU  (MovesU campaign)  [capstone — THE one structure-carrying theorem]
[RETYPED 2026-07-30 per lean/notes/MOVESU_RATIFY_CODEX_2026-07-30.md — the warrant]
moves_ref: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
           prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p), and
           ρ_σ(p) IS the splitting density of type σ over ℤ_p — the undecided
           complement has mass 0 and the classifier verdicts are the true
           factorization types … Σ_σ R_σ = 1 identically in q (RS.4). … The
           quantifier 'for EVERY prime p' reads: every p satisfying (REG-p)."
deps: U6, U7, U11.
RETYPE deltas (each per an accepted finding):
  * GAP 2: the conclusion now EXPORTS `R = S.R` — the witness IS the solve family
    (whose tie to the real Cramer/RS.1-SH output is the typed `ssrc.r_is_solve`).
  * CRITICAL 6: the two-sided (U-n) bracket is now a CONJUNCT of the conclusion.
  * CRITICAL 7: clause (ii) is now typed against the NAMED ℤ_p bridge — the
    `zpDmass` clause reads the density of the classes whose EVERY monic ℤ_p lift
    factors to σ (genuine `Polynomial ℤ_[p]`/`ℚ_[p]` objects), never a free label.
  * CRITICAL 1/2/3/4: the hypothesis surface is `UCarriers`/`UInstance` — the typed
    ledger over the real corpora, with both operative stacks DERIVED.
hypothesis_fields: the COMPLETE retyped ledger via `UInstance` at every prime +
        explicit `RegP S` per adjudicated p. At a p failing (REG-p): NO CLAIM (D8).
-/
import Mathlib
import LeanUrat.MovesU.U6_un_bracket
import LeanUrat.MovesU.U7_squeeze
import LeanUrat.MovesU.U11_identification

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- THEOREM U (CONDITIONAL — on the retyped capstone ledger, carried per prime by
    `UInstance` over the real-carrier pack `UCarriers`; SQ.4). "For each splitting
    type σ of degree n … there is ONE fixed rational function R_σ ∈ ℚ(q)" — the ∃
    binds ONE family BEFORE the prime quantifier (F11), and the conclusion PINS it:
    `R = S.R`, the solve's family (itself tied to the real RS.1-SH output by the
    ledger's `ssrc.r_is_solve`). At EVERY prime p satisfying (REG-p): the two-sided
    (U-n) bracket at every level; ρ_σ(p) exists and equals the literal R_σ(p); the
    TRUE-type density is the same limit; the ℤ_p-READ density (every monic ℤ_p lift
    factors to σ — the NAMED HC-2 bridge's genuine vocabulary) is the same limit;
    the undecided complement has mass 0. Σ_σ R_σ = 1 identically in ℚ(q). At a p
    failing (REG-p): NO CLAIM (D8). -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n) (S : SolveData n)
    (M : MenuData) (KR : UpstreamKernelStatements)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C S M KR p hp) :
    ∃ R : SplittingType n → RatFunc ℚ,
      R = S.R ∧
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP S (inst p hp).D →
        -- (U-n): the exported two-sided bracket (CRITICAL 6)
        (∀ (σ : SplittingType n) (N : ℕ),
          (evalℝ ⟨R⟩ σ p - (inst p hp).X.env N) * (p : ℝ) ^ (n * N)
              ≤ ((inst p hp).X.decided σ N : ℝ) ∧
            ((inst p hp).X.decided σ N : ℝ)
              ≤ evalℝ ⟨R⟩ σ p * (p : ℝ) ^ (n * N))
        -- (i) the classifier-keyed density (the note's ρ_σ(p) = R_σ(p), T_can-keyed)
        ∧ (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (ii) the identification corollary (U11; via cl10_vpsound : VPSound X)
        ∧ (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.trueDmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (ii-ℤ_p) the SAME limit for the ℤ_p-READ density (the NAMED bridge:
        --     classes whose every monic lift factors to σ over ℚ_p — CRITICAL 7)
        ∧ (∀ σ : SplittingType n,
          Tendsto (@ZpBridge.zpDmass n p ⟨hp⟩ _ (inst p hp).bridge σ) atTop
            (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (iii) the undecided complement has mass 0
        ∧ Tendsto (inst p hp).X.env atTop (𝓝 0) := by
  -- Witness: the solve's fixed rational family, EXPORTED as such (GAP 2).
  refine ⟨S.R, rfl, (inst 2 Nat.prime_two).L.rs4_checksum, ?_⟩
  intro p hp hreg
  set U := inst p hp with hU
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- the (U-n) bracket at every (σ, N), from U6 on the ledger's typed seams.
  have hbr : ∀ (σ : SplittingType n) (N : ℕ),
      (evalℝ ⟨S.R⟩ σ p - U.X.env N) * (p : ℝ) ^ (n * N) ≤ (U.X.decided σ N : ℝ) ∧
      (U.X.decided σ N : ℝ) ≤ evalℝ ⟨S.R⟩ σ p * (p : ℝ) ^ (n * N) :=
    fun σ N => un_bracket U.L.seam U.L.ssrc U.Dpin U.L.lowerStack hreg hp σ N
  -- clause (i): U7 squeeze on the bracket + env → 0.
  have hi : ∀ σ : SplittingType n,
      Tendsto (U.X.dmass σ) atTop (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ =>
    squeeze_limit U.X hp.one_lt (evalℝ ⟨S.R⟩ σ p) σ (hbr σ) U.L.cl4_env_tendsto
  -- clause (ii): U11 identification (VP-SOUND + env → 0).
  have hii : ∀ σ : SplittingType n,
      Tendsto (U.X.trueDmass σ) atTop (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ =>
    identification U.X hp.one_lt (evalℝ ⟨S.R⟩ σ p) σ
      U.L.cl10_vpsound (hi σ) U.L.cl4_env_tendsto
  -- clause (ii-ℤ_p): the bridge equates the ℤ_p-read density with the true density.
  haveI : Fact p.Prime := ⟨hp⟩
  have hzp : ∀ σ : SplittingType n,
      Tendsto (@ZpBridge.zpDmass n p ⟨hp⟩ _ U.bridge σ) atTop
        (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ => by
    rw [ZpBridge.zpDmass_eq_trueDmass]
    exact hii σ
  exact ⟨hbr, hi, hii, hzp, U.L.cl4_env_tendsto⟩

end LeanUrat.MovesU
