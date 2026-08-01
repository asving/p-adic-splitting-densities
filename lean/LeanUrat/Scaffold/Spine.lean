/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.MovesU.DefsLedger

/-!
# Scaffold/Spine — the scaffold-form target `RootC` [wave VI-0]

E-phase transcription of `lean/blueprints/BP_VI.md` §1.2 (units VI-S1, VI-S2).
Types reused from `LeanUrat.MovesU` (NOT redefined): `SplittingType n`,
`ClassifierSpec n p`, `SolveData n`/`evalℝ`, `RegData`/`RegP`, `ZpBridge`,
`UInstance`. The statement shape is the 2026-08-01 scaffold authority =
theoremU's conclusion re-packaged clause-for-clause ((0)+(SQ)+(R) per prime,
Σ = 1 globally). Clause (UB) is deliberately NOT here (future VI-F1/F4).

Display adjustment (VI-S1; same sanctioned convention as the MeasureFloor
headers, e.g. Base.lean I-G4): `ZpBridge` carries EXPLICIT `(n p : ℕ)` binders
in the built corpus (DefsLedger.lean:740 sits under `variable (n p : ℕ)
[Fact p.Prime]`; cf. `ZpBridge.zpDmass (B : ZpBridge n p X)` ibid.), so the
§1.2 display `B : ZpBridge X` reads `B : ZpBridge n p X` here — the unique
well-typed reading (n, p forced by `X : ClassifierSpec n p`); no other token
changes. Verbatim `ZpBridge X` fails with: "Application type mismatch: The
argument X has type ClassifierSpec n p but is expected to have type ℕ".
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold

open LeanUrat.MovesU Filter Topology

/-- The per-prime scaffold conclusion at data (X, B, α): clause (0) on three
    density readings (classifier-keyed, true-type, ℤ_p-read), clause (SQ)'s
    two-sided level-N bracket, and drainage. Field-for-field = theoremU's
    per-prime conclusion tuple (U10_theoremU.lean:119–138). `B`'s type reads
    `ZpBridge n p X` per the module header's display adjustment (VI-S1). -/
structure PrimeConclusion {n p : ℕ} [Fact p.Prime] (X : ClassifierSpec n p)
    (B : ZpBridge n p X) (α : SplittingType n → ℝ) : Prop where
  bracket   : ∀ (σ : SplittingType n) (N : ℕ),
      (α σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧
      (X.decided σ N : ℝ) ≤ α σ * (p : ℝ) ^ (n * N)
  dmass     : ∀ σ, Tendsto (X.dmass σ) atTop (𝓝 (α σ))
  trueDmass : ∀ σ, Tendsto (X.trueDmass σ) atTop (𝓝 (α σ))
  zpRead    : ∀ σ, Tendsto (ZpBridge.zpDmass B σ) atTop (𝓝 (α σ))
  drainage  : Tendsto X.env atTop (𝓝 0)

/-- **`RootC` — the spine target.** ONE rational family, Σ_σ R_σ = 1 identically,
    and at every (REG-p) prime the full per-prime scaffold conclusion at
    α := evalℝ R · p. (At a p failing (REG-p): NO CLAIM — D8.) -/
def RootC (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (S : SolveData n)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) : Prop :=
  ∃ R : SplittingType n → RatFunc ℚ,
    R = S.R ∧ (∑ σ, R σ = 1) ∧
    ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
      @PrimeConclusion n p ⟨hp⟩ (inst p hp).X (inst p hp).bridge
        (fun σ => evalℝ ⟨R⟩ σ p)

end LeanUrat.Scaffold
