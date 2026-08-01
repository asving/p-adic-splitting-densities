/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H4.Defs

/-!
# Scaffold/HDischarge/H4/Kernel — units H4-L3, H4-L4, H4-L5, H4-L8

Statements AND proofs VERBATIM from `lean/blueprints/HDISCHARGE_H4.md` §L.2
(PROVED AT PROBE; probe record §L.0). Context per the §L.2 tail note: import
`LeanUrat.Scaffold.HDischarge.H4.Defs`, re-open the namespace and the
`variable (p : ℕ) [Fact p.Prime]` line.

- H4-L3 `SlotTree.dimOf_scale`: dimension scaling along a fixed slot tree.
- H4-L4 `eq2_dim_of_skel`: (EQ-2)(ii) from the conformance carrier.
- H4-L5 `eq2law_of_skel`: `EQ2law` from the carrier + the conjunct-(i)
  linearity row (M14 Lemma 2's conclusion, typed as a hypothesis until the
  graded-piece module carrier lands) — the typed discharge route for
  `UpstreamTyped.cl8_eq2`.
- H4-L8 `k3delta_of_ubxb` (+ `UBXbStmt`, `K3deltaStmt`): the fragment law at
  the typed faces (ROOT's `stable_implies_k3delta`, carrier form).

FAITHFULNESS (§L.1 note (iii), binding): `k3delta_of_ubxb` is exactly the
elementary restriction law ROOT's `stable_implies_k3delta` displays — faithful
at that altitude, claiming nothing more. L8 types the CURRENT (Route-A-shaped)
rows; Route B's face is fenced H4-F5 — not attempted here.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H4

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-- **H4-L3.** Dimension scaling along a fixed slot tree: `dimOf (δ·d) = δ · dimOf d`.
The arithmetic core of M14's Theorem (ii) — the factor δ propagates through
every stage of the product display. -/
theorem SlotTree.dimOf_scale (δ d : ℕ) :
    ∀ t : SlotTree, t.dimOf (δ * d) = δ * t.dimOf d := by
  intro t
  induction t with
  | base => rfl
  | node m cs ih =>
      simp only [SlotTree.dimOf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => ih i

/-- **H4-L4** — (EQ-2)(ii) from the conformance carrier. -/
theorem eq2_dim_of_skel {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (L : LedgerSkel p Sp AD) :
    ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
      AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x := by
  intro δ x hst
  rw [L.dim_conf δ x, L.tree_stable δ x hst, L.dbase_stable δ x hst,
    SlotTree.dimOf_scale, L.dim_conf 1 x]

/-- **H4-L5** — `EQ2law` from the conformance carrier plus the conjunct-(i)
linearity row (M14 Lemma 2's conclusion, typed as a hypothesis until the
graded-piece module carrier lands). This is the typed discharge route for
`UpstreamTyped.cl8_eq2`. -/
theorem eq2law_of_skel {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (L : LedgerSkel p Sp AD)
    (hlin : ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
      IsLinearMap ↥(Fsub p δ) (AD.slotMap δ x)) :
    EQ2law p AD :=
  fun δ x hst => ⟨hlin δ x hst, eq2_dim_of_skel p L δ x hst⟩

/-- (UB-X)(b) typed: δ-stable position classes exhaust the realized ledger at
every δ. -/
def UBXbStmt {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ → AlphabetData.Stable p AD δ x

/-- (K3-δ) typed: (UB-X)(b) RESTRICTED to K3-c's realized δ > 1 pools. -/
def K3deltaStmt {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) : Prop :=
  ∀ P : RL.Pool, AlphabetData.Stable p AD (RL.poolIdx P) (RL.poolPos P)

/-- **H4-L8** — the fragment law at the typed faces (ROOT's
`stable_implies_k3delta`, carrier form): full (UB-X)(b) implies (K3-δ). -/
theorem k3delta_of_ubxb {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) (h : UBXbStmt p RL) : K3deltaStmt p RL :=
  fun P => h (RL.poolIdx P) (RL.poolPos P) (RL.pool_realized P)

end LeanUrat.Scaffold.HDischarge.H4
