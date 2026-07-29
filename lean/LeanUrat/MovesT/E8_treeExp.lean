/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E6_segStep

/-! # T-E8 `treeExp` [hard — THE CORPUS CENTERPIECE] — (TREE-EXP) (MOVES 7449–7461):
strong induction on Tr.chains' card via the first-split decomposition; every site
charged exactly once. The unit prices over the DATA layer; its ∀-closure `TreeExpFin`
(Defs §2.10) carries the FULL W4-1 interface. JOINT-SATISFIABILITY RECORD (REV 6,
Fable-5 CRIT-1): with the §2.9 scoping the premise row is jointly satisfiable at F1's
own shape (§0 record 13). `multiSites`/`TreeScaffold` are Defs carriers.

ESCALATION RECORD 2026-07-30 (the assembly-spine round; statement UNCHANGED): the
adjudicated `CellData.child_red_uniform` law (root-cell uniformity) and the ledger's
`spectator_sol` law are LANDED in Defs; T-E6 (`fiber_seg_step`) is now PROVED
Lean-core (the spectator-relativized C4 kernel) and T-E5 (`fiber_root_split`) is
proved modulo the single fenced `hnostray` residual (see E5's header). The remaining
work HERE is the recursion assembly per the blueprint sketch: root step = E5 at
`sc.root`; unbranched runs = E6 iterated through `state_cell` with the spectator
events carrying the other branches' pins (both spectator laws now available); splits
= E7 at `sc.splitFrame` with `hcharge` from E3 (one-side) or `hjcm` (multi-side);
leaves = factor 1; recursion on the halted-branch roster (`Tr.hfin.toFinset`) with
`sc.hscope`/`sc.subtree_part` handing each factor to the strictly smaller subtree.
It inherits E5's `hnostray` genre at the root step. Deferred to a dedicated unit —
this sorry is the LAST assembly-spine core (E10/E11 gate on it).

BLOCK RECORD 2026-07-29 (the dedicated E8 unit; statement UNCHANGED, sorry STANDS):
executing the recorded plan surfaced a STATEMENT-LEVEL seam at shared split cells —
the blueprint's own E-PHASE WATCH ITEM ("the per-chain `AofTr` accounting at SHARED
split cells and `hframe`'s `jointExp = siteExp` tie are the clauses to re-derive").
The machine-checked finding is landed BELOW as `shared_split_state_forced` /
`shared_split_siteExp_forced` (Lean-core + E6): under THIS theorem's own premise row,
any two sibling one-side sites (same `parentSt`, both `sides = 1`) are FORCED to share
`cellAt`, have EQUAL state events, and carry EQUAL `siteExp` — `state_cell` at a shared
entrance leaves no per-branch freedom. Consequences, Codex-verified (fresh context,
2026-07-29: CLAIM A CONFIRMED, CLAIM C CONFIRMED conditional on the F1 census reading,
countermodel CLAIM B = justification gap pending a full negation-witness build):
(1) the conclusion's exponent `∑_{H ∈ chains} siteExp H` charges the shared per-branch
exponent e* once PER SIBLING while the events pin it ONCE — every proof route must
derive (r−1)·e* = 0 at each shared cell with r realized sides-1 siblings, and NO
displayed law supplies it (the toy G1 carrier satisfies it with e* = 0 by fiat); a
rigged abstract instance with e* > 0 appears to satisfy every displayed law (the
double-charge countermodel shape — recorded in the session charge, /tmp-archived to
`lean/notes/E8_BLOCK_CHARGE_2026-07-29.md`), so the unit is BLOCKED pending
adjudication (candidate repairs: per-branch cell keying of `state_cell`, or a
no-double-charge ledger law, or re-keying the exponent sum per site CLASS);
(2) the REV-6 JOINT-SATISFIABILITY RECORD is REFUTED at branching shapes with
digit-pinning leaves: canonical F1 (two RAM leaves, censused conditional mass 5^{−1}
EACH, hence distinct leaf state events, both one-side) contradicts the forcing —
the row is satisfiable at branching shapes ONLY with equal leaf events (e* = 0, the
toy's degenerate form). E10/E11 remain gated; no proof attempt was pushed past the
seam (honesty invariant: a `sorry`-backed assembly would certify nothing). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

section SharedSplitForcing

/-- nodes determine a `History` (proof-irrelevant remaining fields). -/
private theorem hist_ext' {A B : History p F} (h : A.nodes = B.nodes) : A = B := by
  cases A; cases B; simp only at h; subst h; rfl

/-- a chain of length ≥ 2 has ledger entrance `.st` of its (unique) immediate prefix —
`hparent`'s `.red` leg forces length 1, and equal-length list prefixes coincide. -/
theorem parentSt_of_deep (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H₀ H : History p F) (hH : H ∈ Tr.chains)
    (hpre : H₀.IsPrefixOf H) (hlen : H₀.nodes.length + 1 = H.nodes.length) :
    L.parentSt H = .st H₀ := by
  have hp := L.hparent H hH
  cases hps : L.parentSt H with
  | amb => rw [hps] at hp; exact hp.elim
  | red g ψ =>
    rw [hps] at hp
    have := H₀.nonempty
    have h0 : 0 < H₀.nodes.length := List.length_pos_iff.mpr this
    omega
  | st H' =>
    rw [hps] at hp
    obtain ⟨hpre', hlen', -⟩ := hp
    congr 1
    apply hist_ext'
    have e1 : H'.nodes = H.nodes.take H'.nodes.length := List.prefix_iff_eq_take.mp hpre'
    have e2 : H₀.nodes = H.nodes.take H₀.nodes.length := List.prefix_iff_eq_take.mp hpre
    have hl : H'.nodes.length = H₀.nodes.length := by omega
    rw [e1, e2, hl]

/-- **THE SHARED-SPLIT FORCING** (the E8 block finding, Codex-confirmed CLAIM A,
2026-07-29): under TREE-EXP's own premise row, two sibling ONE-SIDE sites (same
`parentSt`, both `sides = 1`) are FORCED to share `cellAt` and to have EQUAL state
events — `hreal`'s fiber witness lies in both state events, `state_cell` rewrites both
into cell events at the SAME entrance, and `cellOf` is a function. Canonical branching
instances with digit-pinning sibling leaves (F1: censused conditional leaf masses
5^{−1} each, hence DISTINCT leaf state events) therefore cannot satisfy the row: the
REV-6 joint-satisfiability record fails at the leaf sites. -/
theorem shared_split_state_forced (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (hreal : Realizes T χ Tr)
    (H₁ H₂ : History p F) (h1 : H₁ ∈ Tr.chains) (h2 : H₂ ∈ Tr.chains)
    (hp : L.parentSt H₁ = L.parentSt H₂)
    (hs1 : L.sides H₁ = 1) (hs2 : L.sides H₂ = 1) :
    L.cellAt H₁ = L.cellAt H₂ ∧ stateEvent T (some H₁) = stateEvent T (some H₂) := by
  obtain ⟨x₀, hx₀⟩ := hreal
  have hm1 : x₀ ∈ stateEvent T (some H₁) := ((hx₀.1 H₁).mp h1).2.1
  have hm2 : x₀ ∈ stateEvent T (some H₂) := ((hx₀.1 H₂).mp h2).2.1
  have hc1 := L.state_cell H₁ h1 hs1
  have hc2 := L.state_cell H₂ h2 hs2
  rw [hc1] at hm1
  rw [hc2, ← hp] at hm2
  have hcell : L.cellAt H₁ = L.cellAt H₂ := by
    have e1 : CA.cellOf (L.parentSt H₁) x₀ = L.cellAt H₁ := hm1.2
    have e2 : CA.cellOf (L.parentSt H₁) x₀ = L.cellAt H₂ := hm2.2
    rw [← e1, e2]
  refine ⟨hcell, ?_⟩
  rw [hc1, hc2, ← hp, hcell]

/-- the EQUAL-CHARGE corollary (T-E6 at both siblings, `E = univ`): sibling one-side
sites carry the SAME site exponent — so TREE-EXP's conclusion, which sums `siteExp`
over ALL chains, charges a shared split's per-branch exponent e* once PER SIBLING
while the premise row pins those digits ONCE; no displayed law supplies the needed
(r−1)·e* = 0, which is the exact blocked seam (the blueprint's E-PHASE WATCH ITEM). -/
theorem shared_split_siteExp_forced (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (hreal : Realizes T χ Tr)
    (H₁ H₂ : History p F) (h1 : H₁ ∈ Tr.chains) (h2 : H₂ ∈ Tr.chains)
    (hp : L.parentSt H₁ = L.parentSt H₂)
    (hs1 : L.sides H₁ = 1) (hs2 : L.sides H₂ = 1) :
    L.siteExp H₁ = L.siteExp H₂ := by
  obtain ⟨-, hstate⟩ := shared_split_state_forced Tr T CA χ L hreal H₁ H₂ h1 h2 hp hs1 hs2
  obtain ⟨x₀, hx₀⟩ := hreal
  have hm2 : x₀ ∈ stateEvent T (some H₂) := ((hx₀.1 H₂).mp h2).2.1
  have hspec1 : SpectatorFor (L.freshCoords H₁) (Set.univ : Set (Box p m)) := by
    intro x x' _; simp
  have hspec2 : SpectatorFor (L.freshCoords H₂) (Set.univ : Set (Box p m)) := by
    intro x x' _; simp
  have e1 := fiber_seg_step T CA Tr χ L H₁ h1 hs1 Set.univ hspec1
  have e2 := fiber_seg_step T CA Tr χ L H₂ h2 hs2 Set.univ hspec2
  rw [Set.inter_univ, Set.inter_univ] at e1 e2
  rw [hstate, hp] at e1
  have heq := e1.trans e2.symm
  haveI : Finite ↥(stateEvent T (some H₂)) := (Set.toFinite _).to_subtype
  have hpos : 0 < Nat.card ↥(stateEvent T (some H₂)) :=
    Nat.card_pos_iff.mpr ⟨⟨x₀, hm2⟩, inferInstance⟩
  have hpow : p ^ L.siteExp H₁ = p ^ L.siteExp H₂ :=
    Nat.eq_of_mul_eq_mul_left hpos (by
      rw [mul_comm (Nat.card ↥(stateEvent T (some H₂))) (p ^ L.siteExp H₁),
        mul_comm (Nat.card ↥(stateEvent T (some H₂))) (p ^ L.siteExp H₂)] at heq ⊢
      exact heq)
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow

end SharedSplitForcing

theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p))
    (hred : RedCellPartition T CA χ trackOf)
    (hsib : SibCount T CA χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H hH.1 h2))
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m := by
  sorry

end LeanUrat.MovesT
