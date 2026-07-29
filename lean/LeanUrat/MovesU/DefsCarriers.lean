/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.MovesS.Interfaces

/-!
# MovesU/DefsCarriers — the REAL carrier pack (MOVESU RETYPE, 2026-07-30)

STATEMENT-CHANGE WARRANT: `lean/notes/MOVESU_RATIFY_CODEX_2026-07-30.md`
(REJECT 7/2, all findings ACCEPTED — the instantiation-phase charge). CRITICAL 3:
"`SolveData`, `FiberSeries`, and the classifier are not pinned to the note's objects";
CRITICAL 1: the bare-`Prop` ledger. THIS FILE supplies the repair's substrate: the
capstone's hypothesis surface is now stated OVER the real built §S-RESUM corpus —
`MovesS.TableShape`/`MeasuredSide`/`RatBurdens`/`RS4Chain` — via `UCarriers`, and the
splitting-type vocabulary is BRIDGED to the solve's verdict multisets by `vmap`
(through `TableShape.vEquiv`, the R20 structural pin), with `vmap_mem_Sigmas` proving
membership in the chain's exact σ-index (`RS4Chain.sig_exact`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open LeanUrat

/-- The vocabulary bridge: a `SplittingType n` (multiset of (e,f) pairs, Σ e·f = n)
    read as a multiset of the table's verdict types, through the R20 structural pin
    `TableShape.vEquiv` (verdict types ARE the (e,f) pairs of degree e·f ≤ n).
    Each entry's product is ≤ n because it is one summand of the total n. -/
noncomputable def vmap {n : ℕ} (T : MovesS.TableShape n) (σ : SplittingType n) :
    Multiset T.VType :=
  σ.1.attach.map fun x =>
    T.vEquiv.symm ⟨(⟨x.1.1, (σ.2.1 x.1 x.2).1⟩, ⟨x.1.2, (σ.2.1 x.1 x.2).2⟩), by
      have hmem : x.1.1 * x.1.2 ∈ σ.1.map fun a => a.1 * a.2 :=
        Multiset.mem_map_of_mem _ x.2
      have hle := Multiset.single_le_sum
        (fun y _ => Nat.zero_le y) _ hmem
      simpa [σ.2.2] using hle⟩

/-- The bridge is degree-exact: the verdict degrees of `vmap T σ` sum to n —
    EXACTLY `RS4Chain.sig_exact`'s membership criterion. -/
theorem vmap_deg_sum {n : ℕ} (T : MovesS.TableShape n) (σ : SplittingType n) :
    ((vmap T σ).map fun v => ((T.vdeg v : ℕ))).sum = n := by
  unfold vmap
  rw [Multiset.map_map]
  have hcongr : σ.1.attach.map
      ((fun v => ((T.vdeg v : ℕ))) ∘ fun x : {a // a ∈ σ.1} =>
        T.vEquiv.symm ⟨(⟨x.1.1, (σ.2.1 x.1 x.2).1⟩, ⟨x.1.2, (σ.2.1 x.1 x.2).2⟩), by
          have hmem : x.1.1 * x.1.2 ∈ σ.1.map fun a => a.1 * a.2 :=
            Multiset.mem_map_of_mem _ x.2
          have hle := Multiset.single_le_sum (fun y _ => Nat.zero_le y) _ hmem
          simpa [σ.2.2] using hle⟩)
      = σ.1.attach.map fun x => x.1.1 * x.1.2 := by
    apply Multiset.map_congr rfl
    intro x _
    simp only [Function.comp_apply]
    rw [T.vdeg_spec, Equiv.apply_symm_apply]
    rfl
  rw [hcongr]
  have hattach : σ.1.attach.map (fun x : {a // a ∈ σ.1} => x.1.1 * x.1.2)
      = σ.1.map fun a => a.1 * a.2 := by
    conv_rhs => rw [← Multiset.attach_map_val σ.1, Multiset.map_map]
    rfl
  rw [hattach, σ.2.2]

/-- THE REAL CARRIER PACK (p-UNIFORM): Theorem U's S-side hypothesis surface, stated
    over the built §S-RESUM corpus — never instance-invented vocabulary. Carrying
    `chain : RS4Chain …` asserts, TYPED, the S-side ledger rows the old bare-`Prop`
    pack only named: CL-5's nine (the `LedgerIV` field `chain.L`), CL-1 (per-pool
    E0/ACT packages: `chain.legs_reg` at every base prime — see `UCarriers.cl1`),
    CL-9(β) = XRB (`chain.B.xrb`), CTS-M(ii-c)'s consumed-leg read-off
    (`chain.legs_read`), RS.4's measured chain (`chain.x3_total`/`chain.rs1_equates`/
    `chain.rsh_interp`), and the CL-17 carriers (with the OPEN production burden
    `chain.wsh17_pin` consumed as an explicit ledger field, never here). `hdc` is
    CL-11's DEG-CONS at the real roster (`MovesS.DegCons`). -/
structure UCarriers (n : ℕ) where
  T : MovesS.TableShape n
  MS : MovesS.MeasuredSide T
  RB : MovesS.RatBurdens T MS
  hdc : MovesS.DegCons T
  hK : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e
  Fam : MovesS.ShapeFam T
  chain : MovesS.RS4Chain T MS RB hdc hK Fam

/-- `vmap` lands in the chain's EXACT σ-index (via `sig_exact` + `vmap_deg_sum`). -/
theorem UCarriers.vmap_mem_Sigmas {n : ℕ} (C : UCarriers n) (σ : SplittingType n) :
    vmap C.T σ ∈ C.chain.Sigmas :=
  (C.chain.sig_exact _).mpr (vmap_deg_sum C.T σ)

/-- CL-1's typed row, DERIVED from the carrier chain (`legs_reg` + `prime_base`):
    per-pool ESCAPE(E0)/ACT packages at δ = 1 and every consumed base-change leg
    pool, at EVERY base prime — `MovesS.RegP` is the note's own CL-1 quantifier. -/
theorem UCarriers.cl1 {n : ℕ} (C : UCarriers n) {p : ℕ} (hp : p.Prime) :
    MovesS.RegP C.T C.MS C.RB p C.hK C.Fam :=
  C.chain.legs_reg p ((C.chain.prime_base _).mpr ⟨p, hp, rfl⟩)

/-! ## The real-roster menu rows (ROUND-2 RETYPE, 2026-07-31 — ratification
CRITICAL 3's menu finding: the surrogate `MenuData` retired; (K-SUB)/CL-13's
well-formedness face restated over THE table `C.T`). -/

/-- The (K-SUB) m = 1 classification OVER THE REAL ROSTER (was `KsubM1C1` over the
    surrogate menu): "equal-e CONTINUATION rides EXCLUSIVELY in K_e's (c = 1, m = 1)
    rows" — an all-members-size-e outcome with a continuation is a single-member
    single-continuation row. Same-size HALTS (c = 0) stay exempt. (Under DEG-CONS
    the all-size-e guard is equivalent to the ∃-a-size-e-member reading: member
    sizes are ≥ 1 and sum to ≤ e.) -/
def KsubM1C1T {n : ℕ} (T : MovesS.TableShape n) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    (∀ μ ∈ (T.odata e τ o).mem, μ.size = e) → (T.odata e τ o).c ≠ 0 →
    (T.odata e τ o).m = 1 ∧ (T.odata e τ o).c = 1

/-- CL-13's menu well-formedness FACE over THE real roster: every outcome has ≥ 1
    member, ≤ m continuations, and target totality on continuing outcomes (a
    continuing member with a state exists). -/
def MenuWFT {n : ℕ} (T : MovesS.TableShape n) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    1 ≤ (T.odata e τ o).m ∧ (T.odata e τ o).c ≤ (T.odata e τ o).m ∧
    ((T.odata e τ o).c ≠ 0 → ∃ μ ∈ (T.odata e τ o).mem, μ.status.isRight = true)

/-- At the REAL roster the well-formedness face is STRUCTURAL (hence the old
    `cl13_wf` ledger row is DISCHARGED, not carried): m ≥ 1 from `hm`, c ≤ m from
    the filter sublist, and c ≠ 0 exhibits a continuing member. -/
theorem menuWFT_holds {n : ℕ} (T : MovesS.TableShape n) : MenuWFT T := by
  intro e _ τ o
  refine ⟨List.length_pos_iff.mpr (T.odata e τ o).hm, List.length_filter_le _ _, ?_⟩
  intro hc
  have hne : ((T.odata e τ o).mem.filter (fun μ => μ.status.isRight)) ≠ [] := by
    intro h0
    exact hc (by simp [MovesS.Outcome.c, h0])
  obtain ⟨μ, hμ⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨μ, (List.mem_filter.mp hμ).1, by simpa using (List.mem_filter.mp hμ).2⟩

end LeanUrat.MovesU
