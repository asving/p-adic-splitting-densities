/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E6_segStep

/-! # T-D14 `chain_charge_ledger` — MovesS §W4-SYNC S-6: the chain telescopes to the
chain's ROOT-CELL entrance (Σ₀), consuming `state_cell` at each step; the contract's
`ReadLedger` carrier DECLARED VERBATIM (`ReadLedgerT`, Defs) with the (BDY) index
convention L = the LAST READ INDEX (REV 4, Codex-3 #17). `fe` stays the one
owner-supplied datum (MovesV's `isEntrance` — the S-6 residual, quoted). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- nodes determine a `History` (proof-irrelevant remaining fields). -/
private theorem hist_ext {A B : History p F} (h : A.nodes = B.nodes) : A = B := by
  cases A; cases B; simp only at h; subst h; rfl

/-- the length-`H.nodes.length` prefix reconstructs `H`. -/
private theorem prefixAt_length (H : History p F) (hne : H.nodes ≠ []) :
    prefixAt H H.nodes.length = some H := by
  have hlen : 0 < H.nodes.length := List.length_pos_of_ne_nil hne
  unfold prefixAt
  rw [dif_pos ⟨hlen, le_refl _⟩]
  congr 1
  exact hist_ext (by simp)

/-- H's own length-`length` read is a member of its chain-reads. -/
private theorem self_mem_chainReads (Tr : VTree p F) (H : History p F)
    (hH : H ∈ Tr.chains) : H ∈ chainReads Tr H := by
  have hne : H.nodes ≠ [] := Tr.hne_nodes H hH
  have hlen : 0 < H.nodes.length := List.length_pos_of_ne_nil hne
  unfold chainReads
  rw [List.mem_filterMap]
  refine ⟨H.nodes.length - 1, by rw [List.mem_range]; omega, ?_⟩
  have hr : H.nodes.length - 1 + 1 = H.nodes.length := by omega
  rw [hr, prefixAt_length H hne]
  simp only [if_pos hH]

/-- prefixes agree below a common length. -/
private theorem prefixAt_eq_of_prefix (H H' : History p F) (k : ℕ)
    (hpre : H'.IsPrefixOf H) (hk : k ≤ H'.nodes.length) :
    prefixAt H k = prefixAt H' k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp [prefixAt]
  · have hkH : k ≤ H.nodes.length := le_trans hk (List.IsPrefix.length_le hpre)
    unfold prefixAt
    rw [dif_pos ⟨hk0, hkH⟩, dif_pos ⟨hk0, hk⟩]
    congr 1
    apply hist_ext
    show H.nodes.take k = H'.nodes.take k
    have hh : H'.nodes = H.nodes.take H'.nodes.length := List.prefix_iff_eq_take.mp hpre
    calc H.nodes.take k = H.nodes.take (min k H'.nodes.length) := by rw [min_eq_left hk]
      _ = (H.nodes.take H'.nodes.length).take k := List.take_take.symm
      _ = H'.nodes.take k := by rw [← hh]

/-- the chain-reads of `H` split as those of its immediate parent plus `H`. -/
private theorem chainReads_append (Tr : VTree p F) (H Hpar : History p F)
    (hpre : Hpar.IsPrefixOf H) (hlen : Hpar.nodes.length + 1 = H.nodes.length)
    (hH : H ∈ Tr.chains) :
    chainReads Tr H = chainReads Tr Hpar ++ [H] := by
  have hneH : H.nodes ≠ [] := Tr.hne_nodes H hH
  have hrange : H.nodes.length = Hpar.nodes.length + 1 := hlen.symm
  unfold chainReads
  rw [hrange, List.range_succ, List.filterMap_append]
  congr 1
  · apply List.filterMap_congr
    intro r hr
    rw [List.mem_range] at hr
    rw [prefixAt_eq_of_prefix H Hpar (r + 1) hpre (by omega)]
  · have hpr : prefixAt H (Hpar.nodes.length + 1) = some H := by
      rw [← hrange]; exact prefixAt_length H hneH
    simp only [List.filterMap_cons, List.filterMap_nil, hpr, if_pos hH]

/-- the telescope, by strong induction on chain length (T-E6 iterated). -/
private theorem chain_charge_aux (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p)) :
    ∀ (k : ℕ) (H : History p F), H.nodes.length = k → H ∈ Tr.chains →
      (∀ H' ∈ chainReads Tr H, L.sides H' = 1) →
      (∀ H₁ ∈ chainReads Tr H, H₁.nodes.length = 1 → L.parentSt H₁ = .red g ψ) →
      Nat.card ↥(stateEvent T (some H))
          * p ^ ((chainReads Tr H).map (L.siteExp ·)).sum
        = Nat.card ↥(rootCell χ g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro H hk hH hone hent
    have hne : H.nodes ≠ [] := Tr.hne_nodes H hH
    have hselfmem : H ∈ chainReads Tr H := self_mem_chainReads Tr H hH
    have hsides1 : L.sides H = 1 := hone H hselfmem
    have hspec : SpectatorFor (L.freshCoords H) (Set.univ : Set (Box p m)) := by
      intro x x' _; simp
    have hstep := fiber_seg_step T CA Tr χ L H hH Set.univ hspec
    rw [Set.inter_univ, Set.inter_univ] at hstep
    rcases Nat.lt_or_ge H.nodes.length 2 with hlt | hge
    · have hlen1 : H.nodes.length = 1 := by
        have := List.length_pos_of_ne_nil hne; omega
      have hps : L.parentSt H = .red g ψ := hent H hselfmem hlen1
      rw [hps] at hstep
      have hpre1 : prefixAt H 1 = some H := by
        have := prefixAt_length H hne; rwa [hlen1] at this
      have hcr : chainReads Tr H = [H] := by
        unfold chainReads
        rw [hlen1, List.range_one]
        simp only [List.filterMap_cons, List.filterMap_nil, hpre1, if_pos hH]
      rw [hcr]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      simpa [entEvent] using hstep
    · have hp := L.hparent H hH
      cases hpeq : L.parentSt H with
      | amb => rw [hpeq] at hp; exact hp.elim
      | red g' ψ' => rw [hpeq] at hp; exfalso; omega
      | st Hpar =>
        rw [hpeq] at hp
        obtain ⟨hpreHpar, hlenHpar, hmemHpar⟩ := hp
        rw [hpeq] at hstep
        simp only [entEvent] at hstep
        have happ := chainReads_append Tr H Hpar hpreHpar hlenHpar hH
        have hone' : ∀ H' ∈ chainReads Tr Hpar, L.sides H' = 1 := fun H' hmem =>
          hone H' (by rw [happ]; exact List.mem_append_left _ hmem)
        have hent' : ∀ H₁ ∈ chainReads Tr Hpar, H₁.nodes.length = 1 →
            L.parentSt H₁ = .red g ψ := fun H₁ hmem hl =>
          hent H₁ (by rw [happ]; exact List.mem_append_left _ hmem) hl
        have hIH := IH Hpar.nodes.length (by omega) Hpar rfl hmemHpar hone' hent'
        rw [happ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, add_zero]
        rw [pow_add, show Nat.card ↥(stateEvent T (some H))
              * (p ^ ((chainReads Tr Hpar).map (L.siteExp ·)).sum * p ^ L.siteExp H)
            = (Nat.card ↥(stateEvent T (some H)) * p ^ L.siteExp H)
              * p ^ ((chainReads Tr Hpar).map (L.siteExp ·)).sum from by ring]
        rw [hstep]
        exact hIH

theorem chain_charge (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (hone : ∀ H' ∈ chainReads Tr H, L.sides H' = 1)
    (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p))
    (hent : ∀ H₁ ∈ chainReads Tr H, H₁.nodes.length = 1 →
      L.parentSt H₁ = .red g ψ) :
    Nat.card ↥(stateEvent T (some H))
        * p ^ ((chainReads Tr H).map (L.siteExp ·)).sum
      = Nat.card ↥(rootCell χ g) :=
  chain_charge_aux Tr T CA χ L g ψ H.nodes.length H rfl hH hone hent

/-- H's own read is a member, so the last-read index is well-defined on chains. -/
theorem chainReads_ne (Tr : VTree p F) (H : History p F) (hH : H ∈ Tr.chains) :
    (chainReads Tr H) ≠ [] :=
  List.ne_nil_of_mem (self_mem_chainReads Tr H hH)

/-- the (BDY)-split identities AT the constructed value — rfl-level unfolding
(= the contract's `W8_bdy RL` conjunction). PROVED. -/
theorem readLedgerOf_bdy (Tr : VTree p F) {T : TreeModel p F n N m pol}
    {CA : CellData p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) (H : History p F)
    (fe : ℕ) (hfe : fe ≤ (chainReads Tr H).length - 1) :
    (readLedgerOf Tr L H fe hfe).Wcharge
        = ∑ r ∈ Finset.Icc 0 fe, (readLedgerOf Tr L H fe hfe).charge r ∧
    (readLedgerOf Tr L H fe hfe).βcharge
        = ∑ r ∈ Finset.Icc (fe + 1) (readLedgerOf Tr L H fe hfe).L,
            (readLedgerOf Tr L H fe hfe).charge r :=
  ⟨rfl, rfl⟩

end LeanUrat.MovesT
