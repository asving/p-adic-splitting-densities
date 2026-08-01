/-
HDISCHARGE_H6 §4 unit R1 — `H6/Reconcile.lean`: the reconciliation record.

Unit spec transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4:

> **R1 (EASY).** Reconciliation record: `DecIrrSeam`/`DecHenSeam` vs the landed
> `DecIrr`/`DecHen` — one lemma per direction where provable, one compiled
> divergence witness per failure (D-7's trivial `GMNData` witness as an `example`;
> D-8's position drift). Routed to the BP_III owner for the eventual
> single-predicate adjudication. Deps: A2.

plus the fold-round-1 addendum (Codex finding 14, §2 D-8(a)):

> (a) [SUSPECT — downgraded at fold round 1, Codex finding 14: needs the base-row
> representation lemma (does the level-1 read sit at list position 0?); unit R1
> gains that check]

## The record (all four bare directions FAIL; two guarded fragments provable)

Landed pair (`DictIII/CU2t.lean`, III-S1a — UNTOUCHED):
  `DecIrr H   := ∃ k ν g, 1 ≤ k ∧ H.nodes[k]? = some ν ∧ ν.sel = some (g, 1)`
  `DecHen f H := H.nodes.length = 1 ∧ (H.a0 = 1 ∨ ∃ D, D.rootOrder = 1)`
Seam pair (`H6/Emission.lean`, unit A2): `DecIrrSeam` (last node saturated),
`DecHenSeam` (nodes = [], keyed at THE GIVEN D).

* irr, Seam → landed: FAILS at k′ = 1 (witness `R1Witness.Hone`) — D-8(a)'s
  index drift, compiled. Provable fragment: `decIrr_of_decIrrSeam_of_two_le`
  (guard `2 ≤ length`; the residue is EXACTLY the single-read strip).
* irr, landed → Seam: FAILS at a mid-history saturated node (witness
  `R1Witness.Hthree`) — D-8(b)'s ∃-any-position drift, compiled.
* hen, both directions: FAIL — TOTAL carrier drift (`nodes = []` vs
  `length = 1`: 𝐇° the continuing part vs a record counting the terminal node);
  the two predicates NEVER agree positively (`decHenSeam_decHen_incompatible`,
  the provable content), witnesses `Hnil` (Seam ∧ ¬landed) and `Hone`
  (landed ∧ ¬Seam, the landed side firing ONLY through D-7's trivial
  `GMNData` witness at a₀ = 2 — the `example` demanded by the spec).

## D-8(a) base-row representation-lemma check (Codex finding 14): ANSWERED YES

The representation lemma EXISTS in the corpus: `machineEHist_nodes_getElem?`
(`DictIII/CU1.lean`, unit III-U1): `(machineEHist M).nodes[i]? =
Option.map nodeToE M.nodes[i+1]?` — machine node 0 becomes the ROOT DATUM
(ψ̂₀, a₀), so E-list position i carries machine node i+1 = the level-(i+1)
read; position 0 IS the level-1 read (instantiated compiled below,
`baseRow_level1_read_at_position0`). Consequence: at the landed `machineProj`
representation, `DecIrr`'s `1 ≤ k` at 0-indexed lookup EXCLUDES single-read
(k′ = 1) saturated seams — D-8(a) upgrades from SUSPECT to CONFIRMED-at-the-
machineProj-representation (whether the landed `DecIrr` INTENDED 1-indexed
machine positions is the BP_III owner's call, not ours).

**ROUTED TO THE BP_III OWNER** for the eventual single-predicate adjudication;
no landed declaration is edited by this unit.
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU2t
import LeanUrat.Scaffold.DictIII.CU1
import LeanUrat.MovesU.DefsLedger
import LeanUrat.Scaffold.HDischarge.H6.Emission

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII
open LeanUrat.MovesU

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The provable fragments (one lemma per direction where provable) -/

/-- R1, irr Seam → landed, the provable fragment: OFF the single-read strip
(`2 ≤ H.nodes.length`) a seam-corrected τ-irr configuration satisfies the
landed `DecIrr` — the last position `length − 1` clears the landed `1 ≤ k`
guard. The guard is SHARP: at `length = 1` the direction FAILS
(`R1Witness.decIrrSeam_Hone_not_decIrr` below — D-8(a) compiled). -/
theorem decIrr_of_decIrrSeam_of_two_le (H : EHist p F)
    (hlen : 2 ≤ H.nodes.length) (h : DecIrrSeam H) : DecIrr H := by
  obtain ⟨hne, hsat⟩ := h
  cases hlast : H.nodes.getLast? with
  | none =>
      rw [hlast] at hsat
      exact absurd hsat (by simp)
  | some ν =>
      rw [hlast] at hsat
      obtain ⟨g, hg⟩ := hsat
      refine ⟨H.nodes.length - 1, ν, g, by omega, ?_, hg⟩
      rw [← List.getLast?_eq_getElem?]
      exact hlast

/-- R1, hen, BOTH directions at once (the strongest provable statement — and
the whole provable content): the seam-corrected and landed hen predicates are
INCOMPATIBLE. `DecHenSeam` is keyed at 𝐇° with `nodes = []` (the k′ = 0
continuing part; the terminal booking carries NO node — CUC §9.1 carrier
note), while the landed `DecHen` demands `nodes.length = 1` (the record
COUNTING a node). Total carrier drift: neither direction has a positive
instance, so each bare direction holds only vacuously-never; the compiled
one-sided witnesses are `R1Witness.decHenSeam_Hnil_not_decHen` and
`R1Witness.decHen_Hone_not_decHenSeam`. -/
theorem decHenSeam_decHen_incompatible (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (hseam : DecHenSeam f H D) (hland : DecHen f H) :
    False := by
  have h0 : H.nodes = [] := hseam.1
  have h1 : H.nodes.length = 1 := hland.1
  rw [h0] at h1
  simp at h1

/-! ## The compiled divergence witnesses (one per failing bare direction)

Sanctioned NEW declarations of the R1 refutation-witness class, named:
`R1Witness.nuSat`, `R1Witness.nuUnsat`, `R1Witness.Hnil`, `R1Witness.Hone`,
`R1Witness.Hthree`, `R1Witness.DnilJunk`, `R1Witness.DoneJunk`, the four
divergence theorems, the D-7 `example`, and the D-8(a) check
`baseRow_level1_read_at_position0`. -/

namespace R1Witness

open Polynomial

/-- R1 witness node, SATURATED selection: `sel = some (1, 1)` (g = 1, μ = 1). -/
def nuSat : ENodeData :=
  { e := 1, h := 1, ℓ := 1, s := 0, u := 0, sel := some (1, 1), inc := false
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num, hl := le_refl 1
    hsel := by
      intro gμ hgμ
      simp only [Option.mem_def, Option.some.injEq] at hgμ
      subst hgμ
      exact ⟨le_refl 1, le_refl 1, by norm_num⟩ }

/-- R1 witness node, NON-saturated selection: `sel = some (1, 2)` (μ = 2). -/
def nuUnsat : ENodeData :=
  { e := 1, h := 1, ℓ := 2, s := 0, u := 0, sel := some (1, 2), inc := false
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num, hl := by norm_num
    hsel := by
      intro gμ hgμ
      simp only [Option.mem_def, Option.some.injEq] at hgμ
      subst hgμ
      exact ⟨le_refl 1, by norm_num, by norm_num⟩ }

/-- R1 witness history, k′ = 0: NO nodes, `a₀ = 1` — the τ-hen seam carrier
(𝐇° of a Hensel-decided run). Over `F = ZMod 2` (the `S4Refute.H0` dressing
pattern). -/
noncomputable def Hnil : EHist 2 (ZMod 2) :=
  { base := ⊤
    psi0 := X - C 1
    hpsi0 := ⟨monic_X_sub_C 1, irreducible_X_sub_C 1⟩
    a0 := 1
    ha0 := le_refl 1
    nodes := []
    fld := fun _ => ⊤
    psihat := fun _ => X - C 1
    hpsihat := fun _ => ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, by
      intro hXC
      have h0 := congrArg (fun q => q.coeff 0) hXC
      simp at h0⟩ }

/-- R1 witness history, k′ = 1: ONE node, saturated (`sel = some (1, 1)`),
`a₀ = 2` (so the landed `DecHen`'s `a₀ = 1` disjunct is UNAVAILABLE — only
D-7's trivial-data disjunct can fire). -/
noncomputable def Hone : EHist 2 (ZMod 2) :=
  { base := ⊤
    psi0 := X - C 1
    hpsi0 := ⟨monic_X_sub_C 1, irreducible_X_sub_C 1⟩
    a0 := 2
    ha0 := by norm_num
    nodes := [nuSat]
    fld := fun _ => ⊤
    psihat := fun _ => X - C 1
    hpsihat := fun _ => ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, by
      intro hXC
      have h0 := congrArg (fun q => q.coeff 0) hXC
      simp at h0⟩ }

/-- R1 witness history, k′ = 3: a MID-history saturated node (position 1) with
a NON-saturated last node — the landed `DecIrr`'s ∃-any-position form fires,
the seam-corrected last-node form does not (D-8(b)). -/
noncomputable def Hthree : EHist 2 (ZMod 2) :=
  { base := ⊤
    psi0 := X - C 1
    hpsi0 := ⟨monic_X_sub_C 1, irreducible_X_sub_C 1⟩
    a0 := 2
    ha0 := by norm_num
    nodes := [nuUnsat, nuSat, nuUnsat]
    fld := fun _ => ⊤
    psihat := fun _ => X - C 1
    hpsihat := fun _ => ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, by
      intro hXC
      have h0 := congrArg (fun q => q.coeff 0) hXC
      simp at h0⟩ }

/-- Laws-free junk semantic data over `Theta Hnil` (any `D` serves: the seam
witness fires through `a₀ = 1`). -/
noncomputable def DnilJunk : GMNData (X : Polynomial ℤ_[2]) (Theta Hnil) :=
  { principalSides := fun _ => []
    residualOrder := fun _ => 0
    residualDegree := fun _ => 0
    rootOrder := 1 }

/-- D-7's trivial `GMNData` witness (blueprint §2 D-7's `⟨fun _ => [], …⟩`,
here over `Theta Hone`): NO laws constrain the record, so `rootOrder := 1`
comes for free. -/
noncomputable def DoneJunk : GMNData (X : Polynomial ℤ_[2]) (Theta Hone) :=
  { principalSides := fun _ => []
    residualOrder := fun _ => 0
    residualDegree := fun _ => 0
    rootOrder := 1 }

/-- R1 divergence witness (irr, Seam → landed FAILS — D-8(a) compiled): the
single-read saturated seam `Hone` is a `DecIrrSeam`, but the landed `DecIrr`'s
`1 ≤ k` guard cannot see position 0 in a length-1 list. -/
theorem decIrrSeam_Hone_not_decIrr :
    DecIrrSeam Hone ∧ ¬ DecIrr Hone := by
  constructor
  · exact ⟨by simp [Hone], by simp [Hone, nuSat]⟩
  · rintro ⟨k, ν, g, hk, hget, -⟩
    have hlt : k < Hone.nodes.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hget
      cases hget
    have hlen : Hone.nodes.length = 1 := by simp [Hone]
    omega

/-- R1 divergence witness (irr, landed → Seam FAILS — D-8(b) compiled): a
mid-history saturated node at position 1 fires the landed `DecIrr`, while the
LAST node of `Hthree` is non-saturated, so the seam-corrected form fails. -/
theorem decIrr_Hthree_not_decIrrSeam :
    DecIrr Hthree ∧ ¬ DecIrrSeam Hthree := by
  constructor
  · exact ⟨1, nuSat, 1, le_refl 1, by simp [Hthree], rfl⟩
  · rintro ⟨-, hsat⟩
    have hlast : Hthree.nodes.getLast? = some nuUnsat := by simp [Hthree]
    rw [hlast] at hsat
    obtain ⟨g, hg⟩ := hsat
    simp [nuUnsat] at hg

/-- R1 divergence witness (hen, Seam → landed FAILS): the k′ = 0 Hensel seam
`Hnil` (nodes = [], a₀ = 1) is a `DecHenSeam` at any `D`, but the landed
`DecHen` demands `nodes.length = 1` — the carrier drift, compiled. -/
theorem decHenSeam_Hnil_not_decHen :
    DecHenSeam (X : Polynomial ℤ_[2]) Hnil DnilJunk ∧
      ¬ DecHen (X : Polynomial ℤ_[2]) Hnil := by
  refine ⟨⟨rfl, Or.inl rfl⟩, ?_⟩
  rintro ⟨h1, -⟩
  simp [Hnil] at h1

/-- D-7's trivial `GMNData` witness as an `example` (the spec's demand,
verbatim shape `⟨fun _ => [], …⟩`): at `Hone` — where `a₀ = 2` closes the
honest disjunct — the landed `DecHen` STILL holds, through a junk record that
no law forbids. -/
example : DecHen (X : Polynomial ℤ_[2]) Hone :=
  ⟨by simp [Hone],
   Or.inr ⟨{ principalSides := fun _ => []
             residualOrder := fun _ => 0
             residualDegree := fun _ => 0
             rootOrder := 1 }, rfl⟩⟩

/-- R1 divergence witness (hen, landed → Seam FAILS): `Hone` satisfies the
landed `DecHen` ONLY via D-7's junk-data disjunct (`a₀ = 2` here), while
`DecHenSeam` — keyed at THE GIVEN `D` and at the k′ = 0 carrier — fails on
`nodes ≠ []` alone. -/
theorem decHen_Hone_not_decHenSeam :
    DecHen (X : Polynomial ℤ_[2]) Hone ∧
      ¬ DecHenSeam (X : Polynomial ℤ_[2]) Hone DoneJunk := by
  refine ⟨⟨by simp [Hone], Or.inr ⟨DoneJunk, rfl⟩⟩, ?_⟩
  rintro ⟨h1, -⟩
  simp [Hone] at h1

/-- **The D-8(a) base-row representation-lemma check (Codex finding 14):
ANSWERED YES.** The corpus representation lemma `machineEHist_nodes_getElem?`
(`DictIII/CU1.lean`, III-U1) instantiated at position 0: machine node 0
becomes the ROOT DATUM, so E-list position 0 carries machine node 1 — the
LEVEL-1 read. Hence at the `machineProj` representation the landed `DecIrr`'s
`1 ≤ k` excludes single-read (k′ = 1) saturated seams (compiled at the
E-carrier by `decIrrSeam_Hone_not_decIrr`): D-8(a) SUSPECT → CONFIRMED at
this representation. Single-predicate adjudication: BP_III owner. -/
theorem baseRow_level1_read_at_position0 (M : MovesC.History p F) :
    (machineEHist M).nodes[0]? = Option.map nodeToE M.nodes[1]? :=
  machineEHist_nodes_getElem? M 0

end R1Witness

end LeanUrat.Scaffold.HDischarge.H6
