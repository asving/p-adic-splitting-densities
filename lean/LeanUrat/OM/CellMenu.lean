/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.Classifier

/-!
# CellMenu — Phase-B wave W2: the order-1 cell menu and the menu-checking classifier `classify1`

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md` §2 (design decision D-STEP: menu-checking,
not hull-scanning) with ALL FIVE W0 errata transcribed from the gated ground truth
`/workspace-vast/asving/tmp/phaseb_w0/` (`menu_semantics.py`, `SUMMARY.md`, 336 exhaustively
classified boxes at `p = 2, N = 3, s ∈ {2,3,4}`):

* **F1** — `cell_exists` gates on LEFT-ENDPOINT READABILITY `v_p(a₀) < N`, NOT on
  `v_p(disc) < N` (refuted: `x²+2x`, `x²+6x` at `p=2, N=3`). W0's sharp law (verified on all
  336 boxes): a box element matches exactly one menu cell ⟺ `v_p(a₀) < N`; otherwise none.
* **F2** — disc-conditioned gates can be vacuous (s=4 disc-bulk empty at N=3); the gates below
  are left-endpoint-conditioned.
* **F3** — residual convention: `t = 0` at the LEFT vertex, above-side pattern positions
  contribute `0`, unit-normalize before the shape read (here: `normalizedFactors` is
  unit-invariant, so no explicit normalization is needed).
* **F4** — the menu contains MAXIMAL-side paths only: strictly increasing slopes, strictly
  decreasing integer vertex heights, NO collinear interior vertices (load-bearing for
  `cell_unique`: `x²+2x+4` at `p=2, N=3` matches two cells of the non-maximal menu).
* **F5** — height bound `H ≤ N−1` (the `N·s` bound is dead weight; vertex equality at height
  `≥ N` is uncertifiable at level `N`, so the `≤ N−1` menu loses nothing).

**Scope: ORDER 1, x-power cluster only** (the W0-tested case `f ≡ x^s mod p`); deeper orders and
general residue classes are later waves (W6).

**The shared menu type.** The menu cells are `OMCountV2.NodeConfig` — the SAME object the R1
counting recursion `configsOf`/`omCount` consumes (blueprint §2: single-source-of-truth, the
classifier checks membership, the counter sums). Conventions consumed from OMCountV2:
`FaceAssign.dF` = FULL residual degree `d_S = Σ μ·D`; payload-read faces `punctured := true`;
`ChildData` per A2 (`childSize = μ·D` slots, child iff `2 ≤ μ ∧ μ·D < s`, self-loop = no child,
child shape `⟨[(order+1, μ·D, 0)], []⟩` at order 1 → order slot `2`).

**Numeric gates in this file** (W0 table = ground truth): path counts 2/3/3 and cell counts
4/3/5 at `s = 2/3/4, N = 3` (W0's readable sub-menu: 4/3/5 cells); six explicit boxes spanning
`s ∈ {2,3,4}`, incl. a two-sided polygon (S3C3), a self-loop cell (S2C2) and a tail box.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.CellMenu

open LeanUrat LeanUrat.OM Polynomial
open LeanUrat.OM.OMCountV2 (NodeConfig FaceAssign ChildData)

/-! ## 1. Vertex-list geometry: maximal lower-convex lattice paths

A path is carried as its full vertex list `[(0,H), (j₁,v₁), …, (s,0)]` with strictly increasing
abscissae, strictly decreasing heights, and STRICTLY increasing slopes (F4 maximality — no
collinear interior vertices). Slope comparison is cross-multiplied over `ℤ`. -/

/-- `slope(a→b) < slope(c→d)`, cross-multiplied over `ℤ` (a valid comparison when `a.1 < b.1` and
`c.1 < d.1`, the only use sites). -/
def SlopeLt (a b c d : ℕ × ℕ) : Prop :=
  ((b.2 : ℤ) - a.2) * ((d.1 : ℤ) - c.1) < ((d.2 : ℤ) - c.2) * ((b.1 : ℤ) - a.1)

instance (a b c d : ℕ × ℕ) : Decidable (SlopeLt a b c d) :=
  inferInstanceAs (Decidable
    (((b.2 : ℤ) - a.2) * ((d.1 : ℤ) - c.1) < ((d.2 : ℤ) - c.2) * ((b.1 : ℤ) - a.1)))

/-- **The vertex-chain invariant** after the edge `p0 → p1`: the remaining vertices `T` continue
with strictly increasing abscissae, strictly decreasing heights, strictly increasing slopes
(F4), ending exactly at `(s, 0)`. -/
inductive ChainOK (s : ℕ) : (ℕ × ℕ) → (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | nil {p0 p1 : ℕ × ℕ} (h1 : p1.1 = s) (h2 : p1.2 = 0) : ChainOK s p0 p1 []
  | cons {p0 p1 p2 : ℕ × ℕ} {T : List (ℕ × ℕ)} (h1 : p1.1 < p2.1) (h2 : p2.2 < p1.2)
      (h3 : SlopeLt p0 p1 p1 p2) (h4 : ChainOK s p1 p2 T) : ChainOK s p0 p1 (p2 :: T)

/-- **A menu path** (blueprint §2 + F4/F5): a maximal lower-convex lattice path of width `s`,
left endpoint `(0, H)` with `1 ≤ H ≤ N−1` (cluster + F5 height bound), right endpoint `(s, 0)`. -/
def MenuPath (s N : ℕ) (P : List (ℕ × ℕ)) : Prop :=
  ∃ H p1 T, P = (0, H) :: p1 :: T ∧ 1 ≤ H ∧ H ≤ N - 1 ∧ 0 < p1.1 ∧ p1.2 < H ∧
    ChainOK s (0, H) p1 T

/-! ### Chain consequences -/

theorem chainOK_mem_bounds {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : ∀ q ∈ T, p1.1 < q.1 ∧ q.2 < p1.2 := by
  induction h with
  | nil => intro q hq; simp at hq
  | cons h1 h2 h3 h4 ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨h1, h2⟩
      · exact ⟨h1.trans (ih q hq').1, (ih q hq').2.trans h2⟩

theorem chainOK_le {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : p1.1 ≤ s := by
  induction h with
  | nil h1 h2 => exact h1.le
  | cons h1 h2 h3 h4 ih => exact le_trans h1.le ih

theorem chainOK_zero {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) (h0 : p1.2 = 0) : p1.1 = s := by
  cases h with
  | nil h1 h2 => exact h1
  | cons h1 h2 h3 h4 => exact absurd h2 (by omega)

theorem chainOK_last_mem {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : (s, 0) ∈ p1 :: T := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      have hp : p1 = (s, 0) := Prod.ext h1 h2
      simp [hp]
  | cons h1 h2 h3 h4 ih => exact List.mem_cons_of_mem _ ih

/-- The chain's previous-vertex slot is irrelevant to everything except the first slope
comparison; weakening lemma used when re-rooting inductions. -/
theorem chainOK_mem_le {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : ∀ q ∈ T, q.1 ≤ s := by
  induction h with
  | nil => intro q hq; simp at hq
  | cons h1 h2 h3 h4 ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact chainOK_le h4
      · exact ih q hq'

/-- The pairwise strict right-down order along the chain. -/
theorem chainOK_pairwise {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    (p1 :: T).Pairwise (fun a b => a.1 < b.1 ∧ b.2 < a.2) := by
  induction h with
  | nil => simp
  | cons h1 h2 h3 h4 ih =>
      rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨h1, h2⟩
      · obtain ⟨hq1, hq2⟩ := chainOK_mem_bounds h4 q hq'
        exact ⟨h1.trans hq1, hq2.trans h2⟩

theorem menuPath_pairwise {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P) :
    P.Pairwise (fun a b => a.1 < b.1 ∧ b.2 < a.2) := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := h
  rw [List.pairwise_cons]
  refine ⟨?_, chainOK_pairwise hc⟩
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact ⟨hp1, hpH⟩
  · obtain ⟨hq1, hq2⟩ := chainOK_mem_bounds hc q hq'
    exact ⟨by simpa using hp1.trans hq1, by simpa using hq2.trans hpH⟩

theorem menuPath_last_mem {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P) :
    (s, 0) ∈ P := by
  obtain ⟨H, p1, T, rfl, _, _, _, _, hc⟩ := h
  exact List.mem_cons_of_mem _ (chainOK_last_mem hc)

theorem menuPath_mem_le {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P) :
    ∀ q ∈ P, q.1 ≤ s := by
  obtain ⟨H, p1, T, rfl, _, _, _, _, hc⟩ := h
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact Nat.zero_le s
  · rcases List.mem_cons.mp hq' with rfl | hq''
    · exact chainOK_le hc
    · exact chainOK_mem_le hc q hq''

/-- Two members with the same abscissa have the same height (strict fst-sorting). -/
theorem pairwise_fst_unique {P : List (ℕ × ℕ)}
    (hP : P.Pairwise (fun a b => a.1 < b.1 ∧ b.2 < a.2)) {j v1 v2 : ℕ}
    (h1 : (j, v1) ∈ P) (h2 : (j, v2) ∈ P) : v1 = v2 := by
  induction P with
  | nil => simp at h1
  | cons a P ih =>
      rw [List.pairwise_cons] at hP
      rcases List.mem_cons.mp h1 with rfl | h1'
      · rcases List.mem_cons.mp h2 with h | h2'
        · exact (Prod.ext_iff.mp h.symm).2
        · exact absurd (hP.1 _ h2').1 (by simp)
      · rcases List.mem_cons.mp h2 with rfl | h2'
        · exact absurd (hP.1 _ h1').1 (by simp)
        · exact ih hP.2 h1' h2'

theorem menuPath_s_height {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P) {v : ℕ}
    (hv : (s, v) ∈ P) : v = 0 :=
  pairwise_fst_unique (menuPath_pairwise h) hv (menuPath_last_mem h)

/-! ## 2. Enumeration of menu paths -/

/-- Candidate next vertices after `p`: abscissa in `(p.1, s]`, height `< p.2`, height `0` only
at abscissa `s`. -/
def nextCands (s : ℕ) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  ((List.range' (p.1 + 1) (s - p.1)).flatMap fun j =>
    (List.range p.2).map fun v => (j, v)).filter fun q => decide (q.2 = 0 → q.1 = s)

theorem mem_nextCands {s : ℕ} {p q : ℕ × ℕ} :
    q ∈ nextCands s p ↔ p.1 < q.1 ∧ q.1 ≤ s ∧ q.2 < p.2 ∧ (q.2 = 0 → q.1 = s) := by
  unfold nextCands
  rw [List.mem_filter, List.mem_flatMap]
  constructor
  · rintro ⟨⟨j, hj, hq⟩, hdec⟩
    rw [List.mem_range'] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [List.mem_map] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    rw [List.mem_range] at hv
    exact ⟨by omega, by omega, hv, of_decide_eq_true hdec⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨q.1, ?_, ?_⟩, decide_eq_true h4⟩
    · rw [List.mem_range']
      exact ⟨q.1 - p.1 - 1, by omega, by omega⟩
    · rw [List.mem_map]
      exact ⟨q.2, List.mem_range.mpr h3, rfl⟩

/-- All continuations after the edge `p0 → p1`, fuel-based (structural recursion so that the
enumeration kernel-reduces for the tiny-case count gates). -/
def extendPaths (s : ℕ) : ℕ → (ℕ × ℕ) → (ℕ × ℕ) → List (List (ℕ × ℕ))
  | 0, _, _ => []
  | fuel + 1, p0, p1 =>
      if p1.1 = s then (if p1.2 = 0 then [[]] else []) else
      ((nextCands s p1).filter fun p2 => decide (SlopeLt p0 p1 p1 p2)).flatMap fun p2 =>
        (extendPaths s fuel p1 p2).map (p2 :: ·)

theorem mem_extendPaths {s : ℕ} :
    ∀ {fuel : ℕ} {p0 p1 : ℕ × ℕ} {T : List (ℕ × ℕ)}, s < p1.1 + fuel →
      (T ∈ extendPaths s fuel p0 p1 ↔ ChainOK s p0 p1 T) := by
  intro fuel
  induction fuel with
  | zero =>
      intro p0 p1 T hf
      simp only [extendPaths, List.not_mem_nil, false_iff]
      intro hc
      cases hc with
      | nil h1 h2 => omega
      | cons h1 h2 h3 h4 =>
          have := chainOK_le h4
          omega
  | succ fuel ih =>
      intro p0 p1 T hf
      simp only [extendPaths]
      by_cases hs : p1.1 = s
      · rw [if_pos hs]
        by_cases h0 : p1.2 = 0
        · rw [if_pos h0]
          constructor
          · intro hT
            have : T = [] := by simpa using hT
            subst this
            exact ChainOK.nil hs h0
          · intro hc
            cases hc with
            | nil => simp
            | cons h1 h2 h3 h4 =>
                have := chainOK_le h4
                omega
        · rw [if_neg h0]
          simp only [List.not_mem_nil, false_iff]
          intro hc
          cases hc with
          | nil h1 h2 => exact h0 h2
          | cons h1 h2 h3 h4 =>
              have := chainOK_le h4
              omega
      · rw [if_neg hs, List.mem_flatMap]
        constructor
        · rintro ⟨p2, hp2, hT⟩
          rw [List.mem_filter] at hp2
          obtain ⟨hp2c, hp2s⟩ := hp2
          rw [List.mem_map] at hT
          obtain ⟨T', hT', rfl⟩ := hT
          rw [mem_nextCands] at hp2c
          have hrec := (ih (p0 := p1) (p1 := p2) (T := T') (by omega)).mp hT'
          exact ChainOK.cons hp2c.1 hp2c.2.2.1 (of_decide_eq_true hp2s) hrec
        · intro hc
          cases hc with
          | nil h1 h2 => exact absurd h1 hs
          | @cons _ _ p2 T' h1 h2 h3 h4 =>
              refine ⟨p2, ?_, ?_⟩
              · rw [List.mem_filter, mem_nextCands]
                refine ⟨⟨h1, chainOK_le h4, h2, ?_⟩, decide_eq_true h3⟩
                intro h0
                exact chainOK_zero h4 h0
              · rw [List.mem_map]
                exact ⟨T', (ih (by omega)).mpr h4, rfl⟩

/-- **All menu paths of width `s` at level `N`** (vertex-list layer): left height `H ∈ [1, N−1]`
(F5), then all convex maximal continuations. -/
def menuPaths (s N : ℕ) : List (List (ℕ × ℕ)) :=
  (List.range' 1 (N - 1)).flatMap fun H =>
    (nextCands s (0, H)).flatMap fun p1 =>
      (extendPaths s (s + 1) (0, H) p1).map fun T => (0, H) :: p1 :: T

/-- **Membership characterization of the path menu** (deliverable 1). -/
theorem mem_menuPaths_iff {s N : ℕ} {P : List (ℕ × ℕ)} :
    P ∈ menuPaths s N ↔ MenuPath s N P := by
  unfold menuPaths
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨H, hH, hP⟩
    rw [List.mem_range'] at hH
    obtain ⟨i, hi, rfl⟩ := hH
    rw [List.mem_flatMap] at hP
    obtain ⟨p1, hp1, hP⟩ := hP
    rw [List.mem_map] at hP
    obtain ⟨T, hT, rfl⟩ := hP
    rw [mem_nextCands] at hp1
    have hchain := (mem_extendPaths (by omega)).mp hT
    exact ⟨1 + 1 * i, p1, T, rfl, by omega, by omega, hp1.1, hp1.2.2.1, hchain⟩
  · rintro ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩
    refine ⟨H, ?_, ?_⟩
    · rw [List.mem_range']
      exact ⟨H - 1, by omega, by omega⟩
    · rw [List.mem_flatMap]
      refine ⟨p1, ?_, ?_⟩
      · rw [mem_nextCands]
        exact ⟨hp1, chainOK_le hc, hpH, fun h0 => chainOK_zero hc h0⟩
      · rw [List.mem_map]
        exact ⟨T, (mem_extendPaths (by omega)).mpr hc, rfl⟩

/-! ### Nodup of the enumeration -/

/-- Keyed flatMap nodup: if a key function recovers the index from every emitted element, the
flatMap of nodup blocks over a nodup index list is nodup. -/
theorem nodup_flatMap_key {α β : Type*} {l : List α} {f : α → List β} (key : β → α)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hkey : ∀ a ∈ l, ∀ b ∈ f a, key b = a) :
    (l.flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hf, ?_⟩
  have hne : l.Pairwise (· ≠ ·) := hl
  refine hne.imp_of_mem ?_
  intro a a' ha ha' hane x hx1 hx2
  exact hane ((hkey a ha x hx1).symm.trans (hkey a' ha' x hx2))

theorem nodup_nextCands (s : ℕ) (p : ℕ × ℕ) : (nextCands s p).Nodup := by
  unfold nextCands
  refine List.Nodup.filter _ ?_
  refine nodup_flatMap_key Prod.fst List.nodup_range' ?_ ?_
  · intro j _
    have hr : (List.range p.2).Nodup := List.nodup_range
    exact hr.map (fun a b h => by simpa using h)
  · intro j _ b hb
    rw [List.mem_map] at hb
    obtain ⟨v, _, rfl⟩ := hb
    rfl

theorem nodup_extendPaths (s : ℕ) :
    ∀ (fuel : ℕ) (p0 p1 : ℕ × ℕ), (extendPaths s fuel p0 p1).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro p0 p1; simp [extendPaths]
  | succ fuel ih =>
      intro p0 p1
      simp only [extendPaths]
      by_cases hs : p1.1 = s
      · rw [if_pos hs]
        by_cases h0 : p1.2 = 0 <;> simp [h0]
      · rw [if_neg hs]
        refine nodup_flatMap_key (fun L => L.head?.getD (0, 0)) ?_ ?_ ?_
        · exact List.Nodup.filter _ (nodup_nextCands s p1)
        · intro p2 _
          exact (ih p1 p2).map (fun a b h => by simpa using h)
        · intro p2 _ b hb
          rw [List.mem_map] at hb
          obtain ⟨T, _, rfl⟩ := hb
          rfl

/-- **The path menu is duplicate-free** (deliverable 1). -/
theorem nodup_menuPaths (s N : ℕ) : (menuPaths s N).Nodup := by
  unfold menuPaths
  refine nodup_flatMap_key (fun P => (P.head?.map Prod.snd).getD 0) List.nodup_range' ?_ ?_
  · intro H _
    refine nodup_flatMap_key (fun P => (P.tail.head?).getD (0, 0)) (nodup_nextCands s (0, H)) ?_ ?_
    · intro p1 _
      exact (nodup_extendPaths s (s + 1) (0, H) p1).map (fun a b h => by simpa using h)
    · intro p1 _ b hb
      rw [List.mem_map] at hb
      obtain ⟨T, _, rfl⟩ := hb
      rfl
  · intro H _ b hb
    rw [List.mem_flatMap] at hb
    obtain ⟨p1, _, hb⟩ := hb
    rw [List.mem_map] at hb
    obtain ⟨T, _, rfl⟩ := hb
    rfl

/-! ## 3. Residual-shape assignments: partitions of the side degree into `(D, μ)` parts -/

/-- The canonical (lexicographic non-strict) order on `(D, μ)` parts. -/
def shapeLE (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel shapeLE := fun a b => by unfold shapeLE; infer_instance

instance : IsTrans (ℕ × ℕ) shapeLE :=
  ⟨fun a b c hab hbc => by unfold shapeLE at *; omega⟩

instance : Std.Antisymm shapeLE :=
  ⟨fun a b hab hba => by
    unfold shapeLE at hab hba
    exact Prod.ext_iff.mpr ⟨by omega, by omega⟩⟩

instance : Std.Total shapeLE :=
  ⟨fun a b => by unfold shapeLE; omega⟩

theorem shapeLE_trans {a b c : ℕ × ℕ} (hab : shapeLE a b) (hbc : shapeLE b c) : shapeLE a c := by
  unfold shapeLE at *; omega

/-- All lists over `A` of length `≤ n` (enumeration scaffold). -/
def listsLE {α : Type*} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, A => [] :: A.flatMap fun a => (listsLE n A).map (a :: ·)

theorem mem_listsLE {α : Type*} :
    ∀ {n : ℕ} {A : List α} {l : List α},
      l ∈ listsLE n A ↔ l.length ≤ n ∧ ∀ x ∈ l, x ∈ A := by
  intro n
  induction n with
  | zero =>
      intro A l
      simp only [listsLE, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, _⟩
        exact List.length_eq_zero_iff.mp (by omega)
  | succ n ih =>
      intro A l
      simp only [listsLE, List.mem_cons, List.mem_flatMap, List.mem_map]
      constructor
      · rintro (rfl | ⟨a, ha, t, ht, rfl⟩)
        · simp
        · obtain ⟨h1, h2⟩ := ih.mp ht
          refine ⟨by simpa using Nat.succ_le_succ h1, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ha
          · exact h2 x hx'
      · rintro ⟨hlen, hmem⟩
        cases l with
        | nil => exact Or.inl rfl
        | cons a t =>
            refine Or.inr ⟨a, hmem a (by simp), t, ih.mpr ⟨by simpa using hlen, ?_⟩, rfl⟩
            intro x hx
            exact hmem x (List.mem_cons_of_mem _ hx)

theorem nodup_listsLE {α : Type*} [Inhabited α] :
    ∀ {n : ℕ} {A : List α}, A.Nodup → (listsLE n A).Nodup := by
  intro n
  induction n with
  | zero => intro A _; simp [listsLE]
  | succ n ih =>
      intro A hA
      simp only [listsLE]
      rw [List.nodup_cons]
      constructor
      · intro h
        rw [List.mem_flatMap] at h
        obtain ⟨a, _, h⟩ := h
        rw [List.mem_map] at h
        obtain ⟨t, _, h⟩ := h
        exact List.cons_ne_nil a t h
      · refine nodup_flatMap_key (fun L => L.head?.getD default) hA ?_ ?_
        · intro a _
          exact (ih hA).map (fun x y h => by simpa using h)
        · intro a _ b hb
          rw [List.mem_map] at hb
          obtain ⟨t, _, rfl⟩ := hb
          rfl

/-- The `(D, μ)` alphabet with `1 ≤ D, μ ≤ d`. -/
def pairAlphabet (d : ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 d).flatMap fun D => (List.range' 1 d).map fun μ => (D, μ)

theorem mem_pairAlphabet {d : ℕ} {q : ℕ × ℕ} :
    q ∈ pairAlphabet d ↔ (1 ≤ q.1 ∧ q.1 ≤ d) ∧ (1 ≤ q.2 ∧ q.2 ≤ d) := by
  unfold pairAlphabet
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨D, hD, hq⟩
    rw [List.mem_range'] at hD
    obtain ⟨i, hi, rfl⟩ := hD
    rw [List.mem_map] at hq
    obtain ⟨μ, hμ, rfl⟩ := hq
    rw [List.mem_range'] at hμ
    obtain ⟨k, hk, rfl⟩ := hμ
    omega
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨q.1, ?_, ?_⟩
    · rw [List.mem_range']; exact ⟨q.1 - 1, by omega, by omega⟩
    · rw [List.mem_map]
      refine ⟨q.2, ?_, ?_⟩
      · rw [List.mem_range']; exact ⟨q.2 - 1, by omega, by omega⟩
      · exact Prod.ext_iff.mpr ⟨rfl, rfl⟩

theorem nodup_pairAlphabet (d : ℕ) : (pairAlphabet d).Nodup := by
  unfold pairAlphabet
  refine nodup_flatMap_key Prod.fst List.nodup_range' ?_ ?_
  · intro D _
    have hr : (List.range' 1 d).Nodup := List.nodup_range'
    exact hr.map (fun a b h => by simpa using h)
  · intro D _ b hb
    rw [List.mem_map] at hb
    obtain ⟨μ, _, rfl⟩ := hb
    rfl

/-- **All residual shapes of degree `d`**: canonically sorted lists of `(D, μ)` parts with
`D, μ ≥ 1` and `Σ D·μ = d` (partitions of the side degree — blueprint §2 (ii)). -/
def shapesOfDegree (d : ℕ) : List (List (ℕ × ℕ)) :=
  (listsLE d (pairAlphabet d)).filter fun l =>
    decide (l.Pairwise shapeLE) && ((l.map fun q => q.1 * q.2).sum == d)

/-- ℕ-list members are bounded by the sum. -/
theorem nat_le_sum_of_mem : ∀ {L : List ℕ} {x : ℕ}, x ∈ L → x ≤ L.sum := by
  intro L
  induction L with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp
      · have := ih hx'
        simp only [List.sum_cons]
        omega

theorem length_le_sum_of_one_le : ∀ {L : List ℕ}, (∀ x ∈ L, 1 ≤ x) → L.length ≤ L.sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have h1 := h a (by simp)
      have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [List.length_cons, List.sum_cons]
      omega

theorem mem_shapesOfDegree_iff {d : ℕ} {l : List (ℕ × ℕ)} :
    l ∈ shapesOfDegree d ↔
      l.Pairwise shapeLE ∧ (∀ q ∈ l, 1 ≤ q.1 ∧ 1 ≤ q.2) ∧
        (l.map fun q => q.1 * q.2).sum = d := by
  unfold shapesOfDegree
  rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq, mem_listsLE]
  constructor
  · rintro ⟨⟨_, hA⟩, hpw, hsum⟩
    refine ⟨hpw, ?_, hsum⟩
    intro q hq
    have := mem_pairAlphabet.mp (hA q hq)
    exact ⟨this.1.1, this.2.1⟩
  · rintro ⟨hpw, hpos, hsum⟩
    have hbound : ∀ q ∈ l, q.1 * q.2 ≤ d := by
      intro q hq
      rw [← hsum]
      exact nat_le_sum_of_mem (List.mem_map_of_mem hq)
    refine ⟨⟨?_, ?_⟩, hpw, hsum⟩
    · have hlen : (l.map fun q => q.1 * q.2).length ≤ (l.map fun q => q.1 * q.2).sum := by
        refine length_le_sum_of_one_le ?_
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        have := hpos q hq
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      rw [List.length_map] at hlen
      omega
    · intro q hq
      have h1 := hpos q hq
      have h2 := hbound q hq
      rw [mem_pairAlphabet]
      refine ⟨⟨h1.1, ?_⟩, h1.2, ?_⟩
      · calc q.1 ≤ q.1 * q.2 := Nat.le_mul_of_pos_right _ h1.2
          _ ≤ d := h2
      · calc q.2 ≤ q.1 * q.2 := Nat.le_mul_of_pos_left _ h1.1
          _ ≤ d := h2

theorem nodup_shapesOfDegree (d : ℕ) : (shapesOfDegree d).Nodup :=
  List.Nodup.filter _ (nodup_listsLE (nodup_pairAlphabet d))

/-! ## 4. The cell menu -/

/-- The sides of a path (consecutive vertex pairs, left to right). -/
def sidePairs (P : List (ℕ × ℕ)) : List ((ℕ × ℕ) × (ℕ × ℕ)) := P.zip P.tail

/-- The residual degree `d_S` of a side, computed as `gcd(drop, run)` (proved `= M4.residualDeg`
of the packaged side in §6). -/
def sideDeg (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := Nat.gcd (pr.1.2 - pr.2.2) (pr.2.1 - pr.1.1)

/-- Path height ceiling at integer abscissa `i` (the L4 per-column ceiling `⌈h_i⌉`): on the side
`(j₀,v₀) → (j₁,v₁)` containing `i`, `⌈v₀ − (v₀−v₁)(i−j₀)/(j₁−j₀)⌉ = v₀ − ⌊(v₀−v₁)(i−j₀)/(j₁−j₀)⌋`. -/
def ceilAt : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | [q], _ => q.2
  | q0 :: q1 :: T, i =>
      if i ≤ q0.1 then q0.2
      else if i ≤ q1.1 then q0.2 - (q0.2 - q1.2) * (i - q0.1) / (q1.1 - q0.1)
      else ceilAt (q1 :: T) i

/-- At a vertex the ceiling height is the exact vertex height. -/
theorem ceilAt_vertex {P : List (ℕ × ℕ)}
    (hP : P.Pairwise (fun a b => a.1 < b.1 ∧ b.2 < a.2)) {j v : ℕ} (hjv : (j, v) ∈ P) :
    ceilAt P j = v := by
  induction P with
  | nil => simp at hjv
  | cons q0 P ih =>
      rw [List.pairwise_cons] at hP
      cases P with
      | nil =>
          have h : (j, v) = q0 := by simpa using hjv
          simp [ceilAt, ← h]
      | cons q1 T =>
          have hlt : q0.1 < q1.1 := (hP.1 q1 (List.mem_cons_self ..)).1
          have hvv : q1.2 < q0.2 := (hP.1 q1 (List.mem_cons_self ..)).2
          rcases List.mem_cons.mp hjv with heq | hmem
          · -- (j, v) = q0
            have hj : j = q0.1 := by rw [← heq]
            have hv : v = q0.2 := by rw [← heq]
            simp only [ceilAt]
            rw [if_pos (le_of_eq hj)]
            exact hv.symm
          · have hj0 : q0.1 < j := (hP.1 _ hmem).1
            rcases List.mem_cons.mp hmem with heq | hmem'
            · -- (j, v) = q1
              have hj : j = q1.1 := by rw [← heq]
              have hv : v = q1.2 := by rw [← heq]
              simp only [ceilAt]
              rw [if_neg (by omega), if_pos (le_of_eq hj), hj, hv,
                Nat.mul_div_cancel _ (by omega : 0 < q1.1 - q0.1)]
              omega
            · have hj1 : q1.1 < j := ((List.pairwise_cons.mp hP.2).1 _ hmem').1
              simp only [ceilAt]
              rw [if_neg (by omega), if_neg (by omega)]
              exact ih hP.2 hmem

/-- Whether abscissa `i` is a vertex abscissa of `P`. -/
def isVertexAbscissa (P : List (ℕ × ℕ)) (i : ℕ) : Bool := decide (i ∈ P.map Prod.fst)

/-- **The lattice polygon of a menu path** (the `NodeConfig.polygon` slot): width `s`, per-column
ceiling heights of the path, vertex flags at the path's vertex abscissae (the right endpoint `s`
is outside the flag window, as in L4/BB1). -/
def mkPoly (s : ℕ) (P : List (ℕ × ℕ)) : L4.LatticePolygon :=
  { width := s
    ceilHeights := fun i => ceilAt P i.1
    isVertex := fun i => isVertexAbscissa P i.1 }

/-- Non-dependent height reader of a polygon (for injectivity extraction). -/
def polyHeight (pg : L4.LatticePolygon) (i : ℕ) : ℕ :=
  if h : i < pg.width then pg.ceilHeights ⟨i, h⟩ else 0

/-- Non-dependent vertex-flag reader of a polygon. -/
def polyFlag (pg : L4.LatticePolygon) (i : ℕ) : Bool :=
  if h : i < pg.width then pg.isVertex ⟨i, h⟩ else false

theorem polyHeight_mkPoly {s : ℕ} {P : List (ℕ × ℕ)} {i : ℕ} (hi : i < s) :
    polyHeight (mkPoly s P) i = ceilAt P i := by
  simp [polyHeight, mkPoly, hi]

theorem polyFlag_mkPoly {s : ℕ} {P : List (ℕ × ℕ)} {i : ℕ} (hi : i < s) :
    polyFlag (mkPoly s P) i = isVertexAbscissa P i := by
  simp [polyFlag, mkPoly, hi]

/-- **`mkPoly` is injective on menu paths** — the polygon data (vertex flags + exact heights at
vertices) reconstructs the vertex list. -/
theorem mkPoly_injective {s N : ℕ} {P P' : List (ℕ × ℕ)}
    (h1 : MenuPath s N P) (h2 : MenuPath s N P')
    (heq : mkPoly s P = mkPoly s P') : P = P' := by
  have hpw := menuPath_pairwise h1
  have hpw' := menuPath_pairwise h2
  have hH : ∀ i, polyHeight (mkPoly s P) i = polyHeight (mkPoly s P') i := fun i => by rw [heq]
  have hF : ∀ i, polyFlag (mkPoly s P) i = polyFlag (mkPoly s P') i := fun i => by rw [heq]
  have key : ∀ (Q Q' : List (ℕ × ℕ)), MenuPath s N Q → MenuPath s N Q' →
      (∀ i, polyHeight (mkPoly s Q) i = polyHeight (mkPoly s Q') i) →
      (∀ i, polyFlag (mkPoly s Q) i = polyFlag (mkPoly s Q') i) →
      ∀ x : ℕ × ℕ, x ∈ Q → x ∈ Q' := by
    intro Q Q' hQ hQ' hHi hFi x hx
    have hp := menuPath_pairwise hQ
    have hp' := menuPath_pairwise hQ'
    obtain ⟨j, v⟩ := x
    have hjs : j ≤ s := menuPath_mem_le hQ _ hx
    rcases Nat.lt_or_ge j s with hjlt | hjge
    · have hflag : isVertexAbscissa Q j = true :=
        decide_eq_true (List.mem_map_of_mem hx)
      have hflag' : isVertexAbscissa Q' j = true := by
        have hfi := hFi j
        rw [polyFlag_mkPoly hjlt, polyFlag_mkPoly hjlt] at hfi
        rw [← hfi, hflag]
      have hmem' : j ∈ Q'.map Prod.fst := of_decide_eq_true hflag'
      rw [List.mem_map] at hmem'
      obtain ⟨q', hq', hj'⟩ := hmem'
      have hv' : ceilAt Q' j = q'.2 := by
        have hvx := ceilAt_vertex hp' (show (q'.1, q'.2) ∈ Q' by simpa using hq')
        rwa [hj'] at hvx
      have hv1 : ceilAt Q j = v := ceilAt_vertex hp hx
      have hhi := hHi j
      rw [polyHeight_mkPoly hjlt, polyHeight_mkPoly hjlt, hv1, hv'] at hhi
      have hxq : (j, v) = q' := Prod.ext hj'.symm hhi
      rw [hxq]
      exact hq'
    · have hj : j = s := le_antisymm hjs hjge
      subst hj
      have hv0 : v = 0 := menuPath_s_height hQ hx
      subst hv0
      exact menuPath_last_mem hQ'
  haveI hanti : Std.Antisymm (fun (a b : ℕ × ℕ) => a.1 < b.1 ∧ b.2 < a.2) :=
    ⟨fun a b hab hba => absurd hba.1 (by omega)⟩
  haveI hirr : Std.Irrefl (fun (a b : ℕ × ℕ) => a.1 < b.1 ∧ b.2 < a.2) :=
    ⟨fun a h => by omega⟩
  refine List.Pairwise.eq_of_mem_iff hpw hpw' ?_
  intro x
  exact ⟨key P P' h1 h2 hH hF x,
    key P' P h2 h1 (fun i => (hH i).symm) (fun i => (hF i).symm) x⟩

/-- The A2/A3 child shape at order 1: descent children carry the single-tuple shape
`⟨[(2, μ·D, 0)], []⟩` (order slot `order + 1 = 2`, size slot `μ·D`, the schematic W2/A3 payload;
faithful child payloads are wave W3). -/
def childShape (sz : ℕ) : ClusterShape := ⟨[(2, sz, 0)], []⟩

/-- The face assignment of one side: order-1 face over the base residue field (`δ = 1`), the
`(D, μ)` shape multiset, full residual degree `d_F = d_S`, and `punctured := true` (payload-read
faces are genuine, R1/E2 convention). -/
def mkFace (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : FaceAssign :=
  { δ := 1, shape := shape, dF := sideDeg pr, punctured := true }

/-- The descent children of a cell (A2 semantics): one `ChildData` per `(D, μ)` part with
`2 ≤ μ` and `μ·D < s` (the full-budget repeated factor `μ·D = s` is the self-loop, deliberately
NOT a child); `δ = 1`, base change `D`. -/
def cellChildren (s : ℕ) (sh : List (List (ℕ × ℕ))) : List ChildData :=
  sh.flatMap fun shape => shape.filterMap fun q =>
    if 2 ≤ q.2 ∧ q.2 * q.1 < s then some ⟨childShape (q.2 * q.1), 1, q.1⟩ else none

/-- **A menu cell**: polygon of the path, one face per side (left-to-right), A2 children. -/
def mkCell (s : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) : NodeConfig :=
  { polygon := mkPoly s P
    faces := List.zipWith mkFace (sidePairs P) sh
    children := cellChildren s sh }

/-- Valid residual-shape assignments for a path: one shape (partition) per side. -/
def ShapesFor (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) : Prop :=
  List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr)) sh (sidePairs P)

/-- All shape assignments of a path (product over sides). -/
def piList {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | l :: L => l.flatMap fun a => (piList L).map (a :: ·)

theorem mem_piList {α : Type*} :
    ∀ {L : List (List α)} {xs : List α}, xs ∈ piList L ↔ List.Forall₂ (· ∈ ·) xs L := by
  intro L
  induction L with
  | nil =>
      intro xs
      simp only [piList, List.mem_singleton, List.forall₂_nil_right_iff]
  | cons l L ih =>
      intro xs
      simp only [piList, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨a, ha, t, ht, rfl⟩
        exact List.Forall₂.cons ha (ih.mp ht)
      · intro h
        rw [List.forall₂_cons_right_iff] at h
        obtain ⟨a, t, ha, ht, rfl⟩ := h
        exact ⟨a, ha, t, ih.mpr ht, rfl⟩

theorem nodup_piList {α : Type*} [Inhabited α] :
    ∀ {L : List (List α)}, (∀ l ∈ L, l.Nodup) → (piList L).Nodup := by
  intro L
  induction L with
  | nil => intro _; simp [piList]
  | cons l L ih =>
      intro h
      simp only [piList]
      refine nodup_flatMap_key (fun t => t.head?.getD default) (h l (by simp)) ?_ ?_
      · intro a _
        exact (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')).map
          (fun x y hxy => by simpa using hxy)
      · intro a _ b hb
        rw [List.mem_map] at hb
        obtain ⟨t, _, rfl⟩ := hb
        rfl

/-- The shape assignments of a path. -/
def shapeAssignments (P : List (ℕ × ℕ)) : List (List (List (ℕ × ℕ))) :=
  piList ((sidePairs P).map fun pr => shapesOfDegree (sideDeg pr))

theorem mem_shapeAssignments {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))} :
    sh ∈ shapeAssignments P ↔ ShapesFor P sh := by
  unfold shapeAssignments ShapesFor
  rw [mem_piList, List.forall₂_map_right_iff]

theorem nodup_shapeAssignments (P : List (ℕ × ℕ)) : (shapeAssignments P).Nodup := by
  refine nodup_piList ?_
  intro l hl
  rw [List.mem_map] at hl
  obtain ⟨pr, _, rfl⟩ := hl
  exact nodup_shapesOfDegree _

/-- **THE CELL MENU** (deliverable 2, blueprint §2): all menu paths × all per-side residual-shape
assignments, emitted as the shared `OMCountV2.NodeConfig` menu objects. -/
def cellMenu (s N : ℕ) : List NodeConfig :=
  (menuPaths s N).flatMap fun P => (shapeAssignments P).map (mkCell s P)

/-- **Membership characterization of the cell menu** (deliverable 2). -/
theorem mem_cellMenu_iff {s N : ℕ} {c : NodeConfig} :
    c ∈ cellMenu s N ↔ ∃ P sh, MenuPath s N P ∧ ShapesFor P sh ∧ c = mkCell s P sh := by
  unfold cellMenu
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨P, hP, hc⟩
    rw [List.mem_map] at hc
    obtain ⟨sh, hsh, rfl⟩ := hc
    exact ⟨P, sh, mem_menuPaths_iff.mp hP, mem_shapeAssignments.mp hsh, rfl⟩
  · rintro ⟨P, sh, hP, hsh, rfl⟩
    exact ⟨P, mem_menuPaths_iff.mpr hP, List.mem_map.mpr ⟨sh, mem_shapeAssignments.mpr hsh, rfl⟩⟩

/-- Reading the shapes back off the faces of a cell. -/
theorem map_shape_zipWith_mkFace :
    ∀ (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ))),
      sh.length = prs.length →
      (List.zipWith mkFace prs sh).map FaceAssign.shape = sh := by
  intro prs
  induction prs with
  | nil =>
      intro sh h
      rw [List.length_nil, List.length_eq_zero_iff] at h
      simp [h]
  | cons pr prs ih =>
      intro sh h
      cases sh with
      | nil => simp
      | cons l sh' =>
          simp only [List.zipWith_cons_cons, List.map_cons, mkFace]
          rw [ih sh' (by simpa using h)]

/-- **`mkCell` is injective on menu data** (polygon recovers the path, faces recover the shapes). -/
theorem mkCell_injective {s N : ℕ} {P P' : List (ℕ × ℕ)} {sh sh' : List (List (ℕ × ℕ))}
    (h1 : MenuPath s N P) (h2 : MenuPath s N P')
    (hs1 : ShapesFor P sh) (hs2 : ShapesFor P' sh')
    (heq : mkCell s P sh = mkCell s P' sh') : P = P' ∧ sh = sh' := by
  have hpoly : mkPoly s P = mkPoly s P' := congrArg NodeConfig.polygon heq
  have hPP : P = P' := mkPoly_injective h1 h2 hpoly
  subst hPP
  have hfaces : List.zipWith mkFace (sidePairs P) sh = List.zipWith mkFace (sidePairs P) sh' :=
    congrArg NodeConfig.faces heq
  have hl1 : sh.length = (sidePairs P).length := hs1.length_eq
  have hl2 : sh'.length = (sidePairs P).length := hs2.length_eq
  refine ⟨rfl, ?_⟩
  calc sh = (List.zipWith mkFace (sidePairs P) sh).map FaceAssign.shape :=
        (map_shape_zipWith_mkFace _ _ hl1).symm
    _ = (List.zipWith mkFace (sidePairs P) sh').map FaceAssign.shape := by rw [hfaces]
    _ = sh' := map_shape_zipWith_mkFace _ _ hl2

/-- **The cell menu is duplicate-free** (deliverable 2). -/
theorem nodup_cellMenu (s N : ℕ) : (cellMenu s N).Nodup := by
  unfold cellMenu
  rw [List.nodup_flatMap]
  constructor
  · intro P hP
    refine List.Nodup.map_on ?_ (nodup_shapeAssignments P)
    intro sh hsh sh' hsh' hc
    exact (mkCell_injective (mem_menuPaths_iff.mp hP) (mem_menuPaths_iff.mp hP)
      (mem_shapeAssignments.mp hsh) (mem_shapeAssignments.mp hsh') hc).2
  · have hnd : (menuPaths s N).Pairwise (· ≠ ·) := nodup_menuPaths s N
    refine hnd.imp_of_mem ?_
    intro P P' hP hP' hne c h1 h2
    rw [List.mem_map] at h1 h2
    obtain ⟨sh, hsh, rfl⟩ := h1
    obtain ⟨sh', hsh', heq⟩ := h2
    exact hne (mkCell_injective (mem_menuPaths_iff.mp hP) (mem_menuPaths_iff.mp hP')
      (mem_shapeAssignments.mp hsh) (mem_shapeAssignments.mp hsh') heq.symm).1

/-! ### The polygon-layer menu (deliverable 1's stated form) -/

/-- **All menu polygons** (the polygon representation `NodeConfig` carries). -/
def latticePaths (s N : ℕ) : List L4.LatticePolygon :=
  (menuPaths s N).map (mkPoly s)

theorem mem_latticePaths_iff {s N : ℕ} {pg : L4.LatticePolygon} :
    pg ∈ latticePaths s N ↔ ∃ P, MenuPath s N P ∧ pg = mkPoly s P := by
  unfold latticePaths
  rw [List.mem_map]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, mem_menuPaths_iff.mp hP, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, mem_menuPaths_iff.mpr hP, rfl⟩

theorem nodup_latticePaths (s N : ℕ) : (latticePaths s N).Nodup := by
  refine List.Nodup.map_on ?_ (nodup_menuPaths s N)
  intro P hP P' hP' h
  exact mkPoly_injective (mem_menuPaths_iff.mp hP) (mem_menuPaths_iff.mp hP') h

/-! ### Count gates (deliverable 1/2, cross-checked against W0's readable sub-menu:
paths 2/3/3 and cells 4/3/5 at `s = 2/3/4`, `N = 3` — `SUMMARY.md` per-s census headers). -/

example : (menuPaths 2 3).length = 2 := by decide
example : (menuPaths 3 3).length = 3 := by decide
example : (menuPaths 4 3).length = 3 := by decide

example : (latticePaths 2 3).length = 2 := by
  unfold latticePaths; rw [List.length_map]; decide
example : (latticePaths 3 3).length = 3 := by
  unfold latticePaths; rw [List.length_map]; decide
example : (latticePaths 4 3).length = 3 := by
  unfold latticePaths; rw [List.length_map]; decide

example : (cellMenu 2 3).length = 4 := by decide
example : (cellMenu 3 3).length = 3 := by decide
example : (cellMenu 4 3).length = 5 := by decide

/-- The s=2 menu paths' vertex lists, pinned explicitly (W0 `cells_s2.tsv` polygons). -/
example : menuPaths 2 3 = [[(0, 1), (2, 0)], [(0, 2), (2, 0)]] := by decide

/-! ## 5. Side lines over ℚ and the supporting-line geometry (the uniqueness engine)

The §2 pointwise-hull argument: a menu path is the upper envelope of its (extended) side lines;
every side line lies weakly below every vertex (`menuPath_supports`); two matched paths bound
each other's side lines pointwise; F4 strict-slope-increase turns pointwise equality of
envelopes into equality of vertex lists. -/

/-- The slope of a side pair, over ℚ. -/
def slopeQ (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℚ :=
  ((pr.2.2 : ℚ) - pr.1.2) / ((pr.2.1 : ℚ) - pr.1.1)

/-- The (extended) side line at abscissa `x`. -/
def lineAt (pr : (ℕ × ℕ) × (ℕ × ℕ)) (x : ℚ) : ℚ :=
  (pr.1.2 : ℚ) + slopeQ pr * (x - pr.1.1)

theorem lineAt_left (pr : (ℕ × ℕ) × (ℕ × ℕ)) : lineAt pr (pr.1.1 : ℚ) = pr.1.2 := by
  unfold lineAt; ring

theorem lineAt_step (pr : (ℕ × ℕ) × (ℕ × ℕ)) (x y : ℚ) :
    lineAt pr x = lineAt pr y + slopeQ pr * (x - y) := by
  unfold lineAt; ring

theorem lineAt_parab (pr : (ℕ × ℕ) × (ℕ × ℕ)) (x : ℚ) :
    lineAt pr (x - 1) + lineAt pr (x + 1) = 2 * lineAt pr x := by
  unfold lineAt; ring

theorem lineAt_right {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1) :
    lineAt pr (pr.2.1 : ℚ) = pr.2.2 := by
  have hne : ((pr.2.1 : ℚ) - pr.1.1) ≠ 0 := by
    have : (pr.1.1 : ℚ) < pr.2.1 := by exact_mod_cast hw
    linarith
  unfold lineAt slopeQ
  field_simp
  ring

/-- Cross-multiplied ℤ slope comparison ⟺ ℚ slope comparison. -/
theorem slopeLt_iff_slopeQ {a b c d : ℕ × ℕ} (hab : a.1 < b.1) (hcd : c.1 < d.1) :
    SlopeLt a b c d ↔ slopeQ (a, b) < slopeQ (c, d) := by
  have h1 : (0 : ℚ) < (b.1 : ℚ) - a.1 := by
    have : (a.1 : ℚ) < b.1 := by exact_mod_cast hab
    linarith
  have h2 : (0 : ℚ) < (d.1 : ℚ) - c.1 := by
    have : (c.1 : ℚ) < d.1 := by exact_mod_cast hcd
    linarith
  unfold slopeQ SlopeLt
  rw [div_lt_div_iff₀ h1 h2, ← Int.cast_lt (R := ℚ)]
  push_cast
  ring_nf

/-- Affine interpolation: a line below another line at both endpoints of a window is below on
the whole window. -/
theorem lineAt_le_of_endpoints {pr qr : (ℕ × ℕ) × (ℕ × ℕ)} {u v x : ℚ}
    (huv : u < v) (hx1 : u ≤ x) (hx2 : x ≤ v)
    (h1 : lineAt pr u ≤ lineAt qr u) (h2 : lineAt pr v ≤ lineAt qr v) :
    lineAt pr x ≤ lineAt qr x := by
  have key : (lineAt qr x - lineAt pr x) * (v - u)
      = (lineAt qr u - lineAt pr u) * (v - x) + (lineAt qr v - lineAt pr v) * (x - u) := by
    unfold lineAt; ring
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hx2),
    mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hx1)]

/-! ### Side-list structure of a path -/

theorem sidePairs_cons₂ (a b : ℕ × ℕ) (T : List (ℕ × ℕ)) :
    sidePairs (a :: b :: T) = (a, b) :: sidePairs (b :: T) := rfl

/-- Sides of a chain: window/height facts and endpoint memberships. -/
theorem chainOK_side_facts {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    ∀ pr ∈ sidePairs (p1 :: T), pr.1.1 < pr.2.1 ∧ pr.2.2 < pr.1.2 ∧
      pr.1 ∈ p1 :: T ∧ pr.2 ∈ p1 :: T := by
  induction h with
  | nil => intro pr hpr; simp [sidePairs] at hpr
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro pr hpr
      rw [sidePairs_cons₂, List.mem_cons] at hpr
      rcases hpr with rfl | hpr'
      · exact ⟨h1, h2, by simp, by simp⟩
      · obtain ⟨hw, hh, hm1, hm2⟩ := ih pr hpr'
        exact ⟨hw, hh, List.mem_cons_of_mem _ hm1, List.mem_cons_of_mem _ hm2⟩

theorem menuPath_side_facts {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P) :
    ∀ pr ∈ sidePairs P, pr.1.1 < pr.2.1 ∧ pr.2.2 < pr.1.2 ∧ pr.1 ∈ P ∧ pr.2 ∈ P := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := h
  intro pr hpr
  rw [sidePairs_cons₂, List.mem_cons] at hpr
  rcases hpr with rfl | hpr'
  · exact ⟨hp1, hpH, by simp, by simp⟩
  · obtain ⟨hw, hh, hm1, hm2⟩ := chainOK_side_facts hc pr hpr'
    exact ⟨hw, hh, List.mem_cons_of_mem _ hm1, List.mem_cons_of_mem _ hm2⟩

/-- Slope monotonicity along the chain: all later sides are strictly steeper (F4). -/
theorem chainOK_slope_lt {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    p0.1 < p1.1 → ∀ pr ∈ sidePairs (p1 :: T), slopeQ (p0, p1) < slopeQ pr := by
  induction h with
  | nil => intro _ pr hpr; simp [sidePairs] at hpr
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro hw pr hpr
      rw [sidePairs_cons₂, List.mem_cons] at hpr
      rcases hpr with rfl | hpr'
      · exact (slopeLt_iff_slopeQ hw h1).mp h3
      · exact lt_trans ((slopeLt_iff_slopeQ hw h1).mp h3) (ih h1 pr hpr')

/-- Vertices to the right of an edge lie weakly above its extended line. -/
theorem chainOK_above_line {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    p0.1 < p1.1 → ∀ q ∈ T, lineAt (p0, p1) (q.1 : ℚ) ≤ q.2 := by
  induction h with
  | nil => intro _ q hq; simp at hq
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro hw q hq
      have hslope : slopeQ (p0, p1) < slopeQ (p1, p2) := (slopeLt_iff_slopeQ hw h1).mp h3
      have hstep : lineAt (p0, p1) (p2.1 : ℚ)
          = (p1.2 : ℚ) + slopeQ (p0, p1) * ((p2.1 : ℚ) - p1.1) := by
        rw [lineAt_step (p0, p1) (p2.1 : ℚ) (p1.1 : ℚ), lineAt_right hw]
      have hstep2 : (p2.2 : ℚ) = (p1.2 : ℚ) + slopeQ (p1, p2) * ((p2.1 : ℚ) - p1.1) := by
        have hlr := lineAt_right (pr := (p1, p2)) h1
        rw [lineAt_step (p1, p2) (p2.1 : ℚ) (p1.1 : ℚ), lineAt_left] at hlr
        linarith [hlr]
      have hd : (0 : ℚ) < (p2.1 : ℚ) - p1.1 := by
        have : (p1.1 : ℚ) < p2.1 := by exact_mod_cast h1
        linarith
      rcases List.mem_cons.mp hq with rfl | hq'
      · -- q = p2
        rw [hstep, hstep2]
        nlinarith
      · -- q strictly beyond p2: compare against the (p1, p2) line, both through (p1.1, p1.2)
        have hih : lineAt (p1, p2) (q.1 : ℚ) ≤ q.2 := ih h1 q hq'
        have hq1 : (p1.1 : ℚ) ≤ q.1 := by
          have hb := (chainOK_mem_bounds h4 q hq').1
          have : p1.1 < q.1 := lt_trans h1 hb
          exact_mod_cast this.le
        have e1 : lineAt (p0, p1) (q.1 : ℚ)
            = (p1.2 : ℚ) + slopeQ (p0, p1) * ((q.1 : ℚ) - p1.1) := by
          rw [lineAt_step (p0, p1) (q.1 : ℚ) (p1.1 : ℚ), lineAt_right hw]
        have e2 : lineAt (p1, p2) (q.1 : ℚ)
            = (p1.2 : ℚ) + slopeQ (p1, p2) * ((q.1 : ℚ) - p1.1) := by
          rw [lineAt_step (p1, p2) (q.1 : ℚ) (p1.1 : ℚ), lineAt_left]
        nlinarith [mul_le_mul_of_nonneg_right hslope.le (by linarith : (0:ℚ) ≤ (q.1 : ℚ) - p1.1)]

/-- **Supporting-line property**: every side line of a menu path lies weakly below EVERY vertex
of the path (blueprint §2, the pointwise-hull half). -/
theorem chainOK_supports {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    p0.1 < p1.1 →
      ∀ pr ∈ sidePairs (p0 :: p1 :: T), ∀ q ∈ p0 :: p1 :: T, lineAt pr (q.1 : ℚ) ≤ q.2 := by
  induction h with
  | @nil a0 a1 h1 h2 =>
      intro hw pr hpr q hq
      have hpr' : pr = (a0, a1) := by simpa [sidePairs] using hpr
      subst hpr'
      rcases List.mem_cons.mp hq with rfl | hq'
      · rw [lineAt_left]
      · have hq2 : q = a1 := by simpa using hq'
        subst hq2
        rw [lineAt_right hw]
  | @cons a0 a1 a2 T' h1 h2 h3 h4 ih =>
      intro hw pr hpr q hq
      rw [sidePairs_cons₂, List.mem_cons] at hpr
      rcases hpr with rfl | hpr'
      · -- pr = (a0, a1)
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [lineAt_left]
        · rcases List.mem_cons.mp hq' with rfl | hq''
          · rw [lineAt_right hw]
          · exact chainOK_above_line (ChainOK.cons h1 h2 h3 h4) hw q hq''
      · -- pr is a later side
        rcases List.mem_cons.mp hq with heq | hq'
        · -- q = a0: leftward extension below the left endpoint
          rw [heq]
          have hp1 : lineAt pr (a1.1 : ℚ) ≤ a1.2 := ih h1 pr hpr' a1 (by simp)
          have hslope : slopeQ (a0, a1) < slopeQ pr :=
            chainOK_slope_lt (ChainOK.cons h1 h2 h3 h4) hw pr hpr'
          have hd : (0 : ℚ) < (a1.1 : ℚ) - a0.1 := by
            have : (a0.1 : ℚ) < a1.1 := by exact_mod_cast hw
            linarith
          have e1 : lineAt pr (a0.1 : ℚ)
              = lineAt pr (a1.1 : ℚ) - slopeQ pr * ((a1.1 : ℚ) - a0.1) := by
            rw [lineAt_step pr (a0.1 : ℚ) (a1.1 : ℚ)]; ring
          have e2 : (a1.2 : ℚ) = (a0.2 : ℚ) + slopeQ (a0, a1) * ((a1.1 : ℚ) - a0.1) := by
            have hlr := lineAt_right (pr := (a0, a1)) hw
            rw [lineAt_step (a0, a1) (a1.1 : ℚ) (a0.1 : ℚ), lineAt_left] at hlr
            linarith [hlr]
          rw [e1]
          nlinarith [mul_le_mul_of_nonneg_right hslope.le (le_of_lt hd)]
        · exact ih h1 pr hpr' q hq'

theorem menuPath_supports {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P) :
    ∀ pr ∈ sidePairs P, ∀ q ∈ P, lineAt pr (q.1 : ℚ) ≤ q.2 := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := h
  exact chainOK_supports hc hp1

/-- Every abscissa `≤ s` lies in the window of some side. -/
theorem chainOK_containing {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : ∀ i : ℕ, p0.1 ≤ i → i ≤ s →
      ∃ pr ∈ sidePairs (p0 :: p1 :: T), pr.1.1 ≤ i ∧ i ≤ pr.2.1 := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      intro i hi0 his
      exact ⟨(p0, p1), by simp [sidePairs], hi0, show i ≤ p1.1 by omega⟩
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro i hi0 his
      by_cases hle : i ≤ p1.1
      · exact ⟨(p0, p1), by rw [sidePairs_cons₂]; simp, hi0, hle⟩
      · obtain ⟨pr, hpr, hw1, hw2⟩ := ih i (by omega) his
        exact ⟨pr, by rw [sidePairs_cons₂]; exact List.mem_cons_of_mem _ hpr, hw1, hw2⟩

theorem menuPath_containing {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P)
    {i : ℕ} (his : i ≤ s) : ∃ pr ∈ sidePairs P, pr.1.1 ≤ i ∧ i ≤ pr.2.1 := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := h
  exact chainOK_containing hc i (Nat.zero_le i) his

/-- Every non-left vertex is the right endpoint of some side. -/
theorem chainOK_side_ending {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : ∀ x ∈ p1 :: T, ∃ pr ∈ sidePairs (p0 :: p1 :: T), pr.2 = x := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      intro x hx
      have hx1 : x = p1 := by simpa using hx
      exact ⟨(p0, p1), by simp [sidePairs], hx1.symm⟩
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨(p0, x), by rw [sidePairs_cons₂]; simp, rfl⟩
      · obtain ⟨pr, hpr, hpr2⟩ := ih x hx'
        exact ⟨pr, by rw [sidePairs_cons₂]; exact List.mem_cons_of_mem _ hpr, hpr2⟩

/-- Every non-right vertex is the left endpoint of some side. -/
theorem chainOK_side_starting {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    ∀ x ∈ p0 :: p1 :: T, x.1 ≠ s → ∃ pr ∈ sidePairs (p0 :: p1 :: T), pr.1 = x := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      intro x hx hxs
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨(x, p1), by simp [sidePairs], rfl⟩
      · have : x = p1 := by simpa using hx'
        exact absurd (this ▸ h1) hxs
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro x hx hxs
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨(x, p1), by rw [sidePairs_cons₂]; simp, rfl⟩
      · obtain ⟨pr, hpr, hpr1⟩ := ih x hx' hxs
        exact ⟨pr, by rw [sidePairs_cons₂]; exact List.mem_cons_of_mem _ hpr, hpr1⟩

/-- The sides list is slope-sorted with disjoint windows (pairwise, in list order). -/
theorem chainOK_sides_pairwise {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    p0.1 < p1.1 →
      (sidePairs (p0 :: p1 :: T)).Pairwise
        (fun pr pr' => slopeQ pr < slopeQ pr' ∧ pr.2.1 ≤ pr'.1.1) := by
  induction h with
  | nil => intro _; simp [sidePairs]
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      intro hw
      rw [sidePairs_cons₂, List.pairwise_cons]
      constructor
      · intro pr hpr
        refine ⟨chainOK_slope_lt (ChainOK.cons h1 h2 h3 h4) hw pr hpr, ?_⟩
        obtain ⟨_, _, hm1, _⟩ := chainOK_side_facts (ChainOK.cons h1 h2 h3 h4) pr hpr
        rcases List.mem_cons.mp hm1 with heq | hm1'
        · rw [← heq]
        · exact ((chainOK_mem_bounds (ChainOK.cons h1 h2 h3 h4) _ hm1').1).le
      · exact ih h1

/-- Pairwise members compare in one order or the other. -/
theorem pairwise_mem_rel {α : Type*} {r : α → α → Prop} {l : List α}
    (h : l.Pairwise r) {a b : α} (ha : a ∈ l) (hb : b ∈ l) :
    a = b ∨ r a b ∨ r b a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
      rw [List.pairwise_cons] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (h.1 b hb'))
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inr (Or.inr (h.1 a ha'))
        · exact ih h.2 ha' hb'

/-- Two sides sharing a vertex (right endpoint of one = left endpoint of the other) have
strictly increasing slopes — F4 maximality at interior vertices. -/
theorem menuPath_adjacent_slopes {s N : ℕ} {P : List (ℕ × ℕ)} (h : MenuPath s N P)
    {prL prR : (ℕ × ℕ) × (ℕ × ℕ)} (hL : prL ∈ sidePairs P) (hR : prR ∈ sidePairs P)
    (hshare : prL.2 = prR.1) : slopeQ prL < slopeQ prR := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := h
  have hpw := chainOK_sides_pairwise hc hp1
  rcases pairwise_mem_rel hpw hL hR with heq | hrel | hrel
  · -- same side: contradicts strict width
    obtain ⟨hwL, _, _, _⟩ := menuPath_side_facts ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ prL hL
    rw [heq] at hwL hshare ⊢
    exact absurd (congrArg Prod.fst hshare) (by omega)
  · exact hrel.1
  · -- flipped order contradicts the windows
    obtain ⟨hwL, _, _, _⟩ := menuPath_side_facts ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ prL hL
    obtain ⟨hwR, _, _, _⟩ := menuPath_side_facts ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ prR hR
    have : prR.2.1 ≤ prL.1.1 := hrel.2
    have : prR.1.1 = prL.2.1 := (congrArg Prod.fst hshare).symm
    omega

/-! ## 6. The membership predicate `InCell` (deliverable 3)

Conditions on a box element `f` against menu data `(P, sh)` (blueprint §2, W0
`menu_semantics.matches`, all certifiable at level `N` since menu heights are `≤ N−1`):
  (i)  valuation ≥ path at every index of every side window (`SideAbove`, over ℚ via `lineAt`);
  (ii) EXACT valuation at every vertex (`zmodValuation … = v`, both endpoints included);
  (iii) per side, the factorization SHAPE of the residual polynomial
       (`M4.residualPoly` on `B.boxCoeffData` — the REAL classifier-side residual reader)
       equals the assigned `(D, μ)` multiset. -/

section Box

variable (p : ℕ) [hp : Fact p.Prime]

/-- The capped native valuation vector of a box element. -/
noncomputable def vOf {N n : ℕ} (f : QuotientBox.monicBox p N n) (i : ℕ) : ℕ :=
  PadicLift.zmodValuation p N ((f.1).coeff i)

/-- Packaging a side pair as the classifier-side `NewtonPolygon.Side`
(`⟨i₀, j₀, v₀, v₁⟩` = left abscissa, right abscissa, left height, right height). -/
def mkSide (pr : (ℕ × ℕ) × (ℕ × ℕ)) : NewtonPolygon.Side :=
  ⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩

/-- The order-1 residual polynomial of `f` on a side — literally the classifier's reader
(`M4.residualPoly` over `B.boxCoeffData`, D7 on-side guard included). -/
noncomputable def residualOf {N n : ℕ} (f : QuotientBox.monicBox p N n)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) : (ZMod p)[X] :=
  M4.residualPoly (B.boxCoeffData p N (mkSide pr) f) (mkSide pr)

/-- The factorization shape of a polynomial over `ZMod p`: the multiset of
`(degree, multiplicity)` over its distinct monic irreducible factors
(`normalizedFactors`; unit-invariant, so F3's monic pre-normalization is built in). -/
noncomputable def polyShape (R : (ZMod p)[X]) : Multiset (ℕ × ℕ) :=
  letI := Classical.decEq ((ZMod p)[X])
  (UniqueFactorizationMonoid.normalizedFactors R).toFinset.val.map
    fun ψ => (ψ.natDegree, (UniqueFactorizationMonoid.normalizedFactors R).count ψ)

/-- Condition (i) on one side: every dot of the window lies on or above the side line. -/
def SideAbove {N n : ℕ} (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  ∀ i : ℕ, pr.1.1 ≤ i → i ≤ pr.2.1 → lineAt pr (i : ℚ) ≤ (vOf p f i : ℚ)

/-- Conditions (i)+(iii) on one side. -/
def SideMatch {N n : ℕ} (f : QuotientBox.monicBox p N n) (shape : List (ℕ × ℕ))
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  SideAbove p f pr ∧ polyShape p (residualOf p f pr) = (shape : Multiset (ℕ × ℕ))

/-- **The full match of `f` against menu data `(P, sh)`**: vertex exactness (ii) plus the
per-side conditions (i)+(iii). -/
def Matches {N s : ℕ} (f : QuotientBox.monicBox p N s) (P : List (ℕ × ℕ))
    (sh : List (List (ℕ × ℕ))) : Prop :=
  (∀ q ∈ P, vOf p f q.1 = q.2) ∧ List.Forall₂ (fun l pr => SideMatch p f l pr) sh (sidePairs P)

/-- **THE MEMBERSHIP PREDICATE** (deliverable 3): `f` lies in the cell `c` iff `c` is the menu
cell of some valid menu data `(P, sh)` that `f` matches. (`mkCell` is injective on menu data —
`mkCell_injective` — so the data is uniquely determined by `c`.) -/
def InCell {N s : ℕ} (f : QuotientBox.monicBox p N s) (c : NodeConfig) : Prop :=
  ∃ P sh, MenuPath s N P ∧ ShapesFor P sh ∧ c = mkCell s P sh ∧ Matches p f P sh

theorem inCell_mem_cellMenu {N s : ℕ} {f : QuotientBox.monicBox p N s} {c : NodeConfig}
    (h : InCell p f c) : c ∈ cellMenu s N := by
  obtain ⟨P, sh, hP, hsh, rfl, _⟩ := h
  exact mem_cellMenu_iff.mpr ⟨P, sh, hP, hsh, rfl⟩

/-! ## 6b. Multi-block cell membership `InCellMulti` (W4d2-surj deliverable 1)

`InCell` records, per side, only the residual factorization SHAPE (`polyShape`).  A *multi-block*
cell additionally pins, per side, the *root-refined* residual polynomial — the concrete monic
`R_S ∈ (ZMod p)[X]` whose `polyShape` is the recorded shape, and which factors over `ZMod p` into
the per-block coprime pieces `(y − c̃₁)^{μ₁} · (y − c̃₂)^{μ₂} · ⋯` of that side.  A *block* of the
cell is one `(side, residual-irreducible-factor)` pair (blueprint §W4d (d2); the d2-0 gate's
"block grouping convention"), so the residual pin `resid` is precisely the data distinguishing the
blocks that share a side (cases B, C) as well as tying each side to its factors (case A).

`InCellMulti f c resid` = `f ∈ InCell c` PLUS the per-side residual pin: `residualOf f` on each
side of the (concatenated) polygon equals the assigned target in `resid`.  This is the whole-cell
generalization of `RestartEquiv.InCellAt` (which pins a SINGLE side to `(X − c̄)^μ`); here the
polygon may have several sides and each side's residual may factor into several coprime roots.

Since the extra data is a per-side EQUALITY of the residual reader (a pure refinement of the
`polyShape` condition already inside `Matches`), the shape-only / single-block base case reduces to
`InCell` exactly — see `inCellMulti_single`.  All of `InCell`'s hull/uniqueness theory transfers
through the `InCell` conjunct unchanged (this is a purely ADDITIVE extension; nothing downstream of
`InCell` is touched). -/

/-- Per-side residual pin: `resid` assigns one monic target residual polynomial to every side of
`P`, and each target's `polyShape` is the side's recorded shape (so the pin refines, and is
consistent with, the shape data of `sh`).  `ResidRefines` is the well-formedness predicate on the
refinement datum. -/
def ResidRefines {N s : ℕ} (f : QuotientBox.monicBox p N s) (P : List (ℕ × ℕ))
    (resid : List ((ZMod p)[X])) : Prop :=
  List.Forall₂ (fun R pr => residualOf p f pr = R) resid (sidePairs P)

/-- **`InCellMulti` (deliverable 1): multi-block cell membership.**  `f` lies in the multi-block
cell `(c, resid)` iff `f` lies in the shape cell `c` (concatenated polygon + per-side shapes) AND
the residual reader on each side of the polygon equals the pinned root-refined target `resid`.

Concretely: there is menu data `(P, sh)` with `c = mkCell s P sh` such that `Matches f P sh` (the
`InCell` conditions: (i) on/above every side, (ii) vertex exactness, (iii) the residual SHAPE per
side) and, per side, `residualOf f = resid`.  The single-side / shape-determined base case is
`InCell` (`inCellMulti_single`). -/
def InCellMulti {N s : ℕ} (f : QuotientBox.monicBox p N s) (c : NodeConfig)
    (resid : List ((ZMod p)[X])) : Prop :=
  ∃ P sh, MenuPath s N P ∧ ShapesFor P sh ∧ c = mkCell s P sh ∧ Matches p f P sh ∧
    ResidRefines p f P resid

/-- `InCellMulti` refines `InCell`: the shape cell membership is a direct consequence (drop the
residual pin). -/
theorem inCellMulti_inCell {N s : ℕ} {f : QuotientBox.monicBox p N s} {c : NodeConfig}
    {resid : List ((ZMod p)[X])} (h : InCellMulti p f c resid) : InCell p f c := by
  obtain ⟨P, sh, hP, hsh, hc, hm, _⟩ := h
  exact ⟨P, sh, hP, hsh, hc, hm⟩

/-- The tautological residual pin of `f` against a path `P`: read the residual off each side. -/
noncomputable def residOf {N s : ℕ} (f : QuotientBox.monicBox p N s) (P : List (ℕ × ℕ)) :
    List ((ZMod p)[X]) :=
  (sidePairs P).map (residualOf p f)

theorem residOf_refines {N s : ℕ} (f : QuotientBox.monicBox p N s) (P : List (ℕ × ℕ)) :
    ResidRefines p f P (residOf p f P) := by
  unfold ResidRefines residOf
  induction sidePairs P with
  | nil => exact List.Forall₂.nil
  | cons pr rest ih =>
      rw [List.map_cons]
      exact List.Forall₂.cons rfl ih

/-- **`inCellMulti_single` (deliverable 1): the base case is `InCell`.**  Taking the residual pin
to be `f`'s own tautological residual read (`residOf` — the shape-determined refinement), the
multi-block membership `InCellMulti f c (residOf f P)` collapses to plain `InCell f c`.  This is
the sense in which the single-block / shape-only cell is defeq-simple to the existing `InCell`: the
refinement adds no constraint precisely when the residual is read from `f` itself.  (For a genuine
root refinement — a fixed `resid` not read from `f` — `InCellMulti` is strictly stronger, which is
the multi-block content; see `InCellMulti` docstring.) -/
theorem inCellMulti_single {N s : ℕ} {f : QuotientBox.monicBox p N s} {P : List (ℕ × ℕ)}
    {sh : List (List (ℕ × ℕ))} (hP : MenuPath s N P) (hsh : ShapesFor P sh) :
    InCellMulti p f (mkCell s P sh) (residOf p f P) ↔ InCell p f (mkCell s P sh) := by
  constructor
  · exact inCellMulti_inCell p
  · rintro ⟨P', sh', hP', hsh', heq, hm⟩
    obtain ⟨rfl, rfl⟩ := mkCell_injective hP' hP hsh' hsh heq.symm
    exact ⟨P', sh', hP', hsh', rfl, hm, residOf_refines p f P'⟩

theorem inCell_mkCell_iff {N s : ℕ} {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))} (hP : MenuPath s N P) (hsh : ShapesFor P sh) :
    InCell p f (mkCell s P sh) ↔ Matches p f P sh := by
  constructor
  · rintro ⟨P', sh', hP', hsh', heq, hm⟩
    obtain ⟨rfl, rfl⟩ := mkCell_injective hP' hP hsh' hsh heq.symm
    exact hm
  · intro hm
    exact ⟨P, sh, hP, hsh, rfl, hm⟩

/-! ### Uniqueness (deliverable 4): the §2 pointwise-hull argument -/

/-- `Forall₂` extraction on the right list. -/
theorem forall₂_mem_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b := by
  intro l l' h
  induction h with
  | nil => intro b hb; simp at hb
  | cons ha hrest ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨_, by simp, ha⟩
      · obtain ⟨a, hal, har⟩ := ih b hb'
        exact ⟨a, List.mem_cons_of_mem _ hal, har⟩

/-- All side conditions (i) of a match, extracted per side. -/
theorem matches_sideAbove {N s : ℕ} {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))} (hm : Matches p f P sh) :
    ∀ pr ∈ sidePairs P, SideAbove p f pr := by
  intro pr hpr
  obtain ⟨l, _, hl⟩ := forall₂_mem_right hm.2 pr hpr
  exact hl.1

/-- **Claim A of the hull argument**: every side line of a MATCHED path is a global lower bound
for the valuation vector on `[0, s]` (containing side + supports + interpolation). -/
theorem matched_line_le {N s : ℕ} {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))} (hP : MenuPath s N P)
    (hm : Matches p f P sh) :
    ∀ pr ∈ sidePairs P, ∀ j : ℕ, j ≤ s → lineAt pr (j : ℚ) ≤ (vOf p f j : ℚ) := by
  intro pr hpr j hj
  obtain ⟨prc, hprc, hc1, hc2⟩ := menuPath_containing hP hj
  obtain ⟨hwc, _, hmem1, hmem2⟩ := menuPath_side_facts hP prc hprc
  have hsup := menuPath_supports hP
  -- pr's line below prc's line on prc's window (equality of prc's line with vertex heights)
  have hL : lineAt pr (prc.1.1 : ℚ) ≤ lineAt prc (prc.1.1 : ℚ) := by
    rw [lineAt_left]
    exact hsup pr hpr prc.1 hmem1
  have hR : lineAt pr (prc.2.1 : ℚ) ≤ lineAt prc (prc.2.1 : ℚ) := by
    rw [lineAt_right hwc]
    exact hsup pr hpr prc.2 hmem2
  have huv : (prc.1.1 : ℚ) < prc.2.1 := by exact_mod_cast hwc
  have hmid : lineAt pr (j : ℚ) ≤ lineAt prc (j : ℚ) :=
    lineAt_le_of_endpoints huv (by exact_mod_cast hc1) (by exact_mod_cast hc2) hL hR
  exact le_trans hmid (matches_sideAbove p hm prc hprc j hc1 hc2)

/-- **Claim B of the hull argument**: any side line of one matched path is below any side line
of the other matched path, on the latter's window. -/
theorem matched_line_le_line {N s : ℕ} {f : QuotientBox.monicBox p N s}
    {P P' : List (ℕ × ℕ)} {sh sh' : List (List (ℕ × ℕ))}
    (hP : MenuPath s N P) (hP' : MenuPath s N P')
    (hm : Matches p f P sh) (hm' : Matches p f P' sh') :
    ∀ pr ∈ sidePairs P, ∀ pr' ∈ sidePairs P', ∀ x : ℚ,
      (pr'.1.1 : ℚ) ≤ x → x ≤ (pr'.2.1 : ℚ) → lineAt pr x ≤ lineAt pr' x := by
  intro pr hpr pr' hpr' x hx1 hx2
  obtain ⟨hw', _, hmem1', hmem2'⟩ := menuPath_side_facts hP' pr' hpr'
  have hs1 : pr'.1.1 ≤ s := menuPath_mem_le hP' _ hmem1'
  have hs2 : pr'.2.1 ≤ s := menuPath_mem_le hP' _ hmem2'
  -- endpoints of pr' are exact vertices of P', hence bound pr's line via Claim A
  have hex1 : vOf p f pr'.1.1 = pr'.1.2 := hm'.1 pr'.1 hmem1'
  have hex2 : vOf p f pr'.2.1 = pr'.2.2 := hm'.1 pr'.2 hmem2'
  have hL : lineAt pr (pr'.1.1 : ℚ) ≤ lineAt pr' (pr'.1.1 : ℚ) := by
    rw [lineAt_left]
    have := matched_line_le p hP hm pr hpr pr'.1.1 hs1
    rw [hex1] at this
    exact this
  have hR : lineAt pr (pr'.2.1 : ℚ) ≤ lineAt pr' (pr'.2.1 : ℚ) := by
    rw [lineAt_right hw']
    have := matched_line_le p hP hm pr hpr pr'.2.1 hs2
    rw [hex2] at this
    exact this
  exact lineAt_le_of_endpoints (by exact_mod_cast hw') hx1 hx2 hL hR

/-- **Path uniqueness** (the heart of deliverable 4): two menu paths matched by the same box
element are EQUAL. Requires F4 maximality (strict slope increase at interior vertices). -/
theorem matched_path_unique {N s : ℕ} {f : QuotientBox.monicBox p N s}
    {P P' : List (ℕ × ℕ)} {sh sh' : List (List (ℕ × ℕ))}
    (hP : MenuPath s N P) (hP' : MenuPath s N P')
    (hm : Matches p f P sh) (hm' : Matches p f P' sh') : P = P' := by
  have main : ∀ (Q Q' : List (ℕ × ℕ)) (shQ shQ' : List (List (ℕ × ℕ))),
      MenuPath s N Q → MenuPath s N Q' → Matches p f Q shQ → Matches p f Q' shQ' →
      ∀ x ∈ Q, x ∈ Q' := by
    intro Q Q' shQ shQ' hQ hQ' hmQ hmQ' x hx
    obtain ⟨j, v⟩ := x
    have hjs : j ≤ s := menuPath_mem_le hQ _ hx
    have hvw : vOf p f j = v := hmQ.1 (j, v) hx
    rcases Nat.eq_or_lt_of_le hjs with hjeq | hjlt
    · -- j = s
      subst hjeq
      have : v = 0 := menuPath_s_height hQ hx
      subst this
      exact menuPath_last_mem hQ'
    by_cases hmem : j ∈ Q'.map Prod.fst
    · -- j is a vertex abscissa of Q': heights agree via exactness
      rw [List.mem_map] at hmem
      obtain ⟨q', hq', hj'⟩ := hmem
      have : vOf p f j = q'.2 := by rw [← hj']; exact hmQ'.1 q' hq'
      have hxq : (j, v) = q' := Prod.ext hj'.symm (by rw [← hvw, this])
      rw [hxq]; exact hq'
    · -- j is interior to a side of Q': contradiction with F4 strictness
      exfalso
      -- j ≠ 0 (0 is a vertex abscissa of Q')
      have hQ'0 : ∃ H', (0, H') ∈ Q' := by
        obtain ⟨H', p1', T', rfl, _, _, _, _, _⟩ := hQ'
        exact ⟨H', by simp⟩
      obtain ⟨H', hH'mem⟩ := hQ'0
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hmem (List.mem_map.mpr ⟨(0, H'), hH'mem, rfl⟩)
      -- containing side of Q', strictly
      obtain ⟨pr', hpr', hc1, hc2⟩ := menuPath_containing hQ' hjs
      obtain ⟨hw', hh', hm1', hm2'⟩ := menuPath_side_facts hQ' pr' hpr'
      have hne1 : pr'.1.1 ≠ j := fun h =>
        hmem (List.mem_map.mpr ⟨pr'.1, hm1', h⟩)
      have hne2 : pr'.2.1 ≠ j := fun h =>
        hmem (List.mem_map.mpr ⟨pr'.2, hm2', h⟩)
      have hstrict1 : pr'.1.1 < j := lt_of_le_of_ne hc1 hne1
      have hstrict2 : j < pr'.2.1 := lt_of_le_of_ne hc2 (Ne.symm hne2)
      -- adjacent sides of Q at (j, v)
      have hLex : ∃ pr ∈ sidePairs Q, pr.2 = ((j, v) : ℕ × ℕ) := by
        obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := hQ
        have hxQ : ((j, v) : ℕ × ℕ) ∈ p1 :: T := by
          rcases List.mem_cons.mp hx with heq | h'
          · exact absurd (congrArg Prod.fst heq) (by simpa using hj0)
          · exact h'
        exact chainOK_side_ending hc (j, v) hxQ
      have hRex : ∃ pr ∈ sidePairs Q, pr.1 = ((j, v) : ℕ × ℕ) := by
        obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := hQ
        exact chainOK_side_starting hc (j, v) hx (by simpa using hjlt.ne)
      obtain ⟨prL, hprL, hprL2⟩ := hLex
      obtain ⟨prR, hprR, hprR1⟩ := hRex
      have hslopes : slopeQ prL < slopeQ prR :=
        menuPath_adjacent_slopes hQ hprL hprR (hprL2.trans hprR1.symm)
      obtain ⟨hwL, _, hmL1, _⟩ := menuPath_side_facts hQ prL hprL
      obtain ⟨hwR, _, _, hmR2⟩ := menuPath_side_facts hQ prR hprR
      have hLj : prL.2.1 = j := by rw [hprL2]
      have hRj : prR.1.1 = j := by rw [hprR1]
      -- the four double-bounded line equalities at j−1, j, j+1
      have hB := matched_line_le_line p hQ hQ' hmQ hmQ'
      have hB' := matched_line_le_line p hQ' hQ hmQ' hmQ
      have hj1 : (1 : ℚ) ≤ (j : ℚ) := by
        have : 1 ≤ j := by omega
        exact_mod_cast this
      have hwin1 : (pr'.1.1 : ℚ) ≤ (j : ℚ) - 1 := by
        have : pr'.1.1 ≤ j - 1 := by omega
        have hcast : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ j)]; ring
        calc (pr'.1.1 : ℚ) ≤ ((j - 1 : ℕ) : ℚ) := by exact_mod_cast this
          _ = (j : ℚ) - 1 := hcast
      have hwin2 : (j : ℚ) + 1 ≤ (pr'.2.1 : ℚ) := by
        have : j + 1 ≤ pr'.2.1 := by omega
        exact_mod_cast this
      have hwinj1 : (pr'.1.1 : ℚ) ≤ (j : ℚ) := by
        have := hstrict1.le; exact_mod_cast this
      have hwinj2 : (j : ℚ) ≤ (pr'.2.1 : ℚ) := by
        have := hstrict2.le; exact_mod_cast this
      have hLwin1 : (prL.1.1 : ℚ) ≤ (j : ℚ) - 1 := by
        have : prL.1.1 + 1 ≤ j := by omega
        have h2 : ((prL.1.1 + 1 : ℕ) : ℚ) ≤ (j : ℚ) := by exact_mod_cast this
        push_cast at h2
        linarith
      have hLwin2 : (j : ℚ) - 1 ≤ (prL.2.1 : ℚ) := by
        rw [hLj]; linarith
      have hLwinj : (j : ℚ) ≤ (prL.2.1 : ℚ) := by rw [hLj]
      have hLwinj1 : (prL.1.1 : ℚ) ≤ (j : ℚ) := by linarith
      have hRwin1 : (prR.1.1 : ℚ) ≤ (j : ℚ) + 1 := by rw [hRj]; linarith
      have hRwin2 : (j : ℚ) + 1 ≤ (prR.2.1 : ℚ) := by
        have : j + 1 ≤ prR.2.1 := by omega
        exact_mod_cast this
      have hRwinj : (prR.1.1 : ℚ) ≤ (j : ℚ) := by rw [hRj]
      have hRwinj2 : (j : ℚ) ≤ (prR.2.1 : ℚ) := by
        have := (hRj ▸ hwR).le
        calc (j : ℚ) ≤ (j : ℚ) + 1 := by linarith
          _ ≤ (prR.2.1 : ℚ) := hRwin2
      -- equalities
      have e1 : lineAt prL ((j : ℚ) - 1) = lineAt pr' ((j : ℚ) - 1) :=
        le_antisymm (hB prL hprL pr' hpr' _ hwin1 (by linarith))
          (hB' pr' hpr' prL hprL _ hLwin1 hLwin2)
      have e2 : lineAt prL (j : ℚ) = lineAt pr' (j : ℚ) :=
        le_antisymm (hB prL hprL pr' hpr' _ hwinj1 hwinj2)
          (hB' pr' hpr' prL hprL _ hLwinj1 hLwinj)
      have e3 : lineAt prR (j : ℚ) = lineAt pr' (j : ℚ) :=
        le_antisymm (hB prR hprR pr' hpr' _ hwinj1 hwinj2)
          (hB' pr' hpr' prR hprR _ hRwinj hRwinj2)
      have e4 : lineAt prR ((j : ℚ) + 1) = lineAt pr' ((j : ℚ) + 1) :=
        le_antisymm (hB prR hprR pr' hpr' _ (by linarith) hwin2)
          (hB' pr' hpr' prR hprR _ hRwin1 hRwin2)
      -- affine identities
      have hpar : lineAt pr' ((j : ℚ) - 1) + lineAt pr' ((j : ℚ) + 1)
          = 2 * lineAt pr' (j : ℚ) := lineAt_parab pr' (j : ℚ)
      have hLstep : lineAt prL ((j : ℚ) - 1) = lineAt prL (j : ℚ) - slopeQ prL := by
        rw [lineAt_step prL ((j : ℚ) - 1) (j : ℚ)]; ring
      have hRstep : lineAt prR ((j : ℚ) + 1) = lineAt prR (j : ℚ) + slopeQ prR := by
        rw [lineAt_step prR ((j : ℚ) + 1) (j : ℚ)]; ring
      -- combine: slopeQ prR = slopeQ prL, contradicting strictness
      have : slopeQ prR = slopeQ prL := by linarith [e1, e2, e3, e4, hpar, hLstep, hRstep]
      linarith [hslopes]
  have hpw := menuPath_pairwise hP
  have hpw' := menuPath_pairwise hP'
  haveI : Std.Antisymm (fun (a b : ℕ × ℕ) => a.1 < b.1 ∧ b.2 < a.2) :=
    ⟨fun a b hab hba => absurd hba.1 (by omega)⟩
  haveI : Std.Irrefl (fun (a b : ℕ × ℕ) => a.1 < b.1 ∧ b.2 < a.2) :=
    ⟨fun a h => by omega⟩
  refine List.Pairwise.eq_of_mem_iff hpw hpw' ?_
  intro x
  exact ⟨main P P' sh sh' hP hP' hm hm' x, main P' P sh' sh hP' hP hm' hm x⟩

/-- Shape-list uniqueness given the path: the residual shapes are read off `f`, and canonically
sorted lists representing the same multiset are equal. -/
theorem matched_shapes_unique {N s : ℕ} {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} {sh sh' : List (List (ℕ × ℕ))}
    (hs1 : ShapesFor P sh) (hs2 : ShapesFor P sh')
    (hm1 : Matches p f P sh) (hm2 : Matches p f P sh') : sh = sh' := by
  have key : ∀ (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (l1 l2 : List (List (ℕ × ℕ))),
      List.Forall₂ (fun l pr => SideMatch p f l pr) l1 prs →
      List.Forall₂ (fun l pr => SideMatch p f l pr) l2 prs →
      List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr)) l1 prs →
      List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr)) l2 prs →
      l1 = l2 := by
    intro prs
    induction prs with
    | nil =>
        intro l1 l2 h1 h2 _ _
        rw [List.forall₂_nil_right_iff] at h1 h2
        rw [h1, h2]
    | cons pr prs ih =>
        intro l1 l2 h1 h2 hv1 hv2
        rw [List.forall₂_cons_right_iff] at h1 h2
        obtain ⟨a1, t1, ha1, ht1, rfl⟩ := h1
        obtain ⟨a2, t2, ha2, ht2, rfl⟩ := h2
        rw [List.forall₂_cons] at hv1 hv2
        have hmul : (a1 : Multiset (ℕ × ℕ)) = (a2 : Multiset (ℕ × ℕ)) := by
          rw [← ha1.2, ← ha2.2]
        have hperm : a1.Perm a2 := Multiset.coe_eq_coe.mp hmul
        have hsort1 : a1.Pairwise shapeLE := (mem_shapesOfDegree_iff.mp hv1.1).1
        have hsort2 : a2.Pairwise shapeLE := (mem_shapesOfDegree_iff.mp hv2.1).1
        rw [hperm.eq_of_pairwise' hsort1 hsort2, ih t1 t2 ht1 ht2 hv1.2 hv2.2]
  exact key (sidePairs P) sh sh' hm1.2 hm2.2 hs1 hs2

/-- **`cell_unique`** (deliverable 4, blueprint §2 uniqueness): a box element matches AT MOST
ONE menu cell. W0 verified this holds only under the F4 maximal-path convention; the
`matched_path_unique` step is exactly where the no-collinear-interior-vertices property enters
(via `menuPath_adjacent_slopes`). -/
theorem inCell_unique {N s : ℕ} {f : QuotientBox.monicBox p N s} {c1 c2 : NodeConfig}
    (h1 : InCell p f c1) (h2 : InCell p f c2) : c1 = c2 := by
  obtain ⟨P1, sh1, hP1, hs1, rfl, hm1⟩ := h1
  obtain ⟨P2, sh2, hP2, hs2, rfl, hm2⟩ := h2
  have hpp : P1 = P2 := matched_path_unique p hP1 hP2 hm1 hm2
  subst hpp
  rw [matched_shapes_unique p hs1 hs2 hm1 hm2]

/-- `cell_unique`, spelled on menu membership (the blueprint form: at most one `c ∈ cellMenu`
matches; membership is in fact automatic — `inCell_mem_cellMenu`). -/
theorem cell_unique {N s : ℕ} (f : QuotientBox.monicBox p N s) {c1 c2 : NodeConfig}
    (_hc1 : c1 ∈ cellMenu s N) (_hc2 : c2 ∈ cellMenu s N)
    (h1 : InCell p f c1) (h2 : InCell p f c2) : c1 = c2 :=
  inCell_unique p h1 h2

/-! ## 7. Side arithmetic and residual-shape facts (existence inputs, F3 conventions) -/

/-- All vertex heights of a menu path are `≤ N − 1` (F5: certified reads). -/
theorem menuPath_height_le {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P) :
    ∀ q ∈ P, q.2 ≤ N - 1 := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := hP
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact hH2
  · rcases List.mem_cons.mp hq' with rfl | hq''
    · omega
    · have := (chainOK_mem_bounds hc q hq'').2
      omega

/-- The reduced-slope data of a side: `e = run/g`, `h = −drop/g`, `residualDeg = g = sideDeg`,
where `drop = v₀ − v₁`, `run = j₁ − j₀`, `g = gcd(drop, run)`. -/
theorem side_data {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    (mkSide pr).e = (pr.2.1 - pr.1.1) / sideDeg pr
    ∧ (mkSide pr).h = -((((pr.1.2 - pr.2.2) / sideDeg pr : ℕ)) : ℤ)
    ∧ M4.residualDeg (mkSide pr) = sideDeg pr
    ∧ sideDeg pr * ((pr.2.1 - pr.1.1) / sideDeg pr) = pr.2.1 - pr.1.1
    ∧ sideDeg pr * ((pr.1.2 - pr.2.2) / sideDeg pr) = pr.1.2 - pr.2.2
    ∧ 0 < (pr.2.1 - pr.1.1) / sideDeg pr ∧ 0 < (pr.1.2 - pr.2.2) / sideDeg pr := by
  have hdrop : 0 < pr.1.2 - pr.2.2 := by omega
  have hrun : 0 < pr.2.1 - pr.1.1 := by omega
  have hg : 0 < sideDeg pr := Nat.gcd_pos_of_pos_left _ hdrop
  have hgd : sideDeg pr ∣ (pr.1.2 - pr.2.2) := Nat.gcd_dvd_left _ _
  have hge : sideDeg pr ∣ (pr.2.1 - pr.1.1) := Nat.gcd_dvd_right _ _
  have hgh : sideDeg pr * ((pr.1.2 - pr.2.2) / sideDeg pr) = pr.1.2 - pr.2.2 :=
    Nat.mul_div_cancel' hgd
  have hge' : sideDeg pr * ((pr.2.1 - pr.1.1) / sideDeg pr) = pr.2.1 - pr.1.1 :=
    Nat.mul_div_cancel' hge
  have hh0 : 0 < (pr.1.2 - pr.2.2) / sideDeg pr :=
    Nat.div_pos (Nat.le_of_dvd hdrop hgd) hg
  have he0 : 0 < (pr.2.1 - pr.1.1) / sideDeg pr :=
    Nat.div_pos (Nat.le_of_dvd hrun hge) hg
  have hcop : Nat.Coprime ((pr.1.2 - pr.2.2) / sideDeg pr) ((pr.2.1 - pr.1.1) / sideDeg pr) :=
    Nat.coprime_div_gcd_div_gcd hg
  set h0 := (pr.1.2 - pr.2.2) / sideDeg pr
  set e0 := (pr.2.1 - pr.1.1) / sideDeg pr
  have hcop' : ((-(h0 : ℤ)).natAbs).Coprime e0 := by simpa using hcop
  set q' : ℚ := ⟨-(h0 : ℤ), e0, by omega, hcop'⟩ with hq'def
  have hq' : q' = ((-(h0 : ℤ) : ℤ) : ℚ) / ((e0 : ℤ) : ℚ) := by
    rw [hq'def, Rat.mk_eq_divInt, Rat.divInt_eq_div]
  have hslope : (mkSide pr).slope = q' := by
    show ((pr.2.2 : ℚ) - (pr.1.2 : ℚ)) / ((pr.2.1 : ℚ) - (pr.1.1 : ℚ)) = q'
    have hnum : (pr.2.2 : ℚ) - (pr.1.2 : ℚ) = -(((pr.1.2 - pr.2.2 : ℕ)) : ℚ) := by
      rw [Nat.cast_sub hh.le]; ring
    have hden : (pr.2.1 : ℚ) - (pr.1.1 : ℚ) = ((pr.2.1 - pr.1.1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub hw.le]
    have hgQ : ((sideDeg pr : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast hg.ne'
    rw [hnum, hden, ← hgh, ← hge', hq']
    push_cast
    rw [neg_div, neg_div]
    congr 1
    rw [mul_div_mul_left _ _ hgQ]
  have he : (mkSide pr).e = e0 := by
    show (mkSide pr).slope.den = e0
    rw [hslope]
  have hhZ : (mkSide pr).h = -(h0 : ℤ) := by
    show (mkSide pr).slope.num = -(h0 : ℤ)
    rw [hslope]
  refine ⟨he, hhZ, ?_, hge', hgh, he0, hh0⟩
  show (mkSide pr).length / (mkSide pr).e = sideDeg pr
  have hlen : (mkSide pr).length = pr.2.1 - pr.1.1 := rfl
  rw [hlen, he, ← hge', Nat.mul_div_cancel _ he0]

/-- Endpoint residual coefficients are UNITS (vertex exactness + `≤ N−1` heights ⟹ readable
nonzero coefficients ⟹ nonzero unit residues). This is the vertex-exactness engine behind
LEM B.1. -/
theorem residual_endpoint_units {N s : ℕ} (hN : 0 < N) {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    (hexact : ∀ q ∈ P, vOf p f q.1 = q.2) {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpr : pr ∈ sidePairs P) :
    B.boxCoeffData p N (mkSide pr) f 0 ≠ 0 ∧
    B.boxCoeffData p N (mkSide pr) f (M4.residualDeg (mkSide pr)) ≠ 0 := by
  obtain ⟨hw, hh, hm1, hm2⟩ := menuPath_side_facts hP pr hpr
  obtain ⟨he, hhZ, hd, hge, hgh, he0, hh0⟩ := side_data hw hh
  have hb1 : pr.1.2 ≤ N - 1 := menuPath_height_le hP pr.1 hm1
  have hb2 : pr.2.2 ≤ N - 1 := menuPath_height_le hP pr.2 hm2
  have hunit : ∀ i v : ℕ, vOf p f i = v → v < N →
      (f.1).coeff i ≠ 0 ∧ PadicLift.zmodUnitResidue p N ((f.1).coeff i) ≠ 0 := by
    intro i v hv hvN
    have hne : (f.1).coeff i ≠ 0 := by
      intro h0
      rw [vOf, h0, PadicLift.zmodValuation_zero] at hv
      omega
    exact ⟨hne, PadicLift.zmodUnitResidue_ne_zero p hne⟩
  constructor
  · -- t = 0: left vertex
    have hidx : (mkSide pr).i₀ + 0 * (mkSide pr).e = pr.1.1 := by simp [mkSide]
    have hval : vOf p f pr.1.1 = pr.1.2 := hexact pr.1 hm1
    have hguard : (PadicLift.zmodValuation p N
          ((f.1).coeff ((mkSide pr).i₀ + 0 * (mkSide pr).e)) : ℤ)
        = ((mkSide pr).v₀ : ℤ) + (0 : ℕ) * (mkSide pr).h := by
      rw [hidx]
      have hv : PadicLift.zmodValuation p N ((f.1).coeff pr.1.1) = pr.1.2 := hval
      rw [hv]
      show (pr.1.2 : ℤ) = (pr.1.2 : ℤ) + (0 : ℕ) * (mkSide pr).h
      simp
    unfold B.boxCoeffData
    rw [if_pos hguard, hidx]
    exact (hunit pr.1.1 pr.1.2 hval (by omega)).2
  · -- t = residualDeg: right vertex
    have hidx : (mkSide pr).i₀ + (M4.residualDeg (mkSide pr)) * (mkSide pr).e = pr.2.1 := by
      rw [hd, he]
      show pr.1.1 + sideDeg pr * ((pr.2.1 - pr.1.1) / sideDeg pr) = pr.2.1
      omega
    have hval : vOf p f pr.2.1 = pr.2.2 := hexact pr.2 hm2
    have hguard : (PadicLift.zmodValuation p N
          ((f.1).coeff ((mkSide pr).i₀ + (M4.residualDeg (mkSide pr)) * (mkSide pr).e)) : ℤ)
        = ((mkSide pr).v₀ : ℤ) + ((M4.residualDeg (mkSide pr)) : ℕ) * (mkSide pr).h := by
      rw [hidx]
      have hv : PadicLift.zmodValuation p N ((f.1).coeff pr.2.1) = pr.2.2 := hval
      rw [hv, hd, hhZ]
      show (pr.2.2 : ℤ) = ((mkSide pr).v₀ : ℤ)
          + (sideDeg pr : ℕ) * (-(((pr.1.2 - pr.2.2) / sideDeg pr : ℕ) : ℤ))
      have hZ : (sideDeg pr : ℤ) * (((pr.1.2 - pr.2.2) / sideDeg pr : ℕ) : ℤ)
          = ((pr.1.2 - pr.2.2 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℤ)) hgh
      have hv₀ : ((mkSide pr).v₀ : ℤ) = (pr.1.2 : ℤ) := rfl
      rw [hv₀]
      rw [Nat.cast_sub hh.le] at hZ
      push_cast
      push_cast at hZ
      linarith [hZ]
    unfold B.boxCoeffData
    rw [if_pos hguard, hidx]
    exact (hunit pr.2.1 pr.2.2 hval (by omega)).2

/-- The residual polynomial of a matched side is nonzero of degree exactly `sideDeg` (`d_S`). -/
theorem residual_facts {N s : ℕ} (hN : 0 < N) {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    (hexact : ∀ q ∈ P, vOf p f q.1 = q.2) {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpr : pr ∈ sidePairs P) :
    residualOf p f pr ≠ 0 ∧ (residualOf p f pr).natDegree = sideDeg pr := by
  obtain ⟨hw, hh, _, _⟩ := menuPath_side_facts hP pr hpr
  obtain ⟨_, _, hd, _, _, _, _⟩ := side_data hw hh
  obtain ⟨_, hdne⟩ := residual_endpoint_units p hN hP hexact hpr
  have hcoeff : (residualOf p f pr).coeff (M4.residualDeg (mkSide pr))
      = B.boxCoeffData p N (mkSide pr) f (M4.residualDeg (mkSide pr)) := by
    rw [residualOf, M4.residualPoly_coeff, if_pos (le_refl _)]
  have hne : residualOf p f pr ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact hdne hcoeff.symm
  have hle : (residualOf p f pr).natDegree ≤ M4.residualDeg (mkSide pr) :=
    M4.residualPoly_natDegree_le _ _
  have hge : M4.residualDeg (mkSide pr) ≤ (residualOf p f pr).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (hcoeff ▸ hdne)
  exact ⟨hne, by omega⟩

/-! ### `polyShape` validity: the shape of a nonzero polynomial is a partition of its degree -/

/-- The canonically sorted shape list of a polynomial. -/
noncomputable def sortedShape (R : (ZMod p)[X]) : List (ℕ × ℕ) :=
  (polyShape p R).sort shapeLE

theorem polyShape_pos {R : (ZMod p)[X]} (_hR : R ≠ 0) :
    ∀ q ∈ polyShape p R, 1 ≤ q.1 ∧ 1 ≤ q.2 := by
  letI := Classical.decEq ((ZMod p)[X])
  intro q hq
  unfold polyShape at hq
  rw [Multiset.mem_map] at hq
  obtain ⟨ψ, hψ, rfl⟩ := hq
  rw [Finset.mem_val, Multiset.mem_toFinset] at hψ
  constructor
  · exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψ).natDegree_pos
  · exact Multiset.count_pos.mpr hψ

theorem polyShape_sum {R : (ZMod p)[X]} (hR : R ≠ 0) :
    ((polyShape p R).map fun q => q.1 * q.2).sum = R.natDegree := by
  letI := Classical.decEq ((ZMod p)[X])
  have h0 : (0 : (ZMod p)[X]) ∉ UniqueFactorizationMonoid.normalizedFactors R := by
    intro h0
    exact not_irreducible_zero (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ h0)
  have h3 : (Multiset.map Polynomial.natDegree
      (UniqueFactorizationMonoid.normalizedFactors R)).sum = R.natDegree := by
    have h4 := Polynomial.natDegree_multiset_prod
      (t := UniqueFactorizationMonoid.normalizedFactors R) h0
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hR
    have hprodne : (UniqueFactorizationMonoid.normalizedFactors R).prod ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hu
      exact hR hu.symm
    have hRdeg : R.natDegree
        = (UniqueFactorizationMonoid.normalizedFactors R).prod.natDegree := by
      conv_lhs => rw [← hu]
      rw [Polynomial.natDegree_mul hprodne (Units.ne_zero u),
        Polynomial.natDegree_coe_units u, Nat.add_zero]
    rw [hRdeg]
    exact h4.symm
  have h2 := Finset.sum_multiset_map_count
    (UniqueFactorizationMonoid.normalizedFactors R) (fun ψ => ψ.natDegree)
  unfold polyShape
  rw [Multiset.map_map]
  have hsum : (Multiset.map ((fun q : ℕ × ℕ => q.1 * q.2) ∘ fun ψ =>
      (ψ.natDegree, (UniqueFactorizationMonoid.normalizedFactors R).count ψ))
      (UniqueFactorizationMonoid.normalizedFactors R).toFinset.val).sum
      = ∑ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors R).toFinset,
          ψ.natDegree * (UniqueFactorizationMonoid.normalizedFactors R).count ψ := rfl
  rw [hsum, ← h3, h2]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [smul_eq_mul, Nat.mul_comm]

/-- The sorted shape of a nonzero polynomial is a menu shape of its degree. -/
theorem sortedShape_mem_shapesOfDegree {R : (ZMod p)[X]} (hR : R ≠ 0) :
    sortedShape p R ∈ shapesOfDegree R.natDegree := by
  rw [mem_shapesOfDegree_iff]
  refine ⟨?_, ?_, ?_⟩
  · unfold sortedShape
    exact Multiset.pairwise_sort _ _
  · intro q hq
    unfold sortedShape at hq
    rw [Multiset.mem_sort] at hq
    exact polyShape_pos p hR q hq
  · have hcoe : ((sortedShape p R : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) = polyShape p R :=
      Multiset.sort_eq _ _
    have hlist : ((sortedShape p R).map fun q => q.1 * q.2).sum
        = (((polyShape p R).map fun q => q.1 * q.2)).sum := by
      rw [← hcoe, Multiset.map_coe, Multiset.sum_coe]
    rw [hlist]
    exact polyShape_sum p hR

/-- **The per-side shape witness** (existence input): the sorted shape of a matched side's
residual is a valid menu shape for that side. -/
theorem matched_side_shape {N s : ℕ} (hN : 0 < N) {f : QuotientBox.monicBox p N s}
    {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    (hexact : ∀ q ∈ P, vOf p f q.1 = q.2) {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpr : pr ∈ sidePairs P) :
    sortedShape p (residualOf p f pr) ∈ shapesOfDegree (sideDeg pr) := by
  obtain ⟨hne, hdeg⟩ := residual_facts p hN hP hexact hpr
  have hmem := sortedShape_mem_shapesOfDegree p hne
  rwa [hdeg] at hmem

/-! ## 8. The hull construction (deliverable 5: `cell_exists`, F1-gated)

Given left-endpoint readability `v_p(a₀) < N` (F1) and the x-power-cluster hypothesis
(`v_p(aᵢ) ≥ 1` for `i < s`), the lower hull of the (capped) valuation vector is built greedily:
from the current vertex take the FARTHEST minimal-slope point (largest argmin — this yields
maximal sides, F4). All hull heights are `≤ v_p(a₀) ≤ N−1`, so every read is certified: the
capped valuation vector agrees with the true one wherever it matters (W0's sharp law). -/

/-- The slope key from `j0` to `j` of the valuation vector `w`. -/
noncomputable def key (w : ℕ → ℕ) (j0 j : ℕ) : ℚ :=
  ((w j : ℚ) - (w j0 : ℚ)) / ((j : ℚ) - (j0 : ℚ))

theorem slopeQ_key (w : ℕ → ℕ) (j0 j : ℕ) :
    slopeQ ((j0, w j0), (j, w j)) = key w j0 j := rfl

/-- Largest argmin of `key w j0` over `[j0+1, j0+m]`, by upward replace-on-tie scan. -/
noncomputable def bestIdx (w : ℕ → ℕ) (j0 : ℕ) : ℕ → ℕ
  | 0 => j0 + 1
  | m + 1 =>
      if key w j0 (j0 + m + 1) ≤ key w j0 (bestIdx w j0 m) then j0 + m + 1
      else bestIdx w j0 m

theorem bestIdx_spec (w : ℕ → ℕ) (j0 : ℕ) :
    ∀ m : ℕ, 1 ≤ m →
      (j0 + 1 ≤ bestIdx w j0 m ∧ bestIdx w j0 m ≤ j0 + m) ∧
      (∀ j, j0 + 1 ≤ j → j ≤ j0 + m → key w j0 (bestIdx w j0 m) ≤ key w j0 j) ∧
      (∀ j, bestIdx w j0 m < j → j ≤ j0 + m → key w j0 (bestIdx w j0 m) < key w j0 j) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro _
      have hunfold : bestIdx w j0 (m + 1)
          = if key w j0 (j0 + m + 1) ≤ key w j0 (bestIdx w j0 m) then j0 + m + 1
            else bestIdx w j0 m := rfl
      by_cases hm : m = 0
      · subst hm
        have hbase : bestIdx w j0 0 = j0 + 1 := rfl
        rw [hunfold, hbase, if_pos (le_refl _)]
        refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
        · intro j hj1 hj2
          have hj : j = j0 + 1 := by omega
          rw [hj]
        · intro j hj1 hj2
          omega
      · have hm1 : 1 ≤ m := by omega
        obtain ⟨⟨hb1, hb2⟩, hmin, hstrict⟩ := ih hm1
        rw [hunfold]
        by_cases hc : key w j0 (j0 + m + 1) ≤ key w j0 (bestIdx w j0 m)
        · rw [if_pos hc]
          refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
          · intro j hj1 hj2
            rcases Nat.eq_or_lt_of_le hj2 with heq | hlt
            · rw [heq]; exact le_refl _
            · exact le_trans hc (hmin j hj1 (by omega))
          · intro j hj1 hj2
            omega
        · rw [if_neg hc]
          rw [not_le] at hc
          refine ⟨⟨hb1, by omega⟩, ?_, ?_⟩
          · intro j hj1 hj2
            rcases Nat.eq_or_lt_of_le hj2 with heq | hlt
            · rw [heq]; exact hc.le
            · exact hmin j hj1 (by omega)
          · intro j hj1 hj2
            rcases Nat.eq_or_lt_of_le hj2 with heq | hlt
            · rw [heq]; exact hc
            · exact hstrict j hj1 (by omega)

/-- The next hull vertex abscissa after `j0`. -/
noncomputable def nextIdx (w : ℕ → ℕ) (s j0 : ℕ) : ℕ := bestIdx w j0 (s - j0)

/-- **The greedy step**: the chosen next vertex gives a genuine maximal hull side —
strictly-descending, above-side on the window, and strictly-steeper continuation slopes. -/
theorem nextIdx_spec {s : ℕ} (w : ℕ → ℕ) (j0 : ℕ) (hj0 : j0 < s) (hws : w s = 0)
    (hpos : 1 ≤ w j0) :
    (j0 < nextIdx w s j0 ∧ nextIdx w s j0 ≤ s) ∧
    w (nextIdx w s j0) < w j0 ∧
    (∀ i, j0 ≤ i → i ≤ nextIdx w s j0 →
      lineAt ((j0, w j0), (nextIdx w s j0, w (nextIdx w s j0))) (i : ℚ) ≤ (w i : ℚ)) ∧
    (∀ j2, nextIdx w s j0 < j2 → j2 ≤ s →
      slopeQ ((j0, w j0), (nextIdx w s j0, w (nextIdx w s j0)))
        < slopeQ ((nextIdx w s j0, w (nextIdx w s j0)), (j2, w j2))) := by
  have hm : 1 ≤ s - j0 := by omega
  obtain ⟨⟨hb1, hb2⟩, hmin, hstrict⟩ := bestIdx_spec w j0 (s - j0) hm
  have hbdd : j0 + (s - j0) = s := by omega
  have hbi : bestIdx w j0 (s - j0) = nextIdx w s j0 := rfl
  rw [hbdd, hbi] at hb2 hmin hstrict
  rw [hbi] at hb1
  have hj1lt : j0 < nextIdx w s j0 := by omega
  have hden1 : (0 : ℚ) < (nextIdx w s j0 : ℚ) - j0 := by
    have : (j0 : ℚ) < nextIdx w s j0 := by exact_mod_cast hj1lt
    linarith
  have hminN : ∀ j, j0 + 1 ≤ j → j ≤ s → key w j0 (nextIdx w s j0) ≤ key w j0 j := hmin
  have hstrictN : ∀ j, nextIdx w s j0 < j → j ≤ s →
      key w j0 (nextIdx w s j0) < key w j0 j := hstrict
  have hkeyneg : key w j0 (nextIdx w s j0) < 0 := by
    have hks : key w j0 (nextIdx w s j0) ≤ key w j0 s := hminN s (by omega) (le_refl s)
    have hsneg : key w j0 s < 0 := by
      have h1 : (1 : ℚ) ≤ (w j0 : ℚ) := by exact_mod_cast hpos
      have h2 : (j0 : ℚ) < s := by exact_mod_cast hj0
      unfold key
      rw [hws]
      apply div_neg_of_neg_of_pos
      · push_cast
        linarith
      · linarith
    linarith
  have hdrop : w (nextIdx w s j0) < w j0 := by
    by_contra hle
    rw [not_lt] at hle
    have hnum : (0 : ℚ) ≤ (w (nextIdx w s j0) : ℚ) - w j0 := by
      have : (w j0 : ℚ) ≤ w (nextIdx w s j0) := by exact_mod_cast hle
      linarith
    have : 0 ≤ key w j0 (nextIdx w s j0) := div_nonneg hnum hden1.le
    linarith
  refine ⟨⟨hj1lt, hb2⟩, hdrop, ?_, ?_⟩
  · intro i hi0 hi1
    rcases Nat.eq_or_lt_of_le hi0 with heq | hlt
    · rw [← heq]
      have hll : lineAt ((j0, w j0), (nextIdx w s j0, w (nextIdx w s j0))) ((j0 : ℕ) : ℚ)
          = w j0 := lineAt_left _
      rw [hll]
    · have hki : key w j0 (nextIdx w s j0) ≤ key w j0 i := hminN i (by omega) (by omega)
      have hdeni : (0 : ℚ) < (i : ℚ) - j0 := by
        have : (j0 : ℚ) < i := by exact_mod_cast hlt
        linarith
      have hcancel : key w j0 i * ((i : ℚ) - j0) = (w i : ℚ) - w j0 := by
        unfold key
        exact div_mul_cancel₀ _ hdeni.ne'
      have hlin : lineAt ((j0, w j0), (nextIdx w s j0, w (nextIdx w s j0))) (i : ℚ)
          = (w j0 : ℚ) + key w j0 (nextIdx w s j0) * ((i : ℚ) - j0) := by
        unfold lineAt
        rw [slopeQ_key]
      rw [hlin]
      linarith [mul_le_mul_of_nonneg_right hki hdeni.le, hcancel]
  · intro j2 h21 h2s
    by_contra hle
    rw [not_lt] at hle
    have hle' : slopeQ ((nextIdx w s j0, w (nextIdx w s j0)), (j2, w j2))
        ≤ key w j0 (nextIdx w s j0) := hle
    have hden2 : (0 : ℚ) < (j2 : ℚ) - nextIdx w s j0 := by
      have : (nextIdx w s j0 : ℚ) < j2 := by exact_mod_cast h21
      linarith
    have hden20 : (0 : ℚ) < (j2 : ℚ) - j0 := by
      have : (j0 : ℚ) < j2 := by exact_mod_cast (by omega : j0 < j2)
      linarith
    have hc1 : key w j0 (nextIdx w s j0) * ((nextIdx w s j0 : ℚ) - j0)
        = (w (nextIdx w s j0) : ℚ) - w j0 := by
      unfold key
      exact div_mul_cancel₀ _ hden1.ne'
    have hc2 : key w j0 j2 * ((j2 : ℚ) - j0) = (w j2 : ℚ) - w j0 := by
      unfold key
      exact div_mul_cancel₀ _ hden20.ne'
    have hc12 : slopeQ ((nextIdx w s j0, w (nextIdx w s j0)), (j2, w j2)) * ((j2 : ℚ) - nextIdx w s j0)
        = (w j2 : ℚ) - w (nextIdx w s j0) := by
      show ((w j2 : ℚ) - w (nextIdx w s j0)) / ((j2 : ℚ) - nextIdx w s j0)
          * ((j2 : ℚ) - nextIdx w s j0) = (w j2 : ℚ) - w (nextIdx w s j0)
      exact div_mul_cancel₀ _ hden2.ne'
    have hkey12 : key w j0 (nextIdx w s j0) < key w j0 j2 := hstrictN j2 h21 h2s
    have hsplit : key w j0 (nextIdx w s j0) * ((j2 : ℚ) - j0)
        = key w j0 (nextIdx w s j0) * ((nextIdx w s j0 : ℚ) - j0)
          + key w j0 (nextIdx w s j0) * ((j2 : ℚ) - nextIdx w s j0) := by ring
    linarith [mul_le_mul_of_nonneg_right hle' hden2.le,
      mul_lt_mul_of_pos_right hkey12 hden20, hc1, hc2, hc12, hsplit]

/-- The greedy hull tail from `j0` (fuel-based). -/
noncomputable def buildTail (w : ℕ → ℕ) (s : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | fuel + 1, j0 =>
      if j0 < s then
        (nextIdx w s j0, w (nextIdx w s j0)) :: buildTail w s fuel (nextIdx w s j0)
      else []

/-- **The hull-tail invariant**: the built tail is a genuine maximal chain, its vertices read
`w` exactly, and every built side dominates the valuation vector on its window. -/
theorem buildTail_ok {N s : ℕ} (w : ℕ → ℕ) (hcl : ∀ i, i < s → 1 ≤ w i)
    (hws : w s = 0) :
    ∀ (fuel j0 : ℕ) (prev : ℕ × ℕ), j0 ≤ s → s ≤ j0 + fuel → w j0 < N → prev.1 < j0 →
      (∀ j2, j0 < j2 → j2 ≤ s → slopeQ (prev, (j0, w j0)) < slopeQ ((j0, w j0), (j2, w j2))) →
      ChainOK s prev (j0, w j0) (buildTail w s fuel j0) ∧
      (∀ q ∈ buildTail w s fuel j0, q.2 = w q.1) ∧
      (∀ pr ∈ sidePairs ((j0, w j0) :: buildTail w s fuel j0),
        ∀ i : ℕ, pr.1.1 ≤ i → i ≤ pr.2.1 → lineAt pr (i : ℚ) ≤ (w i : ℚ)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j0 prev hj0s hfuel _ _ _
      have hj0 : j0 = s := by omega
      subst hj0
      refine ⟨ChainOK.nil rfl hws, ?_, ?_⟩
      · intro q hq; simp [buildTail] at hq
      · intro pr hpr; simp [buildTail, sidePairs] at hpr
  | succ fuel ih =>
      intro j0 prev hj0s hfuel hwN hprev hpslope
      by_cases hj0 : j0 < s
      · have hunfold : buildTail w s (fuel + 1) j0
            = (nextIdx w s j0, w (nextIdx w s j0)) :: buildTail w s fuel (nextIdx w s j0) := by
          simp [buildTail, hj0]
        obtain ⟨⟨ha1, ha2⟩, hb, hc, hd⟩ := nextIdx_spec w j0 hj0 hws (hcl j0 hj0)
        have hnext : w (nextIdx w s j0) < N := by omega
        obtain ⟨ihChain, ihEx, ihSides⟩ :=
          ih (nextIdx w s j0) (j0, w j0) ha2 (by omega) hnext (by simpa using ha1) hd
        rw [hunfold]
        refine ⟨?_, ?_, ?_⟩
        · refine ChainOK.cons (by simpa using ha1) (by simpa using hb) ?_ ihChain
          have hsl := hpslope (nextIdx w s j0) ha1 ha2
          exact (slopeLt_iff_slopeQ hprev (by simpa using ha1)).mpr hsl
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · rfl
          · exact ihEx q hq'
        · intro pr hpr
          rw [sidePairs_cons₂, List.mem_cons] at hpr
          rcases hpr with rfl | hpr'
          · exact hc
          · exact ihSides pr hpr'
      · have hj0' : j0 = s := by omega
        have hnil : buildTail w s (fuel + 1) j0 = [] := by simp [buildTail, hj0]
        rw [hnil]
        refine ⟨ChainOK.nil hj0' (by rw [hj0']; exact hws), ?_, ?_⟩
        · intro q hq; simp at hq
        · intro pr hpr; simp [sidePairs] at hpr

/-- `Forall₂` against the image of the same list. -/
theorem forall₂_map_self {α β : Type*} {R : β → α → Prop} (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, R (g a) a) → List.Forall₂ R (l.map g) l := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      simp only [List.map_cons]
      exact List.Forall₂.cons (h a (by simp)) (ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))

/-- The leading coefficient of a box element has valuation `0`. -/
theorem vOf_leading {N s : ℕ} (hN : 0 < N) (f : QuotientBox.monicBox p N s) :
    vOf p f s = 0 := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  have hc : (f.1).coeff s = 1 := by
    have hcn : (f.1).coeff ((f.1).natDegree) = 1 := f.2.1.coeff_natDegree
    rwa [f.2.2] at hcn
  rw [vOf, hc]
  have h1 : (1 : ZMod (p ^ N)) ≠ 0 := one_ne_zero
  rw [PadicLift.zmodValuation_of_ne_zero p h1, ZMod.val_one]
  simp

/-- **`cell_exists`** (deliverable 5, F1-gated): an x-power-cluster box element with READABLE
LEFT ENDPOINT (`v_p(a₀) < N` — NOT the refuted `v_p(disc) < N` gate) matches some menu cell.
All hull reads are certified because every hull height is `≤ v_p(a₀) ≤ N−1` (heights strictly
decrease along the maximal path from the readable left endpoint). -/
theorem cell_exists {N s : ℕ} (hN : 0 < N) (hs : 0 < s) (f : QuotientBox.monicBox p N s)
    (hcluster : ∀ i, i < s → 1 ≤ vOf p f i) (hread : vOf p f 0 < N) :
    ∃ c ∈ cellMenu s N, InCell p f c := by
  set w : ℕ → ℕ := vOf p f with hwdef
  have hws : w s = 0 := vOf_leading p hN f
  obtain ⟨⟨hj1a, hj1b⟩, hlt1, habove0, hslope0⟩ := nextIdx_spec w 0 hs hws (hcluster 0 hs)
  obtain ⟨hchain, hex, hsides⟩ := buildTail_ok (N := N) w hcluster hws s (nextIdx w s 0)
    (0, w 0) hj1b (by omega) (by omega) (by simpa using hj1a) hslope0
  set P : List (ℕ × ℕ) :=
    (0, w 0) :: (nextIdx w s 0, w (nextIdx w s 0)) :: buildTail w s s (nextIdx w s 0) with hPdef
  have hMenu : MenuPath s N P :=
    ⟨w 0, (nextIdx w s 0, w (nextIdx w s 0)), buildTail w s s (nextIdx w s 0), rfl,
      hcluster 0 hs, by omega, hj1a, hlt1, hchain⟩
  have hexact : ∀ q ∈ P, vOf p f q.1 = q.2 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · rfl
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · rfl
      · exact (hex q hq'').symm
  have habove : ∀ pr ∈ sidePairs P, SideAbove p f pr := by
    intro pr hpr
    rw [hPdef, sidePairs_cons₂, List.mem_cons] at hpr
    rcases hpr with rfl | hpr'
    · exact habove0
    · exact hsides pr hpr'
  set sh : List (List (ℕ × ℕ)) :=
    (sidePairs P).map fun pr => sortedShape p (residualOf p f pr) with hshdef
  have hShapes : ShapesFor P sh :=
    forall₂_map_self _ _ fun pr hpr => matched_side_shape p hN hMenu hexact hpr
  have hMatch : Matches p f P sh := by
    refine ⟨hexact, ?_⟩
    refine forall₂_map_self _ _ fun pr hpr => ?_
    exact ⟨habove pr hpr, (Multiset.sort_eq _ _).symm⟩
  exact ⟨mkCell s P sh, mem_cellMenu_iff.mpr ⟨P, sh, hMenu, hShapes, rfl⟩,
    P, sh, hMenu, hShapes, rfl, hMatch⟩

/-! ## 9. The order-1 menu classifier `classify1` (deliverable 6) -/

/-- **The order-1 menu-checking classifier**: the unique matched menu cell, if any
(noncomputable choice; uniqueness is `inCell_unique`). -/
noncomputable def classify1 {N s : ℕ} (f : QuotientBox.monicBox p N s) : Option NodeConfig :=
  letI := Classical.dec (∃ c, InCell p f c)
  if h : ∃ c, InCell p f c then some h.choose else none

theorem classify1_eq_some_iff {N s : ℕ} {f : QuotientBox.monicBox p N s} {c : NodeConfig} :
    classify1 p f = some c ↔ InCell p f c := by
  unfold classify1
  constructor
  · intro h
    split at h
    case isTrue hex =>
        rw [Option.some.injEq] at h
        exact h ▸ hex.choose_spec
    case isFalse hex => exact absurd h (by simp)
  · intro hc
    have hex : ∃ c', InCell p f c' := ⟨c, hc⟩
    split
    case isTrue hex' =>
        rw [Option.some.injEq]
        exact inCell_unique p hex'.choose_spec hc
    case isFalse hex' => exact absurd hex hex'

theorem classify1_eq_none_iff {N s : ℕ} {f : QuotientBox.monicBox p N s} :
    classify1 p f = none ↔ ¬ ∃ c, InCell p f c := by
  unfold classify1
  constructor
  · intro h hex
    rw [dif_pos hex] at h
    exact Option.some_ne_none _ h
  · intro hex
    rw [dif_neg hex]

/-- The classified cell is a menu cell matching `f` (spec projection). -/
theorem classify1_spec {N s : ℕ} {f : QuotientBox.monicBox p N s} {c : NodeConfig}
    (h : classify1 p f = some c) : c ∈ cellMenu s N ∧ InCell p f c :=
  ⟨inCell_mem_cellMenu p ((classify1_eq_some_iff p).mp h), (classify1_eq_some_iff p).mp h⟩

/-- **F1 sharp law, matched half**: readable left endpoint ⟹ `classify1` decides. -/
theorem classify1_isSome {N s : ℕ} (hN : 0 < N) (hs : 0 < s)
    (f : QuotientBox.monicBox p N s)
    (hcluster : ∀ i, i < s → 1 ≤ vOf p f i) (hread : vOf p f 0 < N) :
    (classify1 p f).isSome := by
  obtain ⟨c, _, hc⟩ := cell_exists p hN hs f hcluster hread
  rw [Option.isSome_iff_exists]
  exact ⟨c, (classify1_eq_some_iff p).mpr hc⟩

/-- **F1 sharp law, tail half** (W0: UNMATCHED is exactly `a₀ ≡ 0 mod p^N`): an unreadable
left endpoint matches NO menu cell — the left vertex `(0, H)` demands exact valuation
`H ≤ N−1 < N`, but the capped valuation of `a₀ = 0` is `N`. -/
theorem classify1_eq_none_of_tail {N s : ℕ} (hN : 0 < N) {f : QuotientBox.monicBox p N s}
    (hf : (f.1).coeff 0 = 0) : classify1 p f = none := by
  rw [classify1_eq_none_iff]
  rintro ⟨c, P, sh, hP, _, _, hm⟩
  obtain ⟨H, p1, T, rfl, hH1, hH2, _, _, _⟩ := hP
  have hex : vOf p f 0 = H := hm.1 (0, H) (by simp)
  rw [vOf, hf, PadicLift.zmodValuation_zero] at hex
  omega

/-! ## 10. Numeric-gate helpers: explicit valuation / unit-residue / residual evaluation -/

/-- Valuation of an explicit element by divisibility witnesses (kernel-checkable). -/
theorem zmodValuation_eq_of {N v : ℕ} (x : ZMod (p ^ N)) (hx : x ≠ 0)
    (h1 : p ^ v ∣ x.val) (h2 : ¬ p ^ (v + 1) ∣ x.val) :
    PadicLift.zmodValuation p N x = v := by
  rw [PadicLift.zmodValuation_of_ne_zero p hx]
  have hval : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx
  have hle : v ≤ x.val.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp.out hval).mp h1
  have hlt : ¬ (v + 1 ≤ x.val.factorization p) := fun hc =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization hp.out hval).mpr hc)
  omega

/-- Unit residue of an explicit element by a `p^v · u` decomposition. -/
theorem zmodUnitResidue_eq {N : ℕ} {x : ZMod (p ^ N)} (hx : x ≠ 0) {v u : ℕ}
    (hval : PadicLift.zmodValuation p N x = v) (hdecomp : x.val = p ^ v * u) :
    PadicLift.zmodUnitResidue p N x = ((u : ℕ) : ZMod p) := by
  unfold PadicLift.zmodUnitResidue
  congr 1
  have hfac : x.val.factorization p = v := by
    rw [← PadicLift.zmodValuation_of_ne_zero p hx, hval]
  show x.val / p ^ (x.val.factorization p) = u
  rw [hfac, hdecomp, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos v)]

/-- Evaluate `boxCoeffData` at an on-side position (guard true → unit residue). -/
theorem bcd_eval {N n : ℕ} {S : NewtonPolygon.Side} {f : QuotientBox.monicBox p N n}
    {t j : ℕ} (hj : S.i₀ + t * S.e = j)
    (hguard : (PadicLift.zmodValuation p N ((f.1).coeff j) : ℤ) = (S.v₀ : ℤ) + t * S.h) :
    B.boxCoeffData p N S f t = PadicLift.zmodUnitResidue p N ((f.1).coeff j) := by
  unfold B.boxCoeffData
  rw [hj, if_pos hguard]

/-- Evaluate `boxCoeffData` at an above-side position (guard false → 0, the D7 on-side guard). -/
theorem bcd_zero {N n : ℕ} {S : NewtonPolygon.Side} {f : QuotientBox.monicBox p N n}
    {t j : ℕ} (hj : S.i₀ + t * S.e = j)
    (hguard : ¬ (PadicLift.zmodValuation p N ((f.1).coeff j) : ℤ) = (S.v₀ : ℤ) + t * S.h) :
    B.boxCoeffData p N S f t = 0 := by
  unfold B.boxCoeffData
  rw [hj, if_neg hguard]

/-- The degree-1 residual polynomial, expanded. -/
theorem residual_deg_one {N n : ℕ} (f : QuotientBox.monicBox p N n)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hd : M4.residualDeg (mkSide pr) = 1) :
    residualOf p f pr
      = C (B.boxCoeffData p N (mkSide pr) f 0) + C (B.boxCoeffData p N (mkSide pr) f 1) * X := by
  unfold residualOf M4.residualPoly
  rw [hd, Finset.sum_range_succ, Finset.sum_range_one]
  simp [M4.residualCoeff]

/-- The degree-2 residual polynomial, expanded. -/
theorem residual_deg_two {N n : ℕ} (f : QuotientBox.monicBox p N n)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hd : M4.residualDeg (mkSide pr) = 2) :
    residualOf p f pr
      = C (B.boxCoeffData p N (mkSide pr) f 0) + C (B.boxCoeffData p N (mkSide pr) f 1) * X
        + C (B.boxCoeffData p N (mkSide pr) f 2) * X ^ 2 := by
  unfold residualOf M4.residualPoly
  rw [hd, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [M4.residualCoeff]

/-- Shape of a power of a monic linear factor: `{(1, k)}`. -/
theorem polyShape_pow_linear (a : ZMod p) {k : ℕ} (hk : k ≠ 0) :
    polyShape p ((X + C a) ^ k) = {(1, k)} := by
  letI := Classical.decEq ((ZMod p)[X])
  have hirr : Irreducible (X + C a) := by
    have h := Polynomial.irreducible_X_sub_C (-a)
    simpa [sub_neg_eq_add] using h
  have hmon : (X + C a).Monic := Polynomial.monic_X_add_C a
  have hnf : UniqueFactorizationMonoid.normalizedFactors ((X + C a) ^ k)
      = Multiset.replicate k (X + C a) := by
    rw [hirr.normalizedFactors_pow, hmon.normalize_eq_self]
  unfold polyShape
  rw [hnf, Multiset.toFinset_replicate, if_neg hk]
  simp [Multiset.count_replicate_self]

theorem polyShape_linear (a : ZMod p) : polyShape p (X + C a) = {(1, 1)} := by
  have h := polyShape_pow_linear p a (k := 1) one_ne_zero
  rwa [pow_one] at h

theorem polyShape_X_add_one : polyShape p (X + 1) = {(1, 1)} := by
  have h := polyShape_linear p 1
  rwa [map_one] at h

theorem polyShape_X_add_one_sq : polyShape p ((X + 1) ^ 2) = {(1, 2)} := by
  have h := polyShape_pow_linear p 1 (k := 2) two_ne_zero
  rwa [map_one] at h

/-- Shape of a monic irreducible: `{(deg, 1)}`. -/
theorem polyShape_irreducible_monic {R : (ZMod p)[X]} (hirr : Irreducible R) (hmon : R.Monic) :
    polyShape p R = {(R.natDegree, 1)} := by
  letI := Classical.decEq ((ZMod p)[X])
  have hnf : UniqueFactorizationMonoid.normalizedFactors R = {R} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, hmon.normalize_eq_self]
  unfold polyShape
  rw [hnf]
  simp

/-- **R1 `polyShape_mul` — factorization-shape multiplicativity on COPRIME polynomials.**
For nonzero coprime `R, S` over `ZMod p`, the factorization shape of the product is the multiset
union of the two shapes: `polyShape (R · S) = polyShape R + polyShape S`.  This is the shape-level
analogue of `M4.residualPoly_mul` (the residual-coefficient multiplicativity), supplying condition
(iii) of the product transport at the SHAPE level (blueprint §W4d (d2), R1).

Coprimality is REQUIRED and is the correct hypothesis for the multi-block use (block residuals have
DISTINCT roots, hence coprime): a shared irreducible factor would MERGE its multiplicity in the
product but keep the two multiplicities SEPARATE in the multiset sum — sympy-verified `97/400`
general violations, `0/400` coprime violations
(`/workspace-vast/asving/tmp/phaseb_r1r2/shape_check.py`).

Route: `UniqueFactorizationMonoid.normalizedFactors_mul` (factor multisets add, both nonzero) +
disjoint factor SUPPORTS (coprime ⟹ no common irreducible factor, else a common factor divides both
and is a unit by `IsCoprime.isUnit_of_dvd'`, contradicting irreducibility); on each side's support
the `count` in the sum equals the `count` in that side alone (the other side's count is `0`). -/
theorem polyShape_mul {R S : (ZMod p)[X]} (hR : R ≠ 0) (hS : S ≠ 0) (hcop : IsCoprime R S) :
    polyShape p (R * S) = polyShape p R + polyShape p S := by
  -- use the SAME `DecidableEq` instance `polyShape` bakes in, so all `toFinset`/`count` agree
  letI := Classical.decEq ((ZMod p)[X])
  set nfR := UniqueFactorizationMonoid.normalizedFactors R with hnfR
  set nfS := UniqueFactorizationMonoid.normalizedFactors S with hnfS
  have hmul : UniqueFactorizationMonoid.normalizedFactors (R * S) = nfR + nfS :=
    UniqueFactorizationMonoid.normalizedFactors_mul hR hS
  -- disjointness of the factor SUPPORTS: no irreducible divides a coprime pair
  have hdisj : Disjoint nfR.toFinset nfS.toFinset := by
    rw [Finset.disjoint_left]
    intro ψ hψR hψS
    rw [Multiset.mem_toFinset] at hψR hψS
    have hdR : ψ ∣ R := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hψR
    have hdS : ψ ∣ S := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hψS
    have hunit : IsUnit ψ := hcop.isUnit_of_dvd' hdR hdS
    exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψR).not_isUnit hunit
  have hcountS0 : ∀ ψ ∈ nfR.toFinset.val, nfS.count ψ = 0 := by
    intro ψ hψ
    rw [Multiset.count_eq_zero]
    intro hmem
    rw [Finset.mem_val] at hψ
    exact (Finset.disjoint_left.mp hdisj hψ (Multiset.mem_toFinset.mpr hmem))
  have hcountR0 : ∀ ψ ∈ nfS.toFinset.val, nfR.count ψ = 0 := by
    intro ψ hψ
    rw [Multiset.count_eq_zero]
    intro hmem
    rw [Finset.mem_val] at hψ
    exact (Finset.disjoint_right.mp hdisj hψ (Multiset.mem_toFinset.mpr hmem))
  unfold polyShape
  rw [hmul]
  have hval : (nfR + nfS).toFinset.val = nfR.toFinset.val + nfS.toFinset.val := by
    rw [Multiset.toFinset_add, ← Finset.disjUnion_eq_union nfR.toFinset nfS.toFinset hdisj]
    rfl
  rw [hval, Multiset.map_add]
  congr 1
  · apply Multiset.map_congr rfl
    intro ψ hψ
    have hc : (nfR + nfS).count ψ = nfR.count ψ := by
      rw [Multiset.count_add, hcountS0 ψ hψ, add_zero]
    rw [hc]
  · apply Multiset.map_congr rfl
    intro ψ hψ
    have hc : (nfR + nfS).count ψ = nfS.count ψ := by
      rw [Multiset.count_add, hcountR0 ψ hψ, zero_add]
    rw [hc]

end Box

/-! ## 11. THE LEAN-SIDE NUMERIC GATE (deliverable 7)

Six boxes from the W0 ground-truth tables (`p = 2, N = 3`; `results_s{2,3,4}.tsv`), spanning
`s ∈ {2,3,4}`, incl. a two-sided polygon (S3C3), the self-loop cell (S2C2), an on-side interior
dot (S2C3 = `x²+2x+4`, the E4 witness), and a tail box (`a₀ ≡ 0 mod 8` ⟹ `classify1 = none`):

| box (low→high coeffs)  | W0 row                | verdict here                          |
|-------------------------|----------------------|---------------------------------------|
| `x²+2x+2`  = [2,2]      | bulk → S2C1          | `InCell`, `classify1 = some S2C1`      |
| `x²+4x+4`  = [4,4]      | tail_finite → S2C2   | `InCell`, `classify1 = some S2C2`      |
| `x²+2x+4`  = [4,2]      | bulk → S2C3          | `InCell`, `classify1 = some S2C3`      |
| `x³+2x+4`  = [4,2,0]    | tail_infread → S3C3  | `InCell`, `classify1 = some S3C3`      |
| `x⁴+2`     = [2,0,0,0]  | tail_infread → S4C1  | `InCell`, `classify1 = some S4C1`      |
| `x³+2x`    = [0,2,0]    | UNMATCHED (tail)     | `classify1 = none`                     |
-/

section Gates

/-! ### Shared `p = 2, N = 3` valuation and unit-residue facts -/

theorem gv1 : PadicLift.zmodValuation 2 3 (1 : ZMod (2 ^ 3)) = 0 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem gv2 : PadicLift.zmodValuation 2 3 (2 : ZMod (2 ^ 3)) = 1 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem gv4 : PadicLift.zmodValuation 2 3 (4 : ZMod (2 ^ 3)) = 2 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem gv0 : PadicLift.zmodValuation 2 3 (0 : ZMod (2 ^ 3)) = 3 :=
  PadicLift.zmodValuation_zero 2 3

theorem gu1 : PadicLift.zmodUnitResidue 2 3 (1 : ZMod (2 ^ 3)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (1 : ZMod (2 ^ 3))) (u := 1) (by decide) gv1 (by decide)
  simpa using h

theorem gu2 : PadicLift.zmodUnitResidue 2 3 (2 : ZMod (2 ^ 3)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (2 : ZMod (2 ^ 3))) (u := 1) (by decide) gv2 (by decide)
  simpa using h

theorem gu4 : PadicLift.zmodUnitResidue 2 3 (4 : ZMod (2 ^ 3)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (4 : ZMod (2 ^ 3))) (u := 1) (by decide) gv4 (by decide)
  simpa using h

/-! ### Gate 1 — `x² + 2x + 2` → S2C1 (bulk; path `(0,1)→(2,0)`, shape `{(1,1)}`) -/

noncomputable def gbox1 : QuotientBox.monicBox 2 3 2 :=
  ⟨X ^ 2 + C 2 * X + C 2, ⟨by monicity!, by compute_degree!⟩⟩

theorem gate_S2C1 :
    InCell 2 gbox1 (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]]) ∧
    classify1 2 gbox1 = some (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]]) := by
  have hc0 : (gbox1.1).coeff 0 = 2 := by simp [gbox1]
  have hc1 : (gbox1.1).coeff 1 = 2 := by simp [gbox1]
  have hc2 : (gbox1.1).coeff 2 = 1 := by simp [gbox1]
  have hv0 : vOf 2 gbox1 0 = 1 := by unfold vOf; rw [hc0]; exact gv2
  have hv1 : vOf 2 gbox1 1 = 1 := by unfold vOf; rw [hc1]; exact gv2
  have hv2 : vOf 2 gbox1 2 = 0 := by unfold vOf; rw [hc2]; exact gv1
  have hsd := side_data (pr := ((0, 1), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 1), (2, 0))).e = 2 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 1), (2, 0))).h = -1 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 1), (2, 0))) = 1 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 3 ((gbox1.1).coeff 0) : ℤ)
      = ((mkSide ((0, 1), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 1), (2, 0))).h := by
    rw [hc0, gv2]; simp [mkSide]
  have hg1 : (PadicLift.zmodValuation 2 3 ((gbox1.1).coeff 2) : ℤ)
      = ((mkSide ((0, 1), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 1), (2, 0))).h := by
    rw [hc2, gv1, hH]; simp [mkSide]
  have hb0 : B.boxCoeffData 2 3 (mkSide ((0, 1), (2, 0))) gbox1 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0, gu2]
  have hb1 : B.boxCoeffData 2 3 (mkSide ((0, 1), (2, 0))) gbox1 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 2) (by rw [hE]; decide) hg1, hc2, gu1]
  have hR : residualOf 2 gbox1 ((0, 1), (2, 0)) = X + 1 := by
    rw [residual_deg_one 2 gbox1 _ hD, hb0, hb1, map_one, one_mul]
    ring
  have hmenu : MenuPath 2 3 [(0, 1), (2, 0)] :=
    ⟨1, (2, 0), [], rfl, le_refl 1, by norm_num, by norm_num, by norm_num,
      ChainOK.nil rfl rfl⟩
  have hexact : ∀ q ∈ ([(0, 1), (2, 0)] : List (ℕ × ℕ)), vOf 2 gbox1 q.1 = q.2 := by
    intro q hq; fin_cases hq <;> assumption
  have habove : SideAbove 2 gbox1 ((0, 1), (2, 0)) := by
    intro i hi0 hi2
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
  have hshapes : ShapesFor [(0, 1), (2, 0)] [[(1, 1)]] :=
    List.Forall₂.cons (by decide) List.Forall₂.nil
  have hmatch : Matches 2 gbox1 [(0, 1), (2, 0)] [[(1, 1)]] :=
    ⟨hexact, List.Forall₂.cons ⟨habove, by rw [hR, polyShape_X_add_one 2]; simp⟩ List.Forall₂.nil⟩
  have hin : InCell 2 gbox1 (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]]) :=
    ⟨_, _, hmenu, hshapes, rfl, hmatch⟩
  exact ⟨hin, (classify1_eq_some_iff 2).mpr hin⟩

/-! ### Gate 2 — `x² + 4x + 4 = (x+2)²` → S2C2 (the SELF-LOOP cell: path `(0,2)→(2,0)`,
shape `{(1,2)}`; A2: `μ·D = 2 = s`, so NO child — `cellChildren` emits `[]`). -/

noncomputable def gbox2 : QuotientBox.monicBox 2 3 2 :=
  ⟨X ^ 2 + C 4 * X + C 4, ⟨by monicity!, by compute_degree!⟩⟩

theorem gate_S2C2 :
    InCell 2 gbox2 (mkCell 2 [(0, 2), (2, 0)] [[(1, 2)]]) ∧
    classify1 2 gbox2 = some (mkCell 2 [(0, 2), (2, 0)] [[(1, 2)]]) := by
  have hc0 : (gbox2.1).coeff 0 = 4 := by simp [gbox2]
  have hc1 : (gbox2.1).coeff 1 = 4 := by simp [gbox2]
  have hc2 : (gbox2.1).coeff 2 = 1 := by simp [gbox2]
  have hv0 : vOf 2 gbox2 0 = 2 := by unfold vOf; rw [hc0]; exact gv4
  have hv1 : vOf 2 gbox2 1 = 2 := by unfold vOf; rw [hc1]; exact gv4
  have hv2 : vOf 2 gbox2 2 = 0 := by unfold vOf; rw [hc2]; exact gv1
  have hsd := side_data (pr := ((0, 2), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 2), (2, 0))).e = 1 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 2), (2, 0))).h = -1 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 2), (2, 0))) = 2 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 3 ((gbox2.1).coeff 0) : ℤ)
      = ((mkSide ((0, 2), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 2), (2, 0))).h := by
    rw [hc0, gv4]; simp [mkSide]
  have hg1 : ¬ (PadicLift.zmodValuation 2 3 ((gbox2.1).coeff 1) : ℤ)
      = ((mkSide ((0, 2), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 2), (2, 0))).h := by
    rw [hc1, gv4, hH]; decide
  have hg2 : (PadicLift.zmodValuation 2 3 ((gbox2.1).coeff 2) : ℤ)
      = ((mkSide ((0, 2), (2, 0))).v₀ : ℤ) + (2 : ℕ) * (mkSide ((0, 2), (2, 0))).h := by
    rw [hc2, gv1, hH]; decide
  have hb0 : B.boxCoeffData 2 3 (mkSide ((0, 2), (2, 0))) gbox2 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0, gu4]
  have hb1 : B.boxCoeffData 2 3 (mkSide ((0, 2), (2, 0))) gbox2 1 = 0 :=
    bcd_zero 2 (t := 1) (j := 1) (by rw [hE]; decide) hg1
  have hb2 : B.boxCoeffData 2 3 (mkSide ((0, 2), (2, 0))) gbox2 2 = 1 := by
    rw [bcd_eval 2 (t := 2) (j := 2) (by rw [hE]; decide) hg2, hc2, gu1]
  have hR : residualOf 2 gbox2 ((0, 2), (2, 0)) = (X + 1) ^ 2 := by
    rw [residual_deg_two 2 gbox2 _ hD, hb0, hb1, hb2, map_one, map_zero, one_mul, zero_mul]
    have h2 : (2 : (ZMod 2)[X]) = 0 := by
      have hcast : (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (map_ofNat C 2).symm
      rw [hcast, show (2 : ZMod 2) = 0 by decide, map_zero]
    linear_combination (-(X : (ZMod 2)[X])) * h2
  have hmenu : MenuPath 2 3 [(0, 2), (2, 0)] :=
    ⟨2, (2, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      ChainOK.nil rfl rfl⟩
  have hexact : ∀ q ∈ ([(0, 2), (2, 0)] : List (ℕ × ℕ)), vOf 2 gbox2 q.1 = q.2 := by
    intro q hq; fin_cases hq <;> assumption
  have habove : SideAbove 2 gbox2 ((0, 2), (2, 0)) := by
    intro i hi0 hi2
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
  have hshapes : ShapesFor [(0, 2), (2, 0)] [[(1, 2)]] :=
    List.Forall₂.cons (by decide) List.Forall₂.nil
  have hmatch : Matches 2 gbox2 [(0, 2), (2, 0)] [[(1, 2)]] :=
    ⟨hexact, List.Forall₂.cons ⟨habove, by rw [hR, polyShape_X_add_one_sq 2]; simp⟩ List.Forall₂.nil⟩
  have hin : InCell 2 gbox2 (mkCell 2 [(0, 2), (2, 0)] [[(1, 2)]]) :=
    ⟨_, _, hmenu, hshapes, rfl, hmatch⟩
  exact ⟨hin, (classify1_eq_some_iff 2).mpr hin⟩

/-- The S2C2 cell is a genuine SELF-LOOP cell: `μ·D = 2·1 = s = 2`, so A2 emits NO children. -/
theorem gate_S2C2_selfLoop : (mkCell 2 [(0, 2), (2, 0)] [[(1, 2)]]).children = [] := by
  show cellChildren 2 [[(1, 2)]] = []
  decide

/-! ### Gate 3 — `x² + 2x + 4` → S2C3 (bulk; the E4 on-side-interior-dot witness: matches ONLY
the maximal slope-−1 side with residual `y² + y + 1`, shape `{(2,1)}`). -/

noncomputable def gbox3 : QuotientBox.monicBox 2 3 2 :=
  ⟨X ^ 2 + C 2 * X + C 4, ⟨by monicity!, by compute_degree!⟩⟩

theorem gate_S2C3 :
    InCell 2 gbox3 (mkCell 2 [(0, 2), (2, 0)] [[(2, 1)]]) ∧
    classify1 2 gbox3 = some (mkCell 2 [(0, 2), (2, 0)] [[(2, 1)]]) := by
  have hc0 : (gbox3.1).coeff 0 = 4 := by simp [gbox3]
  have hc1 : (gbox3.1).coeff 1 = 2 := by simp [gbox3]
  have hc2 : (gbox3.1).coeff 2 = 1 := by simp [gbox3]
  have hv0 : vOf 2 gbox3 0 = 2 := by unfold vOf; rw [hc0]; exact gv4
  have hv1 : vOf 2 gbox3 1 = 1 := by unfold vOf; rw [hc1]; exact gv2
  have hv2 : vOf 2 gbox3 2 = 0 := by unfold vOf; rw [hc2]; exact gv1
  have hsd := side_data (pr := ((0, 2), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 2), (2, 0))).e = 1 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 2), (2, 0))).h = -1 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 2), (2, 0))) = 2 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 3 ((gbox3.1).coeff 0) : ℤ)
      = ((mkSide ((0, 2), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 2), (2, 0))).h := by
    rw [hc0, gv4]; simp [mkSide]
  have hg1 : (PadicLift.zmodValuation 2 3 ((gbox3.1).coeff 1) : ℤ)
      = ((mkSide ((0, 2), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 2), (2, 0))).h := by
    rw [hc1, gv2, hH]; decide
  have hg2 : (PadicLift.zmodValuation 2 3 ((gbox3.1).coeff 2) : ℤ)
      = ((mkSide ((0, 2), (2, 0))).v₀ : ℤ) + (2 : ℕ) * (mkSide ((0, 2), (2, 0))).h := by
    rw [hc2, gv1, hH]; decide
  have hb0 : B.boxCoeffData 2 3 (mkSide ((0, 2), (2, 0))) gbox3 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0, gu4]
  have hb1 : B.boxCoeffData 2 3 (mkSide ((0, 2), (2, 0))) gbox3 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 1) (by rw [hE]; decide) hg1, hc1, gu2]
  have hb2 : B.boxCoeffData 2 3 (mkSide ((0, 2), (2, 0))) gbox3 2 = 1 := by
    rw [bcd_eval 2 (t := 2) (j := 2) (by rw [hE]; decide) hg2, hc2, gu1]
  have hR : residualOf 2 gbox3 ((0, 2), (2, 0)) = X ^ 2 + X + 1 := by
    rw [residual_deg_two 2 gbox3 _ hD, hb0, hb1, hb2, map_one, one_mul, one_mul]
    ring
  have hRdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Finset.mem_Icc, hRdeg]
      omega
    · intro x
      fin_cases x <;> simp [Polynomial.IsRoot] <;> decide
  have hmenu : MenuPath 2 3 [(0, 2), (2, 0)] :=
    ⟨2, (2, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      ChainOK.nil rfl rfl⟩
  have hexact : ∀ q ∈ ([(0, 2), (2, 0)] : List (ℕ × ℕ)), vOf 2 gbox3 q.1 = q.2 := by
    intro q hq; fin_cases hq <;> assumption
  have habove : SideAbove 2 gbox3 ((0, 2), (2, 0)) := by
    intro i hi0 hi2
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
  have hshapes : ShapesFor [(0, 2), (2, 0)] [[(2, 1)]] :=
    List.Forall₂.cons (by decide) List.Forall₂.nil
  have hmatch : Matches 2 gbox3 [(0, 2), (2, 0)] [[(2, 1)]] :=
    ⟨hexact, List.Forall₂.cons
      ⟨habove, by rw [hR, polyShape_irreducible_monic 2 hirr (by monicity!), hRdeg]; simp⟩
      List.Forall₂.nil⟩
  have hin : InCell 2 gbox3 (mkCell 2 [(0, 2), (2, 0)] [[(2, 1)]]) :=
    ⟨_, _, hmenu, hshapes, rfl, hmatch⟩
  exact ⟨hin, (classify1_eq_some_iff 2).mpr hin⟩

/-! ### Gate 4 — `x³ + 2x + 4` → S3C3 (the TWO-SIDED polygon `(0,2)→(1,1)→(3,0)`,
shapes `{(1,1)}` and `{(1,1)}`). -/

noncomputable def gbox4 : QuotientBox.monicBox 2 3 3 :=
  ⟨X ^ 3 + C 2 * X + C 4, ⟨by monicity!, by compute_degree!⟩⟩

theorem gate_S3C3 :
    InCell 2 gbox4 (mkCell 3 [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]]) ∧
    classify1 2 gbox4 = some (mkCell 3 [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]]) := by
  have hc0 : (gbox4.1).coeff 0 = 4 := by simp [gbox4]
  have hc1 : (gbox4.1).coeff 1 = 2 := by simp [gbox4]
  have hc2 : (gbox4.1).coeff 2 = 0 := by simp [gbox4]
  have hc3 : (gbox4.1).coeff 3 = 1 := by simp [gbox4]
  have hv0 : vOf 2 gbox4 0 = 2 := by unfold vOf; rw [hc0]; exact gv4
  have hv1 : vOf 2 gbox4 1 = 1 := by unfold vOf; rw [hc1]; exact gv2
  have hv2 : vOf 2 gbox4 2 = 3 := by unfold vOf; rw [hc2]; exact gv0
  have hv3 : vOf 2 gbox4 3 = 0 := by unfold vOf; rw [hc3]; exact gv1
  -- side 1: (0,2) → (1,1), slope −1, e = 1, d = 1
  have hsd1 := side_data (pr := ((0, 2), (1, 1))) (by decide) (by decide)
  have hE1 : (mkSide ((0, 2), (1, 1))).e = 1 := by rw [hsd1.1]; decide
  have hH1 : (mkSide ((0, 2), (1, 1))).h = -1 := by rw [hsd1.2.1]; decide
  have hD1 : M4.residualDeg (mkSide ((0, 2), (1, 1))) = 1 := by rw [hsd1.2.2.1]; decide
  -- side 2: (1,1) → (3,0), slope −1/2, e = 2, d = 1
  have hsd2 := side_data (pr := ((1, 1), (3, 0))) (by decide) (by decide)
  have hE2 : (mkSide ((1, 1), (3, 0))).e = 2 := by rw [hsd2.1]; decide
  have hH2 : (mkSide ((1, 1), (3, 0))).h = -1 := by rw [hsd2.2.1]; decide
  have hD2 : M4.residualDeg (mkSide ((1, 1), (3, 0))) = 1 := by rw [hsd2.2.2.1]; decide
  -- residual on side 1
  have hg10 : (PadicLift.zmodValuation 2 3 ((gbox4.1).coeff 0) : ℤ)
      = ((mkSide ((0, 2), (1, 1))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 2), (1, 1))).h := by
    rw [hc0, gv4]; simp [mkSide]
  have hg11 : (PadicLift.zmodValuation 2 3 ((gbox4.1).coeff 1) : ℤ)
      = ((mkSide ((0, 2), (1, 1))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 2), (1, 1))).h := by
    rw [hc1, gv2, hH1]; decide
  have hb10 : B.boxCoeffData 2 3 (mkSide ((0, 2), (1, 1))) gbox4 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg10, hc0, gu4]
  have hb11 : B.boxCoeffData 2 3 (mkSide ((0, 2), (1, 1))) gbox4 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 1) (by rw [hE1]; decide) hg11, hc1, gu2]
  have hR1 : residualOf 2 gbox4 ((0, 2), (1, 1)) = X + 1 := by
    rw [residual_deg_one 2 gbox4 _ hD1, hb10, hb11, map_one, one_mul]
    ring
  -- residual on side 2
  have hg20 : (PadicLift.zmodValuation 2 3 ((gbox4.1).coeff 1) : ℤ)
      = ((mkSide ((1, 1), (3, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((1, 1), (3, 0))).h := by
    rw [hc1, gv2]; simp [mkSide]
  have hg21 : (PadicLift.zmodValuation 2 3 ((gbox4.1).coeff 3) : ℤ)
      = ((mkSide ((1, 1), (3, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((1, 1), (3, 0))).h := by
    rw [hc3, gv1, hH2]; decide
  have hb20 : B.boxCoeffData 2 3 (mkSide ((1, 1), (3, 0))) gbox4 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 1) (by simp [mkSide]) hg20, hc1, gu2]
  have hb21 : B.boxCoeffData 2 3 (mkSide ((1, 1), (3, 0))) gbox4 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 3) (by rw [hE2]; decide) hg21, hc3, gu1]
  have hR2 : residualOf 2 gbox4 ((1, 1), (3, 0)) = X + 1 := by
    rw [residual_deg_one 2 gbox4 _ hD2, hb20, hb21, map_one, one_mul]
    ring
  have hmenu : MenuPath 3 3 [(0, 2), (1, 1), (3, 0)] :=
    ⟨2, (1, 1), [(3, 0)], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      ChainOK.cons (by norm_num) (by norm_num) (by decide) (ChainOK.nil rfl rfl)⟩
  have hexact : ∀ q ∈ ([(0, 2), (1, 1), (3, 0)] : List (ℕ × ℕ)), vOf 2 gbox4 q.1 = q.2 := by
    intro q hq; fin_cases hq <;> assumption
  have habove1 : SideAbove 2 gbox4 ((0, 2), (1, 1)) := by
    intro i hi0 hi1
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
  have habove2 : SideAbove 2 gbox4 ((1, 1), (3, 0)) := by
    intro i hi1 hi3
    interval_cases i
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
    · rw [hv3]; norm_num [lineAt, slopeQ]
  have hshapes : ShapesFor [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]] :=
    List.Forall₂.cons (by decide) (List.Forall₂.cons (by decide) List.Forall₂.nil)
  have hmatch : Matches 2 gbox4 [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]] :=
    ⟨hexact, List.Forall₂.cons ⟨habove1, by rw [hR1, polyShape_X_add_one 2]; simp⟩
      (List.Forall₂.cons ⟨habove2, by rw [hR2, polyShape_X_add_one 2]; simp⟩ List.Forall₂.nil)⟩
  have hin : InCell 2 gbox4 (mkCell 3 [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]]) :=
    ⟨_, _, hmenu, hshapes, rfl, hmatch⟩
  exact ⟨hin, (classify1_eq_some_iff 2).mpr hin⟩

/-! ### Gate 5 — `x⁴ + 2` → S4C1 (path `(0,1)→(4,0)`, slope `−1/4`, shape `{(1,1)}`). -/

noncomputable def gbox5 : QuotientBox.monicBox 2 3 4 :=
  ⟨X ^ 4 + C 2, ⟨by monicity!, by compute_degree!⟩⟩

theorem gate_S4C1 :
    InCell 2 gbox5 (mkCell 4 [(0, 1), (4, 0)] [[(1, 1)]]) ∧
    classify1 2 gbox5 = some (mkCell 4 [(0, 1), (4, 0)] [[(1, 1)]]) := by
  have hc0 : (gbox5.1).coeff 0 = 2 := by simp [gbox5]
  have hc1 : (gbox5.1).coeff 1 = 0 := by simp [gbox5]
  have hc2 : (gbox5.1).coeff 2 = 0 := by simp [gbox5]
  have hc3 : (gbox5.1).coeff 3 = 0 := by simp [gbox5]
  have hc4 : (gbox5.1).coeff 4 = 1 := by simp [gbox5]
  have hv0 : vOf 2 gbox5 0 = 1 := by unfold vOf; rw [hc0]; exact gv2
  have hv1 : vOf 2 gbox5 1 = 3 := by unfold vOf; rw [hc1]; exact gv0
  have hv2 : vOf 2 gbox5 2 = 3 := by unfold vOf; rw [hc2]; exact gv0
  have hv3 : vOf 2 gbox5 3 = 3 := by unfold vOf; rw [hc3]; exact gv0
  have hv4 : vOf 2 gbox5 4 = 0 := by unfold vOf; rw [hc4]; exact gv1
  have hsd := side_data (pr := ((0, 1), (4, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 1), (4, 0))).e = 4 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 1), (4, 0))).h = -1 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 1), (4, 0))) = 1 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 3 ((gbox5.1).coeff 0) : ℤ)
      = ((mkSide ((0, 1), (4, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 1), (4, 0))).h := by
    rw [hc0, gv2]; simp [mkSide]
  have hg1 : (PadicLift.zmodValuation 2 3 ((gbox5.1).coeff 4) : ℤ)
      = ((mkSide ((0, 1), (4, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 1), (4, 0))).h := by
    rw [hc4, gv1, hH]; decide
  have hb0 : B.boxCoeffData 2 3 (mkSide ((0, 1), (4, 0))) gbox5 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0, gu2]
  have hb1 : B.boxCoeffData 2 3 (mkSide ((0, 1), (4, 0))) gbox5 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 4) (by rw [hE]; decide) hg1, hc4, gu1]
  have hR : residualOf 2 gbox5 ((0, 1), (4, 0)) = X + 1 := by
    rw [residual_deg_one 2 gbox5 _ hD, hb0, hb1, map_one, one_mul]
    ring
  have hmenu : MenuPath 4 3 [(0, 1), (4, 0)] :=
    ⟨1, (4, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      ChainOK.nil rfl rfl⟩
  have hexact : ∀ q ∈ ([(0, 1), (4, 0)] : List (ℕ × ℕ)), vOf 2 gbox5 q.1 = q.2 := by
    intro q hq; fin_cases hq <;> assumption
  have habove : SideAbove 2 gbox5 ((0, 1), (4, 0)) := by
    intro i hi0 hi4
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
    · rw [hv3]; norm_num [lineAt, slopeQ]
    · rw [hv4]; norm_num [lineAt, slopeQ]
  have hshapes : ShapesFor [(0, 1), (4, 0)] [[(1, 1)]] :=
    List.Forall₂.cons (by decide) List.Forall₂.nil
  have hmatch : Matches 2 gbox5 [(0, 1), (4, 0)] [[(1, 1)]] :=
    ⟨hexact, List.Forall₂.cons ⟨habove, by rw [hR, polyShape_X_add_one 2]; simp⟩ List.Forall₂.nil⟩
  have hin : InCell 2 gbox5 (mkCell 4 [(0, 1), (4, 0)] [[(1, 1)]]) :=
    ⟨_, _, hmenu, hshapes, rfl, hmatch⟩
  exact ⟨hin, (classify1_eq_some_iff 2).mpr hin⟩

/-! ### Gate 6 — `x³ + 2x` (tail: `a₀ = 0 ≡ 0 mod 8`) → NO match, `classify1 = none`
(W0 UNMATCHED row; the F1 sharp law's tail half, exactly per `classify1_eq_none_of_tail`). -/

noncomputable def gbox6 : QuotientBox.monicBox 2 3 3 :=
  ⟨X ^ 3 + C 2 * X, ⟨by monicity!, by compute_degree!⟩⟩

theorem gate_tail : classify1 2 gbox6 = none := by
  exact classify1_eq_none_of_tail 2 (by norm_num) (by simp [gbox6])

end Gates

end LeanUrat.OM.CellMenu
