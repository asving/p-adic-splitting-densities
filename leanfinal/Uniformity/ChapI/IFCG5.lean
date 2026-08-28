/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG0
import Uniformity.ChapC.C29
import Uniformity.ChapH.H01

/-!
# Uniformity.ChapI.IFCG5 — [A0G6 2026-08-28] the finite face-schema skeletons (node A0G-NP)

**Uniform-a0 campaign, NODE A0G-NP** (`docs/in-progress/A0_GENERAL_2026-08-28.md` §4.2 — the
campaign's conceptual heart — and the §6 `A0G-NP0` row): inside one size-`m` cluster, the
**finitely many parametric NP/OM schemas** whose parameters live only in explicit natural gaps.
A genre is NOT one literal Newton polygon: slopes have arbitrarily large numerators as roots
become arbitrarily close.  What IS finite is the *skeleton*: face lengths, reduced slope
denominators, and residual degree/multiplicity patterns.  This file defines that skeleton,
proves the §6 gate (`b·d ≤ m`, and NO unbounded datum in the skeleton — formalized as a
`Fintype` instance obtained from a complete finite enumeration), and exposes the binding
surfaces the downstream nodes consume (`A0G-HE`: the dvSide realization interface; `A0G-CH`:
the child-decrease arithmetic; `A0G-GC`: the loop-uniqueness and exhaustion-friendly carrier).

## The skeleton design decisions (BINDING for A0G-GC; recorded per the unit charge)

Where §4.2 leaves the representation open, every choice below is made so that A0G-GC's
exhaustion/disjointness proofs are **by construction**, not by lemma:

* **D1 (redundancy-free face carrier).**  A face schema is a bare pair
  `FaceShape := ℕ × FactorizationType` — the reduced slope **denominator** `b` and the residual
  factorization **pattern** `σ` (multiset of `(D, μ)` = residual-factor degree/multiplicity).
  The residual degree `d` is *derived* (`faceResDeg = σ.degree = Σ D·μ`), never stored, and the
  face length is *derived* (`faceLen = b * d`): no two representations of the same face exist,
  so the future classifying map has literally one possible image per NP face.  The pattern
  constraints are EXACTLY IFCG0's residue-pattern constraints at total `d`
  (`validFace_iff_mem_residuePatternFinset` makes the reuse literal — dedup with `A0G-RP`).
* **D2 (faces are a `List`, ordered by slope).**  A cluster skeleton is a `List FaceShape` —
  the faces of the lower Newton polygon read **left to right**, i.e. in increasing-slope order
  (the slopes `h/b` themselves are `A0G-NP1` parameters; only their denominators survive here).
  A list, not a multiset: the classifier reads the hull deterministically, so the assignment
  input ↦ skeleton is a *function*, and skeletons that differ in face order are disjoint cells
  by construction.  (A multiset would fuse genuinely distinct NP shapes — which face carries
  the smaller slope is a real cell distinction with its own weight region.)
* **D3 (integral faces are first-class; the loop is a distinguished skeleton).**  Denominator
  `b = 1` (integral-slope) faces are ordinary skeleton faces, and the π-rescale loop is the
  *distinguished skeleton* `loopSkeleton m = [(1, {(1, m)})]` — not an unclassified leftover.
  `A0G-GC1`'s exhaustion then needs no integral-slope side case, and `A0G-GC3`'s "sole
  same-mass edge" is the skeleton-level theorem `eq_loopSkeleton_of_entry_snd_eq_mass`
  (any residual entry of multiplicity `m` forces the whole skeleton to BE the loop).
* **D4 (no unbounded datum).**  Slope numerators, vertex heights, and gap variables appear in
  this file only as explicit *arguments* of the binding surfaces (`genreDatumOfChildEntry`'s
  `h`, `RealizesFaceAt`'s `h`) — never as skeleton fields.  The formal gate is the complete
  finite enumeration `clusterSkeletonFinset` + the `Fintype (ClusterSkeleton m)` instance,
  plus the explicit `≤ m` bounds on every numeric component.
* **D5 (exact mass law).**  `ValidSkeleton m` demands `Σ faceLen = m` *exactly*: a recentred
  size-`m` cluster polynomial has all `m` roots of positive valuation, so its lower NP spans
  the full horizontal window `[0, m]`.  The `b·d ≤ m` gate is then a one-line consequence —
  and `μ ≤ d ≤ m/b < m` (§4.2's decrease chain) becomes arithmetic on the stored data.

## What this file does NOT do (scoping, recorded)

* No slope numerators/heights/Presburger regions: node `A0G-NP1`.
* No claim that the face pattern equals the factorization pattern of `dvResPoly` — the
  realization interface pins the dvSide *lengths/degrees* (what C.07/C.29 alone can say);
  binding the residual factorization itself is node `A0G-HE1`'s certification work.
* No measures/weights: nodes `A0G-RW*`.

## Landed inputs consumed

`IFCG0.residuePatternFinset` / `mem_residuePatternFinset_iff` (the A0G-RP bank, reused as the
face-pattern constraint), `Tower.IsDvPure` (C.29), the `dvSide*` bank (C.07:
`dvSideSet/Min/Max/Deg/Len` — note `dvSideDeg = dvSideLen / ℓ` matches `d = faceLen / b`),
`Induction.GenreDatum` (H.01 — its `(e₁, f₁, μ)` are exactly a child entry's `(b, D, μ)`; its
`h` is the numerator this skeleton deliberately does not store).

## Regression pins (recorded in `runs/wave-c/verdict_A0G6.md`)

Skeleton counts at mass `m = 0, 1, 2, 3, 4, 5, 6`: `1, 1, 5, 15, 56, 179, 629` — cross-checked
against an independent Python composition/divisor recursion, with per-length face counts
`1, 4, 6, 15, 18, 43` and IFCG0's residual-pattern counts `1, 1, 3, 5, 11, 17, 34`.

## Status

Sorry-free, axiom-free (Lean core only; the AxCheck footer is the proof).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG5

open Uniformity (FactorizationType)

/-! ## §1 — Face schemas: denominator + residual pattern, everything else derived (D1) -/

/-- **A face schema**: the reduced-slope denominator `b` (first component) and the residual
factorization pattern `σ` (second component; `σ.data` is the multiset of `(D, μ)` residual
degree/multiplicity pairs).  The slope numerator is DELIBERATELY absent (D4): it is an
`A0G-NP1` gap parameter.  The residual degree and the face length are derived, never stored
(D1). -/
abbrev FaceShape : Type := ℕ × FactorizationType

/-- The face's reduced-slope denominator `b` (`= e₁` of any stage the face opens). -/
def faceDen (f : FaceShape) : ℕ := f.1

/-- The face's residual pattern `σ`. -/
def facePat (f : FaceShape) : FactorizationType := f.2

/-- The face's residual degree `d = Σ D·μ` — DERIVED from the pattern (D1). -/
def faceResDeg (f : FaceShape) : ℕ := f.2.degree

/-- The face's horizontal length `b·d` — §4.2's face-length identity, definitionally. -/
def faceLen (f : FaceShape) : ℕ := f.1 * faceResDeg f

/-- **Face validity**: positive denominator, positive residual degree, and positive residual
degree/multiplicity in every pattern entry.  These are IFCG0's residue-pattern constraints at
total `d` plus `1 ≤ b` (see `validFace_iff_mem_residuePatternFinset`). -/
def ValidFace (f : FaceShape) : Prop :=
  1 ≤ f.1 ∧ 1 ≤ faceResDeg f ∧ ∀ p ∈ f.2.data, 1 ≤ p.1 ∧ 1 ≤ p.2

/-- **Dedup with A0G-RP (IFCG0):** face validity is EXACTLY membership of the pattern in the
landed `residuePatternFinset` at the derived degree, plus denominator/degree positivity. -/
theorem validFace_iff_mem_residuePatternFinset (f : FaceShape) :
    ValidFace f ↔ 1 ≤ f.1 ∧ 1 ≤ faceResDeg f ∧
      f.2 ∈ IFCG0.residuePatternFinset (faceResDeg f) := by
  rw [IFCG0.mem_residuePatternFinset_iff]
  unfold ValidFace faceResDeg
  tauto

theorem faceLen_pos {f : FaceShape} (hf : ValidFace f) : 1 ≤ faceLen f :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
    (Nat.one_le_iff_ne_zero.1 hf.1) (Nat.one_le_iff_ne_zero.1 hf.2.1))

/-- Every pattern entry's weight `D·μ` is at most the face's residual degree `d`. -/
theorem entry_weight_le_resDeg {f : FaceShape} {p : ℕ × ℕ} (hp : p ∈ f.2.data) :
    p.1 * p.2 ≤ faceResDeg f := by
  have hmem : p.1 * p.2 ∈ f.2.data.map (fun q => q.1 * q.2) := Multiset.mem_map_of_mem _ hp
  simpa [faceResDeg, FactorizationType.degree] using
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hmem

/-- Every residual-factor degree `D` is at most `d`. -/
theorem entry_fst_le_resDeg {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ}
    (hp : p ∈ f.2.data) : p.1 ≤ faceResDeg f :=
  le_trans (Nat.le_mul_of_pos_right _ (hf.2.2 p hp).2) (entry_weight_le_resDeg hp)

/-- Every residual-factor multiplicity `μ` is at most `d` — the left half of §4.2's decrease
chain `μ ≤ d ≤ m/b`. -/
theorem entry_snd_le_resDeg {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ}
    (hp : p ∈ f.2.data) : p.2 ≤ faceResDeg f := by
  have h1 : p.2 ≤ p.1 * p.2 :=
    calc p.2 ≤ p.2 * p.1 := Nat.le_mul_of_pos_right _ (hf.2.2 p hp).1
    _ = p.1 * p.2 := Nat.mul_comm _ _
  exact le_trans h1 (entry_weight_le_resDeg hp)

/-- The number of residual factors (with multiplicity labels) is at most `d`. -/
theorem card_le_resDeg {f : FaceShape} (hf : ValidFace f) :
    f.2.data.card ≤ faceResDeg f := by
  have h1 : ∀ x ∈ f.2.data.map (fun p => p.1 * p.2), 1 ≤ x := by
    rintro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨hp1, hp2⟩ := hf.2.2 p hp
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2 := Multiset.card_nsmul_le_sum h1
  rw [Multiset.card_map, smul_eq_mul, mul_one] at h2
  simpa [faceResDeg, FactorizationType.degree] using h2

/-! ## §2 — Cluster skeletons at mass `m`: the exact mass law (D5) and the §6 gate -/

/-- **A valid cluster skeleton at mass `m`**: a slope-ordered list of valid faces (D2) whose
horizontal lengths sum to `m` EXACTLY (D5 — a recentred size-`m` cluster polynomial's lower NP
spans the whole window `[0, m]`). -/
def ValidSkeleton (m : ℕ) (s : List FaceShape) : Prop :=
  (∀ f ∈ s, ValidFace f) ∧ (s.map faceLen).sum = m

private theorem list_le_sum_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp hx with h | h
    · omega
    · exact le_trans (ih h) (Nat.le_add_left _ _)

private theorem list_length_le_sum {l : List ℕ} (h1 : ∀ x ∈ l, 1 ≤ x) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h1 a List.mem_cons_self
    have ht := ih (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- **THE §6 GATE, `b·d ≤ m`**: every face's length (denominator × residual degree) is bounded
by the cluster mass.  One line from the exact mass law D5. -/
theorem faceLen_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) : f.1 * faceResDeg f ≤ m := by
  have hmem : faceLen f ∈ s.map faceLen := List.mem_map_of_mem hf
  have h := list_le_sum_of_mem hmem
  rw [hs.2] at h
  exact h

/-- The gate, restated on the derived length. -/
theorem faceLen_le_mass' {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) : faceLen f ≤ m :=
  faceLen_le_mass hs hf

/-- No unbounded datum, component 1: every denominator `b ≤ m`. -/
theorem faceDen_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) : f.1 ≤ m :=
  le_trans (Nat.le_mul_of_pos_right _ ((hs.1 f hf).2.1)) (faceLen_le_mass hs hf)

/-- No unbounded datum, component 2: every residual degree `d ≤ m`. -/
theorem faceResDeg_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) : faceResDeg f ≤ m := by
  have h1 : faceResDeg f ≤ f.1 * faceResDeg f :=
    calc faceResDeg f ≤ faceResDeg f * f.1 := Nat.le_mul_of_pos_right _ ((hs.1 f hf).1)
    _ = f.1 * faceResDeg f := Nat.mul_comm _ _
  exact le_trans h1 (faceLen_le_mass hs hf)

/-- No unbounded datum, component 3: at most `m` faces. -/
theorem length_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s) :
    s.length ≤ m := by
  have h1 : ∀ x ∈ s.map faceLen, 1 ≤ x := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    exact faceLen_pos (hs.1 f hf)
  have h2 := list_length_le_sum h1
  rwa [List.length_map, hs.2] at h2

/-- No unbounded datum, component 4: every residual-factor degree `D ≤ m`. -/
theorem entry_fst_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) {p : ℕ × ℕ} (hp : p ∈ f.2.data) : p.1 ≤ m :=
  le_trans (entry_fst_le_resDeg (hs.1 f hf) hp) (faceResDeg_le_mass hs hf)

/-- No unbounded datum, component 5: every residual-factor multiplicity `μ ≤ m`. -/
theorem entry_snd_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) {p : ℕ × ℕ} (hp : p ∈ f.2.data) : p.2 ≤ m :=
  le_trans (entry_snd_le_resDeg (hs.1 f hf) hp) (faceResDeg_le_mass hs hf)

/-- The weighted entry bound: `b·(D·μ) ≤ m` for every entry of every face — the mass a single
residual factor controls never exceeds the cluster mass. -/
theorem den_mul_entry_weight_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) {p : ℕ × ℕ} (hp : p ∈ f.2.data) :
    f.1 * (p.1 * p.2) ≤ m :=
  le_trans (Nat.mul_le_mul_left _ (entry_weight_le_resDeg hp)) (faceLen_le_mass hs hf)

/-- Mass `0` forces the empty skeleton (and conversely). -/
theorem validSkeleton_zero_iff (s : List FaceShape) :
    ValidSkeleton 0 s ↔ s = [] := by
  constructor
  · intro hs
    cases s with
    | nil => rfl
    | cons a t =>
      exfalso
      have h1 := faceLen_pos (hs.1 a List.mem_cons_self)
      have h2 := faceLen_le_mass' hs (List.mem_cons_self : a ∈ a :: t)
      omega
  · rintro rfl
    exact ⟨fun f hf => absurd hf (List.not_mem_nil), by simp⟩

/-! ## §3 — The finite enumeration: `b·d ≤ m` really does close the schema list (D4)

IFCG0's Sigma-ambient technique, with ordered tuples (`Fin k → _`) instead of `Sym` because
skeletons are ORDERED lists (D2): every valid skeleton embeds into
`(k : Fin (m+1)) × (Fin k → skAlphabet m)`, which is a `Fintype` by construction.  This is the
formal "NO unbounded datum remains" gate: the enumeration is complete
(`mem_clusterSkeletonFinset_iff`), so any datum outside the finite ambient would contradict it. -/

/-- The finite alphabet of faces that can occur at mass `m`: denominator `≤ m`, pattern a
residue pattern (IFCG0) of some degree `≤ m`.  `faceDen_le_mass`/`faceResDeg_le_mass` prove
every face of every valid skeleton lands here. -/
noncomputable def skAlphabet (m : ℕ) : Finset FaceShape :=
  Finset.range (m + 1) ×ˢ (Finset.range (m + 1)).biUnion IFCG0.residuePatternFinset

theorem mem_skAlphabet_of_valid {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) : f ∈ skAlphabet m := by
  unfold skAlphabet
  rw [Finset.mem_product]
  refine ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (faceDen_le_mass hs hf)), ?_⟩
  rw [Finset.mem_biUnion]
  exact ⟨faceResDeg f, Finset.mem_range.2 (Nat.lt_succ_of_le (faceResDeg_le_mass hs hf)),
    ((validFace_iff_mem_residuePatternFinset f).1 (hs.1 f hf)).2.2⟩

/-- The finite ambient space of face-tuples: a length `k ≤ m` and an ordered `k`-tuple of
alphabet faces.  Ordered (`Fin k → _`), not `Sym`: skeletons are slope-ordered lists (D2). -/
abbrev SKSigma (m : ℕ) : Type :=
  (k : Fin (m + 1)) × (Fin (k : ℕ) → ↥(skAlphabet m))

/-- The list reading of an ambient tuple. -/
def skEmbed (m : ℕ) (σ : SKSigma m) : List FaceShape :=
  List.ofFn (fun i => ((σ.2 i : FaceShape)))

/-- **The complete finite enumeration** of cluster skeletons at mass `m`: the valid lists among
the images of the finite ambient space. -/
noncomputable def clusterSkeletonFinset (m : ℕ) : Finset (List FaceShape) :=
  open Classical in
  ((Finset.univ : Finset (SKSigma m)).image (skEmbed m)).filter (ValidSkeleton m)

/-- **Completeness** (the "no unbounded datum" gate's formal content): a list is in the
enumeration IFF it is a valid skeleton at mass `m` — every valid skeleton, with no bound on
where its data might a priori live, is caught by the finite ambient space. -/
theorem mem_clusterSkeletonFinset_iff (m : ℕ) (s : List FaceShape) :
    s ∈ clusterSkeletonFinset m ↔ ValidSkeleton m s := by
  classical
  unfold clusterSkeletonFinset
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hs
    refine ⟨?_, hs⟩
    rw [Finset.mem_image]
    have hlen : s.length ≤ m := length_le_mass hs
    refine ⟨⟨⟨s.length, Nat.lt_succ_of_le hlen⟩,
      fun i => ⟨s.get i, mem_skAlphabet_of_valid hs (List.get_mem s i)⟩⟩,
      Finset.mem_univ _, ?_⟩
    show List.ofFn (fun i => s.get i) = s
    exact List.ofFn_get s

/-- **`ClusterSkeleton m`** — the finite type of face-schema skeletons at cluster mass `m`
(§4.2's finite combinatorial datum: face lengths, reduced slope denominators, residual
degree/multiplicity patterns; child positions are derived, see §5). -/
def ClusterSkeleton (m : ℕ) : Type :=
  {s : List FaceShape // s ∈ clusterSkeletonFinset m}

/-- **THE FINITENESS GATE**: the schemas at mass `m` form a finite type.  Together with
`mem_clusterSkeletonFinset_iff` (no valid skeleton escapes), this is the §6 row's "no
unbounded datum remains in the finite skeleton". -/
noncomputable instance instFintypeClusterSkeleton (m : ℕ) : Fintype (ClusterSkeleton m) :=
  inferInstanceAs (Fintype ↥(clusterSkeletonFinset m))

noncomputable instance instDecidableEqClusterSkeleton (m : ℕ) :
    DecidableEq (ClusterSkeleton m) :=
  inferInstanceAs (DecidableEq ↥(clusterSkeletonFinset m))

/-- The face list of a skeleton. -/
def ClusterSkeleton.faces {m : ℕ} (S : ClusterSkeleton m) : List FaceShape := S.1

theorem ClusterSkeleton.valid {m : ℕ} (S : ClusterSkeleton m) : ValidSkeleton m S.1 :=
  (mem_clusterSkeletonFinset_iff m S.1).1 S.2

/-- Package a valid skeleton. -/
def ClusterSkeleton.ofValid {m : ℕ} {s : List FaceShape} (h : ValidSkeleton m s) :
    ClusterSkeleton m :=
  ⟨s, (mem_clusterSkeletonFinset_iff m s).2 h⟩

/-! ## §4 — The π-rescale loop as a distinguished skeleton (D3), and its uniqueness

§4.2: "Integral translations/recentrings either expose such a face or enter the one π-rescale
loop."  The loop — all `m` roots together at one rational point — is the single-face skeleton
`[(1, {(1, m)})]`: one integral-slope face carrying one rational residual point of full
multiplicity.  The uniqueness theorem below is A0G-GC3's "the rescale is the SOLE same-mass
edge", proved at the skeleton level BY CONSTRUCTION: the mere presence of a multiplicity-`m`
entry pins every remaining datum. -/

/-- The loop face: denominator `1`, residual pattern one rational point `(D, μ) = (1, m)`. -/
def loopFace (m : ℕ) : FaceShape := (1, ⟨{(1, m)}⟩)

/-- The π-rescale loop skeleton at mass `m`. -/
def loopSkeleton (m : ℕ) : List FaceShape := [loopFace m]

theorem faceResDeg_loopFace (m : ℕ) : faceResDeg (loopFace m) = m := by
  simp [loopFace, faceResDeg, FactorizationType.degree]

theorem faceLen_loopFace (m : ℕ) : faceLen (loopFace m) = m := by
  rw [faceLen, faceResDeg_loopFace]
  simp [loopFace]

theorem validSkeleton_loopSkeleton {m : ℕ} (hm : 1 ≤ m) :
    ValidSkeleton m (loopSkeleton m) := by
  constructor
  · intro f hf
    have hfe : f = loopFace m := by simpa [loopSkeleton] using hf
    subst hfe
    refine ⟨le_refl 1, ?_, ?_⟩
    · rw [faceResDeg_loopFace]; exact hm
    · intro p hp
      have hpe : p = (1, m) := by simpa [loopFace] using hp
      subst hpe
      exact ⟨le_refl 1, hm⟩
  · simp [loopSkeleton, faceLen_loopFace]

/-- **The same-mass edge is unique, by construction** (feeds A0G-GC3's loop tooth): if ANY
residual entry of ANY face of a valid mass-`m` skeleton has multiplicity `μ = m`, then the
skeleton IS the loop skeleton, the face IS the loop face, and the entry IS `(1, m)`. -/
theorem eq_loopSkeleton_of_entry_snd_eq_mass {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s) {p : ℕ × ℕ}
    (hp : p ∈ f.2.data) (hpm : p.2 = m) :
    s = loopSkeleton m ∧ f = loopFace m ∧ p = (1, m) := by
  have hval : ValidFace f := hs.1 f hf
  have hμ1 : 1 ≤ p.2 := (hval.2.2 p hp).2
  have hD1 : 1 ≤ p.1 := (hval.2.2 p hp).1
  -- `d = m`: `m = μ ≤ d ≤ m`
  have hdm : faceResDeg f = m := by
    have h1 := entry_snd_le_resDeg hval hp
    have h2 := faceResDeg_le_mass hs hf
    omega
  -- `D = 1`: `D·μ ≤ d = m = μ`
  have hD : p.1 = 1 := by
    have h1 := entry_weight_le_resDeg hp
    rw [hdm, ← hpm] at h1
    have h2 : p.1 * p.2 ≤ 1 * p.2 := by omega
    have := Nat.le_of_mul_le_mul_right h2 (by omega : 0 < p.2)
    omega
  -- `b = 1`: `b·d ≤ m = d`
  have hb : f.1 = 1 := by
    have h1 := faceLen_le_mass hs hf
    rw [hdm] at h1
    have h2 : f.1 * m ≤ 1 * m := by omega
    have := Nat.le_of_mul_le_mul_right h2 (by omega : 0 < m)
    have := hval.1
    omega
  -- the entry is `(1, m)`
  have hpe : p = (1, m) := by
    have : p = (p.1, p.2) := rfl
    rw [this, hD, hpm]
  -- the pattern is exactly `{(1, m)}`: the remaining entries have total weight `0`
  have hpat : f.2.data = {(1, m)} := by
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hp
    have hdeg : ((p ::ₘ t).map (fun q => q.1 * q.2)).sum = m := by
      have : faceResDeg f = m := hdm
      simpa [faceResDeg, FactorizationType.degree, ht] using this
    rw [Multiset.map_cons, Multiset.sum_cons, hD, hpm, one_mul] at hdeg
    have hrest : (t.map (fun q => q.1 * q.2)).sum = 0 := by omega
    have ht0 : t = 0 := by
      by_contra hne
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hne
      have hqf : q ∈ f.2.data := by rw [ht]; exact Multiset.mem_cons_of_mem hq
      obtain ⟨hq1, hq2⟩ := hval.2.2 q hqf
      have hmem : q.1 * q.2 ∈ t.map (fun q => q.1 * q.2) := Multiset.mem_map_of_mem _ hq
      have hle := Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
      rw [hrest] at hle
      have : 1 ≤ q.1 * q.2 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [ht, ht0, hpe]
    rfl
  -- the face is the loop face
  have hface : f = loopFace m := by
    have h2 : f.2 = (⟨{(1, m)}⟩ : FactorizationType) := FactorizationType.ext hpat
    have h1 : f = (f.1, f.2) := rfl
    rw [h1, hb, h2]
    rfl
  -- the skeleton is the single loop face: the other faces have total length `0`
  refine ⟨?_, hface, hpe⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hf
  have hflen : faceLen f = m := by rw [hface, faceLen_loopFace]
  have hsum := hs.2
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, hflen] at hsum
  have hz1 : (l1.map faceLen).sum = 0 := by omega
  have hz2 : (l2.map faceLen).sum = 0 := by omega
  have hl1 : l1 = [] := by
    cases l1 with
    | nil => rfl
    | cons a t =>
      exfalso
      have ha : a ∈ (a :: t) ++ f :: l2 := List.mem_append_left _ List.mem_cons_self
      have h1 := faceLen_pos (hs.1 a ha)
      have hmem : faceLen a ∈ (a :: t).map faceLen := List.mem_map_of_mem List.mem_cons_self
      have := list_le_sum_of_mem hmem
      omega
  have hl2 : l2 = [] := by
    cases l2 with
    | nil => rfl
    | cons a t =>
      exfalso
      have ha : a ∈ l1 ++ f :: a :: t := by
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have h1 := faceLen_pos (hs.1 a ha)
      have hmem : faceLen a ∈ (a :: t).map faceLen := List.mem_map_of_mem List.mem_cons_self
      have := list_le_sum_of_mem hmem
      omega
  rw [hl1, hl2, hface]
  rfl

/-! ## §5 — Children and leaves: §4.2's generation law and the A0G-CH feed

"Residual factors of degree `D` and multiplicity `μ` generate leaves `(b, D)` when `μ = 1`, or
recursive clusters of size `μ` over `F_(q^D)` when `μ > 1`.  Since `μ ≤ d ≤ m/b < m`, recursion
decreases."  Child positions are DERIVED from the pattern (D1) — a face's children are its
multiplicity-`≥ 2` entries; nothing is stored. -/

/-- `p` is a **recursive child entry**: a residual factor of multiplicity `μ = p.2 ≥ 2` on a
face of `s` — a recursive cluster call of size `μ` over the degree-`D = p.1` residue extension. -/
def IsChildEntry (s : List FaceShape) (f : FaceShape) (p : ℕ × ℕ) : Prop :=
  f ∈ s ∧ p ∈ f.2.data ∧ 2 ≤ p.2

/-- `p` is a **leaf entry**: a simple residual factor (`μ = 1`) — an unramified-along-the-face
output block `(e, f) = (b, D)` relative to the stage. -/
def IsLeafEntry (s : List FaceShape) (f : FaceShape) (p : ℕ × ℕ) : Prop :=
  f ∈ s ∧ p ∈ f.2.data ∧ p.2 = 1

/-- Off the loop skeleton, EVERY residual multiplicity decreases strictly — the A0G-CH feed
(clause 3 of §4.2's stop-line list, at the skeleton level). -/
theorem entry_snd_lt_mass_of_ne_loop {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    (hne : s ≠ loopSkeleton m) {f : FaceShape} (hf : f ∈ s) {p : ℕ × ℕ}
    (hp : p ∈ f.2.data) : p.2 < m := by
  have hle := entry_snd_le_mass hs hf hp
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact absurd (eq_loopSkeleton_of_entry_snd_eq_mass hs hf hp heq).1 hne
  · exact hlt

/-- Child decrease, unconditional form: a recursive child is strictly smaller than the cluster
mass unless the skeleton is the loop (in which case the child IS the loop's `(1, m)` entry). -/
theorem childEntry_lt_mass_or_loop {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} {p : ℕ × ℕ} (hc : IsChildEntry s f p) :
    p.2 < m ∨ (s = loopSkeleton m ∧ f = loopFace m ∧ p = (1, m)) := by
  have hle := entry_snd_le_mass hs hc.1 hc.2.1
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact Or.inr (eq_loopSkeleton_of_entry_snd_eq_mass hs hc.1 hc.2.1 heq)
  · exact Or.inl hlt

/-- The quantitative fractional-face bound: on a face of denominator `b ≥ 2`, every
multiplicity satisfies `2μ ≤ m` (§4.2's `μ ≤ d ≤ m/b`, cleared of division). -/
theorem two_mul_entry_snd_le_mass_of_two_le_den {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s) (hb : 2 ≤ f.1)
    {p : ℕ × ℕ} (hp : p ∈ f.2.data) : 2 * p.2 ≤ m := by
  have h1 := entry_snd_le_resDeg (hs.1 f hf) hp
  have h2 := faceLen_le_mass hs hf
  have h3 : 2 * faceResDeg f ≤ f.1 * faceResDeg f := Nat.mul_le_mul_right _ hb
  omega

/-- Leaf legality: a leaf entry's output block `(e, f) = (b, D)` has `b·D ≤ m`. -/
theorem leaf_ef_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} {p : ℕ × ℕ} (hl : IsLeafEntry s f p) : f.1 * p.1 ≤ m := by
  have h := den_mul_entry_weight_le_mass hs hl.1 hl.2.1
  rw [hl.2.2, Nat.mul_one] at h
  exact h

/-- **Mass conservation**: summing `b·D·μ` over all residual entries of all faces recovers the
cluster mass exactly — the bookkeeping identity A0G-AS's convolution will consume. -/
theorem mass_conservation {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s) :
    (s.map (fun f => (f.2.data.map (fun p => f.1 * (p.1 * p.2))).sum)).sum = m := by
  have hcong : s.map (fun f => (f.2.data.map (fun p => f.1 * (p.1 * p.2))).sum)
      = s.map faceLen := by
    apply List.map_congr_left
    intro f _
    rw [Multiset.sum_map_mul_left]
    simp [faceLen, faceResDeg, FactorizationType.degree]
  rw [hcong]
  exact hs.2

/-- The multiset of recursive child sizes of a skeleton (with repetition, across all faces). -/
def childSizes (s : List FaceShape) : Multiset ℕ :=
  (s.map (fun f => (f.2.data.map Prod.snd).filter (fun μ => 2 ≤ μ))).sum

private theorem mem_list_sum_multiset {α : Type*} {l : List (Multiset α)} {a : α} :
    a ∈ l.sum ↔ ∃ t ∈ l, a ∈ t := by
  induction l with
  | nil => simp
  | cons b t ih => simp [List.sum_cons, ih]

theorem mem_childSizes_iff {s : List FaceShape} {μ : ℕ} :
    μ ∈ childSizes s ↔ ∃ f ∈ s, ∃ p ∈ f.2.data, p.2 = μ ∧ 2 ≤ μ := by
  unfold childSizes
  rw [mem_list_sum_multiset]
  constructor
  · rintro ⟨t, ht, hμ⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ht
    rw [Multiset.mem_filter] at hμ
    obtain ⟨hmem, h2⟩ := hμ
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hmem
    exact ⟨f, hf, p, hp, rfl, h2⟩
  · rintro ⟨f, hf, p, hp, rfl, h2⟩
    refine ⟨_, List.mem_map_of_mem hf, ?_⟩
    rw [Multiset.mem_filter]
    exact ⟨Multiset.mem_map_of_mem _ hp, h2⟩

/-- The A0G-CH feed, packaged on `childSizes`: off the loop, all child sizes are `< m`. -/
theorem childSizes_lt_mass_of_ne_loop {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) (hne : s ≠ loopSkeleton m) :
    ∀ μ ∈ childSizes s, μ < m := by
  intro μ hμ
  obtain ⟨f, hf, p, hp, hpμ, _⟩ := mem_childSizes_iff.1 hμ
  exact hpμ ▸ entry_snd_lt_mass_of_ne_loop hs hne hf hp

/-- The loop skeleton's unique child is the full-mass rational cluster itself. -/
theorem childSizes_loopSkeleton {m : ℕ} (hm : 2 ≤ m) :
    childSizes (loopSkeleton m) = {m} := by
  simp only [childSizes, loopSkeleton, loopFace, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [show ((⟨{(1, m)}⟩ : FactorizationType).data.map Prod.snd) = ({m} : Multiset ℕ) from by
    simp]
  rw [Multiset.filter_singleton]
  simp [hm]

/-! ## §6 — Binding to chapter H's genre machinery: H.01 `GenreDatum`

H.01's `GenreDatum (Q; e₁, f₁, μ; h)` is the local invariant package of a composite-stage
opening.  Its `(e₁, f₁, μ)` are EXACTLY a child entry's `(b, D, μ)`; its `h` is the slope
numerator this skeleton deliberately does not store (D4) — so the binding is a constructor
taking `h` (and the ambient residue cardinality `Q`) as explicit arguments, with every H.01
side condition discharged from skeleton facts. -/

open Uniformity.Density.Induction (GenreDatum)

/-- Package a recursive child entry `(b, D, μ) = (f.1, p.1, p.2)` as an H.01 `GenreDatum`,
given the two NP1-parameters the skeleton does not carry: the ambient residue cardinality `Q`
and the reduced slope numerator `h` (coprime to the denominator).  `hkey : 2 ≤ b·D` excludes
exactly the rational-recentre child `b = D = 1` — which H.01 also excludes ("else the event is
order-1 α/β"): that child is the recentring/rescale path, not a composite-stage opening. -/
def genreDatumOfChildEntry (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h)
    {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ} (_hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    GenreDatum :=
  { Q := Q, e₁ := f.1, f₁ := p.1, μ := p.2, h := h,
    hQ := hQ, he₁ := hf.1, hh := hh, hkey := hkey, hmul := hμ, hcop := hcop }

@[simp] theorem genreDatumOfChildEntry_e₁ (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h)
    {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ} (hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    (genreDatumOfChildEntry Q h hQ hh hf hp hμ hkey hcop).e₁ = f.1 := rfl

@[simp] theorem genreDatumOfChildEntry_f₁ (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h)
    {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ} (hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    (genreDatumOfChildEntry Q h hQ hh hf hp hμ hkey hcop).f₁ = p.1 := rfl

@[simp] theorem genreDatumOfChildEntry_μ (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h)
    {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ} (hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    (genreDatumOfChildEntry Q h hQ hh hf hp hμ hkey hcop).μ = p.2 := rfl

@[simp] theorem genreDatumOfChildEntry_h (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h)
    {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ} (hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    (genreDatumOfChildEntry Q h hQ hh hf hp hμ hkey hcop).h = h := rfl

@[simp] theorem genreDatumOfChildEntry_Q (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h)
    {f : FaceShape} (hf : ValidFace f) {p : ℕ × ℕ} (hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    (genreDatumOfChildEntry Q h hQ hh hf hp hμ hkey hcop).Q = Q := rfl

/-- On a fractional face (`b ≥ 2`), H.01's key condition `2 ≤ e₁·f₁` is automatic. -/
theorem two_le_den_mul_fst_of_two_le_den {f : FaceShape} (hf : ValidFace f) (hb : 2 ≤ f.1)
    {p : ℕ × ℕ} (hp : p ∈ f.2.data) : 2 ≤ f.1 * p.1 :=
  le_trans hb (Nat.le_mul_of_pos_right _ (hf.2.2 p hp).1)

/-- The opened stage's total degree `e₁·f₁·μ` is bounded by the cluster mass — the stage a
child entry opens fits inside the cluster. -/
theorem stage_degree_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} (hf : f ∈ s) {p : ℕ × ℕ} (hp : p ∈ f.2.data) :
    f.1 * p.1 * p.2 ≤ m := by
  have h := den_mul_entry_weight_le_mass hs hf hp
  rw [Nat.mul_assoc]
  exact h

/-! ## §7 — Binding to the dv-side bank (C.07/C.29): the realization interface for A0G-HE

The skeleton's `(b, d)` are the dv-side's `(ℓ, dvSideDeg)`: C.07 defines
`dvSideDeg = dvSideLen / ℓ`, exactly `d = (b·d) / b`.  `RealizesFaceAt` pins a pure block to a
face by its side LENGTH (what C.07/C.29 alone can certify); matching the residual pattern to
the factorization of `dvResPoly` is A0G-HE1's certification work (scoping note in the header).
The slope numerator enters ONLY as the argument `h` (D4). -/

section DvBinding

open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The face realization predicate** (the A0G-HE binding surface, per-face): `g` is
`(h, b)`-dv-pure at the frame (its level polygon is one-sided of reduced slope `h/b`), and its
side length is the face length `b·d`.  Purity supplies `0 ∈ dvSideSet`, so the side is
nonempty with left endpoint `0`. -/
def RealizesFaceAt (F : KeyFrame O π) (g : Polynomial O) (h : ℕ) (f : FaceShape) : Prop :=
  1 ≤ h ∧ Nat.Coprime h f.1 ∧
  ∃ hpure : IsDvPure F g h f.1,
    dvSideLen F g h f.1 ⟨0, hpure.1⟩ = faceLen f

/-- A dv-pure polynomial's side has left endpoint `0` (C.29 purity pins the abscissa `0` on
the side; the minimum of a set of naturals containing `0` is `0`). -/
theorem dvSideMin_eq_zero_of_isDvPure {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ}
    (hpure : IsDvPure F g u ℓ) :
    dvSideMin F g u ℓ ⟨0, hpure.1⟩ = 0 :=
  Nat.le_zero.1 (Finset.min'_le _ 0 hpure.1)

/-- Under realization, the side's right endpoint is the face length. -/
theorem dvSideMax_eq_of_realizes {F : KeyFrame O π} {g : Polynomial O} {h : ℕ}
    {f : FaceShape} (hr : RealizesFaceAt F g h f) :
    ∃ hne : (dvSideSet F g h f.1).Nonempty, dvSideMax F g h f.1 hne = faceLen f := by
  obtain ⟨hh, hcop, hpure, hlen⟩ := hr
  refine ⟨⟨0, hpure.1⟩, ?_⟩
  have hmin := dvSideMin_eq_zero_of_isDvPure hpure
  unfold dvSideLen at hlen
  omega

/-- **The `d = len / b` reconciliation**: under realization, C.07's side residual degree
`dvSideDeg` is EXACTLY the face's derived residual degree — the skeleton's `d` and the
engine's `d_λ` agree on the nose (the `ℕ`-division `(b·d)/b` is exact). -/
theorem dvSideDeg_eq_of_realizes {F : KeyFrame O π} {g : Polynomial O} {h : ℕ}
    {f : FaceShape} (hf : ValidFace f) (hr : RealizesFaceAt F g h f) :
    ∃ hne : (dvSideSet F g h f.1).Nonempty, dvSideDeg F g h f.1 hne = faceResDeg f := by
  obtain ⟨hh, hcop, hpure, hlen⟩ := hr
  refine ⟨⟨0, hpure.1⟩, ?_⟩
  unfold dvSideLen at hlen
  unfold dvSideDeg
  rw [hlen, faceLen, Nat.mul_div_cancel_left _ hf.1]

/-- Under realization, the block's key-adjusted degree is bounded by the face length —
the abscissa window a pure block occupies never exceeds `b·d` (and hence, in a valid
skeleton, never exceeds the mass `m`, by `faceLen_le_mass`). -/
theorem natDegree_div_le_of_realizes {F : KeyFrame O π} {g : Polynomial O} {h : ℕ}
    {f : FaceShape} (hr : RealizesFaceAt F g h f) :
    g.natDegree / (F.e₁ * F.f₁) ≤ faceLen f := by
  obtain ⟨hne, hmax⟩ := dvSideMax_eq_of_realizes hr
  obtain ⟨hh, hcop, hpure, hlen⟩ := hr
  have hle : g.natDegree / (F.e₁ * F.f₁) ≤ dvSideMax F g h f.1 hne :=
    Finset.le_max' _ _ hpure.2
  rw [← hmax]
  exact hle

/-- Slope numerators for a skeleton's faces, in strictly increasing slope order — D2's list
order made quantitative: `h i / b i < h j / b j` for `i < j`, cross-multiplied so no rational
numbers (and no unbounded skeleton datum) appear. -/
def SlopesOrdered (s : List FaceShape) (num : Fin s.length → ℕ) : Prop :=
  ∀ i j : Fin s.length, (i : ℕ) < (j : ℕ) → num i * (s.get j).1 < num j * (s.get i).1

/-- **The whole-skeleton realization surface for A0G-HE**: one pure block per face, each
realizing its face at its numerator, with slopes strictly increasing along the list (D2). -/
def RealizesSkeletonAt (F : KeyFrame O π) {m : ℕ} (S : ClusterSkeleton m)
    (num : Fin S.1.length → ℕ) (blocks : Fin S.1.length → Polynomial O) : Prop :=
  SlopesOrdered S.1 num ∧ ∀ i, RealizesFaceAt F (blocks i) (num i) (S.1.get i)

/-- Bookkeeping for A0G-HE: the realized blocks' side lengths sum to the cluster mass `m`
exactly (D5's mass law transported through the realization). -/
theorem realization_sideLen_sum {F : KeyFrame O π} {m : ℕ} {S : ClusterSkeleton m}
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    (hr : RealizesSkeletonAt F S num blocks)
    (hne : ∀ i, (dvSideSet F (blocks i) (num i) (S.1.get i).1).Nonempty) :
    ((List.finRange S.1.length).map
      (fun i => dvSideLen F (blocks i) (num i) (S.1.get i).1 (hne i))).sum = m := by
  have hterm : ∀ i : Fin S.1.length,
      dvSideLen F (blocks i) (num i) (S.1.get i).1 (hne i) = faceLen (S.1.get i) := by
    intro i
    obtain ⟨hh, hcop, hpure, hlen⟩ := hr.2 i
    exact hlen
  have h1 : (List.finRange S.1.length).map
        (fun i => dvSideLen F (blocks i) (num i) (S.1.get i).1 (hne i))
      = (List.finRange S.1.length).map (fun i => faceLen (S.1.get i)) :=
    List.map_congr_left (fun i _ => hterm i)
  have h2 : (List.finRange S.1.length).map (fun i => faceLen (S.1.get i))
      = S.1.map faceLen := by
    rw [show (fun i => faceLen (S.1.get i)) = faceLen ∘ S.1.get from rfl,
      ← List.ofFn_eq_map, ← List.map_ofFn, List.ofFn_get]
  rw [h1, h2]
  exact S.valid.2

end DvBinding

/-! ## §9 — Machine pins on the official enumeration (`m = 0, 1`), and the executable mirror

The official `clusterSkeletonFinset` is noncomputable (`FactorizationType`'s only
`DecidableEq` is `Classical.decEq` — same situation as IFCG0's `residuePatternFinset`), so
the `m = 0, 1` pins below are PROVED, and the higher-mass counts are checked by the
`FactorizationType`-free executable mirror (never cited by any proof — IFCG0 precedent). -/

/-- Mass `0`: exactly the empty skeleton. -/
theorem clusterSkeletonFinset_zero : clusterSkeletonFinset 0 = {([] : List FaceShape)} := by
  ext s
  rw [mem_clusterSkeletonFinset_iff, Finset.mem_singleton, validSkeleton_zero_iff]

/-- Mass `1`: exactly the loop skeleton — a size-one cluster is already all-at-one-point. -/
theorem clusterSkeletonFinset_one : clusterSkeletonFinset 1 = {loopSkeleton 1} := by
  ext s
  rw [mem_clusterSkeletonFinset_iff, Finset.mem_singleton]
  constructor
  · intro hs
    cases s with
    | nil => simp [ValidSkeleton] at hs
    | cons f t =>
      have hf : f ∈ f :: t := List.mem_cons_self
      have hval : ValidFace f := hs.1 f hf
      have hne0 : f.2.data ≠ 0 := by
        intro h0
        have hd := hval.2.1
        simp [faceResDeg, FactorizationType.degree, h0] at hd
      obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hne0
      have h1 : 1 ≤ p.2 := (hval.2.2 p hp).2
      have h2 : p.2 ≤ 1 := entry_snd_le_mass hs hf hp
      have hpm : p.2 = 1 := by omega
      exact (eq_loopSkeleton_of_entry_snd_eq_mass hs hf hp hpm).1
  · rintro rfl
    exact validSkeleton_loopSkeleton (le_refl 1)

/-- Face count at exact length `ℓ`: one term per divisor `b ∣ ℓ`, counting the residual
patterns of degree `ℓ / b` via IFCG0's executable `rpCountFast`. -/
def facesCountFast (ℓ : ℕ) : ℕ :=
  (((List.range ℓ).map (· + 1)).filter (· ∣ ℓ)).foldl
    (fun acc b => acc + IFCG0.rpCountFast (ℓ / b)) 0

/-- Skeleton count at mass `m`: compositions of `m` into face lengths, weighted by
`facesCountFast` — the executable mirror of `(clusterSkeletonFinset m).card`.  `partial def`:
computational check only, never cited by a proof (IFCG0's `rpGen` precedent). -/
partial def skCountFast (m : ℕ) : ℕ :=
  if m = 0 then 1
  else ((List.range m).map (· + 1)).foldl
    (fun acc ℓ => acc + facesCountFast ℓ * skCountFast (m - ℓ)) 0

-- Per-length face counts `1, 4, 6, 15` (ℓ = 1..4) and skeleton counts `1, 1, 5, 15, 56,
-- 179, 629` (m = 0..6), cross-checked against an independent Python composition/divisor
-- recursion over IFCG0's independently-verified residual-pattern counts `1, 1, 3, 5, 11, 17,
-- 34` (recorded in `runs/wave-c/verdict_A0G6.md`).  The `m = 0, 1` values also match the
-- PROVED pins `clusterSkeletonFinset_zero`/`_one` above.
#eval facesCountFast 1
#eval facesCountFast 2
#eval facesCountFast 3
#eval facesCountFast 4
#eval skCountFast 0
#eval skCountFast 1
#eval skCountFast 2
#eval skCountFast 3
#eval skCountFast 4
#eval skCountFast 5
#eval skCountFast 6

end Uniformity.Density.IFCG5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG5.validFace_iff_mem_residuePatternFinset
#print axioms Uniformity.Density.IFCG5.entry_weight_le_resDeg
#print axioms Uniformity.Density.IFCG5.entry_fst_le_resDeg
#print axioms Uniformity.Density.IFCG5.entry_snd_le_resDeg
#print axioms Uniformity.Density.IFCG5.card_le_resDeg
#print axioms Uniformity.Density.IFCG5.faceLen_le_mass
#print axioms Uniformity.Density.IFCG5.faceDen_le_mass
#print axioms Uniformity.Density.IFCG5.faceResDeg_le_mass
#print axioms Uniformity.Density.IFCG5.length_le_mass
#print axioms Uniformity.Density.IFCG5.entry_fst_le_mass
#print axioms Uniformity.Density.IFCG5.entry_snd_le_mass
#print axioms Uniformity.Density.IFCG5.den_mul_entry_weight_le_mass
#print axioms Uniformity.Density.IFCG5.validSkeleton_zero_iff
#print axioms Uniformity.Density.IFCG5.mem_skAlphabet_of_valid
#print axioms Uniformity.Density.IFCG5.mem_clusterSkeletonFinset_iff
#print axioms Uniformity.Density.IFCG5.instFintypeClusterSkeleton
#print axioms Uniformity.Density.IFCG5.ClusterSkeleton.valid
#print axioms Uniformity.Density.IFCG5.ClusterSkeleton.ofValid
#print axioms Uniformity.Density.IFCG5.faceResDeg_loopFace
#print axioms Uniformity.Density.IFCG5.faceLen_loopFace
#print axioms Uniformity.Density.IFCG5.validSkeleton_loopSkeleton
#print axioms Uniformity.Density.IFCG5.eq_loopSkeleton_of_entry_snd_eq_mass
#print axioms Uniformity.Density.IFCG5.entry_snd_lt_mass_of_ne_loop
#print axioms Uniformity.Density.IFCG5.childEntry_lt_mass_or_loop
#print axioms Uniformity.Density.IFCG5.two_mul_entry_snd_le_mass_of_two_le_den
#print axioms Uniformity.Density.IFCG5.leaf_ef_le_mass
#print axioms Uniformity.Density.IFCG5.mass_conservation
#print axioms Uniformity.Density.IFCG5.mem_childSizes_iff
#print axioms Uniformity.Density.IFCG5.childSizes_lt_mass_of_ne_loop
#print axioms Uniformity.Density.IFCG5.childSizes_loopSkeleton
#print axioms Uniformity.Density.IFCG5.genreDatumOfChildEntry
#print axioms Uniformity.Density.IFCG5.two_le_den_mul_fst_of_two_le_den
#print axioms Uniformity.Density.IFCG5.stage_degree_le_mass
#print axioms Uniformity.Density.IFCG5.dvSideMin_eq_zero_of_isDvPure
#print axioms Uniformity.Density.IFCG5.dvSideMax_eq_of_realizes
#print axioms Uniformity.Density.IFCG5.dvSideDeg_eq_of_realizes
#print axioms Uniformity.Density.IFCG5.natDegree_div_le_of_realizes
#print axioms Uniformity.Density.IFCG5.realization_sideLen_sum
#print axioms Uniformity.Density.IFCG5.clusterSkeletonFinset_zero
#print axioms Uniformity.Density.IFCG5.clusterSkeletonFinset_one
