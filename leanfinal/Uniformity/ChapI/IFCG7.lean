/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG6

/-!
# Uniformity.ChapI.IFCG7 — [NP1 2026-08-29] gap/slope parameters and Presburger constraints
(node A0G-NP1)

**Uniform-a0 campaign, NODE A0G-NP1** (`docs/in-progress/A0_GENERAL_2026-08-28.md` §4.2 +
the §6 row "A0G-NP1 gap parameters | canonical gap/slope parameters and Presburger
constraints | NP0/CV1 | gate: **reconstruction and uniqueness**").  Scoped per
`runs/wave-c/verdict_A0G7.md`: "GC2 (disjointness) has its residual-level ingredient
(`face_split_unique`), but its parameter-level half needs **A0G-NP1 (gap/slope parameters +
Presburger regions)** — NP1 must precede GC."

IFCG5 (node NP0) deliberately stores NO unbounded datum in a skeleton (its D4): the slope
numerators enter only as *arguments* (`RealizesFaceAt`'s `h`, `genreDatumOfChildEntry`'s
`h`).  This file is the other half: the numerators as a CANONICAL parameter system —

* **§1 the parameter carrier.**  `ValidSlopeParams s num` — per-face positivity +
  reduced-fraction coprimality + IFCG5's `SlopesOrdered` (D2's cross-multiplied
  increasing-slope law).  This is EXACTLY the parameter data of a `RealizesSkeletonAt`
  witness (`validSlopeParams_of_realizes`), so the carrier is canonical by construction.
* **§2 the chain reduction.**  `SlopesOrdered` (all pairs) ⟺ `SlopeChain` (consecutive
  faces only) — the constraint list is FINITE and local; transitivity of cross-multiplied
  fraction comparison (denominators positive) recovers all pairs.
* **§3 gap coordinates + reconstruction/uniqueness (gate half 1).**  `slopeGap i` =
  `num(i+1)·b(i) − num(i)·b(i+1)`, the slope increment in units `1/(b(i)·b(i+1))`.  The
  chain law is `1 ≤ slopeGap i` (`one_le_slopeGap_iff_chain`), the defining identity is
  exact (`slopeGap_recon`), and `(num 0, gaps)` RECONSTRUCT the numerators uniquely
  (`num_eq_of_slopeGap_eq`) — the §4.2 "unbounded numerator/gap variables" are honest
  coordinates.  (Which gap tuples are realizable is a congruence-chain question — that is
  the region's `mod` atoms, §5; the geometric summation over them is node A0G-RW1.)
* **§4 polygon reconstruction + uniqueness (gate half 2).**  From skeleton + parameters,
  the literal lower Newton polygon in ℕ: abscissae `vertexX` (partial sums of face
  lengths; `0` to `m` exactly, strictly increasing) and heights `vertexY` (suffix sums of
  the INTEGER per-face drops `num i · d i` — slope `h/b` × length `b·d` = `h·d`, no
  rationals).  Conversely the polygon determines the parameters: `num_eq_of_vertexY_eq`.
* **§5 the Presburger region.**  A quantifier-free Presburger formula grammar
  (`PresAtom` = linear inequality / linear congruence over `Fin r → ℕ`; `PresburgerRegion`
  = and/or closure; DECIDABLE semantics) — the `constraints : PresburgerRegion r` field of
  §4.2's `ClusterGenre` sketch, landed.  THE theorem: for every skeleton, the valid
  parameter tuples are EXACTLY a constructed region — `holds_slopeRegion_iff`:
  `(slopeRegion s).Holds num ↔ ValidSlopeParams s num` (positivity atoms + consecutive
  chain atoms + coprimality as a disjunction of congruences mod each `b`).  Corollary:
  `ValidSlopeParams` is decidable (`decValidSlopeParams`).
* **§6 realization uniqueness (the GC2 parameter-level feed).**  dv-purity pins the
  reduced slope: `isDvPure_slope_unique` — a polynomial `g` of positive key-degree window
  is `(u,ℓ)`- and `(u′,ℓ′)`-dv-pure only if `(u,ℓ) = (u′,ℓ′)` (endpoint equations of
  C.29 purity at the shared abscissae `0` and `deg g / D′`, then reduced-fraction
  arithmetic).  At the face surface: a block realizes at most one numerator/denominator/
  length/residual-degree (`realizesFaceAt_param_unique`), a block's degree window
  RECONSTRUCTS the face length (`natDegree_div_eq_faceLen_of_realizes`), and at the
  skeleton surface two realizations by the same blocks carry the same parameters and the
  same mass (`realizesSkeletonAt_params_unique`, `mass_eq_of_realizes_same_blocks`).
  Combined with IFCG6's `face_split_unique` (the residual-level half, already landed),
  A0G-GC2's disjointness inputs are complete.

## What this file does NOT do (scoping, recorded)

* No classifier: nothing here produces a skeleton or parameters from a raw coefficient
  vector — that is A0G-GC0/GC1 (the A0G7 verdict's stop line).
* No measures/summation: the geometric summation over the region's unbounded variables is
  A0G-RW1 (which consumes `slopeRegion`'s shape: per-variable positive decay).
* No CV1 (box) interaction: parameter measurability on the coefficient boxes is GC0's
  binding work; nothing combinatorial here needs CV0/CV1.
* The semantic tie `vertexY s num 0 = v(g(0))` (total polygon height = constant-term
  valuation) needs the actual polynomial and belongs to the classifier nodes; here
  `vertexY` is the declared reconstruction, consumed forward.

## Landed inputs consumed

IFCG5's face/skeleton bank (`FaceShape`, `ValidFace`, `ValidSkeleton`, `ClusterSkeleton`,
`faceLen`/`faceResDeg`, `SlopesOrdered`, `RealizesFaceAt`, `RealizesSkeletonAt`,
`faceLen_pos`); C.29 `IsDvPure`; C.35's public purity endpoint calculus
(`dvOnSide_of_mem_dvSideSet`, `dvSideMin_eq_zero_of_isDvPure`, `dvSideMax_eq_of_isDvPure`);
C.07's `dvSideLen`.  The private endpoint equation `dvOnSide_nat_eq` is re-derived from
C.08's mechanism (private there, hence unreachable; credited; C.08 not edited).

## Status

Sorry-free.  AxCheck footer: every declaration Lean core only (`propext`,
`Classical.choice`, `Quot.sound`) — no cite anywhere (the C.33 dissection cite enters only
at IFCG6's two ambient theorems, which this file does not consume).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG7

open Uniformity (FactorizationType)
open Uniformity.Density.IFCG5

/-! ## §1 — The slope-parameter carrier -/

/-- **The valid slope parameters of a skeleton** (the canonical A0G-NP1 parameter system):
one numerator per face, positive, coprime to its face's denominator (the slope `num i / bᵢ`
in lowest terms), with slopes strictly increasing along the list (IFCG5's D2 order, in the
cross-multiplied `SlopesOrdered` form).  This is EXACTLY the parameter data carried by a
`RealizesSkeletonAt` witness — see `validSlopeParams_of_realizes`. -/
def ValidSlopeParams (s : List FaceShape) (num : Fin s.length → ℕ) : Prop :=
  (∀ i, 1 ≤ num i ∧ Nat.Coprime (num i) (s.get i).1) ∧ SlopesOrdered s num

/-! ## §2 — The chain reduction: consecutive comparisons suffice -/

/-- **The consecutive-slope chain**: each face's slope is (cross-multiplied) strictly below
its successor's.  Finitely many LOCAL constraints — the atoms of §5's region. -/
def SlopeChain (s : List FaceShape) (num : Fin s.length → ℕ) : Prop :=
  ∀ i : ℕ, ∀ h : i + 1 < s.length,
    num ⟨i, Nat.lt_of_succ_lt h⟩ * (s.get ⟨i + 1, h⟩).1
      < num ⟨i + 1, h⟩ * (s.get ⟨i, Nat.lt_of_succ_lt h⟩).1

/-- Cross-multiplied fraction comparison is transitive over positive denominators —
the arithmetic core of the chain reduction. -/
private theorem cross_lt_trans {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (hb₁ : 1 ≤ b₁) (_hb₂ : 1 ≤ b₂)
    (hb₃ : 1 ≤ b₃) (h₁₂ : a₁ * b₂ < a₂ * b₁) (h₂₃ : a₂ * b₃ < a₃ * b₂) :
    a₁ * b₃ < a₃ * b₁ := by
  have key : a₁ * b₃ * b₂ < a₃ * b₁ * b₂ := by
    calc a₁ * b₃ * b₂ = a₁ * b₂ * b₃ := by ring
    _ < a₂ * b₁ * b₃ := by
        exact mul_lt_mul_of_pos_right h₁₂ (by omega)
    _ = a₂ * b₃ * b₁ := by ring
    _ < a₃ * b₂ * b₁ := by
        exact mul_lt_mul_of_pos_right h₂₃ (by omega)
    _ = a₃ * b₁ * b₂ := by ring
  exact lt_of_mul_lt_mul_right key (Nat.zero_le _)

/-- **The chain reduction**: over positive denominators, the full pairwise slope order is
equivalent to the consecutive chain — §5's region needs only `s.length − 1` inequality
atoms. -/
theorem slopesOrdered_iff_chain {s : List FaceShape} (hb : ∀ f ∈ s, 1 ≤ f.1)
    (num : Fin s.length → ℕ) : SlopesOrdered s num ↔ SlopeChain s num := by
  constructor
  · intro hord i h
    exact hord ⟨i, Nat.lt_of_succ_lt h⟩ ⟨i + 1, h⟩ (Nat.lt_succ_self i)
  · intro hchain i j hij
    have key : ∀ k, (i : ℕ) + 1 ≤ k → ∀ hk : k < s.length,
        num i * (s.get ⟨k, hk⟩).1 < num ⟨k, hk⟩ * (s.get i).1 := by
      intro k hk1
      induction k, hk1 using Nat.le_induction with
      | base =>
        intro hk
        exact hchain i.1 hk
      | succ k hk ih =>
        intro hkk
        have hk' : k < s.length := by omega
        have h1 := ih hk'
        have h2 := hchain k hkk
        have hb1 : 1 ≤ (s.get i).1 := hb _ (List.get_mem s i)
        have hb2 : 1 ≤ (s.get ⟨k, hk'⟩).1 := hb _ (List.get_mem s _)
        have hb3 : 1 ≤ (s.get ⟨k + 1, hkk⟩).1 := hb _ (List.get_mem s _)
        exact cross_lt_trans hb1 hb2 hb3 h1 h2
    exact key j.1 (by omega) j.isLt

/-! ## §3 — Gap coordinates: reconstruction and uniqueness (gate half 1) -/

/-- **The `i`-th slope gap**: `num(i+1)·b(i) − num(i)·b(i+1)`, the increment from the
`i`-th slope to the next in units of `1/(b(i)·b(i+1))`.  The §4.2 "gap variables". -/
def slopeGap (s : List FaceShape) (num : Fin s.length → ℕ) (i : Fin (s.length - 1)) : ℕ :=
  num ⟨i.1 + 1, by have := i.isLt; omega⟩ * (s.get ⟨i.1, by have := i.isLt; omega⟩).1
    - num ⟨i.1, by have := i.isLt; omega⟩ * (s.get ⟨i.1 + 1, by have := i.isLt; omega⟩).1

/-- The chain law in gap coordinates: slopes strictly increase iff every gap is `≥ 1`. -/
theorem one_le_slopeGap_iff_chain (s : List FaceShape) (num : Fin s.length → ℕ) :
    (∀ i, 1 ≤ slopeGap s num i) ↔ SlopeChain s num := by
  constructor
  · intro hg i h
    have hi : i < s.length - 1 := by omega
    have hgi := hg ⟨i, hi⟩
    have e : slopeGap s num ⟨i, hi⟩
        = num ⟨i + 1, h⟩ * (s.get ⟨i, Nat.lt_of_succ_lt h⟩).1
          - num ⟨i, Nat.lt_of_succ_lt h⟩ * (s.get ⟨i + 1, h⟩).1 := rfl
    rw [e] at hgi
    omega
  · intro hc i
    have h : i.1 + 1 < s.length := by have := i.isLt; omega
    have hci := hc i.1 h
    have e : slopeGap s num i
        = num ⟨i.1 + 1, h⟩ * (s.get ⟨i.1, Nat.lt_of_succ_lt h⟩).1
          - num ⟨i.1, Nat.lt_of_succ_lt h⟩ * (s.get ⟨i.1 + 1, h⟩).1 := rfl
    rw [e]
    omega

/-- **Exactness of the gap identity** under the chain law: the truncated subtraction in
`slopeGap` is exact, so the gap is an honest coordinate. -/
theorem slopeGap_recon {s : List FaceShape} {num : Fin s.length → ℕ}
    (hc : SlopeChain s num) {k : ℕ} (hk : k + 1 < s.length) (hkm : k < s.length - 1) :
    num ⟨k + 1, hk⟩ * (s.get ⟨k, Nat.lt_of_succ_lt hk⟩).1
      = num ⟨k, Nat.lt_of_succ_lt hk⟩ * (s.get ⟨k + 1, hk⟩).1
        + slopeGap s num ⟨k, hkm⟩ := by
  have hck := hc k hk
  have e : slopeGap s num ⟨k, hkm⟩
      = num ⟨k + 1, hk⟩ * (s.get ⟨k, Nat.lt_of_succ_lt hk⟩).1
        - num ⟨k, Nat.lt_of_succ_lt hk⟩ * (s.get ⟨k + 1, hk⟩).1 := rfl
  rw [e]
  omega

/-- **Gap reconstruction/uniqueness (THE gate, half 1)**: the first numerator and the gap
tuple determine ALL numerators — two chain-ordered parameter tuples with equal first
numerator and equal gaps are equal.  (The recursion `num(i+1) = (num(i)·b(i+1) + gap(i))/b(i)`
inverts the gap map; realizability of a prescribed gap tuple is the congruence-chain
content of §5's `mod` atoms.) -/
theorem num_eq_of_slopeGap_eq {s : List FaceShape} {num num' : Fin s.length → ℕ}
    (hb : ∀ f ∈ s, 1 ≤ f.1) (hc : SlopeChain s num) (hc' : SlopeChain s num')
    (hfirst : ∀ h : 0 < s.length, num ⟨0, h⟩ = num' ⟨0, h⟩)
    (hgap : ∀ i, slopeGap s num i = slopeGap s num' i) : num = num' := by
  funext i
  suffices H : ∀ k (hk : k < s.length), num ⟨k, hk⟩ = num' ⟨k, hk⟩ from H i.1 i.isLt
  intro k
  induction k with
  | zero => intro hk; exact hfirst hk
  | succ k ih =>
    intro hk
    have hk' : k < s.length := by omega
    have hkm : k < s.length - 1 := by omega
    have h1 := slopeGap_recon hc hk hkm
    have h2 := slopeGap_recon hc' hk hkm
    have hnum : num ⟨k, Nat.lt_of_succ_lt hk⟩ = num' ⟨k, Nat.lt_of_succ_lt hk⟩ := ih hk'
    have hg := hgap ⟨k, hkm⟩
    rw [hnum, hg] at h1
    have heq : num ⟨k + 1, hk⟩ * (s.get ⟨k, Nat.lt_of_succ_lt hk⟩).1
        = num' ⟨k + 1, hk⟩ * (s.get ⟨k, Nat.lt_of_succ_lt hk⟩).1 := by
      rw [h1, h2]
    have hbk : 1 ≤ (s.get ⟨k, Nat.lt_of_succ_lt hk⟩).1 := hb _ (List.get_mem s _)
    exact Nat.eq_of_mul_eq_mul_right (by omega) heq

/-! ## §4 — Polygon reconstruction: the vertices in ℕ (gate half 2) -/

/-- The `j`-th face length, totalized (`0` past the end). -/
def lenAt (s : List FaceShape) (j : ℕ) : ℕ :=
  if h : j < s.length then faceLen (s.get ⟨j, h⟩) else 0

/-- The `j`-th face's total height drop `num j · d j` — slope `h/b` × length `b·d` = `h·d`,
an INTEGER (the polygon needs no rationals), totalized. -/
def dropAt (s : List FaceShape) (num : Fin s.length → ℕ) (j : ℕ) : ℕ :=
  if h : j < s.length then num ⟨j, h⟩ * faceResDeg (s.get ⟨j, h⟩) else 0

/-- **The `i`-th vertex abscissa**: the sum of the first `i` face lengths. -/
def vertexX (s : List FaceShape) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, lenAt s j

/-- **The `i`-th vertex height** (normalized so the LAST vertex has height `0`): the sum of
the drops of faces `i, i+1, …` — the polygon descends to the right endpoint. -/
def vertexY (s : List FaceShape) (num : Fin s.length → ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico i s.length, dropAt s num j

@[simp] theorem vertexX_zero (s : List FaceShape) : vertexX s 0 = 0 := by
  simp [vertexX]

theorem vertexX_succ {s : List FaceShape} {i : ℕ} (h : i < s.length) :
    vertexX s (i + 1) = vertexX s i + faceLen (s.get ⟨i, h⟩) := by
  rw [vertexX, vertexX, Finset.sum_range_succ]
  congr 1
  simp [lenAt, h]

/-- The polygon spans the full window: the last abscissa is the cluster mass `m` exactly
(IFCG5's D5 mass law, transported). -/
theorem vertexX_length {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s) :
    vertexX s s.length = m := by
  rw [vertexX, ← Fin.sum_univ_eq_sum_range]
  have h2 : ∑ i : Fin s.length, lenAt s i.1 = ∑ i : Fin s.length, faceLen (s.get i) :=
    Finset.sum_congr rfl (fun i _ => dif_pos i.isLt)
  have h4 : List.ofFn (fun i => faceLen (s.get i)) = s.map faceLen := by
    conv_rhs => rw [← List.ofFn_get s]
    rw [List.map_ofFn]
    rfl
  rw [h2, ← List.sum_ofFn, h4]
  exact hs.2

/-- Vertices advance strictly: consecutive abscissae differ by a positive face length. -/
theorem vertexX_lt_succ {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {i : ℕ} (h : i < s.length) : vertexX s i < vertexX s (i + 1) := by
  rw [vertexX_succ h]
  have := faceLen_pos (hs.1 _ (List.get_mem s ⟨i, h⟩))
  omega

@[simp] theorem vertexY_length (s : List FaceShape) (num : Fin s.length → ℕ) :
    vertexY s num s.length = 0 := by
  simp [vertexY]

theorem vertexY_succ {s : List FaceShape} {i : ℕ} (h : i < s.length)
    (num : Fin s.length → ℕ) :
    vertexY s num i = num ⟨i, h⟩ * faceResDeg (s.get ⟨i, h⟩) + vertexY s num (i + 1) := by
  have e : dropAt s num i = num ⟨i, h⟩ * faceResDeg (s.get ⟨i, h⟩) := dif_pos h
  rw [vertexY, Finset.sum_eq_sum_Ico_succ_bot h, e, vertexY]

/-- Reconstruction: a face length is the abscissa difference of its two vertices. -/
theorem faceLen_eq_vertexX_sub {s : List FaceShape} {i : ℕ} (h : i < s.length) :
    faceLen (s.get ⟨i, h⟩) = vertexX s (i + 1) - vertexX s i := by
  have := vertexX_succ h
  omega

/-- Reconstruction: a face's height drop is the height difference of its two vertices. -/
theorem drop_eq_vertexY_sub {s : List FaceShape} {i : ℕ} (h : i < s.length)
    (num : Fin s.length → ℕ) :
    num ⟨i, h⟩ * faceResDeg (s.get ⟨i, h⟩) = vertexY s num i - vertexY s num (i + 1) := by
  have := vertexY_succ h num
  omega

/-- **Polygon uniqueness (THE gate, half 2)**: the vertex heights determine the parameters —
two parameter tuples tracing the same polygon over the same valid skeleton are equal. -/
theorem num_eq_of_vertexY_eq {s : List FaceShape} {num num' : Fin s.length → ℕ}
    (hs : ∀ f ∈ s, ValidFace f)
    (h : ∀ i, vertexY s num i = vertexY s num' i) : num = num' := by
  funext i
  have h1 := vertexY_succ i.isLt num
  have h2 := vertexY_succ i.isLt num'
  have h3 := h i.1
  have h4 := h (i.1 + 1)
  have hd : 1 ≤ faceResDeg (s.get ⟨i.1, i.isLt⟩) := (hs _ (List.get_mem s _)).2.1
  have hAA : num ⟨i.1, i.isLt⟩ * faceResDeg (s.get ⟨i.1, i.isLt⟩)
      = num' ⟨i.1, i.isLt⟩ * faceResDeg (s.get ⟨i.1, i.isLt⟩) := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) hAA

/-! ## §5 — The Presburger region

The `constraints : PresburgerRegion r` field of §4.2's `ClusterGenre` sketch: a
quantifier-free Presburger formula grammar over `Fin r → ℕ` (linear inequalities and
linear congruences, closed under ∧/∨), with decidable satisfaction, and THE region whose
points are exactly a skeleton's valid parameter tuples. -/

/-- A Presburger atom over `r` variables: a linear inequality
`Σ aⱼxⱼ + c ≤ Σ bⱼxⱼ + d` or a linear congruence `Σ aⱼxⱼ ≡ c [MOD n]`. -/
inductive PresAtom (r : ℕ) : Type
  | le (a : Fin r → ℕ) (c : ℕ) (b : Fin r → ℕ) (d : ℕ) : PresAtom r
  | mod (a : Fin r → ℕ) (c n : ℕ) : PresAtom r

/-- Atom satisfaction. -/
def PresAtom.Holds {r : ℕ} (x : Fin r → ℕ) : PresAtom r → Prop
  | .le a c b d => (∑ j, a j * x j) + c ≤ (∑ j, b j * x j) + d
  | .mod a c n => (∑ j, a j * x j) ≡ c [MOD n]

instance PresAtom.decHolds {r : ℕ} (x : Fin r → ℕ) (A : PresAtom r) :
    Decidable (A.Holds x) := by
  cases A with
  | le a c b d => exact inferInstanceAs (Decidable (_ ≤ _))
  | mod a c n => exact inferInstanceAs (Decidable (_ % _ = _ % _))

/-- A (quantifier-free) Presburger region over `r` variables: atoms closed under
conjunction and disjunction, with explicit top/bottom for the finite folds. -/
inductive PresburgerRegion (r : ℕ) : Type
  | atom (A : PresAtom r) : PresburgerRegion r
  | tru : PresburgerRegion r
  | fls : PresburgerRegion r
  | and (P Q : PresburgerRegion r) : PresburgerRegion r
  | or (P Q : PresburgerRegion r) : PresburgerRegion r

/-- Region membership. -/
def PresburgerRegion.Holds {r : ℕ} : PresburgerRegion r → (Fin r → ℕ) → Prop
  | .atom A, x => A.Holds x
  | .tru, _ => True
  | .fls, _ => False
  | .and P Q, x => P.Holds x ∧ Q.Holds x
  | .or P Q, x => P.Holds x ∨ Q.Holds x

instance PresburgerRegion.decHolds {r : ℕ} :
    (P : PresburgerRegion r) → (x : Fin r → ℕ) → Decidable (P.Holds x)
  | .atom A, x => PresAtom.decHolds x A
  | .tru, _ => .isTrue trivial
  | .fls, _ => .isFalse (fun h => h)
  | .and P Q, x => @instDecidableAnd _ _ (PresburgerRegion.decHolds P x)
      (PresburgerRegion.decHolds Q x)
  | .or P Q, x => @instDecidableOr _ _ (PresburgerRegion.decHolds P x)
      (PresburgerRegion.decHolds Q x)

/-- Finite conjunction. -/
def PresburgerRegion.bigAnd {r : ℕ} (l : List (PresburgerRegion r)) : PresburgerRegion r :=
  l.foldr .and .tru

/-- Finite disjunction. -/
def PresburgerRegion.bigOr {r : ℕ} (l : List (PresburgerRegion r)) : PresburgerRegion r :=
  l.foldr .or .fls

theorem PresburgerRegion.holds_bigAnd {r : ℕ} {l : List (PresburgerRegion r)}
    {x : Fin r → ℕ} : (PresburgerRegion.bigAnd l).Holds x ↔ ∀ P ∈ l, P.Holds x := by
  induction l with
  | nil => simp [PresburgerRegion.bigAnd, PresburgerRegion.Holds]
  | cons P t ih =>
    simp only [PresburgerRegion.bigAnd, List.foldr_cons] at ih ⊢
    rw [show (PresburgerRegion.Holds (.and P (t.foldr .and .tru)) x)
        = (P.Holds x ∧ (t.foldr PresburgerRegion.and .tru).Holds x) from rfl, ih]
    simp

theorem PresburgerRegion.holds_bigOr {r : ℕ} {l : List (PresburgerRegion r)}
    {x : Fin r → ℕ} : (PresburgerRegion.bigOr l).Holds x ↔ ∃ P ∈ l, P.Holds x := by
  induction l with
  | nil => simp [PresburgerRegion.bigOr, PresburgerRegion.Holds]
  | cons P t ih =>
    simp only [PresburgerRegion.bigOr, List.foldr_cons] at ih ⊢
    rw [show (PresburgerRegion.Holds (.or P (t.foldr .or .fls)) x)
        = (P.Holds x ∨ (t.foldr PresburgerRegion.or .fls).Holds x) from rfl, ih]
    simp

/-- The coordinate vector supported at `i` with value `c`. -/
def single {r : ℕ} (i : Fin r) (c : ℕ) : Fin r → ℕ := fun j => if j = i then c else 0

theorem sum_single_mul {r : ℕ} (i : Fin r) (c : ℕ) (x : Fin r → ℕ) :
    ∑ j, single i c j * x j = c * x i := by
  have e : ∀ j, single i c j * x j = if j = i then c * x j else 0 := by
    intro j
    by_cases hj : j = i <;> simp [single, hj]
  rw [Finset.sum_congr rfl (fun j _ => e j),
    Finset.sum_ite_eq' Finset.univ i (fun j => c * x j)]
  simp

/-- **Coprimality is Presburger**: `gcd(xᵢ, b) = 1` as the disjunction, over the units `u`
mod `b`, of the congruences `xᵢ ≡ u [MOD b]`. -/
def coprimeRegion {r : ℕ} (i : Fin r) (b : ℕ) : PresburgerRegion r :=
  .bigOr (((List.range b).filter (fun u => Nat.gcd u b = 1)).map
    (fun u => .atom (.mod (single i 1) u b)))

theorem holds_coprimeRegion_iff {r : ℕ} {b : ℕ} (hb : 1 ≤ b) (i : Fin r)
    (x : Fin r → ℕ) : (coprimeRegion i b).Holds x ↔ Nat.Coprime (x i) b := by
  rw [coprimeRegion, PresburgerRegion.holds_bigOr]
  constructor
  · rintro ⟨P, hP, hPx⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hP
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hu
    obtain ⟨hurange, hugcd⟩ := hu
    have hmod : x i ≡ u [MOD b] := by
      have h0 : (∑ j, single i 1 j * x j) ≡ u [MOD b] := hPx
      rwa [sum_single_mul, one_mul] at h0
    have hxu : x i % b = u % b := hmod
    have huu : u % b = u := Nat.mod_eq_of_lt hurange
    have hgcd : Nat.gcd b (x i) = Nat.gcd b u := by
      rw [Nat.gcd_rec b (x i), Nat.gcd_rec b u, hxu, huu]
    unfold Nat.Coprime
    rw [Nat.gcd_comm, hgcd, Nat.gcd_comm]
    exact hugcd
  · intro hcop
    refine ⟨.atom (.mod (single i 1) (x i % b) b), ?_, ?_⟩
    · apply List.mem_map.2
      refine ⟨x i % b, ?_, rfl⟩
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨Nat.mod_lt _ (by omega), ?_⟩
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact hcop
    · show (∑ j, single i 1 j * x j) ≡ (x i % b) [MOD b]
      rw [sum_single_mul, one_mul]
      exact (Nat.mod_mod_of_dvd (x i) dvd_rfl).symm

/-- **THE region of a skeleton**: positivity atoms (one per face) + consecutive chain
atoms (one per adjacent pair, §2's reduction) + coprimality regions (one per face). -/
def slopeRegion (s : List FaceShape) : PresburgerRegion s.length :=
  .bigAnd (
    ((List.finRange s.length).map (fun i =>
      .atom (.le (fun _ => 0) 1 (single i 1) 0)))
    ++ ((List.finRange (s.length - 1)).map (fun i =>
      .atom (.le
        (single ⟨i.1, by have := i.isLt; omega⟩
          ((s.get ⟨i.1 + 1, by have := i.isLt; omega⟩).1)) 1
        (single ⟨i.1 + 1, by have := i.isLt; omega⟩
          ((s.get ⟨i.1, by have := i.isLt; omega⟩).1)) 0)))
    ++ ((List.finRange s.length).map (fun i => coprimeRegion i (s.get i).1)))

/-- ★ **THE PRESBURGER GATE**: over positive denominators, a skeleton's valid parameter
tuples are EXACTLY the points of its constructed region — §4.2's
`constraints : PresburgerRegion r`, proved rather than postulated. -/
theorem holds_slopeRegion_iff {s : List FaceShape} (hb : ∀ f ∈ s, 1 ≤ f.1)
    (num : Fin s.length → ℕ) :
    (slopeRegion s).Holds num ↔ ValidSlopeParams s num := by
  rw [slopeRegion, PresburgerRegion.holds_bigAnd]
  constructor
  · intro hall
    have hpos : ∀ i : Fin s.length, 1 ≤ num i := by
      intro i
      have hP := hall _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem (List.mem_finRange i))))
      have hP' : (∑ j, (fun _ : Fin s.length => 0) j * num j) + 1
          ≤ (∑ j, single i 1 j * num j) + 0 := hP
      rw [sum_single_mul, one_mul] at hP'
      simpa using hP'
    have hcop : ∀ i : Fin s.length, Nat.Coprime (num i) (s.get i).1 := by
      intro i
      have hP := hall _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_finRange i)))
      exact (holds_coprimeRegion_iff (hb _ (List.get_mem s i)) i num).1 hP
    have hchain : SlopeChain s num := by
      intro i h
      have hi : i < s.length - 1 := by omega
      have hP := hall _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_finRange (⟨i, hi⟩ : Fin (s.length - 1))))))
      have hP' : (∑ j, single (⟨i, Nat.lt_of_succ_lt h⟩ : Fin s.length)
            ((s.get ⟨i + 1, h⟩).1) j * num j) + 1
          ≤ (∑ j, single (⟨i + 1, h⟩ : Fin s.length)
            ((s.get ⟨i, Nat.lt_of_succ_lt h⟩).1) j * num j) + 0 := hP
      rw [sum_single_mul, sum_single_mul] at hP'
      rw [Nat.mul_comm ((s.get ⟨i + 1, h⟩).1), Nat.mul_comm ((s.get ⟨i, Nat.lt_of_succ_lt h⟩).1)] at hP'
      omega
    exact ⟨fun i => ⟨hpos i, hcop i⟩, (slopesOrdered_iff_chain hb num).2 hchain⟩
  · intro hv
    have hchain : SlopeChain s num := (slopesOrdered_iff_chain hb num).1 hv.2
    intro P hP
    rcases List.mem_append.1 hP with hAB | hC
    · rcases List.mem_append.1 hAB with hA | hB
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hA
        show (∑ j, (fun _ : Fin s.length => 0) j * num j) + 1
            ≤ (∑ j, single i 1 j * num j) + 0
        rw [sum_single_mul, one_mul]
        have := (hv.1 i).1
        simp only [zero_mul, Finset.sum_const_zero]
        omega
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hB
        have h : i.1 + 1 < s.length := by have := i.isLt; omega
        have hci := hchain i.1 h
        show (∑ j, single (⟨i.1, Nat.lt_of_succ_lt h⟩ : Fin s.length)
              ((s.get ⟨i.1 + 1, h⟩).1) j * num j) + 1
            ≤ (∑ j, single (⟨i.1 + 1, h⟩ : Fin s.length)
              ((s.get ⟨i.1, Nat.lt_of_succ_lt h⟩).1) j * num j) + 0
        rw [sum_single_mul, sum_single_mul]
        rw [Nat.mul_comm ((s.get ⟨i.1 + 1, h⟩).1), Nat.mul_comm ((s.get ⟨i.1, Nat.lt_of_succ_lt h⟩).1)]
        omega
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
      exact (holds_coprimeRegion_iff (hb _ (List.get_mem s i)) i num).2 (hv.1 i).2

/-- The gate at IFCG5's skeleton carrier (face validity supplies denominator positivity). -/
theorem holds_slopeRegion_iff_skeleton {m : ℕ} (S : ClusterSkeleton m)
    (num : Fin S.1.length → ℕ) :
    (slopeRegion S.1).Holds num ↔ ValidSlopeParams S.1 num :=
  holds_slopeRegion_iff (fun f hf => (S.valid.1 f hf).1) num

/-- Parameter validity is DECIDABLE (via the region). -/
def decValidSlopeParams {s : List FaceShape} (hb : ∀ f ∈ s, 1 ≤ f.1)
    (num : Fin s.length → ℕ) : Decidable (ValidSlopeParams s num) :=
  decidable_of_iff _ (holds_slopeRegion_iff hb num)

/-! ## §6 — Realization uniqueness: dv-purity pins the parameters (the GC2 feed) -/

section DvBinding

open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The endpoint equation of two on-side abscissae, in ℕ.  Re-derived from C.08's private
`dvOnSide_nat_eq` (same mechanism; private there, hence unreachable; C.08 not edited). -/
private theorem dvOnSide_nat_eq' {F : KeyFrame O π} {u ℓ : ℕ} {g : Polynomial O}
    {j j' H H' : ℕ} (hH : dvHgt F g j = (H : ℕ∞)) (hH' : dvHgt F g j' = (H' : ℕ∞))
    (hj : DvOnSide F g u ℓ j) (hj' : DvOnSide F g u ℓ j') :
    ℓ * H + u * j = ℓ * H' + u * j' := by
  have e : ℓ • (H : ℕ∞) + (u * j : ℕ∞) = ℓ • (H' : ℕ∞) + (u * j' : ℕ∞) := by
    rw [← hH, ← hH', ← hj.1, hj'.1]
  have e' : ((ℓ * H + u * j : ℕ) : ℕ∞) = ((ℓ * H' + u * j' : ℕ) : ℕ∞) := by
    push_cast
    simpa [nsmul_eq_mul] using e
  exact_mod_cast e'

/-- ★ **dv-purity pins the reduced slope** (the uniqueness engine of this node): a
polynomial with a positive key-degree window is dv-pure in at most one reduced direction.
Both purity certificates place the abscissae `0` and `N = deg g / D′` on their sides; the
two endpoint equations force `ℓ′·u = ℓ·u′`, and reduced-fraction arithmetic finishes. -/
theorem isDvPure_slope_unique {F : KeyFrame O π} {g : Polynomial O} {u ℓ u' ℓ' : ℕ}
    (hu : 1 ≤ u) (hu' : 1 ≤ u') (hcop : Nat.Coprime u ℓ) (hcop' : Nat.Coprime u' ℓ')
    (hN : 1 ≤ g.natDegree / (F.e₁ * F.f₁))
    (h1 : IsDvPure F g u ℓ) (h2 : IsDvPure F g u' ℓ') : u = u' ∧ ℓ = ℓ' := by
  set N := g.natDegree / (F.e₁ * F.f₁) with hNdef
  have hj0 : DvOnSide F g u ℓ 0 := dvOnSide_of_mem_dvSideSet h1.1
  have hjN : DvOnSide F g u ℓ N := dvOnSide_of_mem_dvSideSet h1.2
  have hj0' : DvOnSide F g u' ℓ' 0 := dvOnSide_of_mem_dvSideSet h2.1
  have hjN' : DvOnSide F g u' ℓ' N := dvOnSide_of_mem_dvSideSet h2.2
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hj0.2
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hjN.2
  have e1 : ℓ * a + u * 0 = ℓ * c + u * N := dvOnSide_nat_eq' ha.symm hc.symm hj0 hjN
  have e2 : ℓ' * a + u' * 0 = ℓ' * c + u' * N := dvOnSide_nat_eq' ha.symm hc.symm hj0' hjN'
  have key : ℓ' * u = ℓ * u' := by
    have e1' : ℓ * a = ℓ * c + u * N := by omega
    have e2' : ℓ' * a = ℓ' * c + u' * N := by omega
    have f1 : ℓ' * (ℓ * a) = ℓ' * (ℓ * c) + ℓ' * (u * N) := by rw [e1']; ring
    have f2 : ℓ * (ℓ' * a) = ℓ * (ℓ' * c) + ℓ * (u' * N) := by rw [e2']; ring
    have g1 : ℓ' * (ℓ * a) = ℓ * (ℓ' * a) := by ring
    have g2 : ℓ' * (ℓ * c) = ℓ * (ℓ' * c) := by ring
    have g3 : ℓ' * (u * N) = ℓ * (u' * N) := by omega
    have g4 : (ℓ' * u) * N = (ℓ * u') * N := by
      rw [show (ℓ' * u) * N = ℓ' * (u * N) from by ring,
        show (ℓ * u') * N = ℓ * (u' * N) from by ring]
      exact g3
    exact Nat.eq_of_mul_eq_mul_right (by omega) g4
  have huu' : u = u' := by
    have hd1 : u ∣ ℓ * u' := ⟨ℓ', by rw [← key]; ring⟩
    have hd2 : u' ∣ ℓ' * u := ⟨ℓ, by rw [key]; ring⟩
    exact Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_left hd1) (hcop'.dvd_of_dvd_mul_left hd2)
  refine ⟨huu', ?_⟩
  subst huu'
  have key' : u * ℓ' = u * ℓ := by
    rw [Nat.mul_comm u ℓ', Nat.mul_comm u ℓ]
    exact key
  exact Nat.eq_of_mul_eq_mul_left hu key'.symm

/-- **Reconstruction at the block**: a realized face's length is READ OFF the block — the
key-degree window `deg g / D′` IS `faceLen f` (C.35's endpoint calculus + the realization's
length clause). -/
theorem natDegree_div_eq_faceLen_of_realizes {F : KeyFrame O π} {g : Polynomial O}
    {h : ℕ} {f : FaceShape} (hr : RealizesFaceAt F g h f) :
    g.natDegree / (F.e₁ * F.f₁) = faceLen f := by
  obtain ⟨hh, hcop, hpure, hlen⟩ := hr
  have hmax : dvSideMax F g h f.1 ⟨0, hpure.1⟩ = g.natDegree / (F.e₁ * F.f₁) :=
    dvSideMax_eq_of_isDvPure hpure _
  have hmin : dvSideMin F g h f.1 ⟨0, hpure.1⟩ = 0 :=
    Tower.dvSideMin_eq_zero_of_isDvPure hpure _
  unfold dvSideLen at hlen
  omega

/-- ★ **Face-parameter uniqueness (A0G-GC2's parameter-level half, per the A0G7 verdict)**:
one block realizes at most one numerator, denominator, face length, and residual degree.
(The residual PATTERN is the residual-level half — IFCG6's `face_split_unique`.) -/
theorem realizesFaceAt_param_unique {F : KeyFrame O π} {g : Polynomial O}
    {u u' : ℕ} {f f' : FaceShape} (hf : ValidFace f)
    (hr : RealizesFaceAt F g u f) (hr' : RealizesFaceAt F g u' f') :
    u = u' ∧ f.1 = f'.1 ∧ faceLen f = faceLen f' ∧ faceResDeg f = faceResDeg f' := by
  have hNf := natDegree_div_eq_faceLen_of_realizes hr
  have hNf' := natDegree_div_eq_faceLen_of_realizes hr'
  have hN : 1 ≤ g.natDegree / (F.e₁ * F.f₁) := by
    rw [hNf]
    exact faceLen_pos hf
  obtain ⟨hh, hcop, hpure, hlen⟩ := hr
  obtain ⟨hh', hcop', hpure', hlen'⟩ := hr'
  obtain ⟨huu, hbb⟩ := isDvPure_slope_unique hh hh' hcop hcop' hN hpure hpure'
  have hlen2 : faceLen f = faceLen f' := by rw [← hNf, ← hNf']
  refine ⟨huu, hbb, hlen2, ?_⟩
  have h1 : f.1 * faceResDeg f = f.1 * faceResDeg f' := by
    have h0 : f.1 * faceResDeg f = f'.1 * faceResDeg f' := hlen2
    rw [← hbb] at h0
    exact h0
  exact Nat.eq_of_mul_eq_mul_left (by have := hf.1; omega) h1

/-- A skeleton realization's parameters are valid slope parameters — the §1 carrier is
canonical (it is exactly what a realization carries). -/
theorem validSlopeParams_of_realizes {F : KeyFrame O π} {m : ℕ} {S : ClusterSkeleton m}
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    (hr : RealizesSkeletonAt F S num blocks) : ValidSlopeParams S.1 num :=
  ⟨fun i => ⟨(hr.2 i).1, (hr.2 i).2.1⟩, hr.1⟩

/-- Every realized parameter tuple lies in the skeleton's Presburger region. -/
theorem holds_slopeRegion_of_realizes {F : KeyFrame O π} {m : ℕ} {S : ClusterSkeleton m}
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    (hr : RealizesSkeletonAt F S num blocks) : (slopeRegion S.1).Holds num :=
  (holds_slopeRegion_iff_skeleton S num).2 (validSlopeParams_of_realizes hr)

/-- ★ **Skeleton-parameter uniqueness**: two skeleton realizations by the SAME blocks carry
equal numerators, denominators, face lengths, and residual degrees, face by face. -/
theorem realizesSkeletonAt_params_unique {F : KeyFrame O π} {m m' : ℕ}
    {S : ClusterSkeleton m} {S' : ClusterSkeleton m'} (hlen : S.1.length = S'.1.length)
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    {num' : Fin S'.1.length → ℕ} {blocks' : Fin S'.1.length → Polynomial O}
    (h1 : RealizesSkeletonAt F S num blocks) (h2 : RealizesSkeletonAt F S' num' blocks')
    (hbk : ∀ i : Fin S.1.length, blocks i = blocks' (Fin.cast hlen i)) :
    ∀ i : Fin S.1.length,
      num i = num' (Fin.cast hlen i)
      ∧ (S.1.get i).1 = (S'.1.get (Fin.cast hlen i)).1
      ∧ faceLen (S.1.get i) = faceLen (S'.1.get (Fin.cast hlen i))
      ∧ faceResDeg (S.1.get i) = faceResDeg (S'.1.get (Fin.cast hlen i)) := by
  intro i
  have hf : ValidFace (S.1.get i) := S.valid.1 _ (List.get_mem S.1 i)
  have hr : RealizesFaceAt F (blocks i) (num i) (S.1.get i) := h1.2 i
  have hr' : RealizesFaceAt F (blocks i) (num' (Fin.cast hlen i))
      (S'.1.get (Fin.cast hlen i)) := by
    rw [hbk i]
    exact h2.2 (Fin.cast hlen i)
  exact realizesFaceAt_param_unique hf hr hr'

/-- **Mass rigidity**: two skeletons realized by the same blocks have the same mass. -/
theorem mass_eq_of_realizes_same_blocks {F : KeyFrame O π} {m m' : ℕ}
    {S : ClusterSkeleton m} {S' : ClusterSkeleton m'} (hlen : S.1.length = S'.1.length)
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    {num' : Fin S'.1.length → ℕ} {blocks' : Fin S'.1.length → Polynomial O}
    (h1 : RealizesSkeletonAt F S num blocks) (h2 : RealizesSkeletonAt F S' num' blocks')
    (hbk : ∀ i : Fin S.1.length, blocks i = blocks' (Fin.cast hlen i)) : m = m' := by
  have hmap : S.1.map faceLen = S'.1.map faceLen := by
    apply List.ext_get
    · simp [hlen]
    · intro n h1n h2n
      have h1n' : n < S.1.length := by simpa using h1n
      have hface := (realizesSkeletonAt_params_unique hlen h1 h2 hbk ⟨n, h1n'⟩).2.2.1
      simpa using hface
  calc m = (S.1.map faceLen).sum := S.valid.2.symm
  _ = (S'.1.map faceLen).sum := by rw [hmap]
  _ = m' := S'.valid.2

end DvBinding

end Uniformity.Density.IFCG7

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG7.slopesOrdered_iff_chain
#print axioms Uniformity.Density.IFCG7.one_le_slopeGap_iff_chain
#print axioms Uniformity.Density.IFCG7.slopeGap_recon
#print axioms Uniformity.Density.IFCG7.num_eq_of_slopeGap_eq
#print axioms Uniformity.Density.IFCG7.vertexX_succ
#print axioms Uniformity.Density.IFCG7.vertexX_length
#print axioms Uniformity.Density.IFCG7.vertexX_lt_succ
#print axioms Uniformity.Density.IFCG7.vertexY_succ
#print axioms Uniformity.Density.IFCG7.faceLen_eq_vertexX_sub
#print axioms Uniformity.Density.IFCG7.drop_eq_vertexY_sub
#print axioms Uniformity.Density.IFCG7.num_eq_of_vertexY_eq
#print axioms Uniformity.Density.IFCG7.PresburgerRegion.holds_bigAnd
#print axioms Uniformity.Density.IFCG7.PresburgerRegion.holds_bigOr
#print axioms Uniformity.Density.IFCG7.sum_single_mul
#print axioms Uniformity.Density.IFCG7.holds_coprimeRegion_iff
#print axioms Uniformity.Density.IFCG7.holds_slopeRegion_iff
#print axioms Uniformity.Density.IFCG7.holds_slopeRegion_iff_skeleton
#print axioms Uniformity.Density.IFCG7.decValidSlopeParams
#print axioms Uniformity.Density.IFCG7.isDvPure_slope_unique
#print axioms Uniformity.Density.IFCG7.natDegree_div_eq_faceLen_of_realizes
#print axioms Uniformity.Density.IFCG7.realizesFaceAt_param_unique
#print axioms Uniformity.Density.IFCG7.validSlopeParams_of_realizes
#print axioms Uniformity.Density.IFCG7.holds_slopeRegion_of_realizes
#print axioms Uniformity.Density.IFCG7.realizesSkeletonAt_params_unique
#print axioms Uniformity.Density.IFCG7.mass_eq_of_realizes_same_blocks
