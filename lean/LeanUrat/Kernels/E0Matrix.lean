/-
Kernels/E0Matrix — BP4-c4 E-phase skeletons for the abstract E0 matrix layer:
units KA1, KA2a, KA2b, KA2c, KA3, KA5 (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2,
§3.A ROUTE 1 legs (1a)-(1c) + §4 KA; adjudications per
BRIDGE_ADJUDICATIONS_2026-07-30.md BP4: Q1 Kernels/ mini-corpus ratified,
lakefile/AxChk sweep entry is the ORCHESTRATOR's duty, not this file's).

This file carries the §2.3 named Props (`SubStochastic`, `RowSumLt`,
`NoClosedClass`) and ROUTE 1's escape theorems.  Everything is ABSTRACT (any
finite index type, ℚ entries); the window/table seams (KA6a/KA6b2/KA8) and
pool instances are sibling units.  Consumed vocabulary: `MovesS.EscapeE0`
(MovesS/Defs.lean:524 — nonneg entries + A^k𝟙 → 0).

GATE SEQUENCING (REV 2, F5): KA2c's CM-first twin KA2d is ALREADY ON RECORD
(Kernels/KA2d.lean, BP4-c2): its two witnesses seal that BOTH KA2c hypotheses
(substochasticity, reachability) are needed.  No import needed — the gate is
a scheduling constraint, not a logical dep; per KA2d's own file note, its raw
row-sum/entry forms instantiate this file's named Props definitionally.

RECORDED RESOLUTIONS (statement transcription against the blueprint):
· `RowSumLt` is the PER-STATE STRICT form ∀ i, ∑ j, A i j < 1 (§3.A (1d)
  "row sum < 1" = KA5's hypothesis).  KA1's uniform-κ hypothesis stays RAW
  (∀ i, ∑ j, A i j ≤ κ) exactly as the §4 KA1 sketch displays it.
· `NoClosedClass` is KA2b's hypothesis shape: every state reaches a
  strict-deficit row along a positive-entry path of length ≤ m :=
  Fintype.card ι (the blueprint's "from every state a path to a row-deficit
  state" with KA2b's ≤ m bound built in; path length 0 = the state itself is
  deficit — this covers A = 0, per REV 2 F6).
· KA3's bundled hypothesis "∀ i ∈ C, ∑_{j∈C} A i j = 1 ∧ ∀ j ∉ C, A i j = 0"
  is curried into two hypotheses (same statement, cleaner consumption).

Build: cd lean && lake build LeanUrat.Kernels.E0Matrix
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowEntryNonneg

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.show false

namespace LeanUrat.Kernels

open Matrix

/- `[DecidableEq ι]` is required only where matrix `1`/`^` (hence
`MovesS.EscapeE0`) appears; the summation-level vocabulary and the
`mulVec` toolkit stay decidability-free — it is bound per declaration
below, not file-wide. -/
variable {ι : Type*} [Fintype ι]

/-! ## The §2.3 named Props (the abstract E0 vocabulary) -/

/-- Substochastic (§2.3 named Prop): every row sums to at most 1. -/
def SubStochastic (A : Matrix ι ι ℚ) : Prop := ∀ i, ∑ j, A i j ≤ 1

/-- Per-state strict exit positivity (§2.3 named Prop `RowSumLt`, resolved to
the §3.A (1d) per-state strict form "row sum < 1" — KA5's hypothesis): every
row sums to strictly less than 1. -/
def RowSumLt (A : Matrix ι ι ℚ) : Prop := ∀ i, ∑ j, A i j < 1

/-- Row `i` is a STRICT-DEFICIT row: its one-step mass ∑ⱼ A i j is < 1 (the
deficit 1 − ∑ⱼ A i j > 0 is the exit mass KA2b's ε harvests). -/
def RowDeficit (A : Matrix ι ι ℚ) (i : ι) : Prop := ∑ j, A i j < 1

/-- State `i` reaches a strict-deficit row within `m` steps: a path
i = path 0 → path 1 → … → path ℓ (ℓ ≤ m) whose consecutive entries are all
POSITIVE and whose endpoint is a strict-deficit row.  Path length ℓ = 0 (the
state itself deficient) is allowed — the empty product = 1 convention of
REV 2 F6, covering A = 0. -/
def ReachesDeficitWithin (A : Matrix ι ι ℚ) (m : ℕ) (i : ι) : Prop :=
  ∃ ℓ, ℓ ≤ m ∧ ∃ path : Fin (ℓ + 1) → ι, path 0 = i ∧
    (∀ j : Fin ℓ, 0 < A (path j.castSucc) (path j.succ)) ∧
    RowDeficit A (path (Fin.last ℓ))

/-- No closed class (§2.3 named Prop): from EVERY state, a positive-entry
path of length ≤ Fintype.card ι reaches a strict-deficit row (the §3.A (1b)
reachability hypothesis, with KA2b's ≤ m bound built in). -/
def NoClosedClass (A : Matrix ι ι ℚ) : Prop :=
  ∀ i, ReachesDeficitWithin A (Fintype.card ι) i

/-! ## KA2a — the `mulVec_mono` toolkit -/

/-- KA2a (toolkit, leg i): a NONNEG matrix preserves entrywise ≤ of vectors.
deps: —.  Sketch: per entry, `Finset.sum_le_sum` with termwise
`mul_le_mul_of_nonneg_left`. -/
theorem mulVec_mono {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    {u v : ι → ℚ} (huv : ∀ i, u i ≤ v i) :
    ∀ i, (A *ᵥ u) i ≤ (A *ᵥ v) i := by
  intro i
  show ∑ j, A i j * u j ≤ ∑ j, A i j * v j
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (hnn i j)

/-- KA2a (toolkit, leg i′ — nonneg preservation, the special case u = 0 of
`mulVec_mono` every downstream induction opens with).  deps: —.  Sketch:
`Finset.sum_nonneg` + `mul_nonneg`. -/
theorem mulVec_nonneg {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    {u : ι → ℚ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, 0 ≤ (A *ᵥ u) i := by
  intro i
  show 0 ≤ ∑ j, A i j * u j
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hnn i j) (hu j)

/-- KA2a (toolkit, leg iii): entrywise ≤ of matrices is closed under `mulVec`
against a NONNEG vector: A ≤ B entrywise ⟹ A *ᵥ u ≤ B *ᵥ u entrywise.
deps: —.  Sketch: `Finset.sum_le_sum` + `mul_le_mul_of_nonneg_right`. -/
theorem mulVec_le_mulVec_of_entry_le {A B : Matrix ι ι ℚ}
    (hAB : ∀ i j, A i j ≤ B i j) {u : ι → ℚ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, (A *ᵥ u) i ≤ (B *ᵥ u) i := by
  intro i
  show ∑ j, A i j * u j ≤ ∑ j, B i j * u j
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hu j)

/-- KA2a (toolkit, leg ii): the mass sequence k ↦ A^k𝟙 is ANTITONE (in the
entrywise Pi order) under nonneg + substochastic.  deps: legs i/i′.  Sketch:
one step — A^{k+1}𝟙 = A *ᵥ (A^k𝟙) ≤ A *ᵥ 𝟙-padded ≤ A^k𝟙 by `mulVec_mono`
against A^k𝟙 ≤ 𝟙 (induction from substochasticity); `antitone_nat_of_succ_le`. -/
theorem pow_mulVec_one_antitone [DecidableEq ι]
    {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    (hsub : SubStochastic A) :
    Antitone (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ))) := by
  apply antitone_nat_of_succ_le
  intro k
  show (A ^ (k + 1)) *ᵥ (fun _ => (1 : ℚ)) ≤ (A ^ k) *ᵥ (fun _ => (1 : ℚ))
  intro i
  have hstep : (A ^ (k + 1)) *ᵥ (fun _ => (1 : ℚ))
      = (A ^ k) *ᵥ (A *ᵥ (fun _ => (1 : ℚ))) := by
    rw [pow_succ, Matrix.mulVec_mulVec]
  rw [hstep]
  refine mulVec_mono (fun p q => MovesS.pow_entry_nonneg hnn k p q) (fun j => ?_) i
  show ∑ j', A j j' * 1 ≤ 1
  calc ∑ j', A j j' * 1 = ∑ j', A j j' := by simp
    _ ≤ 1 := hsub j

/-! ## KA1, KA5 — ROUTE 1 (1a): uniform row-sum contraction -/

/-- KA1 `escapeE0_of_rowsum_lt` (ROUTE 1 (1a)): nonneg entries + every row
sum ≤ κ < 1 ⟹ ESCAPE(E0).  deps: — (KA2a legs are the natural helpers).
Sketch: induction on k gives A^k𝟙 ≤ κ^k𝟙 entrywise (`mulVec_mono`); squeeze
with κ^k → 0 (`tendsto_pow_atTop_nhds_zero_of_lt_one`; the |κ| < 1 side needs
0 ≤ κ only in the nonempty case, where some row sum ≥ 0 pins it — the empty
case is trivial). -/
theorem escapeE0_of_rowsum_lt [DecidableEq ι] {A : Matrix ι ι ℚ} {κ : ℚ}
    (hnn : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j ≤ κ) (hκ : κ < 1) :
    MovesS.EscapeE0 A := by
  refine ⟨hnn, tendsto_pi_nhds.mpr fun i => ?_⟩
  -- with a state `i` in hand the index type is nonempty, so 0 ≤ κ is pinned
  have hκ0 : 0 ≤ κ := le_trans (Finset.sum_nonneg fun j _ => hnn i j) (hrow i)
  have hbound : ∀ k p, ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) p ≤ κ ^ k := by
    intro k
    induction k with
    | zero =>
      intro p
      simp [Matrix.one_mulVec]
    | succ k ih =>
      intro p
      have hstep : (A ^ (k + 1)) *ᵥ (fun _ => (1 : ℚ))
          = A *ᵥ ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) := by
        rw [pow_succ', Matrix.mulVec_mulVec]
      rw [hstep]
      show ∑ j, A p j * ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) j ≤ κ ^ (k + 1)
      calc ∑ j, A p j * ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) j
          ≤ ∑ j, A p j * κ ^ k :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hnn p j)
        _ = (∑ j, A p j) * κ ^ k := by rw [Finset.sum_mul]
        _ ≤ κ * κ ^ k := mul_le_mul_of_nonneg_right (hrow p) (pow_nonneg hκ0 k)
        _ = κ ^ (k + 1) := (pow_succ' κ k).symm
  have hnonneg : ∀ k, 0 ≤ ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i := by
    intro k
    show 0 ≤ ∑ j, (A ^ k) i j * 1
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (MovesS.pow_entry_nonneg hnn k i j) zero_le_one
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ) hnonneg (fun k => hbound k i)

/-- Proof-local helper: over an EMPTY state set every mass vector is the zero
function, so escape is trivial (KA1/KA5's "empty case is trivial" leg). -/
private theorem escapeE0_of_isEmpty [DecidableEq ι] [IsEmpty ι]
    {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j) : MovesS.EscapeE0 A := by
  refine ⟨hnn, ?_⟩
  have hconst : ∀ k : ℕ, (A ^ k) *ᵥ (fun _ => (1 : ℚ)) = 0 := fun k =>
    funext fun p => (IsEmpty.false p).elim
  simp only [hconst]
  exact tendsto_const_nhds

/-- KA5 `escapeE0_of_exitPos` (ROUTE 1 (1d)'s abstract half): per-state exit
positivity (every row sum < 1, the named `RowSumLt`) + nonneg ⟹ ESCAPE(E0).
deps: KA1.  Sketch: κ := Finset.univ.sup' of the row sums (< 1 by finiteness
of the state set), then KA1; the empty index type goes through the trivial
escape directly. -/
theorem escapeE0_of_exitPos [DecidableEq ι] {A : Matrix ι ι ℚ}
    (hrow : RowSumLt A) (hnn : ∀ i j, 0 ≤ A i j) :
    MovesS.EscapeE0 A := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact escapeE0_of_isEmpty hnn
  | inr h =>
    haveI := h
    have hκlt : Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, A i j) < 1 :=
      (Finset.sup'_lt_iff Finset.univ_nonempty).mpr fun i _ => hrow i
    have hκle : ∀ i, ∑ j, A i j
        ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, A i j) :=
      fun i => Finset.le_sup' (fun i => ∑ j, A i j) (Finset.mem_univ i)
    exact escapeE0_of_rowsum_lt hnn hκle hκlt

/-! ## KA2b, KA2c — ROUTE 1 (1b): no-closed-class escape -/

/-- Proof-local helper: every entry of `A^k𝟙` is ≤ 1 under nonneg +
substochastic (the `k = 0` anchor of `pow_mulVec_one_antitone`). -/
private theorem pow_mulVec_one_le_one [DecidableEq ι] {A : Matrix ι ι ℚ}
    (hnn : ∀ i j, 0 ≤ A i j) (hsub : SubStochastic A) (k : ℕ) (i : ι) :
    ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i ≤ 1 := by
  have h := pow_mulVec_one_antitone hnn hsub (Nat.zero_le k) i
  simpa [Matrix.one_mulVec] using h

/-- Proof-local helper (the pre-approved KA2b split: the single-path peel):
walking a positive-entry path of length `ℓ` into a strict-deficit row pins
every mass entry `(A^k𝟙)(path 0)` strictly below 1 once `k > ℓ` — one factor
peeled per step, substochastic padding on the rest. -/
private theorem deficit_path_harvest [DecidableEq ι] {A : Matrix ι ι ℚ}
    (hnn : ∀ i j, 0 ≤ A i j) (hsub : SubStochastic A) :
    ∀ ℓ (p : Fin (ℓ + 1) → ι),
      (∀ j : Fin ℓ, 0 < A (p j.castSucc) (p j.succ)) →
      RowDeficit A (p (Fin.last ℓ)) →
      ∀ k, ℓ < k → ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) (p 0) < 1 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro p hpos hdef k hk
    have hdef0 : RowDeficit A (p 0) := by
      have he : p (Fin.last 0) = p 0 := congrArg p (Fin.ext (by simp))
      rwa [he] at hdef
    have h1 : ((A ^ 1) *ᵥ (fun _ => (1 : ℚ))) (p 0) < 1 := by
      show ∑ j, (A ^ 1) (p 0) j * 1 < 1
      simp only [pow_one, mul_one]
      exact hdef0
    have h := pow_mulVec_one_antitone hnn hsub (show 1 ≤ k from hk) (p 0)
    exact lt_of_le_of_lt h h1
  | succ ℓ IH =>
    intro p hpos hdef k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : ℓ < k' := by omega
    -- the tail path (indices 1 … ℓ+1 of p)
    have hqpos : ∀ j : Fin ℓ, 0 < A ((fun t : Fin (ℓ + 1) => p t.succ) j.castSucc)
        ((fun t : Fin (ℓ + 1) => p t.succ) j.succ) := by
      intro j
      have h := hpos j.succ
      rwa [← Fin.succ_castSucc] at h
    have hqdef : RowDeficit A ((fun t : Fin (ℓ + 1) => p t.succ) (Fin.last ℓ)) := by
      show RowDeficit A (p (Fin.last ℓ).succ)
      rw [Fin.succ_last]
      exact hdef
    have hIH := IH (fun t : Fin (ℓ + 1) => p t.succ) hqpos hqdef k' hk'
    -- hIH : ((A ^ k') *ᵥ 𝟙) (p (0 : Fin (ℓ+1)).succ) < 1
    -- peel the first edge
    have hstep : (A ^ (k' + 1)) *ᵥ (fun _ => (1 : ℚ))
        = A *ᵥ ((A ^ k') *ᵥ (fun _ => (1 : ℚ))) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hstep]
    have hedge : 0 < A (p 0) (p (0 : Fin (ℓ + 1)).succ) := by
      have h := hpos 0
      rwa [Fin.castSucc_zero] at h
    show ∑ j, A (p 0) j * ((A ^ k') *ᵥ (fun _ => (1 : ℚ))) j < 1
    have hlt : ∑ j, A (p 0) j * ((A ^ k') *ᵥ (fun _ => (1 : ℚ))) j
        < ∑ j, A (p 0) j * 1 := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_le_mul_of_nonneg_left (pow_mulVec_one_le_one hnn hsub k' j)
          (hnn (p 0) j)
      · exact ⟨p (0 : Fin (ℓ + 1)).succ, Finset.mem_univ _,
          mul_lt_mul_of_pos_left hIH hedge⟩
    calc ∑ j, A (p 0) j * ((A ^ k') *ᵥ (fun _ => (1 : ℚ))) j
        < ∑ j, A (p 0) j * 1 := hlt
      _ = ∑ j, A (p 0) j := by simp
      _ ≤ 1 := hsub (p 0)

/-- Proof-local helper (KA2b): every positive-entry path into a strict-deficit
row shortens to one of length < `Fintype.card ι` with the same start — a
repeated vertex (pigeonhole) bounds a removable loop; splice and recurse. -/
private theorem path_shorten {A : Matrix ι ι ℚ} :
    ∀ ℓ (p : Fin (ℓ + 1) → ι),
      (∀ j : Fin ℓ, 0 < A (p j.castSucc) (p j.succ)) →
      RowDeficit A (p (Fin.last ℓ)) →
      ∃ ℓ' < Fintype.card ι, ∃ q : Fin (ℓ' + 1) → ι, q 0 = p 0 ∧
        (∀ j : Fin ℓ', 0 < A (q j.castSucc) (q j.succ)) ∧
        RowDeficit A (q (Fin.last ℓ')) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ IH =>
  intro p hpos hdef
  by_cases hcard : ℓ < Fintype.card ι
  · exact ⟨ℓ, hcard, p, rfl, hpos, hdef⟩
  · -- pigeonhole: ℓ + 1 > card ι vertices, so the path repeats one
    obtain ⟨a, b, hab, hpab⟩ := Fintype.exists_ne_map_eq_of_card_lt p
      (by rw [Fintype.card_fin]; omega)
    obtain ⟨a, b, hlt, heq⟩ : ∃ a b : Fin (ℓ + 1), a < b ∧ p a = p b := by
      rcases lt_or_gt_of_ne hab with h' | h'
      · exact ⟨a, b, h', hpab⟩
      · exact ⟨b, a, h', hpab.symm⟩
    have hva : (a : ℕ) < (b : ℕ) := hlt
    have hbℓ : (b : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp b.isLt
    set d : ℕ := (b : ℕ) - (a : ℕ) with hd
    set L : ℕ := ℓ - d with hL
    have hLℓ : L < ℓ := by omega
    have haL : (a : ℕ) ≤ L := by omega
    -- the spliced path: prefix up to a, then jump the loop a→b
    set q : Fin (L + 1) → ι := fun j =>
      p (if (j : ℕ) ≤ (a : ℕ)
         then ⟨(j : ℕ), by have hj := j.isLt; omega⟩
         else ⟨(j : ℕ) + d, by have hj := j.isLt; omega⟩) with hqdef
    have hq0 : q 0 = p 0 := by
      simp only [hqdef, Fin.val_zero]
      rw [if_pos (Nat.zero_le _)]
      exact congrArg p (Fin.ext (by simp))
    have hqpos : ∀ j : Fin L, 0 < A (q j.castSucc) (q j.succ) := by
      intro j
      have hjL : (j : ℕ) < L := j.isLt
      simp only [hqdef, Fin.val_castSucc, Fin.val_succ]
      by_cases h1 : (j : ℕ) + 1 ≤ (a : ℕ)
      · -- prefix zone: an original edge
        rw [if_pos (by omega : (j : ℕ) ≤ (a : ℕ)), if_pos h1]
        exact hpos ⟨(j : ℕ), by omega⟩
      · by_cases h2 : (j : ℕ) ≤ (a : ℕ)
        · -- splice zone: j = a, ride the edge out of b instead
          rw [if_pos h2, if_neg h1]
          have e1 : p (⟨(j : ℕ), by omega⟩ : Fin (ℓ + 1)) = p b := by
            have hfa : (⟨(j : ℕ), by omega⟩ : Fin (ℓ + 1)) = a :=
              Fin.ext (by simp only []; omega)
            rw [hfa, heq]
          have e2 : p (⟨(j : ℕ) + 1 + d, by omega⟩ : Fin (ℓ + 1))
              = p (Fin.succ ⟨(b : ℕ), by omega⟩) :=
            congrArg p (Fin.ext (by simp only [Fin.val_succ]; omega))
          rw [e1, e2]
          exact hpos ⟨(b : ℕ), by omega⟩
        · -- suffix zone: an original edge, shifted by the removed loop
          rw [if_neg h2, if_neg (by omega : ¬ ((j : ℕ) + 1 ≤ (a : ℕ)))]
          have e3 : p (⟨(j : ℕ) + 1 + d, by omega⟩ : Fin (ℓ + 1))
              = p (Fin.succ ⟨(j : ℕ) + d, by omega⟩) :=
            congrArg p (Fin.ext (by simp only [Fin.val_succ]; omega))
          rw [e3]
          exact hpos ⟨(j : ℕ) + d, by omega⟩
    have hqdef' : RowDeficit A (q (Fin.last L)) := by
      simp only [hqdef, Fin.val_last]
      by_cases hLa : L ≤ (a : ℕ)
      · -- then L = a and b is the path's end
        rw [if_pos hLa]
        have e4 : p (⟨L, by omega⟩ : Fin (ℓ + 1)) = p (Fin.last ℓ) := by
          have hfa : (⟨L, by omega⟩ : Fin (ℓ + 1)) = a :=
            Fin.ext (by simp only []; omega)
          have hfb : b = Fin.last ℓ := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [hfa, heq, hfb]
        rw [e4]
        exact hdef
      · rw [if_neg hLa]
        have e5 : p (⟨L + d, by omega⟩ : Fin (ℓ + 1)) = p (Fin.last ℓ) :=
          congrArg p (Fin.ext (by simp only [Fin.val_last]; omega))
        rw [e5]
        exact hdef
    obtain ⟨ℓ', hℓ', q', hq'0, hq'pos, hq'def⟩ := IH L hLℓ q hqpos hqdef'
    exact ⟨ℓ', hℓ', q', by rw [hq'0, hq0], hq'pos, hq'def⟩

/-- KA2b `deficit_spread` (ROUTE 1 (1b), the ε-harvest): A nonneg
substochastic with every state reaching a strict-deficit row in ≤ m :=
Fintype.card ι steps ⟹ ∃ ε > 0 with every entry of A^m𝟙 ≤ 1 − ε.
deps: KA2a.  Sketch (REV 2, F6 — the old "min positive entry" is undefined at
A = 0, which satisfies the hypotheses): per state i take the reachability
witness path i = i₀ → … → i_ℓ (entries positive, row i_ℓ strictly deficient);
set ε_i := (Π_j A(i_j, i_{j+1})) · (1 − Σ_β A(i_ℓ, β)) > 0 (empty product = 1
covers ℓ = 0, hence also A = 0); ε := finite min over states; peel the path
one factor per step with substochastic padding on the remaining m − ℓ steps
to bound every entry of A^m𝟙 by 1 − ε_i ≤ 1 − ε.  hard-fable; pre-approved
split if it grows: the single-path peel as its own lemma. -/
theorem deficit_spread [DecidableEq ι]
    {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    (hsub : SubStochastic A) (hreach : NoClosedClass A) :
    ∃ ε > (0 : ℚ), ∀ i,
      ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ))) i ≤ 1 - ε := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, one_pos, fun i => (h.false i).elim⟩
  | inr h =>
    haveI := h
    -- qualitative form: every entry of A^m𝟙 is strictly below 1
    have hlt : ∀ i, ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ))) i < 1 := by
      intro i
      obtain ⟨ℓ, hℓm, path, hp0, hppos, hpdef⟩ := hreach i
      obtain ⟨ℓ', hℓ'card, q, hq0, hqpos, hqdef⟩ := path_shorten ℓ path hppos hpdef
      have hh := deficit_path_harvest hnn hsub ℓ' q hqpos hqdef
        (Fintype.card ι) hℓ'card
      rwa [hq0, hp0] at hh
    -- harvest the finite min of the deficits
    refine ⟨Finset.univ.inf' Finset.univ_nonempty
      (fun i => 1 - ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ))) i), ?_, ?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun i _ => by
        linarith [hlt i]
    · intro i
      have hle := Finset.inf'_le
        (fun i => 1 - ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ))) i)
        (Finset.mem_univ i)
      linarith

/-- KA2c `escapeE0_of_noClosedClass` (ROUTE 1 (1b)): nonneg + substochastic +
no closed class ⟹ ESCAPE(E0).  deps: KA2d (CM gate — ON RECORD at
Kernels/KA2d.lean, sequenced first per REV 2 F5: both hypotheses needed),
KA1, KA2a, KA2b.  Sketch: A^{km}𝟙 ≤ (1−ε)^k𝟙 by KA2b + induction (m :=
Fintype.card ι; substochasticity powers compose); interpolate the in-between
exponents by KA2a antitonicity (`pow_mulVec_one_antitone`); squeeze. -/
theorem escapeE0_of_noClosedClass [DecidableEq ι]
    {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    (hsub : SubStochastic A) (hreach : NoClosedClass A) :
    MovesS.EscapeE0 A := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact escapeE0_of_isEmpty hnn
  | inr h =>
    haveI := h
    obtain ⟨ε, hε, hbound⟩ := deficit_spread hnn hsub hreach
    have hm0 : 0 < Fintype.card ι := Fintype.card_pos
    -- 0 ≤ 1 − ε: the bounded entry is itself nonneg at any state
    have h1ε0 : (0 : ℚ) ≤ 1 - ε := by
      obtain ⟨i₀⟩ := h
      have h0 : 0 ≤ ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ))) i₀ := by
        show 0 ≤ ∑ j, (A ^ Fintype.card ι) i₀ j * 1
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (MovesS.pow_entry_nonneg hnn _ i₀ j) zero_le_one
      linarith [hbound i₀]
    have h1ε1 : (1 : ℚ) - ε < 1 := by linarith
    -- geometric decay along the m-subsequence: A^{km}𝟙 ≤ (1−ε)^k 𝟙
    have hgeo : ∀ k i, ((A ^ (k * Fintype.card ι)) *ᵥ (fun _ => (1 : ℚ))) i
        ≤ (1 - ε) ^ k := by
      intro k
      induction k with
      | zero =>
        intro i
        simp [Matrix.one_mulVec]
      | succ k ihk =>
        intro i
        have hsplit : (A ^ ((k + 1) * Fintype.card ι)) *ᵥ (fun _ => (1 : ℚ))
            = (A ^ (k * Fintype.card ι)) *ᵥ
              ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ))) := by
          rw [Nat.succ_mul, pow_add, Matrix.mulVec_mulVec]
        rw [hsplit]
        calc ((A ^ (k * Fintype.card ι)) *ᵥ
              ((A ^ Fintype.card ι) *ᵥ (fun _ => (1 : ℚ)))) i
            ≤ ((A ^ (k * Fintype.card ι)) *ᵥ (fun _ => 1 - ε)) i :=
              mulVec_mono (fun x y => MovesS.pow_entry_nonneg hnn _ x y) hbound i
          _ = (1 - ε) * ((A ^ (k * Fintype.card ι)) *ᵥ (fun _ => (1 : ℚ))) i := by
              have hsm : (fun _ : ι => 1 - ε) = (1 - ε) • (fun _ : ι => (1 : ℚ)) := by
                funext x
                simp
              rw [hsm, Matrix.mulVec_smul]
              simp
          _ ≤ (1 - ε) * (1 - ε) ^ k :=
              mul_le_mul_of_nonneg_left (ihk i) h1ε0
          _ = (1 - ε) ^ (k + 1) := (pow_succ' _ _).symm
    -- interpolate by antitonicity and squeeze per coordinate
    refine ⟨hnn, tendsto_pi_nhds.mpr fun i => ?_⟩
    have hub : ∀ n, ((A ^ n) *ᵥ (fun _ => (1 : ℚ))) i
        ≤ (1 - ε) ^ (n / Fintype.card ι) := by
      intro n
      have hnm : (n / Fintype.card ι) * Fintype.card ι ≤ n :=
        Nat.div_mul_le_self n _
      have hanti := pow_mulVec_one_antitone hnn hsub hnm i
      exact le_trans hanti (hgeo (n / Fintype.card ι) i)
    have hlb : ∀ n, 0 ≤ ((A ^ n) *ᵥ (fun _ => (1 : ℚ))) i := by
      intro n
      show 0 ≤ ∑ j, (A ^ n) i j * 1
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (MovesS.pow_entry_nonneg hnn n i j) zero_le_one
    have hpow : Filter.Tendsto (fun n : ℕ => (1 - ε) ^ (n / Fintype.card ι))
        Filter.atTop (nhds 0) := by
      have hdiv : Filter.Tendsto (fun n : ℕ => n / Fintype.card ι)
          Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop_of_monotone
          (fun x y hxy => Nat.div_le_div_right hxy)
          (fun c => ⟨c * Fintype.card ι, by rw [Nat.mul_div_cancel _ hm0]⟩)
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one h1ε0 h1ε1).comp hdiv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow hlb hub

/-! ## KA3 — ROUTE 1 (1c): the refuter's soundness -/

/-- KA3 `noEscape_of_closedClass` (ROUTE 1 (1c), the converse — makes
escape_probe_a's layer-1 closed-class criterion a THEOREM, not just a
script): a nonempty class C with every C-row summing to exactly 1 inside C
and vanishing outside C admits NO escape.  deps: KA2a.  Sketch: (A^k𝟙)|_C = 1
by induction on k (the step is the closed-class row computation:
(A^{k+1}𝟙)_i = Σ_{j∈C} A i j · (A^k𝟙)_j = Σ_{j∈C} A i j = 1 for i ∈ C — no
nonneg needed); Tendsto to 0 then fails at any i ∈ C (evaluation is
continuous in the Pi topology; the constant sequence 1 ↛ 0). -/
theorem noEscape_of_closedClass [DecidableEq ι] {A : Matrix ι ι ℚ} {C : Finset ι}
    (hC : C.Nonempty)
    (hclosed : ∀ i ∈ C, ∑ j ∈ C, A i j = 1)
    (hout : ∀ i ∈ C, ∀ j ∉ C, A i j = 0) :
    ¬ MovesS.EscapeE0 A := by
  intro hesc
  obtain ⟨i₀, hi₀⟩ := hC
  -- the mass sits at 1 on C forever
  have hone : ∀ k, ∀ i ∈ C, ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i = 1 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp [Matrix.one_mulVec]
    | succ k ihk =>
      intro i hi
      have hstep : (A ^ (k + 1)) *ᵥ (fun _ => (1 : ℚ))
          = A *ᵥ ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) := by
        rw [pow_succ', Matrix.mulVec_mulVec]
      rw [hstep]
      show ∑ j, A i j * ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) j = 1
      -- the sum collapses onto C (rows of C vanish outside C)
      have hcollapse : ∑ j ∈ C, A i j * ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) j
          = ∑ j, A i j * ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) j :=
        Finset.sum_subset (Finset.subset_univ C)
          (fun j _ hj => by rw [hout i hi j hj, zero_mul])
      rw [← hcollapse]
      calc ∑ j ∈ C, A i j * ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) j
          = ∑ j ∈ C, A i j :=
            Finset.sum_congr rfl fun j hj => by rw [ihk j hj, mul_one]
        _ = 1 := hclosed i hi
  -- but escape drives the i₀ coordinate to 0
  have hten : Filter.Tendsto (fun k => ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i₀)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pi_nhds.mp hesc.escape) i₀
  have hconst : (fun k => ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i₀)
      = fun _ => (1 : ℚ) := funext fun k => hone k i₀ hi₀
  rw [hconst] at hten
  exact one_ne_zero (tendsto_nhds_unique hten tendsto_const_nhds).symm

end LeanUrat.Kernels
