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

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

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
  sorry

/-- KA2a (toolkit, leg i′ — nonneg preservation, the special case u = 0 of
`mulVec_mono` every downstream induction opens with).  deps: —.  Sketch:
`Finset.sum_nonneg` + `mul_nonneg`. -/
theorem mulVec_nonneg {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    {u : ι → ℚ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, 0 ≤ (A *ᵥ u) i := by
  sorry

/-- KA2a (toolkit, leg iii): entrywise ≤ of matrices is closed under `mulVec`
against a NONNEG vector: A ≤ B entrywise ⟹ A *ᵥ u ≤ B *ᵥ u entrywise.
deps: —.  Sketch: `Finset.sum_le_sum` + `mul_le_mul_of_nonneg_right`. -/
theorem mulVec_le_mulVec_of_entry_le {A B : Matrix ι ι ℚ}
    (hAB : ∀ i j, A i j ≤ B i j) {u : ι → ℚ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, (A *ᵥ u) i ≤ (B *ᵥ u) i := by
  sorry

/-- KA2a (toolkit, leg ii): the mass sequence k ↦ A^k𝟙 is ANTITONE (in the
entrywise Pi order) under nonneg + substochastic.  deps: legs i/i′.  Sketch:
one step — A^{k+1}𝟙 = A *ᵥ (A^k𝟙) ≤ A *ᵥ 𝟙-padded ≤ A^k𝟙 by `mulVec_mono`
against A^k𝟙 ≤ 𝟙 (induction from substochasticity); `antitone_nat_of_succ_le`. -/
theorem pow_mulVec_one_antitone [DecidableEq ι]
    {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    (hsub : SubStochastic A) :
    Antitone (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ))) := by
  sorry

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
  sorry

/-- KA5 `escapeE0_of_exitPos` (ROUTE 1 (1d)'s abstract half): per-state exit
positivity (every row sum < 1, the named `RowSumLt`) + nonneg ⟹ ESCAPE(E0).
deps: KA1.  Sketch: κ := Finset.univ.sup' of the row sums (< 1 by finiteness
of the state set), then KA1; the empty index type goes through the trivial
escape directly. -/
theorem escapeE0_of_exitPos [DecidableEq ι] {A : Matrix ι ι ℚ}
    (hrow : RowSumLt A) (hnn : ∀ i j, 0 ≤ A i j) :
    MovesS.EscapeE0 A := by
  sorry

/-! ## KA2b, KA2c — ROUTE 1 (1b): no-closed-class escape -/

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
  sorry

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
  sorry

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
  sorry

end LeanUrat.Kernels
