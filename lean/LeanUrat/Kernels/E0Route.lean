/-
Kernels/E0Route — BP4-c4 E-phase skeletons for the TYPED measure route to E0:
units KA4a, KA4b (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.A ROUTE 2 + §4
KA4a/KA4b; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

⚑ INTERFACE FLAG (KA4a, per the blueprint): the `blockMass` def + `BlockDrain`
Prop shape below is the REV 2 F7-decided interface (ℝ codomain forced by the
ciInf — ℚ has no such infima; the single ℚ→ℝ coercion point sits inside
`blockMass`).  The orchestrator ratifies this def + Prop shape BEFORE provers
run; consumers: KA4b here, then the KA4c ROUTE-E0 seam (sibling unit, NOT in
this cluster) toward the CL-4 X.3 edge.

The SEMANTIC identification (blockMass = the still-in-block-after-k
normalized conditional mass) is deliberately NOT a field or theorem here — it
is KA4c's seam statement against XCtx (blueprint §3.A ROUTE 2).

RECORDED RESOLUTIONS (statement transcription):
· `BlockDrain` is parenthesized (⨅ k, blockMass A k τ) = 0 — the iInf of the
  ℝ-valued sequence, NOT an iInf of Props.
· NON-VACUITY gate ("a decide/norm_num instance at the N2 pool"): stated at
  the RAW 1×1 matrix !![1/8] — the evaluated active matrix value of the N2
  pool package at q₀ = 2, e = 2 (`MovesS.n2_pool`, MovesS/N2Pool.lean:140:
  every `n2P2.A` entry = 1/8) — following the KA2d raw-form precedent to keep
  imports minimal; the identification with `n2P2.A` is definitional (both are
  the constant-1/8 matrix on a one-element index) and belongs to the seam
  layer if ever needed.

deps: Kernels/E0Matrix.lean (`SubStochastic`), MovesS/Defs.lean (`EscapeE0`,
transitively).
Build: cd lean && lake build LeanUrat.Kernels.E0Route
-/
import LeanUrat.Kernels.E0Matrix

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open Matrix

/-! ## KA4a — `blockMass` + `BlockDrain` (the typed interface, ⚑) -/

/-- KA4a (the DEF, REV 2 F7): the ℝ-valued still-in-block mass functional of
the ℚ-matrix iteration — blockMass A k τ = ((A^k 𝟙) τ : ℝ).  The tie to the
matrix side is DEFINITIONAL; the single ℚ→ℝ coercion of ROUTE 2 sits here and
nowhere else.  deps: —. -/
noncomputable def blockMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (k : ℕ) (τ : ι) : ℝ :=
  (((A ^ k) *ᵥ (fun _ => (1 : ℚ))) τ : ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- KA4a (law, as a LEMMA not a field): blockMass at k = 0 is 1.
deps: —.  Sketch: pow_zero + one_mulVec + Rat.cast_one. -/
theorem blockMass_zero (A : Matrix ι ι ℚ) (τ : ι) :
    blockMass A 0 τ = 1 := by
  sorry

/-- KA4a (law, as a LEMMA not a field): the one-step recursion
blockMass A (k+1) τ = Σ_β (A τ β : ℝ) · blockMass A k β.
deps: —.  Sketch: pow_succ'/mulVec_mulVec unfolding + Rat.cast push (the
sum-of-products commutes with the ring hom ℚ → ℝ). -/
theorem blockMass_step (A : Matrix ι ι ℚ) (k : ℕ) (τ : ι) :
    blockMass A (k + 1) τ = ∑ β, (A τ β : ℝ) * blockMass A k β := by
  sorry

/-- KA4a (law, as a LEMMA not a field): blockMass is antitone in k under
nonneg + substochastic.  deps: KA2a (`pow_mulVec_one_antitone`), cast
monotonicity.  Sketch: `Rat.cast_le` transports the ℚ-side antitonicity. -/
theorem blockMass_antitone {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    (hsub : SubStochastic A) (τ : ι) :
    Antitone (fun k => blockMass A k τ) := by
  sorry

/-- KA4a (the Prop, REV 2 F7): BLOCK DRAIN — at every state the infimum of
the still-in-block mass sequence is 0 (ℝ-valued ciInf of a bounded-below
sequence — well-posed; ℚ has no such infima, which forced the codomain).
This is the X.3 consumer face (CL-4); the derivation of BlockDrain from the
XCtx a.e.-termination hypothesis is the sibling seam unit KA4c. -/
def BlockDrain (A : Matrix ι ι ℚ) : Prop :=
  ∀ τ, (⨅ k, blockMass A k τ) = 0

/-! ### KA4a non-vacuity gate (the N2 pool instance) -/

/-- KA4a (non-vacuity data): the evaluated 1×1 active matrix value at the N2
pool q₀ = 2, e = 2 — every entry of `MovesS.n2P2.A` is 1/8 (`MovesS.n2_pool`,
MovesS/N2Pool.lean).  Raw-form per the KA2d precedent (see file header). -/
def n2PoolMatrix : Matrix (Fin 1) (Fin 1) ℚ := !![1/8]

/-- KA4a (non-vacuity, mass law): at the N2 pool matrix the block mass is
exactly (1/8)^k — the escape_probe_b "A^k𝟙 = κ^k EXACTLY" pattern at n = 2.
deps: —.  Sketch: induction on k via blockMass_zero/blockMass_step +
Fin.sum_univ_one + norm_num. -/
theorem n2PoolMatrix_blockMass (k : ℕ) (τ : Fin 1) :
    blockMass n2PoolMatrix k τ = (1 / 8 : ℝ) ^ k := by
  sorry

/-- KA4a (NON-VACUITY gate): BlockDrain holds at the N2 pool matrix.
deps: n2PoolMatrix_blockMass.  Sketch: ⨅ k, (1/8)^k = 0 in ℝ
(geometric decay: antitone, bounded below by 0, tends to 0; `ciInf` of a
sequence tending to its greatest lower bound). -/
theorem n2PoolMatrix_blockDrain : BlockDrain n2PoolMatrix := by
  sorry

/-! ## KA4b — drain implies escape -/

/-- KA4b `escape_of_drain`: nonneg + substochastic + BlockDrain A ⟹
ESCAPE(E0).  deps: KA4a.  Sketch: per-τ blockMass antitone
(`blockMass_antitone`) and bounded below with inf 0 ⟹ Tendsto 0 in ℝ
(`tendsto_atTop_ciInf`); pull the limit back along the inducing
`Rat.cast : ℚ → ℝ` to EscapeE0's ℚ-valued statement; finite index ⟹
`tendsto_pi_nhds` assembles the vector limit. -/
theorem escape_of_drain {A : Matrix ι ι ℚ} (hnn : ∀ i j, 0 ≤ A i j)
    (hsub : SubStochastic A) (hdrain : BlockDrain A) :
    MovesS.EscapeE0 A := by
  sorry

end LeanUrat.Kernels
