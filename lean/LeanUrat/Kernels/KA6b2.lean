/-
Kernels/KA6b2 — BP4-c7 E-phase skeleton for unit KA6b2 [ATTEMPT; NEW id at
REV 2 — the F2/F13 split of the retired KA6b]: the window/table seam, THE
OPEN CORE of E0's per-state route, restated per §3.A (1d)'s a-indexed case
split (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.A (1d) + §4 KA6b2 + R1;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

GATE SEQUENCING (REV 2, F5): KA6b2's CM-first twin KA6a (the python
exit-cell survival probe, verification/, anchored-a≥2-FIRST search order) is
a SIBLING unit and runs BEFORE any prover is assigned here.  Its findings
select between the two a ≥ 2 routes below (cofactor-criterion exit vs the
class-level KA2c reroute); the a ≤ 1 head is gate-independent in shape.

RECORDED RESOLUTIONS (statement transcription):
· CARRIERS (⚑ Q1, blueprint's own disjunction "the §M-SPECIES menu (MovesSp)
  or a self-contained window model"): resolved to the SELF-CONTAINED WINDOW
  MODEL `WindowModel` below — the minimal typed form of "the window digits
  parameterize only the FREE coefficients away from the anchor" (§3.A (1d)).
  The seam from the real table's states to `WindowModel` instances (which
  (state, pool) yields which anchor pin a and which digit set) is the
  prover's attempt territory, guided by KA6a; NO MovesSp import is taken at
  statement time.
· `free_surj` is THE CONTESTED SEAM PREMISE — exactly what KA6a probes: at a
  real (state, pool) the free coefficients may be PINNED, failing the
  surjection; the fallback obstruction record then documents "the exact
  window-to-residual map and the pinned coefficient set" (blueprint §3.A
  (1d) fallback verbatim).
· "pool q₀ ≥ 2" is automatic for a finite field carrier
  (`Fintype.one_lt_card`); the pool is read as q₀ = |F|.
· The "⟹ terminal exit; row sum < 1 via KA5" tie is the TABLE seam (needs
  the pool-table carriers, sibling territory) — deliberately NOT stated
  here; this unit delivers the residual-existence legs the table seam
  consumes.

deps: KA6a (CM gate — runs FIRST; python, no Lean), KA6b1
(Kernels/KA6b1.lean — the counting layer: squarefree-monic count/positivity,
degree-1 separability, the a = 1 X·cofactor mechanism, the a ≥ 2 compiled
impossibility).

Build: cd lean && lake build LeanUrat.Kernels.KA6b2
-/
import LeanUrat.Kernels.KA6b1

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
/- `[Fintype F]` is deliberately kept in both theorem statements although the
bare existentials do not consume it: the pool carrier IS a finite field
(q₀ = |F| — the blueprint's "every pool q₀ ≥ 2" reading) and the intended
KA6b1 counting route is finite-field counting; dropping the instance would
silently widen the unit's scope past the blueprint statement. -/
set_option linter.unusedFintypeInType false

namespace LeanUrat.Kernels

open Polynomial

/-- KA6b2 (⚑ Q1 carrier, the self-contained window model): one realized
active state's window read at a pool with residue field F.  Anchor pin `a`
(anchored strata pin a z^a factor of the residual), read size `e`, and the
FREE window digit choices `Digit` parameterizing the residual's cofactor
away from the anchor.  `free_surj` — the digits reach EVERY monic cofactor
of degree e − a — is the contested seam premise (see file header); at real
anchored states KA6a probes whether it survives. -/
structure WindowModel (F : Type*) [Field F] where
  a : ℕ
  e : ℕ
  e_pos : 0 < e
  a_le : a ≤ e
  Digit : Type
  cofactor : Digit → Polynomial F
  cof_monic : ∀ d, (cofactor d).Monic
  cof_deg : ∀ d, (cofactor d).natDegree = e - a
  free_surj : ∀ c : Polynomial F, c.Monic → c.natDegree = e - a →
    ∃ d, cofactor d = c

/-- KA6b2 (the window-to-residual map): the residual read of a digit choice
— the anchor factor z^a times the digit-parameterized cofactor (§3.A (1d):
"anchored strata pin a z^a factor of the residual; the window digits
parameterize only the FREE coefficients away from the anchor"). -/
noncomputable def WindowModel.residual {F : Type*} [Field F]
    (W : WindowModel F) (d : W.Digit) : Polynomial F :=
  (X : Polynomial F) ^ W.a * W.cofactor d

/-! ## The a ≤ 1 head (the squarefree-residual exit mechanism) -/

/-- KA6b2 (HEAD, a ≤ 1): at every state with anchor pin a ≤ 1 and every pool
(finite F, so q₀ = |F| ≥ 2 automatically), some FREE window digit choice
yields a SQUAREFREE residual — the terminal-exit mechanism of §3.A (1d)
(the row-sum < 1 consequence rides the table seam via KA5, not stated
here).  deps: KA6a (gate), KA6b1, `free_surj`.  Sketch: case a = 0 —
residual = cofactor (up to `one_mul`); e ≥ 2: `ka6b1_card_squarefree_monic_pos`
gives a squarefree monic of degree e, reached by `free_surj`; e = 1:
`ka6b1_degree_one_separable` + `Separable.squarefree`.  Case a = 1 —
target X·c with c monic squarefree of degree e − 1 and X ∤ c (exists: c = 1
at e = 1; X + 1 at e = 2; an irreducible of degree e − 1 with nonzero
constant term at e ≥ 3); `free_surj` reaches c; `ka6b1_X_mul_squarefree`
closes. -/
theorem ka6b2_squarefree_exit_of_anchor_le_one (F : Type*) [Field F]
    [Fintype F] (W : WindowModel F) (ha : W.a ≤ 1) :
    ∃ d : W.Digit, Squarefree (W.residual d) := by
  sorry

/-! ## The a ≥ 2 leg (the cofactor-criterion candidate) -/

/-- KA6b2 (a ≥ 2 candidate leg — the COFACTOR-criterion exit): at a ≥ 2
anchors NO residual is squarefree (`ka6b1_anchor_not_squarefree` — the F2
compiled impossibility), so the sketched universal is dead there; the
candidate replacement exit is the anchored read's own terminal/split
criterion on the COFACTOR — some free digit choice yields a SEPARABLE
(squarefree) cofactor coprime to z (§3.A (1d) a ≥ 2).  Whether the REAL
table grants that read an exit is exactly the open question KA6a's
anchored-first probe answers; if KA6a instead supports the class-level
reroute, the consumer switches to KA2c's reachability form and this lemma
records the model-level half only.  deps: KA6a (gate), KA6b1, `free_surj`.
Sketch: pick c monic squarefree of degree e − a with X ∤ c (c = 1 at
degree 0; X + 1 at degree 1; an irreducible with nonzero constant term at
degree ≥ 2); `free_surj` reaches it. -/
theorem ka6b2_cofactor_exit (F : Type*) [Field F] [Fintype F]
    (W : WindowModel F) :
    ∃ d : W.Digit,
      Squarefree (W.cofactor d) ∧ ¬ (X : Polynomial F) ∣ W.cofactor d := by
  sorry

end LeanUrat.Kernels
