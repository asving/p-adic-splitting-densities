/-
Kernels/KA6b1 — BP4-c4 E-phase skeleton for unit KA6b1 [NEW id at REV 2 —
the F2/F13 split of the retired KA6b]: the finite-field counting layer (pure
F_q[z], NO table seam) (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.A (1d) +
§4 KA6b1; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

Four legs, all over an abstract field F (finite where counting demands it):
 · the squarefree-monic COUNT: #{squarefree monics of degree e over F_q} =
   q^e − q^{e−1} for e ≥ 2, and its positivity (q ≥ 2 is automatic for a
   finite field — `Fintype.one_lt_card`);
 · degree-1 monics are separable outright;
 · z·(squarefree cofactor with z ∤ cofactor) is squarefree — the a = 1
   anchored-target mechanism;
 · the COMPILED IMPOSSIBILITY (the F2 fact, stated positively so no prover
   re-attempts the dead route): for a ≥ 2, z^a·c is NEVER squarefree — z²
   divides every such residual REGARDLESS of the cofactor.  At a ≥ 2
   anchored states the squarefree-residual exit mechanism is provably
   ABSENT; the open (state, pool) seam is the sibling unit KA6b2, gated by
   KA6a's anchored-first probe.

Consumers: KA6b2 (the window/table seam — NOT in this cluster).
deps: — (self-contained; pure Mathlib polynomial algebra).

RECORDED RESOLUTIONS (statement transcription):
· "number q^e − q^{e−1}" is stated via `Nat.card` of the subtype of monic
  squarefree degree-e polynomials (no Fintype instance obligation on the
  subtype at statement time).
· "z" is `Polynomial.X`; "coprime to z" is transcribed as ¬ X ∣ c (the
  blueprint's own "z ∤ cofactor" phrasing, §3.A (1d) a = 1).
· "degree e" is `natDegree = e`; positivity of the count is a separate
  corollary rather than a "> 0" annotation on the equality.
· File placement: the §4 KA header assigns KA units to E0Matrix/E0Route;
  KA6b1 is pure polynomial counting with no matrix content, so it takes the
  default <UnitId>.lean per the campaign file-naming rule.

Build: cd lean && lake build LeanUrat.Kernels.KA6b1
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open Polynomial

/-! ## Leg 1 — the squarefree-monic count (e ≥ 2) -/

/-- KA6b1 (count law): squarefree monics of degree e over a finite field F
number q^e − q^{e−1}, for e ≥ 2 (q := Fintype.card F).  deps: —.  Sketch:
the classical zeta-function/Möbius count — every monic f factors uniquely as
g²·h with h squarefree ... at degree e ≥ 2 the count telescopes to
q^e − q^{e−1}; alternatively port the generating-function identity
Σ (#squarefree monics of deg e)·t^e = (1 − qt²)/(1 − qt).  hard leg of the
unit (known mathematics, no new content). -/
theorem ka6b1_card_squarefree_monic (F : Type*) [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) :
    Nat.card {f : Polynomial F // f.Monic ∧ f.natDegree = e ∧ Squarefree f} =
      Fintype.card F ^ e - Fintype.card F ^ (e - 1) := by
  sorry

/-- KA6b1 (positivity — the "> 0" of the blueprint display): the
squarefree-monic count at degree e ≥ 2 is positive; q ≥ 2 is automatic
(`Fintype.one_lt_card` for a finite field).  deps: the count law (or a direct
witness, e.g. a product of e distinct monic linears when q ≥ e, X^e − z
adjustments otherwise — the count route is the intended one).  Consumed by
KA6b2 as "some free-digit choice makes the residual squarefree" at a = 0. -/
theorem ka6b1_card_squarefree_monic_pos (F : Type*) [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) :
    0 < Nat.card {f : Polynomial F // f.Monic ∧ f.natDegree = e ∧ Squarefree f} := by
  sorry

/-! ## Leg 2 — degree-1 residuals are separable outright -/

/-- KA6b1 (degree-1 leg): every degree-1 monic over a field is separable
(hence squarefree — `Polynomial.Separable.squarefree` closes the consumer
form).  deps: —.  Sketch: f monic of natDegree 1 has derivative 1;
IsCoprime f 1.  (Monicity is not strictly needed over a field but is the
shape the residual reads deliver — kept per the blueprint text "degree-1
monics separable".) -/
theorem ka6b1_degree_one_separable {F : Type*} [Field F]
    (f : Polynomial F) (hm : f.Monic) (hf : f.natDegree = 1) :
    f.Separable := by
  sorry

/-! ## Leg 3 — the a = 1 anchored mechanism -/

/-- KA6b1 (a = 1 leg): z·(squarefree cofactor with z ∤ cofactor) is
squarefree.  deps: —.  Sketch: X is prime in F[z]; a product of coprime
squarefree factors is squarefree (X ∤ c gives IsCoprime X c over the PID/
Bézout field-polynomial ring; then `Squarefree.mul` along coprimality, X
itself squarefree as a prime). -/
theorem ka6b1_X_mul_squarefree {F : Type*} [Field F]
    {c : Polynomial F} (hc : Squarefree c) (hz : ¬ (X : Polynomial F) ∣ c) :
    Squarefree ((X : Polynomial F) * c) := by
  sorry

/-! ## Leg 4 — the compiled impossibility at a ≥ 2 (the F2 fact) -/

/-- KA6b1 (a ≥ 2 leg, COMPILED IMPOSSIBILITY — stated positively so no
prover re-attempts the dead route): for a ≥ 2 no polynomial of the form
z^a·c is squarefree, REGARDLESS of the cofactor c (including c = 0: the zero
polynomial is not squarefree).  deps: —.  Sketch: X·X = X² ∣ X^a ∣ X^a·c and
X is not a unit; c = 0 is `not_squarefree_zero`.  This is the §3.A (1d)
a ≥ 2 verdict: the squarefree-residual exit mechanism is ABSENT at deep
anchors — KA6b2 must route those states through the cofactor criterion or
the class-level escape (KA2c). -/
theorem ka6b1_anchor_not_squarefree {F : Type*} [Field F]
    (a : ℕ) (ha : 2 ≤ a) (c : Polynomial F) :
    ¬ Squarefree ((X : Polynomial F) ^ a * c) := by
  sorry

end LeanUrat.Kernels
