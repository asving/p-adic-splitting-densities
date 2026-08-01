/-
BP_IV §1.3 — `KCount.lean` (ROOT Step 15, the Smith-profile fiber count + (SIB)).
Units landed in this file so far: K0a (`zmodVal`).
Pending (later waves, per BP_IV §4): K0b (`minVal` + the three valuation laws),
K1–K8a, the fiber chart K7*, and the (SIB) product law.

* Blueprint: `lean/blueprints/BP_IV.md` §1.3 (statement transcribed VERBATIM).
* Math source of record: `lean/notes/openmath/O10_phaseB_attempt_rev2.md` §3
  Step 3 (valuation conventions), via ROOT §2 Step 15.
* Convention: `v(0) = M` (the truncation of `v_p(0) = ∞`), matching the corpus
  precedent `PadicLift.zmodValuation` (`LeanUrat/OM/PadicLift.lean`).
-/
import Mathlib

namespace LeanUrat.Scaffold

/-- K0: truncated valuation on ZMod (p^M) vectors: v(x) := min(v_p(lift x), M),
    minVal over coordinates; the three laws the absorption argument needs
    (v(x+y) ≥ min, v(p^a·x) ≥ min(a + v x, M), finite-difference factorization
    transport: polynomial maps are v-Lipschitz). -/
noncomputable def zmodVal {p M : ℕ} [Fact p.Prime] (x : ZMod (p ^ M)) : ℕ :=
  if x = 0 then M else min (padicValNat p x.val) M

/-! ### K0a spec lemmas (definitional pins for K0b's laws) -/

@[simp] theorem zmodVal_zero {p M : ℕ} [Fact p.Prime] :
    zmodVal (0 : ZMod (p ^ M)) = M := by
  simp [zmodVal]

theorem zmodVal_of_ne_zero {p M : ℕ} [Fact p.Prime] {x : ZMod (p ^ M)}
    (hx : x ≠ 0) : zmodVal x = min (padicValNat p x.val) M := by
  simp [zmodVal, hx]

theorem zmodVal_le {p M : ℕ} [Fact p.Prime] (x : ZMod (p ^ M)) :
    zmodVal x ≤ M := by
  unfold zmodVal
  split
  · exact le_rfl
  · exact min_le_right _ _

end LeanUrat.Scaffold
