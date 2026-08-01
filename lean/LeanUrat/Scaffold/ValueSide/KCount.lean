/-
BP_IV §1.3 — `KCount.lean` (ROOT Step 15, the Smith-profile fiber count + (SIB)).
Units landed in this file so far: K0a (`zmodVal`), K0b (`minVal` + the three
valuation laws: `zmodVal_add_ge_min`, `zmodVal_pow_mul_ge`, and the
finite-difference factorization transport `minVal_polyMap_sub_ge`).
Pending (later waves, per BP_IV §4): K1–K8a, the fiber chart K7*, and the
(SIB) product law.

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

/-! ### K0b divisibility bridge: `k ≤ zmodVal x ↔ p^k ∣ x` (for `k ≤ M`)

All three K0 laws are proved through this bridge, which converts truncated
valuation bounds into `ZMod (p^M)` divisibilities and back. -/

/-- `p^k ∣ x` in `ZMod (p^M)` iff `p^k ∣ x.val` in `ℕ`, for `k ≤ M`. -/
theorem pow_dvd_iff_dvd_val {p M k : ℕ} [Fact p.Prime] (hk : k ≤ M)
    (x : ZMod (p ^ M)) : (p : ZMod (p ^ M)) ^ k ∣ x ↔ p ^ k ∣ x.val := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
  constructor
  · rintro ⟨y, rfl⟩
    have hcast : (p : ZMod (p ^ M)) ^ k * y = ((p ^ k * y.val : ℕ) : ZMod (p ^ M)) := by
      push_cast
      rw [ZMod.natCast_rightInverse y]
    rw [hcast, ZMod.val_natCast]
    exact (Nat.dvd_mod_iff (pow_dvd_pow p hk)).2 (dvd_mul_right _ _)
  · rintro ⟨m, hm⟩
    have hx : x = ((p ^ k * m : ℕ) : ZMod (p ^ M)) := by
      rw [← hm, ZMod.natCast_rightInverse x]
    rw [hx]
    push_cast
    exact dvd_mul_right _ _

/-- The bridge: for `k ≤ M`, the truncated valuation is `≥ k` iff `p^k ∣ x`. -/
theorem le_zmodVal_iff {p M k : ℕ} [Fact p.Prime] (hk : k ≤ M)
    (x : ZMod (p ^ M)) : k ≤ zmodVal x ↔ (p : ZMod (p ^ M)) ^ k ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using hk
  · have hval : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).1 h)
    rw [zmodVal_of_ne_zero hx, le_min_iff, pow_dvd_iff_dvd_val hk,
      padicValNat_dvd_iff_le hval]
    exact ⟨And.left, fun h => ⟨h, hk⟩⟩

/-- `p^(zmodVal x) ∣ x` — the valuation's defining divisibility. -/
theorem pow_zmodVal_dvd {p M : ℕ} [Fact p.Prime] (x : ZMod (p ^ M)) :
    (p : ZMod (p ^ M)) ^ zmodVal x ∣ x :=
  (le_zmodVal_iff (zmodVal_le x) x).1 le_rfl

/-! ### K0b law 1: `v(x + y) ≥ min (v x) (v y)` -/

theorem zmodVal_add_ge_min {p M : ℕ} [Fact p.Prime] (x y : ZMod (p ^ M)) :
    zmodVal (x + y) ≥ min (zmodVal x) (zmodVal y) := by
  rw [ge_iff_le, le_zmodVal_iff ((min_le_left _ _).trans (zmodVal_le x))]
  exact dvd_add
    ((pow_dvd_pow _ (min_le_left _ _)).trans (pow_zmodVal_dvd x))
    ((pow_dvd_pow _ (min_le_right _ _)).trans (pow_zmodVal_dvd y))

/-! ### K0b law 2: `v(p^a · x) ≥ min (a + v x) M` -/

theorem zmodVal_pow_mul_ge {p M : ℕ} [Fact p.Prime] (a : ℕ) (x : ZMod (p ^ M)) :
    zmodVal ((p : ZMod (p ^ M)) ^ a * x) ≥ min (a + zmodVal x) M := by
  rw [ge_iff_le, le_zmodVal_iff (min_le_right _ _)]
  refine (pow_dvd_pow _ (min_le_left _ _)).trans ?_
  rw [pow_add]
  exact mul_dvd_mul_left _ (pow_zmodVal_dvd x)

/-! ### K0b: `minVal`, the coordinatewise minimum valuation -/

/-- K0b: minimum truncated valuation over the coordinates of a vector
    (seeded at `M`, the truncation top, so `minVal = M` on the empty index
    type — the convention matching `zmodVal 0 = M`). -/
noncomputable def minVal {p M n : ℕ} [Fact p.Prime] (c : Fin n → ZMod (p ^ M)) : ℕ :=
  Finset.univ.fold min M fun i => zmodVal (c i)

theorem minVal_le {p M n : ℕ} [Fact p.Prime] (c : Fin n → ZMod (p ^ M)) :
    minVal c ≤ M :=
  (Finset.fold_min_le _).2 (Or.inl le_rfl)

theorem minVal_le_zmodVal {p M n : ℕ} [Fact p.Prime] (c : Fin n → ZMod (p ^ M))
    (i : Fin n) : minVal c ≤ zmodVal (c i) :=
  (Finset.fold_min_le _).2 (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)

theorem le_minVal {p M n k : ℕ} [Fact p.Prime] {c : Fin n → ZMod (p ^ M)}
    (hkM : k ≤ M) (h : ∀ i, k ≤ zmodVal (c i)) : k ≤ minVal c :=
  (Finset.le_fold_min _).2 ⟨hkM, fun i _ => h i⟩

/-- `p^(minVal (c - c')) ∣ c i - c' i` for every coordinate `i`. -/
theorem pow_minVal_dvd_sub {p M n : ℕ} [Fact p.Prime]
    (c c' : Fin n → ZMod (p ^ M)) (i : Fin n) :
    (p : ZMod (p ^ M)) ^ minVal (c - c') ∣ c i - c' i := by
  have h := minVal_le_zmodVal (c - c') i
  rw [Pi.sub_apply] at h
  exact (le_zmodVal_iff (minVal_le _) _).1 h

/-! ### K0b law 3: finite-difference factorization transport
    (polynomial maps are `v`-Lipschitz) -/

/-- Divisibility core of the transport: for any polynomial `P` over
    `ZMod (p^M)`, the evaluation difference `P(c) − P(c')` is divisible by
    `p^(minVal (c − c'))` (the finite-difference factorization
    `P(c) − P(c') = Σᵢ (cᵢ − c'ᵢ)·Gᵢ(c, c')`, run as a polynomial induction). -/
theorem pow_minVal_dvd_eval_sub {p M n : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod (p ^ M))) (c c' : Fin n → ZMod (p ^ M)) :
    (p : ZMod (p ^ M)) ^ minVal (c - c') ∣
      MvPolynomial.eval c P - MvPolynomial.eval c' P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    have hsplit : MvPolynomial.eval c (P + Q) - MvPolynomial.eval c' (P + Q)
        = (MvPolynomial.eval c P - MvPolynomial.eval c' P)
          + (MvPolynomial.eval c Q - MvPolynomial.eval c' Q) := by
      simp only [map_add]; ring
    rw [hsplit]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    have hsplit : MvPolynomial.eval c (P * MvPolynomial.X i)
          - MvPolynomial.eval c' (P * MvPolynomial.X i)
        = (MvPolynomial.eval c P - MvPolynomial.eval c' P) * c i
          + MvPolynomial.eval c' P * (c i - c' i) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    rw [hsplit]
    exact dvd_add (hP.mul_right _) ((pow_minVal_dvd_sub c c' i).mul_left _)

/-- Scalar form of law 3: `v(P(c) − P(c')) ≥ minVal (c − c')`. -/
theorem zmodVal_eval_sub_ge {p M n : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod (p ^ M))) (c c' : Fin n → ZMod (p ^ M)) :
    zmodVal (MvPolynomial.eval c P - MvPolynomial.eval c' P) ≥ minVal (c - c') := by
  rw [ge_iff_le, le_zmodVal_iff (minVal_le _)]
  exact pow_minVal_dvd_eval_sub P c c'

/-- K0b law 3 (the transport K1 consumes): a polynomial map
    `c ↦ (i ↦ (S i)(c))` is `v`-Lipschitz —
    `minVal (S(c) − S(c')) ≥ minVal (c − c')`. -/
theorem minVal_polyMap_sub_ge {p M n : ℕ} [Fact p.Prime]
    (S : Fin n → MvPolynomial (Fin n) (ZMod (p ^ M)))
    (c c' : Fin n → ZMod (p ^ M)) :
    minVal ((fun i => MvPolynomial.eval c (S i)) - fun i => MvPolynomial.eval c' (S i))
      ≥ minVal (c - c') := by
  refine le_minVal (minVal_le _) fun i => ?_
  rw [Pi.sub_apply]
  exact zmodVal_eval_sub_ge (S i) c c'

end LeanUrat.Scaffold
