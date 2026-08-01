/-
BP_IV §1.3 — `KCount.lean` (ROOT Step 15, the Smith-profile fiber count + (SIB)).
Units landed in this file so far: K0a (`zmodVal`), K0b (`minVal` + the three
valuation laws: `zmodVal_add_ge_min`, `zmodVal_pow_mul_ge`, and the
finite-difference factorization transport `minVal_polyMap_sub_ge`), K6
(`kcount_guard_range` + the `e_max`-sup packaging `kcount_guard_range_sup`),
K3a (`card_singleCoordSubgroup` + the `min`-exponent form
`card_singleCoordSubgroup_min`), K3b (`card_smithSubgroup`, the product form
over `Fin n`), K7a (`prod_add_sub_prod` + `prod_add_sub_prod_split`, the
subset product expansion), K7b (`prod_pow_mul_of_two_le_card` +
`quadRemainder_pow_extraction` + `prod_add_sub_prod_split_pow`, the p^{2τ}
extraction Q(p^τ b) = p^{2τ} Q̃(b)), K2 (`bijective_of_injective_finVec`,
the `Finite.injective_iff_bijective` cite unit).
Pending (later waves, per BP_IV §4): K1, K4–K8a, the fiber chart K7c,
and the (SIB) product law.

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

/-! ### K6: the guard range (O-10 §3 Theorem 1(ii), the D-8 guard range) -/

/-- K6 (O-10 §3 Theorem 1(ii), the D-8 guard range): once `M ≥ e_max`
    (per-coordinate form: every Smith exponent `e i ≤ M`), the truncated
    exponent sum `s(M) := Σ_i min(e_i, M)` equals `ρ` — the Lemma-2 quantity
    `ρ = Σ_i e_i`, carried here as the named hypothesis `hρ`.  Pure Finset
    arithmetic; with K5 (`kcount_fiber_card`) this is the `p^ρ` clause. -/
theorem kcount_guard_range {n M ρ : ℕ} (e : Fin n → ℕ)
    (hmax : ∀ i, e i ≤ M) (hρ : ∑ i, e i = ρ) :
    ∑ i, min (e i) M = ρ := by
  rw [← hρ]
  exact Finset.sum_congr rfl fun i _ => min_eq_left (hmax i)

/-- K6, literal `e_max` packaging: the guard hypothesis as
    `e_max := Finset.univ.sup e ≤ M`. -/
theorem kcount_guard_range_sup {n M ρ : ℕ} (e : Fin n → ℕ)
    (hmax : Finset.univ.sup e ≤ M) (hρ : ∑ i, e i = ρ) :
    ∑ i, min (e i) M = ρ :=
  kcount_guard_range e
    (fun i => le_trans (Finset.le_sup (Finset.mem_univ i)) hmax) hρ

/-! ### K3a (BP_IV §2 K-table; O-10 §3 Step 4): single-coordinate subgroup card

`#(p^a · ZMod(p^M)) = p^(M−a)`: the multiples of `p^a` in `ZMod (p^M)`, stated
as the divisibility subtype whose per-coordinate form K3b's
`card_smithSubgroup` consumes (`(p : ZMod (p^M))^(M − e i) ∣ c i`).
Truncated ℕ-subtraction throughout: for `a ≥ M` the subgroup is `{0}` and
both sides are `1`, so the count law is unconditional in `a`. -/

/-- K3a, main case `a ≤ M`: the multiples of `p^a` in `ZMod (p^M)` number
    `p^(M−a)`, via the explicit chart `Fin (p^(M−a)) → {x // p^a ∣ x}`,
    `k ↦ p^a·k` (a bijection: injective by mod-`p^M` size bounds, surjective
    by the `pow_dvd_iff_dvd_val` bridge). -/
theorem card_singleCoordSubgroup_of_le {p M a : ℕ} [Fact p.Prime] (ha : a ≤ M) :
    Nat.card {x : ZMod (p ^ M) // (p : ZMod (p ^ M)) ^ a ∣ x} = p ^ (M - a) := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsplit : p ^ a * p ^ (M - a) = p ^ M := by
    rw [← pow_add, Nat.add_sub_cancel' ha]
  have key : Function.Bijective
      (fun k : Fin (p ^ (M - a)) =>
        (⟨((p ^ a * (k : ℕ) : ℕ) : ZMod (p ^ M)), by
            push_cast
            exact dvd_mul_right _ _⟩ :
          {x : ZMod (p ^ M) // (p : ZMod (p ^ M)) ^ a ∣ x})) := by
    constructor
    · intro k k' hkk'
      have h1 : ((p ^ a * (k : ℕ) : ℕ) : ZMod (p ^ M))
          = ((p ^ a * (k' : ℕ) : ℕ) : ZMod (p ^ M)) := Subtype.ext_iff.1 hkk'
      have hval := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at hval
      have hklt : p ^ a * (k : ℕ) < p ^ M := by
        rw [← hsplit]
        exact mul_lt_mul_of_pos_left k.isLt (pow_pos hp a)
      have hk'lt : p ^ a * (k' : ℕ) < p ^ M := by
        rw [← hsplit]
        exact mul_lt_mul_of_pos_left k'.isLt (pow_pos hp a)
      rw [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hk'lt] at hval
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left (pow_pos hp a) hval)
    · rintro ⟨x, hx⟩
      obtain ⟨m, hm⟩ := (pow_dvd_iff_dvd_val ha x).1 hx
      have hmlt : m < p ^ (M - a) := by
        have hlt : p ^ a * m < p ^ M := hm ▸ x.val_lt
        rw [← hsplit] at hlt
        exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
      refine ⟨⟨m, hmlt⟩, ?_⟩
      apply Subtype.ext
      change ((p ^ a * m : ℕ) : ZMod (p ^ M)) = x
      rw [← hm, ZMod.natCast_rightInverse x]
  rw [← Nat.card_congr (Equiv.ofBijective _ key), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- K3a (BP_IV §2 K-table; O-10 §3 Step 4): single-coordinate subgroup count —
    `#(p^a · ZMod(p^M)) = p^(M−a)` (truncated subtraction; unconditional
    in `a`, since at `a ≥ M` both sides collapse to `1`). -/
theorem card_singleCoordSubgroup {p M : ℕ} [Fact p.Prime] (a : ℕ) :
    Nat.card {x : ZMod (p ^ M) // (p : ZMod (p ^ M)) ^ a ∣ x} = p ^ (M - a) := by
  by_cases ha : a ≤ M
  · exact card_singleCoordSubgroup_of_le ha
  · have ha' : M < a := Nat.lt_of_not_le ha
    haveI : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
    have h0 : (p : ZMod (p ^ M)) ^ a = 0 := by
      have hM0 : (p : ZMod (p ^ M)) ^ M = 0 := by
        have hcast : ((p ^ M : ℕ) : ZMod (p ^ M)) = 0 := ZMod.natCast_self _
        push_cast at hcast
        exact hcast
      calc (p : ZMod (p ^ M)) ^ a
          = (p : ZMod (p ^ M)) ^ M * (p : ZMod (p ^ M)) ^ (a - M) := by
            rw [← pow_add, Nat.add_sub_cancel' ha'.le]
        _ = 0 := by rw [hM0, zero_mul]
    have hMa : M - a = 0 := Nat.sub_eq_zero_of_le ha'.le
    simp only [h0, zero_dvd_iff, hMa, pow_zero]
    exact Nat.card_eq_one_iff_unique.2
      ⟨⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩, ⟨⟨0, rfl⟩⟩⟩

/-- K3a in the exact exponent form K3b consumes per coordinate:
    `#{x // p^(M−e) ∣ x} = p^(min e M)` (the `M − (M − e) = min e M`
    truncated-subtraction collapse, matching `card_smithSubgroup`'s RHS). -/
theorem card_singleCoordSubgroup_min {p M : ℕ} [Fact p.Prime] (e : ℕ) :
    Nat.card {x : ZMod (p ^ M) // (p : ZMod (p ^ M)) ^ (M - e) ∣ x}
      = p ^ (min e M) := by
  rw [card_singleCoordSubgroup (M - e)]
  congr 1
  omega

/-- K3 = K3b (BP_IV §1.3; O-10 §3 Step 4): the target subgroup count —
    `#{c | ∀ i, p^(M − e_i) ∣ c_i} = p^(Σ_i min(e_i, M)) = p^(s M)`.
    Product of K3a over `Fin n`: coordinatewise chart
    `Equiv.subtypePiEquivPi`, then `Nat.card_pi` and
    `card_singleCoordSubgroup_min` per factor. -/
theorem card_smithSubgroup {p M n : ℕ} [Fact p.Prime] (e : Fin n → ℕ) :
    Nat.card {c : Fin n → ZMod (p ^ M) //
      ∀ i, (p : ZMod (p ^ M)) ^ (M - e i) ∣ c i} = p ^ (∑ i, min (e i) M) := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
      (p := fun i (x : ZMod (p ^ M)) => (p : ZMod (p ^ M)) ^ (M - e i) ∣ x)),
    Nat.card_pi]
  simp only [card_singleCoordSubgroup_min]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-! ### K7a: the subset product expansion (O-10 §3 Step 1)

`Π_j (h_j + a_j) − Π_j h_j = Σ_{S ⊆ s, |S| ≥ 1} (Π_{j∈S} a_j) · (Π_{i∉S} h_i)`
via Mathlib `Finset.prod_add`, then the `|S| = 1` vs `|S| ≥ 2` split: the
singleton terms form the linear (Jacobian) part `Φ_h(a)` and the `|S| ≥ 2`
tail is the quadratic remainder `Q(a)` that K7b feeds the `p^{2τ}` extraction.
Stated over an arbitrary commutative ring so K7b/K7c can consume it at
`ℤ_p`-polynomial coefficients.  (BP_IV §1.3 K7 doc + §2 K-table row K7a; the
blueprint displays no Lean block for K7a — the statements below transcribe
the table row's identity.) -/

section K7a

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- K7a (full expansion): `Π (h + a) − Π h` is the sum over *nonempty* subsets
    `S ⊆ s` of `(Π_{j∈S} a_j) · (Π_{i∉S} h_i)`. -/
theorem prod_add_sub_prod (s : Finset ι) (h a : ι → R) :
    ∏ j ∈ s, (h j + a j) - ∏ j ∈ s, h j
      = ∑ S ∈ s.powerset.filter (fun S => S.Nonempty),
          (∏ j ∈ S, a j) * ∏ i ∈ s \ S, h i := by
  have hexp : ∏ j ∈ s, (h j + a j)
      = ∑ S ∈ s.powerset, (∏ j ∈ S, a j) * ∏ i ∈ s \ S, h i := by
    rw [Finset.prod_congr rfl fun j _ => add_comm (h j) (a j), Finset.prod_add]
  have hempty : s.powerset.filter (fun S => ¬ S.Nonempty) = {∅} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.not_nonempty_iff_eq_empty, Finset.mem_singleton]
    constructor
    · exact fun ht => ht.2
    · rintro rfl
      exact ⟨Finset.empty_subset s, rfl⟩
  rw [hexp, ← Finset.sum_filter_add_sum_filter_not s.powerset (fun S => S.Nonempty),
    hempty, Finset.sum_singleton, Finset.prod_empty, Finset.sdiff_empty, one_mul,
    add_sub_cancel_right]

/-- K7a (the `|S| = 1` vs `|S| ≥ 2` split): the singleton subsets contribute
    the linear part `Σ_{j∈s} a_j · Π_{i∈s, i≠j} h_i`; the `|S| ≥ 2` tail is
    the quadratic remainder `Q(a)` consumed by K7b. -/
theorem prod_add_sub_prod_split (s : Finset ι) (h a : ι → R) :
    ∏ j ∈ s, (h j + a j) - ∏ j ∈ s, h j
      = (∑ j ∈ s, a j * ∏ i ∈ s.erase j, h i)
        + ∑ S ∈ s.powerset.filter (fun S => 2 ≤ S.card),
            (∏ j ∈ S, a j) * ∏ i ∈ s \ S, h i := by
  rw [prod_add_sub_prod]
  have hsplit : s.powerset.filter (fun S => S.Nonempty)
      = s.powerset.filter (fun S => S.card = 1)
        ∪ s.powerset.filter (fun S => 2 ≤ S.card) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr fun t _ => ?_
    rw [← Finset.one_le_card]
    omega
  have hdisj : Disjoint (s.powerset.filter fun S => S.card = 1)
      (s.powerset.filter fun S => 2 ≤ S.card) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    rw [Finset.mem_filter] at ht ht'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  rw [← Finset.powersetCard_eq_filter, Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [Finset.erase_eq]

end K7a

/-! ### K7b: the `p^{2τ}` extraction (O-10 §3 Step 1)

Substituting `a_j = p^τ b_j` into K7a's quadratic remainder
`Q(a) = Σ_{S, |S| ≥ 2} (Π_{j∈S} a_j) · (Π_{i∉S} h_i)` factors `p^{τ|S|}` out
of each subset term; since `|S| ≥ 2` this yields `Q(p^τ b) = p^{2τ} Q̃(b)`
with `Q̃(b) := Σ_{|S|≥2} p^{τ(|S|−2)} (Π_{j∈S} b_j) · (Π_{i∉S} h_i)` — every
coefficient a *nonnegative* power `p^{τ(|S|−2)}`, which is the "Q̃ has
ℤ_p-coefficients" clause at `R = ℤ_p`.  Stated over an arbitrary commutative
ring with an arbitrary scaling element `π` (specialized to `π = (p : ℤ_p)` by
K7c), matching K7a's generality.  (BP_IV §2 K-table row K7b + §1.3 K7 doc;
the blueprint displays no Lean block for K7b — the statements below
transcribe the table row's identity `Q(p^τ b) = p^{2τ} Q̃(b)`.) -/

section K7b

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- K7b, per-subset factor law: on a subset `S` with `|S| ≥ 2`, substituting
    `π^τ · b_j` for the increments factors the subset product as
    `π^{τ|S|} Π b_j = π^{2τ} · π^{τ(|S|−2)} Π b_j`. -/
theorem prod_pow_mul_of_two_le_card (S : Finset ι) (b : ι → R) (π : R) (τ : ℕ)
    (hS : 2 ≤ S.card) :
    ∏ j ∈ S, π ^ τ * b j
      = π ^ (2 * τ) * (π ^ (τ * (S.card - 2)) * ∏ j ∈ S, b j) := by
  have hexp : τ * S.card = 2 * τ + τ * (S.card - 2) :=
    calc τ * S.card = τ * (2 + (S.card - 2)) := by rw [Nat.add_sub_cancel' hS]
      _ = 2 * τ + τ * (S.card - 2) := by ring
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hexp, pow_add,
    mul_assoc]

/-- K7b (BP_IV §2 K-table; O-10 §3 Step 1): the `p^{2τ}` extraction —
    substituting `a_j = π^τ b_j` into the quadratic remainder (the `|S| ≥ 2`
    tail of K7a's `prod_add_sub_prod_split`) gives `Q(π^τ b) = π^{2τ} Q̃(b)`,
    where `Q̃(b) = Σ_{|S|≥2} π^{τ(|S|−2)} (Π_{j∈S} b_j) · (Π_{i∉S} h_i)` has
    coefficients in the base ring (nonnegative `π`-powers: the
    "Q̃ ℤ_p-coefficients" clause). -/
theorem quadRemainder_pow_extraction (s : Finset ι) (h b : ι → R) (π : R) (τ : ℕ) :
    ∑ S ∈ s.powerset.filter (fun S => 2 ≤ S.card),
        (∏ j ∈ S, π ^ τ * b j) * ∏ i ∈ s \ S, h i
      = π ^ (2 * τ) *
          ∑ S ∈ s.powerset.filter (fun S => 2 ≤ S.card),
            π ^ (τ * (S.card - 2)) * (∏ j ∈ S, b j) * ∏ i ∈ s \ S, h i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_filter] at hS
  rw [prod_pow_mul_of_two_le_card S b π τ hS.2]
  ring

/-- K7b → K7c packaging: K7a's split at `a = π^τ b` with the `π^{2τ}`
    extraction applied — `Π(h + π^τ b) − Π h = π^τ Φ_h(b) + π^{2τ} Q̃(b)`,
    the displayed form of O-10 §3 Step 1 that the fiber condition (⋆)
    divides by `π^τ`. -/
theorem prod_add_sub_prod_split_pow (s : Finset ι) (h b : ι → R) (π : R) (τ : ℕ) :
    ∏ j ∈ s, (h j + π ^ τ * b j) - ∏ j ∈ s, h j
      = π ^ τ * (∑ j ∈ s, b j * ∏ i ∈ s.erase j, h i)
        + π ^ (2 * τ) *
            ∑ S ∈ s.powerset.filter (fun S => 2 ≤ S.card),
              π ^ (τ * (S.card - 2)) * (∏ j ∈ S, b j) * ∏ i ∈ s \ S, h i := by
  rw [prod_add_sub_prod_split s h (fun j => π ^ τ * b j),
    quadRemainder_pow_extraction s h b π τ]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => by ring

end K7b

/-! ### K2: injective ⇒ bijective on the finite vector space (BP_IV §1.3 + §2 K-table)

The blueprint displays no Lean block for K2 — the §1.3 entry is a doc comment
(transcribed verbatim as the docstring below) and the §2 K-table row reads
"injective ⇒ bijective (cite) | `Finite.injective_iff_bijective`".  Stated
generically in the self-map `T` of the finite vector space `Fin n → ZMod (p^M)`
so that K5 can instantiate it at K1's perturbed-identity map (the K1 unit has
not yet landed; per the wave plan K1 stays a pure valuation argument and the
finiteness upgrade lives here). -/

section K2

/-- K2: injective ⇒ bijective on the finite vector space (Mathlib
    `Finite.injective_iff_bijective` — a one-line cite unit, kept separate so K1
    stays a pure valuation argument). -/
theorem bijective_of_injective_finVec {p M n : ℕ} [Fact p.Prime]
    {T : (Fin n → ZMod (p ^ M)) → (Fin n → ZMod (p ^ M))}
    (hT : Function.Injective T) : Function.Bijective T := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
  exact Finite.injective_iff_bijective.mp hT

end K2

end LeanUrat.Scaffold
