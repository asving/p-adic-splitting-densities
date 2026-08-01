/-
BP_IV §1.3 — `KCount.lean` (ROOT Step 15, the Smith-profile fiber count + (SIB)).
Units landed in this file so far: K0a (`zmodVal`), K0b (`minVal` + the three
valuation laws: `zmodVal_add_ge_min`, `zmodVal_pow_mul_ge`, and the
finite-difference factorization transport `minVal_polyMap_sub_ge`), K1
(`newton_absorption_injective` + helpers `zmodVal_neg`, `minVal_sub_comm`,
`minVal_ge_of_contraction`, `eq_zero_of_minVal_ge`), K6
(`kcount_guard_range` + the `e_max`-sup packaging `kcount_guard_range_sup`),
K3a (`card_singleCoordSubgroup` + the `min`-exponent form
`card_singleCoordSubgroup_min`), K3b (`card_smithSubgroup`, the product form
over `Fin n`), K7a (`prod_add_sub_prod` + `prod_add_sub_prod_split`, the
subset product expansion), K7b (`prod_pow_mul_of_two_le_card` +
`quadRemainder_pow_extraction` + `prod_add_sub_prod_split_pow`, the p^{2τ}
extraction Q(p^τ b) = p^{2τ} Q̃(b)), K2 (`bijective_of_injective_finVec`,
the `Finite.injective_iff_bijective` cite unit), K4 (`starstar_iff_smithMem`
+ the scalar legs `pow_mul_eq_zero_iff_pow_dvd` / `starstar_vacuous` /
`starstar_iff_pow_dvd`: (⋆⋆)_i ⟺ T(c)_i ≡ 0 mod p^(M−e_i), vacuous at
e_i > M), K8a (the PID Smith-normal-form availability gate: compiling
`#check` + signature pin of `Submodule.smithNormalForm` at repository HEAD),
K10a (`AdaptedCell`, the O-10 §4.1 (A1)–(A3) adapted-cell carrier; its
`MulFiberData` dependency is the K7c-owned carrier structure transcribed
VERBATIM — single copy, DEDUP(K7c) resolved at the declaration; the chart
bijection `fiber_equiv_solutions` is NOT declared), K7c (first split of the
parent glue chain: `monic_sub_monic_degree_lt` + `dvd_coeff_sub_trans` +
`monicLiftEquiv`, the monic-lift parametrization — differences of monics =
degree-< d_j polys, π^τ-divisible coefficients — plus adopted ownership of
the VERBATIM `MulFiberData` carrier), K7d (`dvd_prod_sub_prod`
+ `fiberCond_congr` + `fiberCond_congr_scaled`: the quotient
well-definedness of the chart parametrization — the fiber condition
Π(h+a) ≡ Πh mod π^N depends only on a mod π^N, and only on b mod π^M at
a = π^τ b), K10c (`adaptedCell_domainProduct_card`, the domain-product
cardinality — the K10a clause `domainCount_eq` exposed as the theorem K10
chains with K10b; + the constructor-side identification lemmas
`card_domainProduct` / `card_domainProduct_finset`, `Nat.card_pi` at the
genuine product of factor cells), K9 (`SmithStable`, the exported named
hypothesis row per §2, PLUS the wave-4 constructor
`smithStable_of_detDivisorRows` — O-10 §2 Lemma 2's ρ-separation transport:
minor congruence `dvd_det_sub_det`, determinantal-divisor predicate
`IsDetDivisor` with uniqueness + mod-p^τ transport `IsDetDivisor.of_congr`,
telescoping `smithPartial`; non-vacuity gate `K9Gate.gate_smithStable` over a
nonempty polydisc), K10
partial (`sib_product_law_of_imageCount`, the K10b+K10c combine step with the
missing K10b image law displayed as the binder `himg`; the verbatim
`sib_product_law` display itself is BLOCKED — see below), K10b (the
constant-fiber image theorem, final section: Finset core
`constFiber_image_card` + clauses `constFiber_fiber_nonempty` /
`constFiber_image_eq` / `constFiber_image_card_eq` (the charged O5CountingB
`card_eq_of_injOn_checksum` consumption — image/counting step only, per
REV-2 finding 20) + type level `constFiber_surjective` /
`constFiber_nat_card` + the K10a-keyed `adaptedCell_constFiber_image_card`,
whose count leg is verbatim the `himg` binder of
`sib_product_law_of_imageCount`; K5's exact fiber cardinality enters as the
NAMED binder `hfib` at value `p^(A.sM)` — K5 unlanded at this wave), K8b
(`SmithData`, the U/D/V adapter carrier for the particular Φ matrix over
`ℤ_[p]` — concrete `U`/`V` with two-sided inverse laws, `Fin n` exponent
indexing `exp`, factorization `Φ = U·diag(p^exp)·V` + solved-form
`SmithData.diagonal_eq`; `smithData_exists` instantiates the K8a-pinned
`Submodule.smithNormalForm` at any injective Φ, `smithDataOfInjective`
packages the choice).
REVISION 3 (mop-up adjudications, 2026-08-01 — full record in
`blueprints/BP_IV.md` REVISION 3; pre-revision BLOCKED notes in git history
at 33656d2): K7e LANDED (`fiber_equiv_solutions`, verbatim, over the
repaired carrier — `MulFiberData` gains the `chart` law field; the
pre-revision countermodel `mulFiberDataCounter` is retired, its content
quoted in the REVISION-3 table; the concrete instance builder is NEW queued
unit K7f); K5 LANDED (`kcount_fiber_card`, re-scoped with the named
solution-count binder `hsol` — see its section); K10 LANDED
(`sib_product_law`, re-scoped with the named K10b image-law binder `himg`;
the `K10Probe` countermodel of the binder-free display STANDS as warrant);
K11 LANDED (`EngineSIBRow` authored with the BP_III-owned K-LOC/(I-τ) rows
as opaque Prop parameters, `K3DeltaRow` pattern — see the K11 section at the
end of this file).

* Blueprint: `lean/blueprints/BP_IV.md` §1.3 (statement transcribed VERBATIM).
* Math source of record: `lean/notes/openmath/O10_phaseB_attempt_rev2.md` §3
  Step 3 (valuation conventions), via ROOT §2 Step 15.
* Convention: `v(0) = M` (the truncation of `v_p(0) = ∞`), matching the corpus
  precedent `PadicLift.zmodValuation` (`LeanUrat/OM/PadicLift.lean`).
-/
-- K8a (BP_IV §2 K-table): the PID Smith-normal-form API module, imported
-- explicitly per the unit charge (also reachable through `import Mathlib`).
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib
-- K10b (BP_IV §3 reuse row; REV-2 finding 20): the O5triple Theorem B
-- counting core, cited only for the image/counting step.
import LeanUrat.MovesU.O5CountingB

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

/-! ### K1: Newton absorption (O-10 §3 Step 3)

The `w := minVal δ` contraction: if `T(c) = T(c')` for the perturbed identity
`T(c) := c + p^a·S(c)`, then every coordinate of `δ := c − c'` satisfies
`v(δ_i) ≥ min(M, 1 + w)` (K0b laws 1–2 + the Lipschitz hypothesis `hS`), whence
`w ≥ min(M, 1 + w)`, forcing `w ≥ M` — and `minVal ≥ M` collapses `δ` to `0`
since `p^M = 0` in `ZMod (p^M)`. -/

/-- Negation preserves the truncated valuation (through the K0b divisibility
    bridge — no `val`-level computation needed). -/
theorem zmodVal_neg {p M : ℕ} [Fact p.Prime] (x : ZMod (p ^ M)) :
    zmodVal (-x) = zmodVal x :=
  le_antisymm
    ((le_zmodVal_iff (zmodVal_le _) x).2 (dvd_neg.1 (pow_zmodVal_dvd (-x))))
    ((le_zmodVal_iff (zmodVal_le _) (-x)).2 (dvd_neg.2 (pow_zmodVal_dvd x)))

/-- `minVal` is symmetric in the difference: `minVal (c − c') = minVal (c' − c)`. -/
theorem minVal_sub_comm {p M n : ℕ} [Fact p.Prime] (c c' : Fin n → ZMod (p ^ M)) :
    minVal (c - c') = minVal (c' - c) := by
  unfold minVal
  refine Finset.fold_congr fun i _ => ?_
  rw [Pi.sub_apply, Pi.sub_apply, ← neg_sub (c' i) (c i), zmodVal_neg]

/-- The contraction step of K1: `w ≥ min(1 + w, M)` forces `w ≥ M`
    (`w := minVal δ`). -/
theorem minVal_ge_of_contraction {p M n : ℕ} [Fact p.Prime]
    {δ : Fin n → ZMod (p ^ M)}
    (h : ∀ i, min (1 + minVal δ) M ≤ zmodVal (δ i)) : M ≤ minVal δ := by
  have h1 : min (1 + minVal δ) M ≤ minVal δ := le_minVal (min_le_right _ _) h
  omega

/-- The collapse step of K1: a vector with `minVal ≥ M` is `0`
    (`p^M ∣ δ_i` and `p^M = 0` in `ZMod (p^M)`). -/
theorem eq_zero_of_minVal_ge {p M n : ℕ} [Fact p.Prime]
    {δ : Fin n → ZMod (p ^ M)} (h : M ≤ minVal δ) : δ = 0 := by
  funext i
  have hdvd : (p : ZMod (p ^ M)) ^ M ∣ δ i :=
    (le_zmodVal_iff le_rfl (δ i)).1 (h.trans (minVal_le_zmodVal δ i))
  have hM0 : (p : ZMod (p ^ M)) ^ M = 0 := by
    have hcast : ((p ^ M : ℕ) : ZMod (p ^ M)) = 0 := ZMod.natCast_self _
    push_cast at hcast
    exact hcast
  rw [hM0, zero_dvd_iff] at hdvd
  simpa using hdvd

/-- K1 (Newton absorption, O-10 §3 Step 3): a v-contractive perturbation of the
    identity is injective.  `hS` is the finite-difference Lipschitz law (supplied
    for polynomial maps by K0's third law). -/
theorem newton_absorption_injective {p M n : ℕ} [Fact p.Prime]
    {S : (Fin n → ZMod (p ^ M)) → (Fin n → ZMod (p ^ M))} {a : Fin n → ℕ}
    (ha : ∀ i, 1 ≤ a i)
    (hS : ∀ c c', minVal (S c - S c') ≥ minVal (c - c')) :
    Function.Injective (fun c => c + fun i => (p : ZMod (p ^ M)) ^ a i * S c i) := by
  intro c c' h
  have hδ : ∀ i, (c - c') i = (p : ZMod (p ^ M)) ^ a i * (S c' - S c) i := by
    intro i
    have hi := congrFun h i
    simp only [Pi.add_apply] at hi
    simp only [Pi.sub_apply]
    linear_combination hi
  have hbound : ∀ i, min (1 + minVal (c - c')) M ≤ zmodVal ((c - c') i) := by
    intro i
    rw [hδ i]
    refine le_trans ?_ (zmodVal_pow_mul_ge (a i) ((S c' - S c) i))
    have h1 : minVal (c - c') ≤ zmodVal ((S c' - S c) i) :=
      ((minVal_sub_comm c c').trans_le (hS c' c)).trans
        (minVal_le_zmodVal (S c' - S c) i)
    have h2 : 1 ≤ a i := ha i
    omega
  exact sub_eq_zero.1 (eq_zero_of_minVal_ge (minVal_ge_of_contraction hbound))

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

/-! ### K7c: the monic-lift parametrization (O-10 §3 Steps 1–2)

First split of the parent K7c glue chain (BP_IV §4 wave 3: K7b → K7c (monic
parametrization) → K7d (quotient well-definedness) → K7e
(`fiber_equiv_solutions`)).  O-10 §3 Step 1's opening clause: a general
element of the stratum `A_j(N)` around a member `g` is `g + a` with
`a ∈ (p^τ ℤ/p^N ℤ)[x]_{<d_j}` — the DIFFERENCE of two monic degree-`d_j`
polynomials agreeing with the base `f_j` coefficientwise mod `p^τ` has
degree `< d_j` and `p^τ`-divisible coefficients, and conversely adding such
an increment to a member gives a member.  Stated over an arbitrary
commutative ring with a scaling element `π` (specialized to `ZMod (p^N)`
with `π = p` by the later splits), matching the K7a/K7b/K7d generality.
(BP_IV §2 K-table row K7c + §1.3 K7 doc; the blueprint displays no Lean
block for this SPLIT — the statements below transcribe the K-table row's
"differences of monics = degree-< d_j polys, p^τ-divisible" clause, the
same convention as the K2/K3a/K4/K7a/K7b/K7d units.  The parent unit's
displayed Lean block is `MulFiberData` + `fiber_equiv_solutions`: the
structure stands transcribed VERBATIM below (the K7-carrier section, single
copy per its DEDUP(K7c) note — ownership now discharged by this split);
the theorem `fiber_equiv_solutions` is unit K7e's per §4 wave 3, and §4
forbids statement-only theorem declarations, so it is NOT declared.) -/

section K7c

variable {R : Type*} [CommRing R]

/-- K7c, degree leg: the difference of two monic polynomials of the same
    degree `d` has degree `< d` (the leading terms cancel;
    `Polynomial.degree_sub_lt`). -/
theorem monic_sub_monic_degree_lt {d : ℕ} {g g' : Polynomial R}
    (hg : g.Monic) (hg' : g'.Monic)
    (hgd : g.degree = (d : WithBot ℕ)) (hg'd : g'.degree = (d : WithBot ℕ)) :
    (g' - g).degree < (d : WithBot ℕ) := by
  have hne : g' ≠ 0 := by
    intro h0
    rw [h0, Polynomial.degree_zero] at hg'd
    exact absurd hg'd (by simp)
  have h := Polynomial.degree_sub_lt (hg'd.trans hgd.symm) hne
    (by rw [hg'.leadingCoeff, hg.leadingCoeff])
  rwa [hg'd] at h

/-- K7c, divisibility leg: two polynomials congruent to the same base `f`
    (coefficientwise `c`-divisible differences) have coefficientwise
    `c`-divisible difference — `g' − g = (g' − f) − (g − f)`. -/
theorem dvd_coeff_sub_trans {c : R} {f g g' : Polynomial R}
    (hgf : ∀ k, c ∣ (g - f).coeff k) (hg'f : ∀ k, c ∣ (g' - f).coeff k)
    (k : ℕ) : c ∣ (g' - g).coeff k := by
  have h : g' - g = (g' - f) - (g - f) := by ring
  rw [h, Polynomial.coeff_sub]
  exact dvd_sub (hg'f k) (hgf k)

/-- K7c (BP_IV §2 K-table row K7c, the monic-lift parametrization clause;
    O-10 §3 Step 1 opening): around a fixed member `g` (monic, degree `d`,
    coefficientwise `≡ f` mod `π^τ`), the stratum members are EXACTLY
    `g + a` for increments `a` of degree `< d` with `π^τ`-divisible
    coefficients — subtraction of `g` is a bijection from the stratum onto
    the increment space (specialized by K7d/K7e at `R = ZMod (p^N)`,
    `π = p`, `d = d_j`, base `f = f_j`, where the source subtype is the
    level-`N` stratum `A_j(N)`). -/
noncomputable def monicLiftEquiv (π : R) (τ : ℕ) {d : ℕ} (f g : Polynomial R)
    (hg : g.Monic) (hgd : g.degree = (d : WithBot ℕ))
    (hgf : ∀ k, π ^ τ ∣ (g - f).coeff k) :
    {g' : Polynomial R // g'.Monic ∧ g'.degree = (d : WithBot ℕ) ∧
        ∀ k, π ^ τ ∣ (g' - f).coeff k}
      ≃ {a : Polynomial R // a.degree < (d : WithBot ℕ) ∧
          ∀ k, π ^ τ ∣ a.coeff k} where
  toFun g' := ⟨g'.1 - g,
    monic_sub_monic_degree_lt hg g'.2.1 hgd g'.2.2.1,
    dvd_coeff_sub_trans hgf g'.2.2.2⟩
  invFun a := ⟨g + a.1,
    hg.add_of_left (a.2.1.trans_eq hgd.symm),
    by rw [Polynomial.degree_add_eq_left_of_degree_lt
        (a.2.1.trans_eq hgd.symm), hgd],
    fun k => by
      have h : g + a.1 - f = (g - f) + a.1 := by ring
      rw [h, Polynomial.coeff_add]
      exact dvd_add (hgf k) (a.2.2 k)⟩
  left_inv g' := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)

end K7c

/-! ### K7d: quotient well-definedness of the chart parametrization (O-10 §3 Steps 1–2)

O-10 §3 Step 1 parametrizes a fiber element as `ḡ'_j = ḡ_j + ā_j`, "subject to
`Π_j (h_j + a_j) ≡ Π_j h_j mod p^N` for one (equivalently any) lift `a_j` of
`ā_j` — the condition depends only on `a` mod `p^N`"; the Step-1 close reads
(⋆) "in `b̄ ∈ (ℤ/p^M)`-coefficient vectors", the same well-definedness one
level down at `a = p^τ b`, `M = N − τ`.  K7d is that quotient
well-definedness clause (BP_IV §4 wave 3: "K7d (quotient well-definedness)";
§2 K-table row K7c clause "mod-p^N well-definedness").  Stated over an
arbitrary commutative ring with scaling element `π`, matching K7a/K7b, so K7c
consumes it at `ℤ_p`-polynomial coefficients (`π = (p : ℤ_p)`, where
`p^N ∣ ·` coefficientwise is `p^N ∣ ·` in `ℤ_p[x]`).  (BP_IV §1.3 displays
no Lean block for K7d — the statements below transcribe the table-row clause
and the quoted Step-1 sentence, the same convention as the K2/K3a/K4/K7a/K7b
units above.) -/

section K7d

variable {R : Type*} [CommRing R] {ι : Type*}

/-- K7d core law: congruent factor tuples have congruent products — if
    `d ∣ g_j − g'_j` on all of `s` then `d ∣ Π g − Π g'` (the telescoping
    `g_j·Π − g'_j·Π' = (g_j − g'_j)·Π + g'_j·(Π − Π')`, by induction). -/
theorem dvd_prod_sub_prod (s : Finset ι) (g g' : ι → R) {d : R}
    (hcong : ∀ j ∈ s, d ∣ g j - g' j) :
    d ∣ ∏ j ∈ s, g j - ∏ j ∈ s, g' j := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    have hsplit : g j * ∏ i ∈ s, g i - g' j * ∏ i ∈ s, g' i
        = (g j - g' j) * ∏ i ∈ s, g i
          + g' j * (∏ i ∈ s, g i - ∏ i ∈ s, g' i) := by ring
    rw [hsplit]
    exact dvd_add ((hcong j (Finset.mem_cons_self j s)).mul_right _)
      ((ih fun i hi => hcong i (Finset.mem_cons_of_mem hi)).mul_left _)

/-- K7d (THE quotient well-definedness, O-10 §3 Step 1): the fiber condition
    `Π_j (h_j + a_j) ≡ Π_j h_j mod π^N` depends only on `a` mod `π^N` — it
    holds at one lift of the increment class iff it holds at any other, so
    the K7 chart parametrization descends to classes `ā`. -/
theorem fiberCond_congr (s : Finset ι) (h a a' : ι → R) (π : R) (N : ℕ)
    (hlift : ∀ j ∈ s, π ^ N ∣ a j - a' j) :
    (π ^ N ∣ ∏ j ∈ s, (h j + a j) - ∏ j ∈ s, h j
      ↔ π ^ N ∣ ∏ j ∈ s, (h j + a' j) - ∏ j ∈ s, h j) := by
  have key : π ^ N ∣ ∏ j ∈ s, (h j + a j) - ∏ j ∈ s, (h j + a' j) :=
    dvd_prod_sub_prod s _ _ fun j hj => by
      simpa using hlift j hj
  constructor
  · intro hcond
    have hrw : ∏ j ∈ s, (h j + a' j) - ∏ j ∈ s, h j
        = (∏ j ∈ s, (h j + a j) - ∏ j ∈ s, h j)
          - (∏ j ∈ s, (h j + a j) - ∏ j ∈ s, (h j + a' j)) := by ring
    rw [hrw]
    exact dvd_sub hcond key
  · intro hcond
    have hrw : ∏ j ∈ s, (h j + a j) - ∏ j ∈ s, h j
        = (∏ j ∈ s, (h j + a' j) - ∏ j ∈ s, h j)
          + (∏ j ∈ s, (h j + a j) - ∏ j ∈ s, (h j + a' j)) := by ring
    rw [hrw]
    exact dvd_add hcond key

/-- K7d at the (⋆) reading level (`a = π^τ b`, `N = τ + M`): the fiber
    condition depends only on `b` mod `π^M` — the "solution set of (⋆) in
    `b̄ ∈ (ℤ/p^M)`-coefficient vectors" of O-10 §3 Step 1 is well-defined
    on classes mod `π^M`. -/
theorem fiberCond_congr_scaled (s : Finset ι) (h b b' : ι → R) (π : R)
    (τ M : ℕ) (hlift : ∀ j ∈ s, π ^ M ∣ b j - b' j) :
    (π ^ (τ + M) ∣ ∏ j ∈ s, (h j + π ^ τ * b j) - ∏ j ∈ s, h j
      ↔ π ^ (τ + M) ∣ ∏ j ∈ s, (h j + π ^ τ * b' j) - ∏ j ∈ s, h j) := by
  refine fiberCond_congr s h _ _ π (τ + M) fun j hj => ?_
  have hfac : π ^ τ * b j - π ^ τ * b' j = π ^ τ * (b j - b' j) := by ring
  rw [hfac, pow_add]
  exact mul_dvd_mul_left _ (hlift j hj)

end K7d

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

/-! ### K8a: PID Smith-normal-form availability gate (BP_IV §2 K-table; REV-2 finding 19)

Blueprint §1.3 K8 comment (the unit K8a serves, transcribed verbatim):

    K8 (Lemma 2 half 1): Smith normal form of Φ over ℤ_p exists — transcription
    of Mathlib `Submodule.smithNormalForm` at the matrix of Φ.

The blueprint displays no Lean block for K8a; the §2 K-table row charges this
unit to "import `Mathlib.LinearAlgebra.FreeModule.PID`; use `#check` to record
the exact declaration available at repository HEAD before fixing the adapter
proof", and the §3 Mathlib row requires the "exact declaration name and
arguments" to be captured by a compiling `#check`.  RECORD, at repository HEAD
(Mathlib pinned by this repo's lakefile, module
`Mathlib.LinearAlgebra.FreeModule.PID`, imported explicitly above):

    noncomputable def Submodule.smithNormalForm [Finite ι] (b : Basis ι R M)
        (N : Submodule R M) : Σ n : ℕ, Basis.SmithNormalForm N ι n

with ambient variables `{ι : Type*} {R : Type*} [CommRing R] {M : Type*}
[AddCommGroup M] [Module R M] [IsDomain R] [IsPrincipalIdealRing R]`, where
`Basis` is `Module.Basis` and the return structure is (same module, HEAD name
`Module.Basis.SmithNormalForm`):

    structure Module.Basis.SmithNormalForm (N : Submodule R M) (ι : Type*)
        (n : ℕ) where
      bM  : Basis ι R M
      bN  : Basis (Fin n) R N
      f   : Fin n ↪ ι
      a   : Fin n → R
      snf : ∀ i, (bN i : M) = a i • bM (f i)

K8b consumes this gate: it instantiates the checked declaration at the matrix
of Φ over ℤ_p and exposes the concrete U/D/V data, inverse laws, diagonal
equality, and `Fin n` exponent indexing required by `MulFiberData`; generic
existence alone does not discharge K8.  Neighbouring HEAD declarations K8b may
also draw on (availability confirmed by this import, not pinned here):
`Submodule.exists_smith_normal_form_of_le`, `Submodule.smithNormalFormOfLE`,
`Submodule.smithNormalFormCoeffs`. -/

section K8a

-- The charged availability gate: the exact declaration name at HEAD.
#check @Submodule.smithNormalForm

-- The charged "exact arguments" capture, as a compiling elaboration pin:
-- this `example` fails to compile if the declaration's signature (argument
-- order, instance assumptions, or return type) drifts at a Mathlib bump.
-- (`noncomputable`: the pinned declaration is itself noncomputable.)
noncomputable example {ι : Type*} {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [IsDomain R] [IsPrincipalIdealRing R] [Finite ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    Σ n : ℕ, Module.Basis.SmithNormalForm N ι n :=
  Submodule.smithNormalForm b N

-- Field-level pin of the returned Smith data (the pieces K8b must adapt):
-- bases `bM`/`bN`, the index embedding `f`, the diagonal entries `a`, and
-- the SNF relation `snf`.
example {ι : Type*} {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [IsDomain R] [IsPrincipalIdealRing R] [Finite ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    ∀ i, ((Submodule.smithNormalForm b N).2.bN i : M)
      = (Submodule.smithNormalForm b N).2.a i
          • (Submodule.smithNormalForm b N).2.bM
              ((Submodule.smithNormalForm b N).2.f i) :=
  (Submodule.smithNormalForm b N).2.snf

end K8a

/-! ### K4 (BP_IV §2 K-table; O-10 §3 Step 4): the per-coordinate equivalence

`(⋆⋆)_i ⟺ T(c)_i ≡ 0 mod p^(M−e_i)`; vacuous at `e_i > M`.  Here `(⋆⋆)_i` is
the Smith-diagonalized congruence `p^(e_i)·c_i + p^τ·S_i(c) ≡ 0 mod p^M`
(O-10 §3 Step 2) and `T(c)_i := c_i + p^(τ−e_i)·S_i(c)` is the Step-3
absorption map — K1's perturbed identity at `a i := τ − e i` (`1 ≤ a i` from
(SEP): `τ ≥ ρ + 1 > e_i`).  Proof: factor `p^(e_i)` out of `(⋆⋆)_i`
(`starstar_factor`), then unit-cancel it through the `ZMod (p^M)`
divisibility shuffle `p^e·y = 0 ↔ p^(M−e) ∣ y`
(`pow_mul_eq_zero_iff_pow_dvd`); at `e_i > M` both sides hold identically
(`p^(e_i) = p^τ = 0` and `M − e_i = 0` in truncated subtraction,
`starstar_vacuous`) — matching `min(e_i, M) = M`.  The RHS is verbatim the
K3b membership predicate (`card_smithSubgroup`), so K5 reads the solution
set of `(⋆⋆)` as `T⁻¹(G)`.  (BP_IV §1.3 displays no Lean block for K4 —
the statements below transcribe the §2 K-table row's equivalence, the same
convention as the K2/K3a/K7a/K7b units above.) -/

section K4

variable {p M : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- `p^t = 0` in `ZMod (p^M)` once `t ≥ M` (the truncation collapse both
    K4 legs use). -/
theorem pPow_eq_zero_of_le (t : ℕ) (ht : M ≤ t) :
    (p : ZMod (p ^ M)) ^ t = 0 := by
  have hM0 : (p : ZMod (p ^ M)) ^ M = 0 := by
    have hcast : ((p ^ M : ℕ) : ZMod (p ^ M)) = 0 := ZMod.natCast_self _
    push_cast at hcast
    exact hcast
  exact pow_eq_zero_of_le ht hM0

/-- K4 cancellation core (the "unit-cancel `p^(e_i)`" step): in `ZMod (p^M)`,
    for `e ≤ M`, `p^e·y = 0 ↔ p^(M−e) ∣ y`.  Forward: lift to `ℕ`
    (`p^M ∣ p^e·y.val`), cancel `p^e`, come back through the K0b bridge
    `pow_dvd_iff_dvd_val`; backward: `p^e·p^(M−e) = p^M = 0`. -/
theorem pow_mul_eq_zero_iff_pow_dvd {e : ℕ} (he : e ≤ M) (y : ZMod (p ^ M)) :
    (p : ZMod (p ^ M)) ^ e * y = 0 ↔ (p : ZMod (p ^ M)) ^ (M - e) ∣ y := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
  constructor
  · intro h0
    rw [pow_dvd_iff_dvd_val (Nat.sub_le M e)]
    have hcast : (p : ZMod (p ^ M)) ^ e * y
        = ((p ^ e * y.val : ℕ) : ZMod (p ^ M)) := by
      push_cast
      rw [ZMod.natCast_rightInverse y]
    rw [hcast, ZMod.natCast_eq_zero_iff] at h0
    have h0' : p ^ e * p ^ (M - e) ∣ p ^ e * y.val := by
      rw [← pow_add, Nat.add_sub_cancel' he]
      exact h0
    exact (mul_dvd_mul_iff_left
      (pow_ne_zero e (Fact.out : p.Prime).ne_zero)).1 h0'
  · rintro ⟨z, rfl⟩
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' he,
      pPow_eq_zero_of_le M le_rfl, zero_mul]

omit [Fact p.Prime] in
/-- Factor `p^e` out of `(⋆⋆)`'s LHS: for `e ≤ τ`,
    `p^e·x + p^τ·y = p^e·(x + p^(τ−e)·y)` — the RHS parenthesis is `T` at
    this coordinate. -/
theorem starstar_factor {e τ : ℕ} (heτ : e ≤ τ) (x y : ZMod (p ^ M)) :
    (p : ZMod (p ^ M)) ^ e * x + (p : ZMod (p ^ M)) ^ τ * y
      = (p : ZMod (p ^ M)) ^ e * (x + (p : ZMod (p ^ M)) ^ (τ - e) * y) := by
  rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heτ]

omit [Fact p.Prime] in
/-- K4, vacuous leg (`e_i > M`, stated at its natural scope `M ≤ e ≤ τ`):
    the congruence `(⋆⋆)_i` holds identically — `p^e·x + p^τ·y = 0` since
    both powers collapse in `ZMod (p^M)`. -/
theorem starstar_vacuous {e τ : ℕ} (hMe : M ≤ e) (heτ : e ≤ τ)
    (x y : ZMod (p ^ M)) :
    (p : ZMod (p ^ M)) ^ e * x + (p : ZMod (p ^ M)) ^ τ * y = 0 := by
  rw [pPow_eq_zero_of_le e hMe, pPow_eq_zero_of_le τ (hMe.trans heτ),
    zero_mul, zero_mul, add_zero]

/-- K4, main leg (`e ≤ M`), scalar form: `(⋆⋆)_i ⟺ p^(M−e) ∣ T_i` with
    `T_i = x + p^(τ−e)·y` (`x = c_i`, `y = S_i(c)`).  Unit-cancel `p^e` via
    `starstar_factor` + `pow_mul_eq_zero_iff_pow_dvd`. -/
theorem starstar_iff_pow_dvd {e τ : ℕ} (heM : e ≤ M) (heτ : e ≤ τ)
    (x y : ZMod (p ^ M)) :
    (p : ZMod (p ^ M)) ^ e * x + (p : ZMod (p ^ M)) ^ τ * y = 0
      ↔ (p : ZMod (p ^ M)) ^ (M - e)
          ∣ x + (p : ZMod (p ^ M)) ^ (τ - e) * y := by
  rw [starstar_factor heτ, pow_mul_eq_zero_iff_pow_dvd heM]

/-- K4 (THE per-coordinate equivalence, BP_IV §2 K-table row): under (SEP)'s
    standing `e_i < τ`, for every coordinate `i`,
    `(⋆⋆)_i ⟺ T(c)_i ≡ 0 mod p^(M−e_i)` — with the `e_i > M` leg vacuous on
    both sides (LHS by `starstar_vacuous`, RHS by the truncated-subtraction
    collapse `M − e_i = 0`), matching `min(e_i, M) = M`.  The divisibility RHS
    is verbatim K3b's subgroup-membership predicate at the absorbed vector
    `T(c) = c + p^(τ−e)·S(c)` (K1's perturbed identity with `a i = τ − e i`),
    so the `(⋆⋆)` solution set is exactly `T⁻¹` of K3b's subgroup. -/
theorem starstar_iff_smithMem {n : ℕ} {τ : ℕ}
    (S : (Fin n → ZMod (p ^ M)) → (Fin n → ZMod (p ^ M)))
    (e : Fin n → ℕ) (c : Fin n → ZMod (p ^ M)) (i : Fin n)
    (heτ : e i < τ) :
    (p : ZMod (p ^ M)) ^ e i * c i + (p : ZMod (p ^ M)) ^ τ * S c i = 0
      ↔ (p : ZMod (p ^ M)) ^ (M - e i)
          ∣ c i + (p : ZMod (p ^ M)) ^ (τ - e i) * S c i := by
  by_cases heM : e i ≤ M
  · exact starstar_iff_pow_dvd heM heτ.le (c i) (S c i)
  · have hMe : M ≤ e i := (Nat.lt_of_not_le heM).le
    refine iff_of_true (starstar_vacuous hMe heτ.le _ _) ?_
    rw [Nat.sub_eq_zero_of_le hMe, pow_zero]
    exact one_dvd _

end K4

/-! ### K7 carrier (BP_IV §1.3; owner unit K7c — LANDED; REPAIRED at REVISION 3)

K10a's `toMulFiberData` field consumes the `MulFiberData` carrier.  The
carrier structure below is the §1.3 display PLUS the REVISION-3 `chart` law
field.  **REVISION-3 adjudication record (K7e):** the pre-revision display
(data fields only) made `fiber_equiv_solutions` REFUTABLE — `Fiber`,
`SolutionSet`, `FiberNonempty` were opaque, mutually unrelated fields, and
the compiled countermodel `mulFiberDataCounter` (+
`fiber_equiv_solutions_display_refuted`: `|Fiber| = 1 ≠ 2 = |SolutionSet|`,
`FiberNonempty := True`) is on file in git history (33656d2).  The §1.3 doc
comment PROMISES Φ, its Smith data, and Q on the carrier; the display
dropped every law.  The mop-up architect ruled the CARRIER wrong and enacted
the escalation's candidate fix (a): the chart row
`chart : FiberNonempty → Fiber ≃ SolutionSet` — K7e becomes the projection
theorem below, and the O-10 §3 Steps 1–2 content moves to the concrete
instance builder (NEW queued unit K7f, BP_IV REVISION 3), where the landed
K7a/K7b/K7c/K7d lemmas supply the (⋆)-assembly ingredients.  DEDUP(K7c)
re-pinned to THIS revised text. -/

/-- K7: the fiber chart (O-10 §3 Step 1 + Step 2 packaged): a bijection between a
    nonempty fiber of the level-N multiplication map and the solution set of the
    Smith-diagonalized congruence (⋆⋆).  `MulFiberData` carries: the factor
    polydisc (monic factor degrees d_j, base point, separation level τ with
    (SEP): τ ≥ ρ + 1), the abstract fiber/solution carriers with the
    REVISION-3 `chart` law (the O-10 Steps 1–2 bijection, supplied by the
    concrete instance builder K7f), and the Smith profile `smithExp` (from
    K8).  K7a = the subset product expansion (`Finset.prod_add`);
    K7c = the monic-lift parametrization layer above. -/
structure MulFiberData (p : ℕ) [Fact p.Prime] (n N : ℕ) where
  τ : ℕ
  ρ : ℕ
  τ_sep : ρ + 1 ≤ τ
  FactorPoint : Type
  instFactorPoint : Fintype FactorPoint
  base : FactorPoint
  polydisc : Finset FactorPoint
  Fiber : Type
  instFiber : Fintype Fiber
  FiberNonempty : Prop
  SolutionSet : Type
  instSolutionSet : Fintype SolutionSet
  smithExp : FactorPoint → Fin n → ℕ
  /-- REVISION 3 (the K7e repair): the chart bijection of a nonempty fiber
      onto the (⋆⋆) solution set — O-10 §3 Steps 1–2, discharged by the
      concrete instance builder (queued unit K7f). -/
  chart : FiberNonempty → Fiber ≃ SolutionSet

attribute [instance] MulFiberData.instFactorPoint
attribute [instance] MulFiberData.instFiber
attribute [instance] MulFiberData.instSolutionSet

/-! ### K7e (BP_IV §4 wave 3; PROVED at REVISION 3 over the repaired carrier) -/

/-- K7e (§1.3 statement VERBATIM, now the `chart` projection — see the
    REVISION-3 record in the carrier section header): a nonempty fiber is in
    bijection with the Smith-diagonalized solution set. -/
theorem fiber_equiv_solutions {p n N : ℕ} [Fact p.Prime]
    (F : MulFiberData p n N) (hne : F.FiberNonempty) :
    Nonempty (F.Fiber ≃ F.SolutionSet) :=
  ⟨F.chart hne⟩

/-! ### K10a (BP_IV §2 K-table; O-10 §4.1): the adapted-cell carrier

The (A1)–(A3) clauses of O-10 §4.1 as fields: the factor index type with its
`Fintype` instance (A1: finitely many factor coordinates), the `MulFiberData`
chart at the cell with its nonempty fiber (A2: the cell sits over a nonempty
fiber of the level-N multiplication map), and the domain-product cardinality
law `domainCount_eq` (A3: the domain count is the product of the per-factor
counts).  `cellCount`, `factorCount`, `sM` are the count columns K10b/K10c/K10
relate; the structure itself is pure data + the two displayed clauses —
definition only, per the §2 K-table row (K10a, MECH). -/

/-- K10 (Theorem 2, the adapted-cell (SIB) product law, O-10 §4.2): at an
    `AdaptedCell` (structure carrying the (A1)–(A3) clauses of §4.1 as fields),
    the level-N count of the assembled cell is the product of the per-factor
    counts divided by the K5 fiber size — UNCONDITIONAL in factor coordinates.
    The APPLICATION to engine strata is a separate statement consuming the
    named rows K-LOC and (I-τ) (owner BP_III), displayed as binders. -/
structure AdaptedCell (p n N : ℕ) [Fact p.Prime] where
  Factor : Type
  instFactor : Fintype Factor
  toMulFiberData : MulFiberData p n N
  cellCount : ℕ
  factorCount : Factor → ℕ
  sM : ℕ
  domainCount_eq : Nat.card Factor = ∏ j, factorCount j
  fiber_nonempty : toMulFiberData.FiberNonempty

attribute [instance] AdaptedCell.instFactor

/-! ### K10c (BP_IV §2 K-table; O-10 §4.2): domain-product cardinality

"identify the domain with the product of factor cells".  BP_IV §1.3 displays
no standalone Lean block for K10c; the fenced identity is the K10a clause
`domainCount_eq : Nat.card Factor = ∏ j, factorCount j`, transcribed verbatim
below as the theorem that K10 (`sib_product_law`) chains with K10b's
constant-fiber count — the same table-row-transcription convention as the
K2/K3a/K4/K7a/K7b units above.  The two identification lemmas supply the
constructor side: at a GENUINE product domain — O-10 §4.2's
μ_N^{−1}(Σ) = Π_j C_j, the product of the factor cells C_j ⊆ A_j(N) — the
domain cardinality IS the product of the per-factor counts (`Nat.card_pi`),
which is how a concrete `AdaptedCell` instance discharges its
`domainCount_eq` field. -/

/-- K10c (the fenced domain-product identity, = the K10a clause
    `domainCount_eq` at an arbitrary adapted cell): the domain count is the
    product of the per-factor counts. -/
theorem adaptedCell_domainProduct_card {p n N : ℕ} [Fact p.Prime]
    (A : AdaptedCell p n N) :
    Nat.card A.Factor = ∏ j, A.factorCount j :=
  A.domainCount_eq

/-- K10c, constructor side (the identification itself): a genuine product
    domain `∀ j, C j` — the product of the factor cells — has cardinality
    `∏ j, Nat.card (C j)` (`Nat.card_pi`; no finiteness needed on the cells:
    an infinite factor makes both sides `0`). -/
theorem card_domainProduct {J : Type*} [Fintype J] (C : J → Type*) :
    Nat.card (∀ j, C j) = ∏ j, Nat.card (C j) :=
  Nat.card_pi

/-- K10c, constructor side at O-10's literal shape: factor cells as finite
    subsets `C j ⊆ A j` (Finsets of the ambient level-N factor spaces); the
    product domain `Π_j C_j` counts `∏ j, (C j).card`. -/
theorem card_domainProduct_finset {J : Type*} [Fintype J] {A : J → Type*}
    (C : ∀ j, Finset (A j)) :
    Nat.card (∀ j, {x // x ∈ C j}) = ∏ j, (C j).card := by
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun j _ => by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-! ### K9 named row (BP_IV §1.3; owner unit K9 — exported hypothesis structure)

K9's constancy THEOREM (Smith exponents constant across the ρ-separated
polydisc) is HARD, wave 4.  Per BP_IV §2 ("K9 export[s] named hypothesis
structures until their dedicated constructor proofs land"), the named row
`SmithStable` is transcribed VERBATIM from the §1.3 display — it is the
field-displayed hypothesis K5 and K10 consume; K10's statement does not
elaborate without it.  DEDUP(K9): when K9's constructor lands, keep a single
copy — both must be character-identical to the §1.3 display.  [Wave 4: the
constructor `smithStable_of_detDivisorRows` has LANDED — see the K9 section
at the end of this file; this named row stays the single carrier of the §1.3
display.] -/

/-- K9 (Lemma 2 half 2, HARD, wave 4): the Smith exponents are CONSTANT across
    the ρ-separated polydisc.  Until it lands: the named row `SmithStable F`
    (a field-displayed hypothesis, consumed by K5), mirroring the paper's
    Lemma-2 dependency honestly. -/
structure SmithStable {p n N : ℕ} [Fact p.Prime] (F : MulFiberData p n N) : Prop where
  exponents_const : ∀ h ∈ F.polydisc, F.smithExp h = F.smithExp F.base

/-! ### K5 (BP_IV §1.3 + §2 K-table; RE-SCOPED and PROVED at REVISION 3)

**REVISION-3 adjudication record (K5).**  The §1.3 display
(`kcount_fiber_card (F) (hS : SmithStable F) (hne : F.FiberNonempty) :
Nat.card F.Fiber = p ^ (∑ i, min (F.smithExp F.base i) (N − F.τ))`) was
REFUTABLE over the abstract carrier for the same root cause as K7e/K10: the
carrier's `SolutionSet` and `smithExp` are unrelated fields, so instances
with `|SolutionSet| ≠ p^Σmin` exist even after the `chart` repair.  The
mop-up re-scope adds the ONE missing named binder `hsol` — the solution-set
count, i.e. EXACTLY the K1/K2 ∘ K4 ∘ K3 conclusion at the concrete (⋆⋆)
solution set, which the landed engine of this file proves at concrete data
and the K7f instance builder supplies alongside `chart` (BP_IV REVISION 3;
countermodel warrant recorded there).  `hS` is kept to mirror the displayed
binder list (the `sib_product_law_of_imageCount` precedent): Smith stability
enters when the builder derives `hsol` at non-base polydisc points. -/

/-- K5 (THE K-COUNT, O-10 Theorem 1(i); REVISION-3 scope): every nonempty
    fiber has size exactly p^(s M), M = N − τ — from the chart (K7e) and the
    solution-set count `hsol` (the K1/K2/K3/K4 leg, supplied by the concrete
    instance builder K7f). -/
theorem kcount_fiber_card {p n N : ℕ} [Fact p.Prime] (F : MulFiberData p n N)
    (_hS : SmithStable F) (hne : F.FiberNonempty)
    (hsol : Nat.card F.SolutionSet
      = p ^ (∑ i, min (F.smithExp F.base i) (N - F.τ))) :
    Nat.card F.Fiber = p ^ (∑ i, min (F.smithExp F.base i) (N - F.τ)) :=
  (Nat.card_congr (F.chart hne)).trans hsol

/-! ### K10 — RE-SCOPED and PROVED at REVISION 3 (countermodel kept below as warrant)

**REVISION-3 adjudication record (K10).**  The §1.3 display

    theorem sib_product_law {p n N : ℕ} [Fact p.Prime] (A : AdaptedCell p n N)
        (hS : SmithStable A.toMulFiberData) :
        A.cellCount * p ^ A.sM = ∏ j, A.factorCount j

is FALSE over the §1.3 `AdaptedCell` (unit K10a, verbatim above): the
display's only law fields are `domainCount_eq` and `fiber_nonempty`; NOTHING
constrains `cellCount` or `sM`, so `cellCount := 0`, `sM := 0`,
`factorCount ≡ 1` satisfies every field and gives `0 = 1` — the compiled
countermodel `K10Probe.sib_product_law_as_displayed_refuted` STANDS below as
the warrant (the carrier is unchanged by this adjudication).  The missing
ingredient is exactly unit K10b's conclusion (O-10 §4.2 "preimage counts are
φ times image counts", φ = p^{s(M)} the constant fiber size of Theorem 1(i)):

    imageCount_eq : cellCount * p ^ sM = Nat.card Factor

The mop-up ruling: K10 gains that ONE named binder (`himg`) — the minimal
re-scope, K10b's theorem at concrete cells being its discharge
(`adaptedCell_constFiber_image_card` below concludes verbatim `himg`).  The
verbatim-named `sib_product_law` is landed in that scope; the combine step
`sib_product_law_of_imageCount` (landed pre-revision) is kept as its body. -/

/-- K10 combine step (the honest form of "K10 = K10b + K10c"): GIVEN the K10b
    constant-fiber image law `cellCount * p^sM = Nat.card Factor` as a binder
    `himg`, the (SIB) multiplicative product law follows by chaining with the
    K10c domain-product clause (`adaptedCell_domainProduct_card` =
    `domainCount_eq`).  The conclusion is verbatim K10's; the extra binder is
    the row the §1.3 `AdaptedCell` display is missing (see the BLOCKED(K10)
    note).  `hS` is kept to mirror the displayed binder list (unused here:
    Smith stability enters through K5 when K10b DERIVES `himg` at concrete
    cells). -/
theorem sib_product_law_of_imageCount {p n N : ℕ} [Fact p.Prime]
    (A : AdaptedCell p n N) (_hS : SmithStable A.toMulFiberData)
    (himg : A.cellCount * p ^ A.sM = Nat.card A.Factor) :
    A.cellCount * p ^ A.sM = ∏ j, A.factorCount j :=
  himg.trans A.domainCount_eq

/-- K10 (Theorem 2, the adapted-cell (SIB) product law, O-10 §4.2;
    REVISION-3 scope — the K10b image law is the named binder `himg`, see
    the adjudication record above): at an `AdaptedCell`, the level-N count of
    the assembled cell times the K5 fiber size is the product of the
    per-factor counts — multiplicative form (REV-2 finding 13), verbatim-
    named per the §1.3 display. -/
theorem sib_product_law {p n N : ℕ} [Fact p.Prime]
    (A : AdaptedCell p n N) (hS : SmithStable A.toMulFiberData)
    (himg : A.cellCount * p ^ A.sM = Nat.card A.Factor) :
    A.cellCount * p ^ A.sM = ∏ j, A.factorCount j :=
  sib_product_law_of_imageCount A hS himg

namespace K10Probe

/-! Probe artifacts ONLY (not blueprint units): the compiled countermodel
justifying BLOCKED(K10).  Corpus precedent for compiled negation witnesses:
`MovesU/SibJcRouteA.lean` (`sib_diag_break`), `HC1` `U1_negWitness`. -/

/-- Probe carrier: every `MulFiberData` field filled with free/trivial data
    (the REVISION-3 `chart` field holds at the identity — Fiber and
    SolutionSet are both `Unit` here, so the probe stays legal on the
    repaired carrier). -/
def freeMFD (p n N : ℕ) [Fact p.Prime] : MulFiberData p n N where
  τ := 1
  ρ := 0
  τ_sep := by omega
  FactorPoint := Unit
  instFactorPoint := inferInstance
  base := ()
  polydisc := ∅
  Fiber := Unit
  instFiber := inferInstance
  FiberNonempty := True
  SolutionSet := Unit
  instSolutionSet := inferInstance
  smithExp := fun _ _ => 0
  chart := fun _ => Equiv.refl _

/-- Probe cell: `cellCount := 0`, `sM := 0` satisfy EVERY field of the §1.3
    `AdaptedCell` display (`domainCount_eq` reads `Nat.card Unit = ∏ _, 1`),
    yet `0 * p^0 = 1` is false — the display omits the K10b image law. -/
def freeCell (p n N : ℕ) [Fact p.Prime] : AdaptedCell p n N where
  Factor := Unit
  instFactor := inferInstance
  toMulFiberData := freeMFD p n N
  cellCount := 0
  factorCount := fun _ => 1
  sM := 0
  domainCount_eq := by simp
  fiber_nonempty := trivial

/-- BLOCKED(K10) witness: the §1.3 K10 display, read as the ∀-closure of its
    binder list, is FALSE over the §1.3 `AdaptedCell` — even with the
    `SmithStable` row supplied.  Countermodel: `freeCell` at `p = 2`,
    `n = N = 0`. -/
theorem sib_product_law_as_displayed_refuted :
    ¬ (∀ (p n N : ℕ) [Fact p.Prime] (A : AdaptedCell p n N),
        SmithStable A.toMulFiberData →
        A.cellCount * p ^ A.sM = ∏ j, A.factorCount j) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 := h 2 0 0 (freeCell 2 0 0) ⟨fun x _ => rfl⟩
  simp [freeCell] at h0

end K10Probe

/-! ### K10b (BP_IV §2 K-table; REV-2 finding 20 split; O-10 §4.2): the
constant-fiber image theorem

The counting engine of Theorem 2's proof ("all four sets are unions of entire
fibers, and preimage counts are φ times image counts"): for the concrete cell
map `μ` from the factor-product domain onto the cell, with every fiber over
the cell of the SAME exact cardinality `φcard` (K5's `kcount_fiber_card`
value `p^(s M)` at the engine site — K5 unlanded at this wave, so the exact
fiber cardinality is a NAMED binder `hfib`, never an axiom), the cell count
times the fiber size is the domain count — the multiplicative orientation K10
consumes (REV-2 finding 13: no truncated division).  The "nonempty fibers"
clause is DERIVED from the exact cardinality at `1 ≤ φcard`
(`constFiber_fiber_nonempty` / `constFiber_surjective`): it forces the cell
map onto the cell, so image = cell (`constFiber_image_eq`).  Charged corpus
reuse (BP_IV §3 reuse row; REV-2 finding 20: "O5 counting is cited only for
the image/counting step"): `MovesU.card_eq_of_injOn_checksum`
(`MovesU/O5CountingB.lean`) is consumed at exactly that step — the
image-exhausts-the-cell count (`constFiber_image_card_eq`), via the
fiber-size weight `w b := #{a ∈ s | μ a = b}`, whose positivity on the cell
is the nonempty-fibers clause and whose two checksums are the fiberwise
partitions of the domain over the image and over the cell.  BP_IV §1.3
displays no Lean block for K10b — the statements below transcribe the §2
K-table row ("combine the concrete cell map, nonempty fibers, and K5's exact
fiber cardinality"), the same convention as the K2/K3a/K4/K7a/K7b/K10c units
above.  SEAM(K10): the keyed form `adaptedCell_constFiber_image_card`
concludes verbatim the `himg` binder of `sib_product_law_of_imageCount`
(`A.cellCount * p ^ A.sM = Nat.card A.Factor`) — the missing image law the
BLOCKED(K10) note identifies — so K10 at a concrete cell map is
`sib_product_law_of_imageCount A hS (adaptedCell_constFiber_image_card ...).2`. -/

section K10b

variable {α β : Type*} [DecidableEq β]

/-- K10b, nonempty-fibers clause (Finset form): the exact fiber cardinality
    `φcard ≥ 1` on `t` makes every point of `t` a hit — `μ` is onto `t`
    from `s`. -/
theorem constFiber_fiber_nonempty (s : Finset α) (t : Finset β) (μ : α → β)
    {φcard : ℕ} (hφ : 1 ≤ φcard)
    (hfib : ∀ b ∈ t, (s.filter fun a => μ a = b).card = φcard) :
    ∀ b ∈ t, ∃ a ∈ s, μ a = b := by
  intro b hb
  have hcard : 0 < (s.filter fun a => μ a = b).card := by
    rw [hfib b hb]; omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hcard
  rw [Finset.mem_filter] at ha
  exact ⟨a, ha.1, ha.2⟩

/-- K10b, image identification: with `μ` mapping `s` into `t` and nonempty
    fibers (from the exact cardinality at `1 ≤ φcard`), the image of the
    cell map IS the cell: `s.image μ = t`. -/
theorem constFiber_image_eq (s : Finset α) (t : Finset β) (μ : α → β)
    {φcard : ℕ} (hφ : 1 ≤ φcard)
    (hmaps : ∀ a ∈ s, μ a ∈ t)
    (hfib : ∀ b ∈ t, (s.filter fun a => μ a = b).card = φcard) :
    s.image μ = t := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps a ha
  · intro b hb
    obtain ⟨a, ha, hab⟩ := constFiber_fiber_nonempty s t μ hφ hfib b hb
    exact Finset.mem_image.mpr ⟨a, ha, hab⟩

/-- K10b, the charged O5CountingB image/counting step (BP_IV §3 reuse row;
    REV-2 finding 20): the image count equals the cell count, by
    `MovesU.card_eq_of_injOn_checksum` at the identity transport
    `s.image μ ↪ t` with the fiber-size weight `w b := #{a ∈ s | μ a = b}` —
    `hpos` is the nonempty-fibers clause, and the two checksums are the
    fiberwise partitions of `#s` over the image and over `t`. -/
theorem constFiber_image_card_eq (s : Finset α) (t : Finset β) (μ : α → β)
    {φcard : ℕ} (hφ : 1 ≤ φcard)
    (hmaps : ∀ a ∈ s, μ a ∈ t)
    (hfib : ∀ b ∈ t, (s.filter fun a => μ a = b).card = φcard) :
    (s.image μ).card = t.card := by
  refine MovesU.card_eq_of_injOn_checksum (s.image μ) t id
    (fun b hb => ?_) (fun b _ b' _ h => h)
    (fun b => (s.filter fun a => μ a = b).card) (fun b hb => ?_) ?_
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps a ha
  · rw [hfib b hb]; exact hφ
  · have h1 : s.card = ∑ b ∈ s.image μ, (s.filter fun a => μ a = b).card :=
      Finset.card_eq_sum_card_fiberwise fun a ha => Finset.mem_image_of_mem μ ha
    have h2 : s.card = ∑ b ∈ t, (s.filter fun a => μ a = b).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    simpa [id_eq] using h1.symm.trans h2

/-- K10b (THE constant-fiber image theorem, Finset core; O-10 §4.2 Theorem
    2's counting engine): the concrete cell map `μ` from `s` into `t` with
    exact constant fiber cardinality `φcard` over `t` has
    `#t · φcard = #s` — "preimage counts are φ times image counts", in the
    multiplicative orientation K10 consumes.  Fiberwise partition of the
    domain over the cell; no positivity is needed for the count itself (at
    `φcard = 0` both sides vanish — O-10 §4.2 Remark (2)'s empty
    degeneracy). -/
theorem constFiber_image_card (s : Finset α) (t : Finset β) (μ : α → β)
    (φcard : ℕ) (hmaps : ∀ a ∈ s, μ a ∈ t)
    (hfib : ∀ b ∈ t, (s.filter fun a => μ a = b).card = φcard) :
    t.card * φcard = s.card := by
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib,
    Finset.sum_const, smul_eq_mul]

/-- K10b, nonempty-fibers clause at type level: exact fiber cardinality
    `φcard ≥ 1` at every point makes the cell map surjective (no finiteness
    needed on the domain). -/
theorem constFiber_surjective {γ δ : Type*} (μ : γ → δ)
    {φcard : ℕ} (hφ : 1 ≤ φcard)
    (hfib : ∀ d : δ, Nat.card {c : γ // μ c = d} = φcard) :
    Function.Surjective μ := by
  intro d
  have hne : Nat.card {c : γ // μ c = d} ≠ 0 := by
    rw [hfib d]; omega
  obtain ⟨⟨c, hc⟩⟩ := (Nat.card_ne_zero.mp hne).1
  exact ⟨c, hc⟩

/-- K10b at type level (the shape K10a's `AdaptedCell` `Nat.card` fields
    consume): a map of finite types with every fiber of exact cardinality
    `φcard` has `Nat.card δ * φcard = Nat.card γ`. -/
theorem constFiber_nat_card {γ δ : Type*} [Finite γ] [Finite δ]
    (μ : γ → δ) (φcard : ℕ)
    (hfib : ∀ d : δ, Nat.card {c : γ // μ c = d} = φcard) :
    Nat.card δ * φcard = Nat.card γ := by
  classical
  haveI := Fintype.ofFinite γ
  haveI := Fintype.ofFinite δ
  have key : (Finset.univ : Finset δ).card * φcard
      = (Finset.univ : Finset γ).card :=
    constFiber_image_card Finset.univ Finset.univ μ φcard
      (fun a _ => Finset.mem_univ _)
      (fun d _ => by
        rw [← hfib d, Nat.card_eq_fintype_card, Fintype.card_subtype])
  simpa [Nat.card_eq_fintype_card, Finset.card_univ] using key

/-- K10b (the K-table row keyed at the K10a carrier): combine the concrete
    cell map (`μ`, with `hcell` reading `A.cellCount` as the cell's count),
    nonempty fibers (DERIVED: `1 ≤ p^(A.sM)` from primality, so the exact
    cardinality forces surjectivity — the image of the cell map is the whole
    cell), and K5's exact fiber cardinality (the named binder `hfib` at the
    K5 value `p^(A.sM)`; K5 itself is a later-wave unit): the cell count
    times the fiber size is the domain count,
    `A.cellCount * p ^ A.sM = Nat.card A.Factor` — verbatim the `himg`
    binder that `sib_product_law_of_imageCount` chains with K10c's
    `adaptedCell_domainProduct_card` (see the BLOCKED(K10) note above). -/
theorem adaptedCell_constFiber_image_card {p n N : ℕ} [Fact p.Prime]
    (A : AdaptedCell p n N) {Cell : Type*} [Finite Cell]
    (μ : A.Factor → Cell)
    (hcell : A.cellCount = Nat.card Cell)
    (hfib : ∀ c : Cell, Nat.card {x : A.Factor // μ x = c} = p ^ A.sM) :
    Function.Surjective μ ∧ A.cellCount * p ^ A.sM = Nat.card A.Factor := by
  have hφ : 1 ≤ p ^ A.sM := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  exact ⟨constFiber_surjective μ hφ hfib,
    by rw [hcell]; exact constFiber_nat_card μ _ hfib⟩

end K10b

/-! ### K8b (BP_IV §2 K-table; O-10 §2 Lemma 2 half 1 + §3 Step 2): the
`SmithData` adapter for the particular Φ matrix

K8b instantiates the K8a-checked PID theorem (`Submodule.smithNormalForm`,
signature pinned in the K8a section above) at the matrix of Φ over `ℤ_[p]`
and exposes the concrete data the K-chain consumes: the matrices `U`, `V`
with their explicit two-sided inverses (the inverse laws), the diagonal
equality `Φ = U · diag(p^{e₁}, …, p^{e_n}) · V` (O-10 §3 Step 2:
`Φ_h = U D V`, `U, V ∈ GL_n(ℤ_p)`, `D = diag(p^{e_i})`), and the `Fin n`
exponent indexing `exp : Fin n → ℕ` in the shape `MulFiberData.smithExp`
consumes (BP_IV §1.3).  Generic existence alone does not discharge K8: the
carrier below is the problem-specific U/D/V adapter charged by the §2
K-table row (deps K8a, K7d).  (BP_IV §1.3 displays no Lean block for K8b —
the statements below transcribe the §2 K-table row, the same convention as
the K2/K3a/K4/K7a/K7b units above.)

Construction (`smithData_exists`): with `b` the standard basis of
`Fin n → ℤ_[p]` and `φ := toLin b b Φ` injective, apply
`Submodule.smithNormalForm b (range φ)` to get `bM`, `bN`, `f`, `a`, `snf`;
the rank count forces the Smith index count to `n` and `f` to a bijection
`σ`; pulling `bN` back through `range φ ≃ₗ (Fin n → ℤ_[p])` gives a domain
basis in which `φ` is the diagonal matrix `diag(a ∘ σ⁻¹)`; the two
change-of-basis matrices then have explicit inverses
(`Basis.toMatrix_mul_toMatrix_flip`), and the DVR factorization
`a = u · p^e` (`eq_unit_mul_pow_irreducible` at the irreducible `p`)
absorbs the units into `U`. -/

section K8b

/-- K8b (BP_IV §2 K-table): the Smith data of the particular matrix `Φ` over
    `ℤ_[p]` — the concrete `U`/`V` with explicit two-sided inverse laws, and
    the `Fin n`-indexed exponents `exp` with the diagonal equality
    `Φ = U * diag(p^exp) * V` (O-10 §3 Step 2; `exp` is the shape
    `MulFiberData.smithExp` consumes per BP_IV §1.3). -/
structure SmithData (p : ℕ) [Fact p.Prime] {n : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℤ_[p]) where
  U : Matrix (Fin n) (Fin n) ℤ_[p]
  Uinv : Matrix (Fin n) (Fin n) ℤ_[p]
  V : Matrix (Fin n) (Fin n) ℤ_[p]
  Vinv : Matrix (Fin n) (Fin n) ℤ_[p]
  exp : Fin n → ℕ
  U_mul_Uinv : U * Uinv = 1
  Uinv_mul_U : Uinv * U = 1
  V_mul_Vinv : V * Vinv = 1
  Vinv_mul_V : Vinv * V = 1
  factor : Φ = U * Matrix.diagonal (fun i => (p : ℤ_[p]) ^ exp i) * V

namespace SmithData

variable {p n : ℕ} [Fact p.Prime] {Φ : Matrix (Fin n) (Fin n) ℤ_[p]}

/-- The diagonal matrix `D = diag(p^{e₁}, …, p^{e_n})` of the factorization. -/
noncomputable def D (S : SmithData p Φ) : Matrix (Fin n) (Fin n) ℤ_[p] :=
  Matrix.diagonal fun i => (p : ℤ_[p]) ^ S.exp i

/-- `Φ = U * D * V`, restated through the `D` abbreviation. -/
theorem factor_D (S : SmithData p Φ) : Φ = S.U * S.D * S.V := S.factor

/-- The diagonal equality in solved form: `U⁻¹ * Φ * V⁻¹ = diag(p^exp)`. -/
theorem diagonal_eq (S : SmithData p Φ) :
    S.Uinv * Φ * S.Vinv = Matrix.diagonal fun i => (p : ℤ_[p]) ^ S.exp i := by
  have hstep : S.Uinv * Φ * S.Vinv
      = S.Uinv * (S.U * Matrix.diagonal (fun i => (p : ℤ_[p]) ^ S.exp i) * S.V)
        * S.Vinv := by
    rw [← S.factor]
  rw [hstep, mul_assoc S.U, ← mul_assoc S.Uinv, S.Uinv_mul_U, one_mul,
    mul_assoc, S.V_mul_Vinv, mul_one]

end SmithData

/-- K8b (BP_IV §2 K-table row, the adapter theorem): instantiating the
    K8a-checked PID theorem `Submodule.smithNormalForm` at an injective
    matrix `Φ` over `ℤ_[p]` yields its concrete Smith data — `U`/`V` with
    inverse laws, the `Fin n` exponents, and the diagonal equality. -/
theorem smithData_exists {p n : ℕ} [Fact p.Prime]
    (Φ : Matrix (Fin n) (Fin n) ℤ_[p])
    (hΦ : Function.Injective Φ.mulVecLin) : Nonempty (SmithData p Φ) := by
  classical
  set b : Module.Basis (Fin n) ℤ_[p] (Fin n → ℤ_[p]) :=
    Pi.basisFun ℤ_[p] (Fin n) with hb
  set φ : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := Matrix.toLin b b Φ
    with hφdef
  have hφ : Function.Injective φ := by
    have hcoe : ⇑φ = ⇑Φ.mulVecLin := by
      funext v
      rw [hφdef, hb, Matrix.toLin_eq_toLin', Matrix.toLin'_apply,
        Matrix.mulVecLin_apply]
    rw [hcoe]; exact hΦ
  obtain ⟨m, S⟩ := Submodule.smithNormalForm b (LinearMap.range φ)
  set ε : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] LinearMap.range φ :=
    LinearEquiv.ofInjective φ hφ with hε
  have hm : n = m := by
    have h1 : Module.finrank ℤ_[p] (LinearMap.range φ) = m :=
      (Module.finrank_eq_card_basis S.bN).trans (Fintype.card_fin m)
    have h2 : Module.finrank ℤ_[p] (LinearMap.range φ) = n :=
      (Module.finrank_eq_card_basis (b.map ε)).trans (Fintype.card_fin n)
    omega
  subst hm
  -- the index embedding is a bijection σ of `Fin n`
  have hfbij : Function.Bijective S.f :=
    Finite.injective_iff_bijective.mp S.f.injective
  set σ : Fin n ≃ Fin n := Equiv.ofBijective S.f hfbij with hσ
  -- the domain basis: bN pulled back through range φ ≃ₗ (Fin n → ℤ_[p])
  set bDom : Module.Basis (Fin n) ℤ_[p] (Fin n → ℤ_[p]) :=
    (S.bN.map ε.symm).reindex σ with hbDom
  have hεφ : ∀ y : LinearMap.range φ, φ (ε.symm y) = (y : Fin n → ℤ_[p]) := by
    intro y
    conv_rhs => rw [← ε.apply_symm_apply y]
    rw [hε, LinearEquiv.ofInjective_apply]
  -- the columns of φ in the bases (bDom, bM): the diagonal a ∘ σ⁻¹
  have hkey : ∀ j, φ (bDom j) = S.a (σ.symm j) • (S.bM j : Fin n → ℤ_[p]) := by
    intro j
    have h1 : bDom j = ε.symm (S.bN (σ.symm j)) := by
      rw [hbDom, Module.Basis.reindex_apply, Module.Basis.map_apply]
    have h2 : S.f (σ.symm j) = j := σ.apply_symm_apply j
    rw [h1, hεφ, S.snf (σ.symm j), h2]
  have hdiag : LinearMap.toMatrix bDom S.bM φ
      = Matrix.diagonal (fun j => S.a (σ.symm j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hkey j, map_smul]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [Matrix.diagonal_apply_ne _ hij, Module.Basis.repr_self]
      rw [Finsupp.single_apply, if_neg (Ne.symm hij)]
  -- change of basis: Φ = U₀ · diag(a ∘ σ⁻¹) · V
  have hcomp1 := LinearMap.toMatrix_comp b S.bM b LinearMap.id φ
  rw [LinearMap.id_comp] at hcomp1
  have hcomp2 := LinearMap.toMatrix_comp b bDom S.bM φ LinearMap.id
  rw [LinearMap.comp_id] at hcomp2
  have hfact : Φ = b.toMatrix ⇑S.bM
      * Matrix.diagonal (fun j => S.a (σ.symm j)) * bDom.toMatrix ⇑b := by
    have h0 : Φ = LinearMap.toMatrix b b φ := by
      rw [hφdef, LinearMap.toMatrix_toLin]
    rw [h0, hcomp1, hcomp2, hdiag, LinearMap.toMatrix_id_eq_basis_toMatrix,
      LinearMap.toMatrix_id_eq_basis_toMatrix, mul_assoc]
  -- the diagonal entries are nonzero, hence unit · p^e over the DVR ℤ_[p]
  have ha : ∀ j : Fin n, S.a (σ.symm j) ≠ 0 := by
    intro j ha0
    refine S.bN.ne_zero (σ.symm j) ?_
    have hz := S.snf (σ.symm j)
    rw [ha0, zero_smul] at hz
    exact ZeroMemClass.coe_eq_zero.mp hz
  have hfac : ∀ j : Fin n, ∃ (e : ℕ) (v : ℤ_[p]ˣ),
      S.a (σ.symm j) = ↑v * (p : ℤ_[p]) ^ e := fun j =>
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha j)
      PadicInt.irreducible_p
  choose e u hu using hfac
  -- assemble: absorb the units into U
  refine ⟨⟨b.toMatrix ⇑S.bM * Matrix.diagonal (fun j => (↑(u j) : ℤ_[p])),
    Matrix.diagonal (fun j => (↑(u j)⁻¹ : ℤ_[p])) * S.bM.toMatrix ⇑b,
    bDom.toMatrix ⇑b, b.toMatrix ⇑bDom, e, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- U * Uinv = 1
    have hd : Matrix.diagonal (fun j => (↑(u j) : ℤ_[p]))
        * Matrix.diagonal (fun j => (↑(u j)⁻¹ : ℤ_[p])) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have h1 : (fun j => (↑(u j) : ℤ_[p]) * ↑(u j)⁻¹) = fun _ => (1 : ℤ_[p]) :=
        funext fun j => Units.mul_inv (u j)
      rw [h1, Matrix.diagonal_one]
    rw [mul_assoc, ← mul_assoc (Matrix.diagonal fun j => (↑(u j) : ℤ_[p])),
      hd, one_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
  · -- Uinv * U = 1
    have hd : Matrix.diagonal (fun j => (↑(u j)⁻¹ : ℤ_[p]))
        * Matrix.diagonal (fun j => (↑(u j) : ℤ_[p])) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have h1 : (fun j => (↑(u j)⁻¹ : ℤ_[p]) * ↑(u j)) = fun _ => (1 : ℤ_[p]) :=
        funext fun j => Units.inv_mul (u j)
      rw [h1, Matrix.diagonal_one]
    rw [mul_assoc, ← mul_assoc (S.bM.toMatrix ⇑b),
      Module.Basis.toMatrix_mul_toMatrix_flip, one_mul, hd]
  · -- V * Vinv = 1
    exact Module.Basis.toMatrix_mul_toMatrix_flip bDom b
  · -- Vinv * V = 1
    exact Module.Basis.toMatrix_mul_toMatrix_flip b bDom
  · -- Φ = U * diag(p^e) * V
    have hDD : Matrix.diagonal (fun j => S.a (σ.symm j))
        = Matrix.diagonal (fun j => (↑(u j) : ℤ_[p]))
          * Matrix.diagonal (fun j => (p : ℤ_[p]) ^ e j) := by
      rw [Matrix.diagonal_mul_diagonal]
      exact congrArg Matrix.diagonal (funext fun j => hu j)
    rw [hfact, hDD, ← mul_assoc]

/-- K8b, packaged: the concrete Smith adapter of an injective `Φ`, extracted
    from `smithData_exists` (noncomputable choice; the structure fields expose
    the U/D/V matrices, inverse laws, diagonal equality, and the `Fin n`
    exponent indexing). -/
noncomputable def smithDataOfInjective {p n : ℕ} [Fact p.Prime]
    (Φ : Matrix (Fin n) (Fin n) ℤ_[p])
    (hΦ : Function.Injective Φ.mulVecLin) : SmithData p Φ :=
  (smithData_exists Φ hΦ).some

end K8b

/-! ### K9 (BP_IV §2 K-table, wave 4; O-10 §2 Lemma 2 half 2): the `SmithStable`
constructor — in-polydisc constancy of the Smith profile

O-10 §2 Lemma 2's proof, transcribed: on the ρ-separated polydisc (h ≡ f mod
p^τ coefficientwise, τ ≥ ρ + 1) every entry of Φ_h is ≡ the corresponding
entry of Φ_f mod p^τ, hence every k×k minor satisfies minor(h) ≡ minor(f)
mod p^τ (`dvd_det_sub_det`: the determinant transport of K7d's
`dvd_prod_sub_prod` along the Leibniz expansion).  The k-th determinantal
divisor d_k = v_p(gcd of all k×k minors) is encoded by the divisibility
predicate `IsDetDivisor π A k d` (π^d divides every k×k minor, some k×k minor
escapes π^(d+1)); it is FUNCTIONAL in d (`IsDetDivisor.unique`) and, strictly
below the separation level, TRANSPORTS along entrywise congruence
(`IsDetDivisor.of_congr`, d < τ) — the paper's "a minor attaining d_k has
valuation < τ, so its valuation is preserved exactly", in both directions.
Minors are indexed by ALL pairs of maps `r c : Fin k → Fin n`, not embeddings
only: a repeating row/column choice has determinant 0, so it neither breaks
the ∀ leg (everything divides 0) nor can serve as the ∃ witness — the
predicate is extensionally the embedding-indexed one, without
`Function.Embedding` plumbing.

The constructor `smithStable_of_detDivisorRows` consumes PER-POINT rows only —
no hypothesis relates two distinct polydisc points except `hcong`, the
polydisc congruence itself (the DEFINITION of the ρ-separated polydisc, in
the K7c `monicLiftEquiv` shape: coefficientwise p^τ-congruent factor tuples
have entrywise p^τ-congruent Sylvester block matrices):
* `hbase`/`hpoly`: at each single point, the partial sums e₁ + ⋯ + e_k of its
  OWN `smithExp` are determinantal divisors of its OWN matrix Φ — the
  standard determinantal-divisor identity for the Smith normal form (O-10 §1,
  classical background; deriving this row from K8b's `SmithData` via
  Cauchy–Binet is a separate follow-up unit, not part of Lemma 2's
  mechanism);
* `hρ`: Σᵢ eᵢ(base) ≤ ρ — the resultant bound (O-10 §2 Lemma 1:
  v_p(det Φ_f) = Σ_{i<j} v_p(Res(h_i, h_j)) = ρ, the "resultant lower
  bounds" leg), which with the carrier clause `τ_sep : ρ + 1 ≤ τ` puts every
  d_k(base) strictly below the congruence level τ.
The CONSTANCY conclusion — the cross-point equality of `smithExp` — is
PROVED, not assumed: d_k(h) = d_k(base) for every k ≤ n by transport +
uniqueness, and the exponents are the consecutive differences
(`smithPartial_succ` telescoping).  Non-vacuity gate:
`K9Gate.gate_smithStable` fires the constructor at a concrete carrier with a
NONEMPTY polydisc. -/

section K9constructor

variable {R : Type*} [CommRing R]

/-- K9 minor-congruence engine (O-10 §2 Lemma 2, step 1): entrywise congruent
    matrices have congruent determinants — `d ∣ A i j − B i j` everywhere ⇒
    `d ∣ det A − det B` (Leibniz expansion; K7d's `dvd_prod_sub_prod` per
    permutation term). -/
theorem dvd_det_sub_det {k : ℕ} {d : R} {A B : Matrix (Fin k) (Fin k) R}
    (hcong : ∀ i j, d ∣ A i j - B i j) : d ∣ A.det - B.det := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun σ _ => ?_
  rw [← mul_sub]
  exact (dvd_prod_sub_prod Finset.univ _ _ fun i _ => hcong (σ i) i).mul_left _

/-- K9 determinantal-divisor predicate: `π^d` divides EVERY k×k minor of `A`
    and SOME k×k minor escapes `π^(d+1)` — the divisibility encoding of
    d_k(A) = v_p(gcd of the k×k minors).  Minors are indexed by all
    row/column choice maps (see the section header: extensionally equivalent
    to embedding-indexed minors, since repeating choices give det 0). -/
def IsDetDivisor {n : ℕ} (π : R) (A : Matrix (Fin n) (Fin n) R)
    (k d : ℕ) : Prop :=
  (∀ r c : Fin k → Fin n, π ^ d ∣ (A.submatrix r c).det) ∧
    ∃ r c : Fin k → Fin n, ¬ π ^ (d + 1) ∣ (A.submatrix r c).det

/-- The determinantal-divisor predicate is antisymmetric in `d`: if `d' < d`
    then `d'`'s escaping minor would be caught by `d`'s ∀ leg. -/
theorem IsDetDivisor.le {n : ℕ} {π : R} {A : Matrix (Fin n) (Fin n) R}
    {k d d' : ℕ} (h : IsDetDivisor π A k d) (h' : IsDetDivisor π A k d') :
    d ≤ d' := by
  by_contra hlt
  obtain ⟨r, c, hrc⟩ := h'.2
  exact hrc ((pow_dvd_pow π (by omega)).trans (h.1 r c))

/-- The determinantal-divisor predicate is functional in `d`. -/
theorem IsDetDivisor.unique {n : ℕ} {π : R} {A : Matrix (Fin n) (Fin n) R}
    {k d d' : ℕ} (h : IsDetDivisor π A k d) (h' : IsDetDivisor π A k d') :
    d = d' :=
  le_antisymm (h.le h') (h'.le h)

/-- K9 ρ-separation transport (O-10 §2 Lemma 2, the mechanism): strictly below
    the congruence level (`d < τ`), the determinantal-divisor predicate
    transports along entrywise congruence mod `π^τ` — divisibility of minors
    crosses over (`d ≤ τ`), and the escaping minor still escapes
    (`d + 1 ≤ τ`), in both directions. -/
theorem IsDetDivisor.of_congr {n : ℕ} {π : R} {A B : Matrix (Fin n) (Fin n) R}
    {τ k d : ℕ} (hcong : ∀ i j, π ^ τ ∣ A i j - B i j)
    (hB : IsDetDivisor π B k d) (hdτ : d < τ) : IsDetDivisor π A k d := by
  have hmin : ∀ r c : Fin k → Fin n,
      π ^ τ ∣ (A.submatrix r c).det - (B.submatrix r c).det := fun r c =>
    dvd_det_sub_det fun i j => hcong (r i) (c j)
  constructor
  · intro r c
    have hsplit : (A.submatrix r c).det
        = ((A.submatrix r c).det - (B.submatrix r c).det)
          + (B.submatrix r c).det := by ring
    rw [hsplit]
    exact dvd_add ((pow_dvd_pow π hdτ.le).trans (hmin r c)) (hB.1 r c)
  · obtain ⟨r, c, hrc⟩ := hB.2
    refine ⟨r, c, fun hdvd => hrc ?_⟩
    have hsplit : (B.submatrix r c).det
        = (A.submatrix r c).det
          - ((A.submatrix r c).det - (B.submatrix r c).det) := by ring
    rw [hsplit]
    exact dvd_sub hdvd ((pow_dvd_pow π (Nat.succ_le_of_lt hdτ)).trans (hmin r c))

/-- K9 partial-sum ladder: e₁ + ⋯ + e_k of a `Fin n`-indexed exponent vector
    (the candidate k-th determinantal divisor). -/
def smithPartial {n : ℕ} (e : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), e i

theorem smithPartial_succ {n : ℕ} (e : Fin n → ℕ) (i : Fin n) :
    smithPartial e ((i : ℕ) + 1) = smithPartial e (i : ℕ) + e i := by
  have hins : Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1)
      = insert i (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      ← Fin.val_inj]
    omega
  have hnot : i ∉ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ)) := by
    simp
  unfold smithPartial
  rw [hins, Finset.sum_insert hnot, add_comm]

theorem smithPartial_le {n : ℕ} (e : Fin n → ℕ) (k : ℕ) :
    smithPartial e k ≤ ∑ i, e i :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- K9 (THE CONSTRUCTOR, O-10 §2 Lemma 2 half 2): `SmithStable` from per-point
    determinantal-divisor rows + the polydisc congruence + the resultant
    bound.  Row-by-row provenance in the section header; no hypothesis
    relates two distinct polydisc points except the congruence `hcong`
    itself.  Proof: for each `k ≤ n`, `d_k(base) ≤ Σᵢ eᵢ(base) ≤ ρ < τ`
    (`hρ` + the carrier's `τ_sep`), so `IsDetDivisor.of_congr` transports the
    base row to `Φ h`, where `IsDetDivisor.unique` pins `d_k(h) = d_k(base)`;
    the exponents are the consecutive differences. -/
theorem smithStable_of_detDivisorRows {p n N : ℕ} [Fact p.Prime]
    (F : MulFiberData p n N)
    (Φ : F.FactorPoint → Matrix (Fin n) (Fin n) ℤ_[p])
    (hcong : ∀ h ∈ F.polydisc, ∀ i j,
      (p : ℤ_[p]) ^ F.τ ∣ Φ h i j - Φ F.base i j)
    (hbase : ∀ k ≤ n, IsDetDivisor (p : ℤ_[p]) (Φ F.base) k
      (smithPartial (F.smithExp F.base) k))
    (hpoly : ∀ h ∈ F.polydisc, ∀ k ≤ n, IsDetDivisor (p : ℤ_[p]) (Φ h) k
      (smithPartial (F.smithExp h) k))
    (hρ : ∑ i, F.smithExp F.base i ≤ F.ρ) :
    SmithStable F := by
  refine ⟨fun h hmem => ?_⟩
  have key : ∀ k, k ≤ n →
      smithPartial (F.smithExp h) k = smithPartial (F.smithExp F.base) k := by
    intro k hk
    have hlt : smithPartial (F.smithExp F.base) k < F.τ :=
      lt_of_le_of_lt (le_trans (smithPartial_le _ _) hρ)
        (Nat.lt_of_succ_le F.τ_sep)
    exact (hpoly h hmem k hk).unique
      ((hbase k hk).of_congr (hcong h hmem) hlt)
  funext i
  have h1 := key (i : ℕ) (le_of_lt i.isLt)
  have h2 := key ((i : ℕ) + 1) (Nat.succ_le_of_lt i.isLt)
  rw [smithPartial_succ, smithPartial_succ, h1] at h2
  omega

end K9constructor

/-! ### K9 gate: non-vacuity of the constructor's hypothesis package

The constructor fires at a concrete carrier with a NONEMPTY polydisc — every
hypothesis row discharged by computation (Φ ≡ the 1×1 identity across the
polydisc, profile ≡ 0, ρ = 0 < τ = 1), so the hypothesis package is
satisfiable and the constructor is not vacuously conditional. -/

namespace K9Gate

/-- K9 gate carrier: p = 2, n = 1, N = 1, factor space `Bool` with base
    `false` and NONEMPTY polydisc `{true}` — the constancy conclusion
    quantifies over a genuinely distinct point. -/
def gateMFD : MulFiberData 2 1 1 where
  τ := 1
  ρ := 0
  τ_sep := by omega
  FactorPoint := Bool
  instFactorPoint := inferInstance
  base := false
  polydisc := {true}
  Fiber := Fin 1
  instFiber := inferInstance
  FiberNonempty := True
  SolutionSet := Fin 1
  instSolutionSet := inferInstance
  smithExp := fun _ _ => 0
  chart := fun _ => Equiv.refl _

/-- Every k×k minor of the 1×1 identity over `ℤ_[p]` (k ≤ 1) is 1: the k = 0
    minor is the empty determinant, the k = 1 minor is the (0,0) entry — so
    0 is the k-th determinantal divisor. -/
theorem isDetDivisor_one_of_le {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : k ≤ 1) :
    IsDetDivisor (p : ℤ_[p]) (1 : Matrix (Fin 1) (Fin 1) ℤ_[p]) k 0 := by
  have hdet : ∀ r c : Fin k → Fin 1,
      ((1 : Matrix (Fin 1) (Fin 1) ℤ_[p]).submatrix r c).det = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · intro r c
      exact Matrix.det_fin_zero
    · intro r c
      rw [Matrix.det_fin_one, Matrix.submatrix_apply,
        Subsingleton.elim (r 0) (c 0), Matrix.one_apply_eq]
  refine ⟨fun r c => ?_, fun _ => 0, fun _ => 0, ?_⟩
  · rw [hdet r c, pow_zero]
  · rw [hdet, zero_add, pow_one]
    exact PadicInt.prime_p.not_dvd_one

/-- K9 gate: the constructor FIRES — a compiled `SmithStable` instance over a
    nonempty polydisc. -/
theorem gate_smithStable : SmithStable gateMFD := by
  refine smithStable_of_detDivisorRows gateMFD (fun _ => 1) ?_ ?_ ?_ ?_
  · intro h _ i j
    simp
  · intro k hk
    have h0 : smithPartial (gateMFD.smithExp gateMFD.base) k = 0 := by
      simp [smithPartial, gateMFD]
    rw [h0]
    exact isDetDivisor_one_of_le hk
  · intro h _ k hk
    have h0 : smithPartial (gateMFD.smithExp h) k = 0 := by
      simp [smithPartial, gateMFD]
    rw [h0]
    exact isDetDivisor_one_of_le hk
  · simp [gateMFD]

end K9Gate

/-! ### K11 (BP_IV §2 K-table + §1.3 application note; AUTHORED at REVISION 3)

**REVISION-3 adjudication record (K11).**  The §2 K-table charges an
`EngineSIBRow` "named structure consuming actual K-LOC and (I-τ) rows", but
BP_IV displays NO verbatim statement, and the K-LOC/(I-τ) rows are BP_III-
owned with NO landed (or even chartered) declaration anywhere in the corpus
(the pre-revision BLOCKED(K11) header, git history 33656d2; BP_III.md never
names them).  The mop-up authors the row from the §2 description + the §1.3
application note ("consuming the named rows K-LOC and (I-τ) ... displayed as
binders"), with the two foreign rows as OPAQUE Prop PARAMETERS — the
sanctioned `K3DeltaRow` pattern; BP_III's actual rows instantiate them with
no re-key.  Content: the engine stratum's level-N count is realized by an
adapted cell carrying Smith stability and the K10b image law — exactly what
K10 (`sib_product_law`) consumes; a wave-4/owner constructor supplies
instances, never an unproved theorem declaration (§2 charge honored). -/

/-- K11 (`EngineSIBRow`, REVISION-3 authored form): under the BP_III-owned
    K-LOC and (I-τ) rows (opaque Prop parameters until the owner lands), the
    engine stratum's level-N count `stratumCount` is computed by an adapted
    cell that carries Smith stability and the K10b constant-fiber image law
    — the (SIB) application package.  Named [M] row: no proof exists at this
    campaign; constructors are owner-side. -/
structure EngineSIBRow (p n N : ℕ) [Fact p.Prime]
    (KLoc ITau : Prop) (stratumCount : ℕ) : Prop where
  kloc : KLoc
  itau : ITau
  cell : ∃ A : AdaptedCell p n N, SmithStable A.toMulFiberData ∧
    A.cellCount * p ^ A.sM = Nat.card A.Factor ∧
    A.cellCount = stratumCount

end LeanUrat.Scaffold
