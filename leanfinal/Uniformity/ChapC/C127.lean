/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C71
import Uniformity.ChapC.C50
import Uniformity.ChapC.C44
import Uniformity.ChapC.C11
import Uniformity.ChapC.C129
import Uniformity.ChapB.B06
import Uniformity.ChapB.B04
import Uniformity.ChapB.B35a

/-!
# Uniformity.ChapC.C127 — LAW E-W: the K2-division boundary identity

**Chapter C, NODE C.127** [theorem] [fresh] [signed: A-C.4]
(`blueprint/CHAP-C_tower_grammar.md`, amendment A-C.4 of 2026-08-16; twin
`leanspec/Leanspec/ChapC.lean`, section `AC4Laws`).  **ENV-C1**.  Proof source: the
corpus-grade note `lean/notes/openmath/LAWEW_PROOF_2026-08-16.md` (PROVED; two-pass
adversarially verified; every display machine-certified bit-exact by
`verification/openmath/ewbs2_lawew_cert.py`, GREEN 2796/0, 5/5 teeth).

## The frame and the two ledgers

The node fixes the **trinomial single-crossing frame** by equation hypotheses (no
`stageLiftO` plumbing is consumed, so the node is D19-safe):

* (F1) `Φ′ = F.key = x^{D′} − πω` with `f₁ = h = 1`, so `D′ = e₁` (Eisenstein, slope `1/D′`);
* (F2) `Φ₂ = composedKey T = Φ′^m + P·Φ′^{m−1} + c₀` with `P = ĉ₂π^{v₂}x^{i₂}`,
  `c₀ = ĉ₀π^{v₀}`, `e₂ = 1`, `m = f₂ ≥ 2` (`T.hcomp`);
* (F3) on-side: `u₂ = D′v₂ + i₂` and `D′v₀ = m·u₂`;
* (F4) the margin `δ = T.margin = u₂ − D′ ≥ 1` — automatic from `T.hfloor` (C.71's
  `one_le_margin`), so no hypothesis carries it;
* (F5) in-grid: `μ₂·i₂ < D′`.

The two ledgers are C.71's: the **honest** read `dev (composedKey T) f j` (B.02's
development at the composed key) and the **stage-shadow** read `shadowDev T f j` (the same
division tower run in `(O[x]/Φ′)[Z]` and lifted back by the canonical degree-`< D′`
representative).  LAW E-W says where they agree and, when they do not, by exactly how much.

## What this file lands, and what it does not

* `lawEW_faithful_of_nox` — **clause (a)**, PROVED here, at the blueprint's own member class
  (`j′ ≤ 1`; see the fence note below).
* `lawEW_faithful_high` — **clause (b) at `j ≥ 2`**, PROVED here.
* `seed_division_census` / `devQ_seed` — the note's §3 Step 3 (the exact quotient and
  remainder of the seed division) and Step 2's "one division", landed as reusable lemmas
  over any commutative base: the pin clause's arithmetic core.
* `lawEW_discrepancy_eq_census` — **the pin clause minus its last two steps**: at a
  crossing entry the two low-coordinate discrepancies are, in closed form,
  `Δ₁ = reass (seedQuot P̄ ḡ b)` and `Δ₀ = reass (seedRem P̄ c̄₀ ḡ m b)` (the note's
  `Δ₁ = red(q)`, `Δ₀ = red(r)`).  `lawEW_pin` is the `dv2Hgt` of these two polynomials.
* `lawEW_pin` — **clause (b) at `j ≤ 1`**, the boundary identity
  `dv2Hgt (Δ_j) = gridWeight T α a b (1−j) + T.margin`.  **NOT landed** (see
  `notes/C127_PIN_BLOCKED_2026-08-16.md` for the exact gap: the §3 Step 3 telescoping census
  is available from the machinery here, but the Step 4 slot-height computation needs a
  `stageHeight`-of-a-monomial layer plus the `b = m−1` collision analysis, neither of which
  exists in the landed corpus).

## ⚠ SCOPE FENCE REPAIR (A-C.4, clause (a)): the `j′ ≤ 1` hypothesis is NOT in the stub

The blueprint STATEMENT fences the member class at `j′ ≤ 1` ("the single-entry member
`f = Φ₂^{μ₂} + c·π^α·x^a·Φ′^b·Φ₂^{j′}` (`j′ ≤ 1`)") and the node's TEETH row carries the
fence explicitly ("`j′ ≥ 2` members DEVIATE … no fleet agent may generalize the statement
over `j′`").  The elaborated stub in `leanspec/Leanspec/ChapC.lean` nevertheless binds
`(α a b j' : ℕ)` with **no** `j′ ≤ 1` hypothesis — i.e. it IS the forbidden generalization,
and **it is false**: at `p ∈ {2,3}`, `D′ = 5`, `i₂ = 1`, `m = 5`, `v₂ = 2`, `v₀ = 11`,
`μ₂ = 3` and the member `f = Φ₂³ + x³Φ′^bΦ₂²` the hypothesis `hnox` holds through its right
disjunct (`a + i₂ = 4 < 5 = D′`) while the discrepancy is NONZERO at coordinates `0,1`
(`b = 0`) and `0,1,2` (`b = 1,2`) — the second seed `E′P²` is over-grid
(`a + 2i₂ = 5 ≥ D′`).  Committed refutation record and reproduction:
`verification/c127_nox_jp2_refutation.py` (independent implementation of the LEAN
definitions; leg 2 agrees with the certified battery on 36/36 rows).  The theorem below
therefore carries the blueprint's own fence as the hypothesis `hjp : j' ≤ 1`; every other
binder is the stub's, verbatim and in order.  This is a signature REPAIR of the stub, not a
weakening of the node: the node's STATEMENT is what is proved.

## Proof route (the note's §2 and §3, Steps 1–2)

Everything is run through ONE mechanism, the **in-grid transfer**: if a two-variable
`Ap ∈ O[x][Y]` has all coefficients of degree `< D′`, then (i) the `Φ′`-digits of `Ap(Φ′)`
ARE the coefficients of `Ap` (B.06's uniqueness, `dev_eval_eq_coeff`) and (ii) therefore
`biRead F (Ap(Φ′)) = Ap.map (AdjoinRoot.mk Φ′)` — a RING-MAP image
(`biRead_eval_eq_map`).  Since `Polynomial.map` is multiplicative, the shadow chain of a
member presented in-grid is computed by the same telescoping as the honest ledger, over the
ring `(O[x]/Φ′)[Z]` (`devQ_pow_add_entry`), and reassembly (`reass`) inverts the transport on
the in-grid locus (`reass_map_C_mul_X_pow`).

* clause (a): the pure power's two-variable presentation is `K(Y)^{μ₂}` — in-grid by (F5),
  every coefficient a `ℤ`-combination of at most `μ₂` entries from `{P, c₀}` — and the entry's
  is `E′Y^bK(Y)^{j′}`, in-grid by `a < D′` (`j′ = 0`) resp. `a + i₂ < D′` (`j′ = 1`).  Both
  ledgers then read `E′Φ′^b` at coordinate `j′` and `0` elsewhere below `μ₂`.
* clause (b) at `j ≥ 2`: `a + i₂ ≥ D′` makes the single coefficient `E′P` over-grid; the
  development identity `A(CΦ₂) = E′Y^bK + g·(Y − Φ′)Y^{b+m−1}` (the note's Step 1) births the
  seed, whose `Φ′`-multiple half dies under the transport (LEMMA 2) leaving `g·Y^{b+m}`; that
  has `Z`-degree `b + m ≤ 2m − 1 < 2m`, so its chain is empty from coordinate `2` up
  (`devQ_eq_zero_of_lt`), while the honest ledger is empty there for degree reasons.

## Trust boundary

Nine of the twelve declarations below are new supporting lemmas (the generic `devQ` API, the
`biRead`/`reass` toolkit, the coefficient-degree bookkeeping); none of them restates a
committed node, and each is a lemma ABOUT the landed C.71/B.02 definitions, never a new
reading of them.  The two signed statements are the stub's, binder for binder, up to the
documented `hjp` fence.

**DEPENDS.** C.11 (`dv2Hgt`, imported for the pin clause's statement context) · C.42/C.43
(`TowerDatum`, `composedKey`) · C.44 (`levelDatum`) · C.50 (`slotOffset`/`gridWeight`) ·
C.71 (`shadowDev`, `devQ`, `biRead`, `margin`) · B.02/B.03/B.04/B.05/B.06 (`dev` and its
uniqueness) · B.32a/B.35a (`dev` additivity and shift).

**SIZE.** ~40 + ~30 lines signed (the two landed clauses) over ~330 lines of new API.

**SOURCE.** `lean/notes/openmath/LAWEW_PROOF_2026-08-16.md` §0–§3; OM-10 §2.4 (LEG E).

**TEETH.** The node's numeric leg is `verification/openmath/ewbs2_lawew_cert.py`
(GREEN 2796/0, 5 teeth); this file adds the clause-(a) scope-fence refutation
`verification/c127_nox_jp2_refutation.py` (6 violating rows at two primes, 30 faithful
control rows, battery cross-check 36/36).

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).  Two of the node's three signed statements are
landed; `lawEW_pin` is BLOCKED, with the exact gap recorded in
`notes/C127_PIN_BLOCKED_2026-08-16.md`.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Polynomial

/-! ## Part 1 — the generic development API -/

section DevQAPI

variable {R : Type*} [CommRing R] [Nontrivial R] {Ψ : Polynomial R}

omit [Nontrivial R] in
theorem devQ_of_zero (Ψ : Polynomial R) : ∀ j : ℕ, devQ Ψ (0 : Polynomial R) j = 0 := by
  intro j
  induction j with
  | zero => exact zero_modByMonic Ψ
  | succ j ih =>
      show devQ Ψ ((0 : Polynomial R) /ₘ Ψ) j = 0
      rw [zero_divByMonic]; exact ih

private theorem add_divByMonicQ (hΨ : Ψ.Monic) (a b : Polynomial R) :
    (a + b) /ₘ Ψ = a /ₘ Ψ + b /ₘ Ψ :=
  (div_modByMonic_unique (a /ₘ Ψ + b /ₘ Ψ) (a %ₘ Ψ + b %ₘ Ψ) hΨ
    ⟨by
      have ha := modByMonic_add_div a Ψ
      have hb := modByMonic_add_div b Ψ
      rw [mul_add]; linear_combination ha + hb,
     lt_of_le_of_lt (degree_add_le _ _)
       (max_lt (degree_modByMonic_lt a hΨ) (degree_modByMonic_lt b hΨ))⟩).1

theorem devQ_add (hΨ : Ψ.Monic) (a b : Polynomial R) (j : ℕ) :
    devQ Ψ (a + b) j = devQ Ψ a j + devQ Ψ b j := by
  induction j generalizing a b with
  | zero => exact add_modByMonic a b
  | succ j ih =>
      show devQ Ψ ((a + b) /ₘ Ψ) j = _
      rw [add_divByMonicQ hΨ]; exact ih _ _

omit [Nontrivial R] in
theorem devQ_mul_pow (hΨ : Ψ.Monic) :
    ∀ (t : ℕ) (x : Polynomial R) (s : ℕ), devQ Ψ (x * Ψ ^ t) (t + s) = devQ Ψ x s := by
  intro t
  induction t with
  | zero => intro x s; simp
  | succ t ih =>
      intro x s
      have hidx : t + 1 + s = (t + s) + 1 := by omega
      have hdiv : (x * Ψ ^ (t + 1)) /ₘ Ψ = x * Ψ ^ t := by
        have hrw : x * Ψ ^ (t + 1) = Ψ * (x * Ψ ^ t) := by rw [pow_succ]; ring
        rw [hrw, mul_divByMonic_cancel_left _ hΨ]
      rw [hidx]
      show devQ Ψ ((x * Ψ ^ (t + 1)) /ₘ Ψ) (t + s) = _
      rw [hdiv, ih]

omit [Nontrivial R] in
theorem devQ_mul_pow_of_lt (hΨ : Ψ.Monic) :
    ∀ (t : ℕ) (x : Polynomial R) (j : ℕ), j < t → devQ Ψ (x * Ψ ^ t) j = 0 := by
  intro t
  induction t with
  | zero => intro x j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ t ih =>
      intro x j hj
      have hdiv : (x * Ψ ^ (t + 1)) /ₘ Ψ = x * Ψ ^ t := by
        have hrw : x * Ψ ^ (t + 1) = Ψ * (x * Ψ ^ t) := by rw [pow_succ]; ring
        rw [hrw, mul_divByMonic_cancel_left _ hΨ]
      match j with
      | 0 =>
          have hdvd : Ψ ∣ x * Ψ ^ (t + 1) := ⟨x * Ψ ^ t, by rw [pow_succ]; ring⟩
          exact (modByMonic_eq_zero_iff_dvd hΨ).2 hdvd
      | (j + 1) =>
          show devQ Ψ ((x * Ψ ^ (t + 1)) /ₘ Ψ) j = 0
          rw [hdiv]
          exact ih x j (by omega)

theorem devQ_eq_zero_of_lt (hΨ : Ψ.Monic) :
    ∀ (g : Polynomial R) (j : ℕ), g.natDegree < j * Ψ.natDegree → devQ Ψ g j = 0 := by
  intro g j
  induction j generalizing g with
  | zero => intro h; simp at h
  | succ j ih =>
      intro h
      show devQ Ψ (g /ₘ Ψ) j = 0
      by_cases hlt : g.natDegree < Ψ.natDegree
      · rw [(divByMonic_eq_zero_iff hΨ).2 (degree_lt_degree hlt)]
        exact devQ_of_zero Ψ j
      · refine ih (g /ₘ Ψ) ?_
        rw [natDegree_divByMonic g hΨ]
        rw [Nat.succ_mul] at h
        omega

theorem devQ_zero_of_degree_lt (hΨ : Ψ.Monic) {g : Polynomial R} (hg : g.degree < Ψ.degree) :
    devQ Ψ g 0 = g :=
  (modByMonic_eq_self_iff hΨ).2 hg

/-- The chain of `Ψ^μ + E·Ψ^{j'}` with `E` in-grid: `E` at coordinate `j'`, nothing else
below `μ`. -/
theorem devQ_pow_add_entry (hΨ : Ψ.Monic) {μ j' : ℕ} {E : Polynomial R}
    (hE : E.degree < Ψ.degree) {j : ℕ} (hj : j < μ) :
    devQ Ψ (Ψ ^ μ + E * Ψ ^ j') j = if j = j' then E else 0 := by
  rw [devQ_add hΨ]
  have h1 : devQ Ψ (Ψ ^ μ) j = 0 := by
    have : Ψ ^ μ = 1 * Ψ ^ μ := by ring
    rw [this]
    exact devQ_mul_pow_of_lt hΨ μ 1 j hj
  rw [h1, zero_add]
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · rw [if_neg (by omega)]
    exact devQ_mul_pow_of_lt hΨ j' E j hlt
  · subst heq
    rw [if_pos rfl]
    have := devQ_mul_pow hΨ j E 0
    rw [Nat.add_zero] at this
    rw [this]
    exact devQ_zero_of_degree_lt hΨ hE
  · rw [if_neg (by omega)]
    by_cases hE0 : E = 0
    · rw [hE0, zero_mul]; exact devQ_of_zero Ψ j
    obtain ⟨s, hs⟩ : ∃ s, j = j' + s := ⟨j - j', by omega⟩
    subst hs
    rw [devQ_mul_pow hΨ]
    refine devQ_eq_zero_of_lt hΨ E s ?_
    have hEd : E.natDegree < Ψ.natDegree := natDegree_lt_natDegree hE0 hE
    have hs1 : 1 ≤ s := by omega
    calc E.natDegree < Ψ.natDegree := hEd
      _ = 1 * Ψ.natDegree := by ring
      _ ≤ s * Ψ.natDegree := Nat.mul_le_mul_right _ hs1

end DevQAPI

/-! ## Part 2 — the frame side: `biRead`, the in-grid transfer, and reassembly -/

section BiReadAPI

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem KeyFrame.natDegree_key_pos (F : KeyFrame O π) : 0 < F.key.natDegree := by
  rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁

theorem KeyFrame.nontrivial_adjoinRoot (F : KeyFrame O π) : Nontrivial (AdjoinRoot F.key) := by
  refine AdjoinRoot.nontrivial _ ?_
  intro h
  rw [degree_eq_natDegree F.hmonic.ne_zero] at h
  have hz : F.key.natDegree = 0 := by exact_mod_cast h
  have := F.natDegree_key_pos
  omega

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- `devQ` at the base ring `O` IS B.02's `dev` (C.71's unfolding check, as a theorem). -/
theorem devQ_eq_dev (φ : Polynomial O) (j : ℕ) : ∀ g : Polynomial O, devQ φ g j = dev φ g j := by
  induction j with
  | zero => intro g; rfl
  | succ k ih => intro g; exact ih (g /ₘ φ)

/-- Every coefficient of `biRead F g` is the class mod `Φ′` of the corresponding `Φ′`-digit —
including past `g.natDegree`, where both sides vanish. -/
theorem biRead_coeff (F : KeyFrame O π) (g : Polynomial O) (b : ℕ) :
    (biRead F g).coeff b = AdjoinRoot.mk F.key (dev F.key g b) := by
  classical
  rw [biRead, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (g.natDegree + 1)) b
    (fun b' => AdjoinRoot.mk F.key (dev F.key g b'))]
  by_cases hb : b ∈ Finset.range (g.natDegree + 1)
  · rw [if_pos hb]
  · rw [if_neg hb]
    rw [Finset.mem_range, not_lt] at hb
    have hzero : dev F.key g b = 0 := by
      refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos g b ?_
      calc g.natDegree < b := by omega
        _ = b * 1 := (Nat.mul_one b).symm
        _ ≤ b * F.key.natDegree := Nat.mul_le_mul_left b F.natDegree_key_pos
    rw [hzero, map_zero]

/-- **In-grid transfer (honest side).**  If every coefficient of the two-variable
`Ap ∈ O[x][Y]` is in-grid (degree `< D′`), then the `Φ′`-digits of `Ap(Φ′)` ARE the
coefficients of `Ap`: uniqueness of the development (B.06). -/
theorem dev_eval_eq_coeff (F : KeyFrame O π) {Ap : Polynomial (Polynomial O)}
    (hdeg : ∀ i, (Ap.coeff i).degree < F.key.degree) (b : ℕ) :
    dev F.key (Polynomial.eval F.key Ap) b = Ap.coeff b := by
  have hd := F.natDegree_key_pos
  have hsum : ∑ j ∈ Finset.range (Ap.natDegree + 1), Ap.coeff j * F.key ^ j
      = Polynomial.eval F.key Ap := (eval_eq_sum_range F.key).symm
  have main := dev_unique F.hmonic hd (a := fun j => Ap.coeff j) (k := Ap.natDegree + 1)
    hdeg hsum
  by_cases hb : b < Ap.natDegree + 1
  · exact (main b hb).symm
  · rw [not_lt] at hb
    have hcoeff : Ap.coeff b = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff]
    refine dev_eq_zero_of_lt F.hmonic hd _ b ?_
    have hdegle : ∀ j, (Ap.coeff j).natDegree ≤ F.key.natDegree - 1 := by
      intro j
      by_cases h0 : Ap.coeff j = 0
      · simp [h0]
      · have := natDegree_lt_natDegree h0 (hdeg j)
        omega
    have hbound : (Polynomial.eval F.key Ap).natDegree
        ≤ (F.key.natDegree - 1) + Ap.natDegree * F.key.natDegree := by
      rw [eval_eq_sum_range F.key]
      refine natDegree_sum_le_of_forall_le _ _ ?_
      intro j hj
      rw [Finset.mem_range] at hj
      calc (Ap.coeff j * F.key ^ j).natDegree
          ≤ (Ap.coeff j).natDegree + (F.key ^ j).natDegree := natDegree_mul_le
        _ ≤ (F.key.natDegree - 1) + j * F.key.natDegree :=
            Nat.add_le_add (hdegle j) natDegree_pow_le
        _ ≤ (F.key.natDegree - 1) + Ap.natDegree * F.key.natDegree :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have hmul : (Ap.natDegree + 1) * F.key.natDegree ≤ b * F.key.natDegree :=
      Nat.mul_le_mul_right _ hb
    have hexp : (Ap.natDegree + 1) * F.key.natDegree
        = Ap.natDegree * F.key.natDegree + F.key.natDegree := by ring
    omega

/-- **In-grid transfer (shadow side).**  Under the same in-grid hypothesis the two-variable read
`biRead` of `Ap(Φ′)` is the coefficient-wise reduction of `Ap` — a RING MAP image, which is what
makes the chain computable. -/
theorem biRead_eval_eq_map (F : KeyFrame O π) {Ap : Polynomial (Polynomial O)}
    (hdeg : ∀ i, (Ap.coeff i).degree < F.key.degree) :
    biRead F (Polynomial.eval F.key Ap) = Ap.map (AdjoinRoot.mk F.key) := by
  ext b
  rw [biRead_coeff, dev_eval_eq_coeff F hdeg, coeff_map]

/-- The reassembly half of `shadowDev` (C.71 (iii)): the canonical degree-`< D′`
representatives of a `Z`-polynomial's coefficients, read against the powers of `Φ′`. -/
noncomputable def reass (F : KeyFrame O π) (S : Polynomial (AdjoinRoot F.key)) : Polynomial O :=
  (Finset.range (S.natDegree + 1)).sum fun b =>
    (AdjoinRoot.modByMonicHom F.hmonic (S.coeff b)) * F.key ^ b

/-- `shadowDev` IS reassembly applied to the transported chain (C.71's body, named). -/
theorem shadowDev_eq_reass {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (f : Polynomial O) (j : ℕ) :
    shadowDev T f j = reass F (devQ (biRead F (composedKey T)) (biRead F f) j) := rfl

/-- Reassembly may be summed over any range past the degree. -/
theorem reass_eq_sum_range (F : KeyFrame O π) (S : Polynomial (AdjoinRoot F.key)) {N : ℕ}
    (hN : S.natDegree < N) :
    reass F S = (Finset.range N).sum fun b =>
      (AdjoinRoot.modByMonicHom F.hmonic (S.coeff b)) * F.key ^ b := by
  simp only [reass]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro b _ hb
    rw [Finset.mem_range, not_lt] at hb
    rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]

theorem reass_zero (F : KeyFrame O π) : reass F 0 = 0 := by
  simp [reass]

theorem reass_add (F : KeyFrame O π) (S₁ S₂ : Polynomial (AdjoinRoot F.key)) :
    reass F (S₁ + S₂) = reass F S₁ + reass F S₂ := by
  set N := max (max S₁.natDegree S₂.natDegree) (S₁ + S₂).natDegree + 1 with hNdef
  rw [reass_eq_sum_range F _ (N := N) (by omega), reass_eq_sum_range F S₁ (N := N) (by omega),
    reass_eq_sum_range F S₂ (N := N) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coeff_add, map_add, add_mul]

/-- Reassembly of a `Z`-monomial: the canonical representative times the power of `Φ′`. -/
theorem reass_C_mul_X_pow (F : KeyFrame O π) (u : AdjoinRoot F.key) (b : ℕ) :
    reass F (Polynomial.C u * Polynomial.X ^ b)
      = (AdjoinRoot.modByMonicHom F.hmonic u) * F.key ^ b := by
  classical
  have hdeg : (Polynomial.C u * Polynomial.X ^ b).natDegree < b + 1 :=
    lt_of_le_of_lt (natDegree_C_mul_le u (Polynomial.X ^ b))
      (by simpa using Nat.lt_succ_of_le (natDegree_X_pow_le b))
  rw [reass_eq_sum_range F _ hdeg]
  have hcoeff : ∀ b' : ℕ, (Polynomial.C u * Polynomial.X ^ b).coeff b'
      = if b' = b then u else 0 := by
    intro b'
    rw [coeff_C_mul, coeff_X_pow]
    split <;> simp_all
  simp only [hcoeff]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
  · intro b' _ hne
    rw [if_neg hne, map_zero, zero_mul]
  · intro hb
    exact absurd (Finset.self_mem_range_succ b) hb

/-- Reassembly of the image of an in-grid two-variable polynomial: each coefficient is its own
canonical representative, so reassembly inverts `biRead` on the in-grid locus. -/
theorem reass_map_C_mul_X_pow (F : KeyFrame O π) (E : Polynomial O) (b : ℕ)
    (hE : E.degree < F.key.degree) :
    reass F (Polynomial.C (AdjoinRoot.mk F.key E) * Polynomial.X ^ b) = E * F.key ^ b := by
  rw [reass_C_mul_X_pow, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff F.hmonic).2 hE]

/-- **NODE C.129, clause (b)** (the C127 record's piece 2) — *the `Φ′`-digits of a REASSEMBLY
are the canonical representatives of its coefficients.*  Landed HERE rather than in
`Uniformity/ChapC/C129.lean` because it reads `reass`, whose carrier is this module: a
`C129 → C127` import would cycle against this file's own `C129` import (see C129's header and
the blueprint's DAG adjudication `C.129 → C.71`).  Its frame-generic helper
`degree_modByMonicHom_lt` is in `C129.lean`. -/
theorem dev_reass (F : KeyFrame O π) (S : Polynomial (AdjoinRoot F.key)) (b : ℕ) :
    dev F.key (reass F S) b = AdjoinRoot.modByMonicHom F.hmonic (S.coeff b) := by
  classical
  set N := S.natDegree + 1 with hN
  set Ap : Polynomial (Polynomial O) :=
    ∑ i ∈ Finset.range N,
      Polynomial.C (AdjoinRoot.modByMonicHom F.hmonic (S.coeff i)) * Polynomial.X ^ i with hAp
  have hcoeff : ∀ i, Ap.coeff i = AdjoinRoot.modByMonicHom F.hmonic (S.coeff i) := by
    intro i
    rw [hAp, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range N) i
      (fun i' => AdjoinRoot.modByMonicHom F.hmonic (S.coeff i'))]
    by_cases hi : i ∈ Finset.range N
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Finset.mem_range, not_lt] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have heval : Polynomial.eval F.key Ap = reass F S := by
    rw [hAp, reass_eq_sum_range F S (N := N) (by omega)]
    simp [eval_finsetSum]
  have hdeg : ∀ i, (Ap.coeff i).degree < F.key.degree := by
    intro i
    rw [hcoeff i]
    exact degree_modByMonicHom_lt F _
  rw [← heval, dev_eval_eq_coeff F hdeg b, hcoeff b]

/-! ### The coefficient-degree toolkit (the in-grid bookkeeping of (F5)) -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natDegree_coeff_mul_le {p q : Polynomial (Polynomial O)} {d e : ℕ}
    (hp : ∀ i, (p.coeff i).natDegree ≤ d) (hq : ∀ i, (q.coeff i).natDegree ≤ e) :
    ∀ i, ((p * q).coeff i).natDegree ≤ d + e := by
  intro i
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ ?_
  rintro ⟨x, y⟩ _
  exact le_trans natDegree_mul_le (Nat.add_le_add (hp x) (hq y))

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natDegree_coeff_pow_le {p : Polynomial (Polynomial O)} {d : ℕ}
    (hp : ∀ i, (p.coeff i).natDegree ≤ d) : ∀ (n i : ℕ), ((p ^ n).coeff i).natDegree ≤ n * d := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [pow_zero, coeff_one]
      split <;> simp
  | succ n ih =>
      intro i
      rw [pow_succ]
      have := natDegree_coeff_mul_le (p := p ^ n) (q := p) (d := n * d) (e := d) ih hp i
      calc ((p ^ n * p).coeff i).natDegree ≤ n * d + d := this
        _ = (n + 1) * d := by ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natDegree_coeff_add_le {p q : Polynomial (Polynomial O)} {d : ℕ}
    (hp : ∀ i, (p.coeff i).natDegree ≤ d) (hq : ∀ i, (q.coeff i).natDegree ≤ d) :
    ∀ i, ((p + q).coeff i).natDegree ≤ d := by
  intro i
  rw [coeff_add]
  exact le_trans (natDegree_add_le _ _) (max_le (hp i) (hq i))

/-- The bridge from the `ℕ`-degree bookkeeping to B.06's `degree`-shaped in-grid hypothesis. -/
theorem degree_coeff_lt_of_natDegree_le (F : KeyFrame O π) {p : Polynomial (Polynomial O)} {d : ℕ}
    (h : ∀ i, (p.coeff i).natDegree ≤ d) (hd : d < F.key.natDegree) :
    ∀ i, (p.coeff i).degree < F.key.degree :=
  fun i => degree_lt_degree (lt_of_le_of_lt (h i) hd)

theorem shadowDev_of_ingrid {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {Kp Ap : Polynomial (Polynomial O)}
    (hK : ∀ i, (Kp.coeff i).degree < F.key.degree)
    (hA : ∀ i, (Ap.coeff i).degree < F.key.degree)
    (hKe : Polynomial.eval F.key Kp = composedKey T)
    {f : Polynomial O} (hAe : Polynomial.eval F.key Ap = f) (j : ℕ) :
    shadowDev T f j
      = reass F (devQ (Kp.map (AdjoinRoot.mk F.key)) (Ap.map (AdjoinRoot.mk F.key)) j) := by
  rw [shadowDev_eq_reass, ← hKe, ← hAe, biRead_eval_eq_map F hK, biRead_eval_eq_map F hA]

end BiReadAPI


/-! ## Part 4 — the seed division census (§3 Step 3) and the discrepancy in closed form

The pin clause `lawEW_pin` is NOT landed (see the module docstring and
`notes/C127_PIN_BLOCKED_2026-08-16.md`).  What IS landed here is everything up to its last
two steps: the exact quotient/remainder of the seed division (§3 Step 3) and the resulting
CLOSED FORM of the two low-coordinate discrepancies (§3 Steps 1–3 assembled).  What remains
for the pin is Step 4/5 only — the slot heights of those two explicit polynomials. -/

section Census

variable {R : Type*} [CommRing R]

/-- §3 Step 3's quotient `q = Σ_{k≤b} (−1)^k g P^k Y^{b−k}`. -/
noncomputable def seedQuot (P g : R) (b : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (b + 1), Polynomial.C ((-1 : R) ^ k * g * P ^ k) * Polynomial.X ^ (b - k)

/-- §3 Step 3's remainder
`r = (−1)^{b+1} g P^{b+1} Y^{m−1} + Σ_{k≤b} (−1)^{k+1} g P^k c₀ Y^{b−k}`. -/
noncomputable def seedRem (P c0 g : R) (m b : ℕ) : Polynomial R :=
  Polynomial.C ((-1 : R) ^ (b + 1) * g * P ^ (b + 1)) * Polynomial.X ^ (m - 1)
    + ∑ k ∈ Finset.range (b + 1),
        Polynomial.C ((-1 : R) ^ (k + 1) * g * P ^ k * c0) * Polynomial.X ^ (b - k)

private noncomputable def seedTerm (P g : R) (b m k : ℕ) : Polynomial R :=
  Polynomial.C ((-1 : R) ^ k * g * P ^ k) * Polynomial.X ^ (b + m - k)

/-- **The seed division census** (the note's §3 Step 3, telescoped): the monic division of
the seed `g·Y^{b+m}` by the trinomial key `K = Y^m + P·Y^{m−1} + c₀` in closed form.  The
telescoping is `Σ_k (u_k − u_{k+1}) = u_0 − u_{b+1}` at `u_k = (−1)^k g P^k Y^{b+m−k}`; the
`P`-column of the product supplies exactly `−u_{k+1}`. -/
theorem seed_division_census (P c0 g : R) {m b : ℕ} (hm : 1 ≤ m) :
    Polynomial.C g * Polynomial.X ^ (b + m)
      = seedQuot P g b * (Polynomial.X ^ m + Polynomial.C P * Polynomial.X ^ (m - 1)
          + Polynomial.C c0) + seedRem P c0 g m b := by
  classical
  have hterm : ∀ k ∈ Finset.range (b + 1),
      Polynomial.C ((-1 : R) ^ k * g * P ^ k) * Polynomial.X ^ (b - k)
          * (Polynomial.X ^ m + Polynomial.C P * Polynomial.X ^ (m - 1) + Polynomial.C c0)
        = (seedTerm P g b m k - seedTerm P g b m (k + 1))
          + Polynomial.C ((-1 : R) ^ k * g * P ^ k * c0) * Polynomial.X ^ (b - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hx1 : (Polynomial.X : Polynomial R) ^ (b - k) * Polynomial.X ^ m
        = Polynomial.X ^ (b + m - k) := by rw [← pow_add]; congr 1; omega
    have hx2 : (Polynomial.X : Polynomial R) ^ (b - k) * Polynomial.X ^ (m - 1)
        = Polynomial.X ^ (b + m - (k + 1)) := by rw [← pow_add]; congr 1; omega
    have hsign : Polynomial.C ((-1 : R) ^ k * g * P ^ k * P)
        = - Polynomial.C ((-1 : R) ^ (k + 1) * g * P ^ (k + 1)) := by
      rw [← Polynomial.C_neg]
      congr 1
      ring
    have expand : Polynomial.C ((-1 : R) ^ k * g * P ^ k) * Polynomial.X ^ (b - k)
          * (Polynomial.X ^ m + Polynomial.C P * Polynomial.X ^ (m - 1) + Polynomial.C c0)
        = Polynomial.C ((-1 : R) ^ k * g * P ^ k)
              * (Polynomial.X ^ (b - k) * Polynomial.X ^ m)
          + Polynomial.C ((-1 : R) ^ k * g * P ^ k * P)
              * (Polynomial.X ^ (b - k) * Polynomial.X ^ (m - 1))
          + Polynomial.C ((-1 : R) ^ k * g * P ^ k * c0) * Polynomial.X ^ (b - k) := by
      simp only [Polynomial.C_mul]
      ring
    rw [expand, hx1, hx2, hsign]
    simp only [seedTerm]
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [seedQuot, Finset.sum_mul, hsum, Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun k => seedTerm P g b m k) (b + 1)]
  have h0 : seedTerm P g b m 0 = Polynomial.C g * Polynomial.X ^ (b + m) := by
    simp [seedTerm]
  have hb1 : seedTerm P g b m (b + 1)
      = Polynomial.C ((-1 : R) ^ (b + 1) * g * P ^ (b + 1)) * Polynomial.X ^ (m - 1) := by
    have he : b + m - (b + 1) = m - 1 := by omega
    simp only [seedTerm, he]
  have hsum_neg : ∑ k ∈ Finset.range (b + 1),
        Polynomial.C ((-1 : R) ^ k * g * P ^ k * c0) * Polynomial.X ^ (b - k)
      = - ∑ k ∈ Finset.range (b + 1),
        Polynomial.C ((-1 : R) ^ (k + 1) * g * P ^ k * c0) * Polynomial.X ^ (b - k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_mul, ← Polynomial.C_neg]
    congr 2
    ring
  rw [h0, hb1, hsum_neg, seedRem]
  abel

theorem seedQuot_natDegree_le (P g : R) (b : ℕ) : (seedQuot P g b).natDegree ≤ b := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact le_trans (natDegree_C_mul_le _ _) (le_trans (natDegree_X_pow_le _) (by omega))

theorem seedRem_natDegree_le (P c0 g : R) {m b : ℕ} (hb : b < m) :
    (seedRem P c0 g m b).natDegree ≤ m - 1 := by
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (natDegree_C_mul_le _ _) (natDegree_X_pow_le _)
  · refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    exact le_trans (natDegree_C_mul_le _ _) (le_trans (natDegree_X_pow_le _) (by omega))

/-- The seed's chain coordinates: `r` at `0`, `q` at `1` (and nothing above, by
`devQ_eq_zero_of_lt`).  This is §3 Step 2's "one division" made explicit. -/
theorem devQ_seed [Nontrivial R] (P c0 g : R) {m b : ℕ} (hb : b < m)
    {K : Polynomial R} (hK : K = Polynomial.X ^ m + Polynomial.C P * Polynomial.X ^ (m - 1)
      + Polynomial.C c0) (hKm : K.Monic) (hKd : K.natDegree = m) :
    devQ K (Polynomial.C g * Polynomial.X ^ (b + m)) 0 = seedRem P c0 g m b
      ∧ devQ K (Polynomial.C g * Polynomial.X ^ (b + m)) 1 = seedQuot P g b := by
  have hm : 1 ≤ m := by omega
  have hsplit : Polynomial.C g * Polynomial.X ^ (b + m)
      = seedQuot P g b * K ^ 1 + seedRem P c0 g m b := by
    rw [pow_one, hK]; exact seed_division_census P c0 g hm
  have hrdeg : (seedRem P c0 g m b).degree < K.degree :=
    degree_lt_degree (by rw [hKd]; exact lt_of_le_of_lt (seedRem_natDegree_le P c0 g hb) (by omega))
  have hqdeg : (seedQuot P g b).degree < K.degree :=
    degree_lt_degree (by rw [hKd]; exact lt_of_le_of_lt (seedQuot_natDegree_le P g b) hb)
  constructor
  · rw [hsplit, devQ_add hKm, devQ_mul_pow_of_lt hKm 1 _ 0 (by omega), zero_add,
      devQ_zero_of_degree_lt hKm hrdeg]
  · rw [hsplit, devQ_add hKm]
    have h1 : devQ K (seedQuot P g b * K ^ 1) 1 = seedQuot P g b := by
      have := devQ_mul_pow hKm 1 (seedQuot P g b) 0
      rw [Nat.add_zero] at this
      rw [this, devQ_zero_of_degree_lt hKm hqdeg]
    have h2 : devQ K (seedRem P c0 g m b) 1 = 0 := by
      refine devQ_eq_zero_of_lt hKm _ 1 ?_
      rw [one_mul, hKd]
      exact lt_of_le_of_lt (seedRem_natDegree_le P c0 g hb) (by omega)
    rw [h1, h2, add_zero]

end Census

/-! ## Part 3 — the trinomial single-crossing frame -/

section LawEW

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natDegree_coeff_X_pow_le (k i : ℕ) :
    (((Polynomial.X : Polynomial (Polynomial O)) ^ k).coeff i).natDegree ≤ 0 := by
  rw [coeff_X_pow]
  split <;> simp

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natDegree_coeff_C_mul_X_pow_le (u : Polynomial O) (k i : ℕ) :
    ((Polynomial.C u * (Polynomial.X : Polynomial (Polynomial O)) ^ k).coeff i).natDegree
      ≤ u.natDegree := by
  rw [coeff_C_mul, coeff_X_pow]
  split <;> simp

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natDegree_coeff_C_le (u : Polynomial O) (i : ℕ) :
    ((Polynomial.C u : Polynomial (Polynomial O)).coeff i).natDegree ≤ u.natDegree := by
  rw [coeff_C]
  split <;> simp

/-- The **trinomial key datum** `K(Y) = Y^{f₂} + P·Y^{f₂−1} + c₀` of (F2), as an element of
`O[x][Y]`: the two-variable presentation of `Φ₂` that carries the whole proof. -/
noncomputable def trinomialY (P c0 : Polynomial O) (m : ℕ) : Polynomial (Polynomial O) :=
  Polynomial.X ^ m + Polynomial.C P * Polynomial.X ^ (m - 1) + Polynomial.C c0

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem trinomialY_coeff_natDegree_le {P c0 : Polynomial O} {d m : ℕ}
    (hP : P.natDegree ≤ d) (hc0 : c0.natDegree ≤ d) :
    ∀ i, ((trinomialY P c0 m).coeff i).natDegree ≤ d := by
  refine natDegree_coeff_add_le (natDegree_coeff_add_le ?_ ?_) ?_
  · exact fun i => le_trans (natDegree_coeff_X_pow_le m i) (Nat.zero_le d)
  · exact fun i => le_trans (natDegree_coeff_C_mul_X_pow_le P (m - 1) i) hP
  · exact fun i => le_trans (natDegree_coeff_C_le c0 i) hc0

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem trinomialY_eval (P c0 : Polynomial O) {m : ℕ} (x : Polynomial O) :
    Polynomial.eval x (trinomialY P c0 m) = x ^ m + P * x ^ (m - 1) + c0 := by
  simp [trinomialY]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The transported trinomial key is monic of `Z`-degree `m` over any nontrivial base. -/
theorem trinomialY_map_monic {R : Type*} [CommRing R] [Nontrivial R] (ρ : Polynomial O →+* R)
    (P c0 : Polynomial O) {m : ℕ} (hm : 2 ≤ m) :
    ((trinomialY P c0 m).map ρ).Monic ∧ ((trinomialY P c0 m).map ρ).natDegree = m := by
  have hmap : (trinomialY P c0 m).map ρ
      = Polynomial.X ^ m + (Polynomial.C (ρ P) * Polynomial.X ^ (m - 1) + Polynomial.C (ρ c0)) := by
    simp only [trinomialY, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, add_assoc]
  have hlt : (Polynomial.C (ρ P) * Polynomial.X ^ (m - 1) + Polynomial.C (ρ c0)).degree
      < ((Polynomial.X : Polynomial R) ^ m).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le (m - 1) (ρ P)) (by exact_mod_cast by omega)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast by omega)
  refine ⟨?_, ?_⟩
  · rw [hmap]; exact (monic_X_pow m).add_of_left hlt
  · refine natDegree_eq_of_degree_eq_some ?_
    rw [hmap, degree_add_eq_left_of_degree_lt hlt, degree_X_pow]

/-! ### Clause (a) — no crossing -/

-- The frozen signature is kept binder-for-binder (A-C.4).  Clause (a) consumes only the
-- in-grid bookkeeping, so nine signed hypotheses are carried but not used: `hπ`, `hh`, `hω`,
-- `hkey`, `hi₂`, `hc₂`, `hc₀`, `hv₀`, `hc` — the shape of `Φ′` (`hkey`), the unit status of
-- the three coefficients and the second on-side relation (`hv₀`) enter only at the crossing
-- clauses, where the wrap `x^{D′} = Φ′ + πω` and the slot valuations are read.  `hu₂` and
-- `hgrid` DO fire (the latter is (F5), the in-grid hypothesis the whole clause rests on).
set_option linter.unusedVariables false in
theorem lawEW_faithful_of_nox {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) [Finite (ResidueField O)]
    (hh : F.h = 1) (hf₁ : F.f₁ = 1) (he₂ : T.e₂ = 1)
    {ω : O} (hω : IsUnit ω)
    (hkey : F.key = Polynomial.X ^ F.e₁ - Polynomial.C (π * ω))
    {i₂ v₂ v₀ : ℕ} (hi₂ : 1 ≤ i₂) {c₂ c₀ : O} (hc₂ : IsUnit c₂) (hc₀ : IsUnit c₀)
    (hcomp : composedKey T
      = F.key ^ T.f₂
        + Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂ * F.key ^ (T.f₂ - 1)
        + Polynomial.C (c₀ * π ^ v₀))
    (hu₂ : T.u₂ = F.e₁ * v₂ + i₂) (hv₀ : F.e₁ * v₀ = T.f₂ * T.u₂)
    {μ₂ : ℕ} (hμ₂ : 2 ≤ μ₂) (hgrid : μ₂ * i₂ < F.e₁)
    {c : O} (hc : IsUnit c) (α a b j' : ℕ) (ha : a < F.e₁) (hb : b < T.f₂)
    {f : Polynomial O}
    (hf : f = composedKey T ^ μ₂
      + Polynomial.C (c * π ^ α) * Polynomial.X ^ a * F.key ^ b
        * composedKey T ^ j')
    (hnox : j' = 0 ∨ a + i₂ < F.e₁) (hjp : j' ≤ 1) {j : ℕ} (hj : j < μ₂) :
    shadowDev T f j = dev (composedKey T) f j := by
  haveI : Nontrivial (AdjoinRoot F.key) := F.nontrivial_adjoinRoot
  have hkeydeg : F.key.natDegree = F.e₁ := by rw [F.hdeg, hf₁, mul_one]
  have hf₂ : 2 ≤ T.f₂ := by have h := T.hcomp; rw [he₂, one_mul] at h; exact h
  have hi₂lt : i₂ < F.e₁ :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left i₂ (by omega)) hgrid
  set Pp : Polynomial O := Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂ with hPp
  set c0p : Polynomial O := Polynomial.C (c₀ * π ^ v₀) with hc0p
  set Ep : Polynomial O := Polynomial.C (c * π ^ α) * Polynomial.X ^ a with hEp
  set Kp : Polynomial (Polynomial O) := trinomialY Pp c0p T.f₂ with hKp
  set Ap : Polynomial (Polynomial O) :=
    Kp ^ μ₂ + (Polynomial.C Ep * Polynomial.X ^ b) * Kp ^ j' with hAp
  -- the one-variable degree data
  have hPpdeg : Pp.natDegree ≤ i₂ := by
    rw [hPp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hc0pdeg : c0p.natDegree ≤ i₂ := by rw [hc0p, natDegree_C]; exact Nat.zero_le _
  have hEpdeg : Ep.natDegree ≤ a := by
    rw [hEp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hEpkey : Ep.degree < F.key.degree :=
    degree_lt_degree (lt_of_le_of_lt hEpdeg (by rw [hkeydeg]; exact ha))
  -- both two-variable data are in-grid
  have hKgridN : ∀ i, (Kp.coeff i).natDegree ≤ i₂ := by
    rw [hKp]; exact trinomialY_coeff_natDegree_le hPpdeg hc0pdeg
  have hKgrid : ∀ i, (Kp.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hKgridN (by rw [hkeydeg]; exact hi₂lt)
  have hdlt : max (μ₂ * i₂) (a + j' * i₂) < F.e₁ := by
    refine max_lt hgrid ?_
    rcases hnox with h0 | hlt
    · subst h0; simpa using ha
    · interval_cases j'
      · simpa using ha
      · simpa using hlt
  have hAgridN : ∀ i, (Ap.coeff i).natDegree ≤ max (μ₂ * i₂) (a + j' * i₂) := by
    rw [hAp]
    refine natDegree_coeff_add_le ?_ ?_
    · exact fun i => le_trans (natDegree_coeff_pow_le hKgridN μ₂ i) (le_max_left _ _)
    · exact fun i => le_trans (natDegree_coeff_mul_le
        (fun i' => le_trans (natDegree_coeff_C_mul_X_pow_le Ep b i') hEpdeg)
        (natDegree_coeff_pow_le hKgridN j') i) (le_max_right _ _)
  have hAgrid : ∀ i, (Ap.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hAgridN (by rw [hkeydeg]; exact hdlt)
  -- the two evaluations
  have hKe : Polynomial.eval F.key Kp = composedKey T := by
    rw [hKp, trinomialY_eval, hcomp]
  have hAe : Polynomial.eval F.key Ap = f := by
    rw [hAp]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, hKe]
    rw [hf]
  -- the level-2 key is monic of degree `D₂`
  have hpowmonic : (F.key ^ T.f₂).Monic := F.hmonic.pow _
  have hpowdeg : (F.key ^ T.f₂).natDegree = T.f₂ * F.e₁ := by rw [natDegree_pow, hkeydeg]
  obtain ⟨k, hk⟩ : ∃ k, T.f₂ = k + 1 := ⟨T.f₂ - 1, by omega⟩
  have hstep : (T.f₂ - 1) * F.e₁ + F.e₁ = T.f₂ * F.e₁ := by rw [hk]; simp; ring
  have hrestN : (Pp * F.key ^ (T.f₂ - 1) + c0p).natDegree < T.f₂ * F.e₁ := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · calc (Pp * F.key ^ (T.f₂ - 1)).natDegree
          ≤ Pp.natDegree + (F.key ^ (T.f₂ - 1)).natDegree := natDegree_mul_le
        _ ≤ i₂ + (T.f₂ - 1) * F.e₁ := by
            refine Nat.add_le_add hPpdeg ?_
            rw [natDegree_pow, hkeydeg]
        _ < T.f₂ * F.e₁ := by omega
    · rw [hc0p]
      simp only [natDegree_C]
      have : 0 < F.e₁ := F.he₁
      calc 0 < F.e₁ := this
        _ ≤ T.f₂ * F.e₁ := Nat.le_mul_of_pos_left _ (by omega)
  have hrest : (Pp * F.key ^ (T.f₂ - 1) + c0p).degree < (F.key ^ T.f₂).degree :=
    degree_lt_degree (by rw [hpowdeg]; exact hrestN)
  have hcomp' : composedKey T = F.key ^ T.f₂ + (Pp * F.key ^ (T.f₂ - 1) + c0p) := by
    rw [hcomp]; ring
  have hΦmonic : (composedKey T).Monic := by rw [hcomp']; exact hpowmonic.add_of_left hrest
  have hΦdeg : (composedKey T).natDegree = T.f₂ * F.e₁ := by
    rw [hcomp']
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_add_eq_left_of_degree_lt hrest, degree_eq_natDegree hpowmonic.ne_zero, hpowdeg]
  -- the entry is a single development slot of the level-2 key
  have hEntryN : (Ep * F.key ^ b).natDegree < T.f₂ * F.e₁ := by
    have h1 : (Ep * F.key ^ b).natDegree ≤ a + b * F.e₁ := by
      calc (Ep * F.key ^ b).natDegree ≤ Ep.natDegree + (F.key ^ b).natDegree := natDegree_mul_le
        _ ≤ a + b * F.e₁ := by
            refine Nat.add_le_add hEpdeg ?_
            rw [natDegree_pow, hkeydeg]
    have h2 : (b + 1) * F.e₁ ≤ T.f₂ * F.e₁ := Nat.mul_le_mul_right _ hb
    have h3 : (b + 1) * F.e₁ = b * F.e₁ + F.e₁ := by ring
    omega
  have hEntry : (Ep * F.key ^ b).degree < (composedKey T).degree :=
    degree_lt_degree (by rw [hΦdeg]; exact hEntryN)
  -- the honest ledger
  have hhonest : dev (composedKey T) f j = if j = j' then Ep * F.key ^ b else 0 := by
    rw [← devQ_eq_dev]
    have hfshape : f = composedKey T ^ μ₂ + (Ep * F.key ^ b) * composedKey T ^ j' := by
      rw [hf]
    rw [hfshape]
    exact devQ_pow_add_entry hΦmonic hEntry hj
  -- the shadow ledger
  have hKbar := trinomialY_map_monic (AdjoinRoot.mk F.key) Pp c0p hf₂
  have hshadow : shadowDev T f j = if j = j' then Ep * F.key ^ b else 0 := by
    rw [shadowDev_of_ingrid T hKgrid hAgrid hKe hAe, hAp]
    have hmapA : (Kp ^ μ₂ + (Polynomial.C Ep * Polynomial.X ^ b) * Kp ^ j').map
          (AdjoinRoot.mk F.key)
        = (Kp.map (AdjoinRoot.mk F.key)) ^ μ₂
          + (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b)
            * (Kp.map (AdjoinRoot.mk F.key)) ^ j' := by
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X]
    rw [hmapA, hKp]
    have hEbar : (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b).degree
        < ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)).degree := by
      rw [degree_eq_natDegree hKbar.1.ne_zero, hKbar.2]
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le b _) (by exact_mod_cast hb)
    rw [devQ_pow_add_entry hKbar.1 hEbar hj]
    split_ifs with hjj
    · exact reass_map_C_mul_X_pow F Ep b hEpkey
    · exact reass_zero F
  rw [hshadow, hhonest]


/-! ### Clause (b) at the high coordinates — the crossing seed cannot reach `j ≥ 2` -/

-- Frozen signature (A-C.4), binder for binder.  Not consumed at this clause: `hπ`, `hh`,
-- `hc₂`, `hc₀`, `hv₀`, `hc`, `hu₂` — the unit status of the coefficients and the second
-- on-side relation are read only by the pin clause, which weighs the slots.  Consumed here
-- and NOT at clause (a): `hkey` (the wrap `x^{D′} = Φ′ + πω`, which is what turns the
-- over-grid coefficient `E′P` into the seed) and `hcross`.
set_option linter.unusedVariables false in
/-- **NODE C.127 clause (b), high coordinates.**  A crossing entry at `j′ = 1`
(`a + i₂ ≥ D′`) leaves every coordinate `j ≥ 2` faithful: the seed born by the wrap has
`Z`-degree `b + m ≤ 2m − 1`, so one division by the transported key exhausts it and the
chain is empty from coordinate `2` up, exactly where the honest ledger is empty too. -/
theorem lawEW_faithful_high {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) [Finite (ResidueField O)]
    (hh : F.h = 1) (hf₁ : F.f₁ = 1) (he₂ : T.e₂ = 1)
    {ω : O} (hω : IsUnit ω)
    (hkey : F.key = Polynomial.X ^ F.e₁ - Polynomial.C (π * ω))
    {i₂ v₂ v₀ : ℕ} (hi₂ : 1 ≤ i₂) {c₂ c₀ : O} (hc₂ : IsUnit c₂) (hc₀ : IsUnit c₀)
    (hcomp : composedKey T
      = F.key ^ T.f₂
        + Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂ * F.key ^ (T.f₂ - 1)
        + Polynomial.C (c₀ * π ^ v₀))
    (hu₂ : T.u₂ = F.e₁ * v₂ + i₂) (hv₀ : F.e₁ * v₀ = T.f₂ * T.u₂)
    {μ₂ : ℕ} (hμ₂ : 2 ≤ μ₂) (hgrid : μ₂ * i₂ < F.e₁)
    {c : O} (hc : IsUnit c) (α a b : ℕ) (ha : a < F.e₁) (hb : b < T.f₂)
    {f : Polynomial O}
    (hf : f = composedKey T ^ μ₂
      + Polynomial.C (c * π ^ α) * Polynomial.X ^ a * F.key ^ b
        * composedKey T)
    (hcross : F.e₁ ≤ a + i₂) {j : ℕ} (hj2 : 2 ≤ j) (hj : j < μ₂) :
    shadowDev T f j = dev (composedKey T) f j := by
  haveI : Nontrivial (AdjoinRoot F.key) := F.nontrivial_adjoinRoot
  have hkeydeg : F.key.natDegree = F.e₁ := by rw [F.hdeg, hf₁, mul_one]
  have hf₂ : 2 ≤ T.f₂ := by have h := T.hcomp; rw [he₂, one_mul] at h; exact h
  have hi₂lt : i₂ < F.e₁ := lt_of_le_of_lt (Nat.le_mul_of_pos_left i₂ (by omega)) hgrid
  obtain ⟨k, hk⟩ : ∃ k, T.f₂ = k + 1 := ⟨T.f₂ - 1, by omega⟩
  set Pp : Polynomial O := Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂ with hPp
  set c0p : Polynomial O := Polynomial.C (c₀ * π ^ v₀) with hc0p
  set Ep : Polynomial O := Polynomial.C (c * π ^ α) * Polynomial.X ^ a with hEp
  set s : ℕ := a + i₂ - F.e₁ with hsdef
  set gp : Polynomial O := Polynomial.C (c * π ^ α * (c₂ * π ^ v₂)) * Polynomial.X ^ s with hgp
  set Kp : Polynomial (Polynomial O) := trinomialY Pp c0p T.f₂ with hKp
  set Ent : Polynomial (Polynomial O) :=
    Polynomial.C (Ep + gp) * Polynomial.X ^ (b + T.f₂)
      + Polynomial.C (gp * Polynomial.C (π * ω)) * Polynomial.X ^ (b + T.f₂ - 1)
      + Polynomial.C (Ep * c0p) * Polynomial.X ^ b with hEnt
  set Ap : Polynomial (Polynomial O) := Kp ^ μ₂ + Ent with hAp
  -- one-variable degrees
  have hPpdeg : Pp.natDegree ≤ i₂ := by
    rw [hPp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hc0pdeg : c0p.natDegree ≤ i₂ := by rw [hc0p, natDegree_C]; exact Nat.zero_le _
  have hEpdeg : Ep.natDegree ≤ a := by
    rw [hEp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hgpdeg : gp.natDegree ≤ s := by
    rw [hgp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hslt : s < F.e₁ := by rw [hsdef]; omega
  -- the wrap: `E′·P = g·x^{D′} = g·(Φ′ + πω)` — the birth of the seed (§3 Step 1)
  have hkeyX : F.key + Polynomial.C (π * ω) = (Polynomial.X : Polynomial O) ^ F.e₁ := by
    rw [hkey]; ring
  have hsadd : s + F.e₁ = a + i₂ := by rw [hsdef]; omega
  have hEpPp : Ep * Pp = gp * (F.key + Polynomial.C (π * ω)) := by
    have hx : (Polynomial.X : Polynomial O) ^ s * Polynomial.X ^ F.e₁
        = Polynomial.X ^ a * Polynomial.X ^ i₂ := by
      rw [← pow_add, ← pow_add, hsadd]
    rw [hkeyX, hEp, hPp, hgp]
    calc Polynomial.C (c * π ^ α) * Polynomial.X ^ a
          * (Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂)
        = Polynomial.C (c * π ^ α) * Polynomial.C (c₂ * π ^ v₂)
            * (Polynomial.X ^ a * Polynomial.X ^ i₂) := by ring
      _ = Polynomial.C (c * π ^ α * (c₂ * π ^ v₂))
            * (Polynomial.X ^ s * Polynomial.X ^ F.e₁) := by
          rw [hx, ← Polynomial.C_mul]
      _ = Polynomial.C (c * π ^ α * (c₂ * π ^ v₂)) * Polynomial.X ^ s
            * Polynomial.X ^ F.e₁ := by ring
  -- both two-variable data are in-grid
  have hKgridN : ∀ i, (Kp.coeff i).natDegree ≤ i₂ := by
    rw [hKp]; exact trinomialY_coeff_natDegree_le hPpdeg hc0pdeg
  have hKgrid : ∀ i, (Kp.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hKgridN (by rw [hkeydeg]; exact hi₂lt)
  have hdlt : max (μ₂ * i₂) (max a s) < F.e₁ := max_lt hgrid (max_lt ha hslt)
  have hEntN : ∀ i, (Ent.coeff i).natDegree ≤ max a s := by
    rw [hEnt]
    refine natDegree_coeff_add_le (natDegree_coeff_add_le ?_ ?_) ?_
    · refine fun i => le_trans (natDegree_coeff_C_mul_X_pow_le _ _ i) ?_
      exact le_trans (natDegree_add_le _ _) (max_le_max hEpdeg hgpdeg)
    · refine fun i => le_trans (natDegree_coeff_C_mul_X_pow_le _ _ i) ?_
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, Nat.add_zero]
      exact le_trans hgpdeg (le_max_right _ _)
    · refine fun i => le_trans (natDegree_coeff_C_mul_X_pow_le _ _ i) ?_
      refine le_trans natDegree_mul_le ?_
      rw [hc0p, natDegree_C, Nat.add_zero]
      exact le_trans hEpdeg (le_max_left _ _)
  have hAgridN : ∀ i, (Ap.coeff i).natDegree ≤ max (μ₂ * i₂) (max a s) := by
    rw [hAp]
    refine natDegree_coeff_add_le ?_ ?_
    · exact fun i => le_trans (natDegree_coeff_pow_le hKgridN μ₂ i) (le_max_left _ _)
    · exact fun i => le_trans (hEntN i) (le_max_right _ _)
  have hAgrid : ∀ i, (Ap.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hAgridN (by rw [hkeydeg]; exact hdlt)
  -- the two evaluations: the crossing presentation IS the development (§3 Step 1)
  have hKe : Polynomial.eval F.key Kp = composedKey T := by
    rw [hKp, trinomialY_eval, hcomp]
  have hcomp' : composedKey T = F.key ^ T.f₂ + (Pp * F.key ^ (T.f₂ - 1) + c0p) := by
    rw [hcomp]; ring
  have hEnte : Polynomial.eval F.key Ent = Ep * F.key ^ b * composedKey T := by
    rw [hEnt, hcomp']
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    have e1 : b + T.f₂ - 1 = b + k := by omega
    have e2 : b + T.f₂ = b + k + 1 := by omega
    have e3 : T.f₂ - 1 = k := by omega
    have e4 : T.f₂ = k + 1 := hk
    rw [e1, e2, e3, e4]
    linear_combination (-(F.key ^ (b + k))) * hEpPp
  have hAe : Polynomial.eval F.key Ap = f := by
    rw [hAp]
    simp only [eval_add, eval_pow, hKe, hEnte]
    rw [hf]
  -- the level-2 key is monic of degree `D₂`, and the entry is one development slot
  have hpowmonic : (F.key ^ T.f₂).Monic := F.hmonic.pow _
  have hpowdeg : (F.key ^ T.f₂).natDegree = T.f₂ * F.e₁ := by rw [natDegree_pow, hkeydeg]
  have hstep : (T.f₂ - 1) * F.e₁ + F.e₁ = T.f₂ * F.e₁ := by rw [hk]; simp; ring
  have hrestN : (Pp * F.key ^ (T.f₂ - 1) + c0p).natDegree < T.f₂ * F.e₁ := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · calc (Pp * F.key ^ (T.f₂ - 1)).natDegree
          ≤ Pp.natDegree + (F.key ^ (T.f₂ - 1)).natDegree := natDegree_mul_le
        _ ≤ i₂ + (T.f₂ - 1) * F.e₁ := by
            refine Nat.add_le_add hPpdeg ?_
            rw [natDegree_pow, hkeydeg]
        _ < T.f₂ * F.e₁ := by omega
    · rw [hc0p]
      simp only [natDegree_C]
      calc 0 < F.e₁ := F.he₁
        _ ≤ T.f₂ * F.e₁ := Nat.le_mul_of_pos_left _ (by omega)
  have hrest : (Pp * F.key ^ (T.f₂ - 1) + c0p).degree < (F.key ^ T.f₂).degree :=
    degree_lt_degree (by rw [hpowdeg]; exact hrestN)
  have hΦmonic : (composedKey T).Monic := by rw [hcomp']; exact hpowmonic.add_of_left hrest
  have hΦdeg : (composedKey T).natDegree = T.f₂ * F.e₁ := by
    rw [hcomp']
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_add_eq_left_of_degree_lt hrest, degree_eq_natDegree hpowmonic.ne_zero, hpowdeg]
  have hEntryN : (Ep * F.key ^ b).natDegree < T.f₂ * F.e₁ := by
    have h1 : (Ep * F.key ^ b).natDegree ≤ a + b * F.e₁ := by
      calc (Ep * F.key ^ b).natDegree ≤ Ep.natDegree + (F.key ^ b).natDegree := natDegree_mul_le
        _ ≤ a + b * F.e₁ := by
            refine Nat.add_le_add hEpdeg ?_
            rw [natDegree_pow, hkeydeg]
    have h2 : (b + 1) * F.e₁ ≤ T.f₂ * F.e₁ := Nat.mul_le_mul_right _ hb
    have h3 : (b + 1) * F.e₁ = b * F.e₁ + F.e₁ := by ring
    omega
  have hEntry : (Ep * F.key ^ b).degree < (composedKey T).degree :=
    degree_lt_degree (by rw [hΦdeg]; exact hEntryN)
  -- the honest ledger is empty at `j ≥ 2`
  have hhonest : dev (composedKey T) f j = 0 := by
    rw [← devQ_eq_dev]
    have hfshape : f = composedKey T ^ μ₂ + (Ep * F.key ^ b) * composedKey T ^ 1 := by
      rw [hf]; ring
    rw [hfshape, devQ_pow_add_entry hΦmonic hEntry hj, if_neg (by omega)]
  -- the shadow ledger is empty at `j ≥ 2`: the seed is exhausted by ONE division
  have hKbar := trinomialY_map_monic (AdjoinRoot.mk F.key) Pp c0p hf₂
  have hshadow : shadowDev T f j = 0 := by
    rw [shadowDev_of_ingrid T hKgrid hAgrid hKe hAe, hAp]
    have hmapA : (Kp ^ μ₂ + Ent).map (AdjoinRoot.mk F.key)
        = (Kp.map (AdjoinRoot.mk F.key)) ^ μ₂ + Ent.map (AdjoinRoot.mk F.key) := by
      simp only [Polynomial.map_add, Polynomial.map_pow]
    rw [hmapA, hKp, devQ_add hKbar.1]
    have h1 : devQ ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        (((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂) j = 0 := by
      have hone : ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂
          = 1 * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂ := by ring
      rw [hone]
      exact devQ_mul_pow_of_lt hKbar.1 μ₂ 1 j hj
    have hEntdeg : (Ent.map (AdjoinRoot.mk F.key)).natDegree ≤ b + T.f₂ := by
      refine le_trans (natDegree_map_le) ?_
      rw [hEnt]
      refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
        (max_le ?_ ?_)) ?_)
      · exact le_trans (natDegree_C_mul_le _ _) (by rw [natDegree_X_pow])
      · exact le_trans (natDegree_C_mul_le _ _) (by rw [natDegree_X_pow]; omega)
      · exact le_trans (natDegree_C_mul_le _ _) (by rw [natDegree_X_pow]; omega)
    have h2 : devQ ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        (Ent.map (AdjoinRoot.mk F.key)) j = 0 := by
      refine devQ_eq_zero_of_lt hKbar.1 _ j ?_
      rw [hKbar.2]
      have h2f : 2 * T.f₂ ≤ j * T.f₂ := Nat.mul_le_mul_right _ hj2
      omega
    rw [h1, h2, add_zero, reass_zero]
  rw [hshadow, hhonest]


/-! ### The two low-coordinate discrepancies in closed form (§3 Steps 1–3 assembled)

This is `lawEW_pin` up to its last two steps.  `lawEW_pin` asks for
`dv2Hgt (Δ_j) = gridWeight T α a b (1−j) + T.margin`; the theorem below computes `Δ_j`
itself, at both low coordinates, as the reassembly of the census pieces.  What is left for
the pin is exactly the note's Step 4/5: the slot heights of these two explicit polynomials
(and the `b = m−1` collision inside the second).  See
`notes/C127_PIN_BLOCKED_2026-08-16.md`. -/

set_option linter.unusedVariables false in
/-- **The crossing discrepancy, in closed form.**  At a crossing entry (`j′ = 1`,
`a + i₂ ≥ D′`) the shadow ledger exceeds the honest one at coordinate `1` by the reassembled
census quotient and at coordinate `0` by the reassembled census remainder — the note's
`Δ₁ = red(q)`, `Δ₀ = red(r)`. -/
theorem lawEW_discrepancy_eq_census {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) [Finite (ResidueField O)]
    (hh : F.h = 1) (hf₁ : F.f₁ = 1) (he₂ : T.e₂ = 1)
    {ω : O} (hω : IsUnit ω)
    (hkey : F.key = Polynomial.X ^ F.e₁ - Polynomial.C (π * ω))
    {i₂ v₂ v₀ : ℕ} (hi₂ : 1 ≤ i₂) {c₂ c₀ : O} (hc₂ : IsUnit c₂) (hc₀ : IsUnit c₀)
    (hcomp : composedKey T
      = F.key ^ T.f₂
        + Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂ * F.key ^ (T.f₂ - 1)
        + Polynomial.C (c₀ * π ^ v₀))
    (hu₂ : T.u₂ = F.e₁ * v₂ + i₂) (hv₀ : F.e₁ * v₀ = T.f₂ * T.u₂)
    {μ₂ : ℕ} (hμ₂ : 2 ≤ μ₂) (hgrid : μ₂ * i₂ < F.e₁)
    {c : O} (hc : IsUnit c) (α a b : ℕ) (ha : a < F.e₁) (hb : b < T.f₂)
    {f : Polynomial O}
    (hf : f = composedKey T ^ μ₂
      + Polynomial.C (c * π ^ α) * Polynomial.X ^ a * F.key ^ b
        * composedKey T)
    (hcross : F.e₁ ≤ a + i₂) :
    shadowDev T f 1 - dev (composedKey T) f 1
        = reass F (seedQuot
            (AdjoinRoot.mk F.key (Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂))
            (AdjoinRoot.mk F.key (Polynomial.C (c * π ^ α * (c₂ * π ^ v₂))
              * Polynomial.X ^ (a + i₂ - F.e₁))) b)
      ∧ shadowDev T f 0 - dev (composedKey T) f 0
        = reass F (seedRem
            (AdjoinRoot.mk F.key (Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂))
            (AdjoinRoot.mk F.key (Polynomial.C (c₀ * π ^ v₀)))
            (AdjoinRoot.mk F.key (Polynomial.C (c * π ^ α * (c₂ * π ^ v₂))
              * Polynomial.X ^ (a + i₂ - F.e₁))) T.f₂ b) := by
  haveI : Nontrivial (AdjoinRoot F.key) := F.nontrivial_adjoinRoot
  have hkeydeg : F.key.natDegree = F.e₁ := by rw [F.hdeg, hf₁, mul_one]
  have hf₂ : 2 ≤ T.f₂ := by have h := T.hcomp; rw [he₂, one_mul] at h; exact h
  have hi₂lt : i₂ < F.e₁ := lt_of_le_of_lt (Nat.le_mul_of_pos_left i₂ (by omega)) hgrid
  obtain ⟨k, hk⟩ : ∃ k, T.f₂ = k + 1 := ⟨T.f₂ - 1, by omega⟩
  set Pp : Polynomial O := Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂ with hPp
  set c0p : Polynomial O := Polynomial.C (c₀ * π ^ v₀) with hc0p
  set Ep : Polynomial O := Polynomial.C (c * π ^ α) * Polynomial.X ^ a with hEp
  set s : ℕ := a + i₂ - F.e₁ with hsdef
  set gp : Polynomial O := Polynomial.C (c * π ^ α * (c₂ * π ^ v₂)) * Polynomial.X ^ s with hgp
  set Kp : Polynomial (Polynomial O) := trinomialY Pp c0p T.f₂ with hKp
  set Ent : Polynomial (Polynomial O) :=
    Polynomial.C (Ep + gp) * Polynomial.X ^ (b + T.f₂)
      + Polynomial.C (gp * Polynomial.C (π * ω)) * Polynomial.X ^ (b + T.f₂ - 1)
      + Polynomial.C (Ep * c0p) * Polynomial.X ^ b with hEnt
  set Ap : Polynomial (Polynomial O) := Kp ^ μ₂ + Ent with hAp
  -- one-variable degrees
  have hPpdeg : Pp.natDegree ≤ i₂ := by
    rw [hPp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hc0pdeg : c0p.natDegree ≤ i₂ := by rw [hc0p, natDegree_C]; exact Nat.zero_le _
  have hEpdeg : Ep.natDegree ≤ a := by
    rw [hEp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hEpkey : Ep.degree < F.key.degree :=
    degree_lt_degree (lt_of_le_of_lt hEpdeg (by rw [hkeydeg]; exact ha))
  have hgpdeg : gp.natDegree ≤ s := by
    rw [hgp]
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, Nat.zero_add]
  have hslt : s < F.e₁ := by rw [hsdef]; omega
  -- the wrap (§3 Step 1)
  have hkeyX : F.key + Polynomial.C (π * ω) = (Polynomial.X : Polynomial O) ^ F.e₁ := by
    rw [hkey]; ring
  have hsadd : s + F.e₁ = a + i₂ := by rw [hsdef]; omega
  have hEpPp : Ep * Pp = gp * (F.key + Polynomial.C (π * ω)) := by
    have hx : (Polynomial.X : Polynomial O) ^ s * Polynomial.X ^ F.e₁
        = Polynomial.X ^ a * Polynomial.X ^ i₂ := by
      rw [← pow_add, ← pow_add, hsadd]
    rw [hkeyX, hEp, hPp, hgp]
    calc Polynomial.C (c * π ^ α) * Polynomial.X ^ a
          * (Polynomial.C (c₂ * π ^ v₂) * Polynomial.X ^ i₂)
        = Polynomial.C (c * π ^ α) * Polynomial.C (c₂ * π ^ v₂)
            * (Polynomial.X ^ a * Polynomial.X ^ i₂) := by ring
      _ = Polynomial.C (c * π ^ α * (c₂ * π ^ v₂))
            * (Polynomial.X ^ s * Polynomial.X ^ F.e₁) := by
          rw [hx, ← Polynomial.C_mul]
      _ = Polynomial.C (c * π ^ α * (c₂ * π ^ v₂)) * Polynomial.X ^ s
            * Polynomial.X ^ F.e₁ := by ring
  -- in-grid
  have hKgridN : ∀ i, (Kp.coeff i).natDegree ≤ i₂ := by
    rw [hKp]; exact trinomialY_coeff_natDegree_le hPpdeg hc0pdeg
  have hKgrid : ∀ i, (Kp.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hKgridN (by rw [hkeydeg]; exact hi₂lt)
  have hdlt : max (μ₂ * i₂) (max a s) < F.e₁ := max_lt hgrid (max_lt ha hslt)
  have hEntN : ∀ i, (Ent.coeff i).natDegree ≤ max a s := by
    rw [hEnt]
    refine natDegree_coeff_add_le (natDegree_coeff_add_le ?_ ?_) ?_
    · refine fun i => le_trans (natDegree_coeff_C_mul_X_pow_le _ _ i) ?_
      exact le_trans (natDegree_add_le _ _) (max_le_max hEpdeg hgpdeg)
    · refine fun i => le_trans (natDegree_coeff_C_mul_X_pow_le _ _ i) ?_
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, Nat.add_zero]
      exact le_trans hgpdeg (le_max_right _ _)
    · refine fun i => le_trans (natDegree_coeff_C_mul_X_pow_le _ _ i) ?_
      refine le_trans natDegree_mul_le ?_
      rw [hc0p, natDegree_C, Nat.add_zero]
      exact le_trans hEpdeg (le_max_left _ _)
  have hAgridN : ∀ i, (Ap.coeff i).natDegree ≤ max (μ₂ * i₂) (max a s) := by
    rw [hAp]
    refine natDegree_coeff_add_le ?_ ?_
    · exact fun i => le_trans (natDegree_coeff_pow_le hKgridN μ₂ i) (le_max_left _ _)
    · exact fun i => le_trans (hEntN i) (le_max_right _ _)
  have hAgrid : ∀ i, (Ap.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hAgridN (by rw [hkeydeg]; exact hdlt)
  -- evaluations
  have hKe : Polynomial.eval F.key Kp = composedKey T := by
    rw [hKp, trinomialY_eval, hcomp]
  have hcomp' : composedKey T = F.key ^ T.f₂ + (Pp * F.key ^ (T.f₂ - 1) + c0p) := by
    rw [hcomp]; ring
  have hEnte : Polynomial.eval F.key Ent = Ep * F.key ^ b * composedKey T := by
    rw [hEnt, hcomp']
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    have e1 : b + T.f₂ - 1 = b + k := by omega
    have e2 : b + T.f₂ = b + k + 1 := by omega
    have e3 : T.f₂ - 1 = k := by omega
    have e4 : T.f₂ = k + 1 := hk
    rw [e1, e2, e3, e4]
    linear_combination (-(F.key ^ (b + k))) * hEpPp
  have hAe : Polynomial.eval F.key Ap = f := by
    rw [hAp]
    simp only [eval_add, eval_pow, hKe, hEnte]
    rw [hf]
  -- the level-2 key
  have hpowmonic : (F.key ^ T.f₂).Monic := F.hmonic.pow _
  have hpowdeg : (F.key ^ T.f₂).natDegree = T.f₂ * F.e₁ := by rw [natDegree_pow, hkeydeg]
  have hstep : (T.f₂ - 1) * F.e₁ + F.e₁ = T.f₂ * F.e₁ := by rw [hk]; simp; ring
  have hrestN : (Pp * F.key ^ (T.f₂ - 1) + c0p).natDegree < T.f₂ * F.e₁ := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · calc (Pp * F.key ^ (T.f₂ - 1)).natDegree
          ≤ Pp.natDegree + (F.key ^ (T.f₂ - 1)).natDegree := natDegree_mul_le
        _ ≤ i₂ + (T.f₂ - 1) * F.e₁ := by
            refine Nat.add_le_add hPpdeg ?_
            rw [natDegree_pow, hkeydeg]
        _ < T.f₂ * F.e₁ := by omega
    · rw [hc0p]
      simp only [natDegree_C]
      calc 0 < F.e₁ := F.he₁
        _ ≤ T.f₂ * F.e₁ := Nat.le_mul_of_pos_left _ (by omega)
  have hrest : (Pp * F.key ^ (T.f₂ - 1) + c0p).degree < (F.key ^ T.f₂).degree :=
    degree_lt_degree (by rw [hpowdeg]; exact hrestN)
  have hΦmonic : (composedKey T).Monic := by rw [hcomp']; exact hpowmonic.add_of_left hrest
  have hΦdeg : (composedKey T).natDegree = T.f₂ * F.e₁ := by
    rw [hcomp']
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_add_eq_left_of_degree_lt hrest, degree_eq_natDegree hpowmonic.ne_zero, hpowdeg]
  have hEntryN : (Ep * F.key ^ b).natDegree < T.f₂ * F.e₁ := by
    have h1 : (Ep * F.key ^ b).natDegree ≤ a + b * F.e₁ := by
      calc (Ep * F.key ^ b).natDegree ≤ Ep.natDegree + (F.key ^ b).natDegree := natDegree_mul_le
        _ ≤ a + b * F.e₁ := by
            refine Nat.add_le_add hEpdeg ?_
            rw [natDegree_pow, hkeydeg]
    have h2 : (b + 1) * F.e₁ ≤ T.f₂ * F.e₁ := Nat.mul_le_mul_right _ hb
    have h3 : (b + 1) * F.e₁ = b * F.e₁ + F.e₁ := by ring
    omega
  have hEntry : (Ep * F.key ^ b).degree < (composedKey T).degree :=
    degree_lt_degree (by rw [hΦdeg]; exact hEntryN)
  have hfshape : f = composedKey T ^ μ₂ + (Ep * F.key ^ b) * composedKey T ^ 1 := by
    rw [hf]; ring
  -- the honest ledger at the two low coordinates
  have hhon1 : dev (composedKey T) f 1 = Ep * F.key ^ b := by
    rw [← devQ_eq_dev, hfshape, devQ_pow_add_entry hΦmonic hEntry (by omega : (1:ℕ) < μ₂),
      if_pos rfl]
  have hhon0 : dev (composedKey T) f 0 = 0 := by
    rw [← devQ_eq_dev, hfshape, devQ_pow_add_entry hΦmonic hEntry (by omega : (0:ℕ) < μ₂),
      if_neg (by omega)]
  -- the transported key and the transported entry
  have hKbar := trinomialY_map_monic (AdjoinRoot.mk F.key) Pp c0p hf₂
  have hKbarEq : (trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)
      = Polynomial.X ^ T.f₂ + Polynomial.C (AdjoinRoot.mk F.key Pp) * Polynomial.X ^ (T.f₂ - 1)
        + Polynomial.C (AdjoinRoot.mk F.key c0p) := by
    simp only [trinomialY, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X]
  have hmkkey : AdjoinRoot.mk F.key F.key = 0 := AdjoinRoot.mk_self
  have hmkEpPp : AdjoinRoot.mk F.key Ep * AdjoinRoot.mk F.key Pp
      = AdjoinRoot.mk F.key gp * AdjoinRoot.mk F.key (Polynomial.C (π * ω)) := by
    have h := congrArg (AdjoinRoot.mk F.key) hEpPp
    rw [map_mul (AdjoinRoot.mk F.key) Ep Pp,
      map_mul (AdjoinRoot.mk F.key) gp (F.key + Polynomial.C (π * ω)),
      map_add (AdjoinRoot.mk F.key) F.key (Polynomial.C (π * ω)), hmkkey, zero_add] at h
    exact h
  have hEntmap : Ent.map (AdjoinRoot.mk F.key)
      = Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
          * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        + Polynomial.C (AdjoinRoot.mk F.key gp) * Polynomial.X ^ (b + T.f₂) := by
    have e1 : b + T.f₂ - 1 = b + k := by omega
    have e2 : b + T.f₂ = b + k + 1 := by omega
    have e3 : T.f₂ - 1 = k := by omega
    have hL : Ent.map (AdjoinRoot.mk F.key)
        = Polynomial.C (AdjoinRoot.mk F.key Ep + AdjoinRoot.mk F.key gp)
              * Polynomial.X ^ (b + k + 1)
          + Polynomial.C (AdjoinRoot.mk F.key gp
              * AdjoinRoot.mk F.key (Polynomial.C (π * ω))) * Polynomial.X ^ (b + k)
          + Polynomial.C (AdjoinRoot.mk F.key Ep * AdjoinRoot.mk F.key c0p)
              * Polynomial.X ^ b := by
      rw [hEnt, e1, e2]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X]
      rw [map_add (AdjoinRoot.mk F.key) Ep gp,
        map_mul (AdjoinRoot.mk F.key) gp (Polynomial.C (π * ω)),
        map_mul (AdjoinRoot.mk F.key) Ep c0p]
    have hR : Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
          * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        + Polynomial.C (AdjoinRoot.mk F.key gp) * Polynomial.X ^ (b + T.f₂)
        = Polynomial.C (AdjoinRoot.mk F.key Ep + AdjoinRoot.mk F.key gp)
              * Polynomial.X ^ (b + k + 1)
          + Polynomial.C (AdjoinRoot.mk F.key Ep * AdjoinRoot.mk F.key Pp)
              * Polynomial.X ^ (b + k)
          + Polynomial.C (AdjoinRoot.mk F.key Ep * AdjoinRoot.mk F.key c0p)
              * Polynomial.X ^ b := by
      rw [hKbarEq, e2, e3, hk]
      simp only [Polynomial.C_add, Polynomial.C_mul]
      ring
    rw [hL, hR, hmkEpPp]
  -- the shadow chain at the two low coordinates
  have hmapA : Ap.map (AdjoinRoot.mk F.key)
      = ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂
        + (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
            * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
          + Polynomial.C (AdjoinRoot.mk F.key gp) * Polynomial.X ^ (b + T.f₂)) := by
    rw [hAp]
    simp only [Polynomial.map_add, Polynomial.map_pow, hEntmap, hKp]
  have hseed := devQ_seed (AdjoinRoot.mk F.key Pp) (AdjoinRoot.mk F.key c0p)
    (AdjoinRoot.mk F.key gp) hb hKbarEq hKbar.1 hKbar.2
  have hEbar : (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b).degree
      < ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)).degree := by
    rw [degree_eq_natDegree hKbar.1.ne_zero, hKbar.2]
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le b _) (by exact_mod_cast hb)
  have hpure : ∀ j : ℕ, j < μ₂ →
      devQ ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        (((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂) j = 0 := by
    intro j hjlt
    have hone : ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂
        = 1 * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ μ₂ := by ring
    rw [hone]
    exact devQ_mul_pow_of_lt hKbar.1 μ₂ 1 j hjlt
  have hsh1 : shadowDev T f 1
      = Ep * F.key ^ b + reass F (seedQuot (AdjoinRoot.mk F.key Pp) (AdjoinRoot.mk F.key gp) b) := by
    rw [shadowDev_of_ingrid T hKgrid hAgrid hKe hAe, hKp, hmapA, devQ_add hKbar.1,
      devQ_add hKbar.1, hpure 1 (by omega), zero_add, hseed.2]
    have hent1 : devQ ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
          * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))) 1
        = Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b := by
      have hpow : Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
            * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
          = (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b)
            * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ 1 := by ring
      have hd := devQ_mul_pow hKbar.1 1 (Polynomial.C (AdjoinRoot.mk F.key Ep)
        * Polynomial.X ^ b) 0
      rw [Nat.add_zero] at hd
      rw [hpow, hd, devQ_zero_of_degree_lt hKbar.1 hEbar]
    rw [hent1, reass_add, reass_map_C_mul_X_pow F Ep b hEpkey]
  have hsh0 : shadowDev T f 0
      = reass F (seedRem (AdjoinRoot.mk F.key Pp) (AdjoinRoot.mk F.key c0p)
          (AdjoinRoot.mk F.key gp) T.f₂ b) := by
    rw [shadowDev_of_ingrid T hKgrid hAgrid hKe hAe, hKp, hmapA, devQ_add hKbar.1,
      devQ_add hKbar.1, hpure 0 (by omega), zero_add, hseed.1]
    have hent0 : devQ ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
        (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
          * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))) 0 = 0 := by
      have hpow : Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b
            * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key))
          = (Polynomial.C (AdjoinRoot.mk F.key Ep) * Polynomial.X ^ b)
            * ((trinomialY Pp c0p T.f₂).map (AdjoinRoot.mk F.key)) ^ 1 := by ring
      rw [hpow]
      exact devQ_mul_pow_of_lt hKbar.1 1 _ 0 (by omega)
    rw [hent0, zero_add]
  refine ⟨?_, ?_⟩
  · rw [hsh1, hhon1]; ring
  · rw [hsh0, hhon0, sub_zero]

end LawEW

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.devQ_of_zero
#print axioms Uniformity.Density.Tower.devQ_add
#print axioms Uniformity.Density.Tower.devQ_mul_pow
#print axioms Uniformity.Density.Tower.devQ_mul_pow_of_lt
#print axioms Uniformity.Density.Tower.devQ_eq_zero_of_lt
#print axioms Uniformity.Density.Tower.devQ_zero_of_degree_lt
#print axioms Uniformity.Density.Tower.devQ_pow_add_entry
#print axioms Uniformity.Density.Tower.devQ_eq_dev
#print axioms Uniformity.Density.Tower.biRead_coeff
#print axioms Uniformity.Density.Tower.dev_eval_eq_coeff
#print axioms Uniformity.Density.Tower.biRead_eval_eq_map
#print axioms Uniformity.Density.Tower.reass
#print axioms Uniformity.Density.Tower.dev_reass
#print axioms Uniformity.Density.Tower.shadowDev_eq_reass
#print axioms Uniformity.Density.Tower.shadowDev_of_ingrid
#print axioms Uniformity.Density.Tower.reass_map_C_mul_X_pow
#print axioms Uniformity.Density.Tower.trinomialY
#print axioms Uniformity.Density.Tower.trinomialY_map_monic
#print axioms Uniformity.Density.Tower.lawEW_faithful_of_nox
#print axioms Uniformity.Density.Tower.lawEW_faithful_high
#print axioms Uniformity.Density.Tower.seedQuot
#print axioms Uniformity.Density.Tower.seedRem
#print axioms Uniformity.Density.Tower.seed_division_census
#print axioms Uniformity.Density.Tower.devQ_seed
#print axioms Uniformity.Density.Tower.lawEW_discrepancy_eq_census

end AxCheck
