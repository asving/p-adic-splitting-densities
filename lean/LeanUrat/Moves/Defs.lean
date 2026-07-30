/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Moves/Defs — shared definitions for the MOVES tower induction (§B2-DEF)  [ROUND 2]

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §B2-DEF (ACCEPTED 2026-07-26, passes 20+21
CLEAN). This is the ROUND-2 redesign, rebuilt to repair the round-1 semantic-faithfulness audit
`lean/notes/MOVES_LEAN_SEMAUDIT1_2026-07-26.md` (which rejected the round-1 `Stage`). Design
rationale and the honest-gaps list live in `lean/notes/MOVES_LEAN_BLUEPRINT_2026-07-26.md`
(§ ROUND 2). It contains ONLY definitions and the `Stage` structure — no theorems, no `sorry`.

## The concrete model (round-2 design decisions; see the blueprint §ROUND 2 for justification)

* **Ambient objects.** `A = ℤ_[p][X]` (`Polynomial ℤ_[p]`). The ambient residue side is a FIXED
  finite field `F` (morally `𝔽_{p^{n!}}`, big enough to contain every residue field of a run —
  `PROJECT_STATE.md` §4). The audit rejected the round-1 use of a bare `resUnits : Subgroup Fˣ`
  as the residue tracker: it is not a field. **Round 2 tracks the CURRENT residue field as a
  genuine `K : Subfield F`** (`σ.K`), with the FIXED base subfield `F_Q = σ.FQ ≤ σ.K`. Residue
  GROWTH `F' = K⟮z̄⟯` is `Subfield.closure (↑K ∪ {z̄})` for a root `z̄ ∈ F` of an irreducible
  `ψ ∈ Polynomial ↥K` — a genuine degree-`g` extension inside `F` (no more `g = 1` collapse).
* **The residual map lands in the CURRENT FIELD's Laurent ring** `L₀ = ↥K[z^{±1}]`
  (`LaurentPolynomial ↥σ.K`), so `ψ` (irreducible over `K`) is genuinely PRIME there — the K1 /
  width / ψ-order arguments (D.3, D.5, D.8) run in `↥K[z^{±1}]`, NOT in the big ambient `F[z^{±1}]`
  where `ψ` would split. `R(f) := [f]·T^{−w(f)}` (D.1(e)); the degree-0 unit `z` is `T 1`.
* **The residue digit** `dig'(B) = R(B) mod ψ ∈ F' = K⟮z̄⟯` is
  `σ.digPrime z̄ B = LaurentPolynomial.eval₂ σ.K.subtype z̄ (σ.R B) ∈ F` (evaluation of a
  `↥K`-coefficient Laurent polynomial at a root `z̄ ∈ F`, landing in `F' ⊆ F`).

## Faithfulness flags (for human review — the trust boundary)

Every `Stage` axiom is flagged for semantic-guardian review; non-vacuity is anchored by the
base-stage construction (blueprint layer L1). Round-2 audit-repairs, one line each, are listed in
the blueprint §ROUND 2; residual honest gaps (the T exponent-vector product identity, the
ambient-`F` sufficiency of the residue tower, the chord-vs-hull scope of `iaugStep`) are in the
blueprint §ROUND 2 gaps.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

universe u

/-! ## 1. The residual codomain `L₀ = (current field)[z^{±1}]` and its distinguished data -/

/-- The distinguished degree-0 unit `z` of `L₀ = K[z^{±1}]`: the Laurent variable `T 1`. -/
noncomputable abbrev zvar (K : Type u) [Field K] : LaurentPolynomial K := LaurentPolynomial.T 1

/-- A Laurent polynomial is a **monomial unit** `c·z^k` with `c ∈ Kˣ` (the shape of a coefficient
digit `dig(B)`, D.2 (S5)). -/
def IsMonomialUnit {K : Type u} [Field K] (x : LaurentPolynomial K) : Prop :=
  ∃ (c : Kˣ) (k : ℤ), x = LaurentPolynomial.C (c : K) * LaurentPolynomial.T k

/-! ## 2. Developments and slot minima (polymorphic over the base ring, so Fact A/B descend to the
reduced boxes `(ZMod (p^N))[X]`) -/

/-- Coefficient-space membership `B ∈ C_Φ`: `deg B < deg Φ` (D.0). -/
def inC {R : Type*} [CommRing R] (Φ B : Polynomial R) : Prop := B.degree < Φ.degree

/-- `f = Σ_{j<N} B_j · Φ^j` with `deg B_j < deg Φ` and `B_j = 0` for `j ≥ N`: the (finite,
unique for monic `Φ`) **Φ-adic development** (D.0 / Fact A). -/
def IsDevelopment {R : Type*} [CommRing R] (Φ f : Polynomial R) (B : ℕ → Polynomial R) (N : ℕ) :
    Prop :=
  (∀ j, (B j).degree < Φ.degree) ∧ (∀ j, N ≤ j → B j = 0) ∧
    f = ∑ j ∈ Finset.range N, B j * Φ ^ j

/-- `m` is the **attained minimum** of the slot-weights `sw j` over the nonzero slots `j < N`
(the honest attained form of `w f = min_j (...)`, dodging `inf'` nonemptiness junk). -/
def SlotMinAttained (m : ℤ) (N : ℕ) (sw : ℕ → ℤ) (nz : ℕ → Prop) : Prop :=
  (∀ j, j < N → nz j → m ≤ sw j) ∧ (∃ j, j < N ∧ nz j ∧ m = sw j)

/-- **Lemma K1** predicate: every `key`-development's weight is the attained slot-minimum
`min_j (w B_j + j·kw)` (D.2 (S2), D.5). -/
def K1At {p : ℕ} [Fact p.Prime] (w : Polynomial ℤ_[p] → ℤ) (key : Polynomial ℤ_[p]) (kw : ℤ) :
    Prop :=
  ∀ f B N, f ≠ 0 → IsDevelopment key f B N →
    SlotMinAttained (w f) N (fun j => w (B j) + (j : ℤ) * kw) (fun j => B j ≠ 0)

/-! ## 3. The stage package (§B2-DEF D.0/D.2), residue tower + correct scales -/

/-- **A stage** — one read of the OM classifier (§B2-DEF D.0, axioms (S1)–(S6) D.2), over a fixed
prime `p` and fixed AMBIENT residue field `F`.

Round-2 corrections keyed to the audit's DEF-defects:
* **DEF-2/DEF-6/DEF-7** — the residue tower: `K : Subfield F` is the CURRENT residue field,
  `FQ ≤ K` the fixed base field `F_Q`; `R` lands in `LaurentPolynomial ↥K`, digit scalars are
  units of `K`; the base orbit group `O` is `F_Qˣ` (via `FQ`), constant across the tower.
* **DEF-4** — correct scales: the stage carries the PARENT valuation `wPrev`; coefficient weights
  stretch as `w B = e·wPrev B` (`hStretch`) and digit positions are `−t·wPrev(B)` (`hS5`).
* **DEF-5** — the `e = 1` pinning `he1t : e = 1 → t = 0` (P2).
* **DEF-8** — the (S6b) threshold is NOT free: it is `wPrev Φ` (the current key's parent weight),
  used literally in `hS6b`.
* **DEF-11** — the value group is the generated-subgroup condition (`hvalgrp`).
* **DEF-3** — `U`/`T` carried: `reps` (the representative list, `p` and previous keys, all in `C`
  so the current key is adjoined separately) and `Tvec` (the `(representative, ℤ)` exponent-vector
  data). The graded-product pinning `T = Π in(ũ)^a` is a construction (blueprint gap G1). -/
structure Stage (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] where
  /-- ramification part of the read index -/
  e : ℕ
  /-- slope numerator of the read index; `= w Φ` -/
  h : ℕ
  /-- Bézout coefficient of `e` -/
  s : ℤ
  /-- Bézout coefficient of `h` -/
  t : ℤ
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hbez : (e : ℤ) * s + (h : ℤ) * t = 1
  /-- **(P2) DEF-5**: the `e = 1` pinning — at unramified reads `T` is coefficient-pure (`t = 0`,
  hence all coefficient digit positions are 0). -/
  he1t : e = 1 → t = 0
  /-- the monic key of the read -/
  Φ : Polynomial ℤ_[p]
  hmonic : Φ.Monic
  hdeg : 1 ≤ Φ.natDegree
  /-- the stage valuation `w : A → ℤ` (values on nonzero elements) -/
  w : Polynomial ℤ_[p] → ℤ
  /-- **DEF-4**: the PARENT valuation `w_prev` (the previous stage's `w`, extended to `A`); at the
  base it is the Gauss valuation. Coefficient positions/weights are read against it. -/
  wPrev : Polynomial ℤ_[p] → ℤ
  /-- **DEF-2**: the CURRENT residue field, a genuine subfield of the ambient `F`. -/
  K : Subfield F
  /-- **DEF-6**: the fixed BASE residue field `F_Q` (constant across the tower). -/
  FQ : Subfield F
  hFQ_le : FQ ≤ K
  /-- **DEF-2**: the residual map `R(f) = [f]·T^{−w(f)} ∈ L₀ = ↥K[z^{±1}]` (D.1(e)). -/
  R : Polynomial ℤ_[p] → LaurentPolynomial ↥K
  -- (S1) `w` is a valuation with value group `ℤ`  [DEF-11: generated subgroup = ⊤]
  hwmul : ∀ f g, f ≠ 0 → g ≠ 0 → w (f * g) = w f + w g
  hwult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (w f) (w g) ≤ w (f + g)
  hvalgrp : AddSubgroup.closure {n : ℤ | ∃ f g, f ≠ 0 ∧ g ≠ 0 ∧ w f - w g = n} = ⊤
  hwΦ : w Φ = (h : ℤ)
  /-- **DEF-4**: coefficient-weight stretch `w B = e·w_prev(B)` for `B ∈ C`. -/
  hStretch : ∀ B, B ≠ 0 → inC Φ B → w B = (e : ℤ) * wPrev B
  -- (D.1(e)) the residual apparatus laws (gr is NOT built; these are what the ledger consumes)
  hR0 : R 0 = 0
  hRne : ∀ f, f ≠ 0 → R f ≠ 0
  hRmul : ∀ f g, f ≠ 0 → g ≠ 0 → R (f * g) = R f * R g
  hRadd : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → w f = w g → w (f + g) = w f →
            R (f + g) = R f + R g
  hRlt : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → w f < w g → R (f + g) = R f
  -- (D.3(b)) the pinned key residual `R(Φ) = z^s`
  hRΦ : R Φ = LaurentPolynomial.T s
  -- (S2) Lemma K1 at the stage's own key
  hK1 : K1At w Φ (w Φ)
  -- (S5) coefficient digits are monomial units `c·z^{−t·w_prev(B)}` with `c` in the CURRENT field
  hS5 : ∀ B, B ≠ 0 → inC Φ B →
          ∃ c : (↥K)ˣ,
            R B = LaurentPolynomial.C (c : ↥K) * LaurentPolynomial.T (- t * wPrev B)
  /-- **DEF-3**: the representative list `U` (`p` and the previous keys); each is a nonzero
  coefficient (`deg < deg Φ`), so the current key is adjoined SEPARATELY (never in `reps`). -/
  reps : List (Polynomial ℤ_[p])
  hreps : ∀ ũ ∈ reps, ũ ≠ 0 ∧ inC Φ ũ
  /-- **DEF-3**: the `T` exponent vector as `(representative, exponent)` pairs; the projection is
  `reps`. The graded-product pinning `T = Π in(ũ)^a` is a `TRANS` construction (blueprint gap). -/
  Tvec : List (Polynomial ℤ_[p] × ℤ)
  hTvec : Tvec.map Prod.fst = reps
  -- (S6) realizers.  weightSet = the PARENT-scale coefficient weight set 𝒲 (positions forced by
  -- `−t·(parent weight)`, so the pair-valued 𝒜 is determined — DEF-6 note).
  weightSet : Set ℤ
  hWS : ∀ B, B ≠ 0 → inC Φ B → wPrev B ∈ weightSet
  /-- (S6a) EXACTNESS + BASIC REALIZERS — **the FIXED-POINT COSET form** (V5 sign-off,
  2026-07-28; blueprint §10 Key Finding 2). The note's axiom is the ORBIT-GROUP-AT-ITS-
  FIXED-POINT statement, D.2 (S6a) rev D⁶/pass-14 finding 1 (MOVES 1964–1971): "every index
  is realized by an explicit single-slot element whose digit is c·(the index's FORCED
  MONOMIAL CLASS) with c ranging over the CONSTANT orbit group O := F_Qˣ" — and D.7(viii)'s
  child realizers likewise have "dig′ … c·(a fixed z̄-monomial class): the O-orbit with
  O = F_Qˣ CONSTANT" (MOVES 2431–2435). So each weight `ν ∈ weightSet` carries ONE base
  point `b` (the forced class, ∃-quantified BEFORE the orbit scalar; free in `Kˣ` — the
  weakest faithful form: depth-2 classes are z̄-monomial but depth ≥ 3 classes are general
  unit products, and no consumer reads the base's shape, MOVES 1971–1981 "exactness
  consumes no scalar range"), and the realized digit scalars are the COSET `F_Qˣ·b`.
  The previous untwisted transcription (`b` hard-coded to 1) was machine-refuted on the
  below-threshold strip (S9a census, F₉/F₃ numerics) and admits no re-pin repair —
  restate-after-refutation, same discipline as the S9a guard event. -/
  hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∃ b : (↥K)ˣ, ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
           ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
             R B = LaurentPolynomial.C ((c * b : (↥K)ˣ) : ↥K) * LaurentPolynomial.T (- t * ν)
  /-- (S6b) FULL SCALARS ABOVE THE KEY WEIGHT: at every parent-scale coefficient weight STRICTLY
  ABOVE the current key's parent weight `wPrev Φ` (DEF-8 threshold), ANY digit scalar in the
  CURRENT field's unit group `Kˣ` (DEF-7) is realizable. -/
  hS6b : ∀ (ν : ℤ) (a : (↥K)ˣ), wPrev Φ < ν →
           ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
             R B = LaurentPolynomial.C (a : ↥K) * LaurentPolynomial.T (- t * ν)

namespace Stage

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- The residue digit `dig'_{z̄}(B) = R(B) mod ψ = R(B) evaluated at the root `z̄ ∈ F`, landing in
`F' = K⟮z̄⟯ ⊆ F` (D.6). Evaluation of a `↥K`-coefficient Laurent polynomial via the inclusion
`σ.K.subtype : ↥K →+* F` and `z ↦ z̄`. -/
noncomputable def digPrime (σ : Stage p F) (zbar : Fˣ) (B : Polynomial ℤ_[p]) : F :=
  LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R B)

/-- The coefficient-space membership predicate for this stage's key. -/
def mem (σ : Stage p F) (B : Polynomial ℤ_[p]) : Prop := inC σ.Φ B

/-- The NEXT residue field `F' = K⟮z̄⟯ = Subfield.closure (↑K ∪ {z̄})` for a root `z̄ ∈ F` of the
descend polynomial `ψ` — a genuine degree-`g` extension inside `F` (D.6/D.7(v)). -/
def nextField (σ : Stage p F) (zbar : Fˣ) : Subfield F :=
  Subfield.closure (↑σ.K ∪ {(zbar : F)})

lemma le_nextField (σ : Stage p F) (zbar : Fˣ) : σ.K ≤ σ.nextField zbar :=
  fun _ hx => Subfield.subset_closure (Or.inl hx)

end Stage

/-! ## 4. The standard lift, the increment side, ψ-order, and the recentering (D.3–D.10) -/

/-- **The standard lift** `Φ̂` (D.5), stated as the DISPLAYED formula (DEF-9), NOT a weak residual
predicate: `Φ̂ = Φ^{eg} + Σ_{0≤k<g, ψ_k≠0} t_k·Φ^{ek}`, where each present `t_k ∈ C` is an (S6b)
realizer of parent weight `h·(g−k)` and digit SCALAR `ψ_k := ψ.coeff k` at the forced position
`−t·h·(g−k)`; absent slots (`ψ_k = 0`) carry `t_k = 0`. Monicity, degree `eg·deg Φ`, weight `ehg`,
and the residual `R(Φ̂) = z^{−thg}·ψ(z)` are THEOREMS (layer L3), not clauses. -/
def IsStandardLift {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) : Prop :=
  ψ.Monic ∧ ψ.natDegree = g ∧
    ∃ tt : ℕ → Polynomial ℤ_[p],
      (∀ k, ψ.coeff k = 0 → tt k = 0) ∧
      (∀ k, k < g → ψ.coeff k ≠ 0 →
          tt k ≠ 0 ∧ inC σ.Φ (tt k) ∧
            σ.wPrev (tt k) = (σ.h : ℤ) * ((g : ℤ) - (k : ℤ)) ∧
            σ.R (tt k) = LaurentPolynomial.C (ψ.coeff k) *
              LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * ((g : ℤ) - (k : ℤ)))) ∧
      Φhat = σ.Φ ^ (σ.e * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k)

/-- **(I-aug)** at an increment (D.4, D.7): the next side `(e', h')` (lowest terms, over `w`) has
per-slot slope strictly exceeding the lift weight `w(Φ̂)`, cleared-denominator form
`h' > e'·w(Φ̂)`. -/
def IAug {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) : Prop :=
  (h' : ℤ) > (e' : ℤ) * σ.w Φhat

/-- **The next-stage slot-minimum weight** predicate: `w'` reads the side `(e', h')` over `w` at
the key `Φ̂`, i.e. `w'(Σ B_j Φ̂^j) = min_j (e'·w(B_j) + j·h')` (D.7 head). -/
def IsSlotMinWeight {p : ℕ} [Fact p.Prime] (w' : Polynomial ℤ_[p] → ℤ) (Φhat : Polynomial ℤ_[p])
    (e' h' : ℕ) (w : Polynomial ℤ_[p] → ℤ) : Prop :=
  ∀ f B N, f ≠ 0 → IsDevelopment Φhat f B N →
    SlotMinAttained (w' f) N (fun j => (e' : ℤ) * w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0)

/-- **The z-anchor** `R f = z^a · R_anch(z)` with `R_anch ∈ K[z]`, `R_anch(0) ≠ 0` (so `a = ord_z`).
The ψ-adic order is then read off `R_anch` as a POLYNOMIAL (DEF: never `ord_ψ` of a Laurent unit
`X`). -/
def HasAnchorK {K : Type u} [Field K] (x : LaurentPolynomial K) (a : ℤ) (Ranch : Polynomial K) :
    Prop :=
  Ranch.coeff 0 ≠ 0 ∧ x = LaurentPolynomial.T a * Polynomial.toLaurent Ranch

/-- **ψ-adic order** `ord_ψ(Ranch) = μ`, defined over `Polynomial K` (F[z]-order, BEFORE Laurent —
DEF fix): `ψ^μ ∣ R_anch` and `¬ ψ^{μ+1} ∣ R_anch`. -/
def OrdPsiPoly {K : Type u} [Field K] (ψ Ranch : Polynomial K) (μ : ℕ) : Prop :=
  ψ ^ μ ∣ Ranch ∧ ¬ ψ ^ (μ + 1) ∣ Ranch

/-- **`σ'` is the recentering of `σ` by center `c̃` via lift `t`** (D.10, `e_read = 1`), stated as a
field-by-field CONSTRUCTION relating `σ'` to `σ` per TRANS-RS's item list (DEF-10 fix — NOT an
assumed unrelated stage). `Φ' = Φ − t` with `deg t < deg Φ`, `w(t) = w(Φ)`, `dig(t) = c̃`
(position 0 since `e = 1`); and item by item: same valuation `w' = w` (S1, `v = v'`), same parent
valuation `wPrev`, SAME residue field `K` and base `FQ` (no residue growth), same coefficient-digit
map (S5 literally unchanged, stated at the F-valued `digPrime` level to dodge the `↥K`-vs-`↥K'`
type wall), same weight set (S6). -/
def IsRecentering {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
    (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p]) : Prop :=
  σ.e = 1 ∧ σ'.e = 1 ∧
    cc ≠ 0 ∧ inC σ.Φ tt ∧ tt ≠ 0 ∧ σ.w tt = σ.w σ.Φ ∧
    σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ) ∧
    σ'.Φ = σ.Φ - tt ∧
    (∀ f, σ'.w f = σ.w f) ∧
    (∀ f, σ'.wPrev f = σ.wPrev f) ∧
    σ'.K = σ.K ∧ σ'.FQ = σ.FQ ∧ σ'.weightSet = σ.weightSet ∧
    (∀ B, B ≠ 0 → inC σ.Φ B → ∀ zbar : Fˣ, σ'.digPrime zbar B = σ.digPrime zbar B)

end LeanUrat.Moves
