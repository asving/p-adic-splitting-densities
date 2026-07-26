/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Moves/Defs — shared definitions for the MOVES tower induction (§B2-DEF)

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §B2-DEF (ACCEPTED 2026-07-26, passes 20+21
CLEAN). This file is the shared vocabulary for the ~60-unit formalization fan-out laid out in
`lean/notes/MOVES_LEAN_BLUEPRINT_2026-07-26.md`. It contains ONLY definitions and the `Stage`
structure — no theorems, no `sorry`.

## The concrete model (design decisions; see the blueprint for full justification)

* **Ambient objects.** `A = ℤ_[p][X]` (`Polynomial ℤ_[p]`); the residue side is a FIXED ambient
  finite field `F` (morally `𝔽_{p^{n!}}`, per `PROJECT_STATE.md` §4's fixed-ambient architecture),
  shared by every stage of a run. Residue-field growth `F' = F[z]/(ψ)` is realized as a subfield
  `F(z̄) ⊆ F` via a chosen root `z̄ ∈ Fˣ` of `ψ`.
* **The graded/localization apparatus is NOT built as a mathlib `GradedRing`.** Per §B2-DEF's own
  structural decision, everything the ledger consumes is packaged in the residual map
  `R : A → L₀` where `L₀ = F[z^{±1}] = LaurentPolynomial F`, with `R(f) := [f]·T^{−w(f)}`
  (D.1(e)). The distinguished degree-0 unit `z` is the Laurent variable `T 1`. The two proved
  facts the ledger uses (D.3(e)) are R's per-piece additivity/injectivity and its
  multiplicativity — bundled here as `Stage` axioms.
* **The residue digit** `dig'(B) = R(B) mod ψ ∈ F'` is `evalUnit z̄ (R B) ∈ F`
  (`LaurentPolynomial.eval₂` at the unit `z̄`), the residue map to `F(z̄) ⊆ F`.

## Faithfulness flags (for human review — the trust boundary)

The `Stage` axioms `(S1)–(S6)` below are a formalization of §B2-DEF D.0/D.2; the precise
quantification of `(S6a)`/`(S6b)` (orbit group `O`, clean threshold `thr`, residue-unit group
`resUnits`) is the most delicate correspondence — it was the longest-fought point of the math
campaign (the S6-split, passes 10–15). Every `Stage` axiom is flagged for semantic-guardian
review; non-vacuity is anchored by the base-stage construction (blueprint layer L1).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

universe u

/-! ## 1. The residual codomain `L₀ = F[z^{±1}]` and its distinguished data -/

/-- The distinguished degree-0 unit `z` of `L₀ = F[z^{±1}]`: the Laurent variable `T 1`. -/
noncomputable abbrev zvar (F : Type u) [Field F] : LaurentPolynomial F := LaurentPolynomial.T 1

/-- A Laurent polynomial is a **monomial unit** `c·z^k` with `c ∈ Fˣ` (the shape of a coefficient
digit `dig(B)`, D.2 (S5)). -/
def IsMonomialUnit {F : Type u} [Field F] (x : LaurentPolynomial F) : Prop :=
  ∃ (c : Fˣ) (k : ℤ), x = LaurentPolynomial.C (c : F) * LaurentPolynomial.T k

/-- **The residue digit map** `dig'(·) = (·) mod ψ`: evaluation of `L₀ = F[z^{±1}]` at a unit
`z̄ ∈ Fˣ` (a root of the descend polynomial `ψ`), landing in `F' = F(z̄) ⊆ F`
(`LaurentPolynomial.eval₂`, D.6). -/
noncomputable def evalUnit {F : Type u} [Field F] (zbar : Fˣ) : LaurentPolynomial F →+* F :=
  LaurentPolynomial.eval₂ (RingHom.id F) zbar

/-! ## 2. Developments and slot minima -/

/-- Coefficient-space membership `B ∈ C_Φ`: `deg B < deg Φ` (D.0). Polymorphic over the base ring
so it applies both to `A = ℤ_[p][X]` and to the reduced boxes `(ZMod (p^N))[X]`. -/
def inC {R : Type*} [CommRing R] (Φ B : Polynomial R) : Prop := B.degree < Φ.degree

/-- `f = Σ_{j<N} B_j · Φ^j` with `deg B_j < deg Φ` and `B_j = 0` for `j ≥ N`: the (finite,
unique for monic `Φ`) **Φ-adic development** (D.0). Polymorphic over the base ring (so "development
commutes with reduction mod `p^N`", Fact A, is statable over `ZMod (p^N)`). -/
def IsDevelopment {R : Type*} [CommRing R] (Φ f : Polynomial R) (B : ℕ → Polynomial R) (N : ℕ) :
    Prop :=
  (∀ j, (B j).degree < Φ.degree) ∧ (∀ j, N ≤ j → B j = 0) ∧
    f = ∑ j ∈ Finset.range N, B j * Φ ^ j

/-- `m` is the **attained minimum** of the slot-weights `sw j` over the nonzero slots `j < N` —
the honest (attained, no `inf'` nonemptiness junk) form of "`w f = min_j (...)`" used for the
key lemma K1 (D.2 (S2), D.5). -/
def SlotMinAttained (m : ℤ) (N : ℕ) (sw : ℕ → ℤ) (nz : ℕ → Prop) : Prop :=
  (∀ j, j < N → nz j → m ≤ sw j) ∧ (∃ j, j < N ∧ nz j ∧ m = sw j)

/-- **Lemma K1** predicate: for the key `key` of weight `kw`, every development's weight is the
attained slot-minimum `min_j (w B_j + j·kw)` (D.2 (S2), D.5 Lemma K1). -/
def K1At {p : ℕ} [Fact p.Prime] (w : Polynomial ℤ_[p] → ℤ) (key : Polynomial ℤ_[p]) (kw : ℤ) : Prop :=
  ∀ f B N, f ≠ 0 → IsDevelopment key f B N →
    SlotMinAttained (w f) N (fun j => w (B j) + (j : ℤ) * kw) (fun j => B j ≠ 0)

/-! ## 3. The stage package (§B2-DEF D.0/D.2) -/

/-- **A stage** — one read of the OM classifier (§B2-DEF D.0, axioms (S1)–(S6) D.2), over a fixed
prime `p` and fixed ambient residue field `F`.

Read index `(e, h)` in lowest terms with Bézout `(s, t)` (`e·s + h·t = 1`); key `Φ` monic of
degree `≥ 1`; valuation `w` (value group `ℤ`); residual map `R : A → L₀ = F[z^{±1}]`. The graded
generalities (D.1) are bundled as the `hR*` laws. `O` is the constant base-orbit group
(`F_Qˣ`), `resUnits` the current residue field's units (`⊇ O`, grows through the tower), `thr`
the clean (S6b) threshold, `weightSet` the coefficient weight set `𝒜` (projected to weights;
positions are forced by `−t·(weight)`, D.2 (S5)). -/
structure Stage (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Fintype F] where
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
  /-- the monic key of the read -/
  Φ : Polynomial ℤ_[p]
  hmonic : Φ.Monic
  hdeg : 1 ≤ Φ.natDegree
  /-- the stage valuation `w : A → ℤ` (values on nonzero elements) -/
  w : Polynomial ℤ_[p] → ℤ
  /-- the residual map `R(f) = [f]·T^{−w(f)} ∈ L₀ = F[z^{±1}]` (D.1(e)) -/
  R : Polynomial ℤ_[p] → LaurentPolynomial F
  -- (S1) `w` is a valuation with value group `ℤ`
  hwmul : ∀ f g, f ≠ 0 → g ≠ 0 → w (f * g) = w f + w g
  hwult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (w f) (w g) ≤ w (f + g)
  hvalgrp : ∃ f g, f ≠ 0 ∧ g ≠ 0 ∧ w f - w g = 1
  hwΦ : w Φ = (h : ℤ)
  -- (D.1(e)) the residual apparatus laws
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
  -- (S5) coefficient digits are monomial units `c·z^{−t·w(B)}`, `c` in the residue units
  resUnits : Subgroup Fˣ
  hS5 : ∀ B, B ≠ 0 → inC Φ B →
          ∃ c : Fˣ, c ∈ resUnits ∧
            R B = LaurentPolynomial.C (c : F) * LaurentPolynomial.T (- t * w B)
  -- (S6) realizers
  /-- the constant base-orbit group `O = F_Qˣ` (D.2 (S6a); constant through the tower) -/
  O : Subgroup Fˣ
  hO_le : O ≤ resUnits
  /-- the clean (S6b) threshold `Θ` (D.2 (S6b), D.9) -/
  thr : ℤ
  /-- the coefficient weight set `𝒜` (projected to weights; positions forced by `−t·w`) -/
  weightSet : Set ℤ
  hWS : ∀ B, B ≠ 0 → inC Φ B → w B ∈ weightSet
  -- (S6a) exactness + base-orbit single-slot realizers at every realized weight
  hS6a : ∀ W : ℤ, W ∈ weightSet → ∀ c : Fˣ, c ∈ O →
           ∃ B, B ≠ 0 ∧ inC Φ B ∧ w B = W ∧
             R B = LaurentPolynomial.C (c : F) * LaurentPolynomial.T (- t * W)
  -- (S6b) full residue-field scalars above the clean threshold `thr`
  hS6b : ∀ (W : ℤ) (a : Fˣ), thr < W → W ∈ weightSet → a ∈ resUnits →
           ∃ B, B ≠ 0 ∧ inC Φ B ∧ w B = W ∧
             R B = LaurentPolynomial.C (a : F) * LaurentPolynomial.T (- t * W)

namespace Stage

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Fintype F]

/-- The residue digit `dig'_{z̄}(B) = R(B) mod ψ = evalUnit z̄ (R B) ∈ F` (D.6). -/
noncomputable def digPrime (σ : Stage p F) (zbar : Fˣ) (B : Polynomial ℤ_[p]) : F :=
  evalUnit zbar (σ.R B)

/-- The coefficient-space membership predicate for this stage's key. -/
def mem (σ : Stage p F) (B : Polynomial ℤ_[p]) : Prop := inC σ.Φ B

end Stage

/-! ## 4. The standard lift, the increment side, and the descend stratum (D.3–D.10) -/

/-- **The standard lift** `Φ̂` at a descend polynomial `ψ` of degree `g` (D.5): monic of degree
`e·g·deg Φ`, with residual `R(Φ̂) = z^{m̂}·ψ(z)`, `m̂ = −t·h·g` (`ψ(z) = ψ.toLaurent`). -/
def IsStandardLift {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Fintype F]
    (σ : Stage p F) (ψ : Polynomial F) (g : ℕ) (Φhat : Polynomial ℤ_[p]) : Prop :=
  Φhat.Monic ∧ Φhat.natDegree = σ.e * g * σ.Φ.natDegree ∧
    σ.R Φhat =
      LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ)) * (Polynomial.toLaurent ψ)

/-- **(I-aug)** at an increment: the next side `(e', h')` (lowest terms, over `w`) has per-slot
slope strictly exceeding the lift weight `w(Φ̂) = e·h·g`, cleared-denominator form
`h' > e'·w(Φ̂)` (D.4, D.7). -/
def IAug {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Fintype F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) : Prop :=
  (h' : ℤ) > (e' : ℤ) * σ.w Φhat

/-- **The next-stage slot-minimum weight** predicate: `w'` reads the side `(e', h')` over `w` at
the key `Φ̂`, i.e. `w'(Σ B_j Φ̂^j) = min_j (e'·w(B_j) + j·h')` (D.7 head). -/
def IsSlotMinWeight {p : ℕ} [Fact p.Prime] (w' : Polynomial ℤ_[p] → ℤ) (Φhat : Polynomial ℤ_[p])
    (e' h' : ℕ) (w : Polynomial ℤ_[p] → ℤ) : Prop :=
  ∀ f B N, f ≠ 0 → IsDevelopment Φhat f B N →
    SlotMinAttained (w' f) N (fun j => (e' : ℤ) * w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0)

/-- `ord_ψ x = μ` in `L₀ = F[z^{±1}]` (ψ prime, `ψ ≠ z`): the ψ-adic multiplicity, phrased by
divisibility of `ψ.toLaurent` (D.8). -/
def OrdPsiEq {F : Type u} [Field F] (ψ : Polynomial F) (x : LaurentPolynomial F) (μ : ℕ) : Prop :=
  (Polynomial.toLaurent ψ) ^ μ ∣ x ∧ ¬ (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ x

/-- The **anchor** `a = ord_z (R f)` with anchored polynomial `R_anch ∈ F[z]`, `R_anch(0) ≠ 0`:
`R f = z^a · R_anch(z)` (D.8, the `(z + c̃)^a` bookkeeping of Case J). -/
def HasAnchor {F : Type u} [Field F] (x : LaurentPolynomial F) (a : ℤ) (Ranch : Polynomial F) :
    Prop :=
  Ranch.coeff 0 ≠ 0 ∧ x = LaurentPolynomial.T a * (Polynomial.toLaurent Ranch)

/-- **`σ'` is the recentering of `σ` by center `c̃` via lift `t`** (D.10, `e_read = 1`):
`Φ' = Φ − t`, `deg t < deg Φ`, `w(t) = w(Φ)`, `dig(t) = c̃` (a monomial), and `w' = w` (the
`v = v'` step). Each stage keeps its OWN residual map into `L₀`; the cross-stage substitution
identity `R'(f)(z') = R(f)(z' + c̃)` is stated at the evaluation level (blueprint L5.recSubst). -/
def IsRecentering {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Fintype F]
    (σ σ' : Stage p F) (cc : Fˣ) (tt : Polynomial ℤ_[p]) : Prop :=
  σ.e = 1 ∧ σ'.e = 1 ∧ inC σ.Φ tt ∧ σ.w tt = σ.w σ.Φ ∧
    σ.R tt = LaurentPolynomial.C (cc : F) * LaurentPolynomial.T (- σ.t * σ.w tt) ∧
    σ'.Φ = σ.Φ - tt ∧ (∀ f, σ'.w f = σ.w f)

end LeanUrat.Moves
