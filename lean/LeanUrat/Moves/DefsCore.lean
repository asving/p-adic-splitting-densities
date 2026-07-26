/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/DefsCore — the round-4 core objects for the MOVES tower induction (§B2-DEF)

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §B2-DEF (D.0–D.11). ROUND-4 design layer,
after the round-3 STOP-THE-LINE (`lean/notes/MOVES_LEAN_SEMAUDIT3_2026-07-26.md`, 17 FAITHLESS).
Imports `Defs.lean` and `DefsT.lean` UNCHANGED (concurrent fan-outs read them). Design decision
and the point-by-point audit answers: blueprint `MOVES_LEAN_BLUEPRINT_2026-07-26.md` § ROUND 4.
Definitions only — no theorems beyond the two nonzero-witness proofs inside `Units.mk0`,
no `sorry`, no axioms.

## The round-4 design decision (hybrid A/B — see blueprint ROUND 4 for the full rationale)

The audits proved four things are inexpressible in the residual-only model. Each gets a REAL
object here (option A), while the stage laws stay residual-level but are re-encoded faithfully
(option B) and BUNDLED into a well-formed core (`StageCore`) that the base CONSTRUCTS and the
transition TRANSPORTS:

1. **The D.10 common localization** is the genuine fraction field `RatFunc F ⊇ F[z^{±1}], F[z'^{±1}]`:
   `Stage.ratRes`/`Stage.ratResShift` embed both frames' residuals by evaluation at the
   TRANSCENDENTAL variable (injective — NOT finite-field point evaluation), and
   `RecenterSubstCore` is the substitution identity `R'(f)(ζ) = R(f)(ζ + c̃)` for EVERY `f`.
2. **The T exponent-vector product law** `T = Π in(ũᵢ)^{aᵢ}·Y^t` is carried EXACTLY, with no
   graded ring, by the two literal elements `tvecNum = Π ũᵢ^{aᵢ⁺}·Φ^{t⁺}`, `tvecDen = Π ũᵢ^{aᵢ⁻}·Φ^{t⁻}`
   of `A` and the equation `TvecLaw : w(num) = w(den) + 1 ∧ R(num) = R(den)` (⟺ `[num]/[den]`
   is a degree-1 unit `T` with `R = [·]·T^{−w}`). Transport is the factorwise list equation
   `child_Tvec` in `TransitionCore`.
3. **The S4 coefficient localization** is characterized on MONOMIAL PRODUCTS (`IsCoeffProd`,
   `IsUnitMonProd`): degree-0 coefficient ratios are `K`-scalars, every `Kˣ`-scalar is realized,
   and the degree-0 EXPONENT group (equal-weight monomial position differences) is all of `ℤ`
   (`CoeffFieldLawCore`).
4. **The D.8 transported pattern** is the EXECUTABLE carry recursion `carryRec`/`carryDigit`
   (canonical ψ-digit + overflow, the displayed triangular recursion), and the landing cylinder
   (`LandingCylinder`) carries it literally; the stratum's pattern is the canonical ψ-adic
   development of the anchored residual (`StratumData`, via `IsDevelopment` at key ψ).

**Machine-checked constraints folded in (prover fan-out, 2026-07-26):** the previous-read
(I-aug) law `e·wPrev(Φ) < h` is `StageCore.prevIaug` (the pinned TRANSviii_b blocker);
`L5.landTransport`/`L6.moveReduceCommute` corrections live in `MANIFEST_CORE.json`.

All items are flagged for semantic-guardian review (the trust boundary).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

/-! ## 1. The common localization (D.10): both frames inside `RatFunc F`

`RatFunc F = Frac F[ζ]` contains the two Laurent rings `F[z^{±1}]` (via `z ↦ ζ`) and
`F[z'^{±1}]` (via `z' ↦ ζ`, `z = z' + c̃ ↦ ζ + c̃`) as subrings — it IS a common localization
of the two frames (the honest `L_both` of D.10 embeds in it). Evaluation at the transcendental
`ζ` is an injective ring hom on Laurent polynomials, so identities stated here carry the FULL
Laurent-polynomial information (unlike evaluation at finite-field points, the audit-#3 defect). -/

/-- The Laurent variable as a unit of `RatFunc F` (the transcendental evaluation point). -/
noncomputable def ratX (F : Type*) [Field F] : (RatFunc F)ˣ :=
  Units.mk0 RatFunc.X RatFunc.X_ne_zero

/-- The shifted variable `ζ + c` as a unit of `RatFunc F` (the D.10 substitution point
`z = z' + c̃`). Nonzero because `X + C c` is a monic (degree-1) polynomial. -/
noncomputable def ratXShift {F : Type*} [Field F] (c : F) : (RatFunc F)ˣ :=
  Units.mk0 (RatFunc.X + RatFunc.C c) (by
    have h : (RatFunc.X + RatFunc.C c : RatFunc F)
        = algebraMap (Polynomial F) (RatFunc F) (Polynomial.X + Polynomial.C c) := by
      simp [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [h]
    exact RatFunc.algebraMap_ne_zero (Polynomial.monic_X_add_C c).ne_zero)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The residual `σ.R f`, embedded in the common localization `RatFunc F` by the injective
evaluation `z ↦ ζ` (coefficients via `σ.K ↪ F ↪ RatFunc F`). This is `R(f)` read in `L_both`. -/
noncomputable def Stage.ratRes (σ : Stage p F) (f : Polynomial ℤ_[p]) : RatFunc F :=
  LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ.K.subtype) (ratX F) (σ.R f)

/-- The residual `σ.R f`, embedded in `RatFunc F` through the SUBSTITUTED variable `z ↦ ζ + c`
(the D.10 change of transcendental `z = z' + c̃`, with `ζ` playing `z'`). -/
noncomputable def Stage.ratResShift (σ : Stage p F) (c : F) (f : Polynomial ℤ_[p]) : RatFunc F :=
  LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ.K.subtype) (ratXShift c) (σ.R f)

/-- **The D.10 substitution identity at its honest scope — EVERY `f`, at read heights**
(`R'(f)` as a `z'`-Laurent polynomial `= R(f)(z' + c̃)`, an identity in the common
localization). "Read heights" is automatic: `σ'.R f` IS the graded (read-height) data of `f`
— digits strictly below the read line never enter either side (the Case-K-sharpened scope). -/
def RecenterSubstCore (σ σ' : Stage p F) (cc : ↥σ.K) : Prop :=
  ∀ f : Polynomial ℤ_[p], σ'.ratRes f = σ.ratResShift (cc : F) f

/-! ## 2. The T exponent-vector product law (P2/D.3(b)/D.7(vi)), exact and graded-ring-free

`T = Π in(ũᵢ)^{aᵢ} · Y^t` (the stage's pinned degree-1 unit as an integer exponent vector over
the representative list, key exponent `t`) is EQUIVALENT, under `R(f) = [f]·T^{−w(f)}`, to the
one equation `R(P) = R(Q) ∧ w(P) = w(Q) + 1` for the two LITERAL elements
`P := Π ũᵢ^{aᵢ⁺}·Φ^{t⁺}`, `Q := Π ũᵢ^{aᵢ⁻}·Φ^{t⁻}` of `A` — because
`R(P)·R(Q)⁻¹ = ([P]/[Q])·T^{−(w P − w Q)} = T·T⁻¹ = 1` pins `[P]/[Q] = T` exactly.
Base check: `T = π^s y^t` over `(p, φ)` gives `w(p^{s⁺}φ^{t⁺}) − w(p^{s⁻}φ^{t⁻}) = es + ht = 1`. -/

/-- The positive part `P = Π ũᵢ^{aᵢ⁺} · Φ^{t⁺}` of the stage's T-vector, as a literal element
of `A` (exponents from `σ.Tvec`; the current key's exponent is the Bézout `σ.t`, per (P2)). -/
noncomputable def Stage.tvecNum (σ : Stage p F) : Polynomial ℤ_[p] :=
  (σ.Tvec.map (fun q => q.1 ^ q.2.toNat)).prod * σ.Φ ^ σ.t.toNat

/-- The negative part `Q = Π ũᵢ^{aᵢ⁻} · Φ^{t⁻}` of the stage's T-vector. -/
noncomputable def Stage.tvecDen (σ : Stage p F) : Polynomial ℤ_[p] :=
  (σ.Tvec.map (fun q => q.1 ^ (-q.2).toNat)).prod * σ.Φ ^ (-σ.t).toNat

/-- **The T-vector product law**: `[tvecNum]/[tvecDen]` is a degree-1 unit and it IS the `T`
normalizing `R` — stated as the exact residual-level equation (see §2 header). Replaces the
round-3 `reps_pinned` (which forced scalar 1 and was refuted for outgoing keys). -/
def TvecLaw (σ : Stage p F) : Prop :=
  σ.w σ.tvecNum = σ.w σ.tvecDen + 1 ∧ σ.R σ.tvecNum = σ.R σ.tvecDen

/-! ## 3. The S4 coefficient localization, characterized on monomial products (D.2 (S4)/D.7(v)-(vi))

The coefficient-side localization `L^coeff = 𝒢^C[⟨U⟩⁻¹]` and the full `L` are not built; their
degree-0 content is characterized on the MULTIPLICATIVE data that generates them: products of
nonzero coefficients (`IsCoeffProd` — the coefficient monoid, whose residuals are the
`⟨U⟩`-monomials up to the graded classes) and products with key powers (`IsUnitMonProd` — the
`L`-monomials). This replaces the round-3 `CoeffFieldLaw`, whose clauses were automatic in the
flattened codomain and unrestricted in their exponent set (audit #3). -/

/-- `f` is a product of nonzero coefficients (a monomial of the coefficient-side monoid). -/
def IsCoeffProd (σ : Stage p F) (f : Polynomial ℤ_[p]) : Prop :=
  ∃ l : List (Polynomial ℤ_[p]), (∀ u ∈ l, u ≠ 0 ∧ inC σ.Φ u) ∧ f = l.prod

/-- `f` is a product of nonzero coefficients times a key power (a monomial of `L`). -/
def IsUnitMonProd (σ : Stage p F) (f : Polynomial ℤ_[p]) : Prop :=
  ∃ (l : List (Polynomial ℤ_[p])) (j : ℕ),
    (∀ u ∈ l, u ≠ 0 ∧ inC σ.Φ u) ∧ f = l.prod * σ.Φ ^ j

/-- **(S4) core**, three clauses, each about the localization's actual generators:
* **(L^coeff)₀ ⊇ K** — every current-field unit scalar is realized as a coefficient digit at
  its forced position;
* **(L^coeff)₀ ⊆ K** — the degree-0 part of the coefficient localization is ONLY `K`: any two
  equal-weight coefficient-products have residual ratio a `K`-CONSTANT (`R f = C d · R g` —
  in particular equal `z`-positions: no `z` survives without `Y`);
* **the degree-0 EXPONENT group of `L` is `ℤ = ⟨class of z⟩`** — position differences of
  equal-weight `L`-monomials (= degree-0 monomials of `L` modulo `Kˣ`) generate all of `ℤ`,
  and `z = T 1` has position 1. -/
def CoeffFieldLawCore (σ : Stage p F) : Prop :=
  (∀ c : (↥σ.K)ˣ, ∃ (B : Polynomial ℤ_[p]) (ν : ℤ),
      B ≠ 0 ∧ inC σ.Φ B ∧ σ.wPrev B = ν ∧
        σ.R B = LaurentPolynomial.C (c : ↥σ.K) * LaurentPolynomial.T (- σ.t * ν))
  ∧
  (∀ f g : Polynomial ℤ_[p], IsCoeffProd σ f → IsCoeffProd σ g → f ≠ 0 → g ≠ 0 →
      σ.w f = σ.w g → ∃ d : ↥σ.K, σ.R f = LaurentPolynomial.C d * σ.R g)
  ∧
  (AddSubgroup.closure
      {n : ℤ | ∃ (f g : Polynomial ℤ_[p]) (c c' : ↥σ.K) (k k' : ℤ),
          IsUnitMonProd σ f ∧ IsUnitMonProd σ g ∧ f ≠ 0 ∧ g ≠ 0 ∧ σ.w f = σ.w g ∧
          σ.R f = LaurentPolynomial.C c * LaurentPolynomial.T k ∧
          σ.R g = LaurentPolynomial.C c' * LaurentPolynomial.T k' ∧ n = k - k'} = ⊤)

/-! ## 4. The slot-image span (D.3(e)(i)), for the P6i image description -/

/-- The slot images at total weight `γ`: residuals of single-slot elements `B·Φ^j` of weight
`γ`. The D.3(e)(i) image description: `R` maps the weight-`γ` graded piece ONTO the additive
span of this set. -/
def Stage.slotImages (σ : Stage p F) (γ : ℤ) : Set (LaurentPolynomial ↥σ.K) :=
  {x | ∃ (B : Polynomial ℤ_[p]) (j : ℕ), B ≠ 0 ∧ inC σ.Φ B ∧
        σ.w (B * σ.Φ ^ j) = γ ∧ x = σ.R (B * σ.Φ ^ j)}

/-! ## 5. The well-formed stage core (the package the base constructs and TRANS transports) -/

/-- **The stage core** — the round-4 well-formedness package. Replaces `StageWF` (whose
`reps_pinned` was refuted and whose `K_gen` was not a localization theorem). The base stage
CONSTRUCTS it (`L1.baseStage_exists`); every transition TRANSPORTS it (`L4.TRANSstage`,
`L5.recTRANSRS`); every unit needing tower provenance CONSUMES it. Fields:
* `wPrev_mul`/`wPrev_ult` — the parent valuation is a valuation;
* `reps_nonempty`/`p_is_rep` — the representative list is genuine (`p` is always on it);
* `tvec` — the T exponent-vector PRODUCT law (§2), tying `R` to the representatives exactly;
* `prevIaug` — **(I-aug) at the read that created this stage**: `e·wPrev(Φ) < h`, i.e. the
  side slope exceeds the key's parent weight [MACHINE-CHECKED constraint: the prover fan-out
  pinned this as the exact `TRANSviii_b` blocker — the (S6b) threshold recursion bottoms
  through it; base: `wPrev(φ) = v(φ) = 0 < h`; increment child: literally `IAug`; recentering:
  transported since `wPrev(Φ − t) = wPrev(Φ)` under the strict inequality];
* `w_strict`/`w_jump`/`R_neg` — the THREE MISSING D.1(b) TIE LAWS (strict-triangle equality;
  residual cancellation at a weight jump; `R(−f) = −R(f)`): true in every genuine graded model,
  UNDERIVABLE from the round-2 `Stage` fields — the root of the audits' pathological-stage
  findings, and the exact inputs from which `SlotDecomp` becomes derivable (`L2.slotDecomp`);
* `slot` — (S3) slot decomposition + degreewise `Y`-transcendence (`SlotDecomp`, DefsT);
* `coeff` — (S4) the coefficient-localization core (§3). -/
structure StageCore (σ : Stage p F) : Prop where
  wPrev_mul : ∀ f g, f ≠ 0 → g ≠ 0 → σ.wPrev (f * g) = σ.wPrev f + σ.wPrev g
  wPrev_ult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (σ.wPrev f) (σ.wPrev g) ≤ σ.wPrev (f + g)
  reps_nonempty : σ.reps ≠ []
  p_is_rep : (Polynomial.C (p : ℤ_[p])) ∈ σ.reps
  w_strict : ∀ f g, f ≠ 0 → g ≠ 0 → σ.w f < σ.w g → σ.w (f + g) = σ.w f
  w_jump : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ.w f = σ.w g → σ.w f < σ.w (f + g) →
      σ.R f + σ.R g = 0
  R_neg : ∀ f, σ.R (-f) = - σ.R f
  tvec : TvecLaw σ
  prevIaug : (σ.e : ℤ) * σ.wPrev σ.Φ < (σ.h : ℤ)
  slot : SlotDecomp σ
  coeff : CoeffFieldLawCore σ

/-! ## 6. The transition core (D.7): construction RECORDS, not child projections -/

/-- **The transition core** — `TransitionData` (DefsT: history, threshold, slot-min, residue
growth, reps growth) PLUS the two construction records the audits demanded:
* `child_Tvec` — the FACTORWISE T-vector transport (D.7(vi)-(vii)): the child's vector is
  `s'·(parent vector)` over the old representatives, extended by `(Φ, s'·t)` for the outgoing
  key, with the child key's own exponent `t'` carried by `σ'.t` (at `e' = 1`, `s' = 1, t' = 0`
  — the formula unifies both P2 cases);
* `child_dig` — the child residual map is BUILT from the parent's ψ-digits: on `Ĉ`, the child
  digit scalar is `dig'(B)·z̄^m` (the parent D.6 digit times an explicit frame unit — cf. the
  D.8 vertex unit `z̄^{−μm̂}`) at the forced position `−t'·(parent weight)`.
`L4.TRANSstage` CONSTRUCTS this bundle together with `StageCore σ'`; `TRANSvi`/`TRANSvii`
verify S4'/S5' against these records (post-construction verification, per audit gap G5′). -/
structure TransitionCore (σ σ' : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) : Prop where
  base : TransitionData σ σ' Φhat e' h' zbar
  child_Tvec : σ'.Tvec
      = σ.Tvec.map (fun q => (q.1, σ'.s * q.2)) ++ [(σ.Φ, σ'.s * σ.t)]
  child_dig : ∀ B, B ≠ 0 → inC Φhat B →
      ∃ (c' : (↥σ'.K)ˣ) (m : ℤ),
        σ'.R B = LaurentPolynomial.C (c' : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * σ.w B) ∧
        ((c' : ↥σ'.K) : F) = σ.digPrime zbar B * ((zbar ^ m : Fˣ) : F)

/-! ## 7. The recentering core (D.10): Laurent-level coefficient identity + unchanged vector -/

/-- **The recentering core** — the round-2 field-by-field `IsRecentering` PLUS the three
Laurent-level records that make the D.10 substitution DERIVABLE for every `f` (round 3's
`digPrime`-level clause compared finite-field evaluations only — audit #3):
* `coeff_R` — coefficient residuals are LITERALLY unchanged (same `C`, same `v`, same `T`;
  at `e = 1` they are position-0 constants, hence substitution-invariant), stated cast-free
  through the common localization;
* `reps_eq`/`Tvec_eq` — representatives and the T-vector are untouched (T coefficient-pure). -/
structure IsRecenteringCore (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p]) : Prop where
  base : IsRecentering σ σ' cc tt
  coeff_R : ∀ B : Polynomial ℤ_[p], inC σ.Φ B → σ'.ratRes B = σ.ratRes B
  reps_eq : σ'.reps = σ.reps
  Tvec_eq : σ'.Tvec = σ.Tvec

end

/-! ## 8. The D.8 carry transport — the triangular recursion, EXECUTABLE

D.8 (TRANSPORT): the higher minimizing-slot residuals and the canonical ψ-adic digits of the
anchored `z^{−a}R(f)` determine each other through a triangular bijection WITH CARRIES. The
recursion is displayed in the proof (MOVES ~2349-2353): `C_μ := c_μ mod ψ`; for `j > μ`,
`C_j := (c_j + carry_j) mod ψ` with `carry_j` the accumulated ψ-overflow. Here it is as an
executable definition (`%ₘ`/`/ₘ` at the monic ψ), so the landing cylinder can carry the
TRANSPORTED PATTERN literally — the structure the residual-only model erased (audit #3). -/

/-- One carry step: canonical digit and overflow of `incoming + carry` at the monic key `ψ`. -/
noncomputable def carryStep {K : Type*} [Field K] (ψ carry cj : Polynomial K) :
    Polynomial K × Polynomial K :=
  ((cj + carry) %ₘ ψ, (cj + carry) /ₘ ψ)

/-- The D.8 triangular carry recursion on the slot-term sequence `c` (digit, carry) at `ψ`. -/
noncomputable def carryRec {K : Type*} [Field K] (ψ : Polynomial K) (c : ℕ → Polynomial K) :
    ℕ → Polynomial K × Polynomial K
  | 0 => carryStep ψ 0 (c 0)
  | j + 1 => carryStep ψ (carryRec ψ c j).2 (c (j + 1))

/-- The `j`-th canonical ψ-digit produced by the carry recursion — the DOWNWARD direction of
D.8's triangular bijection (deterministic; the UPWARD uniqueness is a theorem, not data). -/
noncomputable def carryDigit {K : Type*} [Field K] (ψ : Polynomial K) (c : ℕ → Polynomial K)
    (j : ℕ) : Polynomial K :=
  (carryRec ψ c j).1

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The descend stratum, with its full pinned data** (D.8 head): `f` has anchor `a`
(`R f = z^a·Ranch`, `Ranch(0) ≠ 0`) and the ψ-adic pattern `Cdig` — the CANONICAL ψ-adic
development of `Ranch` (`IsDevelopment` at key ψ: digits of degree `< deg ψ`, unique by Fact B),
vanishing below `μ` and alive at `μ` (⟺ `ord_ψ Ranch = μ`). The pattern is part of the
stratum's data, exactly as the ledger consumes it. -/
def StratumData (σ : Stage p F) (ψ : Polynomial ↥σ.K) (μ : ℕ) (a : ℤ)
    (Cdig : ℕ → Polynomial ↥σ.K) (n : ℕ) (f : Polynomial ℤ_[p]) : Prop :=
  ∃ Ranch : Polynomial ↥σ.K, HasAnchorK (σ.R f) a Ranch ∧
    IsDevelopment ψ Ranch Cdig n ∧ (∀ j, j < μ → Cdig j = 0) ∧ Cdig μ ≠ 0

/-- **The landing cylinder, with the transported pattern** (D.8 (BOX)/(VERTEX)/(TRANSPORT)):
conditions on the child development data `B` alone, at the lift weight `w(Φ̂) = e·h·g` and
normalization `m̂ = −t·h·g`:
* there is a side line `m₀` = the attained slot minimum, with slot `μ` ON it (VERTEX, `B μ ≠ 0`)
  and every slot `j < μ` STRICTLY above it (BOX);
* the anchored minimizing-slot terms `c_j := z^{j·m̂ − a}·R(B_j)` (genuine polynomials;
  zero at non-minimizing slots) reproduce the stratum's pattern under the carry recursion:
  `carryDigit ψ c j = Cdig j` — each equation pins one datum as a deterministic function of
  strictly earlier slot data (the unitriangular shape D.11 counts). The VERTEX digit with its
  explicit unit `z̄^{−μm̂}` is the `j = μ` instance (the unit is the `T (μ·m̂ − a)` factor). -/
def LandingCylinder (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (μ : ℕ) (a : ℤ)
    (Cdig : ℕ → Polynomial ↥σ.K) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) : Prop :=
  ∃ m₀ : ℤ,
    B μ ≠ 0 ∧ σ.w (B μ) + (μ : ℤ) * ((σ.e : ℤ) * σ.h * g) = m₀ ∧
    (∀ j, j < N → B j ≠ 0 → m₀ ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g)) ∧
    (∀ j, j < μ → B j ≠ 0 → m₀ < σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g)) ∧
    ∃ canch : ℕ → Polynomial ↥σ.K,
      (∀ j, j < N →
        ((B j ≠ 0 ∧ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m₀) →
          Polynomial.toLaurent (canch j)
            = LaurentPolynomial.T ((j : ℤ) * (- σ.t * σ.h * g) - a) * σ.R (B j)) ∧
        (¬ (B j ≠ 0 ∧ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m₀) → canch j = 0)) ∧
      (∀ j, j < N → carryDigit ψ canch j = Cdig j)

end

end LeanUrat.Moves
