/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130kp3
import Uniformity.ChapC.C131v

/-!
# Uniformity.ChapC.C130kp7 — S2-source plan nodes KP-7/8/9 — initial_iff_residual CLOSED

**S2-source plan nodes KP-7 + KP-8 + KP-9** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`
§6 rows KP-7 "One direction of initial equivalence versus normalized residual equality",
KP-8 "Converse for arbitrary concrete key polynomials", KP-9 "Assemble Proposition-5.6 field
with zero/equal-value cases"), the FIFTH AND LAST inductive core — on KP-0's predicates and
graded-piece IFF (C130kp0), KP-1's carried-key translation (C130kp1), KP-4's assembled
criterion (C130kp3), and the RP chain's residual banks.  This CLOSES the
`initial_iff_residual` core: the C130fg field is landed in full at the S2 operators.

## NODE KP-7 — the forward direction, at its honest (LARGER) scope

The brief's scope question is ADJUDICATED: the forward direction needs NO key-polynomial
hypothesis at all.  KP-0's normalized tie `s2NormRes_eq_of_initialEquiv` is already
universal, and ★ `s2_initial_to_residual` records it in the node's shape:
`g ∼µ₂ h → R₃(g) = R₃(h)` for ALL `g, h`.  (Published Prop 5.6's (3)→(2) restricted to
keys is a specialization.)

## NODE KP-8 — the converse (the hard direction): the key-structure bank

For KEY polynomials, equal normalized residuals force initial equivalence.  The mechanism
is published Lemma 5.3's structure theory (the arXiv v3 numbering; the published
Proposition 5.6 = arXiv Proposition 5.7 rides on it), machine-proved at the landed
operators — keyhood pins the GRADE and the TRAILING `y`-power as functions of the residual,
so residual equality lifts to graded equality at a COMMON exact grade, and KP-0's
graded-piece IFF closes:

* ★ `s2MuMinimal_natDegree_even` (published Lemma 2.10's `deg g = s′(g)·deg φ` genre, the
  parity half): a monic μ₂-minimal polynomial has EVEN degree.  Mechanism: for
  `deg g = 2m+1`, the monic-linear multiplier `q := x − g₂ₘ` (top-coefficient killer) makes
  `f := g·q − Φ′^(m+1)` a polynomial of degree `≤ 2m` with `f ∼µ₂ g·q` — the subtracted
  key power sits at value `5m+5`, strictly above `µ₂(g·q) = µ₂(g) + µ₂(q) ≤ (5m+2) + 2`
  (monic-linear digits have stage height `≤ 1`) — so `g ∣µ₂ f`, violating minimality.
* ★ `s2MuMinimal_exactGrade` (published Lemma 2.11's invariant `µ(g)/deg g = µ(φ)/deg φ`,
  i.e. `µ₂(g) = 5·(deg g/2)`): the top development slot of a monic even-degree minimal
  polynomial is ON the grade line.  Mechanism: the top digit is `1` (height 0), so
  `µ₂(g) ≤ 5m`; if strict, `f := g − Φ′^m` has degree `< 2m` and `f ∼µ₂ g` — minimality
  dies.
* ★ `s2KeyPoly_slotZero` (published Lemma 5.1's `s(g) = 0` clause): a key polynomial of
  degree `> 2` has slot 0 ON the grade line.  Mechanism: one-step DEFLATION — if slot 0 is
  off the line, KP-1's carried-key backward lemma gives `g ∼µ₂ Φ′·q`, so `g`'s prime
  initial form divides the product `Φ′·q`; dividing `Φ′` violates minimality
  (`deg Φ′ = 2 < deg g`), and dividing `q` is a GRADE contradiction
  (`β = 5 + µ₂(q)` and `µ₂(q) = β + µ₂(q′)` cannot both hold in ℕ).
* the assembled bank (`s2KeyPoly_exactGrade`, `s2KeyPoly_gradedRes_coeff_zero_ne_zero`,
  `s2KeyPoly_normRes_eq_gradedRes`, `s2KeyPoly_normRes_natDegree`,
  `s2KeyPoly_isUnit_normRes_iff`, ★ `s2KeyPoly_natDegree_pin`): every key `g` has
  `µ₂(g) = 5·(deg g/2)`, nonzero residual SCALAR (trailing power 0, so the normalized
  residual IS the graded residual — published Lemma 5.3's `s(g) = 0` consequence),
  `deg R₃(g) = deg g/4`, and the degree dictionary
  `deg g = if IsUnit R₃(g) then 2 else 4·deg R₃(g)` (published Lemma 5.3's
  `deg g = e·deg ψ·m` display at `(e, m) = (2, 2)`; the unit case is the `g ∼µ₂ φ₂`
  fiber).
* ★★ `s2_residual_to_initial` — NODE KP-8: `S2KeyPoly g → S2KeyPoly h → R₃(g) = R₃(h) →
  g ∼µ₂ h`.  The dictionary forces equal degrees, hence equal grades `5·(deg/2)`; the
  trailing pin turns residual equality into graded equality at the common grade; KP-0's
  IFF fires backward.

## NODE KP-9 — the Proposition-5.6 field, assembled

* ★★ `s2_initial_iff_residual` — the C130fg `FGMNSourceLaws.initial_iff_residual` field
  shape (= A-C.11 `FGMNCalculus.nuEquiv_iff_Rres`, published Prop 5.6(2)⇔(3), BOTH `KP`
  hypotheses retained per U9 §4.1): for key polynomials,
  `g ∼µ₂ h ↔ R₃(g) = R₃(h)`.  The zero cases are vacuous on keys (monic ⟹ nonzero, so
  the printed zero clause of Def 1.2 never fires) and the equal-value case is DERIVED
  (the grade dictionary), not hypothesized.
* ★ **the FD-0 pin** (`s2_initial_iff_residual_fills`): for ANY
  `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reading
  `normalizedResidual := s2NormRes`, `keyPolynomial := S2KeyPoly`,
  `initialEquiv := S2InitialEquiv`, the literal field shape holds — zero residual assembly
  work at FD-0 for this field.
* **teeth**: ★ `tooth_landed_keys_not_equiv` — the two landed keys `Φ′` and `Φ′² + 4x` are
  NOT initial-equivalent (residuals `1 ≠ X + 1`, refuted through the assembled iff);
  ★ `tooth_perturbed_lift_isKey` + `tooth_equivalent_key_pair` — a genuinely EQUIVALENT
  key pair: `Φ′² + 4x` and its grade-15 perturbation `Φ′² + 4x + 4x·Φ′` are BOTH keys
  (the perturbed one through KP-4's criterion, residual transported along the
  equivalence), are initial-equivalent, and the iff extracts their residual equality.
  (The brief's candidate pair `(Φ′, Φ′ + 4)` needs the constant-height numeral
  `µ₂(4) = 8`, not landed; the perturbation pair rides entirely on landed teeth.)

## What this node does NOT claim (honesty scope)

* No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` INSTANCE (FD-0 assembles later;
  the `_fills` pin is conditional on the record's operator fields, like RP-6/RP-10/KP-4's
  pins).
* No key-EXISTENCE classification (which residuals are hit is RP-12/KP-4's business; the
  structure bank constrains keys, it does not produce them).
* No `keyAt 2 = composedKey` literal field (KP-6's row), no `key_irreducible` (KP-5).
* The structure bank is stated at the honest hypothesis sets the proofs force: parity and
  the grade pin need only monic + μ₂-minimal; the slot-0 pin needs full keyhood and
  `deg > 2` (at `deg = 2` slot 0 is genuinely OFF the line — `Φ′` itself, grade 5, odd).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements): the three
structure mechanisms (`s2MuMinimal_natDegree_even`, `s2MuMinimal_exactGrade`,
`s2KeyPoly_slotZero`), the degree dictionary (`s2KeyPoly_natDegree_pin`), KP-8's statement
(`s2_residual_to_initial`), the assembled field (`s2_initial_iff_residual`), and the FD-0
pin's field bindings (`s2_initial_iff_residual_fills`).

**DEPENDS.** C130kp3 (`s2_key_criterion`, `s2KeyPoly_key`, `s2KeyPoly_lift`) · C130kp1
(`S2MuDvd_key_of_not_slotOnGrade`) · C130kp0 (the predicates, `S2InitialEquiv_iff_gradedRes`,
`s2NormRes_eq_of_initialEquiv`, `S2InitialEquiv_symm`, `S2InitialEquiv_zero_right`,
`S2ExactGrade_of_initialEquiv`, `s2Hgt₂_neg`) · C130rp8 (`s2NormRes` bank, `s2GradeOf` bank,
`S2ExactGrade_key_pow`, `s2GradedCoeff_ne_zero_of_slotOnGrade`) · C130rp11 (`s2_g_monic`,
`s2_g_natDegree`, `s2_normalized_exists_normRes`, `s2_X_add_one_irreducible`) · C130rp1
(`s2SlotOnGrade_iff`, `s2GradedRes_coeff`, `s2GradedCoeff_eq_zero_of_grade_lt`) · C130rp2
(`tooth_sum_exact`, `tooth_C4X_grade`) · C130rp0 (`S2ExactGrade` normal forms +
existence/uniqueness/mul, `tooth_key`) · C131v (`dev_top_eq_one`, `monic_divByMonic`) ·
C131y (`dvSupp_le_term`) · C130s6 (`s2Hgt₂` bank, `toZ`) · C35b (`key_eq`, `sh_C`, `e1_eq`,
`h_eq`, `gaussVal_C`, `s2Key_natDegree`) · C02 (`KeyFrame.stageHeight_eq_inf`) · C130nv2
(`dev_zero_pin`) · B.02/B.04 (`dev`, `dev_eq_zero_of_lt`) · mathlib (`Polynomial`
coefficient/degree/monic bank, `modByMonic`/`divByMonic` bank, `WithTop` order bank).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130kp7

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C131v
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C130rp9 Uniformity.Density.Tower.C130rp11
open Uniformity.Density.Tower.C130kp0 Uniformity.Density.Tower.C130kp1
open Uniformity.Density.Tower.C130kp3

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — private copies and height/digit helpers (the private-copy pattern) -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private copy of C130rp1's `sh_one`: the stage height of the constant digit `1` is `0`. -/
private theorem stageHeight_one : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], sh_C h2 hq]
  simp

/-- **the monic-linear stage bound**: a monic digit of degree `1` has stage height `≤ 1` —
its leading coefficient `1` sits at level-1 abscissa `1` with zero valuation, so the level-1
support is at most `2·v(1) + 1·1 = 1`. -/
private theorem stageHeight_le_one_of_monic_linear {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 1) : (s2Frame h2 hq).stageHeight A ≤ 1 := by
  rw [KeyFrame.stageHeight_eq_inf]
  refine le_trans (Finset.inf_le (Finset.mem_range.mpr (show 1 < A.natDegree + 1 by omega))) ?_
  have hc : A.coeff 1 = 1 := by rw [← hdeg]; exact hA.coeff_natDegree
  rw [hc]
  simp only [e1_eq h2 hq, h_eq h2 hq, gaussVal_C, AddValuation.map_one, smul_zero, zero_add]
  simp

/-- **odd coefficients of `(x² − 2)^k` vanish**: powers of the S2 key are polynomials in
`x²`. -/
private theorem X_sq_sub_two_pow_coeff_odd :
    ∀ (k j : ℕ), (((Polynomial.X : Polynomial O) ^ 2 - Polynomial.C 2) ^ k).coeff (2 * j + 1) = 0 := by
  intro k
  induction k with
  | zero =>
    intro j
    rw [pow_zero, Polynomial.coeff_one]
    simp
  | succ k ih =>
    intro j
    rw [pow_succ, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_C, ih, zero_mul,
      sub_zero, Polynomial.coeff_mul_X_pow']
    rcases j with _ | j
    · rw [if_neg (by omega)]
    · rw [if_pos (by omega), show 2 * (j + 1) + 1 - 2 = 2 * j + 1 from by omega, ih]

/-- the key-power odd-coefficient law, at the frame's key. -/
private theorem key_pow_coeff_odd (k j : ℕ) :
    ((((s2Frame h2 hq).key : Polynomial O)) ^ k).coeff (2 * j + 1) = 0 := by
  rw [key_eq h2 hq, show s2Key O = Polynomial.X ^ 2 - Polynomial.C (2 : O) from rfl]
  exact X_sq_sub_two_pow_coeff_odd k j

/-- **the odd top digit is monic linear**: for monic `A` of degree `2m + 1`, the top
`Φ′`-development digit `dev Φ′ A m` is monic of degree `1` (the odd analogue of C131v's
`dev_top_eq_one`). -/
private theorem dev_top_monic_linear :
    ∀ (m : ℕ) (A : Polynomial O), A.Monic → A.natDegree = 2 * m + 1 →
      (dev (s2Frame h2 hq).key A m).Monic ∧ (dev (s2Frame h2 hq).key A m).natDegree = 1 := by
  intro m
  induction m with
  | zero =>
    intro A hA hdeg
    have hself : dev (s2Frame h2 hq).key A 0 = A := by
      rw [dev_zero_pin]
      refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
        key_natDegree_two h2 hq, hdeg]
      exact_mod_cast (by omega : 2 * 0 + 1 < 2)
    rw [hself]
    exact ⟨hA, by omega⟩
  | succ m ih =>
    intro A hA hdeg
    rw [show dev (s2Frame h2 hq).key A (m + 1)
        = dev (s2Frame h2 hq).key (A /ₘ (s2Frame h2 hq).key) m from rfl]
    have hdle : ((s2Frame h2 hq).key : Polynomial O).degree ≤ A.degree := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
        key_natDegree_two h2 hq, hdeg]
      exact_mod_cast (by omega : 2 ≤ 2 * (m + 1) + 1)
    refine ih _ (monic_divByMonic hA (s2Frame h2 hq).hmonic hdle) ?_
    rw [Polynomial.natDegree_divByMonic A (s2Frame h2 hq).hmonic, key_natDegree_two h2 hq,
      hdeg]
    omega

/-- **the even top height is `0`**: monic of degree `2m` has top digit `1` (C131v), height
`0`. -/
private theorem dvHgt_zero_of_monic_even {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 2 * m) : dvHgt (s2Frame h2 hq) g m = 0 := by
  rw [dvHgt, dev_top_eq_one (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos m g hmon
    (by rw [key_natDegree_two h2 hq]; omega), stageHeight_one h2 hq]

/-- **the odd top height is `≤ 1`**: monic of degree `2m + 1` has monic-linear top digit. -/
private theorem dvHgt_le_one_of_monic_odd {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 2 * m + 1) : dvHgt (s2Frame h2 hq) g m ≤ 1 := by
  obtain ⟨hm, hdeg⟩ := dev_top_monic_linear h2 hq m g hmon hd
  rw [dvHgt]
  exact stageHeight_le_one_of_monic_linear h2 hq hm hdeg

/-- **the term bound at a finite-height slot**: the exact grade is at most any slot term
`2·dv + 5·j` (C131y's `dvSupp_le_term`, read through RP-0's normal form and pushed to ℕ). -/
private theorem grade_le_of_dvHgt_le {β c j : ℕ} {g : Polynomial O}
    (hβ : S2ExactGrade h2 hq β g) (hc : dvHgt (s2Frame h2 hq) g j ≤ (c : ℕ∞)) :
    β ≤ 2 * c + 5 * j := by
  have hterm := dvSupp_le_term (s2Frame h2 hq) g 5 (by norm_num : (0 : ℕ) < 2) j
  rw [(S2ExactGrade_iff_dvSupp h2 hq).mp hβ] at hterm
  have h2c : (2 : ℕ) • dvHgt (s2Frame h2 hq) g j ≤ ((2 * c : ℕ) : ℕ∞) := by
    rw [two_nsmul]
    calc dvHgt (s2Frame h2 hq) g j + dvHgt (s2Frame h2 hq) g j
        ≤ (c : ℕ∞) + (c : ℕ∞) := add_le_add hc hc
      _ = ((2 * c : ℕ) : ℕ∞) := by push_cast; ring
  have hle : ((β : ℕ) : ℕ∞) ≤ ((2 * c + 5 * j : ℕ) : ℕ∞) := by
    calc ((β : ℕ) : ℕ∞)
        ≤ 2 • dvHgt (s2Frame h2 hq) g j + ((5 * j : ℕ) : ℕ∞) := by
          refine hterm.trans (le_of_eq ?_)
          push_cast
          ring
      _ ≤ ((2 * c : ℕ) : ℕ∞) + ((5 * j : ℕ) : ℕ∞) := add_le_add h2c le_rfl
      _ = ((2 * c + 5 * j : ℕ) : ℕ∞) := by push_cast; ring
  exact_mod_cast hle

/-- **the top slot is on its own line**: monic of degree `2m` has slot `m` on the
grade-`5m` line (the equation `2·0 + 5m = 5m`; whether `5m` IS the grade is
`s2MuMinimal_exactGrade`'s business). -/
private theorem slot_top_of_monic_even {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 2 * m) : S2SlotOnGrade h2 hq (5 * m) g m :=
  (s2SlotOnGrade_iff h2 hq).mpr
    ⟨0, by rw [dvHgt_zero_of_monic_even h2 hq hmon hd]; norm_num, by omega⟩

/-! ## Part 1 — ★ the parity pin (published Lemma 2.10's genre, the parity half)

μ₂-minimality forces EVEN degree.  The refuting construction for `deg g = 2m + 1`: multiply
by the monic-linear `q := x − g₂ₘ` (chosen to kill the `x^(2m+1)` coefficient of the
product) and subtract `Φ′^(m+1)`; the difference has degree `≤ 2m` yet the SAME initial
form as `g·q` — the key power sits at value `5(m+1)`, strictly above
`µ₂(g·q) ≤ (5m + 2) + 2` (both top digits are monic linear, stage height `≤ 1`). -/

/-- ★ **the parity pin**: a monic μ₂-minimal polynomial has even degree (published Lemma
2.10's `deg g = s′(g)·deg Φ′` genre — the concrete parity half at `deg Φ′ = 2`). -/
theorem s2MuMinimal_natDegree_even {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2MuMinimal h2 hq g) : 2 ∣ g.natDegree := by
  by_contra hodd
  obtain ⟨m, hd⟩ : ∃ m, g.natDegree = 2 * m + 1 := ⟨g.natDegree / 2, by omega⟩
  set a := g.coeff (2 * m) with ha
  set q : Polynomial O := Polynomial.X - Polynomial.C a with hqdef
  have hqmon : q.Monic := Polynomial.monic_X_sub_C a
  have hqdeg : q.natDegree = 1 := Polynomial.natDegree_X_sub_C a
  obtain ⟨β, hβ⟩ := S2ExactGrade_exists h2 hq hmon.ne_zero
  obtain ⟨γ, hγ⟩ := S2ExactGrade_exists h2 hq hqmon.ne_zero
  have hβle : β ≤ 2 * 1 + 5 * m :=
    grade_le_of_dvHgt_le h2 hq hβ (dvHgt_le_one_of_monic_odd h2 hq hmon hd)
  have hγle : γ ≤ 2 * 1 + 5 * 0 :=
    grade_le_of_dvHgt_le h2 hq hγ
      (dvHgt_le_one_of_monic_odd h2 hq hqmon (by rw [hqdeg]))
  have hgq : S2ExactGrade h2 hq (β + γ) (g * q) := S2ExactGrade_mul h2 hq hβ hγ
  have hkp : S2ExactGrade h2 hq (5 * (m + 1))
      (((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)) := S2ExactGrade_key_pow h2 hq (m + 1)
  have hlt : β + γ < 5 * (m + 1) := by omega
  have hltc : ((β + γ : ℕ) : WithTop ℤ) < ((5 * (m + 1) : ℕ) : WithTop ℤ) := by
    exact_mod_cast hlt
  have hvgq : s2Hgt₂ h2 hq (g * q) = ((β + γ : ℕ) : WithTop ℤ) := hgq
  have hvkp : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) ^ (m + 1))
      = ((5 * (m + 1) : ℕ) : WithTop ℤ) := hkp
  have hvf : s2Hgt₂ h2 hq (g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1))
      = ((β + γ : ℕ) : WithTop ℤ) := by
    rw [sub_eq_add_neg, s2Hgt₂_add_eq h2 hq _ _ (by
        rw [s2Hgt₂_neg h2 hq, hvgq, hvkp]; exact hltc.ne), s2Hgt₂_neg h2 hq, hvgq, hvkp]
    exact min_eq_left hltc.le
  have hf_exact : S2ExactGrade h2 hq (β + γ)
      (g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)) := hvf
  have hf0 : g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1) ≠ 0 :=
    S2ExactGrade_not_zero h2 hq hf_exact
  have hequiv : S2InitialEquiv h2 hq
      (g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)) (g * q) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [show (g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)) - g * q
          = -(((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)) from by ring,
        s2Hgt₂_neg h2 hq, hvkp, hvf]
      exact hltc
    · rw [hvf, hvgq]
  have hdvd : S2MuDvd h2 hq g
      (g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)) := ⟨q, hequiv⟩
  -- the degree collapse: both top coefficients cancel
  have hkpmon : (((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)).Monic :=
    (s2Frame h2 hq).hmonic.pow _
  have hkpdeg : (((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)).natDegree = (m + 1) * 2 := by
    rw [Polynomial.natDegree_pow, key_natDegree_two h2 hq]
  have hfdeg : (g * q - ((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)).natDegree ≤ 2 * m := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hgq_coeff : (g * q).coeff (n + 1) = g.coeff n - g.coeff (n + 1) * a := by
      rw [hqdef, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
        Polynomial.coeff_mul_C]
    rw [Polynomial.coeff_sub, hgq_coeff]
    rcases Nat.lt_trichotomy n (2 * m + 1) with hcase | hcase | hcase
    · -- `n = 2m`: the chosen constant kills the coefficient; the key power is odd-dead
      have hn' : n = 2 * m := by omega
      subst hn'
      have hg1 : g.coeff (2 * m + 1) = 1 := by
        have h := hmon.coeff_natDegree
        rwa [hd] at h
      rw [hg1, one_mul, key_pow_coeff_odd h2 hq (m + 1) m, ← ha, sub_zero, sub_self]
    · -- `n = 2m + 1`: both leading coefficients are `1`
      have hn' : n = 2 * m + 1 := by omega
      subst hn'
      have hg1 : g.coeff (2 * m + 1) = 1 := by
        have h := hmon.coeff_natDegree
        rwa [hd] at h
      have hg2 : g.coeff (2 * m + 1 + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hk1 : (((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)).coeff (2 * m + 1 + 1) = 1 := by
        have h := hkpmon.coeff_natDegree
        rwa [hkpdeg, show (m + 1) * 2 = 2 * m + 1 + 1 from by ring] at h
      rw [hg1, hg2, hk1, zero_mul, sub_zero, sub_self]
    · -- `n ≥ 2m + 2`: everything is past its degree
      have hg2 : g.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hg3 : g.coeff (n + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hk2 : (((s2Frame h2 hq).key : Polynomial O) ^ (m + 1)).coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hkpdeg]; omega)
      rw [hg2, hg3, hk2, zero_mul, sub_zero, sub_zero]
  exact hmin.2 _ hf0 (by omega) hdvd

/-! ## Part 2 — ★ the grade pin (published Lemma 2.11's invariant)

μ₂-minimality pins the value: `µ₂(g) = 5·(deg g/2)` — the top slot is on the grade line.
If the value sat strictly below `5m`, the truncation `g − Φ′^m` (degree `< 2m` by the
common leading coefficient) would carry the SAME initial form as `g`, violating
minimality. -/

/-- ★ **the grade pin**: a monic μ₂-minimal polynomial has exact grade `5·(deg g/2)`
(published Lemma 2.11's constancy of `µ(g)/deg g` at the S2 slope `5/2`). -/
theorem s2MuMinimal_exactGrade {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2MuMinimal h2 hq g) : S2ExactGrade h2 hq (5 * (g.natDegree / 2)) g := by
  have heven := s2MuMinimal_natDegree_even h2 hq hmon hmin
  set m := g.natDegree / 2 with hm
  have hd : g.natDegree = 2 * m := by omega
  obtain ⟨β, hβ⟩ := S2ExactGrade_exists h2 hq hmon.ne_zero
  have hle : β ≤ 2 * 0 + 5 * m :=
    grade_le_of_dvHgt_le h2 hq hβ (le_of_eq (dvHgt_zero_of_monic_even h2 hq hmon hd))
  rcases (show β ≤ 5 * m from by omega).lt_or_eq with hlt | heq
  · -- strictly below the top term: the truncation `g − Φ′^m` refutes minimality
    exfalso
    have hkp : S2ExactGrade h2 hq (5 * m) (((s2Frame h2 hq).key : Polynomial O) ^ m) :=
      S2ExactGrade_key_pow h2 hq m
    rcases eq_or_ne (g - ((s2Frame h2 hq).key : Polynomial O) ^ m) 0 with hf0 | hf0
    · have hg : g = ((s2Frame h2 hq).key : Polynomial O) ^ m := sub_eq_zero.mp hf0
      rw [hg] at hβ
      exact absurd (S2ExactGrade_unique h2 hq hβ hkp) (by omega)
    · have hltc : ((β : ℕ) : WithTop ℤ) < ((5 * m : ℕ) : WithTop ℤ) := by exact_mod_cast hlt
      have hvg : s2Hgt₂ h2 hq g = ((β : ℕ) : WithTop ℤ) := hβ
      have hvk : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) ^ m)
          = ((5 * m : ℕ) : WithTop ℤ) := hkp
      have hvf : s2Hgt₂ h2 hq (g - ((s2Frame h2 hq).key : Polynomial O) ^ m)
          = ((β : ℕ) : WithTop ℤ) := by
        rw [sub_eq_add_neg, s2Hgt₂_add_eq h2 hq _ _ (by
            rw [s2Hgt₂_neg h2 hq, hvg, hvk]; exact hltc.ne), s2Hgt₂_neg h2 hq, hvg, hvk]
        exact min_eq_left hltc.le
      have hequiv : S2InitialEquiv h2 hq
          (g - ((s2Frame h2 hq).key : Polynomial O) ^ m) g := by
        refine Or.inl ⟨?_, ?_⟩
        · rw [show (g - ((s2Frame h2 hq).key : Polynomial O) ^ m) - g
              = -(((s2Frame h2 hq).key : Polynomial O) ^ m) from by ring,
            s2Hgt₂_neg h2 hq, hvk, hvf]
          exact hltc
        · rw [hvf, hvg]
      have hdvd : S2MuDvd h2 hq g (g - ((s2Frame h2 hq).key : Polynomial O) ^ m) :=
        ⟨1, by rw [mul_one]; exact hequiv⟩
      -- degree drop: monic minus monic of the same degree
      have hkm : (((s2Frame h2 hq).key : Polynomial O) ^ m).Monic :=
        (s2Frame h2 hq).hmonic.pow m
      have hdeg_eq : g.degree = (((s2Frame h2 hq).key : Polynomial O) ^ m).degree := by
        rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
          Polynomial.degree_eq_natDegree hkm.ne_zero, Polynomial.natDegree_pow,
          key_natDegree_two h2 hq, hd, Nat.mul_comm]
      have hdlt := Polynomial.degree_sub_lt hdeg_eq hmon.ne_zero
        (by rw [hmon.leadingCoeff, hkm.leadingCoeff])
      exact hmin.2 _ hf0 (Polynomial.natDegree_lt_natDegree hf0 hdlt) hdvd
  · rw [hm, ← heq]
    exact hβ

/-! ## Part 3 — ★ the slot-0 pin (published Lemma 5.1's `s(g) = 0` clause)

A key polynomial of degree `> 2` has slot 0 ON the grade line.  The one-step DEFLATION:
if slot 0 is off the line, KP-1's carried-key backward lemma factors `g`'s initial form as
`Φ′·q`; primality then forces `g ∣µ₂ Φ′` (killed by minimality, `deg Φ′ = 2 < deg g`) or
`g ∣µ₂ q` (killed by the grade ledger: `β = 5 + µ₂(q)` yet `µ₂(q) = β + µ₂(q′)` — cleared
grades are naturals). -/

/-- ★ **the slot-0 pin**: a key polynomial of degree `> 2` has slot 0 on its grade line. -/
theorem s2KeyPoly_slotZero {g : Polynomial O} {β : ℕ} (hkey : S2KeyPoly h2 hq g)
    (hβ : S2ExactGrade h2 hq β g) (hdeg : 2 < g.natDegree) :
    S2SlotOnGrade h2 hq β g 0 := by
  obtain ⟨hmon, hmin, -, -, hprime⟩ := hkey
  by_contra hgate
  obtain ⟨q, hq'⟩ := S2MuDvd_key_of_not_slotOnGrade h2 hq hβ hgate
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq'
    exact hmon.ne_zero ((S2InitialEquiv_zero_right h2 hq).mp hq')
  have hprod : S2MuDvd h2 hq g (((s2Frame h2 hq).key : Polynomial O) * q) :=
    ⟨1, by rw [mul_one]; exact S2InitialEquiv_symm h2 hq hq'⟩
  rcases hprime _ _ hprod with hL | hR
  · -- `g ∣µ₂ Φ′` refutes minimality
    exact hmin.2 _ (s2Frame h2 hq).hmonic.ne_zero
      (by rw [key_natDegree_two h2 hq]; omega) hL
  · -- `g ∣µ₂ q` refutes the grade ledger
    obtain ⟨q', hq''⟩ := hR
    have hq'0 : q' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq''
      exact hq0 ((S2InitialEquiv_zero_right h2 hq).mp hq'')
    have hγq := S2ExactGrade_s2GradeOf h2 hq hq0
    have hγ' := S2ExactGrade_s2GradeOf h2 hq hq'0
    have hkq : S2ExactGrade h2 hq (5 + s2GradeOf h2 hq q)
        (((s2Frame h2 hq).key : Polynomial O) * q) :=
      S2ExactGrade_mul h2 hq (tooth_key h2 hq) hγq
    have hkqβ : S2ExactGrade h2 hq β (((s2Frame h2 hq).key : Polynomial O) * q) :=
      S2ExactGrade_of_initialEquiv h2 hq hβ hq'
    have h1 : β = 5 + s2GradeOf h2 hq q := S2ExactGrade_unique h2 hq hkqβ hkq
    have hgq' : S2ExactGrade h2 hq (β + s2GradeOf h2 hq q') (g * q') :=
      S2ExactGrade_mul h2 hq hβ hγ'
    have hq2 : S2ExactGrade h2 hq (β + s2GradeOf h2 hq q') q :=
      S2ExactGrade_of_initialEquiv h2 hq hgq' (S2InitialEquiv_symm h2 hq hq'')
    have h2' : s2GradeOf h2 hq q = β + s2GradeOf h2 hq q' :=
      S2ExactGrade_unique h2 hq hγq hq2
    omega

/-! ## Part 4 — the key-structure bank (published Lemma 5.3, machine-proved)

Everything a key polynomial's residual data must satisfy, assembled from the three pins.
The master collects: even degree, the grade `5·(deg/2)`, the LOW gate (the slot of the
grade's own parity is on the line — slot 0 for proper keys, the top slot for the `∼ Φ′`
fiber), and the `deg/2` parity dichotomy. -/

private theorem key_master {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    2 ∣ g.natDegree
    ∧ S2ExactGrade h2 hq (5 * (g.natDegree / 2)) g
    ∧ S2SlotOnGrade h2 hq (5 * (g.natDegree / 2)) g (g.natDegree / 2 % 2)
    ∧ (g.natDegree / 2 = 1 ∨ 2 ∣ g.natDegree / 2) := by
  obtain ⟨hmon, hmin, hirr⟩ := hkey
  have heven := s2MuMinimal_natDegree_even h2 hq hmon hmin
  have hβ := s2MuMinimal_exactGrade h2 hq hmon hmin
  have hpos : 0 < g.natDegree := hmin.1
  rcases Nat.lt_or_ge 2 g.natDegree with hbig | hsmall
  · -- `deg g > 2`: the slot-0 pin fires, the grade is even
    have h0 := s2KeyPoly_slotZero h2 hq ⟨hmon, hmin, hirr⟩ hβ hbig
    have hm2 : 2 ∣ g.natDegree / 2 := by
      obtain ⟨c, -, hc⟩ := (s2SlotOnGrade_iff h2 hq).mp h0
      omega
    refine ⟨heven, hβ, ?_, Or.inr hm2⟩
    rw [show g.natDegree / 2 % 2 = 0 from by omega]
    exact h0
  · -- `deg g = 2`: the top slot IS the parity slot (grade 5, odd)
    have hd2 : g.natDegree = 2 := by omega
    have htop := slot_top_of_monic_even h2 hq hmon (m := 1) (by omega)
    refine ⟨heven, hβ, ?_, Or.inl (by omega)⟩
    rw [show g.natDegree / 2 = 1 from by omega]
    exact htop

/-- **the grade of a key polynomial**: `µ₂(g) = 5·(deg g/2)` (published Lemma 2.11 at
keys; the equal-value input of the Prop 5.6 assembly is DERIVED, never hypothesized). -/
theorem s2KeyPoly_exactGrade {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    S2ExactGrade h2 hq (5 * (g.natDegree / 2)) g :=
  (key_master h2 hq hkey).2.1

/-- **the residual scalar of a key polynomial is nonzero** (published Lemma 5.3's
`s(g) = 0` read at the graded residual: the lowest `y`-coefficient lives). -/
theorem s2KeyPoly_gradedRes_coeff_zero_ne_zero {g : Polynomial O}
    (hkey : S2KeyPoly h2 hq g) :
    (s2GradedRes h2 hq (5 * (g.natDegree / 2)) g).coeff 0 ≠ 0 := by
  obtain ⟨-, -, hlow, -⟩ := key_master h2 hq hkey
  have h := s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hlow
  rw [show g.natDegree / 2 % 2 / 2 = 0 from by omega] at h
  rw [s2GradedRes_coeff]
  exact h

/-- ★ **the strip is trivial on keys**: the normalized residual of a key polynomial IS its
graded residual at the pinned grade — the trailing `y`-power is `0`. -/
theorem s2KeyPoly_normRes_eq_gradedRes {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    s2NormRes h2 hq g = s2GradedRes h2 hq (5 * (g.natDegree / 2)) g := by
  have hβ := s2KeyPoly_exactGrade h2 hq hkey
  have hntd : (s2GradedRes h2 hq (5 * (g.natDegree / 2)) g).natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero
      (s2KeyPoly_gradedRes_coeff_zero_ne_zero h2 hq hkey))
  rw [s2NormRes_of_exact h2 hq hβ, hntd]
  exact Function.iterate_zero_apply _ _

/-- **the residual degree of a key polynomial**: `deg R₃(g) = deg g/4` (published
Corollary 4.4's `s′ − s = e·deg R` at `s = 0`, `e = 2`, `deg g = 2s′`). -/
theorem s2KeyPoly_normRes_natDegree {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    (s2NormRes h2 hq g).natDegree = g.natDegree / 4 := by
  obtain ⟨heven, -, -, -⟩ := key_master h2 hq hkey
  rw [s2KeyPoly_normRes_eq_gradedRes h2 hq hkey]
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [s2GradedRes_coeff]
    exact s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega)
  · have htop := slot_top_of_monic_even h2 hq hkey.1 (m := g.natDegree / 2) (by omega)
    have h := s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq htop
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [s2GradedRes_coeff, show g.natDegree / 4 = g.natDegree / 2 / 2 from by omega]
    exact h

/-- **the unit dichotomy**: a key polynomial has UNIT residual exactly when it has the
carried key's degree `2` (published Lemma 5.3's two fibers: `g ∼µ₂ φ₂` versus the proper
keys). -/
theorem s2KeyPoly_isUnit_normRes_iff {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    IsUnit (s2NormRes h2 hq g) ↔ g.natDegree = 2 := by
  obtain ⟨heven, -, -, -⟩ := key_master h2 hq hkey
  have hdegψ := s2KeyPoly_normRes_natDegree h2 hq hkey
  have hpos : 0 < g.natDegree := hkey.2.1.1
  constructor
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · intro h2d
    have h0 : (s2NormRes h2 hq g).natDegree = 0 := by rw [hdegψ, h2d]
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (s2NormRes_coeff_zero_ne_zero h2 hq hkey.1.ne_zero))

open scoped Classical in
/-- ★ **the degree dictionary** (published Lemma 5.3's degree display
`deg g = e·(deg ψ)·m = 4·deg ψ`, with the `∼ φ₂` fiber at `deg g = 2`): a key polynomial's
degree is DETERMINED by its normalized residual. -/
theorem s2KeyPoly_natDegree_pin {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    g.natDegree
      = if IsUnit (s2NormRes h2 hq g) then 2 else 4 * (s2NormRes h2 hq g).natDegree := by
  obtain ⟨heven, -, -, hpar⟩ := key_master h2 hq hkey
  have hdegψ := s2KeyPoly_normRes_natDegree h2 hq hkey
  have hpos : 0 < g.natDegree := hkey.2.1.1
  split_ifs with hu
  · exact (s2KeyPoly_isUnit_normRes_iff h2 hq hkey).mp hu
  · have hne2 : g.natDegree ≠ 2 :=
      fun h => hu ((s2KeyPoly_isUnit_normRes_iff h2 hq hkey).mpr h)
    rw [hdegψ]
    omega

/-! ## Part 5 — ★ NODE KP-7: the forward direction at its honest scope

ADJUDICATION of the brief's scope question: NO key-polynomial hypothesis is needed —
KP-0's normalized tie is universal.  Published Prop 5.6's (3)→(2) for keys is the
specialization consumed by KP-9 below. -/

/-- ★ **NODE KP-7 — initial equivalence forces residual equality, UNIVERSALLY**:
`g ∼µ₂ h → R₃(g) = R₃(h)` for ALL `g, h` — no key-polynomial, monic, degree, or nonzero
hypothesis (KP-0's `s2NormRes_eq_of_initialEquiv`, recorded in the node's shape). -/
theorem s2_initial_to_residual {g h : Polynomial O} (hgh : S2InitialEquiv h2 hq g h) :
    s2NormRes h2 hq g = s2NormRes h2 hq h :=
  s2NormRes_eq_of_initialEquiv h2 hq hgh

/-! ## Part 6 — ★★ NODE KP-8: the converse for arbitrary concrete key polynomials

Equal residuals + keyhood: the dictionary forces equal degrees, hence equal grades
`5·(deg/2)`; the trivial strip turns residual equality into GRADED equality at the common
exact grade; KP-0's graded-piece IFF fires backward.  The zero clause never arises — keys
are monic. -/

/-- ★★ **NODE KP-8 — residual equality forces initial equivalence, for key polynomials**
(published Prop 5.6's (2)→(3), the hard direction, machine-proved at the landed
operators). -/
theorem s2_residual_to_initial {g h : Polynomial O} (hkg : S2KeyPoly h2 hq g)
    (hkh : S2KeyPoly h2 hq h) (hres : s2NormRes h2 hq g = s2NormRes h2 hq h) :
    S2InitialEquiv h2 hq g h := by
  have hpin_g := s2KeyPoly_natDegree_pin h2 hq hkg
  have hpin_h := s2KeyPoly_natDegree_pin h2 hq hkh
  rw [hres] at hpin_g
  have hd : g.natDegree = h.natDegree := hpin_g.trans hpin_h.symm
  have hβg := s2KeyPoly_exactGrade h2 hq hkg
  have heqg := s2KeyPoly_normRes_eq_gradedRes h2 hq hkg
  rw [hd] at hβg heqg
  exact (S2InitialEquiv_iff_gradedRes h2 hq hβg (s2KeyPoly_exactGrade h2 hq hkh)).mpr
    (by rw [← heqg, ← s2KeyPoly_normRes_eq_gradedRes h2 hq hkh, hres])

/-! ## Part 7 — ★★ NODE KP-9: the Proposition-5.6 field, assembled -/

/-- ★★ **NODE KP-9 — the S2 `initial_iff_residual`** (published Proposition 5.6(2)⇔(3);
the C130fg `FGMNSourceLaws.initial_iff_residual` / A-C.11 `FGMNCalculus.nuEquiv_iff_Rres`
hypothesis list, BOTH `keyPolynomial` hypotheses retained per U9 §4.1): for key
polynomials, initial-form equivalence IS equality of normalized residuals. -/
theorem s2_initial_iff_residual :
    ∀ g h : Polynomial O, S2KeyPoly h2 hq g → S2KeyPoly h2 hq h →
      (S2InitialEquiv h2 hq g h ↔ s2NormRes h2 hq g = s2NormRes h2 hq h) :=
  fun _ _ hkg hkh =>
    ⟨s2_initial_to_residual h2 hq, s2_residual_to_initial h2 hq hkg hkh⟩

/-- ★ **the FD-0 pin**: if `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reads
`normalizedResidual := s2NormRes`, `keyPolynomial := S2KeyPoly`, and
`initialEquiv := S2InitialEquiv`, then the `FGMNSourceLaws.initial_iff_residual` field
shape holds for `S` — zero residual assembly work at FD-0 for this field. -/
theorem s2_initial_iff_residual_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5)
    (hnorm : S.normalizedResidual = s2NormRes h2 hq)
    (hkp : S.keyPolynomial = S2KeyPoly h2 hq)
    (hie : S.initialEquiv = S2InitialEquiv h2 hq) :
    ∀ g h : Polynomial O, S.keyPolynomial g → S.keyPolynomial h →
      (S.initialEquiv g h ↔ S.normalizedResidual g = S.normalizedResidual h) := by
  intro g h hg hh
  rw [hkp] at hg hh
  rw [hie, hnorm]
  exact s2_initial_iff_residual h2 hq g h hg hh

/-! ## Part 8 — teeth

The field is non-degenerate in BOTH truth values on the landed keys: the two landed keys
`Φ′` (residual `1`) and `Φ′² + 4x` (residual `X + 1`) are NOT equivalent, and the
grade-15 perturbation of the lift gives a genuinely EQUIVALENT key pair. -/

/-- ★ **tooth (the iff refutes)**: the two landed keys are NOT initial-equivalent — their
residuals differ (`1` vs `X + 1`), so the assembled field's forward direction refutes the
equivalence. -/
theorem tooth_landed_keys_not_equiv :
    ¬ S2InitialEquiv h2 hq ((s2Frame h2 hq).key : Polynomial O)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X) := by
  intro hEq
  have h := (s2_initial_iff_residual h2 hq _ _ (s2KeyPoly_key h2 hq)
    (s2KeyPoly_lift h2 hq)).mp hEq
  rw [s2NormRes_key h2 hq, s2_normalized_exists_normRes h2 hq] at h
  have hX : (Polynomial.X : Polynomial ((s2DepthTwo h2 hq).fld 2)) = 0 := by
    linear_combination -h
  exact Polynomial.X_ne_zero hX

/-- the perturbation is initial-invisible: `Φ′² + 4x ∼µ₂ Φ′² + 4x + 4x·Φ′` (the
perturbation `4x·Φ′` sits at grade `15 > 10`; kp0's perturbation pattern at the lift). -/
theorem tooth_lift_perturb_equiv :
    S2InitialEquiv h2 hq
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X
        + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
  have h15 : S2ExactGrade h2 hq 15
      (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) :=
    S2ExactGrade_mul h2 hq (tooth_C4X_grade h2 hq) (tooth_key h2 hq)
  have hv15 : s2Hgt₂ h2 hq (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
      = ((15 : ℕ) : WithTop ℤ) := h15
  have hv10 : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X) = ((10 : ℕ) : WithTop ℤ) :=
    tooth_sum_exact h2 hq
  have hlt : ((10 : ℕ) : WithTop ℤ) < ((15 : ℕ) : WithTop ℤ) := by
    exact_mod_cast (by norm_num : (10 : ℕ) < 15)
  refine Or.inl ⟨?_, ?_⟩
  · rw [show (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)
        - (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X
          + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
        = -(Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) from by ring,
      s2Hgt₂_neg h2 hq, hv15, hv10]
    exact hlt
  · have hne : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
        ≠ s2Hgt₂ h2 hq (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
      rw [hv10, hv15]
      exact hlt.ne
    rw [s2Hgt₂_add_eq h2 hq _ _ hne, hv10, hv15]
    exact (min_eq_left hlt.le).symm

/-- ★ **tooth (a second key in the lift's class)**: the perturbed lift
`Φ′² + 4x + 4x·Φ′` IS a key polynomial — monic of the recipe degree with the SAME residual
`X + 1` (transported along the equivalence), so KP-4's criterion fires. -/
theorem tooth_perturbed_lift_isKey :
    S2KeyPoly h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X
      + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
  have h4 : (4 : O) ≠ 0 := by
    have h2ne : (2 : O) ≠ 0 := h2.ne_zero
    rw [show (4 : O) = 2 * 2 from by norm_num]
    exact mul_ne_zero h2ne h2ne
  have hC4X : (Polynomial.C (4 : O) * Polynomial.X) ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr h4) Polynomial.X_ne_zero
  have hP0 : (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) ≠ 0 :=
    mul_ne_zero hC4X (s2Frame h2 hq).hmonic.ne_zero
  have hPdeg : (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key).natDegree = 3 := by
    rw [Polynomial.natDegree_mul hC4X (s2Frame h2 hq).hmonic.ne_zero,
      Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr h4) Polynomial.X_ne_zero,
      Polynomial.natDegree_C, Polynomial.natDegree_X, key_natDegree_two h2 hq]
  have hdlt : (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key).degree
      < (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X).degree := by
    rw [Polynomial.degree_eq_natDegree hP0,
      Polynomial.degree_eq_natDegree (s2_g_monic h2 hq).ne_zero, hPdeg,
      s2_g_natDegree h2 hq]
    exact_mod_cast (by norm_num : (3 : ℕ) < 4)
  have hmon₂ : (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X
      + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key).Monic :=
    (s2_g_monic h2 hq).add_of_left hdlt
  have hdeg₂ : (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X
      + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key).natDegree = 4 := by
    have h := Polynomial.degree_add_eq_left_of_degree_lt hdlt
    rw [Polynomial.degree_eq_natDegree (s2_g_monic h2 hq).ne_zero, s2_g_natDegree h2 hq] at h
    exact Polynomial.natDegree_eq_of_degree_eq_some h
  have hres₂ : s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X
      + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
      = Polynomial.X + 1 := by
    rw [← s2_initial_to_residual h2 hq (tooth_lift_perturb_equiv h2 hq)]
    exact s2_normalized_exists_normRes h2 hq
  refine s2_key_criterion h2 hq _ hmon₂ (by rw [hdeg₂, key_natDegree_two h2 hq]) ?_ ?_ ?_
  · rw [hres₂]
    exact s2_X_add_one_irreducible h2 hq
  · rw [hres₂,
      show (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = Polynomial.C 1 from (map_one _).symm]
    exact Polynomial.natDegree_X_add_C 1
  · rw [hres₂, Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
      zero_add]
    exact one_ne_zero

/-- ★ **tooth (the iff fires positively)**: a genuinely equivalent KEY pair — the lift and
its perturbation are both keys, initial-equivalent, and the assembled field extracts their
residual equality. -/
theorem tooth_equivalent_key_pair :
    S2KeyPoly h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
    ∧ S2KeyPoly h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X
        + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
    ∧ S2InitialEquiv h2 hq
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X
          + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
    ∧ s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)
        = s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X
          + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) :=
  ⟨s2KeyPoly_lift h2 hq, tooth_perturbed_lift_isKey h2 hq, tooth_lift_perturb_equiv h2 hq,
    (s2_initial_iff_residual h2 hq _ _ (s2KeyPoly_lift h2 hq)
      (tooth_perturbed_lift_isKey h2 hq)).mp (tooth_lift_perturb_equiv h2 hq)⟩

end S2

end Uniformity.Density.Tower.C130kp7

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130kp7.s2MuMinimal_natDegree_even
#print axioms Uniformity.Density.Tower.C130kp7.s2MuMinimal_exactGrade
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_slotZero
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_exactGrade
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_gradedRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_normRes_eq_gradedRes
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_normRes_natDegree
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_isUnit_normRes_iff
#print axioms Uniformity.Density.Tower.C130kp7.s2KeyPoly_natDegree_pin
#print axioms Uniformity.Density.Tower.C130kp7.s2_initial_to_residual
#print axioms Uniformity.Density.Tower.C130kp7.s2_residual_to_initial
#print axioms Uniformity.Density.Tower.C130kp7.s2_initial_iff_residual
#print axioms Uniformity.Density.Tower.C130kp7.s2_initial_iff_residual_fills
#print axioms Uniformity.Density.Tower.C130kp7.tooth_landed_keys_not_equiv
#print axioms Uniformity.Density.Tower.C130kp7.tooth_lift_perturb_equiv
#print axioms Uniformity.Density.Tower.C130kp7.tooth_perturbed_lift_isKey
#print axioms Uniformity.Density.Tower.C130kp7.tooth_equivalent_key_pair

end AxCheck
