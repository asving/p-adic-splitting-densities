/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130kp3
import Uniformity.ChapC.C130lb
import Uniformity.ChapC.C78adj

/-!
# Uniformity.ChapC.C130kp5 — S2-source plan nodes KP-5/KP-6

**S2-source plan nodes KP-5 + KP-6** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 rows
KP-5 "Prove `key_irreducible`; state any source-to-fraction-field bridge explicitly" and KP-6
"Prove `carried_key_is_key` and `carried_key_residual`"), on the landed key inventory
(C130kp3: `S2KeyPoly`, `s2_key_criterion`, `s2KeyPoly_lift`), CC-15's executed Gauss transport
(C130lb: `irreducible_of_fraction_map_irreducible`), and the tower's own composed key
(C78adj: `composedKey_s2Tower`).

## NODE KP-5 — `key_irreducible` at the landed key, the bridge stated explicitly

The abstract field (`C130fg.FGMNSourceLaws.key_irreducible`) is a UNIVERSAL statement over
every key polynomial (`∀ g, S.keyPolynomial g → g.Monic → Irreducible g`); discharging it in
full needs FGMN's published Lemma 1.8 (irreducibility over the fraction field `K_v[x]`), which
is not landed for the S2 model and is honestly out of scope for a single node (CC-15's own
verdict: "a realization owes only Lemma 1.8 plus the `K_v` dictionary").  What THIS node
proves is the row's own request: the landed key `Φ′ = x² − 2` (the S2 model's `(s2Frame
h2 hq).key`) is irreducible in `Polynomial O` — **directly**, via mathlib's classical
Eisenstein criterion at the maximal ideal (Eisenstein-style directness, per the row's own
suggestion, is simpler here than staging through a fraction field):

* ★ `s2Key_eisenstein_irreducible` — `Irreducible (s2Key O)`: `Polynomial.
  irreducible_of_eisenstein_criterion` at `P := IsLocalRing.maximalIdeal O`. `P` is prime
  (maximal ideals are prime); the leading coefficient `1 ∉ P` (units are never in the maximal
  ideal); the sole below-degree coefficient needing a scope check is `coeff 0 = −2 ∈ P`
  (`h2.not_isUnit`, `Ideal.neg_mem`) and `coeff 1 = 0 ∈ P` trivially; the constant term is
  **exactly** at valuation one, `−2 ∉ P² = (4)` (`4 ∣ 2` would make `2` a unit, contradicting
  `h2`); and `s2Key O` is primitive (monic). No fraction field, no Gauss transport, and no
  `FGMNSourceLaws` field is needed for this specific key.
* **The bridge, stated explicitly** (the row's own charge): the executed CC-15 Gauss leg
  (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, C130lb) is an **iff**, not
  a one-way transport. Since `s2Key O` is monic, the SAME lemma, read forward, upgrades the
  `O[x]`-irreducibility just proved into the fraction-field statement any faithful realization
  of Lemma 1.8 would need to supply as its hypothesis (★
  `s2Key_irreducible_map_fractionRing`). This is the honest content of "stating the bridge":
  the direct Eisenstein route and CC-15's fraction-field route are the SAME theorem read in
  opposite directions at this key, and either free the other.
* `s2KeyPoly_key_irreducible` restates the conclusion at the abstract-shaped key field
  (`(s2Frame h2 hq).key`, via `key_eq`), and spells it at the literal polynomial `x² − 2`.

**What is NOT claimed**: irreducibility of RP-12's degree-four lift `Φ′² + 4x` or of the
tower's own `composedKey`. Their Newton polygon has a single segment of slope `−1/2` with
`gcd(4, 2) = 2`, so plain Eisenstein (at any single prime, including a shifted variable) does
not decide it — deciding it needs exactly the residual-polynomial machinery (FGMN Lemma
1.8/Theorem 5.7's substance) that C78adj's own docstring already flags as open ("left as
named open work, NOT claimed there" for the closely related `g₄`). No new attempt is made
here; this is honestly out of scope for a 60-minute node.

## NODE KP-6 — the carried key `keyAt 1 = Φ′` is ALREADY closed elsewhere; the genuinely new
content is the tower's OWN `keyAt 2 = composedKey`

`carried_key_is_key`/`carried_key_residual`, AT THE LANDED `r = 1` ANCHORING (`K.keyAt 1 =
Φ′`), are already fully discharged in the earlier corpus: `s2KeyPoly_key : S2KeyPoly h2 hq Φ′`
(C130kp1) and `s2NormRes_key : s2NormRes h2 hq Φ′ = 1` (C130rp8) — nothing to re-prove.

The row's genuinely open question is the tower's OWN `KeyChain.keyAt 2 = composedKey (s2Tower
h2 hq)` (C78adj's `composedKey_s2Tower`): `Φ₂ = Φ′² − C(4w)·X` for the noncanonical `resLift`
UNIT `w = entryW h2 hq` (residue `1`, but not literally `1`) — a genuine generalization of
RP-11/RP-12's fixed witness `Φ′² + 4x` (built at the literal scalar `4`, i.e. `w = 1`) to the
tower's own unit. **Computed here**: the SAME `S2ExactGrade`/`s2GradedRes` machinery that
built RP-12's witness runs verbatim once `4` is replaced by `4w` (only the input `addVal (4w)
= 2` changes, already landed as C78adj's `addVal_entryW_four`) — the private `…cX` lemma bank
below re-derives the grade-`10` tie for `C(c)·X` at ANY nonzero `c` of valuation `2`, not just
`c = 4`.  The residual scalar is then *forced* to be `1` regardless of the specific unit `w`,
by the SAME two-element collapse (`s2Fld₂_card`) that RP-11 already uses generically — no
recomputation of the actual `twistRead` value of `4w` is needed:

* ★ `s2NormRes_composedKey` — `s2NormRes h2 hq (composedKey (s2Tower h2 hq)) = X + 1`: the
  **carried_key_residual GENRE**, realized at the literal tower key `keyAt 2`. (NOT the
  abstract field's literal conclusion `= 1` — that conclusion belongs to `keyAt 1 = Φ′`, per
  the `r = 1` anchoring; `X + 1` is the same "own recipe residual" genre RP-12's witness
  already exhibits, now proved for the tower's actual unit `w` rather than the fixed
  numeral.)
* ★★ `s2KeyPoly_composedKey` — `S2KeyPoly h2 hq (composedKey (s2Tower h2 hq))`: **YES, the
  tower's own composed key IS an `S2KeyPoly`** — the **carried_key_is_key GENRE** at
  `keyAt 2`. Assembled from KP-4's `s2_key_criterion` (monic: C47's `composedKey_monic`;
  degree `4 = 2·1·deg Φ′`: C78adj's `composedKey_s2Tower_natDegree`; irreducible residual of
  degree `1` with nonzero constant term: the two facts above).

## What this node does NOT claim (honesty scope)

* No literal instance of the ABSTRACT `FGMNSourceLaws.key_irreducible` field for arbitrary
  key polynomials (KP-5's row, in full) — only the landed key `Φ′` is shown irreducible.
* No irreducibility of `composedKey`/the degree-four lift (KP-5's scope note above).
* No literal `FGMNSourceData`/`FGMNSourceLaws` INSTANCE at `r = 2` reading `K.keyAt 2 =
  composedKey` as ITS OWN carried key (that would need a genuinely deeper `μ₃`-level engine,
  not landed); `s2NormRes_composedKey`/`s2KeyPoly_composedKey` are honest ANALOGOUS statements
  at the landed `μ₂` engine, computed at the literal tower polynomial, exactly the "same
  quantifier/binder genre, realized honestly at the numerals the landed engine actually
  supports" pattern RP-11/KP-3/KP-4 already established.
* No `initial_iff_residual` (KP-7..KP-9), no FD-0 assembly.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2Key_eisenstein_irreducible`, `s2Key_irreducible_map_fractionRing`, the `…cX` generalization
bank, `s2NormRes_composedKey`, `s2KeyPoly_composedKey`.

**DEPENDS.** C130kp3 (`S2KeyPoly`, `s2_key_criterion`, KP-0..KP-4 predicates) · C130lb
(`irreducible_of_fraction_map_irreducible`) · C78adj (`entryW`, `isUnit_entryW`,
`addVal_entryW_four`, `entryW_mul_four_ne_zero`, `composedKey_s2Tower`,
`composedKey_s2Tower_natDegree`) · C130rp11 (`s2_normalized_recipe`, `s2_X_add_one_irreducible`)
· C130rp8 (`s2GradedRes_coeff_zero_ne_zero_of_exact`, `s2NormRes_key`) · C130rp2
(`tooth_char_two`) · C47 (`composedKey_monic`) · C80 (`s2Tower`) · C35b/C97 (`key_eq`,
`s2Key_monic`, `s2Key_natDegree`, `s2Key_deg`, `s2Key_coeff0`, `s2Key_coeff1`) · mathlib
(`Polynomial.irreducible_of_eisenstein_criterion`,
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`,
`IsDiscreteValuationRing.irreducible_iff_uniformizer`, `IsLocalRing.mem_maximalIdeal`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130kp5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp4 Uniformity.Density.Tower.C130rp6
open Uniformity.Density.Tower.C130rp8 Uniformity.Density.Tower.C130rp11
open Uniformity.Density.Tower.C130kp0 Uniformity.Density.Tower.C130kp1
open Uniformity.Density.Tower.C130kp3 Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C78adj Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — private copies (the private-copy pattern) -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-! ## Part 1 — ★ NODE KP-5: `Φ′` is irreducible in `Polynomial O`, via Eisenstein directly -/

omit [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
include h2 in
/-- helper: `4 ∤ 2` in `O` — if it did, cancelling the nonzero `2` would make `2` a unit. -/
private theorem not_four_dvd_two : ¬ ((4 : O) ∣ (2 : O)) := by
  rintro ⟨k, hk⟩
  have hk' : (2 : O) * 1 = 2 * (2 * k) := by
    rw [mul_one, show (2 : O) * (2 * k) = 4 * k by ring]
    exact hk
  have h1 : (1 : O) = 2 * k := mul_left_cancel₀ h2.ne_zero hk'
  exact h2.not_isUnit (IsUnit.of_mul_eq_one k h1.symm)

include h2 in
/-- ★ **NODE KP-5 — the landed key `Φ′ = x² − 2` is irreducible in `Polynomial O`**, directly
via mathlib's classical Eisenstein criterion at the maximal ideal — no fraction field, no
Gauss transport needed for this key. -/
theorem s2Key_eisenstein_irreducible : Irreducible (s2Key O) := by
  have hP : (IsLocalRing.maximalIdeal O).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal O).isPrime
  have hspan : IsLocalRing.maximalIdeal O = Ideal.span {(2 : O)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (2 : O)).mp h2
  have hmem2 : (2 : O) ∈ IsLocalRing.maximalIdeal O := h2.not_isUnit
  refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ s2Key_monic.isPrimitive
  · -- leading coefficient `1 ∉ P`
    rw [s2Key_monic]
    intro h1
    exact (h1 : (1 : O) ∈ nonunits O) isUnit_one
  · -- every below-degree coefficient is in `P`
    intro n hn
    rw [s2Key_deg] at hn
    have hn2 : n < 2 := by exact_mod_cast hn
    interval_cases n
    · rw [s2Key_coeff0]
      exact (IsLocalRing.maximalIdeal O).neg_mem hmem2
    · rw [s2Key_coeff1]
      exact Ideal.zero_mem _
  · -- `0 < degree`
    rw [s2Key_deg]
    decide
  · -- the constant term is NOT in `P²`
    rw [s2Key_coeff0, hspan, Ideal.span_singleton_pow,
      show (2 : O) ^ 2 = 4 by norm_num, Ideal.mem_span_singleton, dvd_neg]
    exact not_four_dvd_two h2

include h2 in
/-- `Φ′`'s irreducibility, spelled at the concrete polynomial `x² − 2` (C97's `s2Key`, matching
`s2KeyPoly_lift_spelled`'s style). -/
theorem s2Key_irreducible_spelled :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : O)) :=
  s2Key_eisenstein_irreducible h2

/-- `Φ′`'s irreducibility at the abstract-shaped key field `(s2Frame h2 hq).key`. -/
theorem s2Key_irreducible_at_frame :
    Irreducible ((s2Frame h2 hq).key : Polynomial O) := by
  rw [key_eq h2 hq]
  exact s2Key_eisenstein_irreducible h2

include h2 in
/-- ★ **the bridge, stated explicitly**: CC-15's executed Gauss leg
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, C130lb) is an IFF; read
FORWARD at `Φ′` (which is monic), the `O[x]`-irreducibility just proved upgrades to the
fraction-field statement — exactly the hypothesis a faithful realization of published Lemma
1.8 would need to supply for this key, for ANY fraction field `Kv` of `O`. -/
theorem s2Key_irreducible_map_fractionRing
    {Kv : Type} [Field Kv] [Algebra O Kv] [IsFractionRing O Kv] :
    Irreducible ((s2Key O).map (algebraMap O Kv)) :=
  (s2Key_monic.irreducible_iff_irreducible_map_fraction_map (K := Kv)).mp
    (s2Key_eisenstein_irreducible h2)

/-! ## Part 2 — ★ NODE KP-6: the tower's own `composedKey` under the μ₂-predicates

The generalization of RP-11's grade-`10` tie tooth bank (`C130rp2`'s `C4X` family) from the
literal scalar `4` to any nonzero `c` of valuation exactly `2` — the input the tower's own
composed key actually needs (`c = 4w`, `w` a unit). -/

/-- generalized `sh_C4X`: the stage height of `C c · X` is `5`, for ANY `c ≠ 0` with
`addVal O c = 2` (not just the literal `c = 4`). -/
private theorem sh_cX {c : O} (hc0 : c ≠ 0) (hc : addVal O c = (2 : ℕ∞)) :
    (s2Frame h2 hq).stageHeight (Polynomial.C c * Polynomial.X) = ((5 : ℕ) : ℕ∞) := by
  rw [C130nv3.s2_stageHeight_linear h2 hq (le_of_eq (Polynomial.natDegree_C_mul_X c hc0))]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    mul_zero, mul_one, AddValuation.map_zero]
  rw [C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), min_eq_right le_top, hc, nsmul_eq_mul]
  norm_cast

/-- generalized `dev_C4X_zero`: slot `0` of the `Φ′`-development of `C c · X` is itself
(degree reasons alone; no hypothesis on `c` needed). -/
private theorem dev_cX_zero {c : O} :
    dev (s2Frame h2 hq).key (Polynomial.C c * Polynomial.X) 0
      = Polynomial.C c * Polynomial.X := by
  rw [dev_zero_pin]
  exact (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [key_eq h2 hq, s2Key_deg]
        exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le c) (by norm_num))

/-- generalized `dvHgt_C4X_zero`. -/
private theorem dvHgt_cX_zero {c : O} (hc0 : c ≠ 0) (hc : addVal O c = (2 : ℕ∞)) :
    dvHgt (s2Frame h2 hq) (Polynomial.C c * Polynomial.X) 0 = ((5 : ℕ) : ℕ∞) := by
  rw [dvHgt, dev_cX_zero h2 hq]
  exact sh_cX h2 hq hc0 hc

/-- generalized `dvHgt_C4X_one`: the development of `C c · X` stops at slot `0` (degree
reasons alone). -/
private theorem dvHgt_cX_one {c : O} :
    dvHgt (s2Frame h2 hq) (Polynomial.C c * Polynomial.X) 1 = ⊤ := by
  have hdev : dev (s2Frame h2 hq).key (Polynomial.C c * Polynomial.X) 1 = 0 := by
    change ((Polynomial.C c * Polynomial.X) /ₘ (s2Frame h2 hq).key) %ₘ (s2Frame h2 hq).key = 0
    rw [(Polynomial.divByMonic_eq_zero_iff (s2Frame h2 hq).hmonic).mpr
        (by rw [key_eq h2 hq, s2Key_deg]
            exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le c) (by norm_num)),
      Polynomial.zero_modByMonic]
  rw [dvHgt, hdev]
  exact (s2Frame h2 hq).stageHeight_zero

/-- generalized `dvSupp_C4X`: `h₂(C c · X) = 10` for ANY nonzero `c` of valuation `2`. -/
private theorem dvSupp_cX {c : O} (hc0 : c ≠ 0) (hc : addVal O c = (2 : ℕ∞)) :
    dvSupp (s2Frame h2 hq) (Polynomial.C c * Polynomial.X) 5 2 = ((10 : ℕ) : ℕ∞) := by
  simp only [dvSupp, Polynomial.natDegree_C_mul_X c hc0,
    show Finset.range (1 + 1) = {0, 1} from rfl, Finset.inf_insert, Finset.inf_singleton]
  rw [dvHgt_cX_zero h2 hq hc0 hc, dvHgt_cX_one h2 hq,
    C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add, min_eq_left le_top, weight_read]

/-- generalized `tooth_C4X_grade`. -/
private theorem exactGrade_cX {c : O} (hc0 : c ≠ 0) (hc : addVal O c = (2 : ℕ∞)) :
    S2ExactGrade h2 hq 10 (Polynomial.C c * Polynomial.X) :=
  (S2ExactGrade_iff_dvSupp h2 hq).mpr (dvSupp_cX h2 hq hc0 hc)

/-- private copy of C.80's `eq_one_of_card_two` at `fld 2` (the corpus's established
private-copy pattern). -/
private theorem s2Fld2_eq_one_of_ne_zero {x : (s2DepthTwo h2 hq).fld 2} (hx : x ≠ 0) :
    x = 1 := by
  haveI : Finite ((s2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((s2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  haveI : Subsingleton ((s2DepthTwo h2 hq).fld 2)ˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hx.isUnit.unit = 1 := Subsingleton.elim _ _
  calc x = ((hx.isUnit.unit : ((s2DepthTwo h2 hq).fld 2)ˣ) : (s2DepthTwo h2 hq).fld 2) :=
        (hx.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- every element of `K₂` is its own negative (private copy of RP-11's char-2 identity). -/
private theorem s2Fld2_neg_eq_self (x : (s2DepthTwo h2 hq).fld 2) : -x = x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [s2Fld2_eq_one_of_ne_zero h2 hq hx]
    have h := tooth_char_two h2 hq
    calc (-1 : (s2DepthTwo h2 hq).fld 2) = -1 + (1 + 1) := by rw [h, add_zero]
      _ = 1 := by ring

/-- the char-2 negation identity, polynomial form. -/
private theorem s2Fld2_poly_neg_eq_self (p : Polynomial ((s2DepthTwo h2 hq).fld 2)) :
    -p = p := by
  ext n
  rw [Polynomial.coeff_neg]
  exact s2Fld2_neg_eq_self h2 hq _

/-- the coefficient `c := 4w`'s own graded residual, at grade `10`, has constant term `1` —
NOT recomputed from the actual `twistRead` value of `4w`, but forced by the two-element
collapse of `K₂` once nonvanishing is known (RP-8's degree law). -/
private theorem cX_gradedRes_coeff0_eq_one {c : O} (hc0 : c ≠ 0) (hc : addVal O c = (2 : ℕ∞)) :
    (s2GradedRes h2 hq 10 (Polynomial.C c * Polynomial.X)).coeff 0 = 1 :=
  s2Fld2_eq_one_of_ne_zero h2 hq
    (s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq (exactGrade_cX h2 hq hc0 hc)
      (by rw [Polynomial.natDegree_C_mul_X c hc0]; norm_num))

/-- the S2-realized recipe (RP-11's `s2_normalized_recipe`), applied at `khat := C c · X` for
ANY nonzero `c` of valuation `2`, then the residual collapsed to the ONLY possible value: the
generalization of RP-12's fixed witness `Φ′² + 4x`'s residual to `Φ′² − C c·X` for arbitrary
such `c`. -/
private theorem s2NormRes_key_sq_sub_cX {c : O} (hc0 : c ≠ 0) (hc : addVal O c = (2 : ℕ∞)) :
    s2NormRes h2 hq
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          - Polynomial.C c * Polynomial.X)
      = Polynomial.X + 1 := by
  have hrecipe := s2_normalized_recipe h2 hq (exactGrade_cX h2 hq hc0 hc)
    (by rw [Polynomial.natDegree_C_mul_X c hc0]; norm_num)
  rw [hrecipe, cX_gradedRes_coeff0_eq_one h2 hq hc0 hc, map_one, sub_eq_add_neg,
    s2Fld2_poly_neg_eq_self h2 hq 1]

/-- the tower's own composed key, rewritten in the `Φ′ * Φ′ − C c · X` shape RP-11's recipe
consumes (C78adj's `composedKey_s2Tower`, bridged through `key_eq`). -/
private theorem composedKey_eq_key_sq_sub_cX :
    composedKey (s2Tower h2 hq)
      = ((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        - Polynomial.C (entryW h2 hq * 4) * Polynomial.X := by
  rw [composedKey_s2Tower h2 hq, key_eq h2 hq, pow_two]

/-- ★ **NODE KP-6, `carried_key_residual` GENRE at `keyAt 2 = composedKey`**: the tower's own
composed key has normalized residual `X + 1` — the SAME residual RP-12's fixed witness
exhibits, now proved at the tower's actual (noncanonical, unit) coefficient `4w` rather than
the literal numeral `4`. -/
theorem s2NormRes_composedKey :
    s2NormRes h2 hq (composedKey (s2Tower h2 hq)) = Polynomial.X + 1 := by
  rw [composedKey_eq_key_sq_sub_cX h2 hq]
  exact s2NormRes_key_sq_sub_cX h2 hq (entryW_mul_four_ne_zero h2 hq) (addVal_entryW_four h2 hq)

/-- ★★ **NODE KP-6, `carried_key_is_key` GENRE at `keyAt 2 = composedKey`**: the tower's own
composed key IS an `S2KeyPoly` — assembled via KP-4's `s2_key_criterion` from C47's monicity,
C78adj's degree-four numeral, and the residual `X + 1` just computed (irreducible, degree
`1`, nonzero constant term). -/
theorem s2KeyPoly_composedKey :
    S2KeyPoly h2 hq (composedKey (s2Tower h2 hq)) := by
  have hres := s2NormRes_composedKey h2 hq
  refine s2_key_criterion h2 hq _ (composedKey_monic (s2Tower h2 hq)) ?_ ?_ ?_ ?_
  · rw [composedKey_s2Tower_natDegree h2 hq, key_natDegree_two h2 hq]
  · rw [hres]
    exact s2_X_add_one_irreducible h2 hq
  · rw [hres, show (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = Polynomial.C 1 from
        (map_one _).symm]
    exact Polynomial.natDegree_X_add_C 1
  · rw [hres, Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
      zero_add]
    exact one_ne_zero

end S2

end Uniformity.Density.Tower.C130kp5

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130kp5.s2Key_eisenstein_irreducible
#print axioms Uniformity.Density.Tower.C130kp5.s2Key_irreducible_spelled
#print axioms Uniformity.Density.Tower.C130kp5.s2Key_irreducible_at_frame
#print axioms Uniformity.Density.Tower.C130kp5.s2Key_irreducible_map_fractionRing
#print axioms Uniformity.Density.Tower.C130kp5.s2NormRes_composedKey
#print axioms Uniformity.Density.Tower.C130kp5.s2KeyPoly_composedKey

end AxCheck
