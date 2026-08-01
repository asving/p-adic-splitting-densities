/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps

/-!
# Scaffold/DictIII/Devid — DEVID's graded interface (BP_III §1.5)

E-phase transcription of `lean/blueprints/BP_III.md` §1.5.  This file currently
holds unit III-G15a: the `ValGr` structure (Gr/zero/add/mul/grade/inF + laws
inF_zero, grade_inF, g1, g2, mul_zero, dom — REV2 finding 7), the `KPaBlock`
def, and the `minDev` def — FIELDS ONLY, transcribed VERBATIM.  Source of
record: GD23 §1.3 (g1)(g2).  Unit III-G18 (`bridge_equivDiv`, Lemma BRIDGE)
is appended below; its §1.5 line is ELIDED (`theorem bridge_equivDiv …`), so
its statement is completed from the source of record (GD23 brief §5) — see
its docstring for the completion ledger.

Forward dependency: `minDev`'s display consumes `devCoeff` (unit III-G1,
`devCoeff` def via `Polynomial.modByMonic`/`divByMonic`, not yet in the
corpus at transcription time); it is provided here per the III-G1 row's spec
so §1.5's displays compile.  When III-G1 lands in its own module this def is
the one to dedupe against.

Unit III-G14 (`devid_ge`, GD23 §4 proof "≥") also lives here: the ≥ half of
Theorem DEVID from ultrametric + multiplicativity alone (NO `ValGr`, no KPa).
The §1.5 display gives `devid_ge` by signature sketch only ("the ≥ half
(ultrametric only; no ValGr)"); its statement below renders that sketch with
the displayed `devid`'s binder frame minus the graded data `G`/`hkpa`, keeping
as explicit hypotheses exactly the two `KPaBlock` rows the development
identity needs (`monic`, `positiveDegree`).  Second forward dependency, same
convention as `devCoeff` above: the III-G14 dep column names III-H8's
`IsPolyValuation`, which is in no landed module (Hyps.lean's III-H8 block has
only `MacLaneV1Pkg`/`KeyPkg`); it is provided here as the un-indexed row set
of `MacLaneV1Pkg` (zero/one/mul/add at a fixed level) — dedupe when III-H8's
owner lands it.

Display adjustment (III-G15a): the §1.5 display declares `add mul : Gr → Gr → Gr`
on one field line; in the Lean-4.31 structure-`where` syntax pinned here that
parses as a single field `add` with a BINDER `mul` (exact downstream error:
"Type mismatch: add (inF A) (inF B) has type Gr → Gr but is expected to have
type Gr", with `mul` unknown).  The surviving spelling of the SAME two fields
is one line each (`add : Gr → Gr → Gr` / `mul : Gr → Gr → Gr`); the
propositions are unchanged.  Additionally `devCoeff`/`minDev` carry the
`noncomputable` modifier (forced by `Polynomial.modByMonic`; definition bodies
untouched).  No other token differs from the display.
-/

namespace LeanUrat.Scaffold.DictIII

open Polynomial

/-- Unit III-G1 (forward-provided dependency): the Φ-adic development
    coefficients, `devCoeff Φ B k` = the k-th coefficient `C_k` in
    `B = Σ_k C_k Φ^k` with `deg C_k < deg Φ`, via monic mod/div
    (`Polynomial.modByMonic`/`divByMonic`) — BP_III unit-table row III-G1,
    GD23 §3 DEV-g. -/
noncomputable def devCoeff {K : Type*} [CommRing K] (Φ : Polynomial K) :
    Polynomial K → ℕ → Polynomial K
  | B, 0 => B %ₘ Φ
  | B, k + 1 => devCoeff Φ (B /ₘ Φ) k

/-- The graded interface DEVID actually consumes: initial-form data for w with
    (g1) in(A)+… sum law at the min weight, (g2) in(AB) = in(A)·in(B), domain. An
    instance at order ≤ 1 is built from §1.4's explicit descriptions (unit III-G15b). -/
structure ValGr {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) where
  Gr : Type*
  zero : Gr
  add : Gr → Gr → Gr
  mul : Gr → Gr → Gr
  grade : Gr → WithTop ℤ
  inF : Polynomial K → Gr
  inF_zero : inF 0 = zero
  grade_inF : ∀ A, grade (inF A) = w A
  g1 : ∀ A B, w A = w B → inF (A + B) = add (inF A) (inF B)
  g2 : ∀ A B, inF (A * B) = mul (inF A) (inF B)
  mul_zero : ∀ a, mul a zero = zero ∧ mul zero a = zero
  dom : ∀ a b, mul a b = zero → a = zero ∨ b = zero

/-- Theorem DEVID (GD23 §4): under (V1) + (KPa)'s block, the Φ-development computes
    w from below: w(B) = min_k (w(C_k) + k·w(Φ)). -/
noncomputable def minDev {K : Type*} [CommRing K] (w : Polynomial K → WithTop ℤ)
    (Φ B : Polynomial K) : WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun k =>
    w (devCoeff Φ B k) + (k : ℕ) • w Φ

structure KPaBlock {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (G : ValGr w)
    (Φ : Polynomial K) : Prop where
  monic : Φ.Monic
  positiveDegree : 1 ≤ Φ.natDegree
  primeInitial : ∀ A B, G.mul (G.inF A) (G.inF B) = G.inF Φ →
    G.inF A = G.inF Φ ∨ G.inF B = G.inF Φ
  lowerDegree : ∀ B, B.natDegree < Φ.natDegree →
    B ≠ 0 → G.inF B ≠ G.inF Φ

/-- Helper for unit III-G19: with `Φ` monic of positive degree, every
    development coefficient `devCoeff Φ B k` has `natDegree < Φ.natDegree`
    (each is a `%ₘ Φ` remainder, by the dev recursion). -/
theorem devCoeff_natDegree_lt {K : Type*} [CommRing K] {Φ : Polynomial K}
    (hΦ : Φ.Monic) (hdeg : 1 ≤ Φ.natDegree) (B : Polynomial K) (k : ℕ) :
    (devCoeff Φ B k).natDegree < Φ.natDegree := by
  have hΦ1 : Φ ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hdeg
    exact absurd hdeg (by omega)
  induction k generalizing B with
  | zero => exact Polynomial.natDegree_modByMonic_lt B hΦ hΦ1
  | succ k ih => simpa only [devCoeff] using ih (B /ₘ Φ)

/-- Unit III-G19 — Lemma UNIQ (GD23 §6): two valuations satisfying the same
    dev recursion are equal.  Hypotheses render the brief's display verbatim
    in this module's vocabulary — (u1) `w = v` on nonzero polynomials of
    degree `< deg Φ` and at the key (`hlow`, `hkey`); (u2) both are computed
    by the Φ-development min formula on `K[x]∖{0}` (`hw`, `hv`, via `minDev`).
    The blueprint §1.5 line is elided (`theorem uniq_two_valuations…`); the
    brief's ν live on `K[x]∖{0}`, so the total `WithTop ℤ` carriers here get
    the convention row `hzero : w 0 = v 0` (⊤ = ⊤ for actual valuations). -/
theorem uniq_two_valuations {K : Type*} [CommRing K]
    (w v : Polynomial K → WithTop ℤ) (Φ : Polynomial K)
    (hΦ : Φ.Monic) (hdeg : 1 ≤ Φ.natDegree)
    (hzero : w 0 = v 0)
    (hlow : ∀ B : Polynomial K, B ≠ 0 → B.natDegree < Φ.natDegree → w B = v B)
    (hkey : w Φ = v Φ)
    (hw : ∀ B : Polynomial K, B ≠ 0 → w B = minDev w Φ B)
    (hv : ∀ B : Polynomial K, B ≠ 0 → v B = minDev v Φ B) :
    w = v := by
  funext B
  by_cases hB : B = 0
  · rw [hB]; exact hzero
  · rw [hw B hB, hv B hB]
    unfold minDev
    refine Finset.inf'_congr (by simp) rfl fun k _ => ?_
    have hC : w (devCoeff Φ B k) = v (devCoeff Φ B k) := by
      by_cases h0 : devCoeff Φ B k = 0
      · rw [h0]; exact hzero
      · exact hlow _ h0 (devCoeff_natDegree_lt hΦ hdeg B k)
    rw [hC, hkey]

/-- Unit III-G20 — Theorem TIE (GD23 §6; GD-2(a) second half): two
    level-indexed valuation families over the SAME key chain agree at every
    level, conditional on the `MacLaneV1Pkg` + `KeyPkg` rows at each level
    (unit III-H8) plus the §6 recursion pins rendered as named hypothesis
    rows: base agreement (`hbase` = (P-base)); low-degree coefficient scaling
    by `e i` on each side (`hlowW` = §1.2's slot-0 computation, `hlowV` =
    (T-1)'s rescaling clause); the shared key value `γ i` (`hkeyW`/`hkeyV` =
    (P-key)); and the Φ-development min formula on each side (`hdevW`/`hdevV`
    = UNIQ's (u2), via `minDev`).  `v` is GMN's `v_{j+1}` re-indexed by the
    §1.2 index dictionary, in the SAME ℤ-normalization; the §6 policy pin
    (engine keys ARE the GMN representatives) is the shared `keys` family.
    The blueprint §1.5 line is ELIDED (`theorem tie_w_eq_v …` — "conditional
    on MacLaneV1Pkg + KeyPkg rows at each level"), so — same convention as
    III-G18/G19 above — this statement is completed from the source of record
    (GD23 brief §6 Theorem TIE) per unit-table row III-G20 (stmt + proof from
    UNIQ + rows).  Proof: at each level both sides satisfy UNIQ's (u1)/(u2)
    at `keys n` — induction on the level, then `uniq_two_valuations`. -/
theorem tie_w_eq_v {p : ℕ} [Fact p.Prime]
    (w v : ℕ → Polynomial ℤ_[p] → WithTop ℤ)
    (keys : ℕ → Polynomial ℤ_[p]) (e : ℕ → ℕ) (γ : ℕ → WithTop ℤ)
    (hV1w : MacLaneV1Pkg w keys) (hV1v : MacLaneV1Pkg v keys)
    (hKPw : ∀ i, KeyPkg (w i) (keys i))
    (hKPv : ∀ i, KeyPkg (v i) (keys i))
    (hbase : w 0 = v 0)
    (hlowW : ∀ i (B : Polynomial ℤ_[p]), B ≠ 0 →
      B.natDegree < (keys i).natDegree → w (i + 1) B = e i • w i B)
    (hlowV : ∀ i (B : Polynomial ℤ_[p]), B ≠ 0 →
      B.natDegree < (keys i).natDegree → v (i + 1) B = e i • v i B)
    (hkeyW : ∀ i, w (i + 1) (keys i) = γ i)
    (hkeyV : ∀ i, v (i + 1) (keys i) = γ i)
    (hdevW : ∀ i (B : Polynomial ℤ_[p]), B ≠ 0 →
      w (i + 1) B = minDev (w (i + 1)) (keys i) B)
    (hdevV : ∀ i (B : Polynomial ℤ_[p]), B ≠ 0 →
      v (i + 1) B = minDev (v (i + 1)) (keys i) B) :
    ∀ i, w i = v i := by
  intro i
  induction i with
  | zero => exact hbase
  | succ n ih =>
    refine uniq_two_valuations (w (n + 1)) (v (n + 1)) (keys n)
      (hKPw n).monic (hKPv n).positiveDegree ?_ ?_ ?_ (hdevW n) (hdevV n)
    · rw [hV1w.zero (n + 1), hV1v.zero (n + 1)]
    · intro B hB hdB
      rw [hlowW n B hB hdB, hlowV n B hB hdB, ih]
    · rw [hkeyW n, hkeyV n]

/-! ## Unit III-G14 — `devid_ge` (GD23 §4 proof "≥") -/

/-- (V1) at a single state (the III-G14/`devid` dep column's `IsPolyValuation`,
forward-provided for III-H8): `w` is a polynomial valuation — the un-indexed
row set of `Hyps.lean`'s `MacLaneV1Pkg`: `w 0 = ⊤`, `w 1 = 0`, multiplicative,
ultrametric.  HYPOTHESIS predicate, not an axiom. -/
structure IsPolyValuation {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) : Prop where
  zero : w 0 = ⊤
  one : w 1 = 0
  mul : ∀ A B, w (A * B) = w A + w B
  add : ∀ A B, min (w A) (w B) ≤ w (A + B)

/-- III-G14 support (bounded development identity, auxiliary form): for monic
`Φ` of positive degree over a nontrivial ring, the development recursion
terminates within any `n + 1` slots once `B.natDegree ≤ n`. -/
theorem devCoeff_sum_aux {K : Type*} [CommRing K] [Nontrivial K]
    (Φ : Polynomial K) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) :
    ∀ (n : ℕ) (B : Polynomial K), B.natDegree ≤ n →
      ∑ k ∈ Finset.range (n + 1), devCoeff Φ B k * Φ ^ k = B := by
  intro n
  induction n with
  | zero =>
    intro B hB
    rw [Finset.sum_range_one]
    simp only [devCoeff, pow_zero, mul_one]
    refine (Polynomial.modByMonic_eq_self_iff hΦ).mpr ?_
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    rw [Nat.le_zero.mp hB]
    exact_mod_cast Polynomial.natDegree_pos_iff_degree_pos.mp hd
  | succ n ih =>
    intro B hB
    have hQ : (B /ₘ Φ).natDegree ≤ n := by
      have hdiv := Polynomial.natDegree_divByMonic B hΦ
      omega
    rw [Finset.sum_range_succ']
    have h1 : ∑ k ∈ Finset.range (n + 1), devCoeff Φ B (k + 1) * Φ ^ (k + 1)
        = (∑ k ∈ Finset.range (n + 1), devCoeff Φ (B /ₘ Φ) k * Φ ^ k) * Φ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [devCoeff, pow_succ, mul_assoc]
    rw [h1, ih (B /ₘ Φ) hQ]
    simp only [devCoeff, pow_zero, mul_one]
    calc (B /ₘ Φ) * Φ + B %ₘ Φ = B %ₘ Φ + Φ * (B /ₘ Φ) := by ring
      _ = B := Polynomial.modByMonic_add_div B Φ

/-- III-G14 support — the development identity (GD23 §3 DEV-g, sum form, as
consumed by the §4 "≥" proof): `B = Σ_{k ≤ deg B} C_k Φ^k`. -/
theorem devCoeff_sum {K : Type*} [CommRing K]
    (Φ : Polynomial K) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree)
    (B : Polynomial K) :
    ∑ k ∈ Finset.range (B.natDegree + 1), devCoeff Φ B k * Φ ^ k = B := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  · exact devCoeff_sum_aux Φ hΦ hd B.natDegree B le_rfl

/-- III-G14 support — multiplicativity iterated: `w (Φ^k) = k·(w Φ)`. -/
theorem IsPolyValuation.w_pow {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} (hval : IsPolyValuation w)
    (Φ : Polynomial K) (k : ℕ) : w (Φ ^ k) = k • w Φ := by
  induction k with
  | zero => simpa using hval.one
  | succ k ih => rw [pow_succ, hval.mul, ih, succ_nsmul]

/-- III-G14 support — the ultrametric row over a finite sum: any uniform lower
bound on the summands' values bounds the sum's value (the empty sum lands at
`w 0 = ⊤` via the `zero` row). -/
theorem IsPolyValuation.le_w_sum {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} (hval : IsPolyValuation w)
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial K) (c : WithTop ℤ)
    (h : ∀ k ∈ s, c ≤ w (f k)) : c ≤ w (∑ k ∈ s, f k) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, hval.zero]; exact le_top
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    refine le_trans (le_min (h a (Finset.mem_cons_self a s))
      (ih fun k hk => h k (Finset.mem_cons_of_mem hk))) (hval.add _ _)

/-- Unit III-G14 (`devid_ge`, GD23 §4 proof "≥"): the ≥ half of Theorem DEVID —
ultrametric + multiplicativity only, NO `ValGr`, no KPa: the Φ-development
bounds `w` from below, `min_k (w(C_k) + k·w(Φ)) ≤ w B`.  The `Monic` and
positive-degree hypotheses are the two `KPaBlock` rows the assembled `devid`
(unit III-G17) extracts from `hkpa`. -/
theorem devid_ge {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (hval : IsPolyValuation w)
    (Φ : Polynomial K) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree)
    (B : Polynomial K) :
    minDev w Φ B ≤ w B := by
  calc minDev w Φ B
      ≤ w (∑ k ∈ Finset.range (B.natDegree + 1), devCoeff Φ B k * Φ ^ k) := by
        refine hval.le_w_sum _ _ _ fun k hk => ?_
        rw [hval.mul, hval.w_pow]
        exact Finset.inf'_le _ hk
    _ = w B := by rw [devCoeff_sum Φ hΦ hd B]

/- BLOCKED(III-G21b): no Lean statement exists to prove. The unit's charter
("gd3_min general proof under KeyPkg") presupposes a verbatim `gd3_min`
statement in BP_III §1.5, but the display there (line 477) is ELIDED:

  theorem gd3_min …            -- GD3-MIN: ord_{ψ̂_hom}(in f) = ord_ψ(R_λ f), per level
                               --   under KeyPkg (order ≤ 1 instance outright)

REV-2 finding 1 ("§1 signatures replace central ellipses") did not reach this
row: the statement is delegated to unit III-G21a ("gd3_min statement and
order-≤1 instance", unit-table row 755), which has NOT landed — zero
`gd3_min` hits in LeanUrat/ at this writing.  Proof-side dependency state at
this writing (a concurrent wave is filling this file): `IsPolyValuation` and
`devid_ge` (III-G14) are landed ABOVE; `devid_le` (III-G16) and the
assembled `devid` (III-G17) are not yet present; the order-≤1 `ValGr`
instance (III-G15b) and the RES-1 dictionary (III-G12b/G13a) are in no
landed module.  Formulating the gd3_min statement in this unit is not
sanctioned (contrast III-G9 in GDOrder1.lean, whose brief authorized a
source-of-record rendering): GD3-MIN's two sides — ord_{ψ̂}(·) on the graded
carrier (the `ValGr` interface above has NO order/divisibility operation) and
the level-i residual read R_λ (III-G13a's dictionary, unlanded) — each
require carrier design owned by III-G12b/G13a/G15b/G21a.  NO declaration is
added for III-G21b.  Unblock order: G16/G17 (`devid`) → G12b/G13a/G15b →
G21a statement → THEN this unit ("apply DEVID and the named graded/KPa
rows"). -/

/-! ## Unit III-G18 — `bridge_equivDiv` (Lemma BRIDGE, GD23 §5) -/

/-- III-G18 support — negation invariance from the valuation rows:
`w (-A) = w A` (via `w (-1) = 0`, forced by `w ((-1)·(-1)) = w 1 = 0`). -/
theorem IsPolyValuation.w_neg {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} (hval : IsPolyValuation w)
    (A : Polynomial K) : w (-A) = w A := by
  have h1 : w (-1 : Polynomial K) + w (-1 : Polynomial K) = 0 := by
    rw [← hval.mul, neg_one_mul, neg_neg]; exact hval.one
  have hx : w (-1 : Polynomial K) ≠ ⊤ := by
    intro h; rw [h] at h1; simp at h1
  obtain ⟨x, hxeq⟩ := WithTop.ne_top_iff_exists.mp hx
  rw [← hxeq] at h1
  have hx0 : x = 0 := by
    have hxx : x + x = 0 := by exact_mod_cast h1
    omega
  have hm1 : w (-1 : Polynomial K) = 0 := by rw [← hxeq, hx0]; rfl
  rw [← neg_one_mul, hval.mul, hm1, zero_add]

/-- Unit III-G18 (`bridge_equivDiv`, Lemma BRIDGE — GD23 §5, "equivalence-
divisibility = graded divisibility").  The §1.5 line is ELIDED
(`theorem bridge_equivDiv …    -- Lemma BRIDGE: a |_W b ⟺ in(a) | in(b)`), so
the statement is completed from the source of record, GD23 brief §5.
Completion ledger:
* `a |_W b` (MacLane equivalence-divisibility) = `∃ c, w b < w (b - c * a)` —
  the brief's `∃c : W(b − ca) > W(b)` verbatim;
* `in(a) | in(b) in gr(W)` = `∃ d : G.Gr, G.inF b = G.mul d (G.inF a)` at the
  III-G15a interface (all interface elements model homogeneous elements);
* "W a valuation" = `hval` (this module's `IsPolyValuation`, the III-H8 frame);
* `hfaith` — the graded-piece law of the concrete grading `⊕ P_γ/P_γ⁺`
  (equal-weight initial forms coincide iff the difference sits strictly
  higher), definitional at the concrete instance (III-G15b's world), a NAMED
  hypothesis row at this abstract interface (it is not derivable from the
  III-G15a fields);
* `hlift` — the brief's representative-lift step ("every nonzero homogeneous
  element of gr(W) is in(c) for any representative c"), proved concretely in
  the brief §5, a NAMED row here;
* `hb` — the abstract residue of the brief's "b nonzero" (in the concrete
  grading `in(b) ≠ 0 ⟺ b ≠ 0`); without it the ⟸ direction is false at
  `d = 0`.
Proof = the brief's two ultrametric forcing steps (`w(ca) = w(b)` by
trichotomy) + `(g2)` for ⟹; lift + `(g2)` + `grade_inF` + `hfaith` for ⟸. -/
theorem bridge_equivDiv {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (hval : IsPolyValuation w)
    (G : ValGr w)
    (hfaith : ∀ A B, w A = w B → (G.inF A = G.inF B ↔ w A < w (A - B)))
    (hlift : ∀ d : G.Gr, d ≠ G.zero → ∃ c : Polynomial K, G.inF c = d)
    (a b : Polynomial K) (hb : G.inF b ≠ G.zero) :
    (∃ c : Polynomial K, w b < w (b - c * a)) ↔
      ∃ d : G.Gr, G.inF b = G.mul d (G.inF a) := by
  constructor
  · rintro ⟨c, hc⟩
    -- ultrametric forcing: w (c * a) = w b
    have hforce : w (c * a) = w b := by
      rcases lt_trichotomy (w (c * a)) (w b) with hlt | heq | hgt
      · -- forcing step 1: w(ca) < w(b) contradicts w(b − ca) > w(b)
        exfalso
        have h1 := hval.add b (-(b - c * a))
        have e : b + -(b - c * a) = c * a := by ring
        rw [e, hval.w_neg] at h1
        exact ((lt_min hlt (hlt.trans hc)).trans_le h1).false
      · exact heq
      · -- forcing step 2: w(ca) > w(b) makes w(b) ≥ min > w(b)
        exfalso
        have h1 := hval.add (b - c * a) (c * a)
        have e : (b - c * a) + c * a = b := by ring
        rw [e] at h1
        exact ((lt_min hc hgt).trans_le h1).false
    have hinf : G.inF b = G.inF (c * a) := (hfaith b (c * a) hforce.symm).mpr hc
    exact ⟨G.inF c, by rw [hinf, G.g2]⟩
  · rintro ⟨d, hd⟩
    have hdz : d ≠ G.zero := by
      rintro rfl
      exact hb (hd.trans (G.mul_zero (G.inF a)).2)
    obtain ⟨c, hcd⟩ := hlift d hdz
    have hinf : G.inF b = G.inF (c * a) := by rw [G.g2, hcd]; exact hd
    have hw : w b = w (c * a) := by
      rw [← G.grade_inF b, ← G.grade_inF (c * a), hinf]
    exact ⟨c, (hfaith b (c * a) hw).mp hinf⟩

/-! ## Unit III-G15b — `ValGr` instance at order ≤ 1 (BLOCKED record + D-R3 probe) -/

/- BLOCKED(III-G15b): the order-≤1 `ValGr` instance cannot be transcribed —
NO declaration below claims this unit.  Findings:

1. PROVENANCE: BP_III §1.5 displays no Lean statement for III-G15b; the only
   anchors are the `ValGr` docstring pointer above ("An instance at order ≤ 1
   is built from §1.4's explicit descriptions") and unit-table row 749
   ("package the concrete grading" from III-G8/G9).  The faithful target is a
   term of `ValGr (w1 Φ₀ e h)` at §1.4's order-≤1 valuation, carrier = the
   VAL-g (2)/(3) graded ring (weight-γ pieces free over K₀ = O[x]/(π, Φ₀) on
   lattice monomials π̄^a Φ̄₀^t).
2. HARD BLOCK (supply): `w1` (III-G6) is in no landed module, and its §1.4
   display cannot compile — INDEPENDENTLY of III-G3a's fatal `gaussW` type
   error (GDOrder1.lean's BLOCKED(III-G3a) record): `w1` applies `gaussW` to
   development coefficients over `FractionRing O`, so elaboration must solve
   `IsDiscreteValuationRing (FractionRing O)` — unsynthesizable AND
   unsatisfiable (`FractionRing O` is a field; DVRs are `not_a_field'`).
   Exact error, probed 2026-08-01 against the verbatim §1.4 displays with
   only the recorded modifier cures applied: "failed to synthesize instance
   of type class  IsDiscreteValuationRing (FractionRing O)" at `w1`'s
   `gaussW` token.  Architect consequence: the body-only repair sketched in
   the BLOCKED(III-G3a) record cannot feed `w1` as displayed — the repair
   must also re-seat `gaussW`'s signature (Gauss weight on
   `Polynomial (FractionRing O)` reading O-coefficient valuations) or
   re-route `w1`'s call.
3. SUPPLY STATUS (dep row G15a/G8/G9/G10): G15a landed above; G9 landed as
   GDOrder1.lean's `w0_mul_asK0` (formulated, flagged for review); G8 is
   unlanded; G10 (`w1_mul`) is blocked downstream of the same displays.
   Unblock order: G3a/G6 display repair → G8/G10 → THEN this unit.

D-R3 probe (below, `valGrIdentity`): the `ValGr` rows alone are satisfied by
the IDENTITY instance for EVERY `w` over a domain — the interface does not
enforce gradedness, so the honesty burden D-R3 assigns to III-G15b (the
CONCRETE grading, whose `KPaBlock`/`hfaith` rows are the GD23 §3 KEY-g facts)
is real and remains OPEN.  Note the probe fails III-G18's `hfaith` row for
any nontrivial `w` (`inF = id` separates equal-initial-form pairs), so it
cannot impersonate the graded world downstream. -/

/-- D-R3 probe — NOT unit III-G15b (see the BLOCKED(III-G15b) record): the
identity instance of `ValGr w`, available for every `w` once `K` is a domain
(`Gr := K[x]`, `inF := id`, `grade := w`; `dom` = `K[x]` is a domain).
Compiled evidence that the III-G15a rows underdetermine the carrier, and the
first instantiation exercise of the landed structure.  Discharges nothing. -/
noncomputable def valGrIdentity {K : Type*} [CommRing K] [IsDomain K]
    (w : Polynomial K → WithTop ℤ) : ValGr w where
  Gr := Polynomial K
  zero := 0
  add := (· + ·)
  mul := (· * ·)
  grade := w
  inF := id
  inF_zero := rfl
  grade_inF _ := rfl
  g1 _ _ _ := rfl
  g2 _ _ := rfl
  mul_zero a := ⟨MulZeroClass.mul_zero a, MulZeroClass.zero_mul a⟩
  dom _ _ h := mul_eq_zero.mp h

/-! ## Unit III-G22 — `gd3_full_of_GRB` (Theorem GD3-FULL + OL-B, GD23 §7.3) -/

/-- Unit III-G22 — Theorem GD3-FULL + OL-B (GD23 rev-4 §7.3), general order,
from (GR-B): the STATEMENT FIRES THE (H1) ROW (BP_III unit-table pin; proof
sketch "unfold `GRB`, apply clause").  The §1.5 line is ELIDED after its
binder frame (`theorem gd3_full_of_GRB (h : GRB p F) : …`), so — same
convention as III-G18/G19/G20 above — the conclusion is completed from the
source of record.  Completion ledger:
* the binder frame `(h : GRB p F)` is the display's, verbatim; `p`/`F` get
  this module's explicit binders (Devid.lean declares no section variables);
* the conclusion renders the source theorem's two clauses AS THE LANDED (H1)
  ROW RENDERS THEM (`Hyps.lean`, unit III-H1 `GRB`, orders ≥ 2): clause
  (full) "R^nrm = R^gr(in f) = c·R_λ(f)" ↦ the `residualNormalForm` body (a
  reader exists whose every returned side reads the residual degree off its
  ℓ); clause (OL-B) "a bijection of K_i per slot" ↦ the `slotBijection` body
  (the slot self-map on `Fin (D.residualDegree i + 1)` is bijective);
* the properness proviso is (GR-B)-side (a clause OF the hypothesis row, per
  its §7.2 display), not a GD3-FULL conclusion — it is NOT restated here;
* the dep-column `gd3_min` (III-G21) is NOT consumed: the source proof is
  "re-readings of (2′) + the structure clause … the statement now carries
  exactly what (GR-B) asserts" (§7.3, REV 2), and `gd3_min` is unlanded
  (III-G21b BLOCKED above) — when III-G21a lands a graded-ord carrier, any
  refit is that owner's dedupe question.
At orders ≥ 2 the content sits entirely inside (GR-B): HYPOTHESIS-priced,
exactly as the brief prices it. -/
theorem gd3_full_of_GRB {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Finite F] (h : GRB p F) :
    ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F} {D : GMNData f c} (i : ℕ),
      2 ≤ i →
      (∃ R : GMNReader f c D, ∀ S, R.side i = some S →
        D.residualDegree i = S.ℓ) ∧
      Function.Bijective (fun j : Fin (D.residualDegree i + 1) => j) := by
  intro f c D i hi
  exact ⟨h.residualNormalForm i hi, h.slotBijection i hi⟩

end LeanUrat.Scaffold.DictIII
