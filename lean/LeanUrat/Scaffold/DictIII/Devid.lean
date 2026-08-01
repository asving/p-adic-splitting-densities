/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.Moves.Defs

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

Unit III-G16 (`devid_le`, appended below): the ≤ half of `devid` — statement
transcribed with the hypothesis list of §1.5's `devid` display (the blueprint
elides the halves' own displays: `theorem devid_le …`), conclusion its ≤ half.
STATUS: **REFUTED as stated** — see `G16Refutation.devid_le_refuted`, a
compiled countermodel; the statement stands as an honest sorry pending
statement adjudication.  The countermodel instantiates the D-R3 probe
`valGrIdentity` at K = 𝔽₂, w = the (X+1)-adic order, Φ = X — sharpening the
probe's record: the identity instance CAN impersonate the graded world for
III-G16's exact hypothesis set (`KPaBlock` holds at a non-key Φ), because 𝔽₂
has no unit but 1.  Consumes the III-G14 wave's `IsPolyValuation`.
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

/-! ## Unit III-G16 — `devid_le` (GD23 §4 proof "≤"): REFUTED AS STATED

The blueprint elides the display (`theorem devid_le …  -- the ≤ half (the ψ̂ |
in(C_m) contradiction)`); the statement below renders the ≤ half of the
VERBATIM `devid` display (§1.5 lines 465–469) with `devid`'s exact binder
frame — the only completion consistent with the landed `devid_ge`
(`minDev ≤ w B` being the "≥"/ultrametric half).

It is FALSE over the landed III-G15a interface.  `G16Refutation` below
compiles the countermodel: K = 𝔽₂ (= `ZMod 2`), w = the (X+1)-adic order (a
genuine polynomial valuation, `ipvCM`), G = the D-R3 identity probe
`valGrIdentity wCM`, Φ = X, B = X + 1.  Every hypothesis holds — in
particular `KPaBlock` (`kpaCM`): `primeInitial` because the only
factorizations of the irreducible monic X in 𝔽₂[x] are 1·X and X·1 (𝔽₂ has
no unit but 1), `lowerDegree` by degree alone.  Yet w(X+1) = 1 while
minDev w X (X+1) = 0 (the k = 0 slot: (X+1) %ₘ X = 1 and w(1) = 0).

Root cause: `ValGr.g1` is stated WITHOUT a no-cancellation guard (e.g.
`w (A + B) = w A`) and without a graded-piece-indexed initial form, so the
rows never force `inF` to identify polynomials agreeing to higher w-order —
`inF := id` satisfies g1 unconditionally.  GD23 §4's "≤" proof consumes
exactly the cancellation law (Σ_{k∈S} in(C_k)·in(Φ)^k = 0 in gr_{u₀} when
w(B) exceeds the min) that g1 cannot express; note the INTENDED gr(w)
instance conversely FAILS g1 as displayed in the cancellation case (LHS a
nonzero higher-grade initial form, RHS the grade-v sum = the zero of gr_v),
so III-G15b will hit the same seam from the other side.  In the true gr(wCM)
the key test fails here — in(X) = in(1) since w(X − 1) = 1 > 0 = w(X), so
genuine `lowerDegree` is violated at B = 1 — but the abstract rows cannot
see it.  The fix requires a STATEMENT change on III-G15a's landed `ValGr`
(cancellation-guarded g1 + a zero-detection law, or a graded-sum law) —
outside this unit's authority (statement fence); adjudication queued.  The
≤ half stands below as an honest sorry so the unit's target is on record. -/

/-- Unit III-G16 (`devid_le`, GD23 §4 proof "≤"): the ≤ half of Theorem
DEVID — under (V1) + (KPa)'s block, the development min bounds `w B` from
above.  **REFUTED AS STATED**: `G16Refutation.devid_le_refuted` compiles a
countermodel to this exact statement (see the section header).  DO NOT
consume (III-G17 assembly: do not wire until the interface adjudication
lands); the `sorry` is the honest record of the unit's target. -/
theorem devid_le {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (hval : IsPolyValuation w)
    (G : ValGr w) (Φ : Polynomial K) (hkpa : KPaBlock w G Φ)
    (B : Polynomial K) :
    w B ≤ minDev w Φ B := by
  -- BLOCKED(III-G16): statement FALSE over the landed III-G15a interface —
  -- compiled countermodel `G16Refutation.devid_le_refuted` below (identity
  -- ValGr over 𝔽₂ satisfies KPaBlock at the non-key Φ = X for the (X+1)-adic
  -- valuation; w(X+1) = 1 > 0 = minDev).  ValGr.g1 lacks the cancellation
  -- law GD23 §4 "≤" consumes; fix = statement adjudication on III-G15a.
  sorry

namespace G16Refutation

open scoped Classical in
/-- III-G16 refutation carrier — the (X+1)-adic order on 𝔽₂[x] (order of
vanishing at the point 1): a GENUINE polynomial valuation (`ipvCM`), of Gauss
type, for which X is NOT a key polynomial (in gr(wCM), in(X) = in(1)). -/
noncomputable def wCM (B : Polynomial (ZMod 2)) : WithTop ℤ :=
  if B = 0 then ⊤ else ((Polynomial.rootMultiplicity 1 B : ℤ) : WithTop ℤ)

theorem wCM_zero : wCM 0 = ⊤ := if_pos rfl

theorem wCM_of_ne {B : Polynomial (ZMod 2)} (hB : B ≠ 0) :
    wCM B = ((Polynomial.rootMultiplicity 1 B : ℤ) : WithTop ℤ) := if_neg hB

theorem wCM_one : wCM 1 = 0 := by
  rw [wCM_of_ne one_ne_zero,
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])]
  rfl

theorem wCM_X : wCM X = 0 := by
  rw [wCM_of_ne Polynomial.X_ne_zero,
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])]
  rfl

/-- Multiplicativity of the (X+1)-adic order (root multiplicities add). -/
theorem wCM_mul (A B : Polynomial (ZMod 2)) : wCM (A * B) = wCM A + wCM B := by
  by_cases hA : A = 0
  · rw [hA, zero_mul, wCM_zero, top_add]
  by_cases hB : B = 0
  · rw [hB, mul_zero, wCM_zero, add_top]
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  rw [wCM_of_ne hAB, Polynomial.rootMultiplicity_mul hAB,
    wCM_of_ne hA, wCM_of_ne hB]
  push_cast
  rfl

/-- Ultrametric row for the (X+1)-adic order (shared `(X-1)^n` divisor). -/
theorem wCM_add (A B : Polynomial (ZMod 2)) :
    min (wCM A) (wCM B) ≤ wCM (A + B) := by
  by_cases hA : A = 0
  · rw [hA, zero_add, wCM_zero]
    exact min_le_right _ _
  by_cases hB : B = 0
  · rw [hB, add_zero, wCM_zero]
    exact min_le_left _ _
  by_cases hAB : A + B = 0
  · rw [hAB, wCM_zero]
    exact le_top
  have hle : min (Polynomial.rootMultiplicity 1 A) (Polynomial.rootMultiplicity 1 B)
      ≤ Polynomial.rootMultiplicity 1 (A + B) :=
    (Polynomial.le_rootMultiplicity_iff hAB).mpr
      (dvd_add
        ((pow_dvd_pow _ (min_le_left _ _)).trans (Polynomial.pow_rootMultiplicity_dvd A 1))
        ((pow_dvd_pow _ (min_le_right _ _)).trans (Polynomial.pow_rootMultiplicity_dvd B 1)))
  rw [wCM_of_ne hA, wCM_of_ne hB, wCM_of_ne hAB]
  exact_mod_cast hle

/-- The refutation valuation is a genuine `IsPolyValuation`. -/
theorem ipvCM : IsPolyValuation wCM :=
  ⟨wCM_zero, wCM_one, wCM_mul, wCM_add⟩

/-- 𝔽₂ paucity of units: the only unit of `ZMod 2` is 1. -/
theorem eq_one_of_isUnit_K2 {r : ZMod 2} (h : IsUnit r) : r = 1 := by
  have h2 : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  exact h2 r h.ne_zero

/-- III-G16 refutation: `KPaBlock` HOLDS for the D-R3 identity probe at the
NON-key Φ = X over 𝔽₂ — the abstract rows cannot see that the genuine graded
key test fails (in gr(wCM), in(X) = in(1), so real `lowerDegree` dies at
B = 1). -/
theorem kpaCM : KPaBlock wCM (valGrIdentity wCM) X where
  monic := Polynomial.monic_X
  positiveDegree := by simp
  primeInitial := by
    intro A B h
    have h' : A * B = X := h
    rcases (Polynomial.irreducible_X (R := ZMod 2)).isUnit_or_isUnit h'.symm with hu | hu
    · right
      rcases Polynomial.isUnit_iff.mp hu with ⟨r, hr, hCA⟩
      have hA1 : A = 1 := by rw [← hCA, eq_one_of_isUnit_K2 hr, Polynomial.C_1]
      show B = X
      rw [← h', hA1, one_mul]
    · left
      rcases Polynomial.isUnit_iff.mp hu with ⟨r, hr, hCB⟩
      have hB1 : B = 1 := by rw [← hCB, eq_one_of_isUnit_K2 hr, Polynomial.C_1]
      show A = X
      rw [← h', hB1, mul_one]
  lowerDegree := by
    intro B hdeg hB0 hBX
    have hBX' : B = X := hBX
    rw [hBX', Polynomial.natDegree_X] at hdeg
    exact absurd hdeg (by omega)

/-- Slot-0 development coefficient of X + 1 in Φ = X: the remainder is 1. -/
theorem modX : (X + 1 : Polynomial (ZMod 2)) %ₘ X = 1 :=
  (Polynomial.div_modByMonic_unique 1 1 Polynomial.monic_X
    ⟨by ring, by rw [Polynomial.degree_one, Polynomial.degree_X]; decide⟩).2

/-- w(X + 1) = 1: over 𝔽₂, X + 1 = X − C 1, of root multiplicity 1 at 1. -/
theorem wCM_X_add_one : wCM (X + 1) = 1 := by
  have hne : (X + 1 : Polynomial (ZMod 2)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun q : Polynomial (ZMod 2) => q.coeff 1) h
    simp [Polynomial.coeff_one] at h1
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have h2 : (X - Polynomial.C 1 : Polynomial (ZMod 2)) = X + 1 := by
    rw [sub_eq_add_neg, ← Polynomial.C_neg, hneg, Polynomial.C_1]
  rw [wCM_of_ne hne, ← h2, Polynomial.rootMultiplicity_X_sub_C_self]
  rfl

/-- THE COMPILED III-G16 COUNTERMODEL: all of `devid_le`'s hypotheses hold,
its conclusion fails.  K = 𝔽₂, w = (X+1)-adic order, G = identity probe,
Φ = X, B = X + 1: then w B = 1 but minDev w Φ B ≤ 0 (slot k = 0). -/
theorem devid_le_refuted :
    ∃ w : Polynomial (ZMod 2) → WithTop ℤ, IsPolyValuation w ∧
      ∃ G : ValGr.{0, 0} w, ∃ Φ : Polynomial (ZMod 2), KPaBlock w G Φ ∧
        ∃ B : Polynomial (ZMod 2), ¬ w B ≤ minDev w Φ B := by
  refine ⟨wCM, ipvCM, valGrIdentity wCM, X, kpaCM, X + 1, fun hle => ?_⟩
  have hterm : wCM (devCoeff X (X + 1 : Polynomial (ZMod 2)) 0)
      + (0 : ℕ) • wCM X = 0 := by
    have hdev : devCoeff (X : Polynomial (ZMod 2)) (X + 1) 0 = (X + 1) %ₘ X := rfl
    rw [hdev, modX, wCM_one, zero_nsmul, add_zero]
  have hmin : minDev wCM X (X + 1 : Polynomial (ZMod 2)) ≤ 0 := by
    have h0 : (0 : ℕ) ∈ Finset.range ((X + 1 : Polynomial (ZMod 2)).natDegree + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    have hinf := Finset.inf'_le
      (fun k => wCM (devCoeff X (X + 1 : Polynomial (ZMod 2)) k) + (k : ℕ) • wCM X) h0
    exact le_trans hinf (le_of_eq hterm)
  have h1 : wCM (X + 1) ≤ 0 := le_trans hle hmin
  rw [wCM_X_add_one] at h1
  have h2 : (1 : ℤ) ≤ 0 := by exact_mod_cast h1
  omega

/-- The universally-quantified III-G16 statement is FALSE (negation witness,
`Type`-instantiated). -/
theorem devid_le_universal_false :
    ¬ ∀ (K : Type) [CommRing K]
        (w : Polynomial K → WithTop ℤ), IsPolyValuation w →
        ∀ (G : ValGr.{0, 0} w) (Φ : Polynomial K), KPaBlock w G Φ →
        ∀ B : Polynomial K, w B ≤ minDev w Φ B := by
  intro h
  obtain ⟨w, hval, G, Φ, hkpa, B, hnot⟩ := devid_le_refuted
  exact hnot (h (ZMod 2) w hval G Φ hkpa B)

end G16Refutation

/-! ## Unit III-G21a — `gd3_min`: statement + order-≤1 instance (GD23 §7.3 GD3-MIN)

The §1.5 line is ELIDED (`theorem gd3_min …` with only the record comment
"GD3-MIN: ord_{ψ̂_hom}(in f) = ord_ψ(R_λ f), per level — under KeyPkg (order
≤ 1 instance outright)"); same convention as III-G18/G19/G20/G22 above: the
statement is completed from the source of record, GD23 brief §7.2–§7.3.
Completion ledger:

* LEFT side `ord_{ψ̂_hom}(in f)`: the III-G15a `ValGr` interface carries no
  divisibility operation, so the ψ̂-order is rendered through IMAGE
  divisibility (`GrOrdAt` below): ψ̂^μ = in(Φ^μ) divides in(f) with an
  initial-form cofactor, ψ̂^{μ+1} does not — the exact two-clause shape of
  the corpus residual-side order `Moves.OrdPsiPoly`.  At order ≤ 1 the
  ambient carrier is the fraction-field polynomial ring (§1.4), where every
  homogeneous element of gr(w₁) is an initial form (HOM-FACT, GD23 §7.3
  Route B display), so image divisibility IS graded divisibility there.
* RIGHT side `ord_{ψ_i}(R_λ f)`: the corpus `Moves.OrdPsiPoly` (verbatim
  reuse by import — the dedup rule), fired at the level's residual read
  `Rlam` into the level residue field `𝒦`.
* "per level, anchored read": the level enters as the NAMED row package
  `AnchoredRead` — GD23 §7.2's order-1 display
  `in(f) = ϕ · hom_{e,h}(R_λ f)` (KEY-g(iii)/RES-1) abstracted to its
  consumed rows: the read itself (`read`, with anchor ϕ_f), the dictionary
  laws (`lift_mul`, `lift_key` = "residual = initial-form ψ-order"'s KEY-g(i)
  tie in(Φ) = ψ̂ = hom(ψ)), the (g3)-type graded rows (`key_ne`, `cancel` —
  gr(w₁) is a domain, GD23 §1.3 (g3)), and RES-1's divisibility reflection
  (`reflect`, the §7.3 clause-(4) content at order ≤ 1).  All are
  [M]-hypothesis rows, NEVER axioms.
* "under KeyPkg": carried as the `KPaBlock` hypothesis (§1.5's graded
  rendering of III-H8's `KeyPkg`, per this file's DEVID convention).  The
  order-≤1 transfer below does not consume it; the general-order unit
  III-G21b does ("apply DEVID and the named graded/KPa rows").

Status honesty: `gd3_min` is PROVED OUTRIGHT below from the rows (the unit
row's proof column "residual = initial-form ψ-order; anchored read"), and the
row set is certified satisfiable by the compiled gate `gd3_min_gate` at the
`valGrIdentity` carrier over 𝔽₂ (trivial dressing: anchor ≡ 1, R_λ = id,
lift = id — the D-R3 probe's world, so the same D-R3 caveat applies: this
certifies non-vacuity of the row set, NOT the concrete order-≤1 grading).
The CONCRETE order-≤1 instantiation data (w₁'s graded carrier, hom_{e,h},
the ϕ-anchor, RES-1's slot basis) is owned by units III-G12b/G13a/G15b —
G15b is BLOCKED above (the §1.4 `gaussW`/`w1` display defect), so the
concrete instance inherits that block; unblock order per the G15b record. -/

/-- `ord_{ψ̂}(in f) = μ` on the graded carrier, via image divisibility:
    `in(Φ^μ)` divides `in(f)` with an initial-form cofactor and `in(Φ^{μ+1})`
    does not — shape-matched to the corpus `Moves.OrdPsiPoly`
    (`ψ^μ ∣ R ∧ ¬ ψ^{μ+1} ∣ R`). -/
def GrOrdAt {K : Type*} [CommRing K] {w : Polynomial K → WithTop ℤ}
    (G : ValGr w) (Φ f : Polynomial K) (μ : ℕ) : Prop :=
  (∃ B, G.inF f = G.inF (Φ ^ μ * B)) ∧ ¬ ∃ B, G.inF f = G.inF (Φ ^ (μ + 1) * B)

/-- The per-level ANCHORED READ (GD23 §7.2 (2′) at order ≤ 1 = KEY-g(iii) +
    RES-1, units III-G12b/G13a): named hypothesis rows tying the level's
    residual read `Rlam` to the graded world through a coefficient lift and
    an anchor.  See the unit header ledger for the row-by-row provenance. -/
structure AnchoredRead {K : Type*} [CommRing K] {w : Polynomial K → WithTop ℤ}
    (G : ValGr w) (Φ : Polynomial K)
    {𝒦 : Type*} [Field 𝒦] (ψ : Polynomial 𝒦)
    (Rlam : Polynomial K → Polynomial 𝒦) where
  lift : Polynomial 𝒦 → Polynomial K
  anchor : Polynomial K → Polynomial K
  read : ∀ f, f ≠ 0 → G.inF f = G.inF (anchor f * lift (Rlam f))
  lift_mul : ∀ R S, G.inF (lift (R * S)) = G.inF (lift R * lift S)
  lift_key : G.inF (lift ψ) = G.inF Φ
  key_ne : G.inF Φ ≠ G.zero
  cancel : ∀ a b c, a ≠ G.zero → G.mul a b = G.mul a c → b = c
  reflect : ∀ f R, (∃ B, G.inF (anchor f * lift R) = G.inF (Φ * B)) → ψ ∣ R

/-- III-G21a support — initial forms of key powers are nonzero (`inF 1 ≠ 0`
    forced by `key_ne` through (g2) + `mul_zero`; then (g2) + `dom`). -/
theorem ValGr.inF_pow_ne {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} (G : ValGr w) {Φ : Polynomial K}
    (hΦ : G.inF Φ ≠ G.zero) (μ : ℕ) : G.inF (Φ ^ μ) ≠ G.zero := by
  induction μ with
  | zero =>
    rw [pow_zero]
    intro h1
    refine hΦ ?_
    have h2 : G.inF Φ = G.mul (G.inF Φ) (G.inF 1) := by
      conv_lhs => rw [← mul_one Φ]
      exact G.g2 Φ 1
    rw [h2, h1]
    exact (G.mul_zero _).1
  | succ μ ih =>
    rw [pow_succ, G.g2]
    intro h
    rcases G.dom _ _ h with h' | h'
    · exact ih h'
    · exact hΦ h'

/-- III-G21a support — the anchored read marches ψ-powers to key powers:
    `in(g · lift(ψ^μ · S)) = in(Φ^μ · (g · lift S))`, one `lift_key` firing
    per step ((g2) + `lift_mul` + `lift_key` only). -/
theorem AnchoredRead.read_step {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} {G : ValGr w} {Φ : Polynomial K}
    {𝒦 : Type*} [Field 𝒦] {ψ : Polynomial 𝒦}
    {Rlam : Polynomial K → Polynomial 𝒦}
    (A : AnchoredRead G Φ ψ Rlam) (g : Polynomial K) (S : Polynomial 𝒦) :
    G.inF (g * A.lift (ψ * S)) = G.inF (Φ * (g * A.lift S)) := by
  rw [G.g2 g (A.lift (ψ * S)), A.lift_mul ψ S,
    G.g2 (A.lift ψ) (A.lift S), A.lift_key, ← G.g2 Φ (A.lift S),
    ← G.g2 g (Φ * A.lift S)]
  exact congrArg G.inF (by ring)

/-- III-G21a support — `read_step` iterated: the full ψ-power march. -/
theorem AnchoredRead.read_pow {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} {G : ValGr w} {Φ : Polynomial K}
    {𝒦 : Type*} [Field 𝒦] {ψ : Polynomial 𝒦}
    {Rlam : Polynomial K → Polynomial 𝒦}
    (A : AnchoredRead G Φ ψ Rlam) (g : Polynomial K) (S : Polynomial 𝒦)
    (μ : ℕ) :
    G.inF (g * A.lift (ψ ^ μ * S)) = G.inF (Φ ^ μ * (g * A.lift S)) := by
  induction μ generalizing S with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ μ ih =>
    calc G.inF (g * A.lift (ψ ^ (μ + 1) * S))
        = G.inF (g * A.lift (ψ ^ μ * (ψ * S))) :=
          congrArg (fun t => G.inF (g * A.lift t)) (by ring)
      _ = G.inF (Φ ^ μ * (g * A.lift (ψ * S))) := ih (ψ * S)
      _ = G.inF ((Φ ^ μ * g) * A.lift (ψ * S)) := congrArg G.inF (by ring)
      _ = G.inF (Φ * ((Φ ^ μ * g) * A.lift S)) := A.read_step _ S
      _ = G.inF (Φ ^ (μ + 1) * (g * A.lift S)) := congrArg G.inF (by ring)

/-- Unit III-G21a — the GD3-MIN transfer core, PROVED: under the anchored
    read, `ord_ψ(R_λ f) = μ` forces `ord_{ψ̂}(in f) = μ`.  Upper clause =
    the march (`read_pow`); lower clause = cancel the key power (`cancel`,
    `inF_pow_ne`) and reflect the leftover division into the residue
    polynomial ring (`reflect`), contradicting `¬ ψ^{μ+1} ∣ R_λ f`. -/
theorem gd3_min_transfer {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} {G : ValGr w} {Φ : Polynomial K}
    {𝒦 : Type*} [Field 𝒦] {ψ : Polynomial 𝒦}
    {Rlam : Polynomial K → Polynomial 𝒦}
    (A : AnchoredRead G Φ ψ Rlam)
    {f : Polynomial K} (hf : f ≠ 0) {μ : ℕ}
    (hres : Moves.OrdPsiPoly ψ (Rlam f) μ) :
    GrOrdAt G Φ f μ := by
  obtain ⟨⟨S, hS⟩, hnot⟩ := hres
  have hpsiS : ¬ ψ ∣ S := by
    rintro ⟨T, hT⟩
    exact hnot ⟨T, by rw [hS, hT]; ring⟩
  have hread : G.inF f = G.inF (Φ ^ μ * (A.anchor f * A.lift S)) := by
    rw [A.read f hf, hS]
    exact A.read_pow (A.anchor f) S μ
  refine ⟨⟨A.anchor f * A.lift S, hread⟩, ?_⟩
  rintro ⟨B, hB⟩
  have hEq : G.mul (G.inF (Φ ^ μ)) (G.inF (A.anchor f * A.lift S))
      = G.mul (G.inF (Φ ^ μ)) (G.inF (Φ * B)) := by
    rw [← G.g2, ← G.g2, ← hread, hB]
    exact congrArg G.inF (by ring)
  have hcanc := A.cancel _ _ _ (G.inF_pow_ne A.key_ne μ) hEq
  exact hpsiS (A.reflect f S ⟨B, hcanc⟩)

/-- The graded order is single-valued, so `gd3_min` reads as the record
    comment's EQUATION `ord_{ψ̂_hom}(in f) = ord_ψ(R_λ f)`. -/
theorem GrOrdAt.unique {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} {G : ValGr w} {Φ f : Polynomial K}
    {μ μ' : ℕ} (h : GrOrdAt G Φ f μ) (h' : GrOrdAt G Φ f μ') : μ = μ' := by
  by_contra hne
  rcases Nat.lt_or_ge μ μ' with hlt | hge
  · obtain ⟨B, hB⟩ := h'.1
    refine h.2 ⟨Φ ^ (μ' - (μ + 1)) * B, ?_⟩
    rw [hB]
    refine congrArg G.inF ?_
    rw [← mul_assoc, ← pow_add]
    have he : μ + 1 + (μ' - (μ + 1)) = μ' := by omega
    rw [he]
  · have hlt : μ' < μ := by omega
    obtain ⟨B, hB⟩ := h.1
    refine h'.2 ⟨Φ ^ (μ - (μ' + 1)) * B, ?_⟩
    rw [hB]
    refine congrArg G.inF ?_
    rw [← mul_assoc, ← pow_add]
    have he : μ' + 1 + (μ - (μ' + 1)) = μ := by omega
    rw [he]

/-- Unit III-G21a — `theorem gd3_min` (the §1.5 elided line, completed per
    the unit header ledger): per level — graded data `(G, Φ)` with its key
    block ("under KeyPkg": `KPaBlock`, consumed by the general-order proof
    III-G21b, not by the order-≤1 transfer) and the level's anchored
    residual read — `ord_{ψ̂_hom}(in f) = ord_ψ(R_λ f)`:
    the ψ̂-adic graded order of the initial form of `f` is the ψ-adic order
    of the residual `R_λ f`.  Equation form via `GrOrdAt.unique`. -/
theorem gd3_min {K : Type*} [CommRing K]
    {w : Polynomial K → WithTop ℤ} (G : ValGr w) (Φ : Polynomial K)
    (_hkpa : KPaBlock w G Φ)
    {𝒦 : Type*} [Field 𝒦] (ψ : Polynomial 𝒦)
    (Rlam : Polynomial K → Polynomial 𝒦)
    (A : AnchoredRead G Φ ψ Rlam)
    (f : Polynomial K) (hf : f ≠ 0) (μ : ℕ)
    (hres : Moves.OrdPsiPoly ψ (Rlam f) μ) :
    GrOrdAt G Φ f μ :=
  gd3_min_transfer A hf hres

/-! ### The compiled gate: the row set is satisfiable and `gd3_min` fires
(trivial-dressing carrier — see the unit header's status-honesty note). -/

/-- `KPaBlock` at the `valGrIdentity` carrier over `𝔽₂`, key `X`: monic ✓,
    degree 1 ✓, `X` irreducible with unit group `{1}` gives `primeInitial`,
    and no constant equals `X` gives `lowerDegree`. -/
theorem idKPaX :
    KPaBlock (fun _ => (0 : WithTop ℤ))
      (valGrIdentity (K := ZMod 2) fun _ => (0 : WithTop ℤ))
      (Polynomial.X : Polynomial (ZMod 2)) := by
  constructor
  · exact Polynomial.monic_X
  · simp
  · intro A B h
    have h' : A * B = Polynomial.X := h
    have hone : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
    rcases (Polynomial.irreducible_X (R := ZMod 2)).isUnit_or_isUnit h'.symm
      with hu | hu
    · right
      obtain ⟨r, hr, hCr⟩ := Polynomial.isUnit_iff.mp hu
      have hA : A = 1 := by rw [← hCr, hone r hr.ne_zero, Polynomial.C_1]
      show B = Polynomial.X
      rwa [hA, one_mul] at h'
    · left
      obtain ⟨r, hr, hCr⟩ := Polynomial.isUnit_iff.mp hu
      have hB : B = 1 := by rw [← hCr, hone r hr.ne_zero, Polynomial.C_1]
      show A = Polynomial.X
      rwa [hB, mul_one] at h'
  · intro B hdeg _ hBX
    have hB : B = Polynomial.X := hBX
    rw [hB, Polynomial.natDegree_X] at hdeg
    exact absurd hdeg (by omega)

/-- The trivial-dressing anchored read at the `valGrIdentity` carrier over
    `𝔽₂` (anchor ≡ 1, `lift` = `R_λ` = `id`, ψ = ψ̂ = `X`): every row holds
    outright.  Satisfiability certificate ONLY (D-R3 caveat). -/
noncomputable def idReadX :
    AnchoredRead (valGrIdentity (K := ZMod 2) fun _ => (0 : WithTop ℤ))
      (Polynomial.X : Polynomial (ZMod 2)) (Polynomial.X : Polynomial (ZMod 2))
      id where
  lift := id
  anchor _ := 1
  read f _ := (one_mul f).symm
  lift_mul _ _ := rfl
  lift_key := rfl
  key_ne := Polynomial.X_ne_zero
  cancel a b c ha h := by
    refine mul_left_cancel₀ (M₀ := Polynomial (ZMod 2)) (a := a) ?_ ?_
    · exact ha
    · exact h
  reflect f R h := by
    obtain ⟨B, hB⟩ := h
    have hB' : (1 : Polynomial (ZMod 2)) * R = Polynomial.X * B := hB
    rw [one_mul] at hB'
    exact ⟨B, hB'⟩

/-- Unit III-G21a gate, FIRED: at the trivial-dressing level the theorem
    computes `ord_{ψ̂}(in(X²(X+1))) = 2` from `ord_X(R_λ) = 2`.  Non-vacuity
    of the `gd3_min` row set, machine-checked. -/
theorem gd3_min_gate :
    GrOrdAt (valGrIdentity (K := ZMod 2) fun _ => (0 : WithTop ℤ))
      (Polynomial.X : Polynomial (ZMod 2))
      (Polynomial.X ^ 2 * (Polynomial.X + 1)) 2 := by
  have hne : (Polynomial.X ^ 2 * (Polynomial.X + 1) : Polynomial (ZMod 2)) ≠ 0 := by
    have h1 : (Polynomial.X + 1 : Polynomial (ZMod 2)).Monic := by
      simpa using Polynomial.monic_X_add_C (1 : ZMod 2)
    exact ((Polynomial.monic_X.pow 2).mul h1).ne_zero
  refine gd3_min _ _ idKPaX _ _ idReadX _ hne 2 ⟨⟨Polynomial.X + 1, rfl⟩, ?_⟩
  rintro ⟨T, hT⟩
  have hT' : (Polynomial.X ^ 2 * (Polynomial.X + 1) : Polynomial (ZMod 2))
      = Polynomial.X ^ (2 + 1) * T := hT
  have hT'' : (Polynomial.X ^ 2 * (Polynomial.X + 1) : Polynomial (ZMod 2))
      = Polynomial.X ^ 2 * (Polynomial.X * T) := by rw [hT']; ring
  have hXT : (Polynomial.X + 1 : Polynomial (ZMod 2)) = Polynomial.X * T :=
    mul_left_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) hT''
  have hev := congrArg (Polynomial.eval 0) hXT
  simp at hev

/-! ## Unit III-G23 — POS-g(iv): sub-multiplicativity at order i+1 (GD23 §3)

BP_III §1 displays NO Lean statement for III-G23 (unit-table row 758 only;
"Module not §1-displayed").  Following this module's III-G18/G19/G22
convention, the statement layer below is completed from the source of
record: `lean/notes/openmath/GD23_phaseB_verifybrief_rev4.md`, §1.2 ("Order
i+1": the `w_{i+1}` development definition) and §3 (Lemma POS-g REV 2,
clause (iv) + the division-control display).  The unit's dependency row
names III-G17 (`devid`); `devid` is UNLANDED and its hard half `devid_le`
(III-G16) is REFUTED AS STATED at the abstract `ValGr` interface (see the
module-header III-G16 record), so the division control enters as the NAMED
hypothesis row `hdev` of `wSucc_submul` — see that docstring's ledger. -/

/-- III-G23 support — the zero polynomial develops to `0` in every slot
(`0 %ₘ Φ = 0`, `0 /ₘ Φ = 0`, inducting along the development). -/
theorem devCoeff_zero_poly {K : Type*} [CommRing K] (Φ : Polynomial K) :
    ∀ j, devCoeff Φ (0 : Polynomial K) j = 0
  | 0 => by simp only [devCoeff, Polynomial.zero_modByMonic]
  | j + 1 => by
    simp only [devCoeff, Polynomial.zero_divByMonic]
    exact devCoeff_zero_poly Φ j

/-- III-G23 support — `n • ⊤ = ⊤` in `WithTop ℤ` for `1 ≤ n` (no Mathlib
form at `WithTop`; `Filter.nsmul_top` is the filter lattice). -/
theorem nsmul_top_of_one_le {n : ℕ} (hn : 1 ≤ n) : n • (⊤ : WithTop ℤ) = ⊤ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [succ_nsmul]
  exact add_top _

/-- III-G23 support — the order-(i+1) development weight (GD23 rev-4 §1.2,
"Order i+1"): from the order-i weight `w` (the brief's `w_i`), its key `Φ`
(`Φ_i`), the ramification datum `e` (`e_i`) and the augmented key value `γ`
(`γ_{i+1}`, integral normalization, carried in `ℤ`), the next weight reads
the `Φ`-adic development from below:
`wSucc w Φ e γ B = min_j (e·w(C_j) + j·γ)` — same `Finset.inf'` rendering
and slot range as `minDev` above. -/
noncomputable def wSucc {K : Type*} [CommRing K] (w : Polynomial K → WithTop ℤ)
    (Φ : Polynomial K) (e : ℕ) (γ : ℤ) (B : Polynomial K) : WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun j =>
    e • w (devCoeff Φ B j) + j • (γ : WithTop ℤ)

/-- III-G23 support — `wSucc` sends the zero polynomial to `⊤` (its only
slot is `e • w 0 = ⊤` for positive `e`). -/
theorem wSucc_zero {K : Type*} [CommRing K] {w : Polynomial K → WithTop ℤ}
    (hval : IsPolyValuation w) (Φ : Polynomial K) {e : ℕ} (he : 1 ≤ e) (γ : ℤ) :
    wSucc w Φ e γ 0 = ⊤ := by
  unfold wSucc
  refine le_antisymm le_top (Finset.le_inf' _ _ fun j _ => ?_)
  have hj : e • w (devCoeff Φ (0 : Polynomial K) j) + j • ((γ : ℤ) : WithTop ℤ)
      = ⊤ := by
    rw [devCoeff_zero_poly, hval.zero, nsmul_top_of_one_le he, top_add]
  exact hj.ge

/-- III-G23 support — uniqueness of the Φ-adic development (the display's
"the development is unique" step): any expansion `B = Σ_{k<N} Q_k·Φ^k` with
`deg Q_k < deg Φ` reads off slotwise as `devCoeff Φ B r = Q r` for `r < N`.
Via `Polynomial.div_modByMonic_unique`, inducting along the development. -/
theorem devCoeff_eq_of_eq_sum {K : Type*} [CommRing K] {Φ : Polynomial K}
    (hΦ : Φ.Monic) :
    ∀ (N : ℕ) (Q : ℕ → Polynomial K) (B : Polynomial K),
      (∀ k, (Q k).degree < Φ.degree) →
      B = ∑ k ∈ Finset.range N, Q k * Φ ^ k →
      ∀ r, r < N → devCoeff Φ B r = Q r := by
  intro N
  induction N with
  | zero => intro Q B _ _ r hr; exact absurd hr (Nat.not_lt_zero r)
  | succ N ih =>
    intro Q B hdeg hB r hr
    have hterm : ∑ k ∈ Finset.range N, Φ * (Q (k + 1) * Φ ^ k)
        = ∑ k ∈ Finset.range N, Q (k + 1) * Φ ^ (k + 1) :=
      Finset.sum_congr rfl fun k _ => by ring
    have hsum' : Q 0 + Φ * ∑ k ∈ Finset.range N, Q (k + 1) * Φ ^ k = B := by
      conv_rhs => rw [hB]
      simp only [Finset.sum_range_succ' (fun k => Q k * Φ ^ k) N, pow_zero,
        mul_one]
      rw [Finset.mul_sum, hterm, add_comm (Q 0)]
    obtain ⟨hdiv, hmod⟩ := Polynomial.div_modByMonic_unique
      (∑ k ∈ Finset.range N, Q (k + 1) * Φ ^ k) (Q 0) hΦ ⟨hsum', hdeg 0⟩
    cases r with
    | zero => simpa only [devCoeff] using hmod
    | succ r =>
      simp only [devCoeff]
      rw [hdiv]
      exact ih (fun k => Q (k + 1)) _ (fun k => hdeg (k + 1)) rfl r
        (Nat.lt_of_succ_lt_succ hr)

/-- III-G23 support — the division-control split of a product of development
coefficients (the display's `P_{ts} = c_{ts} + d_{ts}·Φ_i`): the low slot
`c_{ts}`. -/
noncomputable def devMulC {K : Type*} [CommRing K] (Φ A B : Polynomial K)
    (t s : ℕ) : Polynomial K :=
  (devCoeff Φ A t * devCoeff Φ B s) %ₘ Φ

/-- III-G23 support — the carry slot `d_{ts}` of the division-control split. -/
noncomputable def devMulD {K : Type*} [CommRing K] (Φ A B : Polynomial K)
    (t s : ℕ) : Polynomial K :=
  (devCoeff Φ A t * devCoeff Φ B s) /ₘ Φ

/-- III-G23 support — the carry slot has degree `< deg Φ` (the display's
"deg c, deg d < deg Φ_i — the full Φ_i-development of such P"): a product of
two development coefficients has `natDegree ≤ 2·deg Φ − 2`, so its monic
quotient drops below `deg Φ`. -/
theorem devMulD_degree_lt {K : Type*} [CommRing K] {Φ : Polynomial K}
    (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (A B : Polynomial K) (t s : ℕ) :
    (devMulD Φ A B t s).degree < Φ.degree := by
  unfold devMulD
  have h2 := Polynomial.natDegree_divByMonic (devCoeff Φ A t * devCoeff Φ B s) hΦ
  have h3 := Polynomial.natDegree_mul_le (p := devCoeff Φ A t)
    (q := devCoeff Φ B s)
  have h4 := devCoeff_natDegree_lt hΦ hd A t
  have h5 := devCoeff_natDegree_lt hΦ hd B s
  exact Polynomial.degree_lt_degree (by omega)

/-- III-G23 support — the assembled slot-`r` coefficient of `A·B`'s
Φ-development (the display's "the slot-r coefficient of AB's
Φ_i-development is `Σ_{t+s=r} c_{ts} + Σ_{t+s=r−1} d_{ts}`"). -/
noncomputable def devMulSlot {K : Type*} [CommRing K] (Φ A B : Polynomial K)
    (r : ℕ) : Polynomial K :=
  (∑ t ∈ Finset.range (A.natDegree + 1), ∑ s ∈ Finset.range (B.natDegree + 1),
    if t + s = r then devMulC Φ A B t s else 0)
  + ∑ t ∈ Finset.range (A.natDegree + 1), ∑ s ∈ Finset.range (B.natDegree + 1),
      if t + s + 1 = r then devMulD Φ A B t s else 0

/-- III-G23 support — every assembled slot has degree `< deg Φ` ("degrees
`< deg Φ_i`, and the development is unique"). -/
theorem devMulSlot_degree_lt {K : Type*} [CommRing K] [Nontrivial K]
    {Φ : Polynomial K} (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree)
    (A B : Polynomial K) (r : ℕ) : (devMulSlot Φ A B r).degree < Φ.degree := by
  have hbot : (⊥ : WithBot ℕ) < Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ.ne_zero]
    exact WithBot.bot_lt_coe _
  have hpiece : ∀ F : ℕ → ℕ → Polynomial K,
      (∀ t s, (F t s).degree < Φ.degree) →
      (∑ t ∈ Finset.range (A.natDegree + 1),
        ∑ s ∈ Finset.range (B.natDegree + 1), F t s).degree < Φ.degree := by
    intro F hF
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff hbot).mpr fun t _ => ?_)
    exact lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff hbot).mpr fun s _ => hF t s)
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · refine hpiece _ fun t s => ?_
    split_ifs
    · exact Polynomial.degree_modByMonic_lt _ hΦ
    · rw [Polynomial.degree_zero]; exact hbot
  · refine hpiece _ fun t s => ?_
    split_ifs
    · exact devMulD_degree_lt hΦ hd A B t s
    · rw [Polynomial.degree_zero]; exact hbot

/-- III-G23 support — the product's development identity (the display's
"AB = Σ_{t,s} a_t b_s Φ_i^{t+s}, and each P_{ts} divides as
c_{ts} + d_{ts}Φ_i", re-assembled by slot):
`A·B = Σ_{r < NA+NB+2} slot_r·Φ^r` with the assembled `devMulSlot` slots. -/
theorem mul_eq_sum_devMulSlot {K : Type*} [CommRing K] {Φ : Polynomial K}
    (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (A B : Polynomial K) :
    A * B = ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
      devMulSlot Φ A B r * Φ ^ r := by
  have hterm : ∀ t ∈ Finset.range (A.natDegree + 1),
      ∀ s ∈ Finset.range (B.natDegree + 1),
      devCoeff Φ A t * Φ ^ t * (devCoeff Φ B s * Φ ^ s)
        = (∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
            (if t + s = r then devMulC Φ A B t s else 0) * Φ ^ r)
          + ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
              (if t + s + 1 = r then devMulD Φ A B t s else 0) * Φ ^ r := by
    intro t ht s hs
    have ht' := Finset.mem_range.mp ht
    have hs' := Finset.mem_range.mp hs
    have h1 : (∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
        (if t + s = r then devMulC Φ A B t s else 0) * Φ ^ r)
        = devMulC Φ A B t s * Φ ^ (t + s) := by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
    have h2 : (∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
        (if t + s + 1 = r then devMulD Φ A B t s else 0) * Φ ^ r)
        = devMulD Φ A B t s * Φ ^ (t + s + 1) := by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
    rw [h1, h2]
    have hcd : devMulC Φ A B t s + Φ * devMulD Φ A B t s
        = devCoeff Φ A t * devCoeff Φ B s := by
      unfold devMulC devMulD
      exact Polynomial.modByMonic_add_div _ Φ
    calc devCoeff Φ A t * Φ ^ t * (devCoeff Φ B s * Φ ^ s)
        = devCoeff Φ A t * devCoeff Φ B s * Φ ^ (t + s) := by
          rw [pow_add]; ring
      _ = (devMulC Φ A B t s + Φ * devMulD Φ A B t s) * Φ ^ (t + s) := by
          rw [hcd]
      _ = devMulC Φ A B t s * Φ ^ (t + s)
          + devMulD Φ A B t s * Φ ^ (t + s + 1) := by
          rw [pow_succ]; ring
  have hswap : ∀ F : ℕ → ℕ → ℕ → Polynomial K,
      ∑ t ∈ Finset.range (A.natDegree + 1),
        ∑ s ∈ Finset.range (B.natDegree + 1),
          ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2), F t s r
      = ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
          ∑ t ∈ Finset.range (A.natDegree + 1),
            ∑ s ∈ Finset.range (B.natDegree + 1), F t s r := by
    intro F
    calc ∑ t ∈ Finset.range (A.natDegree + 1),
          ∑ s ∈ Finset.range (B.natDegree + 1),
            ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2), F t s r
        = ∑ t ∈ Finset.range (A.natDegree + 1),
            ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
              ∑ s ∈ Finset.range (B.natDegree + 1), F t s r :=
          Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
            ∑ t ∈ Finset.range (A.natDegree + 1),
              ∑ s ∈ Finset.range (B.natDegree + 1), F t s r := Finset.sum_comm
  calc A * B
      = (∑ t ∈ Finset.range (A.natDegree + 1), devCoeff Φ A t * Φ ^ t)
        * ∑ s ∈ Finset.range (B.natDegree + 1), devCoeff Φ B s * Φ ^ s := by
        rw [devCoeff_sum Φ hΦ hd A, devCoeff_sum Φ hΦ hd B]
    _ = ∑ t ∈ Finset.range (A.natDegree + 1),
          ∑ s ∈ Finset.range (B.natDegree + 1),
            devCoeff Φ A t * Φ ^ t * (devCoeff Φ B s * Φ ^ s) :=
        Finset.sum_mul_sum _ _ _ _
    _ = ∑ t ∈ Finset.range (A.natDegree + 1),
          ∑ s ∈ Finset.range (B.natDegree + 1),
            ((∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
              (if t + s = r then devMulC Φ A B t s else 0) * Φ ^ r)
              + ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
                  (if t + s + 1 = r then devMulD Φ A B t s else 0) * Φ ^ r) := by
        refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun s hs => ?_
        exact hterm t ht s hs
    _ = (∑ t ∈ Finset.range (A.natDegree + 1),
          ∑ s ∈ Finset.range (B.natDegree + 1),
            ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
              (if t + s = r then devMulC Φ A B t s else 0) * Φ ^ r)
        + ∑ t ∈ Finset.range (A.natDegree + 1),
            ∑ s ∈ Finset.range (B.natDegree + 1),
              ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
                (if t + s + 1 = r then devMulD Φ A B t s else 0) * Φ ^ r := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
          ∑ t ∈ Finset.range (A.natDegree + 1),
            ∑ s ∈ Finset.range (B.natDegree + 1),
              (if t + s = r then devMulC Φ A B t s else 0) * Φ ^ r)
        + ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
            ∑ t ∈ Finset.range (A.natDegree + 1),
              ∑ s ∈ Finset.range (B.natDegree + 1),
                (if t + s + 1 = r then devMulD Φ A B t s else 0) * Φ ^ r := by
        rw [hswap, hswap]
    _ = ∑ r ∈ Finset.range (A.natDegree + B.natDegree + 2),
          devMulSlot Φ A B r * Φ ^ r := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        unfold devMulSlot
        simp only [add_mul, Finset.sum_mul]

/-- Unit III-G23 — Lemma POS-g clause (iv) at order i+1 (GD23 rev-4 §3,
POS-g REV 2 + the division-control display; BP_III unit-table row 758:
"POS-g(iv) submultiplicativity at order i+1 GIVEN (V1)_i + KPa (division
control display)"; proof sketch "DEVID at (w_i, Φ_i) gives (α)/(β); slot
bookkeeping").  BP_III §1 displays no Lean statement for this unit, so —
the III-G18/G19/G22 convention — the statement is completed from the source
of record (GD23 rev-4 §1.2 "Order i+1" + §3 "Sub-multiplicativity of
w_{i+1}, given the above").  Completion ledger:
* `(V1)_i` = `hval : IsPolyValuation w` (the III-H8 frame): the order-i
  weight is a valuation at the state below;
* `hΦ`/`hd` are the two carrier rows of `(KP_{i−1})`'s (KPa)-block that the
  slot bookkeeping consumes directly (`monic`, `positiveDegree`) — the same
  extraction convention as `devid_ge` (III-G14);
* `hdev` — THE DIVISION-CONTROL SUPPLY: the "≤" half of Theorem DEVID at
  `(w_i, Φ_i)`, scoped exactly to the display's "any nonzero P of degree
  ≤ 2·deg Φ_i − 2".  The source derives it from "exactly the hypotheses of
  Theorem DEVID (§4) at (w_i, Φ_i)"; it CANNOT be consumed as a theorem
  here because `devid_le` (unit III-G16) is REFUTED AS STATED at the
  abstract `ValGr` interface (module-header III-G16 record) and the
  assembled `devid` (III-G17) is unlanded pending that statement
  adjudication.  It is therefore a NAMED hypothesis row (not an axiom, not
  discharged by fiat); once an adjudicated DEVID lands, discharge it as
  `fun P _ _ => (devid …).le`, collapsing this unit's conditionality to
  exactly "(V1)_i + KPa".  (α) `w(c_{ts}) ≥ w(P_{ts})` and (β)
  `w(d_{ts}) + w(Φ) ≥ w(P_{ts})` are read off `hdev` at slots 0 and 1;
* `e`/`γ`/`h` are §1.2's tower data at the read: `e = e_i ≥ 1` (`he`),
  `h = h_i ≥ 1` (`hh`), and `hγ` renders `γ_{i+1} := e_i·w_i(Φ_i) + h_i`
  (in particular pinning `w Φ ≠ ⊤`); the coprimality of `(e_i, h_i)` is
  not consumed and NOT assumed;
* conclusion: the display's `w_{i+1}(AB) ≥ w_{i+1}(A) + w_{i+1}(B)` in `≤`
  form at the `wSucc` rendering — the same shape as §1.4's order-1
  `w1_submul_heavyCarry` row (III-G7).  The display's "carry terms strictly
  heavier by h_i" enters as `h ≥ 0` slack only; the STRICT carry refinement
  is the order-1 unit III-G7's shape and is not claimed here. -/
theorem wSucc_submul {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (hval : IsPolyValuation w)
    (Φ : Polynomial K) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree)
    (e : ℕ) (he : 1 ≤ e) (γ h : ℤ) (hh : 1 ≤ h)
    (hγ : (γ : WithTop ℤ) = e • w Φ + (h : WithTop ℤ))
    (hdev : ∀ P : Polynomial K, P ≠ 0 → P.natDegree ≤ 2 * Φ.natDegree - 2 →
      w P ≤ minDev w Φ P)
    (A B : Polynomial K) :
    wSucc w Φ e γ A + wSucc w Φ e γ B ≤ wSucc w Φ e γ (A * B) := by
  by_cases hA : A = 0
  · rw [hA, zero_mul, wSucc_zero hval Φ he γ]; exact le_top
  by_cases hB : B = 0
  · rw [hB, mul_zero, wSucc_zero hval Φ he γ]; exact le_top
  haveI : Nontrivial K := by
    rcases subsingleton_or_nontrivial K with hK | hK
    · exact absurd (Subsingleton.elim A 0) hA
    · exact hK
  -- the degree bound feeding the division-control supply
  have hPdeg : ∀ t s : ℕ,
      (devCoeff Φ A t * devCoeff Φ B s).natDegree ≤ 2 * Φ.natDegree - 2 := by
    intro t s
    have h3 := Polynomial.natDegree_mul_le (p := devCoeff Φ A t)
      (q := devCoeff Φ B s)
    have h4 := devCoeff_natDegree_lt hΦ hd A t
    have h5 := devCoeff_natDegree_lt hΦ hd B s
    omega
  -- (α): the low slot is no lighter than the product
  have halpha : ∀ t s : ℕ,
      w (devCoeff Φ A t * devCoeff Φ B s) ≤ w (devMulC Φ A B t s) := by
    intro t s
    by_cases hP : devCoeff Φ A t * devCoeff Φ B s = 0
    · have hc0 : devMulC Φ A B t s = 0 := by
        unfold devMulC
        rw [hP, Polynomial.zero_modByMonic]
      exact le_of_eq (by rw [hP, hc0])
    · calc w (devCoeff Φ A t * devCoeff Φ B s)
          ≤ minDev w Φ (devCoeff Φ A t * devCoeff Φ B s) :=
            hdev _ hP (hPdeg t s)
        _ ≤ w (devCoeff Φ (devCoeff Φ A t * devCoeff Φ B s) 0) + (0 : ℕ) • w Φ :=
            Finset.inf'_le _ (Finset.mem_range.mpr (Nat.succ_pos _))
        _ = w (devMulC Φ A B t s) := by
            unfold devMulC
            simp only [devCoeff, zero_nsmul, add_zero]
  -- (β): the carry slot plus the key weight is no lighter than the product
  have hbeta : ∀ t s : ℕ,
      w (devCoeff Φ A t * devCoeff Φ B s) ≤ w (devMulD Φ A B t s) + w Φ := by
    intro t s
    by_cases hD : devMulD Φ A B t s = 0
    · rw [hD, hval.zero, top_add]; exact le_top
    · have hP : devCoeff Φ A t * devCoeff Φ B s ≠ 0 := by
        intro h0
        refine hD ?_
        unfold devMulD
        rw [h0, Polynomial.zero_divByMonic]
      have h1n : 1 ≤ (devCoeff Φ A t * devCoeff Φ B s).natDegree := by
        by_contra hlt
        refine hD ?_
        unfold devMulD
        exact (Polynomial.divByMonic_eq_zero_iff hΦ).mpr
          (Polynomial.degree_lt_degree (by omega))
      have hdc1 : devCoeff Φ (devCoeff Φ A t * devCoeff Φ B s) 1
          = devMulD Φ A B t s := by
        simp only [devCoeff]
        exact (Polynomial.modByMonic_eq_self_iff hΦ).mpr
          (devMulD_degree_lt hΦ hd A B t s)
      calc w (devCoeff Φ A t * devCoeff Φ B s)
          ≤ minDev w Φ (devCoeff Φ A t * devCoeff Φ B s) :=
            hdev _ hP (hPdeg t s)
        _ ≤ w (devCoeff Φ (devCoeff Φ A t * devCoeff Φ B s) 1) + (1 : ℕ) • w Φ :=
            Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
        _ = w (devMulD Φ A B t s) + w Φ := by rw [hdc1, one_nsmul]
  -- wSucc's slots bound it from above, definitionally
  have hwA : ∀ t ∈ Finset.range (A.natDegree + 1),
      wSucc w Φ e γ A ≤ e • w (devCoeff Φ A t) + t • (γ : WithTop ℤ) :=
    fun t ht => Finset.inf'_le _ ht
  have hwB : ∀ s ∈ Finset.range (B.natDegree + 1),
      wSucc w Φ e γ B ≤ e • w (devCoeff Φ B s) + s • (γ : WithTop ℤ) :=
    fun s hs => Finset.inf'_le _ hs
  -- the core product bound: each (t,s) contribution dominates the target
  have hcore : ∀ t ∈ Finset.range (A.natDegree + 1),
      ∀ s ∈ Finset.range (B.natDegree + 1),
      wSucc w Φ e γ A + wSucc w Φ e γ B
        ≤ e • w (devCoeff Φ A t * devCoeff Φ B s) + (t + s) • (γ : WithTop ℤ) := by
    intro t ht s hs
    refine (add_le_add (hwA t ht) (hwB s hs)).trans (le_of_eq ?_)
    simp only [hval.mul, nsmul_add, add_nsmul]
    abel
  -- the double-sum reduction under e•w(–) + c₀ (attained inf + ultrametric)
  have hsum : ∀ (T : Finset ℕ) (f : ℕ → Polynomial K) (c₀ : WithTop ℤ),
      (∀ i ∈ T, wSucc w Φ e γ A + wSucc w Φ e γ B ≤ e • w (f i) + c₀) →
      wSucc w Φ e γ A + wSucc w Φ e γ B ≤ e • w (∑ i ∈ T, f i) + c₀ := by
    intro T f c₀ hleaf
    rcases T.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.sum_empty, hval.zero, nsmul_top_of_one_le he, top_add]
      exact le_top
    · obtain ⟨i₀, hi₀, heq⟩ := Finset.exists_mem_eq_inf' hne fun i => w (f i)
      have hmin : w (f i₀) ≤ w (∑ i ∈ T, f i) := by
        rw [← heq]
        exact hval.le_w_sum T f _ fun j hj => Finset.inf'_le _ hj
      exact (hleaf i₀ hi₀).trans
        (add_le_add (nsmul_le_nsmul_right hmin e) le_rfl)
  -- c-part column bound
  have hSc : ∀ r : ℕ,
      wSucc w Φ e γ A + wSucc w Φ e γ B
        ≤ e • w (∑ t ∈ Finset.range (A.natDegree + 1),
            ∑ s ∈ Finset.range (B.natDegree + 1),
              if t + s = r then devMulC Φ A B t s else 0)
          + r • (γ : WithTop ℤ) := by
    intro r
    refine hsum _ _ _ fun t ht => hsum _ _ _ fun s hs => ?_
    split_ifs with hts
    · subst hts
      exact (hcore t ht s hs).trans
        (add_le_add (nsmul_le_nsmul_right (halpha t s) e) le_rfl)
    · rw [hval.zero, nsmul_top_of_one_le he, top_add]
      exact le_top
  -- d-part column bound (the carry, heavier by h ≥ 1 ≥ 0)
  have hSd : ∀ r : ℕ,
      wSucc w Φ e γ A + wSucc w Φ e γ B
        ≤ e • w (∑ t ∈ Finset.range (A.natDegree + 1),
            ∑ s ∈ Finset.range (B.natDegree + 1),
              if t + s + 1 = r then devMulD Φ A B t s else 0)
          + r • (γ : WithTop ℤ) := by
    intro r
    refine hsum _ _ _ fun t ht => hsum _ _ _ fun s hs => ?_
    split_ifs with hts
    · subst hts
      refine (hcore t ht s hs).trans ?_
      calc e • w (devCoeff Φ A t * devCoeff Φ B s) + (t + s) • (γ : WithTop ℤ)
          ≤ e • (w (devMulD Φ A B t s) + w Φ) + (t + s) • (γ : WithTop ℤ) :=
            add_le_add (nsmul_le_nsmul_right (hbeta t s) e) le_rfl
        _ ≤ e • (w (devMulD Φ A B t s) + w Φ) + (t + s) • (γ : WithTop ℤ)
            + (h : WithTop ℤ) :=
            le_add_of_nonneg_right (by exact_mod_cast (show (0 : ℤ) ≤ h by omega))
        _ = e • w (devMulD Φ A B t s) + (t + s + 1) • (γ : WithTop ℤ) := by
            simp only [succ_nsmul, hγ, nsmul_add]
            abel
    · rw [hval.zero, nsmul_top_of_one_le he, top_add]
      exact le_top
  -- assemble along the slots of A·B (ultrametric across the c/d split)
  have hslot : ∀ r : ℕ, r < A.natDegree + B.natDegree + 2 →
      wSucc w Φ e γ A + wSucc w Φ e γ B
        ≤ e • w (devMulSlot Φ A B r) + r • (γ : WithTop ℤ) := by
    intro r _
    unfold devMulSlot
    have hadd := hval.add
      (∑ t ∈ Finset.range (A.natDegree + 1),
        ∑ s ∈ Finset.range (B.natDegree + 1),
          if t + s = r then devMulC Φ A B t s else 0)
      (∑ t ∈ Finset.range (A.natDegree + 1),
        ∑ s ∈ Finset.range (B.natDegree + 1),
          if t + s + 1 = r then devMulD Φ A B t s else 0)
    rcases le_total
      (w (∑ t ∈ Finset.range (A.natDegree + 1),
        ∑ s ∈ Finset.range (B.natDegree + 1),
          if t + s = r then devMulC Φ A B t s else 0))
      (w (∑ t ∈ Finset.range (A.natDegree + 1),
        ∑ s ∈ Finset.range (B.natDegree + 1),
          if t + s + 1 = r then devMulD Φ A B t s else 0)) with hcs | hcs
    · rw [min_eq_left hcs] at hadd
      exact (hSc r).trans (add_le_add (nsmul_le_nsmul_right hadd e) le_rfl)
    · rw [min_eq_right hcs] at hadd
      exact (hSd r).trans (add_le_add (nsmul_le_nsmul_right hadd e) le_rfl)
  -- finish: the inf' over A·B's slots, each identified by dev uniqueness
  unfold wSucc
  refine Finset.le_inf' _ _ fun r hr => ?_
  have hrN : r < A.natDegree + B.natDegree + 2 := by
    have h3 := Polynomial.natDegree_mul_le (p := A) (q := B)
    have h6 := Finset.mem_range.mp hr
    omega
  have hdc : devCoeff Φ (A * B) r = devMulSlot Φ A B r :=
    devCoeff_eq_of_eq_sum hΦ (A.natDegree + B.natDegree + 2) (devMulSlot Φ A B)
      (A * B) (fun k => devMulSlot_degree_lt hΦ hd A B k)
      (mul_eq_sum_devMulSlot hΦ hd A B) r hrN
  rw [hdc]
  exact hslot r hrN

end LeanUrat.Scaffold.DictIII
