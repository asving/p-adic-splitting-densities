/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C1_stripClause
import LeanUrat.MovesC.C1_TYP_toClause
import LeanUrat.MovesD.Defs

/-!
# HC2/Defs — the JetSetup-existence bridge (HC-2), E-phase Defs layer

E-phase transcription of `lean/notes/HC2_LEAN_BLUEPRINT_2026-07-28.md` (REV 2, the accepted
blueprint), §3 (the two NAMED HYPOTHESES — never axioms) + §4 (D1 → D3 → D2 → D8 → D4 → D5 →
D6 → D7, the normative declaration order). Statements with `sorry` bodies where the blueprint
assigns P-phase proof duty; NO axiom is declared anywhere in this corpus (the §3 P-1 proposal
is NOT-DECLARED per its rev-2 disposition; P-2/P-3 are STRUCK tombstones).

FILE-LAYOUT NOTE: the blueprint names the directory `MovesJ/`; the E-phase charge names it
`HC2/`. Module path = `LeanUrat.HC2.*`; the NAMESPACE stays the blueprint's normative
`LeanUrat.MovesJ` (all downstream references are namespace-keyed, not module-keyed).

Elaboration deviations (each recorded in `MANIFEST.json` "deviations"):
* D4 GAP FOLD: `SideReads` is WIDENED by a `Φnext` parameter so clause (iv) (`LandingKey` at
  the next key) is hosted inside the per-read bundle; `ReadsOf` existentially designates
  `Φnext`, pinning it to the recorded child key at interior reads (the "designated final key"
  stays existential at the last read).
* `ReadsOf` carries `HistoryCoherent H` as a conjunct — the "D4 RECORDS coherence-adjacent
  data" route the blueprint's U19 NOTE authorizes (U19 collapses to a projection).
* `SideReads` clause (v) is the ALL-NODES polOM lift law + the canonRoot normalization (the
  U24 E-phase decision offered by the blueprint; runs are normalized by definition).
* `pinTransportSystem` is choice-on-spec (`IsFreshAttach`); existence of the attached system
  is U7's obligation (the "strip/value pin-attachment constructor" of the blueprint's D7).
* `mkFresh`'s `FreshData.disj` obligation is the forward lemma `mkFreshClauses_disj`
  (sorry here; U2's content).
* `ZCSeedLaws`'s E-phase field list: `downsets_literal` (§C C.1.5 "Downsets are literal",
  LST(i)/R4.5 item 3) + `pres_attain` (§B2-DEF D.3(e)(ii) attainable accounting). STANDING
  OBLIGATION (blueprint GAP-7(iii)): the E-phase AUDIT round checks this list line-by-line
  against C.1.5's proof.
Flagged for semantic-guardian review throughout (the trust boundary).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ## D1 `boxChart` — the ≺-sorted chart of the n×N box  [blueprint §4 D1] -/

/-- The canonical ≺-sorted enumeration of the n·N coordinate box: level-major
(ℓ ascending), base-index DESCENDING within a level (CoordPrec, §C C.0). -/
def boxChart (n N : ℕ) : Fin (n * N) → Coord :=
  fun j => ((j : ℕ) / n, n - 1 - (j : ℕ) % n)

/-- D1 law [P-phase obligation; consumes `C0.coordPrec_trichotomy` + div/mod arithmetic]:
`Fin`-order IS the global order `≺` on the chart. -/
theorem boxChart_sorted (n N : ℕ) :
    ∀ j j' : Fin (n * N), j < j' ↔ CoordPrec (boxChart n N j) (boxChart n N j') := by
  sorry

/-- D1 law [P-phase obligation]: the chart lands in the box (levels `< N`, base indices
`< n`); the `n = 0` case is junk-guarded by `Fin (0 * N)` emptiness. -/
theorem boxChart_lt (n N : ℕ) :
    ∀ j : Fin (n * N), (boxChart n N j).1 < N ∧ (boxChart n N j).2 < n := by
  sorry

/-! ## D3 `RecenterLiftSpec` — the lift specification (before D2, which chooses from it) -/

/-- The EXACT specification of a recentering lift at node ν — verbatim the recentering
clause of MovesC's `LandingKey` (D.10's center realizer): `t ∈ C_Φ`, `t ≠ 0`,
`w(t) = w(Φ)`, `dig(t) = c̃` at position 0. -/
def RecenterLiftSpec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (tL : Polynomial ℤ_[p]) : Prop :=
  inC ν.σ.Φ tL ∧ tL ≠ 0 ∧ ν.σ.w tL = ν.σ.w ν.σ.Φ ∧
    ν.σ.R tL = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0

/-! ## D2 `polOM` — the canonical policy instance (POL-PIN's carrier) -/

open Classical in
/-- THE canonical policy — nominally the note's (S6b′) OFFSET-P policy (MovesD §2's POL-PIN
row names it so; naming per the rev-2 GAP-6 reconciliation, SIGN-OFF recorded inline at the
blueprint's D2), delivered as the choice-selected realizer of that policy's specification:
at every node, the classically chosen realizer of `RecenterLiftSpec` when one exists, else 0.
Deterministic; reads only (σ, center) — never the lift field — so `blind` holds.
DISPLAYED CANONICITY DEVIATION — RATIFIED (blueprint AUDIT RULING 2, 2026-07-28): every
spec-realizer (the offset-P formula included) produces identical graded data, η's, masses,
counts, gates; the offset-P FORMULA's Lean form remains HC-1 property and can later replace
`h.choose` with zero consumer changes (same spec). -/
noncomputable def polOM (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] :
    CanonPolicy p F where
  liftOf ν := if h : ∃ tL, RecenterLiftSpec ν tL then h.choose else 0
  blind := by
    intro ν t
    -- `{ν with lift := t}` leaves σ and center untouched; the ∃ and its choice
    -- are literally the same proposition/term (structure eta).
    rfl

/-! ## D8 `IsReadLift` — the read-pair lift predicate (rev 2, the GAP-1 keying) -/

/-- The `IsNodeLift` formula abstracted off `Node` (rev 2, audit GAP-1): stride
`e'`, CURRENT-valuation weights `σ.w (t_k) = h'·(g−k)`, digit scalars the literal
ψ-coefficients at the frame's forced (S5) positions — the READ's own pair (the
F10 adjudication), NOT the frame-creating pair of `IsStandardLift`. -/
def IsReadLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
    (Φhat : Polynomial ℤ_[p]) : Prop :=
  ∃ tt : ℕ → Polynomial ℤ_[p],
    (∀ k, ψ.coeff k = 0 → tt k = 0) ∧
    (∀ k, k < g → ψ.coeff k ≠ 0 →
        tt k ≠ 0 ∧ inC σ.Φ (tt k) ∧
          σ.w (tt k) = (h' : ℤ) * ((g : ℤ) - (k : ℤ)) ∧
          σ.R (tt k) = LaurentPolynomial.C (ψ.coeff k) *
            LaurentPolynomial.T (- σ.t * σ.wPrev (tt k))) ∧
    Φhat = σ.Φ ^ (e' * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k)

/-- Definitional (blueprint D8): `IsNodeLift` at the node's own read pair IS `IsReadLift`
— both sides are the same formula at `(ψ, g, e', h') := (ν.ψ, ν.g, ν.e, ν.h)`. -/
theorem isNodeLift_iff {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (Φhat : Polynomial ℤ_[p]) :
    IsNodeLift ν Φhat ↔ IsReadLift ν.σ ν.ψ ν.g ν.e ν.h Φhat := Iff.rfl

/-! ## §3 — the two NAMED HYPOTHESES (ours; hypothesis-NEVER-axiom; the P-1/P-3 dispositions) -/

/-- The stage-transition supplier hypothesis (HC-1's TRANS; rev-1 P-1's statement with the
lift keyed at the READ pair per GAP-1). **NEVER an axiom** — consumers (U17a, history
construction) carry it verbatim; its discharge is HC-1's D.7 induction, or the recorded
P-1-reduced + `StageLedgerHyp` contingency (blueprint §3 DISPOSITION: DEFAULT = NO
DECLARATION). -/
def StageTransHyp (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ (σ : Stage p F), StageCoreL σ →
    ∀ (ψ : Polynomial ↥σ.K) (g : ℕ), ψ.Monic → ψ.natDegree = g → Irreducible ψ →
      ψ ≠ Polynomial.X → 1 ≤ g →
    ∀ (zbar : Fˣ), Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 →
    ∀ (e' h' : ℕ) (s' t' : ℤ), 1 ≤ e' → 1 ≤ h' → Nat.gcd e' h' = 1 →
      (e' : ℤ) * s' + (h' : ℤ) * t' = 1 → 0 ≤ t' ∧ t' < (e' : ℤ) →
    ∀ (Φhat : Polynomial ℤ_[p]), IsReadLift σ ψ g e' h' Φhat →
      IAug σ Φhat e' h' →
    ∃ σ' : Stage p F, σ'.Φ = Φhat ∧ σ'.e = e' ∧ σ'.h = h' ∧ σ'.s = s' ∧ σ'.t = t' ∧
      TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ'

/-- The uniqueness supplier hypothesis — typed VERBATIM as U18's statement (MovesD
`PresentNorm` clause (ii)). **NEVER an axiom** (P-3 STRUCK, blueprint §3 GAP-3); carried by
U15/U16 through `hnorm`'s uniqueness clause and by U26 ONLY if the proof-first route (U18)
fails — a recorded non-discharge, never a declaration. -/
def OmUniqHyp {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Prop :=
  ∀ H H' : History p F, H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') →
    etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H'

/-! ## D4 `SideReads` / `ReadsOf` — the f-explicit run predicate (Wall A; the W4-1 seam) -/

/-- The recorded read data are the ACTUAL window data of the development `B` — the ONE
per-read clause bundle (kept a separate def so U20–U22 consume its conjuncts by name; THE
NEGOTIATING DEFINITION for MovesD's W4-1 `eligible` seam — MovesT re-keys to THIS):
(i) SIDE (D.3(a)/(c), stage scale) — the read functional `e·w(B_j) + j·h` is ≥ the recorded
    total side weight `γ` at every nonzero slot (the side is a genuine lower-hull support
    line), with equality ONLY at the recorded stride digits `j = s0 + e·k`, `pat k ≠ 0`;
(ii) DIGITS — at every recorded stride slot the coefficient is nonzero, ON the side, and its
    residual is the monomial-unit with scalar `pat k` at the forced (S5) position;
(iii) ANCHOR/ORDER — the recorded (a, Ranch) anchor the frame residual of `f = Σ B_j Φ^j`
    (`HasAnchorK`), and `ord_ψ Ranch = μ` (ties the PATTERN to `f`; E-PHASE FLAG: the
    `σ.R f` rendering of "frame residual" may over-strengthen at multi-side polygons —
    U31 is the day-one adjudicating gate);
(iv) DESCENT WITNESS [the D4 FOLD: hosted here through the widened `Φnext` parameter] —
    the landing key is realized: `LandingKey ν Φnext`;
(v) LIFTS + ROOT NORMALIZATION [the U24 E-phase decision] — the node carries the polOM
    lift and the canonical residue root (runs are normalized by definition, §D4-R's
    "the classifier is run with ONE lift rule" + rev-6 canonRoot pinning). -/
def SideReads {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) : Prop :=
  -- (i) SIDE
  ((∀ j : ℕ, j < Nd → B j ≠ 0 →
      ν.gam ≤ (ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ)) ∧
   (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ) = ν.gam →
      ∃ k : ℕ, k ≤ ν.wSide / ν.e ∧ j = ν.s0 + ν.e * k ∧ ν.pat k ≠ 0)) ∧
  -- (ii) DIGITS
  (∀ k : ℕ, k ≤ ν.wSide / ν.e → ν.pat k ≠ 0 →
      B (ν.s0 + ν.e * k) ≠ 0 ∧
      (ν.e : ℤ) * ν.σ.w (B (ν.s0 + ν.e * k)) + ((ν.s0 + ν.e * k : ℕ) : ℤ) * (ν.h : ℤ)
        = ν.gam ∧
      ν.σ.R (B (ν.s0 + ν.e * k)) = LaurentPolynomial.C (ν.pat k) *
        LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (B (ν.s0 + ν.e * k)))) ∧
  -- (iii) ANCHOR/ORDER
  (HasAnchorK (ν.σ.R (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j)) ν.a ν.Ranch ∧
   OrdPsiPoly ν.ψ ν.Ranch ν.μ) ∧
  -- (iv) DESCENT WITNESS (the fold: LandingKey at the designated next key)
  LandingKey ν Φnext ∧
  -- (v) LIFTS + ROOT NORMALIZATION
  (ν.lift = (polOM p F).liftOf ν ∧ ((ν.zbar : Fˣ) : F) = canonRoot ν)

/-- "History H is a classifier run on f" (Wall A; the W4-1 seam): H is a coherent recorded
tower, and per read i, f's development in frame i's key realizes the recorded side/digit
data and the recorded landing produces the designated next key (pinned to the recorded
child frame key at interior reads). NON-VACUITY ANCHOR: U31 (`gate_readsOf_inert2`). -/
def ReadsOf (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (f : Polynomial ℤ_[p]) (H : History p F) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ HistoryCoherent H ∧
  ∀ (i : ℕ) (hi : i < H.nodes.length),
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
      IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd ∧
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      SideReads (H.nodes[i]'hi) B Nd Φnext

/-! ## D5 `KeysLawful` / `ZCSeedLaws` / `PresentSeed` — the graded seed (Wall B; HC-1's interface) -/

/-- U1's key-tower laws, named (rev 2): interior keys are the recorded child keys, and
EVERY read (incl. the final one) lands on `keys i`. -/
def KeysLawful {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (keys : ℕ → Polynomial ℤ_[p]) : Prop :=
  (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i))

/-- **`ZCSeedLaws`** — the TO-BE-FIXED-AT-E-PHASE seed-law bundle (blueprint D5 FENCE:
only laws (a) stated in §C C.1.5/rev-9's display or (b) §B2-DEF D.3(e) content). E-PHASE
FIELD LIST (STANDING OBLIGATION GAP-7(iii): the E-phase AUDIT round checks this list
line-by-line against C.1.5's proof — every field a quoted note display):
* `downsets_literal` — §C C.1.5 "Downsets are literal", QUOTED: "since w is defined through
  the K1 chain as an iterated slot-minimum, a valuation clause w(B) ≥ β is, in the frame's
  own tower coordinates, the literal zero system {y_(b,l) = 0 : ht(b,l) < β, b ∈ blk(B)}".
  This is LST(i)/R4.5 item 3 — the identification of the DEFINED `History.htH` with the
  presentation's own height reading, in its U9/U10 consumer form. Scale: stage-i weights
  are `STR_i ×` absolute (C.1.0(c)); the stage side reads `σ.w B / STR_i` against ht.
* `pres_attain` — §B2-DEF D.3(e)(ii)'s ATTAINABLE ACCOUNTING (MovesC `History.htH` FLAG:
  "log_p|𝒜(γ)| = |{c : htH = γ}| per block"): on each recorded value support,
  presentations attain every digit assignment, holding the off-support digits fixed. -/
structure ZCSeedLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) {m : ℕ} (coordOf : Fin m → Coord)
    (pres : ℕ → (Fin m → ZMod p) → Polynomial ℤ_[p] → Prop)
    (Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p)))
    (keys : ℕ → Polynomial ℤ_[p]) : Prop where
  downsets_literal : ∀ (i : ℕ) (hi : i < H.nodes.length) (x : Fin m → ZMod p)
      (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      pres i x f → IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd →
      ∀ (j : ℕ) (β : ℚ),
        ((B j = 0 ∨ β ≤ ((H.nodes[i]'hi).σ.w (B j) : ℚ) / (H.strFrame i : ℚ)) ↔
          (∀ c : Fin m, (H.nodes[i]'hi).fineSlot (coordOf c).2 = j →
            H.htH i (coordOf c) < β → x c = 0))
  pres_attain : ∀ (i : ℕ) (hi : i < H.nodes.length) (S : Finset (Fin m)),
      IsValueSupport H coordOf i (H.nodes[i]'hi) S →
      ∀ (x : Fin m → ZMod p) (f : Polynomial ℤ_[p]), pres i x f →
      ∀ d : Fin m → ZMod p,
        ∃ (x' : Fin m → ZMod p) (f' : Polynomial ℤ_[p]), pres i x' f' ∧
          (∀ c ∉ S, x' c = x c) ∧ (∀ c ∈ S, x' c = d c)

/-- The graded-presentation SEED (D5, rev-2 PRUNED per audit GAP-5): exactly the fields of
`JetSetup` that MovesC's honest boundary defers to the unbuilt graded ring (§B2-DEF R4.5
items 1&3), and literally NOTHING else. HC-1 supplies values (SEED-EXIST, Wall B — stated
ONCE, at U15); U13 proves `JetSetup` from a seed. Field statements are byte-identical to
`JetSetup`'s at `coordOf := boxChart n N` and these `keys`. -/
structure PresentSeed (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (H : History p F) (n N : ℕ) (keys : ℕ → Polynomial ℤ_[p]) where
  pres : ℕ → (Fin (n * N) → ZMod p) → Polynomial ℤ_[p] → Prop
  pres_zero : ∀ (x : Fin (n * N) → ZMod p) (f : Polynomial ℤ_[p]), pres 0 x f ↔
      ∀ j : Fin (n * N), x j = baseDigit p (boxChart n N j).1 (f.coeff (boxChart n N j).2)
  pres_total : ∀ i : ℕ, i ≤ H.nodes.length → ∀ f : Polynomial ℤ_[p],
      f.Monic → f.natDegree = n → ∃ x, pres i x f
  Theta : ℕ → ((Fin (n * N) → ZMod p) → (Fin (n * N) → ZMod p))
  Theta_uni : ∀ i : ℕ, IsUnitriangular (Theta i)
  pres_theta : ∀ i : ℕ, i < H.nodes.length →
      ∀ (x : Fin (n * N) → ZMod p) (f : Polynomial ℤ_[p]), pres (i+1) x f → pres i (Theta i x) f
  /-- verbatim `JetSetup.pres_block`, at these keys and `boxChart` (C.1.0(a) block-locality). -/
  pres_block : ∀ i : ℕ, i < H.nodes.length →
      ∀ (f f' : Polynomial ℤ_[p]) (x x' : Fin (n * N) → ZMod p),
        pres (i+1) x f → pres (i+1) x' f' →
      ∀ (B B' : ℕ → Polynomial ℤ_[p]) (Nd Nd' : ℕ),
        IsDevelopment (keys i) f B Nd → IsDevelopment (keys i) f' B' Nd' →
        ∀ c : Fin (n * N),
          B ((boxChart n N c).2 / (keys i).natDegree) = B' ((boxChart n N c).2 / (keys i).natDegree) →
          x c = x' c
  /-- R4.5 item 1: the graded piece map of each recorded value support — a TypObject with
  FULL alphabet (`Fin S.card → ZMod p`): D.3(e)(i)'s additive span + D.3(e)(ii)'s attainable
  accounting, jointly (surjectivity onto the full `p^|S|` alphabet IS the two
  identifications' consumer form). -/
  typObj : ∀ (i : ℕ) (hi : i < H.nodes.length) (S : Finset (Fin (n * N))),
      IsValueSupport H (boxChart n N) i (H.nodes[i]'hi) S →
      TypObject p (n * N) S (Fin S.card → ZMod p)
  /-- the height-law consumer form (LST(i), R4.5 item 3): the DEFINED `History.htH` is the
  presentation's own height reading — the ZC-seed laws the U9/U10 induction consumes. -/
  zcSeed : ZCSeedLaws H (boxChart n N) pres Theta keys

/-! ## D6 `mkFresh` — the fresh-data constructor  [def-only; laws = U2–U6] -/

/-- The emitted-value family (the R4.B.2 provenance boundary, concretized): per read `i`,
span slot `j`, and support `T`, the emitted value in `T`'s alphabet. Free parameter at this
layer; U27/U28's gates fix it concretely at order 0. -/
abbrev VOf (p m : ℕ) : Type := ℕ → ℕ → (T : Finset (Fin m)) → (Fin T.card → ZMod p)

/-- `Nat.card` of a digit alphabet (elaboration helper for `C1_TYP_toClause`). -/
private lemma card_fin_fun (p k : ℕ) [Fact p.Prime] :
    Nat.card (Fin k → ZMod p) = p ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [Nat.card_eq_fintype_card, ZMod.card]

open Classical in
/-- The COMPLETE height-level set of span slot `j` at its exact valuation (rev 14 C.1(ii)'s
on-lattice value-digit locus, as a Finset of the box — `IsValueSupport`'s carrier). -/
noncomputable def levelSet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) (i : ℕ) (ν : Node p F) (j : ℕ) : Finset (Fin (n * N)) :=
  Finset.univ.filter (fun c =>
    ν.fineSlot ((boxChart n N c).2) = j ∧ H.htH i (boxChart n N c) = ν.slotVal j)

open Classical in
/-- The STRIP roster of read `i`: band coordinates that are NOT value positions
(β/γ strips through the line, (α)-strips strictly between floor and exact valuation,
cluster zeros at the root — §C C.1(ii)). -/
noncomputable def stripSet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) (i : ℕ) (ν : Node p F) : Finset (Fin (n * N)) :=
  Finset.univ.filter (fun c =>
    inFreshBand H n (boxChart n N) i ν c ∧ ¬ IsValueCoord H (boxChart n N) i ν c)

open Classical in
/-- The VALUE-SLOT roster of read `i`: recorded span slots whose exact-valuation level set
is nonempty AND in-band (the (γ)-crossing self-truncation — D6 constructs value clauses
only at pre-crossing slots, blueprint U3 sketch). -/
noncomputable def valueSlots {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) (i : ℕ) (ν : Node p F) : Finset ℕ :=
  (Finset.range (ν.s0 + ν.wSide + 1)).filter (fun j =>
    ν.spanSlot j ∧ (levelSet H n N i ν j).Nonempty ∧
    ∀ c ∈ levelSet H n N i ν j, inFreshBand H n (boxChart n N) i ν c)

open Classical in
/-- Membership in the value-slot roster yields the span-slot certificate (elaboration
helper feeding `valueClause`'s `hsp` argument). -/
lemma valueSlots_spanSlot {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} {n N : ℕ} {i : ℕ} {ν : Node p F} {j : ℕ}
    (hj : j ∈ valueSlots H n N i ν) : ν.spanSlot j := by
  unfold valueSlots at hj
  exact (Finset.mem_filter.mp hj).2.1

/-- One VALUE clause: the `C1.TYP_toClause` clause of the seed's TypObject at slot `j`'s
level set, at the emitted value `vOf i j` (support the level set, `codim = |support|`,
constraint `T.φ x = v` — §C Lemma TYP(b)). -/
noncomputable def valueClause {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ)
    (hsp : (H.nodes[i]'hi).spanSlot j) : LevelClause p (n * N) :=
  (C1_TYP_toClause
    (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
      ⟨j, hsp, fun c => Iff.intro
        (fun hc => (Finset.mem_filter.mp hc).2)
        (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
    (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
    (levelSet H n N i (H.nodes[i]'hi) j).card
    (card_fin_fun p _)).choose

/-- Read `i`'s fresh clause LIST: one STRIP clause (`C1.stripClause`) per band coordinate
that is NOT a value position; one VALUE clause per rostered span slot. -/
noncomputable def mkFreshClauses {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) : List (LevelClause p (n * N)) :=
  ((stripSet H n N i (H.nodes[i]'hi)).toList.map
      (fun c => (C1_stripClause (p := p) c).choose))
  ++ ((valueSlots H n N i (H.nodes[i]'hi)).attach.toList.map
      (fun jh => valueClause H n N S vOf i hi jh.1 (valueSlots_spanSlot jh.2)))

/-- The constructed clause supports are pairwise disjoint [P-phase obligation = U2's
content: strips are singletons at distinct non-value coords; value supports are level sets
of distinct span slots; strips exclude value coords]. -/
theorem mkFreshClauses_disj {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    (mkFreshClauses H n N S vOf i hi).Pairwise
      (fun c₁ c₂ => Disjoint c₁.support c₂.support) := by
  sorry

/-- **D6 `mkFresh`** — read `i`'s fresh clauses, constructed from node geometry (blueprint
D6): strips + value clauses at the seed's TypObjects and the emitted values `vOf` (the
R4.B.2 provenance boundary — a free parameter here). -/
noncomputable def mkFresh {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) : FreshData p (n * N) :=
  ⟨mkFreshClauses H n N S vOf i hi, mkFreshClauses_disj H n N S vOf i hi⟩

/-- The empty fresh data (junk beyond the history; U13's total-`fresh` filler). -/
def emptyFresh (p m : ℕ) : FreshData p m := ⟨[], List.Pairwise.nil⟩

/-! ## D7 `pinTransportSystem` / `mkStratum` / `mkSigma` — the state chain  [def-only; laws = U7–U10] -/

/-- **The fresh-attachment SPEC** (D7): `D'` re-presents `Θ*(D) ∩ (fresh locus)` as a digit
system with (1) that exact solution set, (2) pins = the transported pins PLUS the fresh
clauses' cut coordinates (= the clause supports: a strip cuts its coordinate, a value
clause its whole level set — the DIG re-presentation's pinned set), (3) literal-zero
solves at strip coordinates and (4) zero-solve transport (C.1.5(2): old zeros survive as
zeros — the (ZC-a) normalized presentation). Existence of such a `D'` from
`C0.pinTransport` + the strip/value pin-attachment constructor is U7's obligation. -/
def IsFreshAttach {p m : ℕ} (D : Locus p m)
    (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) (fd : FreshData p m)
    (D' : Locus p m) : Prop :=
  (∀ x, D'.IsSolution x ↔ (D.IsSolution (Θ x) ∧ fd.sat x)) ∧
  (∀ c : Fin m, D'.pinned c = true ↔
    (D.pinned c = true ∨ ∃ cl ∈ fd.clauses, c ∈ cl.support)) ∧
  (∀ c : Fin m, (∃ cl ∈ fd.clauses, cl.support = {c} ∧ ∀ x, (cl.sat x ↔ x c = 0)) →
    ∀ g, D'.solve c g = 0) ∧
  (∀ c : Fin m, D.pinned c = true → (∀ g, D.solve c g = 0) → ∀ g, D'.solve c g = 0)

open Classical in
/-- The transported-and-attached system: THE spec-satisfying digit system when one exists
(choice), else the junk default `D`. The (ZC)-relevant geometry (WHICH coordinates the
value clauses pin) is settled by U9/U10, not by this definition; the definition only
fixes the digit-system CARRIER (blueprint D7). -/
noncomputable def pinTransportSystem {p m : ℕ} (D : Locus p m)
    (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) (fd : FreshData p m) : Locus p m :=
  if h : ∃ D' : Locus p m, IsFreshAttach D Θ fd D' then h.choose else D

/-- Choice-unfolding glue: under existence, `pinTransportSystem` satisfies its spec. -/
theorem pinTransportSystem_spec {p m : ℕ} (D : Locus p m)
    (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) (fd : FreshData p m)
    (h : ∃ D' : Locus p m, IsFreshAttach D Θ fd D') :
    IsFreshAttach D Θ fd (pinTransportSystem D Θ fd) := by
  unfold pinTransportSystem
  rw [dif_pos h]
  exact h.choose_spec

/-- **D7 `mkStratum`** — read `i`'s stratum = its FRESH clause content (THE §2.1 DISPLAYED
DEVIATION, RATIFIED at the blueprint's AUDIT RULING 1: `inh_implied` then holds
one unfold deep; the inherited content of `E(ν_i)` is INSTALLED, its semantic residue
carried by U9/U10 + the U27/U28 gates). Junk-true beyond the history. -/
noncomputable def mkStratum {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) : (Fin (n * N) → ZMod p) → Prop :=
  fun y => ∀ hi : i < H.nodes.length, (mkFresh H n N S vOf i hi).sat y

/-- **D7 `mkSigma`** — the state chain: `Sigma 0` = the full box (`topLocus`); each read is
consumed once through the transported-and-attached system (junk: identity step beyond the
history). -/
noncomputable def mkSigma {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) : ℕ → Locus p (n * N)
  | 0 => topLocus p (n * N)
  | i + 1 =>
      if hi : i < H.nodes.length then
        pinTransportSystem (mkSigma H n N S vOf i) (S.Theta i) (mkFresh H n N S vOf i hi)
      else mkSigma H n N S vOf i

/-! ## Addenda (elaboration helpers, MovesD-poolProj pattern) -/

/-- [U14 addendum] The fresh band on RAW coordinates (the `inFreshBand` formula off the
chart — NP-ID's ⊆-direction carrier: band levels, not box positions, are what `NPband`
bounds). At `c = coordOf j` this is literally `inFreshBand`. -/
def inFreshBandC {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n : ℕ) (i : ℕ) (ν : Node p F) (c : Coord) : Prop :=
  c.2 < H.prevRim n i ∧
  H.floorH i c.2 < ((H.htH i c : ℚ) : WithBot ℚ) ∧
  H.htH i c ≤ ν.slotVal (ν.fineSlot c.2)

/-- [Gate addendum] The ambient field of the p = 2 order-0 gates (U27/U31): GF(4) — big
enough for the n = 2 inert read's residue growth. -/
abbrev F4 : Type := GaloisField 2 2

/-- [Gate addendum] The ambient field of the q′ = 3 separation gate (U28): GF(9). -/
abbrev F9 : Type := GaloisField 3 2

end LeanUrat.MovesJ
