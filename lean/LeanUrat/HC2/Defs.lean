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
* DEFS-REPAIR (2026-07-27, deviation-correction — blueprint §2.2): the first transcription
  of `downsets_literal` BOX-TRUNCATED the note's iff (the zero system {ht(b,l) < β} ranges
  over the frame's OWN tower coordinates, not the n×N box), over-claiming the ← direction;
  machine-refuted (`scratch_U9_presentSeed_false.lean` derived `False` from any
  `PresentSeed` via `f = C(p^N)`). Repaired by the CHART-COVERAGE GUARD (see the field's
  docstring); the refutation no longer elaborates. Seed-chain units restated-in-place and
  annotated RESTATED-POST-DEFS-REPAIR (U5, U6, U8, U9, U13, U14, U27, U29, U30).
* DEFS-REPAIR DC-2 (2026-07-28, deviation-correction — blueprint §2.2; §9 F-7 AUTHORIZED):
  `IsFreshAttach`'s solution-set clause read the fresh locus at `x` (`fd.sat x`) where the
  blueprint's normative U7 display and the FROZEN `JetSetup.recursion` field type demand
  `Θ x`. Repaired to `fd.sat (Θ x)` (see the def's docstring); U7's stop-the-line record
  is thereby discharged and its route re-opens.
* DEFS-REPAIR DC-3 (2026-07-28, deviation-correction — same class as DC-1/DC-2; K2 kernel
  round): `IsFreshAttach` clauses (3)/(4) demanded LITERAL-zero solves in the NEW
  coordinates where the frozen recursion keying and the PROVED `C0_pinTransport`
  transported-solve shape demand zeros OF THE Θ-IMAGE (the same untransported-coordinate
  bug DC-2 fixed in clause (1), one clause over). Post-DC-2 clauses (1)+(3) were JOINTLY
  UNSATISFIABLE at lawful seeds with nonzero `Theta`-corrections on strip coordinates —
  machine-refuted (`scratch_U7_recursion_false.lean`, U27's gate seed + the constant
  unitriangular shift; now dead). Repaired to the Θ-composed form (see the def's
  docstring); blueprint statements unchanged (its D7 fixes only the carrier). U7's
  second stop-the-line record is discharged: the i = 0 recursion instance is now PROVED
  (`mkSigma_recursion_zero`, subsuming the refutation's exact instance), the general
  attachment constructor is proved under the blueprint's own pre-named per-step
  condition ("fresh supports UNPINNED on the prior state", D5 zcSeed docstring). The
  LITERAL-zero (ZC-a) content moves where the note keeps it (conditional): the pending
  Θ-normalization zcSeed law (U9b/U9c records; D5-fence sign-off item).
* N-QUEUE SIGN-OFF ROUND (2026-07-28, Asvin definition-change authority; Codex confirms
  after — see MANIFEST "nqueue_2026-07-28"): (N-4) `SideReads` gains the ADDITIVE clause
  (vi) VERTEX READ-OFF (§9 F-3; U31 gate re-run queued for the fleet phase); (N-2)
  `D10Eligible` addendum (§9 F-1); (N-5) `RootD4` addendum (§9 F-6); (K3)
  `AdjacentReads` addendum (the U18 conditional-refutation repair — NOTE 2026-07-30
  verify-2 fold-in: the guarded U18 was itself refuted same-round and superseded by
  the transport-keyed REV 3; the def is now consumer-less — see its docstring); (K2)
  `SeedFreshUnpinned` addendum (the bare-recursion disposition); (D5 fence) `ZCSeedLaws`
  gains the two pre-assigned laws `theta_norm` + `root_shape` (the U9b/U9c residue —
  NOTE root_shape's faithful weakening recorded at the field). Every addition is
  hypothesis-side or additive; no axiom, no weakening.
* QUEUE ITEM 17 (2026-07-31, Asvin sign-off on the consolidated queue — the U10c
  designer addendum, Q8-class D5-fence event): `ZCSeedLaws` gains the STEP-READ law
  `step_shape` — `root_shape`'s all-reads generalization (the (ZC-b) "leads at rim"
  interior content; U10c's third-prover record named exactly this residue). U10c
  (`U10_zcStep.zc_step_interiorZero`) and the assembled `zc_step` close with it.
  Hypothesis-side, additive; discharged at U27's gate by the root_shape arithmetic.
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
  intro j j'
  have hnN : 0 < n * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at hnN)
  have hda : n * ((j : ℕ) / n) + (j : ℕ) % n = (j : ℕ) := Nat.div_add_mod _ _
  have hdb : n * ((j' : ℕ) / n) + (j' : ℕ) % n = (j' : ℕ) := Nat.div_add_mod _ _
  have hra : (j : ℕ) % n < n := Nat.mod_lt _ hn
  have hrb : (j' : ℕ) % n < n := Nat.mod_lt _ hn
  simp only [boxChart, CoordPrec, Fin.lt_def]
  constructor
  · intro hab
    rcases lt_trichotomy ((j : ℕ) / n) ((j' : ℕ) / n) with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by rw [h] at hda; omega⟩
    · exact absurd (Nat.div_le_div_right hab.le) (not_le.mpr h)
  · rintro (h | ⟨h, hlt⟩)
    · by_contra hcon
      exact absurd (Nat.div_le_div_right (not_lt.mp hcon)) (not_le.mpr h)
    · rw [h] at hda; omega

/-- D1 law [P-phase obligation]: the chart lands in the box (levels `< N`, base indices
`< n`); the `n = 0` case is junk-guarded by `Fin (0 * N)` emptiness. -/
theorem boxChart_lt (n N : ℕ) :
    ∀ j : Fin (n * N), (boxChart n N j).1 < N ∧ (boxChart n N j).2 < n := by
  intro j
  have hnN : 0 < n * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at hnN)
  simp only [boxChart]
  refine ⟨?_, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm N n]; exact j.isLt)
  · omega

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
    "the classifier is run with ONE lift rule" + rev-6 canonRoot pinning);
(vi) VERTEX READ-OFF [N-4 sign-off, 2026-07-28 — §9 F-3]: the recorded transported vertex
    value is f's actual vertex digit in the designated next key's development (the
    layer-2 terminal seam's minimal additive repair; the wave-4 seam registry copies this
    clause into MovesT's `eligible` re-key). -/
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
  (ν.lift = (polOM p F).liftOf ν ∧ ((ν.zbar : Fˣ) : F) = canonRoot ν) ∧
  -- (vi) VERTEX READ-OFF [N-4 SIGN-OFF, 2026-07-28 — §9 F-3's minimal ADDITIVE repair of
  -- the layer-2 TERMINAL seam]: at the read's window vertex — slot μ of f's development
  -- in the DESIGNATED NEXT key — f's actual frame-i residual digit IS the recorded
  -- transported vertex value (D.8's (VERTEX) normalization `T(μ·m̂ − a)`/`z̄^{−μm̂}` is
  -- folded into `Node.vtx`), stated in the `σ.digPrime zbar (B μ)` vocabulary of
  -- `L5_landVertexDigit`. Additive-only: U19/U23/U24 remain projections; U21 is a
  -- DERIVATION from this clause (never (HV) itself). NON-VACUITY: U31's gate re-run with
  -- this clause is MANDATORY (fleet phase) — if the concrete witness cannot discharge it,
  -- the clause is over-strengthened and the design returns to F-3 (the GAP-4 mechanism).
  (∀ (Bh : ℕ → Polynomial ℤ_[p]) (Nh : ℕ),
      IsDevelopment Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) Bh Nh →
      ν.σ.digPrime ν.zbar (Bh ν.μ) = ν.vtx)

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
  DEFS-REPAIR (2026-07-27, deviation-correction; blueprint §2.2): the note's zero system
  ranges over the frame's OWN tower coordinates — ALL `(b,l) : Coord` with `ht(b,l) < β`,
  unboundedly many levels — while the chart `coordOf` records only the n×N box. The first
  E-phase transcription BOX-TRUNCATED the iff (quantified the zero system over `Fin m`
  only), over-claiming its ← direction; machine-refuted (`PresentSeed` uninhabited via
  `f = C(p^N)`: all box digits vanish, `σ.w (B 0)` finite — `scratch_U9_presentSeed_false`,
  now dead). Repaired form: the iff carries the note's own losslessness proviso as a
  CHART-COVERAGE GUARD — the law fires exactly when `coordOf` records the ENTIRE literal
  zero system of `(j, β)`, which is the note's (ZC-c) side condition "for every N ≥ 1 + the
  largest constrained level" / C.2's `N(H,Z)` box-size rule, rendered per-threshold. The
  ⊆-consumption sites (U9/U10) hold `InBox`/`hN`-type hypotheses that discharge the guard
  at every recorded threshold; blueprint D5 statement UNCHANGED (the quote is the contract).
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
        -- CHART-COVERAGE GUARD (the DEFS-REPAIR): the chart records the ENTIRE literal
        -- zero system {(b,l) : ht(b,l) < β, b ∈ blk(B_j)} of the frame's own tower
        -- coordinates — the note's (ZC-c)/C.2 box-size proviso, per-threshold.
        (∀ cc : Coord, (H.nodes[i]'hi).fineSlot cc.2 = j → H.htH i cc < β →
            ∃ c : Fin m, coordOf c = cc) →
        ((B j = 0 ∨ β ≤ ((H.nodes[i]'hi).σ.w (B j) : ℚ) / (H.strFrame i : ℚ)) ↔
          (∀ c : Fin m, (H.nodes[i]'hi).fineSlot (coordOf c).2 = j →
            H.htH i (coordOf c) < β → x c = 0))
  pres_attain : ∀ (i : ℕ) (hi : i < H.nodes.length) (S : Finset (Fin m)),
      IsValueSupport H coordOf i (H.nodes[i]'hi) S →
      ∀ (x : Fin m → ZMod p) (f : Polynomial ℤ_[p]), pres i x f →
      ∀ d : Fin m → ZMod p,
        ∃ (x' : Fin m → ZMod p) (f' : Polynomial ℤ_[p]), pres i x' f' ∧
          (∀ c ∉ S, x' c = x c) ∧ (∀ c ∈ S, x' c = d c)
  /-- Θ-NORMALIZATION [N-QUEUE SIGN-OFF LAW, 2026-07-28 — the D5-fence residue the
  U9b/U9c records landed exactly where the blueprint's residue rule predicted]: the move
  map `Θ_i` carries NO correction at frame-(i+1) VALUATION CONTENT — coordinates whose
  height sits at-or-below the step floor are `Θ_i`-LITERAL. This is §C C.1.5(2)'s
  normalized re-presentation ("No carries occur in valuation content", MOVES 3984–3988)
  — CONDITIONAL note content, hence a named seed law (HC-1's to discharge), never the
  unconditional `IsFreshAttach` spec (the DC-3 lesson). Consumer: U9c's strip solves
  (post-DC-3 a chosen-system strip solve is `−corr`; literal zero ⟺ the correction
  vanishes); U10c's steps consume the same law at i > 0. -/
  theta_norm : ∀ (i : ℕ), i < H.nodes.length →
      ∀ c : Fin m,
        ((H.htH (i+1) (coordOf c) : ℚ) : WithBot ℚ) ≤ H.floorH (i+1) (coordOf c).2 →
        ∀ x : Fin m → ZMod p, Theta i x c = x c
  /-- ROOT-SHAPE [N-QUEUE SIGN-OFF LAW, 2026-07-28 — the U9c obstruction-(ii) repair,
  §9 F-6's sibling]: the ROOT read's factor interior carries NO exact-valuation (value)
  coordinate — the blueprint sketch's "value pins sit at the rim by the root band's
  shape" (§B2-DEF D.4's root case), given its Lean carrier as a seed law. NOTE the form:
  the escalation record's draft `μ·childWidth ≤ s0·Dwidth` is FALSE at the U27/U31 gate
  node (`s0 = 0` with span slots crossing the interior but every interior LEVEL SET
  EMPTY); the value-coordinate-free form below is the faithful weakening — it is what
  U9c's value-pin exclusion actually consumes, and it HOLDS at the gate (heights 0,
  slot valuations ≥ 1). Consumer: U9c (interior pins are then STRIP pins). -/
  root_shape : ∀ (h0 : 0 < H.nodes.length) (c : Fin m),
      (coordOf c).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      ¬ IsValueCoord H coordOf 0 (H.nodes[0]'h0) c
  /-- STEP-READ VALUE-INTERIOR EXCLUSION [QUEUE ITEM 17 SIGN-OFF LAW, 2026-07-31 — the
  U10c designer addendum (Q8-class D5-fence event); the U10c third-prover record's exact
  named residue]: NO read's factor interior carries an exact-valuation (value)
  coordinate — value pins are the (ZC-b) RIM LEADS (`ZCData` docstring, MovesC/Defs:
  "(ZC-b) LEADS AT RIM — every other pin is at a rim base index"; §C C.1(ii)'s rim rule
  keeps the DIG leads at-or-beyond the read's factor interior `μ_r·cW_r`). This is
  `root_shape`'s all-reads generalization — that field is the `r = 0` instance, KEPT for
  byte-stability of U9c's consumption — with the SAME faithful weakening (the value-
  COORDINATE-free form, not the refuted `μ·childWidth ≤ s0·Dwidth` draft; see
  root_shape's docstring). Consumer: U10c (`zc_step_interiorZero` — interior pins of a
  step read are then STRIP pins or Θ-literal old zeros, closing `zc_step`). Discharged
  at U27's gate by the root_shape arithmetic (single-read history). -/
  step_shape : ∀ (r : ℕ) (hr : r < H.nodes.length) (c : Fin m),
      (coordOf c).2 < (H.nodes[r]'hr).μ * (H.nodes[r]'hr).childWidth →
      ¬ IsValueCoord H coordOf r (H.nodes[r]'hr) c

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
  classical
  -- Support of a strip clause is the singleton at its coordinate.
  have hStrip : ∀ c : Fin (n * N),
      ((C1_stripClause (p := p) c).choose).support = {c} :=
    fun c => (C1_stripClause (p := p) c).choose_spec.1
  -- Support of a value clause is its slot's level set.
  have hVal : ∀ (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j),
      (valueClause H n N S vOf i hi j hsp).support
        = levelSet H n N i (H.nodes[i]'hi) j := by
    intro j hsp
    exact (C1_TYP_toClause
      (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
        ⟨j, hsp, fun c => Iff.intro
          (fun hc => (Finset.mem_filter.mp hc).2)
          (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
      (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
      (levelSet H n N i (H.nodes[i]'hi) j).card
      (card_fin_fun p _)).choose_spec.1
  -- Level sets of distinct span slots are disjoint (distinct fine slots).
  have hLSdisj : ∀ (j₁ j₂ : ℕ), j₁ ≠ j₂ →
      Disjoint (levelSet H n N i (H.nodes[i]'hi) j₁)
        (levelSet H n N i (H.nodes[i]'hi) j₂) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    unfold levelSet at hc1 hc2
    rw [Finset.mem_filter] at hc1 hc2
    exact hne (hc1.2.1.symm.trans hc2.2.1)
  -- A non-value coordinate cannot lie in any span slot's level set.
  have hCross : ∀ (c : Fin (n * N)),
      ¬ IsValueCoord H (boxChart n N) i (H.nodes[i]'hi) c →
      ∀ (j : ℕ), (H.nodes[i]'hi).spanSlot j →
        c ∉ levelSet H n N i (H.nodes[i]'hi) j := by
    intro c hnv j hsp hc
    unfold levelSet at hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, hfs, hht⟩ := hc
    exact hnv ⟨by rw [hfs]; exact hsp, by rw [hfs]; exact hht⟩
  -- Split the list into strips ++ values.
  unfold mkFreshClauses
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · -- strips are pairwise disjoint (distinct singletons)
    rw [List.pairwise_map]
    have hnd : ((stripSet H n N i (H.nodes[i]'hi)).toList).Pairwise (· ≠ ·) :=
      Finset.nodup_toList _
    refine hnd.imp ?_
    intro a b hab
    rw [hStrip a, hStrip b]
    exact Finset.disjoint_singleton.mpr hab
  · -- value clauses are pairwise disjoint (distinct slots)
    rw [List.pairwise_map]
    have hnd : ((valueSlots H n N i (H.nodes[i]'hi)).attach.toList).Pairwise (· ≠ ·) :=
      Finset.nodup_toList _
    refine hnd.imp ?_
    intro a b hab
    rw [hVal a.1 (valueSlots_spanSlot a.2), hVal b.1 (valueSlots_spanSlot b.2)]
    exact hLSdisj a.1 b.1 (fun heq => hab (Subtype.ext heq))
  · -- a strip and a value clause are disjoint
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨jh, hjh, rfl⟩ := hy
    rw [hStrip c, hVal jh.1 (valueSlots_spanSlot jh.2), Finset.disjoint_singleton_left]
    refine hCross c ?_ jh.1 (valueSlots_spanSlot jh.2)
    rw [Finset.mem_toList] at hc
    unfold stripSet at hc
    rw [Finset.mem_filter] at hc
    exact hc.2.2

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
clause its whole level set — the DIG re-presentation's pinned set), (3) strip coordinates
solve BY the strip's own transported equation — the solved value zeroes the Θ-IMAGE's
coordinate — and (4) zero-solve transport (C.1.5(2): old zeros survive as zeros OF THE
Θ-IMAGE — the transported equation, exactly `C0_pinTransport`'s constructed solve shape).
Existence of such a `D'` from `C0.pinTransport` + the strip/value pin-attachment
constructor is U7's obligation.
DC-2 (2026-07-28, deviation-correction — blueprint §2.2; the §9 F-7 authorization,
executed): clause (1) originally read the fresh locus at `x` (`fd.sat x`), where the
blueprint's normative U7 display — and the FROZEN `JetSetup.recursion` field type it
mirrors (`stratum i (Theta i x)`, MovesC/Defs.lean 872–873) — read it at `Θ x`. That
E-phase elaboration bug made U7's `mkSigma_recursion` unprovable as stated (its in-file
STOP-THE-LINE record: the forced reduction demanded `Θ`-invariance of the fresh locus,
which nothing supplies). Repaired to `fd.sat (Θ x)`; blueprint statement unchanged.
DC-3 (2026-07-28, deviation-correction — blueprint §2.2 class; the K2 diagnosis): clauses
(3)/(4) carried the SAME untransported-coordinate bug one clause over — they demanded
LITERAL-zero solves in the NEW coordinates (`∀ g, D'.solve c g = 0`) where the frozen
recursion keying (everything at `Θ x`) and the PROVED `C0_pinTransport` (its constructed
transported solve is `D.solve∘Θ-image − corr`, i.e. the solved value zeroes the Θ-image,
NOT the new coordinate) demand the transported equation. Post-DC-2 that made clauses
(1)+(3) JOINTLY UNSATISFIABLE at any lawful seed whose `Theta` carries a nonzero
correction on a strip coordinate — machine-refuted from U27's gate seed + the constant
unitriangular shift (`scratch_U7_recursion_false.lean`, now dead; the refutation's own
header records the blueprint U7 display as NOT refuted). The blueprint's D7 fixes only
the solution-set/pin CARRIER ("The (ZC)-relevant geometry … is settled by U9/U10, not by
this definition"); clauses (3)/(4) are E-phase ADDENDA (MANIFEST deviation: they make
U9c/U10c statable of the chosen system) and are here repaired to the Θ-composed form.
The LITERAL-zero content ((ZC-a), C.1.5's "No carries occur in valuation content",
MOVES 3984–3988) is CONDITIONAL note content; its Lean carrier is the pending
Θ-normalization zcSeed law (D5 fence, U9b/U9c records) — never this unconditional spec. -/
def IsFreshAttach {p m : ℕ} (D : Locus p m)
    (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) (fd : FreshData p m)
    (D' : Locus p m) : Prop :=
  (∀ x, D'.IsSolution x ↔ (D.IsSolution (Θ x) ∧ fd.sat (Θ x))) ∧
  (∀ c : Fin m, D'.pinned c = true ↔
    (D.pinned c = true ∨ ∃ cl ∈ fd.clauses, c ∈ cl.support)) ∧
  (∀ c : Fin m, (∃ cl ∈ fd.clauses, cl.support = {c} ∧ ∀ x, (cl.sat x ↔ x c = 0)) →
    ∀ x : Fin m → ZMod p, x c = D'.solve c (fun j _ => x j) → Θ x c = 0) ∧
  (∀ c : Fin m, D.pinned c = true → (∀ g, D.solve c g = 0) →
    ∀ x : Fin m → ZMod p, x c = D'.solve c (fun j _ => x j) → Θ x c = 0)

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

/-! ## Addenda (elaboration helpers, MovesD-poolProj pattern; N-queue Defs addenda) -/

/-- [N-2 ADDENDUM, 2026-07-28 — §9 F-1's completed eligibility narrowing] The COMPLETE
D.10 eligibility of a recentering node (MOVES 2583–2671): unramified frame, nonzero
recorded center, the (S6b)/(I-aug) threshold. Necessity of all three + joint sufficiency
are machine-checked in U25 (`recenterLiftSpec_forces_frame_e_one`,
`recenterLiftSpec_forces_center_ne_zero`, `recenterLiftSpec_of_eligible`). Carried by
U25's final-read guard (interior recenterings close from coherence); under `ReadsOf`,
clause (iv)'s final `LandingKey` discharges it outright — runs need no extra hypothesis. -/
def D10Eligible {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) : Prop :=
  ν.σ.e = 1 ∧ ν.center ≠ 0 ∧ ν.σ.wPrev ν.σ.Φ < (ν.σ.h : ℤ)

/-- [N-5 ADDENDUM, 2026-07-28 — §9 F-6's designed minimal addition] §B2-DEF D.4's ROOT
clause, as a named history hypothesis: nonnegative root intercept datum (`ustar ≥ 0`) and
"every side slope ≥ 1" (at the root `Dwidth = 1`, `STR = 1` give `slope = h/e`, so
`1 ≤ slope` IS D.4's clause). U11 is REFUTABLE without it (`ustar := −5` junk shapes
inhabit the Lean shape universe — `ShapeWF` carries no height law); HC-1's seed
constructions sit over the decided cluster strata, where D.4's root clause is the note's
own standing hypothesis — the content lives there. Carried by U11/U13/U15. -/
def RootD4 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) : Prop :=
  ∀ h0 : 0 < H.nodes.length,
    0 ≤ (H.nodes[0]'h0).ustar ∧ 1 ≤ (H.nodes[0]'h0).line.slope

/-- [K3 ADDENDUM, 2026-07-28 — HISTORICAL; DEAD as-built, see below] READ ADJACENCY
along a history: every consecutive read's window reaches its parent's standing vertex
(`s0 + wSide = μ`, the U21 (HV) hypothesis form).

AS-BUILT STATUS (2026-07-30 verify-2 fold-in): this def has ZERO consumers in the
corpus (grep-verified: its only occurrences are this definition, the Defs header K3
line, and the scratch refutation file). It was introduced as the K3 guard on U18's
uniqueness after `lean/scratch_U18_unique_false.lean` refuted the unguarded form —
but the `AdjacentReads`-GUARDED U18 was ITSELF refuted the same round
(`lean/scratch_U18_adjacent_refuted.lean` compiles green: refuted as insufficient),
and the as-built `presentNorm_unique` (U18_unique.lean REV 3, U18-ADJUDICATION) is
keyed by `HistGalTransport` with these guards REMOVED. Do NOT read this def as the
active uniqueness repair; it is retained as a dead named-hypothesis object pending
wave-4 disposal. -/
def AdjacentReads {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) : Prop :=
  ∀ (i : ℕ) (hi1 : i + 1 < H.nodes.length),
    (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega : i < H.nodes.length)).μ

/-- [U14 addendum] The fresh band on RAW coordinates (the `inFreshBand` formula off the
chart — NP-ID's ⊆-direction carrier: band levels, not box positions, are what `NPband`
bounds). At `c = coordOf j` this is literally `inFreshBand`. -/
def inFreshBandC {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n : ℕ) (i : ℕ) (ν : Node p F) (c : Coord) : Prop :=
  c.2 < H.prevRim n i ∧
  H.floorH i c.2 < ((H.htH i c : ℚ) : WithBot ℚ) ∧
  H.htH i c ≤ ν.slotVal (ν.fineSlot c.2)

/-- [K2 ADDENDUM, 2026-07-28 — the mkSigma-recursion disposition] The blueprint's
pre-named PER-STEP CONDITION (D5 zcSeed docstring: "fresh clauses cut freshly = their
supports are UNPINNED on the prior state"), named as a hypothesis object per the U25
pattern: read `i`'s fresh supports carry no pin of the prior state. FREE at i = 0
(nothing is pinned before the root read — `U7.mkSigma_recursion_zero`); its per-step
discharge at i > 0 is U10's (ZC)+DOM geometry (U9's at the root). Carried by U7's
restated `mkSigma_recursion` and threaded through U13/U15/U16; the BARE ∀-i recursion
was refuted-as-underivable on junk histories (U7's POST-DC-3 record) and is RETIRED. -/
def SeedFreshUnpinned {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) : Prop :=
  ∀ (i : ℕ) (hi : i < H.nodes.length) (c : Fin (n * N)),
    (mkSigma H n N S vOf i).pinned c = true →
    ¬ ∃ cl ∈ (mkFresh H n N S vOf i hi).clauses, c ∈ cl.support

/-- [Gate addendum] The ambient field of the p = 2 order-0 gates (U27/U31): GF(4) — big
enough for the n = 2 inert read's residue growth. -/
abbrev F4 : Type := GaloisField 2 2

/-- [Gate addendum] The ambient field of the q′ = 3 separation gate (U28): GF(9). -/
abbrev F9 : Type := GaloisField 3 2

end LeanUrat.MovesJ
