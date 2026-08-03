/-
DITERSUP P1 + JS1/JS2 — `H1/DIterCarrier.lean`: the 𝒟₂ carrier interface (the
application-INDEPENDENT layer of the DIterJunctionSupplier program).

Sources (statement shapes transcribed VERBATIM where a display exists):
* `lean/notes/openmath/DITERSUP_STMT_2026-08-08.md` §S3 (the 𝒟₂ carrier display:
  `DIterCarrier`, `δ₂`, `InnerIntegral`, `IterLaw`) and §S4 GATES JS1–JS3
  (`gateJS1_cocycle_assoc`, `gateJS2_dreal_degeneration` displays).
* `lean/notes/openmath/DITER_RESTATE_2026-08-08.md` §S2 (D-ITER statement of record)
  and §S3 (the consumable spec: carrier / cocycle / sanity gates / cyclic fence).

HONESTY LEDGER (what is PROVED vs HYPOTHESIS-STYLE vs DESIGN-OWED):
* PROVED (Lean-core, this file): `DIterCarrier.δ₂_cocycle` (outer-carry cocycle
  identity FROM the `OuterTrackAdd` hypothesis); `gateJS1_cocycle_assoc` (JS1, WITH
  the `OuterTrackAdd` hypothesis added — see DEVIATION below); `gateJS2_dreal_
  degeneration` (JS2, exactly as displayed — no added hypotheses);
  `DIterCarrier.iterLaw_iterCocycle` (every carrier hosts a formula-cocycle
  satisfying `IterLaw` — interface non-vacuity); the two concrete witnesses
  (`witnessOuterDReal` e₀ = 1, `witnessInnerE1` e₁ = 1) with their `InnerIntegral`/
  `OuterTrackAdd`/non-triviality legs and fired JS1/JS2 instances; and
  `gateJS1_freeTracks_false` (compiled countermodel: the JS1 display WITHOUT the
  track law is FALSE on the free-field interface).
* HYPOTHESIS-STYLE (the DensityFoundation genre — honest Props consumed as named
  hypotheses, NEVER asserted): `IterLaw` (the accepted law enters Lean ONLY as a
  displayed hypothesis — nothing here machine-checks it); `DIterCarrier.
  InnerIntegral` (probe row B1, sealed — application-derived); `DIterCarrier.
  OuterTrackAdd` (the s₂-track digit-additivity law — application-derived from the
  iterated eq-(12-int) split; the E-phase flag "the s₁/s₂ tracks must be DERIVED
  from eq12 data, not free fields" made concrete).
* DESIGN-OWED STATEMENT SITES (no verbatim display exists; shaped conservatively
  from DITER_RESTATE §S1 + the DITERSUP JS3 comment; review-owed against the
  22-table JSON falsifier record BEFORE any JS3 consumption; consumed by NOTHING
  in this file): `RowNPattern`, `CyclicPresentation`.

DEVIATION RECORD (statement-review flag, trust boundary): the DITERSUP §S4 JS1
display takes only (hLaw : IterLaw D c) (hInt : D.InnerIntegral).  On this
interface (s₁/s₂ FREE fields, per the display's own E-phase flag) that statement
is FALSE — compiled countermodel `gateJS1_freeTracks_false` below (e₀ = 1, e₁ = 2,
s₂ ≡ 1 on evens: c(0,0)·c(0,1) = z̄ ≠ 1 = c(0,1)·c(0,1)).  The shipped
`gateJS1_cocycle_assoc` therefore carries the additional honest hypothesis
`hTrack : D.OuterTrackAdd` (which any eq12-derived instance satisfies
definitionally).  This is a NEW-statement site, not an edit to any existing
theorem; the DITERSUP displays are DISPLAY ONLY — NOT COMMITTED by that note's
own banner.

QUEUE-DISCIPLINE BANNER (quoted from DITERSUP §S4 GATES JS1–JS3): "JS1/JS2 are
theorems ABOUT the interface (provable as soon as the §S3 carrier layer compiles —
they do not need the application, but they are gates OF the supplier program, so
they carry the same banner for queue discipline; JS2's arithmetic is definitional
collapse; JS1 is the carry-bookkeeping identity...".  The J-gates (J1/J2/J3a/J3b)
are NOT here: BLOCKED-ON-APPLICATION (DITERSUP §S0 banner — the three-token repair
is Asvin-gated, NOT applied; nothing here touches `SideReads`, any primed mirror,
or any byte-frozen JuncForge/GlueRun statement).

ITER-LAW STATUS (citation pasted from the ledger block "ITER-LAW ACCEPTED —
2026-08-03", `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`): "Scope as accepted:
the harness tower class (superset of DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose
coincidence restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3
untouched."  Same ledger, r36 sweep wording (pasted): "SCOPE AS ACCEPTED: proved
and ACCEPTED on the harness tower class (standard-lift; a STRICT SUPERSET of
DITER_RESTATE §S2's pinned E₂ = e₀e₁ > 1 setting; coincides with the §S2 display
on the nose restricted to E₂ > 1; the E₂ = 1 leg a harmless COR-3-covered
extension outside the statement of record); RESIDUALS ALL THREE at every site:
(ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; the gr(w₂) semantics wrapper
rides the accepted GRB retarget consumer-side; orders ≥ 3 untouched."  That
acceptance is a numerics + math-level result about the ACTUAL tower cocycle; the
Lean `IterLaw` below is the interface Prop it is consumed through — accepting the
law does NOT discharge any hypothesis in this file.

THE MISSING TIE (displayed open, DITERSUP §S3): the clause binding a cocycle `c`
to the ACTUAL degree-0 composite digit algebra of gr(w₂) (anchor monomials, class
values) requires the order ≥ 2 graded-carrier layer the corpus does not have
(PROJECT_STATE standing obligation 2) — OUT OF SCOPE here; this file is the
INTERFACE layer only, and no gate below pretends to the gr(w₂) semantics.
-/
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H1

universe u

/-- 𝒟₂ carrier data on the canonical (dig-consumed) anchor alphabet.  Indexing is
ℤ/E₂ FIBRED: outer s₂-track mod e₁, inner s₁-track mod e₀ (the iterated eq-(12-int)
split) — NEVER a single-constant cyclic F′[u′]/(u′^{E₂} − ζ′) carrier (the 22/28
byte-frozen refutation, DITER_RESTATE §S1).  [E-phase spelling flags, all standing
(DITERSUP §S3): ℤ-indexing with E₂-periodicity vs `ZMod E₂` — the ℤ-with-`hper`
spelling is taken here; units vs field carrier — `K₂ˣ` is taken for the constants;
the s₁/s₂ tracks must be DERIVED from eq12 data, not free fields, when the gr(w₂)
tie lands — they are FREE FIELDS here (interface layer), which is exactly why the
JS1 gate needs the `OuterTrackAdd` hypothesis (see `gateJS1_freeTracks_false`).]
Statement-review owed at E-phase against the probe harness's exact conventions
(trust boundary: definitions are where errors hide). -/
structure DIterCarrier (K₂ : Type u) [Field K₂] where
  e₀ e₁ : ℕ
  he₀ : 0 < e₀
  he₁ : 0 < e₁
  hE₂ : 1 < e₀ * e₁                 -- composite stage: E₂ > 1
  z₁ zbar : K₂ˣ                     -- INNER constant (frame letter) / OUTER constant (last-read wrap)
  ℓ₀ : ℕ                            -- normalized Bézout inverse (0 ≤ ℓ₀ < e₀, ℓ₀h₀ ≡ 1 [e₀]; the congruence is APPLICATION data — h₀ is not carrier data, so only the range law is carried here)
  hℓ₀ : ℓ₀ < e₀
  γ₂ : ℕ                            -- level-2 abscissa-step generator weight e₁·w₁(Φ₁) + h₁ (application datum, free here)
  s₁ s₂ : ℤ → ℕ                     -- the fibred digit tracks (iterated eq-(12-int) split)
  hs₁ : ∀ γ, s₁ γ < e₀
  hs₂ : ∀ γ, s₂ γ < e₁
  hper : ∀ γ, s₁ (γ + (e₀ * e₁ : ℤ)) = s₁ γ ∧ s₂ (γ + (e₀ * e₁ : ℤ)) = s₂ γ

variable {K₂ : Type u} [Field K₂]

/-- δ₂ — the OUTER carry.  (Verbatim from the DITERSUP §S3 display; ℕ-division is
the floor.) -/
def DIterCarrier.δ₂ (D : DIterCarrier K₂) (γ γ' : ℤ) : ℕ := (D.s₂ γ + D.s₂ γ') / D.e₁

/-- The B1 INTEGRALITY clause (probe row B1, sealed): the inner exponent is exact.
(Verbatim from the DITERSUP §S3 display.)  HYPOTHESIS-STYLE: application-derived;
consumed as a named hypothesis, never asserted at the interface. -/
def DIterCarrier.InnerIntegral (D : DIterCarrier K₂) : Prop :=
  ∀ γ γ', (D.e₀ : ℤ) ∣
    ((D.s₁ γ : ℤ) + D.s₁ γ' - D.s₁ (γ + γ') + D.ℓ₀ * D.γ₂ * D.δ₂ γ γ')

/-- (ITER-LAW) as the carrier's cocycle law — BOTH constants (z̄ outer, z₁ inner)
AND the fibration term ℓ₀γ₂δ₂; the §S2 degenerations are the only collapses.
(Verbatim from the DITERSUP §S3 display, whose status line predates acceptance.)

STATUS of the law itself (pasted from the ledger block "ITER-LAW ACCEPTED —
2026-08-03", `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`): "Scope as accepted:
the harness tower class (superset of DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose
coincidence restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3
untouched."  The e₀ = 1 leg is theorem-backed by Lemma D-REAL (GRB S5.3).  In
Lean this Prop is a HYPOTHESIS carrier: no theorem below asserts it of the real
gr(w₂) data (the tie layer is the displayed missing piece). -/
def IterLaw (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ) : Prop :=
  ∀ γ γ', c γ γ' = D.zbar ^ (D.δ₂ γ γ') *
    D.z₁ ^ (((D.s₁ γ : ℤ) + D.s₁ γ' - D.s₁ (γ + γ') + D.ℓ₀ * D.γ₂ * D.δ₂ γ γ') / D.e₀)

/-- The OUTER TRACK ADDITIVITY law: s₂ is a genuine mod-e₁ digit track (the outer
component of the iterated eq-(12-int) split), not a free function.  HYPOTHESIS-
STYLE (application-derived): every eq12-derived instance satisfies this
definitionally; on the FREE-field interface it is independent (see
`gateJS1_freeTracks_false`), which is why JS1 consumes it explicitly.  NEW
statement site (not in the DITERSUP display) — statement review owed. -/
def DIterCarrier.OuterTrackAdd (D : DIterCarrier K₂) : Prop :=
  ∀ γ γ' : ℤ, D.s₂ (γ + γ') = (D.s₂ γ + D.s₂ γ') % D.e₁

/-- The formula cocycle: every carrier hosts the (ITER-LAW)-shaped cocycle by
construction.  This is the interface's canonical non-vacuity device — it says the
INTERFACE is inhabited, NOT that the gr(w₂) cocycle of any tower satisfies the
law (that is the accepted math-level result + the missing tie layer). -/
def DIterCarrier.iterCocycle (D : DIterCarrier K₂) : ℤ → ℤ → K₂ˣ := fun γ γ' =>
  D.zbar ^ (D.δ₂ γ γ') *
    D.z₁ ^ (((D.s₁ γ : ℤ) + D.s₁ γ' - D.s₁ (γ + γ') + D.ℓ₀ * D.γ₂ * D.δ₂ γ γ') / D.e₀)

/-- `IterLaw` is non-vacuous at every carrier: the formula cocycle satisfies it
definitionally. -/
theorem DIterCarrier.iterLaw_iterCocycle (D : DIterCarrier K₂) :
    IterLaw D D.iterCocycle := fun _ _ => rfl

/-! ## The pure finite-algebra layer (PROVED) -/

/-- Carry-chain bookkeeping over ℕ: dividing a running sum in two carries is the
same as dividing it at once.  (The first lemma of any carry-cocycle argument.) -/
private theorem carry_chain (e a b c : ℕ) (he : 0 < e) :
    (a + b) / e + ((a + b) % e + c) / e = (a + b + c) / e := by
  have hsplit : a + b + c = (a + b) % e + c + e * ((a + b) / e) := by
    have := Nat.mod_add_div (a + b) e
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ he]
  omega

/-- The outer-carry 2-cocycle identity, FROM the track-additivity law.  Pure
finite algebra: this is the standard carry-cocycle computation for the mod-e₁
digit track, and (per the DITERSUP JS1 comment) "the first lemma of any ITER-LAW
proof". -/
theorem DIterCarrier.δ₂_cocycle (D : DIterCarrier K₂) (hTrack : D.OuterTrackAdd)
    (γ γ' γ'' : ℤ) :
    D.δ₂ γ γ' + D.δ₂ (γ + γ') γ'' = D.δ₂ γ' γ'' + D.δ₂ γ (γ' + γ'') := by
  have h₁₂ := hTrack γ γ'
  have h₂₃ := hTrack γ' γ''
  simp only [DIterCarrier.δ₂, h₁₂, h₂₃]
  rw [Nat.add_comm (D.s₂ γ) ((D.s₂ γ' + D.s₂ γ'') % D.e₁)]
  have hL := carry_chain D.e₁ (D.s₂ γ) (D.s₂ γ') (D.s₂ γ'') D.he₁
  have hR := carry_chain D.e₁ (D.s₂ γ') (D.s₂ γ'') (D.s₂ γ) D.he₁
  rw [show D.s₂ γ' + D.s₂ γ'' + D.s₂ γ = D.s₂ γ + D.s₂ γ' + D.s₂ γ'' by omega] at hR
  exact hL.trans hR.symm

/-- GATE JS1 (B0a): the 2-cocycle (associativity) identity.  PROVED, with ONE
honest hypothesis ADDED relative to the DITERSUP §S4 display: `hTrack :
D.OuterTrackAdd`.  DEVIATION RECORD: the display's (hLaw, hInt)-only statement is
FALSE on the free-field interface — compiled countermodel
`gateJS1_freeTracks_false` below — because nothing ties the free s₂ field to a
genuine digit track; every eq12-derived application instance satisfies `hTrack`
definitionally, so the gate's application-facing content is unchanged.
Statement-review flag: NEW statement site (per the note's own banner the display
was DISPLAY ONLY — NOT COMMITTED). -/
theorem gateJS1_cocycle_assoc (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ)
    (hLaw : IterLaw D c) (hInt : D.InnerIntegral) (hTrack : D.OuterTrackAdd) :
    ∀ γ γ' γ'', c γ γ' * c (γ + γ') γ'' = c γ' γ'' * c γ (γ' + γ'') := by
  intro γ γ' γ''
  have hδ : D.δ₂ γ γ' + D.δ₂ (γ + γ') γ'' = D.δ₂ γ' γ'' + D.δ₂ γ (γ' + γ'') :=
    D.δ₂_cocycle hTrack γ γ' γ''
  have he0 : (D.e₀ : ℤ) ≠ 0 := by exact_mod_cast D.he₀.ne'
  obtain ⟨k₁, hk₁⟩ := hInt γ γ'
  obtain ⟨k₂, hk₂⟩ := hInt (γ + γ') γ''
  obtain ⟨k₃, hk₃⟩ := hInt γ' γ''
  obtain ⟨k₄, hk₄⟩ := hInt γ (γ' + γ'')
  rw [hLaw γ γ', hLaw (γ + γ') γ'', hLaw γ' γ'', hLaw γ (γ' + γ'')]
  rw [hk₁, hk₂, hk₃, hk₄, Int.mul_ediv_cancel_left k₁ he0,
    Int.mul_ediv_cancel_left k₂ he0, Int.mul_ediv_cancel_left k₃ he0,
    Int.mul_ediv_cancel_left k₄ he0]
  have hδz : ((D.δ₂ γ γ' : ℤ)) + (D.δ₂ (γ + γ') γ'' : ℤ) =
      (D.δ₂ γ' γ'' : ℤ) + (D.δ₂ γ (γ' + γ'') : ℤ) := by exact_mod_cast hδ
  have hNsum : (D.e₀ : ℤ) * (k₁ + k₂) = (D.e₀ : ℤ) * (k₃ + k₄) := by
    rw [mul_add, mul_add, ← hk₁, ← hk₂, ← hk₃, ← hk₄, ← add_assoc γ γ' γ'']
    push_cast
    linear_combination ((D.ℓ₀ : ℤ) * (D.γ₂ : ℤ)) * hδz
  have hk : k₁ + k₂ = k₃ + k₄ := mul_left_cancel₀ he0 hNsum
  rw [mul_mul_mul_comm, mul_mul_mul_comm, ← pow_add, ← pow_add, ← zpow_add,
    ← zpow_add, hδ, hk]

/-- GATE JS2: the D-REAL degeneration at e₀ = 1 (the theorem-backed leg; ℓ₀ < e₀
= 1 forces ℓ₀ = 0 and s₁ ≡ 0, so the inner factor is trivial).  PROVED exactly as
displayed (DITERSUP §S4) — no added hypotheses; the arithmetic is definitional
collapse. -/
theorem gateJS2_dreal_degeneration (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ)
    (hLaw : IterLaw D c) (he₀ : D.e₀ = 1) :
    ∀ γ γ', c γ γ' = D.zbar ^ (D.δ₂ γ γ') := by
  intro γ γ'
  have hs₁ : ∀ δ : ℤ, D.s₁ δ = 0 := fun δ => by have := D.hs₁ δ; omega
  have hℓ₀ : D.ℓ₀ = 0 := by have := D.hℓ₀; omega
  rw [hLaw γ γ']
  simp only [hs₁, hℓ₀, Nat.cast_zero, zero_mul, add_zero, sub_zero, zero_add,
    Int.zero_ediv, zpow_zero, mul_one]

/-! ## The compiled countermodel (why JS1 needs the track law) -/

/-- A carrier with a BAD (non-eq12) outer track: s₂ ≡ 1 on evens, 0 on odds
(so s₂(0) = 1 — impossible for a genuine digit track, where the digit of 0 is 0).
e₀ = 1, e₁ = 2, z̄ = 2 ∈ ℚˣ, z₁ = 1.  Every structure law of the FREE-field
interface holds; `OuterTrackAdd` fails at (0,0). -/
def badTracksCarrier : DIterCarrier ℚ where
  e₀ := 1
  e₁ := 2
  he₀ := one_pos
  he₁ := two_pos
  hE₂ := by norm_num
  z₁ := 1
  zbar := Units.mk0 (2 : ℚ) two_ne_zero
  ℓ₀ := 0
  hℓ₀ := one_pos
  γ₂ := 3
  s₁ := fun _ => 0
  s₂ := fun γ => 1 - (γ % 2).toNat
  hs₁ := fun _ => one_pos
  hs₂ := fun γ => by dsimp only; omega
  hper := fun γ => ⟨rfl, by dsimp only; omega⟩

theorem badTracksCarrier_innerIntegral : badTracksCarrier.InnerIntegral := by
  intro γ γ'
  simp [badTracksCarrier]

/-- DEVIATION JUSTIFICATION (compiled): the DITERSUP §S4 JS1 display — cocycle
associativity from (hLaw, hInt) ALONE — is FALSE on the free-field interface.
Witness: `badTracksCarrier` at (γ,γ',γ'') = (0,0,1), where the LHS is z̄ = 2 and
the RHS is 1.  (Stated at K₂ = ℚ; a fortiori the ∀-K₂ display shape is
unprovable.)  This is what forces the honest `hTrack` hypothesis in
`gateJS1_cocycle_assoc`, and it concretely instantiates the display's own E-phase
flag that the s₁/s₂ tracks must be eq12-DERIVED, not free fields. -/
theorem gateJS1_freeTracks_false :
    ¬ ∀ (D : DIterCarrier ℚ) (c : ℤ → ℤ → ℚˣ),
        IterLaw D c → D.InnerIntegral →
        ∀ γ γ' γ'', c γ γ' * c (γ + γ') γ'' = c γ' γ'' * c γ (γ' + γ'') := by
  intro h
  have h001 := h badTracksCarrier badTracksCarrier.iterCocycle
    badTracksCarrier.iterLaw_iterCocycle badTracksCarrier_innerIntegral 0 0 1
  have hc00 : badTracksCarrier.iterCocycle 0 0 = Units.mk0 (2 : ℚ) two_ne_zero := by
    norm_num [DIterCarrier.iterCocycle, DIterCarrier.δ₂, badTracksCarrier]
  have hc01 : badTracksCarrier.iterCocycle 0 1 = 1 := by
    norm_num [DIterCarrier.iterCocycle, DIterCarrier.δ₂, badTracksCarrier]
  rw [show ((0 : ℤ) + 0) = 0 by norm_num, show ((0 : ℤ) + 1) = 1 by norm_num] at h001
  rw [hc00, hc01, mul_one, one_mul] at h001
  rw [Units.ext_iff] at h001
  norm_num at h001

/-! ## Concrete witnesses (interface non-vacuity; both §S2 degeneration legs) -/

/-- OUTER witness — the D-REAL e₀ = 1 degeneration leg (per DITERSUP gate J3a's
pricing, this leg is ITER-LAW-FREE: the cocycle collapses to z̄^{δ₂}, the
theorem-backed Lemma D-REAL shape).  Honest scope: this is an ABSTRACT interface
instance (e₀ = 1, e₁ = 2, honest mod-2 outer digit track, z̄ = 2 ∈ ℚˣ), NOT the
row-A application data — no `SideReads`/stage content is touched. -/
def witnessOuterDReal : DIterCarrier ℚ where
  e₀ := 1
  e₁ := 2
  he₀ := one_pos
  he₁ := two_pos
  hE₂ := by norm_num
  z₁ := 1
  zbar := Units.mk0 (2 : ℚ) two_ne_zero
  ℓ₀ := 0
  hℓ₀ := one_pos
  γ₂ := 3
  s₁ := fun _ => 0
  s₂ := fun γ => (γ % 2).toNat
  hs₁ := fun _ => one_pos
  hs₂ := fun γ => by dsimp only; omega
  hper := fun γ => ⟨rfl, by dsimp only; omega⟩

theorem witnessOuterDReal_innerIntegral : witnessOuterDReal.InnerIntegral := by
  intro γ γ'
  simp [witnessOuterDReal]

theorem witnessOuterDReal_outerTrackAdd : witnessOuterDReal.OuterTrackAdd := by
  intro γ γ'
  simp only [witnessOuterDReal]
  omega

/-- JS2 FIRES at the outer witness (e₀ = 1 holds definitionally). -/
theorem witnessOuterDReal_js2 :
    ∀ γ γ' : ℤ, witnessOuterDReal.iterCocycle γ γ' =
      witnessOuterDReal.zbar ^ (witnessOuterDReal.δ₂ γ γ') :=
  gateJS2_dreal_degeneration witnessOuterDReal _ witnessOuterDReal.iterLaw_iterCocycle rfl

/-- ...and non-vacuously so: the outer carry actually fires, c(1,1) = z̄ = 2 ≠ 1. -/
theorem witnessOuterDReal_c11_ne_one : witnessOuterDReal.iterCocycle 1 1 ≠ 1 := by
  have hval : witnessOuterDReal.iterCocycle 1 1 = Units.mk0 (2 : ℚ) two_ne_zero := by
    norm_num [DIterCarrier.iterCocycle, DIterCarrier.δ₂, witnessOuterDReal]
  rw [hval, Ne, Units.ext_iff]
  norm_num

/-- INNER witness — the e₁ = 1 degeneration leg (c = z₁^{δ₁}): e₀ = 2, e₁ = 1,
honest mod-2 inner digit track, z₁ = 3 ∈ ℚˣ, ℓ₀ = 1.  The fibration term is 0
(δ₂ ≡ 0 at e₁ = 1), so `InnerIntegral` is the pure inner-carry integrality —
satisfied by the honest digit track. -/
def witnessInnerE1 : DIterCarrier ℚ where
  e₀ := 2
  e₁ := 1
  he₀ := two_pos
  he₁ := one_pos
  hE₂ := by norm_num
  z₁ := Units.mk0 (3 : ℚ) three_ne_zero
  zbar := 1
  ℓ₀ := 1
  hℓ₀ := one_lt_two
  γ₂ := 1
  s₁ := fun γ => (γ % 2).toNat
  s₂ := fun _ => 0
  hs₁ := fun γ => by dsimp only; omega
  hs₂ := fun _ => one_pos
  hper := fun γ => ⟨by dsimp only; omega, rfl⟩

theorem witnessInnerE1_innerIntegral : witnessInnerE1.InnerIntegral := by
  intro γ γ'
  simp only [witnessInnerE1, DIterCarrier.δ₂]
  omega

theorem witnessInnerE1_outerTrackAdd : witnessInnerE1.OuterTrackAdd := by
  intro γ γ'
  simp [witnessInnerE1]

/-- JS1 FIRES at the inner witness (all three hypotheses discharged concretely). -/
theorem witnessInnerE1_js1 :
    ∀ γ γ' γ'', witnessInnerE1.iterCocycle γ γ' * witnessInnerE1.iterCocycle (γ + γ') γ'' =
      witnessInnerE1.iterCocycle γ' γ'' * witnessInnerE1.iterCocycle γ (γ' + γ'') :=
  gateJS1_cocycle_assoc witnessInnerE1 _ witnessInnerE1.iterLaw_iterCocycle
    witnessInnerE1_innerIntegral witnessInnerE1_outerTrackAdd

/-- ...and non-vacuously so: the inner constant actually fires, c(1,1) = z₁ = 3 ≠ 1. -/
theorem witnessInnerE1_c11_ne_one : witnessInnerE1.iterCocycle 1 1 ≠ 1 := by
  have hval : witnessInnerE1.iterCocycle 1 1 = Units.mk0 (3 : ℚ) three_ne_zero := by
    norm_num [DIterCarrier.iterCocycle, DIterCarrier.δ₂, witnessInnerE1]
  rw [hval, Ne, Units.ext_iff]
  norm_num

/-- The bundled interface non-vacuity: a carrier with a lawful cocycle satisfying
ALL the hypothesis-style laws, with genuinely non-trivial cocycle values. -/
theorem carrier_interface_nonvacuous :
    ∃ (D : DIterCarrier ℚ) (c : ℤ → ℤ → ℚˣ),
      IterLaw D c ∧ D.InnerIntegral ∧ D.OuterTrackAdd ∧ ∃ γ γ' : ℤ, c γ γ' ≠ 1 :=
  ⟨witnessInnerE1, witnessInnerE1.iterCocycle, witnessInnerE1.iterLaw_iterCocycle,
    witnessInnerE1_innerIntegral, witnessInnerE1_outerTrackAdd,
    1, 1, witnessInnerE1_c11_ne_one⟩

/-! ## DESIGN-OWED statement sites for gate JS3 (NOT consumed in this file)

Gate JS3 (row-N NOT-CYCLIC compiled falsifier) is priced M and is NOT this unit;
the DITERSUP §S4 display names `RowNPattern` and `CyclicPresentation` without
displaying them ("Both defs are E-phase statement sites, review-owed against the
22-table JSON record").  The P1 pricing row lists both in the carrier layer, so
they are landed here as HONEST Prop-level statement sites — shaped from
DITER_RESTATE §S1's operationalization ("single non-1 cocycle value + carry
pattern realizable by some relabeling of ℤ/E₂") and the JS3 comment's value-set
template {z₁, z̄, z̄·z₁^b}.  REVIEW-OWED before ANY JS3 consumption, against the
22-table JSON falsifier record; if the probe's operationalization differs (e.g.
diagonal-gauge freedom, exponent conventions), the JS3 unit restates these under
the standing statement-change authority with a ledger trail.  No theorem in this
file consumes either. -/

/-- DESIGN-OWED (see section header).  The row-N VALUE PATTERN abstracted to the
interface: the cocycle's non-1 value set is EXACTLY the three-element table
{z₁, z̄, z̄·z₁^b} (pairwise distinct, all ≠ 1) for some exponent b — the kill-shot
row N (2;2,1,1;2,1,2) genre-(i) failure shape (≥ 2 distinct non-1 values), per
DITER_RESTATE §S1.  [Flags: b : ℕ vs ℤ; no tower-data pins (value-pattern only);
"exactly attained" spelled as cover + three attainment legs.] -/
def RowNPattern (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ) : Prop :=
  ∃ b : ℕ,
    (D.z₁ ≠ 1 ∧ D.zbar ≠ 1 ∧ D.zbar * D.z₁ ^ b ≠ 1) ∧
    (D.z₁ ≠ D.zbar ∧ D.z₁ ≠ D.zbar * D.z₁ ^ b ∧ D.zbar ≠ D.zbar * D.z₁ ^ b) ∧
    (∀ γ γ' : ℤ, c γ γ' = 1 ∨ c γ γ' = D.z₁ ∨ c γ γ' = D.zbar ∨
      c γ γ' = D.zbar * D.z₁ ^ b) ∧
    ((∃ γ γ' : ℤ, c γ γ' = D.z₁) ∧ (∃ γ γ' : ℤ, c γ γ' = D.zbar) ∧
      (∃ γ γ' : ℤ, c γ γ' = D.zbar * D.z₁ ^ b))

/-- DESIGN-OWED (see section header).  A single-constant CYCLIC presentation of
the cocycle on the canonical alphabet: one non-1 value ζ′, and a relabeling θ of
ℤ/E₂ (E₂-periodic, range [0,E₂), surjective on residues — hence bijective) whose
standard carry pattern realizes the cocycle: c(γ,γ′) = ζ′^⌊(θγ + θγ′)/E₂⌋.  This
is the PATTERN-LEVEL operationalization (DITER_RESTATE §S1: "single non-1 cocycle
value + carry pattern realizable by some relabeling of ℤ/E₂") — the shape the
22/28 refutation adjudicated FALSE at composite stages, and the shape the cyclic
fence forbids any discharge to bake in.  [Flags: diagonal-gauge freedom NOT
included (strictest form — the JS3 unit must confirm against the probe's exact
convention); θ additivity NOT required (pattern-level, not algebra-map-level);
carry expressed as ℕ-floor of the label sum.] -/
def CyclicPresentation (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ)
    (ζ' : K₂ˣ) (θ : ℤ → ℕ) : Prop :=
  ζ' ≠ 1 ∧
  (∀ γ γ' : ℤ, c γ γ' = 1 ∨ c γ γ' = ζ') ∧
  (∀ γ : ℤ, θ γ < D.e₀ * D.e₁) ∧
  (∀ γ : ℤ, θ (γ + (D.e₀ * D.e₁ : ℤ)) = θ γ) ∧
  (∀ k : ℕ, k < D.e₀ * D.e₁ → ∃ γ : ℤ, θ γ = k) ∧
  (∀ γ γ' : ℤ, c γ γ' = ζ' ^ ((θ γ + θ γ') / (D.e₀ * D.e₁)))

/-! ## In-file census (expected: Lean-core only — propext, Classical.choice,
Quot.sound; zero sorryAx anywhere) -/

#print axioms LeanUrat.Scaffold.HDischarge.H1.DIterCarrier.iterLaw_iterCocycle
#print axioms LeanUrat.Scaffold.HDischarge.H1.DIterCarrier.δ₂_cocycle
#print axioms LeanUrat.Scaffold.HDischarge.H1.gateJS1_cocycle_assoc
#print axioms LeanUrat.Scaffold.HDischarge.H1.gateJS2_dreal_degeneration
#print axioms LeanUrat.Scaffold.HDischarge.H1.badTracksCarrier_innerIntegral
#print axioms LeanUrat.Scaffold.HDischarge.H1.gateJS1_freeTracks_false
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessOuterDReal_innerIntegral
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessOuterDReal_outerTrackAdd
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessOuterDReal_js2
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessOuterDReal_c11_ne_one
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessInnerE1_innerIntegral
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessInnerE1_outerTrackAdd
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessInnerE1_js1
#print axioms LeanUrat.Scaffold.HDischarge.H1.witnessInnerE1_c11_ne_one
#print axioms LeanUrat.Scaffold.HDischarge.H1.carrier_interface_nonvacuous

end LeanUrat.Scaffold.HDischarge.H1
