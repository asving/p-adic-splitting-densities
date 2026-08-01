/-
BP_IV §1.2 — the order-r census carrier root (`CensusCore.lean`).
Units in this file: C0a (`CensusData`) · C0b (`d/period/J`) · C0c
(`wt/Gset/attainDim/s`) · C0d (`onLineSlots`) · H1 (`ADMFull`, statement
verbatim — landed by unit C3 as prerequisite; declared immediately after the
derived definitions, per BP_IV §1.0).
This module imports no value-side module (import graph: CensusCore → Hyps →
Census, never a cycle).
-/
import Mathlib

/-!
# The order-r census carriers [wave IV-0a]

**PROVENANCE (unit C0a; BP_IV §1.2).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement verbatim) and §1.0
  (module/namespace placement).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` (§§1, 5.1, the r4
  FULL-attainment form) and M08 (`M08-cl6-general_fable.md` §2, Theorem 2).
* Imports: `Mathlib` only.
-/

namespace LeanUrat.Scaffold

/-- The order-r census datum: the ledger of stage triples (e_i, h_i, f_i),
    i = 0..r, with e_i, f_i ≥ 1.  Derived: d = ∏ f_i (census field degree —
    O-9's DELTA-3 index fix: d = f₀⋯f_r, NOT f₀⋯f_{r−1}), the period
    e = ∏ e_i, the slot-weight function wt on the mixed-radix φ-monomial index
    set J (a Fintype), the graded pieces G_β, and s(β) = #{j | wt j ≤ β}.

    **ADM-U0 REPAIR RECORD (HDISCHARGE_H3 §1.3(b) (F-ADM-1), definition-change
    authority).**  The BP_IV §1.2 display carried a fourth axiom row
    `triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i`, which JOINTLY with `h_coprime`
    forces e_i = 1 at every stage i ≥ 1 (e_i ∣ h_i ∧ gcd(h_i, e_i) = 1 ⟹
    e_i = 1 — the compiled degeneracy witnesses, git history at the pre-repair
    `Census.lean`), so the landed carrier could express NO ramified stage-≥1
    type (the K6 datum e₁ = 3, h₁ = 2 fails 3 ∣ 2).  Adjudicated against the
    math source of record, O-9 rev5 §1 (the pinned data sheet): the type data
    is `λ_i = −h_i/e_i in lowest terms` — COPRIMALITY ONLY, e_i > 1 explicitly
    live at stages ≥ 1 (warning display 1).  The row was a transcription
    defect of the blueprint display (the C1/C2 `ledgerE` precedent, REVISION 3)
    and is DROPPED; `he/hf/h_coprime` are the complete axiom set. -/
structure CensusData where
  r : ℕ
  e : Fin (r + 1) → ℕ
  h : Fin (r + 1) → ℕ
  f : Fin (r + 1) → ℕ
  he : ∀ i, 1 ≤ e i
  hf : ∀ i, 1 ≤ f i
  h_coprime : ∀ i, Nat.Coprime (h i) (e i)

/-!
**PROVENANCE (unit C0b; BP_IV §1.2, wave IV-0b; REVISED at BP_IV REVISION 3,
mop-up adjudication).**  Derived defs: `d` = ∏ f_i (the census field degree,
O-9's DELTA-3 index fix: d = f₀⋯f_r, NOT f₀⋯f_{r−1}), the LEDGER period, and
the mixed-radix φ-monomial index set `J` (a Fintype — instance supplied
immediately after the def).

**THE REVISION-3 CARRIER FIX (the C1/C2 adjudication; warrant: the compiled
countermodels `C1Refutation.not_admFull_cmC1` / `C2Refutation.*` of the
pre-revision `Census.lean`, retired with this fix — see git history at
33656d2 and BP_IV REVISION 3).**  The §1.2 display gave stage 0 a full
`Fin (e 0) × Fin (f 0)` pair in `J` and an `e 0` factor in `period`; the O9
ledger (rev5 §§1–2, the math source of record) has stage 0 contributing the
`f₀` monomials `x^{j₀}` ONLY (φ₀ = x, weight 0 — "m = f₀ = d at r = 0") and
the period `e = e₁⋯e_r` (NO e₀ factor; "the O9 convention is e₀ = 1").
Against the display, the O9-scoped laws C1 (r = 0 automaticity — a ROOT (ADM)
row clause) and C2 (the r = 1 criterion) are FALSE (countermodels at e₀ = 2);
the carrier transcription, not the laws, was wrong.  The fix: the LEDGER
stage multiplicity `ledgerE` (:= 1 at stage 0, e_i at stages i ≥ 1) replaces
`e i` in the DERIVED defs `J`/`period`/`wt`-radix.  The stage-0 FIELDS
`e 0`/`h 0` remain carrier data (consumed by C4c's canonical level-1 polygon,
which is untouched by this fix).
-/

namespace CensusData

def d (D : CensusData) : ℕ := ∏ i, D.f i

/-- The LEDGER stage multiplicity (REVISION 3): stage 0 rides at multiplicity
    1 (φ₀ = x contributes the `f₀` monomials only — O9 rev5 §2), stages i ≥ 1
    at their ramification `e i`. -/
def ledgerE (D : CensusData) (i : Fin (D.r + 1)) : ℕ :=
  if i.1 = 0 then 1 else D.e i

@[simp] theorem ledgerE_zero (D : CensusData) : D.ledgerE 0 = 1 := by
  simp [ledgerE]

theorem ledgerE_of_ne_zero (D : CensusData) {i : Fin (D.r + 1)} (hi : i.1 ≠ 0) :
    D.ledgerE i = D.e i := by
  simp [ledgerE, hi]

theorem ledgerE_pos (D : CensusData) (i : Fin (D.r + 1)) : 1 ≤ D.ledgerE i := by
  unfold ledgerE
  split_ifs
  · exact le_rfl
  · exact D.he i

/-- The LEDGER period `e = e₁⋯e_r` (REVISION 3: no `e 0` factor — O9 rev5 §1,
    "e = 1 at r = 0"). -/
def period (D : CensusData) : ℕ := ∏ i, D.ledgerE i

def J (D : CensusData) : Type :=
  (i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)

/-- `J` is a Fintype (the blueprint carrier docstring: "the mixed-radix
    φ-monomial index set J (a Fintype)"). -/
instance instFintypeJ (D : CensusData) : Fintype D.J :=
  inferInstanceAs
    (Fintype ((i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)))

instance instDecidableEqJ (D : CensusData) : DecidableEq D.J :=
  inferInstanceAs
    (DecidableEq ((i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)))

/-!
**PROVENANCE (unit C0c; BP_IV §1.2, wave IV-0c).**  The derived slot-weight
layer: `wt` (signature verbatim from the blueprint; body = the mixed-radix
φ-monomial weight of the O9 ledger, per the C0 unit-table row "wt = the
mixed-radix φ-monomial weight (O9 ledger LED)"), then `Gset`, `attainDim`, `s`
(all three verbatim from the blueprint, `-- unit C0c` annotations).

The `wt` body transcribes `O9_phaseB_verifybrief_rev5.md` §4 (the slot ledger,
Lemma LED's weight data) into the census-datum coordinates:

* ledger weights: `wt(𝐣) = Σ_i j_i · w(φ_i)`, where stage 0 contributes weight
  0 — §2's r = 0/r = 1 automaticity discussion: the `f₀` choices of `j₀` ride
  "at weight contribution 0" (φ₀ = x);
* stage weights by the pinned (P3) V-recursion (GMN Prop 2.7(4) + Thm 2.11):
  `w(φ_i) = e_i·V_i + h_i` with `V₁ = 0` and `V_{i+1} = e_i·f_i·(e_i·V_i + h_i)`
  — §2's worked data: `w(φ₁) = e₁V₁ + h₁, V₁ = 0`; `V̂ = e₁f₁·w(φ₁)`;
* the per-stage mixed-radix split of the blueprint's `Fin (e i) × Fin (f i)`
  pair: `j_i = a_i + e_i·b_i` (`a_i` the mod-`e_i` class digit, `b_i` the
  `t < f_i` digit) — §2's class decomposition `j₁ = j₁* + t·e₁, 0 ≤ t < f₁`.
-/

/-- The (P3) V-recursion ladder (GMN Prop 2.7(4) + Thm 2.11), ℕ-indexed for
    structural recursion: `V₀ := 0` (stage-0 slot, never consumed — stage 0
    carries weight 0), `V₁ := 0`, and `V_{i+2} = e_{i+1}·f_{i+1}·(e_{i+1}·
    V_{i+1} + h_{i+1})` for in-range stages (out-of-range indices return 0;
    `wt` only reads stages `i ≤ r`). -/
def Vrec (D : CensusData) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (i + 2) =>
    if hi : i + 1 < D.r + 1 then
      let k : Fin (D.r + 1) := ⟨i + 1, hi⟩
      D.e k * D.f k * (D.e k * Vrec D (i + 1) + D.h k)
    else 0

/-- The stage weight `w(φ_i)`: 0 at stage 0 (φ₀ = x — O9 §2: the `j₀` digit
    rides at weight contribution 0), and `e_i·V_i + h_i` at stages `i ≥ 1`
    (O9 §4, the slot ledger, via the (P3) V-recursion `Vrec`). -/
def wphi (D : CensusData) (i : Fin (D.r + 1)) : ℕ :=
  if i.1 = 0 then 0 else D.e i * D.Vrec i.1 + D.h i

/-- unit C0c — the mixed-radix φ-monomial slot weight (O9 ledger LED):
    `wt 𝐣 = Σ_i j_i · w(φ_i)` with the per-stage digit `j_i = a_i + e_i·b_i`
    read off the `Fin (ledgerE i) × Fin (f i)` pair (REVISION 3: the ledger
    radix — at stage 0 the class digit collapses, `j₀ = b₀ < f₀`; at stages
    i ≥ 1 `ledgerE i = e i` and the digit is unchanged) and
    `w(φ_i) = wphi i`. -/
noncomputable def wt (D : CensusData) : D.J → ℕ :=
  fun j => ∑ i, ((j i).1.1 + D.ledgerE i * (j i).2.1) * D.wphi i

noncomputable def Gset (D : CensusData) (β : ℕ) : Finset D.J :=
  Finset.univ.filter
    (fun j => D.wt j % D.period = β % D.period ∧ D.wt j ≤ β)         -- unit C0c

noncomputable def attainDim (D : CensusData) (β : ℕ) : ℕ := (D.Gset β).card

noncomputable def s (D : CensusData) (β : ℕ) : ℕ :=
  (Finset.univ.filter fun j : D.J => D.wt j ≤ β).card                -- unit C0c

/-!
**PROVENANCE (unit C0d; BP_IV §1.2, wave IV-0b).**  Signature verbatim from the
blueprint (`-- unit C0d`); the body is DERIVED (the blueprint displays no body)
and is hereby flagged for division-lead/Codex ratification per the trust
boundary (definitions are where errors hide):

* O9 §2 (the TRI bullet): the w-values attained on `{deg < m} \ {0}` are
  exactly `{e·v + wt(𝐣) : v ≥ 0, 𝐣 a ledger index}` — the ON-LINE lattice
  values.  The census carrier holds no polygon datum (no face endpoints, no
  `U₀/ℓ/K_D`), so the carrier's canonical finite slot set is the `v = 0`
  fundamental layer: the ledger's own attained weights, `wt(J)` as a Finset.
* Fit with the unit table: C1's sketch "at r = 0 … count the f₀ on-line j
  directly" reads off exactly this image (at r = 0 the slots collapse to the
  weights of the single-digit ledger); C3 gets `Finset.decidableBAll` over
  this Finset; H1's `ADMFull` quantifies `∀ β ∈ D.onLineSlots`.
* NOT chosen (recorded to prevent re-attempts): all on-line lattice points
  `≤ max wt` in attained classes — refuted against C1 (at r = 0 it contains
  class points below the class weight, where `attainDim = 0 ≠ d`, breaking
  the blueprint's r = 0 automaticity row).
-/

/-- unit C0d — the on-line lattice slots of the census datum: the Finset of
    ledger-attained slot weights `{wt 𝐣 : 𝐣 ∈ J}` (O9 §2 TRI bullet's `v = 0`
    fundamental layer of the on-line lattice `{e·v + wt(𝐣)}`).  Consumed by
    `ADMFull` (unit H1: every on-line slot FULLY attained) and the C1–C3
    layer. -/
noncomputable def onLineSlots (D : CensusData) : Finset ℕ :=
  Finset.image D.wt Finset.univ

end CensusData

/-!
**PROVENANCE (unit H1; BP_IV §1.0).**  Statement transcribed VERBATIM from the
blueprint ("In `CensusCore.lean`, immediately after `CensusData` and its
derived definitions").  Landed by unit C3 as its compile-time prerequisite
(H1 had not landed when C3 ran, 2026-08-01); H1's owner should verify verbatim
transcription rather than re-declare.  Math source of record: ROOT §3.1 (ADM).
-/

/-- **(ADM)-FULL** (ROOT §3.1 (ADM), the single operative O-9 r4 form; unit of
record 35faac7): every on-line lattice slot's β_k is FULLY attained by the
ledger — `attainDim β_k = d`, equivalently
`#{j : wt j ≡ β_k (mod e), wt j ≤ β_k} = d`.  p-free, per-datum decidable
(unit C3).  Automatic at r = 0 ONLY (unit C1); NOT automatic at r ≥ 1 (two
countermodels on file, O-9 pass-2/pass-3 records). -/
structure ADMFull (D : CensusData) : Prop where
  full_attained : ∀ β ∈ D.onLineSlots, D.attainDim β = D.d

end LeanUrat.Scaffold
