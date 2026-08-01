/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H2.Carriers

/-!
# Scaffold/HDischarge/H2/FreshLaws — the (FRESH) counting-shadow laws
  [HDISCHARGE_H2 unit U2; wave 0, dep U1; STATEMENTS ONLY]

Transcription of `lean/blueprints/HDISCHARGE_H2.md` §6 unit H2-U2 (statements
VERBATIM, compile-probed at the blueprint session; REVISED at review pass 1 —
findings 6/7/9/10/12). This file is part of the H2 trust surface: Codex
statement-audit REQUIRED before any consumption.

Laws: `FloorsChargeLaw` · `DigitsProdLaw` · `FiberSumLaw` · `FreshReadsLaw` ·
`SlotUniformLaw` · `JunctionPinLaw`, packaged as `FreshClauses` — the
CENSUS-FACE COUNTING SHADOW of (H2) = (FRESH) (O-9 rev-5 §5.4), in exactly the
shape CEN-J (O-9 §6.4 steps 2–4) consumes.

Encoding conventions (blueprint §6 preamble, FLAGGED for prover+verifier):
ℕ-subtraction in exponents implements the max(0,·) truncation (exact within
LED(i) scope m·N ≥ s(·)); digit alphabets ride ℕ with counts vanishing
off-range; `s`-monotonicity (`Finset.card_le_card`) gives
max(s β, s g) = s (max β g).

**CEN-J SCOPE GUARD (O-9 rev-3 pass-2 GAP-4 scope; review finding 7).**
Where the O-9 CEN-J display requires g_k ≤ β_k at every on-line slot, that
requirement is a HYPOTHESIS of the consuming theorems (U5/U6 take
`hscope : ∀ k ∈ W.onLine, P.g k ≤ W.beta k` where the O-9 display requires
it) — it is NEVER silently assumed by the laws in this file, which are stated
without it.

**Monic-top engine seam (review finding 14).** At `monicTop = true` the
junction is the erased top slot (`W.hks_top : ks = Fin.last ℓ`, outside
`boxSlots`); its read = the monicity constant 1 is an ENGINE-SEAM fact owed at
instantiation, so `JunctionPinLaw` is honestly vacuous there (guard
`monicTop = false`).

NOT the full (H2) row: the structural affine/carry content of (b) and the
classifier face (Step 10/K1) are priced at (TRANS-DEEP) (blueprint §5) and the
§2.3 adjudication.
-/

namespace LeanUrat.Scaffold.HDischarge.H2

open LeanUrat.Scaffold

variable {D : CensusData}

/-- (FRESH)(a′) LED-CHARGE face at every box slot: the per-slot height count
    at the JOINT condition max(β_k, g_k) (ℕ-subtraction = max(0,·); exact in
    the LED(i) regime m·N ≥ s(·), the law's declared scope).

    O-9 PIN — §5.4 clause (a′) [transported floors]; consumed at §6.4 step 2:
    the per-slot relative LED charge q^{−max(0, s(β_k) − s(g_k))} — this
    absolute count against the parent's q^{mN − s(g_k)} baseline. CEN-J's
    g_k ≤ β_k on-line requirement is the consuming theorems' `hscope`
    HYPOTHESIS (module docstring), never assumed here. -/
def FloorsChargeLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
    ∀ k ∈ W.boxSlots,
      J.slotCount ρ k q
        = q ^ ((D.period * D.d) * J.N - D.s (max (W.beta k) (P.g k)))

/-- (FRESH)(a′) PRODUCT-BOX face, digit level (THE (a′) core: "a product
    box"): on each ρ-fiber the prescribed-digit count factorizes per-slot —
    on-line slots contribute their digit counts, off-line box slots their
    height counts. Alphabet-bounded.

    O-9 PIN — §5.4 clause (a′) [the product-box / "no cross-slot condition
    survives" content]; consumed at §6.4 step 2 (the product box behind the
    per-slot LED charges) and as the factorization feeding step 3's joint
    independence across on-line slots. Scope guard as in the module
    docstring. -/
def DigitsProdLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
    ∀ z : (↥W.onLine → ℕ), (∀ k, z k < q ^ D.d) →
      J.fiberDigits ρ z q
        = (∏ k ∈ W.onLine.attach, J.slotDigits ρ k (z k) q)
          * ∏ k ∈ W.boxSlots \ W.onLine, J.slotCount ρ k q

/-- The fiber ↔ fiberDigits SEAM (review finding 10): summing the digit-vector
    counts over the full F_{q^d}-alphabet box recovers the height-only fiber
    count (z_k = 0 encodes "strictly above" — O-9 §5.1's read convention).

    O-9 PIN — the §5.1 read-convention seam between the digit-level and
    height-level counts; consumed at §6.4 steps 2–3 as the aggregation tying
    the step-3 per-digit factors back to the step-2 height-only census (the
    U5 route to the derived cardinality law). -/
def FiberSumLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
    ∑ z : (↥W.onLine → Fin (q ^ D.d)),
        J.fiberDigits ρ (fun k => (z k).1) q
      = J.fiber ρ q

/-- (FRESH)(b), COUNTING FACE: per prescribed in-alphabet digit vector
    agreeing at the junction, fiber counts coincide. NOT the full structural
    clause (affine-in-one-fresh-digit, unit slope) — see the §3.2 residue
    display; the structural content is priced at (VTX-DEEP).

    O-9 PIN — §5.4 clause (b) [fresh reads], counting face only; consumed at
    §6.4 step 3: per prescribed digit q^{−d} at each of
    L′ = L − [k_s ∈ K_D] on-line slots, jointly independent. -/
def FreshReadsLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
    ∀ z z' : (↥W.onLine → ℕ),
      (∀ k, z k < q ^ D.d) → (∀ k, z' k < q ^ D.d) →
      (∀ hk : W.ks ∈ W.onLine, z ⟨W.ks, hk⟩ = z' ⟨W.ks, hk⟩) →
      J.fiberDigits ρ z q = J.fiberDigits ρ z' q

/-- LED §5.1's per-slot uniformity shadow (engine-seam supplied; (ADM)-FULL +
    (GR-B) line clause are its suppliers there): non-junction on-line slots'
    per-digit counts are digit-independent on the alphabet.

    O-9 PIN — the §5.1 per-slot read uniformity underlying §5.4 clause (b);
    consumed at §6.4 step 3 (it is what makes each non-junction on-line
    slot's per-digit factor the uniform q^{−d}). -/
def SlotUniformLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
    ∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
      ∀ z z' : ℕ, z < q ^ D.d → z' < q ^ D.d →
        J.slotDigits ρ k z q = J.slotDigits ρ k z' q

/-- (FRESH)(c), COUNTING FACE: the junction read is a ρ-determined NONZERO
    constant — off-c vectors count 0 (free-end box; at monic top the junction
    is the erased top slot (`hks_top`), whose read is the monicity constant —
    an engine-seam fact, so the law is honestly vacuous there). The c-fiber is
    NOT asserted nonempty: empty ρ-fibers are legitimate (O-9's padding).

    O-9 PIN — §5.4 clause (c) [the junction pin; rev-0's "JUNCTION-PIN",
    PROVED label WITHDRAWN at 01c21e6]; consumed at §6.4 step 4: the
    k_s-read is charged to the parent and the vertex telescope closes to
    ∏_S M_{λ_S}(q^d) with NO stray (q^d − 1) factor (O-9 Lemma D pinned-end +
    Lemma C — only the pin's nonvanishing and fixedness enter, never its
    value). -/
def JunctionPinLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  W.monicTop = false →
    ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
      ∃ c : ℕ, c ≠ 0 ∧ c < q ^ D.d ∧
        ∀ (hk : W.ks ∈ W.onLine) (z : (↥W.onLine → ℕ)),
          z ⟨W.ks, hk⟩ ≠ c → J.fiberDigits ρ z q = 0

/-- The CENSUS-FACE COUNTING SHADOW of (H2) = (FRESH), packaged at one
    (W, P, J) — exactly the faces CEN-J (O-9 §6.4) consumes. NOT the full
    row: the structural affine/carry content of (b) and the classifier face
    (Step 10/K1) are priced at (VTX-DEEP) and the §2.3 adjudication.

    O-9 PIN — the §5.4 display (a′)/(b)/(c) as counting shadows, consumed at
    §6.4 steps 2–4 respectively (see the per-law docstrings). CEN-J SCOPE
    GUARD: the g_k ≤ β_k on-line requirement (O-9 rev-3 pass-2 GAP-4 scope)
    is a HYPOTHESIS of the consuming theorems — U5/U6 take
    `hscope : ∀ k ∈ W.onLine, P.g k ≤ W.beta k` where the O-9 display
    requires it — never a silent assumption of this package. -/
structure FreshClauses (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop where
  floorsCharge : FloorsChargeLaw W P J
  digitsProd : DigitsProdLaw W P J
  fiberSum : FiberSumLaw W P J
  freshReads : FreshReadsLaw W P J
  junctionPin : JunctionPinLaw W P J

end LeanUrat.Scaffold.HDischarge.H2
