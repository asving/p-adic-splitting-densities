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
import LeanUrat.Moves.L1_gaussVal
import LeanUrat.HC1.DefsD

/-!
# HC1/DefsTower — towers, moves, birth indices (blueprint §2.2)

**Provenance.** `HC1_LEAN_BLUEPRINT_2026-07-28.md` (rev 2) §2.2, with the §2.2
RECORDED DECISIONS paragraph (audit G-3) and the audit C-1 exclusive-STR convention.
Design decisions D2 (explicit towers), D4 (the MovesGr fences as inputs), D5 (the
Gauss-valuation base pin), D6 (e_birth as a tower function). Definitions only — no
theorems, no `sorry`. E-phase deviations (constructor rename `rec → recenter`; the
recursion clamps) are recorded in the blueprint's DEVIATIONS appendix.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- The FULL D.3–D.7 increment hypothesis interface (the TRANSstage fence, D4(ii)):
everything the note requires of a legal read, nothing more. FALSE at `e′ = 0`, at
`ψ = X` (the note's ψ ≠ z), at reducible ψ, at a non-(I-aug) side. -/
structure TransHyp (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) : Prop where
  hmonic : ψ.Monic
  hirr : Irreducible ψ
  hne_z : ψ ≠ Polynomial.X          -- ψ ≠ z (D.3 head)
  hdeg : ψ.natDegree = g
  hg : 1 ≤ g
  hlift : IsStandardLift σ ψ g Φhat -- D.5's displayed formula (Moves Defs)
  he' : 1 ≤ e'
  hh' : 1 ≤ h'
  hcop : Nat.gcd e' h' = 1
  hiaug : IAug σ Φhat e' h'         -- h′ > e′·w(Φ̂) (D.4/D.7 head)
  hroot : Polynomial.aeval (zbar : F) (ψ.map σ.K.subtype) = 0  -- z̄ a root of ψ in F

/-- One tower move: an increment with its full interface + transition record, or a
recentering with the RECORDING form (the recTRANSRS fence, D4(iii)). E-phase rename:
the blueprint's constructor `rec` collides with the auto-generated recursor and is
`recenter` here (Deviation D-1).

**F-5 ENRICHMENT (sign-off event 2026-07-28, blueprint §9.6):** each constructor
carries the child core `core' : StageCoreL σ'`. The note's move IS a stage-producing
construction (MOVES 2464–2465: "The stage axioms (S1′)–(S5′), (S6a′), (S6b′) all
hold"); the S11 escalation countermodel (sign-twist, in-file at `S11_towerSpine`)
machine-certified that the twist-class legs {w_jump, TvecLaw, TvecUnitLaw,
CoeffLocLaw, SlotDecomp, CoeffFieldLawCore} are INDEPENDENT of the previously
recorded witnesses, so a `Tower` recording less than stage-hood under-records the
note. S9/S10 (statements unchanged) prove enriched witnesses EXIST for every legal
read — inhabitation is unweakened; `S11a_coreTransport` certifies the enrichment is
MINIMAL (every non-twist leg was already derivable). -/
inductive MoveWitness (σ σ' : Stage p F) : Type u
  | inc (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
      (hyp : TransHyp σ ψ g Φhat e' h' zbar)
      (core : TransitionCoreL σ σ' Φhat e' h' zbar)
      (core' : StageCoreL σ') : MoveWitness σ σ'
  | recenter (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
      (core : IsRecenteringCore σ σ' cc tt)
      (core' : StageCoreL σ') : MoveWitness σ σ'

/-- The faithful D.2 base pin (the baseStage fence, D4(i)/D5): parent valuation =
the Gauss valuation, reps = [C p] (U = {π}, representative p — MOVES 1999–2001),
current field = the base field. FALSE for the wPrev = 0 clone MovesGr certified
vacuous. -/
def IsBaseStage (σ : Stage p F) : Prop :=
  (∀ f, f ≠ 0 → σ.wPrev f = gaussVal f) ∧
  σ.reps = [Polynomial.C (p : ℤ_[p])] ∧ σ.K = σ.FQ

/-- **A tower**: base + K moves; `stg 0` faithfully based, every step witnessed.
Nonempty by gate T2 (depth 0) and S1's gate (depth 1). -/
structure Tower (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] where
  K : ℕ
  stg : Fin (K + 1) → Stage p F
  base : IsBaseStage (stg 0) ∧ StageCoreL (stg 0)
  move : ∀ k : Fin K, MoveWitness (stg k.castSucc) (stg k.succ)
  /-- **CHAR PIN (F-2, frontier adjudication 2026-07-28, blueprint §9.2):** the ambient
  residue field has characteristic p — intrinsic to the note's setting (the F_{k+1}/F_p
  extensions of MOVES 2148–2165 are residue fields of extensions of ℚ_p); the card-K
  bridge `Nat.card ↥K = p^[K:F_p]` (C6's conjuncts 2–3) is underivable without it
  (round-2 fleet kernel, commit 2f388c8). Excludes only note-rejected char ≠ p
  instantiations; every planned gate instance (T2/S1/G2: `GaloisField 2 2` at p = 2)
  satisfies it by instance. -/
  hcharF : CharP F p

namespace Tower

variable (T : Tower p F)

/-- e_birth per level (D6), on the underlying ℕ index (clamped junk beyond K): base
e at 0; an increment sets e′; a recentering KEEPS the previous value ("same C, same
v, same T" — TRANS-RS). ROOT CONVENTION (recorded decision (4)): `eBirth 0 = (stg 0).e`
— the root coefficient algebra is born at the base read. -/
def eBirthAux : ℕ → ℕ
  | 0 => (T.stg 0).e
  | k + 1 =>
    if h : k < T.K then
      match T.move ⟨k, h⟩ with
      | .inc _ _ _ e' _ _ _ _ _ => e'
      | .recenter _ _ _ _ => eBirthAux k
    else eBirthAux k

/-- e_birth per level (D6): `eBirthAux` read at the tower index. -/
def eBirth (k : Fin (T.K + 1)) : ℕ := T.eBirthAux k.val

/-- **EXCLUSIVE accumulated stretch** (the note's STR, audit C-1), on ℕ (clamped):
the stretch accumulated BEFORE level k's read — `STR₀ = 1`, `STR_{k+1} = STR_k·e_k`
(e_k := (T.stg k).e; recentered stages contribute e = 1 — D.10's e_read = 1
precondition, S10's `σ.e = 1` hypothesis). LST base 3752: κ₀ at STR₀ = 1. -/
def strAux : ℕ → ℕ
  | 0 => 1
  | k + 1 => strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1)

/-- The exclusive STR at a tower level (audit C-1: each e counted ONCE). -/
def str (k : Fin (T.K + 1)) : ℕ := T.strAux k.val

/-- κ_k := h_k/(e_k·STR_k) — the note's formula VERBATIM on the exclusive STR
(LST head, MOVES 3731–3735); = h_k/(e₀·…·e_k), each e counted once. AUDIT
RECOMPUTE (C-1): at (e₀,h₀) = (2,1), κ₀ = 1/2. TOTAL on Fin (T.K+1); its value at a
recentered level is junk-but-harmless (recorded decision (3): it multiplies a
forced-0 slot). -/
noncomputable def kappa (k : Fin (T.K + 1)) : ℚ :=
  ((T.stg k).h : ℚ) / (((T.stg k).e : ℚ) * (T.str k : ℚ))

/-- the frame-(K+1) accumulated stretch `strTop = STR_K·e_K = e₀·…·e_K`
(C.1.0(c)'s frame str, inclusive of the last read): THE stage-scale conversion
factor — stage-K weights = strTop × absolute heights (T3; the carrier's
reindexing, T6; TYP's δ' := strTop·γ', C2). -/
def strTop : ℕ := T.str (Fin.last T.K) * (T.stg (Fin.last T.K)).e

/-- The top (frame-(K+1)) stage of the tower. -/
def topStage : Stage p F := T.stg (Fin.last T.K)

/-- `slotBound T r` for r < K := the key-degree ratio (recorded decision (1)):
`deg Φ_{r+1} / deg Φ_r` — an integer (= e_r·g_{r+1} at an increment, by D.3; = 1 at
a recentering, degree unchanged). -/
noncomputable def slotBound (r : Fin T.K) : ℕ :=
  (T.stg r.succ).Φ.natDegree / (T.stg r.castSucc).Φ.natDegree

/-- A tower coordinate: p-adic level l + inner slot vector (bounded per level by the
key-degree ratios — the iterated-development address (b, l) of D.3(e)); the TOP
slot is the current development-slot index, UNBOUNDED here (recorded decision (2):
every consumer pins it per use — levelSet fixes it to b; T12's level-N boxes bound
it by the box's window length; LST/TYP are per-block statements). -/
structure Coord (T : Tower p F) where
  l : ℕ
  slot : Fin (T.K + 1) → ℕ
  slot_lt : ∀ r : Fin T.K, slot r.castSucc < T.slotBound r

/-- the coordinate's basis monomial `m_c = p^l·∏_r Φ_r^{slot r}` (TYP(a) display).
Recorded decision (3): recentered levels have ratio-1 bounds forcing slot ≡ 0, so
`mono` auto-selects the CURRENT frame's key of each degree class. -/
noncomputable def mono (c : T.Coord) : Polynomial ℤ_[p] :=
  Polynomial.C ((p : ℤ_[p]) ^ c.l) * ∏ r, (T.stg r).Φ ^ c.slot r

/-- the absolute height `ht(c) = l + Σ_r slot_r·κ_r` (LST head, MOVES 3734–3735). -/
noncomputable def ht (c : T.Coord) : ℚ :=
  (c.l : ℚ) + ∑ r, (c.slot r : ℚ) * T.kappa r

/-- The mixed-radix base index of a coordinate: `Σ_r slot_r·deg Φ_r` — the base
index of `mono c`'s x-leading block (C.1.0(a)/(c)'s affine correspondence; T9(b)). -/
noncomputable def baseIdx (c : T.Coord) : ℕ := ∑ r, c.slot r * (T.stg r).Φ.natDegree

/-- nonzero-monomial guard (T3's hypothesis; provable for genuine towers, kept as
the blueprint's own guard). -/
def Coord.MonoNZ {T : Tower p F} (c : T.Coord) : Prop := T.mono c ≠ 0

end Tower

end LeanUrat.HC1
