/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# MovesRBase/Defs — the MovesR WITT BASE LAYER (base-index conventions)

E-phase transcription of `lean/notes/MOVESR_LEAN_BLUEPRINT_2026-07-28.md` (rev 4) §1,
BASE-LAYER SPLIT-OFF ONLY (campaign-ledger disposition: the MovesR corpus is PARKED —
its §C-pointer layer awaits HC-1's carriers — but the Witt base layer is verified
clean across four audits and splits off). Scope here: U1's base defs
(`Kbar/Wbar/Fsub/O/qq/relExt/cyl`), D1's local `map_comp` ext lemma, and the provable
units U2–U6, U12, U41 (one file per unit). EXCLUDED per the split-off charge:
everything touching `GradedCarrier`/`CStatements`/`REL1`/`Setting`/`BoxVol` — so U5's
`βarg_eq` half and U41's `Setting`-parameterization are handled per MANIFEST.json's
deviations section.

Supporting vocabulary for U12's statement — `SpeciesSyntax`, `AlphabetData`,
`AlphabetData.Stable`, `EQ2law` (the blueprint's U9–U11 statement-layer carriers) — is
transcribed VERBATIM below; these are NOT units of this split-off and carry no proof
obligations (statements-only, sorry-free; the MovesR corpus proper re-homes them).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## R0. Base-index convention (unit U1: base_defs — "F_m is THE subfield of order
p^m and O_m := W(F_m) ⊂ W(F̄_p)") -/

/-- `F̄_p`, fixed ONCE. -/
abbrev Kbar := AlgebraicClosure (ZMod p)

/-- `W(F̄_p)` — every base below is a LITERAL subring of this one ring. -/
abbrev Wbar := WittVector p (Kbar p)

/-- `F_m` — THE subfield of `F̄_p` of order `p^m` (fixed field of the m-th Frobenius
iterate; membership definitionally `x ^ p ^ m = x`; the order fact is unit U6). -/
noncomputable def Fsub (m : ℕ+) : Subfield (Kbar p) :=
  RingHom.eqLocusField (iterateFrobenius (Kbar p) p (m : ℕ)) (RingHom.id _)

/-- `O_m := W(F_m) ⊂ W(F̄_p)`: "nested base changes then compose LITERALLY as
subrings … no per-pair embedding choices". -/
noncomputable def O (m : ℕ+) : Subring (Wbar p) :=
  (WittVector.map (Subfield.subtype (Fsub p m))).range

/-- `q_m := p^m = |F_m|` (the note's `q_δ := p^δ`; `= |F_m|` by U6). -/
def qq (m : ℕ+) : ℕ := p ^ (m : ℕ)

/-- degree-δ′ unramified base change of `O_m` inside `W(F̄_p)` — BY THE CONVENTION
this IS `O_{m·δ′}` (ABSOLUTE indices; "never an identification up to isomorphism"). -/
noncomputable def relExt (m δ' : ℕ+) : Subring (Wbar p) := O p (m * δ')

/-- The level-N digit cylinder at `g` in the degree-n coefficient box over `O_m`:
agreement of the first N Witt coordinates (F_m perfect ⇒ p^N W(F_m) = V^N W(F_m),
so this IS "f mod p^N" — (R0-box)'s level-N counting). -/
def cyl (m : ℕ+) {n : ℕ} (N : ℕ) (g : Fin n → ↥(O p m)) : Set (Fin n → ↥(O p m)) :=
  {h | ∀ (j : Fin n) (i : ℕ), i < N → ((h j : Wbar p)).coeff i = ((g j : Wbar p)).coeff i}

/-! ## U12 supporting vocabulary (blueprint U9–U11, verbatim; NOT units here) -/

/-- (EQ-1) carrier: species letters are FINITE SYNTAX — "defined by stage tuples
(e, h, g, μ), side/lattice data, and polygon conventions … never by the residue
field's SIZE". `shape` exposes the stage tuple (the grammar anchor); `menu δ` is a
FINSET (finiteness typed). (CF3: no `menuNe` — empty menus are in range.) -/
structure SpeciesSyntax where
  Letter : Type
  shape : Letter → ℕ × ℕ × ℕ × ℕ          -- the stage tuple (e, h, g, μ)
  /-- (CF4) the rest of the note's grammar: side/lattice and polygon-convention data
  as declared carriers, with `letter_det` typing "defined by". -/
  SideData : Type
  side : Letter → SideData
  PolyConv : Type
  poly : Letter → PolyConv
  letter_det : Function.Injective (fun l => (shape l, side l, poly l))
  menu : ℕ+ → Finset Letter               -- the realized menu over O_δ

/-- (EQ-2) carrier: the alphabet 𝔸_δ at a position class as an actual ADDITIVE SPAN —
"the attainable additive image/span of the RE-BASED slot maps"; `card_eq` is the
note's UNCONDITIONAL definition part |𝔸_δ| = p^{a_δ}; `posLetter` is the realized
species letter (the owed dictionary AS DATA). -/
structure AlphabetData (Sp : SpeciesSyntax) where
  Pos : Type                              -- shape position classes
  posNe : Nonempty Pos
  Carrier : ℕ+ → Pos → Type               -- the re-based receiving group
  [carrierGrp : ∀ δ x, AddCommGroup (Carrier δ x)]
  [carrierMod : ∀ δ x, Module ↥(Fsub p δ) (Carrier δ x)]   -- F_δ-structure (CF6)
  /-- (CF5) the RE-BASED SLOT MAPS themselves, as declared data. -/
  SlotDom : ℕ+ → Pos → Type
  [slotDomGrp : ∀ δ x, AddCommGroup (SlotDom δ x)]
  [slotDomMod : ∀ δ x, Module ↥(Fsub p δ) (SlotDom δ x)]
  slotMap : ∀ δ x, SlotDom δ x → Carrier δ x
  alpha : ∀ δ x, Set (Carrier δ x)        -- 𝔸_δ
  /-- (CF5) ATTAINABILITY, typed as span-generation equality. -/
  alpha_attain : ∀ δ x,
    alpha δ x = ↑(AddSubgroup.closure (Set.range (slotMap δ x)))
  aDim : ℕ+ → Pos → ℕ                     -- a_δ: F_p-additive-span dimension
  card_eq : ∀ δ x, Nat.card (alpha δ x) = p ^ aDim δ x
  posLetter : ℕ+ → Pos → Sp.Letter        -- the realized species letter

attribute [instance] AlphabetData.carrierGrp AlphabetData.carrierMod
attribute [instance] AlphabetData.slotDomGrp AlphabetData.slotDomMod

/-- δ-STABLE-SPECIES position (rev-4 comparison-domain pin), DEFINED: the species
letter persists under re-basing. Split positions fail this and are OUT-OF-DOMAIN. -/
def AlphabetData.Stable {Sp} (AD : AlphabetData p Sp) (δ : ℕ+) (x : AD.Pos) : Prop :=
  AD.posLetter δ x = AD.posLetter 1 x

/-- **(EQ-2) the law ON THE PINNED PER-POSITION-CLASS DOMAIN** [OPEN,
REL.1-conditional]: "at a fixed shape position WHOSE SPECIES IS δ-STABLE …, the
re-based piece maps are F_δ-linear AND a_δ = δ·a" — BOTH conjuncts typed (CF6). -/
def EQ2law {Sp} (AD : AlphabetData p Sp) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
    IsLinearMap ↥(Fsub p δ) (AD.slotMap δ x) ∧
    AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x

end MovesRBase
