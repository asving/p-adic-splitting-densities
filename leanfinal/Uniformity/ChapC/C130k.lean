/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130f

/-!
# Uniformity.ChapC.C130k — the chain-realization carrier skeleton (CC-1)

CC-1 of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§4, §10): the U11 carrier skeleton signatures
ONLY — `KeyChain`, `LaurentNormalizer`, `NodePointSource` — plus the live-lint helpers.  The
elaboration authority for the three structures is `leanfinal/scratch/U11_carrier_check.lean`;
their types here are exactly the scratch types.  Every reused name (`StageLive`, `GaugeLive`,
`DeepLive`, `TerminalReceiver` from C.130a; `LevelExponentLattice`, `levelExponentHeight` from
C.130f; `DeepTower` from C.83) is imported, never duplicated.

Deliberately NOT here (later CC nodes): `FGMNSourceData`/`FGMNSourceLaws` and the OPEN-DICT
signatures (CC-13), `ChainRealization` and the A-C.11 packaging (CC-13/CC-16), `RealizedInput`
(CC-8), and the S2 depth-two key chain (CC-2).  No carrier structure is instantiated in this
file; the only instances below are decidability of the C.130a live ranges (lint tooling).
Every field of the three structures is either a source obligation or a repository dictionary
in the sense of the design doc §9; none is a socket conclusion, a consumer class, or a `True`
body.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ## Live-lint helpers

Proved conversions, unfolding pins, decidability, and off-range refuters for the D-TIF-4
live ranges of C.130a, so that later layers (CC-12's off-range lint, CC-18's live-range
lint) can discharge or refute range guards mechanically.  These are theorems about the
existing ranges, not new interfaces. -/

/-- Anti-drift pin: `StageLive` is definitionally its D-TIF-4 arithmetic range. -/
theorem stageLive_iff (r j : ℕ) : StageLive r j ↔ 1 ≤ j ∧ j ≤ r := Iff.rfl

/-- Anti-drift pin: `GaugeLive` is definitionally its D-TIF-4 arithmetic range. -/
theorem gaugeLive_iff (r j : ℕ) : GaugeLive r j ↔ 1 ≤ j ∧ j < r := Iff.rfl

/-- Anti-drift pin: `DeepLive` is definitionally its D-TIF-4 arithmetic range. -/
theorem deepLive_iff (r j : ℕ) : DeepLive r j ↔ 3 ≤ j ∧ j < r := Iff.rfl

/-- A gauge-live level is stage-live: a level-`j` gauge read sits inside the stage range. -/
theorem GaugeLive.stageLive {r j : ℕ} (h : GaugeLive r j) : StageLive r j :=
  ⟨h.1, Nat.le_of_lt h.2⟩

/-- A gauge-live level has a stage-live successor: level `j` consumes `u_(j+1)`. -/
theorem GaugeLive.stageLive_succ {r j : ℕ} (h : GaugeLive r j) : StageLive r (j + 1) :=
  ⟨Nat.le_succ_of_le h.1, h.2⟩

/-- A deep-live level is gauge-live. -/
theorem DeepLive.gaugeLive {r j : ℕ} (h : DeepLive r j) : GaugeLive r j :=
  ⟨Nat.le_trans (by omega) h.1, h.2⟩

/-- A deep-live level is stage-live. -/
theorem DeepLive.stageLive {r j : ℕ} (h : DeepLive r j) : StageLive r j :=
  h.gaugeLive.stageLive

/-- Off-range lint: level `0` is never stage-live. -/
theorem not_stageLive_zero (r : ℕ) : ¬ StageLive r 0 := fun h => by
  exact absurd h.1 (by omega)

/-- Off-range lint: the terminal level `r` is never gauge-live (`u_(r+1)` does not exist). -/
theorem not_gaugeLive_terminal (r : ℕ) : ¬ GaugeLive r r := fun h =>
  absurd h.2 (lt_irrefl r)

/-- Off-range lint: nothing above the terminal level is stage-live. -/
theorem not_stageLive_of_terminal_lt {r j : ℕ} (h : r < j) : ¬ StageLive r j := fun hs =>
  absurd hs.2 (Nat.not_le_of_lt h)

/-- Live-range guards are decidable, so lint side conditions close by `decide`/`omega`. -/
instance instDecidableStageLive (r j : ℕ) : Decidable (StageLive r j) :=
  decidable_of_iff (1 ≤ j ∧ j ≤ r) (stageLive_iff r j).symm

/-- Live-range guards are decidable, so lint side conditions close by `decide`/`omega`. -/
instance instDecidableGaugeLive (r j : ℕ) : Decidable (GaugeLive r j) :=
  decidable_of_iff (1 ≤ j ∧ j < r) (gaugeLive_iff r j).symm

/-- Live-range guards are decidable, so lint side conditions close by `decide`/`omega`. -/
instance instDecidableDeepLive (r j : ℕ) : Decidable (DeepLive r j) :=
  decidable_of_iff (3 ≤ j ∧ j < r) (deepLive_iff r j).symm

/-! ## The carrier skeleton (U11 signatures) -/

/-- OPEN-DICT-1 and C.130b: the polynomial keys are a layer over `DeepTower`.

At depth two the second key is exactly EFF.HETOW.13's wrap-corrected `composedKey`; at
general depth the constructor is the EFF.GENTOW5 S2.1 composed-key recipe (the effective
s1of2.18 row).  EFF.GENTOW5.21 is only the worked `n̂₃(85)`/`n̂₂(21)` regression and must not
be cited as the general key theorem. -/
structure KeyChain (W : DeepTower.{0, uKt} F H₀ hpin r) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_monic : ∀ i, StageLive r i → (keyAt i).Monic
  keyAt_degree : ∀ i, StageLive r i → (keyAt i).natDegree = W.Dcum i

/-- EFF.T2.07 and EFF.GENTOW5.15: an honest integer/Laurent normalizer.

This is the missing source carrier identified by C130B.  It is intentionally not required to
equal C.83's truncated-natural `towerNorm` on all nonnegative inputs — that demand is FALSE
(C130B's counterexample at `(e₂,u₂,k) = (2,5,1)`); compatibility with `towerNorm` may later
be proved only on a named nontruncation domain. -/
structure LaurentNormalizer (W : DeepTower.{0, uKt} F H₀ hpin r) where
  norm : (i : ℕ) → ℤ → LevelExponentLattice i
  norm_zero : ∀ i, norm i 0 = 1
  exact_height : ∀ i, StageLive r i → ∀ k : ℤ,
    levelExponentHeight W i (norm i k) = Multiplicative.ofAdd k

/-- EFF.T2.04/.05/.09/.11 and DEF GENTOW5-1's legal node-point data.

The stage laws are source obligations, not a copy of `SlotCarrier`: they are a tower-indexed
EFF.T2 source family.  `pointHgt_eval` makes the point read an actual polynomial evaluation,
and `slot_value`/`slot_digit` tie the stage tables to legal points, witnessing that `hgt`
and `dig` are not freely chosen tables.  C.130c derives `Ladder.SlotCarrier` from these
fields.  The two Laurent reads `canonicalRead` and `arenaRead` are deliberately separate
fields; no field equates them or gives a Kt-preimage between them (the OM-8 L3 descent goal
stays open at the sockets, as freeze v2 requires). -/
structure NodePointSource
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
    (receiver : TerminalReceiver F H₀ hpin r W Kt) (K : KeyChain W) where
  /-- DEF GENTOW5-1 and EFF.GENTOW5.16: the legal node points (the P-locus). -/
  Point : Type
  /-- EFF.GENTOW5.16: legality of a node point at each live stage. -/
  Pt : ℕ → Point → Prop
  /-- EFF.GENTOW5.16: every live stage has a legal point. -/
  point_exists : ∀ i, StageLive r i → Nonempty {x : Point // Pt i x}
  /-- EFF.GENTOW5.16/.19: the ambient coefficient read of the evaluation. -/
  coeffHom : O →+* L
  /-- EFF.GENTOW5.16/.19: the ambient coordinate of a node point. -/
  coord : Point → L
  /-- EFF.GENTOW5.16/.19: the ambient stage valuation read. -/
  valueOn : ℕ → L → WithTop ℤ
  /-- EFF.GENTOW5.19: valuation law — zero has infinite value. -/
  value_zero : ∀ i, StageLive r i → valueOn i 0 = ⊤
  /-- EFF.GENTOW5.19: valuation law — multiplicativity. -/
  value_mul : ∀ i, StageLive r i → ∀ a b,
    valueOn i (a * b) = valueOn i a + valueOn i b
  /-- EFF.GENTOW5.19: valuation law — ultrametric inequality. -/
  value_add_ge : ∀ i, StageLive r i → ∀ a b,
    min (valueOn i a) (valueOn i b) ≤ valueOn i (a + b)
  /-- EFF.GENTOW5.19: valuation law — ultrametric equality off ties. -/
  value_add_eq : ∀ i, StageLive r i → ∀ a b,
    valueOn i a ≠ valueOn i b →
      valueOn i (a + b) = min (valueOn i a) (valueOn i b)

  /-- EFF.T2.04: the stage height table. -/
  hgt : ℕ → Polynomial O → WithTop ℤ
  /-- EFF.T2.05: the stage digit table. -/
  dig : (i : ℕ) → Polynomial O → W.fld i
  /-- EFF.T2.04 at a node point: the pointwise height read. -/
  pointHgt : ℕ → Point → Polynomial O → WithTop ℤ
  /-- EFF.T2.05 at a node point: the pointwise digit read. -/
  pointDig : (i : ℕ) → Point → Polynomial O → W.fld i
  /-- The point read is an actual polynomial evaluation, not a free table. -/
  pointHgt_eval : ∀ i x A,
    pointHgt i x A = valueOn i (Polynomial.eval₂ coeffHom (coord x) A)
  /-- EFF.T2.04: the stage height table agrees with every legal-point read in slot range. -/
  slot_value : ∀ i (_hi : StageLive r i) (x : Point), Pt i x →
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < W.Dcum i → pointHgt i x A = hgt i A
  /-- EFF.T2.05: the stage digit table agrees with every legal-point read in slot range. -/
  slot_digit : ∀ i (_hi : StageLive r i) (x : Point), Pt i x →
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < W.Dcum i → pointDig i x A = dig i A

  /-- EFF.T2.04: stage law — zero has infinite height. -/
  hgt_zero : ∀ i, StageLive r i → hgt i 0 = ⊤
  /-- EFF.T2.05: stage law — zero has digit zero. -/
  dig_zero : ∀ i, StageLive r i → dig i 0 = 0
  /-- EFF.T2.04: stage law — slot-range nonzero polynomials have finite height. -/
  hgt_ne_top : ∀ i, StageLive r i → ∀ A : Polynomial O,
    A ≠ 0 → A.natDegree < W.Dcum i → hgt i A ≠ ⊤
  /-- EFF.T2.05: stage law — slot-range nonzero polynomials have nonzero digit. -/
  dig_ne_zero : ∀ i, StageLive r i → ∀ A : Polynomial O,
    A ≠ 0 → A.natDegree < W.Dcum i → dig i A ≠ 0
  /-- EFF.T2.04: stage law — ultrametric inequality for heights. -/
  hgt_add_ge : ∀ i, StageLive r i → ∀ A B,
    min (hgt i A) (hgt i B) ≤ hgt i (A + B)
  /-- EFF.T2.04: stage law — ultrametric equality off ties. -/
  hgt_add_eq : ∀ i, StageLive r i → ∀ A B,
    hgt i A ≠ hgt i B → hgt i (A + B) = min (hgt i A) (hgt i B)
  /-- EFF.T2.05: stage law — digit additivity at a common height, off digit cancellation. -/
  dig_add : ∀ i, StageLive r i → ∀ A B : Polynomial O, ∀ k : ℤ,
    hgt i A = (k : WithTop ℤ) → hgt i B = (k : WithTop ℤ) →
    dig i A + dig i B ≠ 0 →
      hgt i (A + B) = (k : WithTop ℤ) ∧ dig i (A + B) = dig i A + dig i B
  /-- EFF.T2.09: the fullness predicate for realizable heights. -/
  Full : ℕ → ℤ → Prop
  /-- EFF.T2.09: every full height realizes every nonzero digit by a slot-range polynomial. -/
  lift : ∀ i, StageLive r i → ∀ k : ℤ, Full i k → ∀ c : W.fld i, c ≠ 0 →
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < W.Dcum i ∧
      hgt i A = (k : WithTop ℤ) ∧ dig i A = c

  /-- EFF.T2.04/.11: inherited integer input, not a function inferred from `(W,i,F₀)`. -/
  thresholdZ : ℕ → ℤ
  /-- Repo dictionary to E.11's current natural-valued `BlockData.T`. -/
  thresholdNat : ℕ → ℕ
  /-- The dictionary obligation forced by the natural-valued `BlockData.T`: if a source
  instance has a genuinely negative inherited threshold, this field is uninhabitable and
  E.11 must be re-signed to `ℤ`; no truncation to zero is allowed. -/
  threshold_nonneg : ∀ i, StageLive r i → (thresholdNat i : ℤ) = thresholdZ i
  /-- EFF.T2.11: the WINDOW source law `T < d(Φ(ρ)) < ∞` at every legal point. -/
  window : ∀ i, StageLive r i → ∀ x : Point, Pt i x →
    (thresholdZ i : WithTop ℤ) < pointHgt i x (K.keyAt i) ∧
      pointHgt i x (K.keyAt i) ≠ ⊤

  /-- EFF.GENTOW5 S2.1/S2.3: the ambient node-point letters. -/
  ambientLetter : ℕ → Lˣ
  /-- EFF.GENTOW5.19: the exact key value `u_(i+1)` at a legal point (gauge-live only). -/
  key_value : ∀ i, GaugeLive r i → ∀ x : Point, Pt i x →
    pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ)
  /-- EFF.GENTOW5 S2.3: the transported `ψ`-root law for the ambient letter. -/
  psi_root : ∀ i, GaugeLive r i →
    Polynomial.eval₂ ((algebraMap Kt L).comp (receiver.levelHom i))
      (ambientLetter i : L) (W.ψ i) = 0
  /-- EFF.T1.01 and EFF.GENTOW5 S2.3 step (3): the L-valued node read. -/
  canonicalRead : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Lˣ
  /-- D.07/D.08, D.44 and EFF.T3.21: the separate terminal-field W-leg read. -/
  arenaRead : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Ktˣ
  /-- D.07/D.08, D.44 and EFF.T3.21: the terminal-field lattice read for the arena family. -/
  towerRead : (i : ℕ) → LevelExponentLattice i → Kt
  /-- EFF.T1.01--.03 and EFF.T3.21: the peel units of the separate arena data. -/
  peelUnit : ℕ → Ktˣ

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.stageLive_iff
#print axioms Uniformity.Density.Tower.gaugeLive_iff
#print axioms Uniformity.Density.Tower.deepLive_iff
#print axioms Uniformity.Density.Tower.GaugeLive.stageLive
#print axioms Uniformity.Density.Tower.GaugeLive.stageLive_succ
#print axioms Uniformity.Density.Tower.DeepLive.gaugeLive
#print axioms Uniformity.Density.Tower.DeepLive.stageLive
#print axioms Uniformity.Density.Tower.not_stageLive_zero
#print axioms Uniformity.Density.Tower.not_gaugeLive_terminal
#print axioms Uniformity.Density.Tower.not_stageLive_of_terminal_lt
#print axioms Uniformity.Density.Tower.instDecidableStageLive
#print axioms Uniformity.Density.Tower.instDecidableGaugeLive
#print axioms Uniformity.Density.Tower.instDecidableDeepLive
#print axioms Uniformity.Density.Tower.KeyChain
#print axioms Uniformity.Density.Tower.LaurentNormalizer
#print axioms Uniformity.Density.Tower.NodePointSource

end AxCheck
