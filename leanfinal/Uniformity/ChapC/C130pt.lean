/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130k
import Uniformity.ChapC.C130s2

/-!
# Uniformity.ChapC.C130pt — the legal node-point layer (chain-carrier node CC-9)

**Chain-carrier node CC-9** (`docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md` §4.2, §8 row
C.130g, §10 row CC-9: *"Land `Point`/`Pt`, exact key values, transported `ψ`-root, and ambient
letters; exclude all descent claims"*).  The point-layer SOURCE fields were landed with the
CC-1 skeleton (`NodePointSource`, C130k); this file lands the LAYER on top of them — the legal
P-locus exports, the derived exact-key-value laws, the transported-`ψ` object and its root/
forcing theorems, and the bundled clause-by-clause legality read — the freeze-v2 layer C.130g
(`NodePointDatum`/`LegalGENTOW5NodeRead`) content at the carrier, derived rather than stored.

## Source rows (design §9's "source obligations" for this layer)

* **EFF.GENTOW5.s1of2.19** (DEF GENTOW5-1, the depth-(i+1) node locus `P_{i+1}`): roots with
  the stage values EXACT (`v(Φ_j(ξ)) = u_{j+1}/ê_{j+1}` exactly) and the level residue class a
  `ψ`-root.  Carried as `Pt`/`point_exists`/`key_value`; exported here as `LegalPt`,
  `legalPoint`, `key_value_coe/ne_top/pow/pow_e`.  Nonemptiness of the locus is a HYPOTHESIS
  wherever consumed (the row's own conditionality) — here it is the `point_exists` source
  field, never a theorem about a bare `DeepTower`.
* **EFF.GENTOW5.s1of2.16** (DEF GENTOW5-1, cocycle and letters): the level letters `Λ_i` with
  dv-value `0` at level-(i+1) points and residues `β_{i,ξ}`.  The height-arithmetic half of the
  value-`0` claim (`dv_i(Φ_i^{e_{i+1}}) = e_{i+1}·u_{i+1}`, the row's own DERIVATION sentence)
  is PROVED here from the carrier: `key_value_pow_e`.  The normalizer half
  (`n̂_i(u_{i+1})` at the same height) is CC-4/CC-10's, not taken here.
* **EFF.GENTOW5 §S2.3 step (3)** (the transport/cocycle residue computation): the transported
  letter is a `ψ`-root through the level transport — carried as `psi_root`, materialized here
  as the transported minimal polynomial `TerminalReceiver.psiTransported` with
  `ambientLetter_isRoot`, and the codomain-forcing theorem `psiTransported_root_ne_zero`
  (freeze v2 §4's "`ψ_(a+1)(0) ≠ 0` … admits only an `Lˣ` value", now a THEOREM: any root of
  the transported `ψ` is nonzero, so the `Lˣ` codomain of `ambientLetter` is forced, not a
  convenience).

## Deliberately NOT here (the design's fences)

* **No descent claim** (design §10 row CC-9's explicit exclusion; freeze v2 §7 row C.130g:
  "exclude OM-8 L3").  No declaration in this file mentions the separate terminal-field reads,
  any `Kt`-preimage of an ambient letter, or any agreement between the two residue reads of
  `NodePointSource`; unpacking a socket still leaves exactly the descent/agreement goal, as
  freeze v2 requires.  The bundled `LegalGentowNodeRead` has three clauses — legality, exact
  key value, `ψ`-root — and nothing `Kt`-valued.
* The canonical L-read on level kernels (CC-10), the separate arena family (CC-11), the
  threshold/window dictionary (CC-7, landed at C130th — its `thresholdZ_lt_u_succ` teeth are
  not duplicated here), `RealizedInput` (CC-8), and the actual S2 point instance (CC-17).
  Nothing here inhabits `NodePointSource`; every theorem consumes an instance.

## ⚠ Deferred CC-3 tie (an integration finding, not a math gap)

The natural one-liner tying this layer to CC-3's canonical receiver — the transport hom of
`DeepTower.terminalReceiver` at a live level is `algebraMap ∘ towerHom`, junk-free — CANNOT be
stated here yet: `C130k` and `C130tr` both declare
`Uniformity.Density.Tower.instDecidableStageLive`, so importing both fails
(`import … failed, environment already contains …`).  Orchestrator fix needed (rename/delete
one duplicate); the tie is then `rfl`-adjacent via `terminalReceiver_levelHom_live`.

DEPENDS: C130k (CC-1 skeleton: `NodePointSource`, `KeyChain`, live ranges, `GaugeLive.stageLive`)
· C130s2 (CC-2: `s2DepthTwo`, `s2DepthTwoKeyChain` — the teeth) · C83 (`DeepTower.hψ/he/hf/u/f`).

## Status

Zero `sorry`; no new axiom; no `unsafe`; no `True` body; axiom footprint Lean-core only
(AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-! ## 1. The ambient transport and the transported `ψ`

`psi_root`'s transport composite, named (GENTOW5.16's tower transport `ι^{(i+1)}`, read at
level `i` into the ambient field), and the transported minimal polynomial it acts through.
These are receiver-level objects: no `NodePointSource` is needed to define them. -/

namespace TerminalReceiver

variable (R : TerminalReceiver F H₀ hpin r W Kt)

/-- GENTOW5.16's transport, ambient-valued at level `i`: the composite `K_i →+* Kt →+* L`
that `psi_root` evaluates through.  Total over `i` (like `levelHom`); every LAW below is
live-range guarded. -/
noncomputable def ambientHom (i : ℕ) : W.fld i →+* L :=
  (algebraMap Kt L).comp (R.levelHom i)

/-- Anti-drift pin: `ambientHom` is definitionally `psi_root`'s transport composite. -/
theorem ambientHom_def (i : ℕ) :
    R.ambientHom (L := L) i = (algebraMap Kt L).comp (R.levelHom i) := rfl

/-- The ambient transport is injective at every level: a ring hom out of a field. -/
theorem ambientHom_injective (i : ℕ) :
    Function.Injective (R.ambientHom (L := L) i) :=
  RingHom.injective _

/-- GENTOW5 S2.3: the transported level-`i` minimal polynomial `ψ_i`, pushed along the
ambient transport — the polynomial whose root law is `psi_root`. -/
noncomputable def psiTransported (i : ℕ) : Polynomial L :=
  (W.ψ i).map (R.ambientHom (L := L) i)

/-- Anti-drift pin: the transported `ψ` is `map` along `ambientHom`, nothing else. -/
theorem psiTransported_def (i : ℕ) :
    R.psiTransported (L := L) i = (W.ψ i).map (R.ambientHom (L := L) i) := rfl

/-- On the gauge-live range the transported `ψ` is monic (C.83's `hψ`, transported). -/
theorem psiTransported_monic {i : ℕ} (hi : GaugeLive r i) :
    (R.psiTransported (L := L) i).Monic :=
  (W.hψ i hi.1 hi.2).1.map _

/-- On the gauge-live range the transported `ψ` keeps its degree `f_(i+1)` (C.83's `hψ`). -/
theorem psiTransported_natDegree {i : ℕ} (hi : GaugeLive r i) :
    (R.psiTransported (L := L) i).natDegree = W.f (i + 1) := by
  rw [psiTransported_def, (W.hψ i hi.1 hi.2).1.natDegree_map, (W.hψ i hi.1 hi.2).2.2.1]

/-- The transported `ψ` is nonconstant on the gauge-live range (`0 < f_(i+1)` by `W.hf`):
the root law below is about a genuine polynomial. -/
theorem psiTransported_natDegree_pos {i : ℕ} (hi : GaugeLive r i) :
    0 < (R.psiTransported (L := L) i).natDegree := by
  rw [R.psiTransported_natDegree (L := L) hi]
  exact W.hf (i + 1) (by omega) hi.2

/-- The transported `ψ` keeps its nonzero constant coefficient (C.83's `hψ` clause
`(ψ i).coeff 0 ≠ 0`, through the injective ambient transport). -/
theorem psiTransported_coeff_zero_ne_zero {i : ℕ} (hi : GaugeLive r i) :
    (R.psiTransported (L := L) i).coeff 0 ≠ 0 := by
  rw [psiTransported_def, Polynomial.coeff_map]
  intro h
  exact (W.hψ i hi.1 hi.2).2.2.2
    (R.ambientHom_injective (L := L) i (by rw [h, map_zero]))

/-- ★ The `Lˣ`-forcing theorem (freeze v2 §4: "`ψ_(a+1)(0) ≠ 0` … admits only an `Lˣ` value"):
EVERY root of the transported `ψ` is nonzero.  So the unit codomain of the carrier's
`ambientLetter` field is forced by the source clauses, not chosen for convenience. -/
theorem psiTransported_root_ne_zero {i : ℕ} (hi : GaugeLive r i) {z : L}
    (hz : (R.psiTransported (L := L) i).IsRoot z) : z ≠ 0 := by
  rintro rfl
  exact R.psiTransported_coeff_zero_ne_zero (L := L) hi
    (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hz)

end TerminalReceiver

namespace NodePointSource

/-! ## 2. The legal P-locus (`Point`/`Pt`), exported

GENTOW5.19's `P_{i+1}` at the carrier: the stage-`i` legal points as a subtype, with the
canonical (choice) legal point that CC-8's `RealizedInput` and CC-17's gate can consume.
Nonemptiness is the `point_exists` SOURCE field — never derived from a bare tower. -/

/-- GENTOW5.19: the stage-`i` legal P-locus, as a subtype of the carrier's point type. -/
def LegalPt (S : NodePointSource (L := L) W receiver K) (i : ℕ) : Type :=
  {x : S.Point // S.Pt i x}

/-- The legal locus is nonempty at every live stage — the `point_exists` source field,
re-read at the subtype (GENTOW5.19's nonemptiness hypothesis, carried not proved). -/
theorem legalPt_nonempty (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : Nonempty (S.LegalPt i) :=
  S.point_exists i hi

/-- The canonical legal point at a live stage (choice on `point_exists`).  This is the
supply for `RealizedInput`'s `point` field (CC-8) at any instance. -/
noncomputable def legalPoint (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : S.Point :=
  ((S.point_exists i hi).some : {x : S.Point // S.Pt i x}).1

/-- The canonical legal point is legal. -/
theorem legalPoint_mem (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : S.Pt i (S.legalPoint i hi) :=
  ((S.point_exists i hi).some : {x : S.Point // S.Pt i x}).2

/-! ## 3. Pointwise value arithmetic

Derived laws of the point read (`pointHgt` through `pointHgt_eval` and the `valueOn`
source laws) — the dv-arithmetic GENTOW5.19's exactness clauses ride on. -/

/-- The point read of `0` is `⊤` at a live stage (evaluation is `0`; `value_zero`). -/
theorem pointHgt_zero (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : StageLive r i) (x : S.Point) : S.pointHgt i x 0 = ⊤ := by
  rw [S.pointHgt_eval i x 0, Polynomial.eval₂_zero, S.value_zero i hi]

/-- The point read is multiplicative at a live stage: the evaluation is a ring hom and
`valueOn` is multiplicative (`value_mul`). -/
theorem pointHgt_mul (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : StageLive r i) (x : S.Point) (A B : Polynomial O) :
    S.pointHgt i x (A * B) = S.pointHgt i x A + S.pointHgt i x B := by
  rw [S.pointHgt_eval i x (A * B), S.pointHgt_eval i x A, S.pointHgt_eval i x B,
    Polynomial.eval₂_mul]
  exact S.value_mul i hi _ _

/-- The point read of a positive power: `pointHgt (A^m) = m • pointHgt A` (`1 ≤ m`). -/
theorem pointHgt_pow (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : StageLive r i) (x : S.Point) (A : Polynomial O) (m : ℕ) (hm : 1 ≤ m) :
    S.pointHgt i x (A ^ m) = m • S.pointHgt i x A := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  clear hm
  induction k with
  | zero => rw [pow_one, one_nsmul]
  | succ n ih =>
      rw [pow_succ, S.pointHgt_mul hi x _ A, ih, succ_nsmul (S.pointHgt i x A) (n + 1)]

/-! ## 4. The exact key values at legal points

GENTOW5.19's exactness clause `v(Φ_i(ξ)) = u_{i+1}` (in the carrier's stage normalization),
exported and consumed: the coercion pin, finiteness, and the power law — the last is the
height-arithmetic half of GENTOW5.16's `Λ_i` dv-value-`0` derivation. -/

/-- Coercion pin for the exact key value: the same law with the `ℤ`-cast spelled out. -/
theorem key_value_coe (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : GaugeLive r i) (x : S.Point) (hx : S.Pt i x) :
    S.pointHgt i x (K.keyAt i) = ((W.u (i + 1) : ℤ) : WithTop ℤ) := by
  exact_mod_cast S.key_value i hi x hx

/-- The key value at a legal point is FINITE (it is the exact integer `u_(i+1)`) —
the `< ∞` half of GENTOW5.19's exactness, derived rather than assumed. -/
theorem key_value_ne_top (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : GaugeLive r i) (x : S.Point) (hx : S.Pt i x) :
    S.pointHgt i x (K.keyAt i) ≠ ⊤ := by
  rw [S.key_value i hi x hx]
  exact WithTop.natCast_ne_top _

/-- ★ The exact key-POWER value at a legal point: `pointHgt (Φ_i^m) = m·u_(i+1)` exactly
(`1 ≤ m`).  GENTOW5.16's height arithmetic, from `key_value` and multiplicativity. -/
theorem key_value_pow (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : GaugeLive r i) (x : S.Point) (hx : S.Pt i x) (m : ℕ) (hm : 1 ≤ m) :
    S.pointHgt i x (K.keyAt i ^ m) = ((m * W.u (i + 1) : ℕ) : WithTop ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  clear hm
  induction k with
  | zero => rw [pow_one, zero_add, one_mul]; exact S.key_value i hi x hx
  | succ n ih =>
      rw [pow_succ, S.pointHgt_mul hi.stageLive x _ _, ih, S.key_value i hi x hx,
        show (n + 1 + 1) * W.u (i + 1) = (n + 1) * W.u (i + 1) + W.u (i + 1) from by ring,
        Nat.cast_add]

/-- GENTOW5.16's `Λ_i`-numerator height, at the tower's own stage data: the read of
`Φ_i^(e_(i+1))` at any legal point is `e_(i+1)·u_(i+1)` exactly (`e_(i+1) ≥ 1` by `W.he`).
The dv-value-`0` claim for the letter `Λ_i` is this height matched against the normalizer's
— the normalizer half is CC-4/CC-10's and is NOT claimed here. -/
theorem key_value_pow_e (S : NodePointSource (L := L) W receiver K) {i : ℕ}
    (hi : GaugeLive r i) (x : S.Point) (hx : S.Pt i x) :
    S.pointHgt i x (K.keyAt i ^ W.e (i + 1)) =
      ((W.e (i + 1) * W.u (i + 1) : ℕ) : WithTop ℤ) :=
  S.key_value_pow hi x hx (W.e (i + 1)) (W.he (i + 1) (by omega) hi.2)

/-! ## 5. The ambient letters and the transported `ψ`-root

GENTOW5.16's letters and S2.3's transport, at the carrier: the letter is a unit, its
nonzeroness is FORCED by the root law (not just recorded by the `Lˣ` codomain), and the
`psi_root` source law is exported at the named transport objects. -/

/-- The ambient letter is nonzero in `L` (the `Lˣ` codomain, read off). -/
theorem ambientLetter_ne_zero (S : NodePointSource (L := L) W receiver K) (i : ℕ) :
    (S.ambientLetter i : L) ≠ 0 :=
  Units.ne_zero _

/-- The `psi_root` source law, exported at the named transport hom (`ambientHom` is
definitionally `psi_root`'s composite). -/
theorem psi_root_ambientHom (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : GaugeLive r i) :
    Polynomial.eval₂ (receiver.ambientHom (L := L) i) (S.ambientLetter i : L) (W.ψ i) = 0 :=
  S.psi_root i hi

/-- ★ The transported `ψ`-root, as a root of the transported polynomial: the ambient letter
is a root of `psiTransported` on the gauge-live range (GENTOW5 S2.3's transport clause). -/
theorem ambientLetter_isRoot (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : GaugeLive r i) :
    (receiver.psiTransported (L := L) i).IsRoot (S.ambientLetter i : L) := by
  have h : ((W.ψ i).map (receiver.ambientHom (L := L) i)).eval (S.ambientLetter i : L) = 0 := by
    rw [Polynomial.eval_map]
    exact S.psi_root i hi
  exact h

/-- The letter's nonzeroness DERIVED from the root law and `ψ_i(0) ≠ 0` alone — the honesty
check that the clauses force the unit value even without the `Lˣ` codomain. -/
theorem ambientLetter_ne_zero_forced (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : GaugeLive r i) : (S.ambientLetter i : L) ≠ 0 :=
  receiver.psiTransported_root_ne_zero (L := L) hi (S.ambientLetter_isRoot i hi)

/-! ## 6. The bundled legality read (freeze-v2 layer C.130g, descent-free)

The clause-by-clause legal GENTOW5 node read at a stage and a point: legality, the exact key
value, and the transported `ψ`-root.  Three clauses, none `Kt`-valued — OM-8 L3 (descent) is
excluded by construction, exactly as design §10 row CC-9 and freeze v2 §7 row C.130g demand.
The threshold/window clause lives in CC-7's `CanonicalThresholdAt` (C130th), not here. -/

/-- Freeze-v2 layer C.130g's legality read, at the carrier: `x` is a stage-`i` legal node
point, the key value at `x` is exactly `u_(i+1)`, and the ambient letter is a transported
`ψ_i`-root.  NO descent clause (nothing `Kt`-valued) — the design's explicit fence. -/
def LegalGentowNodeRead (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (x : S.Point) : Prop :=
  S.Pt i x ∧
    S.pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ) ∧
    (receiver.psiTransported (L := L) i).IsRoot (S.ambientLetter i : L)

/-- Anti-drift pin: the legality read is exactly its three displayed clauses. -/
theorem legalGentowNodeRead_def (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (x : S.Point) :
    S.LegalGentowNodeRead i x ↔
      (S.Pt i x ∧
        S.pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ) ∧
        (receiver.psiTransported (L := L) i).IsRoot (S.ambientLetter i : L)) :=
  Iff.rfl

/-- ★ **NODE CC-9, the producing theorem**: on the gauge-live range EVERY legal point
satisfies the full legality read — the three clauses are the `Pt` membership and the
`key_value`/`psi_root` source laws, consumed verbatim. -/
theorem legalGentowNodeRead_of_pt (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : GaugeLive r i) (x : S.Point) (hx : S.Pt i x) :
    S.LegalGentowNodeRead i x :=
  ⟨hx, S.key_value i hi x hx, S.ambientLetter_isRoot i hi⟩

/-- Existence of a fully-read legal node point on the gauge-live range (via the canonical
`legalPoint`; nonemptiness is still the carried `point_exists` source field). -/
theorem exists_legalGentowNodeRead (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : GaugeLive r i) : ∃ x : S.Point, S.LegalGentowNodeRead i x :=
  ⟨S.legalPoint i hi.stageLive,
    S.legalGentowNodeRead_of_pt i hi _ (S.legalPoint_mem i hi.stageLive)⟩

namespace LegalGentowNodeRead

variable {S : NodePointSource (L := L) W receiver K} {i : ℕ} {x : S.Point}

/-- Projection: legality (`Pt`). -/
theorem pt (h : S.LegalGentowNodeRead i x) : S.Pt i x := h.1

/-- Projection: the exact key value. -/
theorem key_value (h : S.LegalGentowNodeRead i x) :
    S.pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ) := h.2.1

/-- Projection: the transported `ψ`-root. -/
theorem psi_isRoot (h : S.LegalGentowNodeRead i x) :
    (receiver.psiTransported (L := L) i).IsRoot (S.ambientLetter i : L) := h.2.2

end LegalGentowNodeRead

end NodePointSource

end Uniformity.Density.Tower

/-! ## Teeth — the S2 depth-two specialization (elaboration regressions)

Statements about ANY instance over the landed CC-2 occurrence (`s2DepthTwo`,
`s2DepthTwoKeyChain`): they check that the layer specializes to the S2 numerals with no
type/universe/index obstruction (design §6's sense of "instantiable").  They do NOT claim an
instance exists — the actual S2 point instance is CC-17's. -/

section Teeth

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {Kt : Type} [Field Kt] {L : Type} [Field L] [Algebra Kt L]
variable (R : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2 (s2DepthTwo h2 hq) Kt)
variable (S : NodePointSource (L := L) (s2DepthTwo h2 hq) R (s2DepthTwoKeyChain h2 hq))

-- at depth two the only gauge-live stage is 1
example : GaugeLive 2 1 := ⟨le_rfl, by omega⟩
example {i : ℕ} (hi : GaugeLive 2 i) : i = 1 := by
  obtain ⟨h1, h2'⟩ := hi; omega

-- the exact key value at any legal point specializes to the S2 numeral: the frame key
-- `Φ′ = x² − 2` reads exactly `5 = u₂` (GENTOW5.19's ladder at the S2 witness)
example (x : S.Point) (hx : S.Pt 1 x) :
    S.pointHgt 1 x ((s2Frame h2 hq).key) = (5 : WithTop ℤ) := by
  have h := S.key_value 1 ⟨le_rfl, by omega⟩ x hx
  rw [(s2DepthTwoKeyChain h2 hq).keyAt_one] at h
  rw [show (s2DepthTwo h2 hq).u (1 + 1) = 5 from rfl] at h
  exact_mod_cast h

-- the transported minimal polynomial at the S2 occurrence has degree f₂ = 1
example : (R.psiTransported (L := L) 1).natDegree = 1 :=
  (R.psiTransported_natDegree (L := L) ⟨le_rfl, by omega⟩).trans rfl

-- the bundled legality read specializes and is realized at the canonical legal point
example : ∃ x, S.LegalGentowNodeRead 1 x :=
  S.exists_legalGentowNodeRead 1 ⟨le_rfl, by omega⟩

end Teeth

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.TerminalReceiver.ambientHom
#print axioms Uniformity.Density.Tower.TerminalReceiver.ambientHom_def
#print axioms Uniformity.Density.Tower.TerminalReceiver.ambientHom_injective
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported_def
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported_monic
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported_natDegree
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported_natDegree_pos
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.TerminalReceiver.psiTransported_root_ne_zero
#print axioms Uniformity.Density.Tower.NodePointSource.LegalPt
#print axioms Uniformity.Density.Tower.NodePointSource.legalPt_nonempty
#print axioms Uniformity.Density.Tower.NodePointSource.legalPoint
#print axioms Uniformity.Density.Tower.NodePointSource.legalPoint_mem
#print axioms Uniformity.Density.Tower.NodePointSource.pointHgt_zero
#print axioms Uniformity.Density.Tower.NodePointSource.pointHgt_mul
#print axioms Uniformity.Density.Tower.NodePointSource.pointHgt_pow
#print axioms Uniformity.Density.Tower.NodePointSource.key_value_coe
#print axioms Uniformity.Density.Tower.NodePointSource.key_value_ne_top
#print axioms Uniformity.Density.Tower.NodePointSource.key_value_pow
#print axioms Uniformity.Density.Tower.NodePointSource.key_value_pow_e
#print axioms Uniformity.Density.Tower.NodePointSource.ambientLetter_ne_zero
#print axioms Uniformity.Density.Tower.NodePointSource.psi_root_ambientHom
#print axioms Uniformity.Density.Tower.NodePointSource.ambientLetter_isRoot
#print axioms Uniformity.Density.Tower.NodePointSource.ambientLetter_ne_zero_forced
#print axioms Uniformity.Density.Tower.NodePointSource.LegalGentowNodeRead
#print axioms Uniformity.Density.Tower.NodePointSource.legalGentowNodeRead_def
#print axioms Uniformity.Density.Tower.NodePointSource.legalGentowNodeRead_of_pt
#print axioms Uniformity.Density.Tower.NodePointSource.exists_legalGentowNodeRead
#print axioms Uniformity.Density.Tower.NodePointSource.LegalGentowNodeRead.pt
#print axioms Uniformity.Density.Tower.NodePointSource.LegalGentowNodeRead.key_value
#print axioms Uniformity.Density.Tower.NodePointSource.LegalGentowNodeRead.psi_isRoot

end AxCheck
