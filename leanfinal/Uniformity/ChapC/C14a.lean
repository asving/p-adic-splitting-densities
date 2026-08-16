/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C03
import Uniformity.ChapC.C15
import Uniformity.ChapC.C19
import Uniformity.ChapB.B59a
import Uniformity.ChapH.H54

/-!
# Uniformity.ChapC.C14a — the H §8 carrier bridge: `genreDatum`, `stageLiftIA`, `stageLiftO`

**Chapter C, NODE C.14a** [def] [fresh] [signed: A-C.1(b)] (`blueprint/CHAP-C_tower_grammar.md`
§3, the level frame; the A-C.1 amendment set governs). **ENV-C1 + `[Finite (ResidueField O)]`**
(the latter only on the declarations that read `Q = residueCard O`). Six declarations, all
definitional; the single theorem is `rfl`.

This is the **one door** through which chapter C consumes chapter H's §8 lift layer (GC-5 / H-14).
It exists because of stub-gate defect **D19**: chapter C's carrier `KeyFrame` (C.01) and chapter
H's carrier `GenreDatum` (H.01) do not match, so `C.43`'s `stageLiftO` — the object the composed
key's display is written in — was not constructible from anything landed.

* `KeyFrame.Pin F H₀` — the pin proposition, NAMED (amendment **A-C.1(c)**, adopting the stub
  gate's D4 recommendation). Nothing but an abbreviation for the 90-character
  `npHgt X F.key (sideMin X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)` that §§3–4 spell out at ~30 sites.
* `KeyFrame.genreDatum F hh hkey` — the adapter `KeyFrame → GenreDatum`, at
  `(Q, e₁, f₁, μ, h) := (residueCard O, F.e₁, F.f₁, 2, F.h)`.
* `KeyFrame.stageLiftIA F i a lift` — H.54's own summand shape over the frame's numerals, TOTAL.
* `stageLiftIA_eq_stageLift'` — the `rfl`-grade reconciliation of the two.
* `resLift` — a choice-section of the residue map `O → ResidueField O`.
* `KeyFrame.stageCoord` / `KeyFrame.stageLiftO` — the element-at-height-`M` form that C.43's
  display (and C.56a's `k2DigitLift`) consume.

## What the mismatch was, and how the bridge closes it without touching chapter H

Landed `GenreDatum` (`ChapH/H01.lean`) carries five proof fields: `hQ : 2 ≤ Q`, `he₁ : 1 ≤ e₁`,
`hh : 1 ≤ h`, `hkey : 2 ≤ e₁ * f₁`, `hmul : 2 ≤ μ`, `hcop : Nat.Coprime h e₁`. Landed `KeyFrame`
(`ChapC/C01.lean`) has **no `Q`**, **no `μ`**, **no `2 ≤ e₁ * f₁`**, and deliberately ADMITS
`h = 0` (the degenerate frame, kept so that C.05's level-1 reconciliation is definitional). Three
of the six gaps are closable outright and three are not:

* `Q := residueCard O` with `hQ` the landed `two_le_residueCard` — free, given
  `[Finite (ResidueField O)]`.
* `he₁ := F.he₁` (`0 < F.e₁` *is* `1 ≤ F.e₁`) and `hcop := F.hcop` — free, the frame has them.
* `μ := 2`, `hmul := le_rfl` — a **DUMMY**. Legitimate exactly because H §8's lift layer never
  reads `μ`: `stageLift' G π i a lift = Σ_{s < G.f₁} C (lift s · π^(a − s·G.h)) · X^(i + G.e₁·s)`
  (`ChapH/H54.lean:76`) mentions `G.f₁`, `G.h`, `G.e₁` and nothing else. This was the half of the
  blueprint's ⚠ at C.14 step 2 that the stub gate DISCHARGED by inspection; it is re-pinned below
  by the `rfl` reconciliation, which would fail outright if the body read another field.
* `hh : 1 ≤ F.h` and `hkey : 2 ≤ F.e₁ * F.f₁` — **explicit hypotheses**, because they are false
  on frames `KeyFrame` admits. They are the corpus's own frame conditions (`EFF.HE6.08`'s
  `1 ≤ h`; `GENHN.CLASS`(i)'s "`e₁f₁ ≥ 2`, else the event is order-1 α/β"), which is why the
  right move is to demand them of the caller rather than to widen H.01 or narrow C.01.

**H's landed side is untouched.** No chapter-H declaration is restated, generalized, or copied
except `stageLift'`'s *body shape*, which is immediately proved equal to `stageLift'` itself.

## Why `stageLiftIA` exists at all, rather than calling `stageLift'` directly

Because a definition must be total. `stageLift' (F.genreDatum hh hkey) π i a lift` mentions the
two proof terms `hh`, `hkey`, so any def phrased through it would carry them as arguments — and
then `stageLiftO`, and then `composedKey` (C.43), and then every §7 statement, would carry them
in the *term*, making two occurrences of the composed key with different proofs syntactically
distinct objects. `stageLiftIA` takes the shape and no proofs; the perimeter conditions sit on
the *theorems* that consume H.55 (exact height) and H.56 (the residue identity), which is
precisely where the corpus puts them. `stageLiftIA_eq_stageLift'` is the transport, and it is
`rfl`, so no rewriting cost is incurred at the seam either.

## The `(i, a)` solve, and H.54's signed lesson

H.54's ⚠ SIGNATURE NOTE records that the `normIdx` form (`M ↦ (i(M), a(M))` via `Exists.choose`)
was WITHDRAWN in favour of explicit `i`, `a` with the height equation `i·h + e₁·a = M` carried by
the consuming lemmas. `stageLiftO` obeys that lesson at the C side: the pair is produced by
C.15's `slotIdx` — a *computable, junk-`0`-defaulting* solve, not a choice — as
`i := F.slotIdx M`, `a := (M − i·F.h) / F.e₁`. C.16's `slotIdx_spec` (`i < e₁` and
`i·h ≡ M [MOD e₁]`) is what makes `a` the honest quotient and the height equation hold; that
lemma is cited by the consumers, never here. At binders where the congruence fails the value is
junk, exactly as `slotIdx` is junk there — the totality convention of the whole gauge layer.

## Trust-boundary notes on `stageCoord` (⚠ new definitions, flagged for human review)

`stageCoord F H₀ hpin c s` is the `s`-th `F_Q`-digit of a stage-field element `c` in the letter
basis `{η^s}`. `F.stageField H₀ hpin` is `AdjoinRoot (F.frameRes H₀ hpin)` (C.03), so `c` is a
class of polynomials over `resField X`; the digit is read off **a chosen representative**
(`(AdjoinRoot.mk_surjective c).choose`) and transported to `ResidueField O` along B.59a's landed
`resFieldXEquiv : ResidueField O ≃+* resField X`. Two consequences a consumer must know:

1. **Representative-dependence.** Different representatives of the same class differ by a
   multiple of `frameRes`, so `stageCoord` is NOT determined by `c` alone at `s ≥ f₁`, nor is the
   `choose` guaranteed to have degree `< f₁`. It is a *section*, not an invariant. Every
   downstream statement pins it the way H.56 does — through a residue equation asserted of the
   resulting lift — never by an equation about `stageCoord` in isolation.
2. **Junk outside the basis range.** `stageLiftO` reads `stageCoord … s` only for `s < F.f₁`
   (the `Finset.range F.f₁` of `stageLiftIA`), which is the basis range; values at larger `s`
   never enter.

`resLift` is likewise a section, of `IsLocalRing.residue`, and satisfies
`residue (resLift x) = x` by `Exists.choose_spec` — the only property of it anyone should use.

## Divergences from the blueprint text, recorded

* **`resLift` is PUBLIC, not `private`.** The blueprint's C.14a block calls it "a private helper
  of this file". It cannot be: the blueprint's OWN signature for `C.56a`'s `k2DigitLift`
  (§8, and `leanspec/Leanspec/ChapC.lean`'s A-C.1 layer) writes `resLift (F.stageCoord …)` in the
  body of a declaration in another file, and Lean's `private` is not importable. Landing it
  private would BLOCK C.56a and C.62. Visibility only; the statement is the signed one verbatim.
* **`KeyFrame.Pin` is landed here**, per A-C.1(c), and is *not* retrofitted into C.03/C.09/C.19/
  C.21/C.22/C.42/C.44/C.45, which already spell the proposition out. Both spellings are the same
  `Prop` and interconvert by `id`; the retrofit is a mechanical RE-PLAN item, not this node's.
* **`isKey_X` is NOT landed here.** C.44's file note anticipates "when C.14a lands a public
  `isKey_X`"; the blueprint's C.14a SIGNATURE block declares no such thing, and this node does not
  need it (`stageCoord` uses only the `CommRing` structure on `AdjoinRoot`, never a `Field`).
  The four private copies stay where they are; retiring them remains an unassigned RE-PLAN item.

**DEPENDS.** C.01 (`KeyFrame`) · C.03 (`frameRes`, `stageField`) · C.15 (`slotIdx`) ·
H.01 (`GenreDatum`) · H.54 (`stageLift'`) — all by committed node ID (GC-13(b)); the consuming
height/residue clauses enter through H.55/H.56 at the consumers, never here. Landed
`two_le_residueCard` (`Uniformity/Density/LocalData.lean`), `resFieldXEquiv` (B.59a's auxiliary).
Mathlib: `AdjoinRoot.mk_surjective`, `IsLocalRing.residue_surjective`.

**PROOF.** Definitional; `stageLiftIA_eq_stageLift'` is `rfl` (structure projections of a
constructor application reduce).

SOURCE: `EFF.HE6.08` (the `1 ≤ h` frame hypothesis); `EFF.GENHN.07` clause (i) (the `2 ≤ e₁f₁`
clause, via H.01); `EFF.GENHN.81` (`LEMMA GENHN-LIFT`, the lift whose shape `stageLiftIA`
repeats); H.54's ⚠ SIGNATURE NOTE (the `(i, a)`-explicit lesson); stub-gate defects D19/D20 and
recommendation D4 (the adjudication record).

**TEETH.** Signed non-applicable (an adapter; its consumers' teeth fire at C.14, C.43 and §13).
The local substitute is the `rfl` reconciliation itself, which pins that `stageLift'` reads
exactly `(f₁, e₁, h)` — a transposed field or a `μ`-read would break it — plus the two
`example`s below fixing `f₁ = 1, 2`.

ENVIRONMENT: ENV-C1 + `[Finite (ResidueField O)]` on the `Q`-reading declarations.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## The named pin proposition (A-C.1(c)) -/

/-- The pin proposition: `H₀` is the numeral naming the polygon height of `F.key` at the frame
side's left endpoint (the GC-1 `sideMin` pin). Spelled out ~30 times across §§3–4; named here
per amendment A-C.1(c) (the stub gate's D4 recommendation). -/
def KeyFrame.Pin (F : KeyFrame O π) (H₀ : ℕ) : Prop :=
  npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)

/-! ## (i) the carrier adapter -/

/-- The frame's genre datum: H.01's landed carrier at
`(Q, e₁, f₁, μ, h) = (residueCard O, F.e₁, F.f₁, 2, F.h)`.

The two hypotheses are exactly the corpus conditions `KeyFrame` deliberately lacks —
`hh : 1 ≤ F.h` (`EFF.HE6.08`'s frame; `KeyFrame` admits `h = 0` for C.05's sake) and
`hkey : 2 ≤ F.e₁ * F.f₁` (`GENHN.CLASS`(i)'s composite-stage clause). The `μ`-slot is the
**dummy** `2`: H §8's lift layer never reads it (`stageLift'`, `ChapH/H54.lean:76`), which the
`rfl` below re-pins. -/
noncomputable def KeyFrame.genreDatum (F : KeyFrame O π) [Finite (ResidueField O)]
    (hh : 1 ≤ F.h) (hkey : 2 ≤ F.e₁ * F.f₁) : Uniformity.Density.Induction.GenreDatum where
  Q := residueCard O
  e₁ := F.e₁
  f₁ := F.f₁
  μ := 2
  h := F.h
  hQ := two_le_residueCard O
  he₁ := F.he₁
  hh := hh
  hkey := hkey
  hmul := le_rfl
  hcop := F.hcop

/-! ## (ii) the lift over the frame's numerals, and (iii) the reconciliation -/

/-- H.54's summand shape over the frame's own numerals:
`Σ_{s < f₁} (lift s · π^(a − s·h)) · X^(i + e₁·s)`. TOTAL and hypothesis-free — the corpus
preconditions sit on the theorems that consume H.55/H.56, not on the object. -/
noncomputable def KeyFrame.stageLiftIA (F : KeyFrame O π) (i a : ℕ) (lift : ℕ → O) :
    Polynomial O :=
  ∑ s ∈ Finset.range F.f₁,
    Polynomial.C (lift s * π ^ (a - s * F.h)) * Polynomial.X ^ (i + F.e₁ * s)

/-- **The corpus perimeter, as one equation.** On `1 ≤ h`, `2 ≤ e₁f₁` the frame lift IS H.54's
`stageLift'` at the adapter datum — definitionally. H.55 (exact height, `deg < D′`) and H.56 (the
residue identity) transport through this and through nothing else: it is the single door of
GC-5 / H-14. -/
theorem stageLiftIA_eq_stageLift' (F : KeyFrame O π) [Finite (ResidueField O)]
    (hh : 1 ≤ F.h) (hkey : 2 ≤ F.e₁ * F.f₁) (i a : ℕ) (lift : ℕ → O) :
    F.stageLiftIA (π := π) i a lift
      = Uniformity.Density.Induction.stageLift' (F.genreDatum hh hkey) π i a lift := rfl

/-! ## (iv) the element-at-height form -/

/-- A choice-section of the residue map `O → ResidueField O`; its one property is
`residue (resLift x) = x` (`resLift_spec`).

**Public, against the blueprint's "private helper" prose:** C.56a's `k2DigitLift` writes it into
a body in another file, and `private` is not importable. -/
noncomputable def resLift (x : ResidueField O) : O :=
  (IsLocalRing.residue_surjective (R := O) x).choose

/-- `resLift` is a section: `residue (resLift x) = x`. The only fact about it any consumer may
use — the choice itself is junk. -/
theorem resLift_spec (x : ResidueField O) : IsLocalRing.residue O (resLift x) = x :=
  (IsLocalRing.residue_surjective (R := O) x).choose_spec

/-! ### The letter power basis, and the digit read on it

**REPAIR of 2026-08-16 (see the module docstring).** The digits below are read off
`AdjoinRoot.powerBasis`, not off a chosen `AdjoinRoot.mk`-preimage: that is what makes
`stageCoord` an invariant of `c` and gives it the reconstruction identity `sum_stageCoord`, the
pin every consumer of `stageLiftO` needs. `isKey_X` is the D9 private-copy pattern
(C.04/C.12/C.14/C.19/C.21/C.22/C.44 each carry one): `private` does not export, and this is what
names the `Field (resField X)` instance `AdjoinRoot.powerBasis` demands. -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense; the private copy
pattern, because `private` does not export. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

noncomputable local instance instFieldResFieldX :
    Field (resField (Polynomial.X : Polynomial O)) :=
  instFieldResField isKey_X

private theorem frameRes_ne_zero (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    F.frameRes H₀ hpin ≠ 0 :=
  (F.hresirr H₀ hpin).1.ne_zero

/-- The **letter power basis** of the stage field `K = AdjoinRoot ψ` over `resField X`: the basis
`{η^s}_{s < f₁}` in which the frame's digits are read (`stagePB_dim`, `stagePB_gen`). -/
noncomputable def KeyFrame.stagePB (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    PowerBasis (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) :=
  AdjoinRoot.powerBasis (frameRes_ne_zero F H₀ hpin)

/-- The letter basis has exactly `f₁` elements: `dim = deg ψ = f₁` (`KeyFrame.hresirr`). -/
theorem KeyFrame.stagePB_dim (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    (F.stagePB H₀ hpin).dim = F.f₁ := by
  rw [KeyFrame.stagePB, AdjoinRoot.powerBasis_dim]
  exact (F.hresirr H₀ hpin).2

/-- The letter basis is generated by C.19's stage letter `η`. -/
theorem KeyFrame.stagePB_gen (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    (F.stagePB H₀ hpin).gen = F.stageLetter H₀ hpin := by
  rw [KeyFrame.stagePB, AdjoinRoot.powerBasis_gen, KeyFrame.stageLetter]

/-- The stage coordinate read: the `s`-th `F_Q`-digit of a stage-field element in the letter
basis `{η^s}`, taken through `AdjoinRoot.powerBasis` (`stagePB`) and B.59a's identification
`ResidueField O ≃+* resField X`.

An **invariant of `c`**, not a section (REPAIRED 2026-08-16; see the module docstring): it is a
basis coordinate, and `sum_stageCoord` is the reconstruction identity that pins it. Outside the
basis range (`s ≥ f₁`, i.e. `s ≥ (F.stagePB H₀ hpin).dim` by `stagePB_dim`) the read takes the
`else 0` branch of the `dif`, which `stageLiftO` never enters. -/
noncomputable def KeyFrame.stageCoord (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (c : F.stageField H₀ hpin) (s : ℕ) : ResidueField O :=
  (resFieldXEquiv O).symm
    (if h : s < (F.stagePB H₀ hpin).dim then (F.stagePB H₀ hpin).basis.repr c ⟨s, h⟩ else 0)

/-- **The reconstruction identity — what makes `stageCoord` pinnable.** The letter-basis digits
reassemble the element: `c = Σ_{s < f₁} coord_s · η^s`, with the digits carried from
`ResidueField O` to `K` along B.59a's identification and the algebra map.

This is exactly the clause the pre-repair `stageCoord` (a `Classical.choice` preimage read) could
not supply: `slotRes M (stageLiftO M c) = c`, the only equation that can pin `stageLiftO`, reduces
to it. -/
theorem KeyFrame.sum_stageCoord (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (c : F.stageField H₀ hpin) :
    ∑ s ∈ Finset.range F.f₁,
        algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
          (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
            (F.stageCoord H₀ hpin c s)) * F.stageLetter H₀ hpin ^ s = c := by
  have hdim : (F.stagePB H₀ hpin).dim = F.f₁ := F.stagePB_dim H₀ hpin
  have hgen : (F.stagePB H₀ hpin).gen = F.stageLetter H₀ hpin := F.stagePB_gen H₀ hpin
  have hsum := (F.stagePB H₀ hpin).basis.sum_repr c
  rw [← hdim]
  rw [← Fin.sum_univ_eq_sum_range
    (fun s => algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
      (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
        (F.stageCoord H₀ hpin c s)) * F.stageLetter H₀ hpin ^ s) (F.stagePB H₀ hpin).dim]
  have key : ∀ y : resField (Polynomial.X : Polynomial O),
      algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
        ((resFieldXEquiv O).symm y) = y := by
    intro y
    change (AdjoinRoot.of ((Polynomial.X : Polynomial O).map (residue O)))
        ((resFieldXEquiv O).symm y) = y
    rw [← resFieldXEquiv_coe]
    exact (resFieldXEquiv O).apply_symm_apply y
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  rw [PowerBasis.coe_basis, hgen, Algebra.smul_def, KeyFrame.stageCoord, dif_pos i.2, key]

/-- The blueprint's `stageLiftO`: the exact-height-`M` lift of a stage-field ELEMENT, i.e. the
object C.43's `composedKey` display and C.56a's `k2DigitLift` are written in.

The `(i, a)`-solve is C.15's `slotIdx` — `i := F.slotIdx M`, `a := (M − i·h) / e₁` — a computable
junk-defaulting solve rather than an `Exists.choose` (H.54's signed lesson); the height equation
`i·h + e₁·a = M` is C.16's business at the consumers. Digits by `stageCoord`, lifted by
`resLift`. -/
noncomputable def KeyFrame.stageLiftO (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (M : ℕ) (c : F.stageField H₀ hpin) : Polynomial O :=
  F.stageLiftIA (π := π) (F.slotIdx M) ((M - F.slotIdx M * F.h) / F.e₁)
    (fun s => resLift (F.stageCoord H₀ hpin c s))

end Uniformity.Density.Tower

/-! ## Unfolding checks — the summand shape at `f₁ = 1, 2`

`example`s, not declarations: they mirror H.54's own checks on the C side, so that a transposed
`i ↔ a` or an `e₁ ↔ h` swap in `stageLiftIA` cannot survive silently even if the `rfl`
reconciliation were ever to be re-proved by a tactic. -/

section UnfoldingChecks

open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `f₁ = 1`: the single term `lift 0 · π^a · X^i` — the normalizer `x^i π^a` itself. -/
example (F : KeyFrame O π) (i a : ℕ) (lift : ℕ → O) (hf : F.f₁ = 1) :
    F.stageLiftIA (π := π) i a lift = Polynomial.C (lift 0 * π ^ a) * Polynomial.X ^ i := by
  rw [KeyFrame.stageLiftIA, hf, Finset.sum_range_one]
  simp

/-- `f₁ = 2`: the second summand drops the `π`-exponent by exactly `h` and raises the
`X`-exponent by exactly `e₁` — the pair of moves that preserves the `dv`-height (H.55(iii)). -/
example (F : KeyFrame O π) (i a : ℕ) (lift : ℕ → O) (hf : F.f₁ = 2) :
    F.stageLiftIA (π := π) i a lift
      = Polynomial.C (lift 0 * π ^ a) * Polynomial.X ^ i
        + Polynomial.C (lift 1 * π ^ (a - F.h)) * Polynomial.X ^ (i + F.e₁) := by
  rw [KeyFrame.stageLiftIA, hf, Finset.sum_range_succ, Finset.sum_range_one]
  simp

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.Pin
#print axioms Uniformity.Density.Tower.KeyFrame.genreDatum
#print axioms Uniformity.Density.Tower.KeyFrame.stageLiftIA
#print axioms Uniformity.Density.Tower.stageLiftIA_eq_stageLift'
#print axioms Uniformity.Density.Tower.resLift
#print axioms Uniformity.Density.Tower.resLift_spec
#print axioms Uniformity.Density.Tower.KeyFrame.stagePB
#print axioms Uniformity.Density.Tower.KeyFrame.stagePB_dim
#print axioms Uniformity.Density.Tower.KeyFrame.stagePB_gen
#print axioms Uniformity.Density.Tower.KeyFrame.stageCoord
#print axioms Uniformity.Density.Tower.KeyFrame.sum_stageCoord
#print axioms Uniformity.Density.Tower.KeyFrame.stageLiftO

end AxCheck
