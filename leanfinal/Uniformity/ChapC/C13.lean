/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C02
import Uniformity.ChapC.C09
import Uniformity.ChapC.C21

/-!
# Uniformity.ChapC.C13 — `IsTestKey`: what it is to be a level-2 test key

**Chapter C, NODE C.13** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame;
the A-C.1 amendment set governs). **ENV-C1** (`hπ` enters only through `slotRes`, which takes
`π` as data). One signed declaration, definitional.

`IsTestKey L Ψ` is `EFF.HE6.14`'s DEFINITION HE6-1 turned into a predicate. The corpus
*constructs* the enlarged test family
`Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_t·Φ′^{ℓt}`,  `dv(B_t) = (d−t)u`,  `res(B_t) = c_t`,
`B_t := 0` when `c_t = 0` (`d := deg r`, `c_t := r.coeff t`); the construction is
non-canonical (the lifts `B_t` are choices), so what lands here is its **output shape**, read
off the `Φ′`-development of `Ψ`, and the existence of a `Ψ` satisfying it is C.14's separate
obligation. Five conjuncts, in the order the corpus displays them:

1. `Ψ.Monic` — the family is monic by construction.
2. `Ψ.natDegree = L.keyDeg₂` — degree `D″ = D′ℓd` (C.09's dictionary numeral).
3. `dev F.key Ψ (ℓ·d) = 1` — the leading `Φ′`-digit is the top term `Φ′^{ℓd}`.
4. `dev F.key Ψ b = 0` for every `b < ℓ·d` that is **not** a multiple of `ℓ` — the corpus's sum
   runs over `Φ′^{ℓt}` only, so the off-lattice digits are absent.
5. For each `t < d`, the two `c_t`-cases: `c_t = 0` kills the digit outright, and `c_t ≠ 0`
   pins the digit's **stage height** at `(d−t)·u` (C.02's `stageHeight`, the corpus's `dv`) and
   its **normalized slot residue at that height** at `c_t` (C.21's `slotRes`, the A3 F-1
   TERMINAL `γ_k`).

## Why the residue clause is the `n(k)`-read and not the ϖ-read

Conjunct 5 reads through C.21's `slotRes` (`γ_k`), not through C.22's `twistRead`
(`γ_k·η^{−q(k)}`). That is the corpus's own bookkeeping and not a simplification: every height
occurring here is `(d−t)·u` with `u > ℓ·D′·h ≥ D′h` (C.09's `hκ`), so every one of these reads
sits in the **fullness regime**, where `EFF.HE6.13`'s NON-PROPAGATION route (1) makes the
`η^{−q(k)}` coset factor invisible to the clause being asserted (`η^{−q}·K^× = K^×`). Writing
the clause with the untwisted `γ_k` is therefore the faithful transcription of `EFF.HE6.14`,
and it is also what the twin signs.

## ⚠ ORDERING (the blueprint's own note, and defect D12(ii))

`slotRes` is C.21, a §4 object, and this is a §3 node: the DAG edge is **C.21 → C.13**, against
the index's section order. The blueprint states the inversion explicitly ("the index places C.13
in §3 because it is frame data; the fleet fires it after §4's C.21 lands"), and the
gate-verified twin `leanspec/Leanspec/ChapC.lean` lands `IsTestKey` inside its §4 block for
exactly that reason (defect **D12(ii)**). The file lands with the §3 ID it was signed under; the
import list is what records the real edge.

## What this node does NOT promise

It is a `Prop`-valued definition and carries no proof obligation. In particular: nothing here
says a test key **exists** (that is C.14, whose D20 re-sign adds the corpus frame hypothesis
`1 ≤ F.h`), nothing here says a test key is **unique** or canonical (it is not — the `B_t` are
choices), and nothing here connects `Ψ` to the block factor it is meant to test (that is §6's
`IsTestKey`-consuming divisibility layer, C.49 and its neighbours). Consumers that need the
`Φ′`-development of the explicit sum to *be* the displayed sum must cite B.05/B.06's uniqueness,
which C.14's proof does.

**FAITHFULNESS.** `L.r.coeff t` lives in the stage field `K = F.stageField H₀ hpin` (C.03) and
`slotRes … : F.stageField H₀ hpin`, so conjunct 5's residue equation is an equation in `K` with
no coercion inserted; the `stageHeight` equation is in `ℕ∞`, with `(d−t)·u` a **truncated**
`ℕ`-subtraction that is harmless because the clause is only ever asserted at `t < d`
(conjunct 5's binder). The whole predicate is stated over `L`'s own numerals — no numeral is
recomputed from `Ψ`.

**DEPENDS.** C.01 (`KeyFrame`) · C.02 (`stageHeight`) · C.09 (`LevelDatum`, `keyDeg₂`) ·
C.21 (`slotRes`) · B.02 (`dev`) — by committed node ID (GC-13(b)). Imports:
`Uniformity.ChapC.C02` (pulls C.01 and B.15), `Uniformity.ChapC.C09` (pulls C.03),
`Uniformity.ChapC.C21` (pulls C.15/C.16/C.17/C.19 and the B chain).

**PROOF.** Definitional. The body is the gate-verified twin's verbatim.

SOURCE: `EFF.HE6.14` (DEFINITION HE6-1, verbatim: `Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_tΦ′^{ℓt}`,
`B_t` with `dv(B_t) = (d−t)u` and residue `c_t`, `B_t := 0` if `c_t = 0`); `EFF.HE6.13` (the
corrected LIFT display, whose fullness clause licenses writing conjunct 5 with the untwisted
`γ_k`); A3 F-1 via `spec/EFF-HE6.md` `.58` (the normalized-γ TERMINAL form, C-H8 discipline).

**TEETH.** `EFF.HE6.14`'s audit (`deg(B_tΦ′^{ℓt}) < D″`; the lift heights exceed `(D′−1)h`) →
**Lean theorem at C.14 steps 2–3**, not here: at this node's binders there is no `Ψ` to audit,
only a shape to state. Signed non-applicable at the definition (§16's "definitional nodes
(C.01–C.13 class)" row).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `Ψ_{κ,r}`-hood: the slot-pinned shape of `EFF.HE6.14`'s enlarged test family, as a predicate
(the construction is non-canonical — the lifts `B_t` are choices — so C.14 supplies existence).
Conjunct 5's residue read is C.21's untwisted `γ_k`: at these heights `u > ℓD′h` the ϖ-twist
`η^{−q(k)}` is invisible (`EFF.HE6.13`'s NON-PROPAGATION route (1)). -/
def IsTestKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ : Polynomial O) : Prop :=
  Ψ.Monic ∧ Ψ.natDegree = L.keyDeg₂ ∧
  dev F.key Ψ (L.ℓ * L.r.natDegree) = 1 ∧
  (∀ b < L.ℓ * L.r.natDegree, ¬ L.ℓ ∣ b → dev F.key Ψ b = 0) ∧
  (∀ t < L.r.natDegree,
    (L.r.coeff t = 0 → dev F.key Ψ (L.ℓ * t) = 0) ∧
    (L.r.coeff t ≠ 0 →
      F.stageHeight (dev F.key Ψ (L.ℓ * t)) = (((L.r.natDegree - t) * L.u : ℕ) : ℕ∞) ∧
      F.slotRes H₀ hpin ((L.r.natDegree - t) * L.u) (dev F.key Ψ (L.ℓ * t)) = L.r.coeff t))

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.IsTestKey

end AxCheck
