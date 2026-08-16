/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C02
import Uniformity.ChapC.C09
import Uniformity.ChapC.C21
import Uniformity.ChapC.C22

/-!
# Uniformity.ChapC.C13 — `IsTestKey`: what it is to be a level-2 test key

**Chapter C, NODE C.13** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame;
the A-C.1 amendment set governs, **as amended by A-C.5's clause-5 re-sign of 2026-08-16**).
**ENV-C1** (`hπ` enters only through `slotRes`/`twistRead`, which take `π` as data). One signed
declaration, definitional.

## ⚠ CLAUSE 5 RE-SIGNED [A-C.5, 2026-08-16 — the residue read is the ϖ-read]

Conjunct 5's residue equation now reads through **C.22's `twistRead`** (`γ_k·η^{−q(k)}`), not
C.21's untwisted `slotRes` (`γ_k`). The rest of the predicate is byte-identical to the A-C.1
signing, and so are the signatures of C.14 and C.47 — the re-sign changes what `IsTestKey`
*means*, nowhere what it is *called*.

*Why.* `leanfinal/Uniformity/ChapC/C47_REFUTATION.lean.txt` machine-refutes NODE C.47 as frozen:
landed C.46 proves `twistRead ((f₂−t)u₂) (dev Φ′ Φ₂ (e₂t)) = r̃_t` for C.43's composed key, so the
untwisted clause 5 forced the letter collapse `η^{q((f₂−t)u₂)} = 1` — false at `(e₁,f₁,h) =
(2,2,3)` over `ℤ₃` (`Φ′ = x⁴ + 3⁶`, `η² = −1`, `q(27) = 13`, `η^{13} ≠ 1` in `F₉`). The SOURCE
decides which side was wrong: `EFF.HE6.14` (DEFINITION HE6-1, verbatim) writes the family's
residue condition as `res(B_t(θ)/ϖ(θ)^{(d−t)u}) = c_t` — division by `ϖ^k`, i.e. exactly
`twistRead` (`EFF.HE6.13`'s RIDER with `EFF.HE6.15`'s `[r2]` sign correction: the ϖ-read residue
is the `n(k)`-read residue times `res(n(k)/ϖ^k) = η^{−q}`). C.22's own node text is categorical
in the same direction ("All corpus residual polynomials read through THIS, never through the bare
`n(k)`-read C.21").

*Certified before signing* (`leanfinal/Uniformity/ChapC/C47_RESIGN_CERT.lean.txt`, sorry-free,
Lean-core): the re-signed clause AT THE COMPOSED KEY **is** landed C.46, so C.47's residue half is
discharged rather than relocated; and the re-signed predicate is **not vacuous** — test keys still
exist (C.14's `exists_testKey`, whose witness now lifts `η^{q((d−t)u)}·c_t` through the new
fullness lemma `KeyFrame.exists_twistRead_preimage`). REJECTED, with reasons recorded in the
blueprint: un-wrapping C.43, hypothesizing the collapse, and a separate `IsTestKey₂` for §6.

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
   its **ϖ-read residue at that height** at `c_t` (**[A-C.5]** C.22's `twistRead`, the A3 F-1
   TERMINAL `γ_k` divided by `ϖ^k` — `EFF.HE6.14`'s own display).

## ~~Why the residue clause is the `n(k)`-read and not the ϖ-read~~

**⚠ RETIRED [A-C.5, 2026-08-16].** The section below is the RATIONALE OF THE DEFECT, kept
verbatim as the record of what was believed and struck so that no reader takes it for current
doctrine (wrong comments self-reinforce). Its category slip: `EFF.HE6.13`'s NON-PROPAGATION
route (1) inventories the **twist-blind** clauses — `K^×`-fullness (`η^{−q}·K^× = K^×`) and
`T(k) = ∅` — which make a lift EXIST under either read; it says nothing about the VALUE, and
conjunct 5 pins a value. Fullness is blind to the twist for the SET of realizable residues, not
for the element of it that this clause names. The live doctrine is the ⚠ banner above.

> ~~Conjunct 5 reads through C.21's `slotRes` (`γ_k`), not through C.22's `twistRead`
> (`γ_k·η^{−q(k)}`). That is the corpus's own bookkeeping and not a simplification: every height
> occurring here is `(d−t)·u` with `u > ℓ·D′·h ≥ D′h` (C.09's `hκ`), so every one of these reads
> sits in the **fullness regime**, where `EFF.HE6.13`'s NON-PROPAGATION route (1) makes the
> `η^{−q(k)}` coset factor invisible to the clause being asserted (`η^{−q}·K^× = K^×`). Writing
> the clause with the untwisted `γ_k` is therefore the faithful transcription of `EFF.HE6.14`,
> and it is also what the twin signs.~~

## ⚠ ORDERING (the blueprint's own note, and defect D12(ii))

`slotRes` is C.21 and `twistRead` is C.22, both §4 objects, and this is a §3 node: the DAG edges
are **C.21 → C.22 → C.13**, against the index's section order. The blueprint states the inversion explicitly ("the index places C.13
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
`twistRead … : F.stageField H₀ hpin`, so conjunct 5's residue equation is an equation in `K` with
no coercion inserted; the `stageHeight` equation is in `ℕ∞`, with `(d−t)·u` a **truncated**
`ℕ`-subtraction that is harmless because the clause is only ever asserted at `t < d`
(conjunct 5's binder). The whole predicate is stated over `L`'s own numerals — no numeral is
recomputed from `Ψ`.

**DEPENDS.** C.01 (`KeyFrame`) · C.02 (`stageHeight`) · C.09 (`LevelDatum`, `keyDeg₂`) ·
C.21 (`slotRes`, through C.22) · **[A-C.5]** C.22 (`twistRead`, the read conjunct 5 takes) ·
B.02 (`dev`) — by committed node ID (GC-13(b)). Imports: `Uniformity.ChapC.C02` (pulls C.01 and
B.15), `Uniformity.ChapC.C09` (pulls C.03), `Uniformity.ChapC.C21` (pulls C.15/C.16/C.17/C.19 and
the B chain), **[A-C.5]** `Uniformity.ChapC.C22`.

**PROOF.** Definitional. The body is the gate-verified twin's verbatim.

SOURCE: `EFF.HE6.14` (DEFINITION HE6-1, verbatim: `Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_tΦ′^{ℓt}`,
`B_t` with `dv(B_t) = (d−t)u` and `res(B_t(θ)/ϖ(θ)^{(d−t)u}) = c_t`, `B_t := 0` if `c_t = 0` —
**[A-C.5]** the displayed division by `ϖ^k` is conjunct 5's read); `EFF.HE6.13` (the corrected
LIFT display, whose fullness clause licenses the EXISTENCE of the lifts at these heights, C.14's
step 1) with `EFF.HE6.15`'s `[r2]` sign correction (ϖ-read = `n(k)`-read × `η^{−q}`); A3 F-1 via
`spec/EFF-HE6.md` `.58` (the normalized-γ TERMINAL form, C-H8 discipline).

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
[A-C.5: conjunct 5's residue conjunct reads through `twistRead` (the ϖ-read of the source's own
display); the other four conjuncts are byte-identical to the A-C.1 signing.] -/
def IsTestKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ : Polynomial O) : Prop :=
  Ψ.Monic ∧ Ψ.natDegree = L.keyDeg₂ ∧
  dev F.key Ψ (L.ℓ * L.r.natDegree) = 1 ∧
  (∀ b < L.ℓ * L.r.natDegree, ¬ L.ℓ ∣ b → dev F.key Ψ b = 0) ∧
  (∀ t < L.r.natDegree,
    (L.r.coeff t = 0 → dev F.key Ψ (L.ℓ * t) = 0) ∧
    (L.r.coeff t ≠ 0 →
      F.stageHeight (dev F.key Ψ (L.ℓ * t)) = (((L.r.natDegree - t) * L.u : ℕ) : ℕ∞) ∧
      F.twistRead H₀ hpin ((L.r.natDegree - t) * L.u) (dev F.key Ψ (L.ℓ * t))
        = L.r.coeff t))

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.IsTestKey

end AxCheck
