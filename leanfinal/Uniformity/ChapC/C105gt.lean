/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C105
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C105gt — Chapter C, NODES C.105–C.106 + C.88/C.85 (GENTOW supply)

Unit GTC's landing for four §9/§10 GENTOW supply nodes. Verdict per node, honest and
non-uniform: two declarations transcribe cleanly; the rest are BLOCKED with a named,
checked reason (never a `sorry`, never an improvised proof). Full detail in
`runs/wave-b/verdict_GTC.md`.

## NODE C.105 — ALREADY LANDED (not by this unit)

`wconj`/`wconj_invariants` (leanspec `blueprint/CHAP-C_tower_grammar.md` §10, `[Q]`-free
`w`-blindness lemma) were landed at `Uniformity/ChapC/C105.lean` before this unit ran:
sorry-free, axiom-free, `Field K`-generic, no `FGMNCalculus` dependency. This file imports
it and re-exercises its axiom footprint below for the record; no re-declaration.

## NODE C.85 — SPLIT VERDICT

The signed node has two declarations, `theta_dictionary` and `substitution_kills`.

* `substitution_kills` — **LANDED** below. A binomial-free `CommRing` identity
  (`(X - C s)^μ` composed with `X + C s` collapses to `X^μ` because composition distributes
  over `-`/`^` and `(X + C s) - C s = X`); no project dependency, both characteristics.
* `theta_dictionary` — **BLOCKED**, and the reason is a checked logical fact about the
  signed statement, not a missing proof step. The signed existential quantifies `s t : ℕ`
  and `A B : Polynomial O` **independently** (no side condition ties `s`/`t` to the actual
  `dv2`-grade of `A`/`B`). Instantiating the inner `∀` at `s = t = 0` and using the required
  `θ 0 = 1` forces, for *every* `A B` satisfying the two `dv2Res ≠ 0` hypotheses:
  `dv2Res (A * B) = dv2Res A * dv2Res B` — i.e. the theorem is provable only if `dv2Res`
  (`C.38a`) is *already* exactly multiplicative on its whole nonzero-image domain, with no
  correction factor needed at all (θ then collapses to the constant `1`, and the general-`s,t`
  clause reduces to the same equation again after cancelling the nonzero `dv2Res (A*B)`,
  available in the field `AdjoinRoot L.r`). No such multiplicativity fact for `dv2Res`
  exists anywhere in the corpus (`rg dv2Res` over `Uniformity/ChapC/*.lean` turns up only
  congruence lemmas, `dv2Res_congr_of_lt`, never a `_mul`), and `dv2Res`'s own definition
  (`C38a.lean`) reads a residual polynomial keyed to *each polynomial's own* level-1 side
  set (`dvSideSet F A L.u L.ℓ` via `dvResPoly`) — a construction with no structural reason
  to respect products. The informal proof this node cites (`EFF.GENTOW5.06`–`.10`) proves a
  **different, graded** statement (`s`, `t` tied to the actual heights of `A`, `B` via the
  ladder normalizer `n̂`, θ a genuine per-height cocycle correction) — already flagged as an
  "unlanded existence statement" by the two `C.84` trust-boundary notes (lines ~77, ~260)
  written before this unit ran. The Lean signature as elaborated does not carry that grading,
  so the informal proof does not certify the signed form. No proof prose bridges this gap;
  not attempted further (no improvised mathematics).

## NODE C.88 — SPLIT VERDICT

Three declarations: `boundRec`, `tower_slot_exact`, `tower_lift`.

* `boundRec` — **LANDED** below (definitional transcription, no proof obligation; the two
  numerals it recurses over, `F.e₁ * F.f₁` and `W.e i * W.f i`, are C.01/C.83 data).
* `tower_slot_exact` — **BLOCKED**. Its conclusion is a concrete valuation identity,
  `(W.ehat r * e') * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat = g.natDegree * β`,
  entirely in terms of `O`, `g`, `C` (via `Algebra.norm`/`addVal`, the `Uniformity.Density`
  machinery in `TypeOf.lean`/`TypeOfFaithful.lean`). Its only tie to the hypotheses is
  through `I.ExactGrade β C` and `I.KP g`, both OPAQUE `Prop`-valued fields of the
  `FGMNCalculus` interface (`C130pk.lean`'s landed class twin). None of the class's law
  fields (`Rgr_zero_of_above`, `Rgr_add`, `Rgr_mul`, `Rgr_ne_zero`, `Rres_mul`,
  `Rres_recipe`, `Rres_exists`, `KP_criterion`, `KP_irred`, `KP_keyAt`, `Rres_keyAt`,
  `nuEquiv_iff_Rres`, `letterZ_ne_zero`) mentions `addVal` or `Algebra.norm` at all, so for
  a *generic* instance `I` — which is all a `[FGMNCalculus …]` binder gives — the interface
  supplies no route from `ExactGrade`/`KP` to a fact about the norm's valuation. This is
  exactly the gap the U7/U9 audits name `OPEN-DICT-2`/`OPEN-DICT-3` (the rational-grade ↔
  `ℕ`-grade dictionary and the `W.fld i ≃ F_i` coefficient identification) and record as
  still open project-wide (`docs/PROJECT_STATE.md` §3–4, 2026-08-24). The informal proof
  route (`EFF.GENTOW5.22`) additionally needs the general-depth tower-induction pattern
  anchored on a chapter-E `ANNEX-THEOREM R1-b/R1-c` that has no Lean transcription yet (it
  is recorded in the blueprint as a `[supplied-by: chapter E]` placeholder). BLOCKED: no
  proof prose bridges the class interface to the stated conclusion.
* `tower_lift` — **BLOCKED**. Its conclusion, `∃ C, C.natDegree < W.Dcum r ∧
  I.ExactGrade k C ∧ I.Rgr k C = s`, stays inside the class's own vocabulary (no norm/valuation
  needed), but it asserts *scalar surjectivity of `Rgr` at every grade `k > boundRec W r` and
  every nonzero `s : W.fld r`*, for parameters `k`, `s` with no tie to the fixed `(e', f', u')`
  of the ambient `FGMNCalculus W e' f' u'` instance. The nearest class law, `Rres_exists`,
  only realizes a *polynomial*-shaped residual `ψ` of the fixed degree `f'` with `ψ.coeff 0 ≠ 0`
  and (in the current re-signed form) `Irreducible ψ`; there is no field or combination of
  fields taking an arbitrary scalar target `s` at an arbitrary grade `k` to a realizing `C`.
  Same root cause as `tower_slot_exact`: the interface is a hypothesis carrier
  (`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` §7's own verdict), not yet a
  realized calculus, so a fact this strong about a *generic* instance is not derivable from
  its listed fields. BLOCKED: no proof prose bridges this gap.

## NODE C.106 — BLOCKED (documentation manifest, not a theorem)

The signed node is a `#check` manifest re-exporting ten already-signed names
(`gentow2_Bpp`/C.99, `theta_letter_valued`, `gentow2_Bp`/C.100, `gentow2_B`/C.101,
`s2Witness`/C.97, `shear_onesided_iff`/C.98, `letter_formula`/C.102, `gentow2_A`/C.103,
`repoRead`/C.104, `wconj_invariants`/C.105). Of these, seven — `gentow2_Bpp`,
`theta_letter_valued`, `gentow2_Bp`, `gentow2_B`, `letter_formula`, `gentow2_A`, `repoRead`
(= C.99–C.104) — are owned by the concurrently-running sibling units GTA (`C99gt.lean`) and
GTB (`C102gt.lean`), per `docs/PROJECT_STATE.md` §6's in-flight ledger; this unit must not
touch their files, and at this unit's run time they are not yet confirmed landed, so a
`#check` importing them cannot be verified to build. The other three names (`s2Witness`,
`shear_onesided_iff`, `wconj_invariants` = C.97/C.98/C.105) ARE already landed, but a
three-of-ten subset is not the signed manifest and would misrepresent the node as landed.
BLOCKED: assemble once GTA/GTB land.

## Status

Two declarations landed (`substitution_kills`, `boundRec`), sorry-free, axiom-free
(Lean core only, verified below). Four sub-nodes BLOCKED with named, checked reasons; zero
new axioms; zero `sorry`; zero statement weakening.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial Uniformity.Density.Leaf

/-! ## NODE C.85 (half) — `substitution_kills`, the binomial-free substitution identity -/

/-- **NODE C.85 (Step A) — `substitution_kills`.** Over any `CommRing R`, substituting
`X ↦ X + C s` into `(X - C s) ^ μ` collapses to `X ^ μ`: an identity of composition with `+`,
`-`, `^` distributing, and `(X + C s) - C s = X`. Binomial-free, both characteristics — no
project dependency. -/
theorem substitution_kills {R : Type*} [CommRing R] (μ : ℕ) (s : R) :
    ((Polynomial.X - Polynomial.C s) ^ μ).comp (Polynomial.X + Polynomial.C s)
      = Polynomial.X ^ μ := by
  rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  congr 1
  ring

/-! ## NODE C.88 (part) — `boundRec`, the recursion companion -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.88's `boundRec`** — the height threshold above which `(LIFT_i)` attains every
`K_{i+1}`-residue: `bound_1 = (e₁f₁ - 1)h`, `bound_{i+2} = (e_{i+2}f_{i+2}-1)u_{i+2} +
e_{i+2}·bound_{i+1}` (the PE5-F-3 restored token). Pure numeral recursion over C.01/C.83
data; no proof obligation. -/
def boundRec {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
    {r : ℕ} (W : DeepTower F H₀ hpin r) : ℕ → ℕ
  | 0 => 0
  | 1 => (F.e₁ * F.f₁ - 1) * F.h
  | (i + 2) => (W.e (i + 2) * W.f (i + 2) - 1) * W.u (i + 2) + W.e (i + 2) * boundRec W (i + 1)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

-- NODE C.105 — already landed at `Uniformity.ChapC.C105`; re-exercised here for the record.
#print axioms Uniformity.Density.Tower.wconj
#print axioms Uniformity.Density.Tower.wconj_invariants

-- NODE C.85 (half) and C.88 (part) — landed by this unit.
#print axioms Uniformity.Density.Tower.substitution_kills
#print axioms Uniformity.Density.Tower.boundRec

end AxCheck
