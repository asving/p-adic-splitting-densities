/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C42
import Uniformity.ChapC.C83
import Uniformity.ChapC.C38a

/-!
# Uniformity.ChapC.C102gt — Chapter C, NODES C.102–C.104 (GENTOW2)

Unit GTB. Target nodes (leanspec `leanspec/Leanspec/ChapC.lean`, the A-C.1 §10 GENTOW2 supply
layer, `#check` manifest at `NODE C.106`):

* **C.102** `letter_formula` — the γ-letter identity
  `I.letterZ 2 * I.letterZ 1 ^ (T.e₂ * T.u₂ / F.e₁) = ρ.symm (AdjoinRoot.root T.ψ₂)`.
* **C.103** `gentow2_A` — `THEOREM GENTOW2-A`, the depth-3 key certificate: `I.KP (recipe3 …)`,
  `Irreducible (recipe3 …)`, `¬ I.nuEquiv (recipe3 …) (composedKey T)`.
* **C.104** `repoRead` — the `(R-repo)` reads convention, `repoRead L g := dv2Res L g`.

## Verdict (see `runs/wave-b/verdict_GTB.md` for the full record)

* **C.104 LANDED** below, byte-identical to the leanspec `def` (axiom→def is not even needed:
  `repoRead` was already signed as a `def`, not an `axiom`).
* **C.102 and C.103 are BLOCKED.** Both signatures quantify over an ARBITRARY hypothesis
  instance `[I : FGMNCalculus (T.deepTower hπ) e' f' u']` (`FGMNCalculus` a HYPOTHESIS CARRIER
  per the A-C.6/A-C.11 dispositions — `C92_VACUITY`, no `fgmn_calculus_exists`), so a proof must
  derive the conclusion from `I`'s FIELDS ALONE. It cannot, for reasons independent of each
  other and independent of whichever concrete instance eventually gets supplied:

  1. **C.102 (`letter_formula`).** The class carries exactly one field mentioning `letterZ`
     (`letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0`) — pure nonvanishing, with no law
     relating `letterZ i` to `ρ`, to `AdjoinRoot.root T.ψ₂`, or to any other class field. No
     combination of `nuEquiv_iff_Rres`, `Rres_keyAt`, `KP_criterion`, `Rgr_*`, `Rres_*` mentions
     `letterZ` either, so there is no algebraic route from the class to the stated equality for
     an arbitrary `I`. This is exactly the audited gap **OPEN-EVAL-ISO**
     (`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` §5: *"published Proposition 1.12
     and Theorem 4.3 … is the bridge used in the proof of C.100 and the letter formula, but it
     cannot be expressed by `ρ : W.fld 2 ≃+* AdjoinRoot T.ψ₂` alone"*) and **OPEN-LETTERS**
     (§5: *"fraction-field rational functions, homogeneous initial forms, and embeddings of all
     `F_i` into the terminal field"* — none of this is in `DeepTower`/`FGMNCalculus`).
     **Wanted field:** a law of the shape `letterZ_recursion : ∀ …, letterZ (i+1) * letterZ i ^ k
     = (some explicit AdjoinRoot-root read)`, which does not exist yet in either the leanspec
     class or the U7/U9 adjudicated field list.

  2. **C.103 (`gentow2_A`).** Reaching `I.KP (recipe3 T e' f' u' c)` has exactly one entry point,
     `KP_criterion`, whose five antecedents are `g.Monic`, `g.natDegree = e'*f'*(keyAt r).natDegree`,
     `Irreducible (Rres g)`, `(Rres g).natDegree = f'`, **and** `(Rres g).coeff 0 ≠ 0`. The
     hypothesis bundle `hadm` supplied by the signed statement gives only the middle two
     (`Irreducible (I.Rres (recipe3 …))` and `.natDegree = f'`); it does **not** give
     `(I.Rres (recipe3 …)).coeff 0 ≠ 0`. This is not a bookkeeping gap: the informal source
     theorem this node transcribes states the hypothesis explicitly — `GENTOW2-A`
     (`lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md` S4, lines 187–188): *"Let ψ₃ ∈ F₃[y] …
     monic irreducible of degree f₃ ≥ 1 **with ψ₃(0) ≠ 0**"* — the Lean avatar of FGMN's
     `s(g) = 0` (`KP_criterion`'s own faithfulness note: *"The extra nonzero-constant hypothesis
     exposes a source invariant that the provisional type hid"*). `hadm` in `leanspec/Leanspec/
     ChapC.lean` (NODE C.103, ~line 2553) omits it. Nor is there a way to derive it from the
     other fields for an arbitrary `I`: doing so would need `Rres_recipe` (which needs
     `I.ExactGrade ((f'-t)*u') (k2DigitLift T (c t) ((f'-t)*u'))` for every live `t`, hypotheses
     nowhere supplied) followed by `Rgr_ne_zero` at `t = 0` — and `ExactGrade` has **no** class
     law connecting it to the concrete `k2DigitLift` construction (audited gap **OPEN-DICT-2**,
     same §5 table). Separately, even the `Monic`/`natDegree` legs need a `k2DigitLift`
     degree/grade companion lemma that `Uniformity/ChapC/C56a.lean` explicitly defers ("the
     exactness/`deg < D₂` companions are fleet-time nodes, not this def's obligation").
     **Wanted field/hypothesis:** either (a) `hadm` re-signed to add
     `(I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0` (the direct transcription of the informal
     theorem's `ψ₃(0) ≠ 0`), or (b) a class law discharging `OPEN-DICT-2` so it can be derived.

  Neither gap is closable by more proof effort against the *current* `FGMNCalculus` field list;
  both are corpus-content gaps (missing class fields / an under-hypothesized `hadm`), flagged per
  the parent CLAUDE.md trust boundary (statements, not proofs, are where errors hide) rather than
  silently patched — no statement weakening, no new axiom, no `sorry`.

  A third, purely mechanical prerequisite also blocks even *stating* C.102/C.103 today:
  `TowerDatum.deepTower`/`TowerDatum.deepTower_data` (the unlabeled §10 preamble axioms just
  above leanspec NODE C.99, `leanspec/Leanspec/ChapC.lean:2420-2427`) are not yet landed in
  `leanfinal` (confirmed absent repo-wide; independently flagged already at
  `Uniformity/ChapC/C84.lean:110`, *"`TowerDatum.deepTower` … is an axiom constant … NOT
  statable yet"*). This file does not attempt to supply it: it is not one of this unit's three
  assigned nodes, it is shared infrastructure other in-flight §10 nodes (C.100/C.101) also need,
  and — per (1)/(2) above — supplying it would not unblock C.102 or C.103 anyway, since their
  gaps are in the `FGMNCalculus` field list itself, not in `DeepTower`.

## DEPENDS

C.42 (`TowerDatum`) · C.83 (`DeepTower`) · C.38a (`dv2Res`, `LevelDatum`) for C.104.

## Status

C.104 landed: sorry-free, axiom-free (Lean core only). C.102/C.103: no declaration emitted
(content-blocked; see above), so no `sorry`/`axiom`/`unsafe`/weakened statement is introduced.
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## NODE C.104 — the two-reads convention (the `(R-repo)` leg)

Byte-identical to the leanspec `def` (`leanspec/Leanspec/ChapC.lean`, NODE C.104, ~line 2455):
no `axiom → theorem` transcription is even needed here, since the signed node is already a
`def`. `(R-FGMN)` is `FGMNCalculus.Rgr`/`.Rres`, out of scope for this def. -/

/-- **NODE C.104** — the coherent repo-side read of an `O[x]`-coefficient at level 2: the
existing C.38a `K₂`-read `dv2Res`, renamed to the §10 convention. -/
noncomputable def repoRead {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : AdjoinRoot L.r :=
  dv2Res L g

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.repoRead

end AxCheck
