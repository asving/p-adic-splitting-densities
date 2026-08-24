/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130pk

/-!
# Uniformity.ChapC.C99gt — Chapter C, NODES C.99–C.101 (GENTOW2 B″/B′/B)

Unit GTA.  The five signed declarations at these three nodes are **BLOCKED** against the
landed A-C.11 `FGMNCalculus` hypothesis carrier.  Full per-node evidence is recorded in
`runs/wave-b/verdict_GTA.md`.

## C.99 — `gentow2_Bpp` and `theta_letter_valued`: BLOCKED

The source proof of B″ explicitly uses that the two ladder monomials have exact grades:

> “`N := n̂₂(u₃)`, `M := n̂₂(u₃d)`: ladder monomials, `deg < m₃`, single-point
> `N₃`-polygon, exact grades `κ̄` resp. `β_t` (B-1).”

(`lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md`, S5.2, lines 740–744.)  The signed
statement supplies no `I.ExactGrade` hypothesis for either `I.chainNorm r u'` or
`I.chainNorm r ((f' - t) * u')`, and the class has no field relating `chainNorm` to
`ExactGrade`.  Consequently `I.Rgr_mul` cannot establish the power identity and
`I.Rgr_ne_zero` cannot justify cancellation in the definition of `I.thetaRatio`.

The companion is independently blocked: the only class field mentioning `letterZ` is
`letterZ_ne_zero`.  No class law says that the normalizer ratio is a monomial in
`letterZ 1` and `letterZ 2`; this is the audited `OPEN-LETTERS` gap.  Even
`I.thetaRatio 1 = 1` needs the same missing nonvanishing input for the denominator.

## C.100 — `gentow2_Bp` and `gentow2_Bp_unit_iff`: BLOCKED

The A-C.11 re-sign is respected verbatim: the old ordinary-divisibility `hfree` is absent
and the live scope is `g.natDegree < T.D₂`.  That repair does not supply the missing
cross-read dictionary.  The source fixes

> “the GENHN-2′ coherent read ... through the CANONICAL EVALUATION identification
> `k(L2) ≅ F₃` [Prop. 1.15].”

(`GENTOW2_PROOF_2026-08-09.md`, S5.1, lines 500–509, `(R-repo)`.)  The signed Lean statement instead
quantifies an arbitrary `ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂`, with no
hypothesis identifying `ρ` with that canonical evaluation map.  No `FGMNCalculus` field
mentions `repoRead`, `dv2Res`, `towerLabelEquiv`, or `ρ`, so the displayed equality cannot
be derived for a generic class instance.  This is precisely the audited `OPEN-EVAL-ISO`
gap.  The iff companion would follow algebraically from `gentow2_Bp` and its nonzero
repo-read hypothesis, but its required equality theorem is unavailable for the same reason.

There is also a mechanical prerequisite: `TowerDatum.deepTower` and
`TowerDatum.deepTower_data`, the unsigned §10 preamble constants used by both signatures,
have no leanfinal declarations.  Thus neither signed C.100 signature is currently statable.

## C.101 — `gentow2_B`: BLOCKED

The only applicable class law is `I.Rres_recipe`.  It requires, for every `t < f'`, both

* `I.ExactGrade ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u'))`, and
* `(k2DigitLift T (c t) ((f' - t) * u')).natDegree < (I.keyAt 2).natDegree`.

Neither premise occurs in the signed statement and neither follows from a class field.
They are hypotheses of the source lemma itself:

> “Let the recipe data be as in the r3 box: `k̂_t ∈ K[x]` with
> `deg k̂_t < deg Φ₂`, `dv₂`-height `u₃(f₃-t)`, and K₂-digit residual class `c_t`.”

(`GENTOW2_PROOF_2026-08-09.md`, S5, lines 303–315, statement of GENTOW2-B.)  The proof then uses the
exact on-line value of every correction term before applying residual additivity.  In the
landed vocabulary this is the audited `OPEN-DICT-2` bridge between concrete
`k2DigitLift` data and the opaque `ExactGrade` predicate.  The arbitrary `ρ` has the same
`OPEN-EVAL-ISO` problem as C.100, and the unlanded `TowerDatum.deepTower` also prevents the
signature from being stated.

## Status

No declaration is emitted: adding the missing premises would change the signed statements,
while manufacturing the missing laws would add new axioms.  Hence this file contains no
`sorry`, no new axiom, no `unsafe`, and no weakened theorem.  Since there are no declarations,
the requested per-declaration `#print axioms` footer is vacuous.
-/
