# GSW verdict — GENTOW2 signed-shape sweep (adjudication unit)

**5 RE-SIGN (exact diffs delivered, proposed amendment A-C.12) · 5 HOLD (named unformalized
source math) · 1 no-action.** Full evidence, quotes, suppliers, and the unified diff:
`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md`. Elaboration authority:
`leanfinal/scratch/GSW_check.lean` (`lake env lean` exit 0, zero warnings; no sorry, no
axiom; its single proof is Lean-core). Leanspec NOT touched (read-only; orchestrator
enacts). Nothing committed.

## Summary table

| node | signed name | verdict | key fact |
|---|---|---|---|
| C.99 | `gentow2_Bpp` | **RE-SIGN** | + B-1 normalizer supply (3 binder families, source S5.2 ll.740–744); re-signed form **PROVED from the A-C.11 class fields alone** — machine certificate `gentow2_Bpp_resigned_provable`, Lean-core |
| C.99 | `theta_letter_valued` | **RE-SIGN shape; proof BLOCKED** | + same B-1 supply; exponents ℕ→ℤ (source: "grade-determined INTEGERS"; LP1 pin ϑ(0) = z₂⁻¹z₁⁻⁵ — ℕ-form overclaims); letter clause stays OPEN-LETTERS |
| C.100 | `gentow2_Bp` (+`_unit_iff`) | **HOLD** | it IS lemma B′; needs OPEN-EVAL-ISO (Prop 1.15/Thm 4.8) + polynomial-valued graded laws (eq (14), Cor 4.4(3), Lemma 3.17); honest antecedent = the conclusion; carrier re-base doesn't cure (reads deliberately unrelated, design §8) |
| C.101 | `gentow2_B` | **RE-SIGN** | + recipe data `hlift`/`hliftdeg` (source S5 ll.307–309) + per-slot B′ unit law `hunit` (explicit discharge-node hypothesis = C.100 at slots); then provable from `Rres_recipe` + rewriting (sketch in doc) |
| C.102 | `letter_formula` | **HOLD** | needs OPEN-LETTERS (Def 3.12 γ-recursion) + OPEN-EVAL-ISO; U7 §8.4: must be a THEOREM of that dictionary; `letter_compat` is only a compatibility signature |
| C.103 | `gentow2_A` | **RE-SIGN** | `hadm` gains the omitted `ψ₃(0) ≠ 0` conjunct (source S4 ll.187–188; = `KP_criterion`'s 5th antecedent, GTB option (a)) + `hliftdeg`; then provable from `KP_criterion`/`KP_irred`/`KP_keyAt`/`Rres_keyAt`/`nuEquiv_iff_Rres` (sketch in doc) |
| C.85 | `theta_dictionary` | **FALSE-AS-SIGNED (plausible) → RE-SIGN** | GTC's s=t=0 collapse confirmed; counterexample construction specified (LP1, A=B=n̂₂(19), sealed pin res(n̂₂(19)²/n̂₂(38)) = z₁² ≠ 1); re-signed with dv₂-height-tied quantifiers + product exactness/pinned-ness hypotheses — absorbs the PE4 mode exactly; proof deferred to the dv-graded-engine vocabulary |
| C.88 | `tower_slot_exact` | **HOLD** | HE7 ANNEX R1-b/R1-c untranscribed + norm↔root-value bridge (OPEN-ROOT-EVAL; future home = U12 `CompletedRootAmbient` + `root_value`) |
| C.88 | `tower_lift` | **HOLD** | R1-c + the graded expansion pack (eq (14)/Cor 4.4(3)/Lemma 3.17 — in neither `FGMNCalculus` nor `FGMNSourceLaws`); any curing antecedent = the conclusion |
| C.106 | manifest | **NO ACTION** | assemble after the re-signed names land (GTC's disposition stands) |

## Cross-cutting

* **Option (b) RE-BASE rejected globally**: CC-17 landed mid-run — the S2
  `ChainRealization`'s source side (`node`/`fgmn`/`fgmnLaws`/OPEN-DICT-2/4) is itself a
  blocked frontier (`S2SourceFrontier`), and the carrier's laws are field-for-field the
  class laws (CC-16), so re-basing swaps conditionality carriers without adding provable
  content. All decisions are (a) or (c); §10 stays on `[FGMNCalculus …]` per A-C.11.
* Follow-ups flagged (doc §10): `TowerDatum.deepTower` still unlanded in leanfinal (blocks
  STATING C.100–C.103 there); C.89 `gentow5w_two` cascade (needs the same B-1 supply);
  `Rres_recipe` zero-digit scope finding; optional Lean refutation tooth for the untied
  C.85.

## Verification

```text
cd leanfinal && lake env lean scratch/GSW_check.lean
```

Exit 0; sole output: `gentow2_Bpp_resigned_provable` depends on
`[propext, Classical.choice, Quot.sound]`.
