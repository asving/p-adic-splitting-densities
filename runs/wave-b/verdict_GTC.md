# GTC verdict — GENTOW supply C.105–C.106 + C.88/C.85

**SPLIT: 2 declarations LANDED, 4 sub-nodes BLOCKED (named reasons), 1 sub-node already
landed before this unit ran.** No `sorry`, no new axiom, no `unsafe`, no statement weakening.

## Deliverable

One new file: `leanfinal/Uniformity/ChapC/C105gt.lean` (imports `C105`, `C83` only). No
other file touched; leanspec read-only; roll-ups and other in-flight units' files untouched
(C130cr.lean, C130ar.lean, C131ae.lean, C99gt.lean [GTA], C102gt.lean [GTB], C131y.lean,
the E57 unit, the C78 unit — none of these were read or written). Nothing committed.

## Per-node verdict

| node | declaration | verdict | reason |
|---|---|---|---|
| C.105 | `wconj`, `wconj_invariants` | **ALREADY LANDED** (not by this unit) | Found pre-existing at `Uniformity/ChapC/C105.lean`, sorry-free/axiom-free, `Field K`-generic, no `FGMNCalculus` dependency. Rebuilt (`lake env lean`) to confirm: exit 0, Lean-core only. Re-exercised via `#print axioms` in the new file. |
| C.85 | `substitution_kills` | **LANDED** (this unit, in `C105gt.lean`) | `CommRing`-generic binomial-free identity; `pow_comp`/`sub_comp`/`X_comp`/`C_comp` + `ring`. No project dependency. |
| C.85 | `theta_dictionary` | **BLOCKED** | The signed `∃ θ, … ∀ s t A B, dv2Res A ≠ 0 → dv2Res B ≠ 0 → θ(s+t)·dv2Res(A*B) = θ s·θ t·(dv2Res A·dv2Res B)` quantifies `s, t : ℕ` with **no tie to A, B's grade**. Instantiating at `s = t = 0` (using the required `θ 0 = 1`) forces `dv2Res(A*B) = dv2Res A · dv2Res B` for *every* `A, B` with both sides nonzero — i.e. the theorem is provable only if `dv2Res` (`C38a.lean`) is already exactly multiplicative on its nonzero-image domain (θ then collapses to the constant `1`). No such multiplicativity fact for `dv2Res` exists anywhere in the corpus (checked: `rg dv2Res Uniformity/ChapC/*.lean` finds only congruence lemmas, never a `_mul`), and `dv2Res`'s definition (a residual polynomial keyed to *each polynomial's own* level-1 side set via `dvResPoly`) gives no structural reason to expect it. The informal proof cited (`EFF.GENTOW5.06`–`.10`, `spec/EFF-GENTOW5.md`) proves a **different, graded** statement (s, t tied to the actual heights of A, B via the ladder normalizer; θ a genuine per-height cocycle correction) — and is already flagged "unlanded existence statement" by `C84.lean`'s own trust-boundary notes (written before this unit ran). The Lean signature as elaborated does not carry that grading, so the cited proof does not certify the signed form. No proof prose bridges this; not attempted further. |
| C.88 | `boundRec` | **LANDED** (this unit, in `C105gt.lean`) | Pure recursive numeral definition over C.01/C.83 data (`F.e₁, F.f₁, F.h, W.e, W.f, W.u`); no proof obligation, transcribed verbatim. |
| C.88 | `tower_slot_exact` | **BLOCKED** | Conclusion is a concrete valuation identity over `O, g, C` (`addVal`/`Algebra.norm`, the `Uniformity/Density/TypeOf*.lean` machinery); its only tie to the hypotheses is through the OPAQUE `FGMNCalculus` fields `ExactGrade`/`KP`. None of the class's 13 law fields (checked against the landed twin `C130pk.lean`) mentions `addVal` or `Algebra.norm`, so for a generic instance the interface supplies no route to the conclusion — exactly the `OPEN-DICT-2`/`OPEN-DICT-3` gap the U7/U9 audits record as still open (`docs/PROJECT_STATE.md` §3–4). The informal route (`EFF.GENTOW5.22`) additionally needs a chapter-E `ANNEX-THEOREM R1-b/R1-c` with no Lean transcription yet. BLOCKED. |
| C.88 | `tower_lift` | **BLOCKED** | Conclusion (`∃ C, C.natDegree < W.Dcum r ∧ ExactGrade k C ∧ Rgr k C = s`) stays in-vocabulary but asserts scalar surjectivity of `Rgr` at *every* grade `k > boundRec W r` and *every* nonzero `s`, untied to the ambient instance's fixed `(e', f', u')`. The nearest class law, `Rres_exists`, only realizes a *polynomial*-shaped residual of the fixed degree `f'`; no field takes an arbitrary scalar target at an arbitrary grade to a realizing `C`. Same root cause as `tower_slot_exact` (hypothesis-carrier interface, not a realized calculus). BLOCKED. |
| C.106 | `#check` manifest (10 names) | **BLOCKED** | Documentation node, not a theorem. Seven of its ten checked names (`gentow2_Bpp`, `theta_letter_valued`, `gentow2_Bp`, `gentow2_B`, `letter_formula`, `gentow2_A`, `repoRead` = C.99–C.104) are owned by the concurrently-running sibling units GTA (`C99gt.lean`) and GTB (`C102gt.lean`) and are not confirmed landed at this unit's run time; this unit must not touch their files, and a `#check` importing them cannot be verified to build now. The other three (`s2Witness`, `shear_onesided_iff`, `wconj_invariants` = C.97/C.98/C.105) are already landed, but a three-of-ten subset would misrepresent the node. Assemble once GTA/GTB land. |

## Declarations landed (namespace `Uniformity.Density.Tower`, file `C105gt.lean`)

| declaration | kind |
|---|---|
| `substitution_kills` | theorem (NODE C.85, Step A) |
| `boundRec` | def (NODE C.88, recursion companion) |

Plus two `#print axioms` re-exercises of the pre-existing `wconj`/`wconj_invariants`
(NODE C.105, landed at `C105.lean` before this unit).

## Verification

```
cd leanfinal
lake env lean Uniformity/ChapC/C105.lean     # exit 0 (pre-existing; re-confirmed)
lake env lean Uniformity/ChapC/C105gt.lean   # exit 0, zero warnings
```

`#print axioms` (all 4 declarations exercised in `C105gt.lean`):
`[propext, Classical.choice, Quot.sound]` — Lean core only. No `sorry`, no new axiom
(`rg -n "sorry|^axiom" Uniformity/ChapC/C105gt.lean` matches nothing outside prose).
