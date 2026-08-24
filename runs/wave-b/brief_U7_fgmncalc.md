# UNIT U7 — author the `FGMNCalculus` field list (C.92's structure; HIGH reasoning)

You are a research mathematician authoring a Lean-facing interface from cited literature.
Deliver a DOCUMENT (docs/in-progress/FGMNCALCULUS_FIELDLIST_<date>.md); nothing is signed.

CONTEXT: `FGMNCalculus W e' f' u'` is an interface CLASS over a `DeepTower W` (chapter C §10)
that the signed nodes C.88 (`tower_slot_exact`, `tower_lift`), C.89 (`GENTOW5W`, `Wle`),
C.90, C.99–C.101 consume via instance binders — but NO field list exists anywhere (recorded
blueprint defect). The blueprint's §10 design note lists fields only by CITED CLAUSE NAME:
"[Q1]…[Q10], Prop 1.15, Def 1.8's expansion-minimum, Cor 4.4, Thm 4.8, Lemma 3.17, Prop 1.9,
Def 3.12's γ_i-letters". The cite target C.92 is `fgmn_calculus_exists` (gate (b)).

READ: (1) blueprint/CHAP-C_tower_grammar.md §10 (search "FGMNCalculus" and the design-note
field list); (2) leanspec/Leanspec/ChapC.lean §§9–13 — EVERY consumer signature naming
`FGMNCalculus` and the member accessors used (`I.Rgr`, `I.chainNorm`, `I.thetaRatio`,
`I.letterZ`, `I.ExactGrade`, `I.KP`, `I.Rres`, `W.Dcum`, `W.Econst`, `W.ehat` …) — the field
list must TYPE every one of these uses; (3) leanfinal/Uniformity/ChapC/C83.lean (DeepTower);
(4) docs/references/FGMN_residual_ideals_2015_authorpdf.pdf and
docs/references/montes-blueprint.pdf + docs/references/HigherNewton.tex as the cited-source
pool (the [Q]-clauses live in the HigherNewton/Montes material; the residual-operator laws
in the FGMN paper — Thm 4.1, Cor 4.9, Cor 4.12, Lemma 5.2, Cor 5.5 are likely anchors).

DELIVER: the complete `class FGMNCalculus` field list as Lean signatures (each field: name,
type in corpus vocabulary, the cited clause it ports with paper+number, and a faithfulness
line), a consumer-typing matrix (each leanspec §10 use ↦ the fields that type it — verify by
hand-elaboration that every accessor exists at a compatible type), the
`fgmn_calculus_exists` cite statement draft, and the open questions. Full rigor; no invented
laws — every field must trace to a cited clause; mark anything you cannot source as OPEN.
