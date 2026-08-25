# Verdict — unit U15: the packaging route DECIDED (Route A + the parameter adjudication)

Date: 2026-08-25 · Deliverables: `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` (decision
+ evidence + node plan + diffs, NOT applied) · `leanfinal/scratch/U15_check.lean`
(elaboration authority: exit 0, zero errors/warnings, no `sorry`/axiom, every
`#print axioms` row exactly `[propext, Classical.choice, Quot.sound]`) · this verdict.
No corpus, leanspec, or roll-up file touched; no commit.

## The decision

**Route A — retype the packaging — with Route C's parameter adjudication folded in; Route B
(build μ₃) deferred to a separately-scoped ~20–30-node campaign at the CORRECTED depth-2
parameters (2,1,21).**  Six enactment nodes PK-1..6 + one doc node (plan §5).

## The three load-bearing findings (each machine-pinned in `U15_check.lean`)

1. ★ **The depth-2 parameters were mis-anchored — (2,1,5) belongs to depth 1; depth 2 is
   (2,1,21).**  The CC17-verdict orchestrator addendum's untraced flag is now adjudicated:
   U9 Q1 is CONFIRMED (the class at depth `r` = calculus of the next augmentation), and
   under it the S2 witness's own `u 3 = 21` (rfl) fixes the depth-2 triple.  Decisively,
   the consumers' OWN floor hypothesis enforces it: `hfloor : e' * W.Econst 2 < u'` at S2
   is `20 < u'` — machine pins `depthTwo_floor_rejects_five` (`¬(20 < 5)`) and
   `depthTwo_floor_accepts_u3` (`20 < 21`); `gentow2_A`'s `hκ : 10 < u'` rejects 5 the
   same way; the depth-1 floor `4 < 5` accepts the landed records' typing.  So SG-1's
   `Nonempty (FGMNCalculus (s2DepthTwo …) 2 1 5)` is a phantom target no consumer can
   ever consume, and "Route B as written" (satisfy the r=2-typed records AS TYPED) is
   incoherent — μ₃'s recipe grades are multiples of 21, not 5.
2. ★ **The carrier was a shotgun marriage; both refutations were the machine catching it.**
   CC-16's `toCalculus` consumes only `keys`/`fgmn`/`fgmnLaws`; the socket view layer
   consumes NO fgmn leg, NO `(e',f',u')`, and NONE of the four evaluation fields
   (grep-verified over C130vw/ar/pt/st/cr/th).  CC-13's own `grade_compat` ties
   `fgmn.nextValue` to `node.pointHgt r` (= μ_r), contradicting the legs' depth-r typing
   (= μ_{r+1}) — the landed model's `s2SourceDataOne.nextValue = s2Hgt₂` (rfl) realizes
   the honest (r−1)-anchored reading.  Hence the retype: `ChainRealization` becomes
   node-side only (split ambient `E`, no `(e',f',u')`), and the class packaging factors
   through the standalone map `fgmnCalculusOf : KeyChain → FGMNSourceData →
   FGMNSourceLaws → FGMNCalculus`.
3. ★ **The first non-vacuous class discharge is one packaging call away — elaborated
   TODAY**: `U15Check.s2_calculus_discharge : Nonempty (FGMNCalculus (s2DepthOne h2 hq)
   2 1 5)`, UNCONDITIONAL (no `w`, no `ev`, no `lf`), Lean-core, with rfl pins
   `Rres = s2NormRes`, `KP = S2KeyPoly`.  Likewise the retyped carrier + realized input
   inhabit at S2 with NO quarantined premise (`s2CarrierV2`/`s2RealizedInputV2`,
   conditional only on `w : S2LevelOneThreshold`; all three dictionary fields `rfl`) —
   after PK-1..6 the sockets fire `ev`/`lf`-free.

## What Route A delivers vs what stays open

Delivered by PK-1..6: non-vacuous I.10a/b socket applications + refinement at the
`keyAt 2 + 1` occurrence (conditional exactly on `w` + `IsAdicComplete`); the unconditional
anchored class discharge; the architecture the future μ₃ campaign plugs into with zero new
packaging.  NOT delivered (honest): no GENTOW consumer conclusion fires at S2 — blocked by
the deferred μ₃ instance (depth 2) and by two flagged supply gaps: `htie` (OPEN-LETTERS)
and the NEW review row that `hprev : I.PrevGrade u'` is unsatisfiable at any
evenness-realized instance passing `hcop` (`¬S2PrevGrade 5 ∧ ¬S2PrevGrade 21`, pinned;
the μ₃ operators' clearing choice — U14 §8.1 / OPEN-DICT-2 — must be decided before the
Route-B campaign; at `f' = 1` the `ratio_power_law` never consumes `hprev`, so an A-C.15
fence `2 ≤ f'` is a candidate unblock).

## Review-list rows opened (doc §6)

(1) the (2,1,5)→(2,1,21) depth-2 amendment (print-read-adjacent; three independent legs);
(2) the `hprev`/`hcop` clearing tension; (3) leanspec C.90's single-triple truncation
family `I : ∀ i ≤ r, FGMNCalculus (W.trunc i hi) e' f' u'` — satisfiable only for
uniform-data towers, needs a per-level `(e'ᵢ,f'ᵢ,u'ᵢ)` family at its next re-sign;
(4) the depth-1 consumer's remaining holds (`htie`, `hprev`).

## Flagged for human review (trust boundary — new scratch statements)

`fgmnCalculusOf` (the factored packaging map), `s2AnchorCalculus`/`s2_calculus_discharge`
(the anchored instance statements), `ChainRealizationV2`/`V2b`/`RealizedInputV2` (the
proposed retyped shapes), and the four floor/PrevGrade numeral pins.
