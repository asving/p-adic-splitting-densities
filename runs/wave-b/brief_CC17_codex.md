# Unit CC-17 (codex HIGH) — ACCEPTANCE GATE: the full S2 ChainRealization instance

You are a Lean 4 unit in the p-adic-splitting-densities campaign, executing node CC-17 of
the chain-realization carrier plan — the first of the two serial acceptance gates. Repo
root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(mathlib v4.31.0, built; `lake env lean <file>` from leanfinal/; module builds fine; NEVER
bare `lake build`).

## The gate (design doc §10 row CC-17)
"Construct one named full S2 `ChainRealization` and `RealizedInput`; print axioms and list
every cite used." This is the moment the carrier stops being a hypothesis stack: a CONCRETE
inhabitant at the S2 depth-two tower. Everything you need has landed TODAY:

- C130s2.lean — `s2DepthTwoKeyChain` + the full (e,f,u,ψ,step) bridge (CC-2).
- C130tr.lean — `TerminalReceiver` constructor; its verdict notes S2's constant `fld`
  fills the `junk` field with `RingHom.id` trivially (CC-3).
- C130ln.lean — the REPAIRED Laurent normalizer, literal `DeepTower.laurentNormalizer` (CC-4).
- C130st.lean + C130s6.lean — the stage source interface + the S2 level-2 instance data
  (values/digits/Full/lift ALL proved at i=2; CC-5/CC-6; read verdict_CC06.md's note on
  what the NodePointSource instance still needs from points).
- C130th.lean — the threshold dictionary (CC-7; threshold = inherited data).
- C130in.lean — `RealizedInput` + `inputBlock` (CC-8).
- C130pt.lean — legal points/letters (CC-9; `legalPoint` from the carried `point_exists`).
- C130cr.lean / C130ar.lean / C130vw.lean — the two reads + views (CC-10/11/12).
- C130fg.lean — `ChainRealization` itself (CC-13; the OPEN-DICT fields are the honest
  frontier: fill what the S2 instance can, and report EXACTLY which OPEN-DICT fields
  resist and why).
- C130pk.lean — `ChainRealization.toCalculus` (CC-16): if your instance lands, ALSO
  exhibit `Nonempty (FGMNCalculus (s2 tower) e' f' u')` at the S2 parameters (2,1,5) —
  the FIRST non-vacuous calculus instance, discharging the class hypothesis at S2.

Read: docs/PROJECT_STATE.md, docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md §6
(the depth-two instantiability sketch — your roadmap; it names which fields were checked
constructible), all the verdicts runs/wave-b/verdict_CC*.md.

## Honesty
This gate is EXPECTED to possibly block on the FGMN source-side fields (FGMNSourceData/
Laws are SOURCE objects; U12's level-general audit says the source MacLane valuations are
not yet formalized). The acceptance standard: construct everything repo-side (keys,
normalizer, receiver, stage tables, points, threshold, reads, input) as a named instance
of whatever partial-carrier structure composition the design permits, and give a
field-by-field table: FILLED (with the witness) / BLOCKED (with the exact missing source
object). If `ChainRealization` cannot be fully inhabited, land the maximal honest
sub-record instance + the table — do NOT weaken any field, do NOT use `sorry`.

## Deliverable
ONE new file leanfinal/Uniformity/ChapC/C130s17.lean (house style; docstring "chain-carrier
node CC-17 — the S2 acceptance gate"). `#print axioms` for every declaration, and an
explicit LIST OF CITES consumed (expected: possibly `fgmn_dv_exact_mul` via C131ac lemmas
if used; everything else Lean-core).

## Rules
NO sorry/new axioms/unsafe/field weakening. `rg` every name. Do NOT touch roll-ups,
leanspec/, or other units' files (in flight: C99gt.lean [GTA codex], C131ae.lean,
C78adj.lean). Do NOT git commit. Write runs/wave-b/verdict_CC17.md (the field table,
declarations, cites list, verification command).
