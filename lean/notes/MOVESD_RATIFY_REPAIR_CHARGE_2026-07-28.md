# MovesD RATIFICATION-REPAIR CHARGE (2026-07-28, orchestrator-adjudicated)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Corpus: lean/LeanUrat/MovesD/
(49 units, ALL PROVED, Lean-core footprints). A fresh-context Codex ratification pass
(lean/notes/MOVESD_RATIFY_CODEX_2026-07-28.md — to be committed; verdict text at
/tmp/leanratify_d/verdict.txt, READ IT FIRST) returned 5 crit / 1 gap. The orchestrator
adjudicated each finding against direct note reads (MOVES = lean/notes/MOVES_2026-07-24.md,
§D4-R = lines 4580–5436, §C C.0 display at 3430–3480, C.1.0 at 3598–3660). Your job:
execute the accepted repairs, keep every existing proof green, and DO NOT weaken any
existing statement. You are ADDING typed structure; the two def changes are specified
exactly. No git operations — the orchestrator commits.

## Ground rules
- Statement fence: existing theorem statements/signatures stay byte-identical except where
  a repair EXPLICITLY says otherwise (none do in this charge — everything is additive).
- Do not touch LeanUrat/Moves/ or LeanUrat/MovesC/ (frozen).
- Build discipline: after each unit, `cd lean && lake build LeanUrat.MovesD.<Module>`;
  at the end run a full `lake build` and `#print axioms` spot-checks on the new lemmas
  (footprints must stay Lean-core: propext, Classical.choice, Quot.sound).
- Staged writes: keep every response under ~4000 tokens; long files in several Edit calls.
- Docstrings on every new decl must cite the note lines (the displays quoted below).

## Finding D1 (γ-tie STR factor) — OVERRULED; add the coherence seal
Adjudication: the note L3 display "γ_r := e_r·u*_r + j*_r·h_r" (line 4707) is scale-
homogeneous at STAGE scale (§C C.0 marks γ_i "(augmented scale)", line 3461); the frozen
MovesC Node records ustar ABSOLUTE + gam STAGE with the conversion stage = STR × absolute
(C.1.0(c), Scale declaration 3635–3645); ShapeWF.gamTie/lineS/kappaS carry the STR factor
in exactly the compensating spots. NOT a defect. Repairs:
(a) New unit file SW2_scaleCoherence.lean: theorem `lineS_at_jstar` — for a ShapeWF shape
    and r < reads.length, the read line lineS r evaluated at base index (s0+wSide)·Dwidth
    equals ustar (i.e., the intercept convention and gamTie cohere: from the lineS def,
    essentially ring arithmetic), AND theorem `gamTie_stage_form`: gam = e·(strS·ustar)
    + (s0+wSide)·h as the displayed stage-scale identity (a restatement of gamTie packaged
    as the ruling record). Docstring: quote the ruling (note 3461 + 3635 + 4707; the
    ratifier had only §D4-R in context — this lemma is the machine-checked answer).
(b) Extend the gamTie docstring in Defs.lean (comment-only edit): add "RATIFICATION RULING
    2026-07-28: overruled — see SW2_scaleCoherence; stage = STR × absolute per C.1.0(c)".

## Finding D2 (CanonPolicy under-typed; POL-PIN is comment-only) — ACCEPTED as seam typing
The note (L1/L2, §D4-R): the classifier runs with ONE lift rule — the (S6b) OFFSET-P-LIFT
realizer; all histories carry these lifts and no others. The corpus quantifies over every
blind `CanonPolicy` (STRONGER theorems, so nothing false), but WHICH policy is the note's
is only a comment (POL-PIN). Repair: in Defs.lean (or a new PolPin.lean) add the TYPED
consumer-side pin, mirroring the W4-SYNC style:
  structure OffsetPPin (pol : CanonPolicy p F) : Prop — with the statable content. Read
  the note around the (S6b) citation in §D4-R (grep "offset-P" / "S6b" in 4580–5436 and
  the L1/L2 lemma bodies) and type what IS statable with MovesD+MovesC vocabulary (e.g.
  totality/prefix-monotonicity/the residual-class normal form of the produced lift, if
  displayed); whatever genuinely needs HC-1/§B2-DEF vocabulary stays as a NAMED field
  documented as the seam residue (a Prop-valued field is acceptable ONLY if accompanied by
  at least one non-trivially-typed law — do not reproduce the vacuous-tag defect).
  Then add W4-5 to the seam roster comment in Defs.lean §W4 block and record consumers:
  NO existing theorem changes; new corollaries MAY specialize (e.g. `CD_canonical` :=
  CD at a pinned pol) if cheap.

## Finding D3 (PrefIdx image/normalization) — OVERRULED core; ACCEPTED residue
Adjudication: EtaData/PrefIdx/PresentNorm IS the faithful η-granularity design (REV 4
Fable#2 C1 record; the note's η carries digits+ψ, everything else shape-pinned/derived/
policy-determined; zbar is NOT η data — the normalization kills conjugate-presentation
overcounting; PresentNorm(ii) IS the typed anti-collapse law). Residue repair: make the
conditionality visible as a real theorem. New unit F2_absCount.lean:
  define the policy-free Galois setoid on PrefSetAny classes: two histories related iff
  EtaGalEq of their etaData; theorem `card_classes_abs` (hnorm : PresentNorm n pol P) :
  Nat.card (PrefIdx n pol P) = Nat.card (Quotient of PrefSetAny n P by that setoid) —
  from PresentNorm (i) totality + (ii) uniqueness + E9's encInj. If the full bijection
  fights you past ~3 attempts, land the two inequality halves as separate lemmas and
  record the exact gap in the file header as a typed obligation (NO sorry on the
  capstone-path; a sorried spec-lemma in this NEW file is acceptable if clearly marked
  SEAM, but strongly prefer the proof — it should be a finite plumbing argument).

## Finding D4 (∅-shape event/mult) — ACCEPTED
Note: L5 (line ~4796): the EMPTY prefix η = ∅ INCLUDED, S(∅,⊤) = the FULL BOX, the base
of L6; mult_∅ ≡ 1; Pref(∅) = {∅}. Lean Presented.event/mult are PrefIdx-indexed, so at
reads = [] they give ∅/0. PrefOpt/etaDataO/emptyFiber exist but are unwired. Repair in
Defs.lean AFTER the Presented section (all additive):
  def Presented.eventO (S) : Set (Box p m) :=
    if (P : ShapePrefix).reads = [] then Set.univ else S.event
  noncomputable def Presented.multO (S) (x) : ℕ :=
    if (P : ShapePrefix).reads = [] then 1 else S.mult x
  (dispatch on reads = [], matching Shape.CD's own dispatch — cite "the F3 displayed
  deviation: the History type has no empty chain".)
New unit D14c_emptyEvent.lean: theorems `eventO_empty_shape` (reads = [] → eventO =
Set.univ ∧ ∀ x, multO x = 1), `eventO_eq_event` / `multO_eq_mult` (reads ≠ [] →
agreement with the old objects), and the ∅ mass law in the D4R.1 normal form:
Nat.card ↥(S.eventO) * p^A' = CD * p^(n*N) at reads = [] — i.e. card univ = p^(n*N)
(Box card) times CD = 1 with A' ∅ = 0; check ShapePrefix.A' at reads = [] reduces to 0
(it should — verify and cite; if A' ∅ ≠ 0 STOP and report, do not force). Existing
theorems (D2a/D3b/D12/D13/D14b with their hne guards) stay UNTOUCHED.

## Finding D5 (NP-ID untyped; D4R4_all range) — ACCEPTED
The docstring already QUOTES L12 and names the pin NP-ID (§2.5 W4-4) but there is no Lean
object. Repair (additive):
  def NPIDPin (n pol P) (Nthr : PrefIdx n pol P → ℕ) : Prop :=
    Nonempty (PrefIdx n pol P) →
      (P : ShapePrefix).NPband n = Finset.univ.sup (fun i => Nthr i)   -- Fintype PrefIdx:
  (PrefIdx is finite — find/derive the Fintype/Finite instance from F-enum/L8 units; if
  the instance is genuinely absent, take (hfin : (Set-finiteness form)) as a hypothesis.)
  theorem D4R4_all_noteRange (Nthr) (hpin : NPIDPin n pol P Nthr) : the D4R4_all
  conclusion with the quantifier ∀ N, (Nonempty (PrefIdx …) → Finset.univ.sup Nthr ≤ N) →
  … — i.e. L12's own range, derived from D4R4_all + hpin by rewriting the threshold.
  Docstring: "W4-4 NP-ID, now a Lean object; the ledger pin discharged to a typed premise."
  Update the W4-SYNC roster comment (W4-4: TYPED at NPIDPin).

## Finding D6 (gap: classifier-side gate numbers) — ACCEPTED as typed obligations
In G1_gates.lean (or new G2_gatesClassifier.lean): the sealed classifier-side falsifiers
as NAMED Prop defs (NOT sorried theorems, NO proofs): e.g.
  def Gate_CD_q2 (pol : CanonPolicy 2 F2instance…) : Prop := (PSTAR2shape).CD pol = 3
  def Gate_CD_q3 … : Prop := … = 48, and Gate_multOne … : Prop := ∀ x ∈ event, mult = 1
— read G1_gates.lean first and mirror however P̂* is encoded there; if P̂* at p = 2/3 is
not yet constructible as a Shape instance in MovesD vocabulary, then state the gates over
the EXISTING gate shapes and document precisely which piece is missing (that gap statement
itself goes in the file header + your report). The point: the obligations become TYPED,
owner = the classifier corpora (HC-1/HC-2).

## Deliverables (final response, ≤4000 tokens)
Per finding: what landed (file:decl), build status, axiom check result, any deviation from
this charge with the reason. List every file touched. NO commits.
