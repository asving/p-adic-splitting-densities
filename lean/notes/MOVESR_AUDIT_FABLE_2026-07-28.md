# MovesR Lean blueprint REV 2 — fresh-instance semantic re-audit (Fable)

DATE: 2026-07-28 · AUDITOR: fresh Fable instance (no prior MovesR context) ·
SCOPE: re-audit of `MOVESR_LEAN_BLUEPRINT_2026-07-28.md` rev 2 after the Codex
REJECT (15 crit / 6 gap); charge = `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` with
<CORPUS> = MovesR, <NOTE> = §R-LEDGER, plus the two addenda (statements-only
typing-vacuity rule; repair-verification + fresh sweep). GROUND TRUTH:
`MOVES_2026-07-24.md` lines 9290–9763 (§R-LEDGER rev 5) read in full. For the
one writer-flagged judgment call (LST) the note's own Lemma LST display
(§C, lines 3728–3781; cross-checked at 4460 "R5 (LST): the level-set
scale-typing lemma") was consulted per the audit instruction. The blueprint's
prose was treated as claims, not evidence. Nothing was fixed.

## 0. Repair verification (F1–F21 against `MOVESR_AUDIT_CODEX_2026-07-28.md`)

All 21 repairs are GENUINE — each addresses the specific defect Codex quoted:

- F1 → R6 `Fsub_card` stated as a frozen provable unit: the card fact of "F_m
  is THE subfield of order p^m" is now on the ledger. Genuine. (Residue: the
  uniqueness reading of "THE" is not stated; nothing in the corpus consumes it
  — Fsub is a fixed definition, so no embedding choices arise. Nit, uncounted.)
- F2 → `Setting` now carries the realized-measure laws (mass in [0,1],
  event algebra, additivity, conditional normalization guarded by
  0 < cellMass) + nonempty Cont/PTree; the surviving cellMass = 0 records are
  exactly the note's proviso-excluded cells and every display guards on the
  proviso. Genuine, with widening (i) recorded.
- F3/F5 → `REL1Clauses` ten TYPED fields over `ReBased`/`TowerData`; True-slot
  inhabitation is gone; `REL1 := REL1Clauses ∧ REL1b`. Genuine (but see
  fresh findings 1–2 below: one field mislabeled, one display leg unpinned).
- F4 → fixed box degree `n`; `histNe`/`locusNe`; vols through the pinned `V`.
  Genuine.
- F6/F7 → `FrameIdx`/`AmbRead` nonempty; `readDict` injective +
  letter-preserving; `teich_pin` a FIELD pinning to `WittVector.teichmuller`.
  Genuine (residue at (a5): fresh finding 7).
- F8 → `BoxVol` is now a normalized finitely-additive content on an algebra
  containing every cylinder, with `vol_cyl` pinning cylinder masses to
  (q_δ^{nN})⁻¹. Genuine and internally consistent (level-N cylinders partition
  univ into q^{nN} classes given R6; N = 0 and n = 0 edge cases check out).
- F9/F10/F18 → REL2b guarded by the note's own μ(Σ_c) > 0 proviso, quantified
  over a cylinder-populated event class; `REL2b_linked` conjoins REL1 at
  (δ_j, d_rel); EQ3 aliases the repaired REL2b ("REL.2(b) verbatim" — an alias
  IS verbatim). Genuine.
- F11/F12 → `nodeCorr` specified by corr_word/corr_reads/corr_verdict; PUnit
  example dropped; `posOf` wires (EQ-2)'s alphabets; (a3) enters via
  `A.teich_pin`. Genuine (residue folded into fresh finding 7).
- F13/F14 → `entryFirst : ℕ` FIXED per branch (the subtree no longer smuggled
  into the first index); `consumed` nonempty deliverable set; `determines` =
  singleton class; `massEqEntry` GIVEN determines; `stateDict_compat` types
  (e1)↔(a6); `e4agrees (tableConv)` parameterized on [3]'s export;
  `firstIdxCandidate` named, asserted nowhere. Genuine (residue: fresh
  finding 6). The (e5) second disjunct as a statement-fence event rather than
  a satisfiable-by-construction disjunct is a RECORDED widening (iii) and is
  accepted — the note's re-keying route changes types, which is exactly a
  fence event.
- F15 → `menu : ℕ+ → Finset Letter` + `menuNe` + stage-tuple anchor; EQ1 now
  the finite-syntax invariant. Genuine.
- F16/F17 → alphabets as additively-closed subsets of carrier groups with
  `card_eq : Nat.card (alpha δ x) = p ^ aDim δ x` (this also FORCES alpha
  finite — Nat.card of an infinite set is 0 ≠ p^a — and a finite
  additively-closed subset containing 0 is a p-subgroup: the typed object
  really is an additive span of p-power order, matching "|𝔸_δ| = p^{a_δ},
  a_δ := the F_p-additive-span dimension"); `posLetter` is the owed matching
  dictionary AS DATA and `Stable` is DEFINED from it. Genuine. EQ2law's
  domain is exactly the rev-4 per-position-class pin; the note's F₉
  out-of-domain instance is correctly NOT typed.
- F19/F20 → `SettingsFamily` (ne, root δ = 1, typed descent closure with
  `desc_amb : S'.δ = S.δabs`); SIBOdelta guards 0 < cellMass, conjoins REL1
  explicitly, and types both the event identity (S_j IS the Θ-pullback of the
  target realization event) and the pricing verbatim; `O_chain` is the ring
  half only, family closure the other half. Genuine.
- F21 → REL.3 pseudo-statement DELETED; recorded non-unit with the acceptance
  path and the plan discipline as a fenced comment. Faithful to "no theorem
  statement is possible here" — honest absence over fake shape. Genuine.

No repair regressed a previously-clean unit; the fresh findings below are new
defects or residues the repairs exposed.

## 1. Unit-by-unit sweep (fresh; findings referenced by number)

- R1: `Fsub`/`O`/`qq`/`relExt` faithful to the BASE-INDEX CONVENTION;
  `relExt := O (m·δ')` making the composition display `rfl` is SANCTIONED by
  the note's own "bookkeeping inside W(F̄_p), never an identification up to
  isomorphism". `cyl` = agreement of the first N Witt coordinates is a correct
  rendering of "f mod p^N" over a perfect residue field, and its class count
  q_δ^{nN} matches (R0-box). Clean. (Syntax nit, E-phase: `Setting` as
  declared uses no field mentioning `p`, yet `Setting p` / `SettingsFamily`'s
  `Set (Setting p)` assume the parameter — elaboration will force a fix;
  covered by the skeleton's syntax-only fence.)
- R2–R5: statements faithful (nesting, composition, pool-size law, (e2) via
  `βarg_eq`). Clean.
- R6: statement faithful. Clean.
- R7 Setting: laws sufficient (condMass ≤ 1 on events is derivable from
  additivity + complement + univ, so not missing). Clean modulo finding 5's
  first site.
- R8 SettingsFamily: `desc ≡ ∅` families remain lawful — but "which settings
  arise" is ambient-theory content by the note's own quantifier, the closure
  TYPING is what [2r] owes, and widening (i) records the supplier-side
  residue. Accepted.
- R9 TowerData + Laws: "built afresh, NOT by scalar-extending" is carried by
  the polynomials living over the actual tower carriers; §B1's typable residue
  + fence recorded (widening (ii)). Clean.
- R10 BoxVol: clean (see F8 above).
- R11/R13 REL1Counting/REL1b/REL1: (REL.1-b) display transcribed exactly
  (range (k+1), q_δ^{nN}, ∀ N ≥ N(H,Z)) — but see finding 2 (count unpinned).
- R12 ReBased + REL1Clauses: secA/secB1/secB2def/thmCa/c1/c15ZC/typ/dom
  faithful head-shapes under the recorded widening (ii); `typ` is walk item
  (i)'s retyping verbatim (additive only, F_δ-linearity correctly NOT
  asserted); c1 is (R0-ledger)'s per-constrained-digit (p^{a_δ})⁻¹ product
  verbatim, and its ∀F form correctly forces frame-invariance of the mass.
  Findings 1 (lst), 3 (pin status), 4 (aDim wiring).
- R14 REL2a: six items typed; (a2) integrality as a deliverable FIELD matches
  "the pass that closes (a) must EXHIBIT"; E·F ∣ d_j correctly left fenced.
  Findings 5 ((a1) measurability), 7 ((a5) anchor).
- R15 REL2b/_linked/EQ3: display verbatim with the note's guard; the W-domain
  = V.events with cylinders forced present matches "REL.1-measurable … (digit
  cylinders generate)". Clean modulo finding 5's second site.
- R16 REL2d: square + specified correspondence faithful; TgtRealizes opaque
  per (W1) — correctly neutral to the [1]/[3t] "realizes" pin. Clean modulo
  findings 5/7.
- R17 REL2e: (e1)–(e5) all present and typed; keying matches [3]'s
  (first index, state, argument). Finding 6 ((e3)'s V unpinned).
- R18/R19/R20/R21: EQ1/EQ2/EQ2law_card/EQ3 faithful, PREDICTED/OPEN statuses
  respected (hypothesis-side only, asserted nowhere); EQ2law_card discharges
  no kernel (pure arithmetic from card_eq + the hypothesized law). Clean.
- R22 SIBOdelta: quantifier = the realized family with root + closure; the ∃
  binds one identification package per branch-setting (correct: Θ_j does not
  depend on T); event-typing + pricing conjuncts render "S_j IS an
  O_{δ_j}-statement" and the pricing display verbatim; the REL1 conjunct makes
  the right side a REL.1-theory mass; (e) correctly NOT in the fence
  (matching "FENCED = REL.1 + REL.2(a)+(b)+(d)"). Clean modulo finding 5's
  third site.
- R23 O_chain: the literal subring chain, provable via O_le. Clean.
- Non-units (D6): REL.3 (deleted, faithful), REL.2(c) (no sibling-independence
  Prop anywhere in MovesR — checked; SIBOdelta prices single branches only,
  no ⋂/∏, so (SIB)'s product law is NOT re-stated — faithful to the fence),
  gate REL-n4 (census artifact, spec owed in the note itself — sound
  non-unit), (R0-tower)/(R0-reads) PREDICTED brackets (doc-comments only —
  typing them would assert what the note fences; correct). No axioms; no
  kernel discharged; hypothesis fidelity holds for every named kernel (REL1,
  REL2b, e3/e4/e5, EQ1, EQ2law, EQ3, SIBOdelta — all named Props consumers
  hypothesize, none proved, none axiomatized, none strengthened into a
  definition). The R.2 closing β-sentence is not typed as a unit; it is
  derivable glue (SIBOdelta + massEqEntry at V := RB.C.V) and consumer-side
  citation bookkeeping — uncounted, noted for the MovesS sync.

## 2. Findings (fresh sweep; quotes from the blueprint, refs to the note)

**Finding 1 — CRITICAL (R12 `lst`): the LST clause field types a (REL.1-b)
consequence, not LST; the ledger's LST slot is effectively empty.**
Offending spec: "/-- LST: normalized level counts stabilize above N(H,Z)
(cross-multiplied form). -/ lst : ∀ H Z N N', K.C.Nmin H Z ≤ N → N ≤ N' →
(K.C.count H Z N' : ℚ) * ((qq p δ : ℚ) ^ (n * N)) = (K.C.count H Z N : ℚ) *
((qq p δ : ℚ) ^ (n * N'))" — with the blueprint's own flag (§3, widening iv)
that it was "typed from (REL.1-b)'s quantifier rather than a named display".
The note's LST display exists and says something else entirely: "**Lemma LST
(level-set scale-typing)** … (i) TYPING: ht(b, l) is the K1-chain weight …
(ii) FLOOR CONSTANCY ON THE INTERIOR … (iii) SELECTION" (MOVES 3728–3749;
confirmed at 4460: "R5 (LST): the level-set scale-typing lemma"). Two
independent defects: (a) MISLABELING — the typed content is count
stabilization, which is no part of level-set scale-typing; (b) REDUNDANCY —
the field is ENTAILED by the sibling conjunct `REL1b` (count(N) = q^{nN}·P at
both N and N' gives the cross-multiplied identity in one line), so inside
`REL1 := REL1Clauses ∧ REL1b` it constrains nothing: the ten-clause ledger is
de facto nine clauses, and the note's REL.1 ("§C — through … LST …") is
silently WEAKENED — a future pass could 'supply' this field by proving a
C(b)-consequence and the ledger would book LST as covered. Repair shape:
retype `lst` as the typable residue of Lemma LST's actual head (or fence it
exactly like §B1's internals with the docstring citing the §C display).

**Finding 2 — CRITICAL (R11/R13 `count`): the (REL.1-b) LHS is a
note-DEFINED cardinality typed as free data; REL1b is true on lawful
instances the note would reject.**
Offending spec: "count : (H : Hist) → Locus H → ℕ → ℕ    -- #{ f mod p^N ∈
S(H, Z) }". The note's display: "(REL.1-b) #{ f mod p^N ∈ S(H, Z) } =
q_δ^{nN} · ∏ … vol(E_fresh(ν_i)) · vol(Z)" — the LHS is the cardinality of
level-N residue classes of the classifier locus, and BOTH ingredients exist
in-corpus (`ReBased.SHZ` and `cyl`), so it is pinnable NOW (e.g. `count_spec :
count H Z N = Nat.card {C // ∃ f ∈ K.SHZ H Z, C = cyl p δ N f}`). Left free,
`REL1b` is a relation between two pieces of supplied data: the instance
count := q^{nN}, freshEvent/locusEvent := univ, pinnedIn := ∅, digitLocus :=
all-solutions (SHZ = univ via thmCa), jet := 0, trivial tower — satisfies
every clause field AND REL1b while asserting no counting fact about any
classifier. This fails the blueprint's own acceptance lesson ("a faithful
obligation statement must be FALSE for instances the note would reject") and
is the exact analogue of Codex F8's dummy-vol CRITICAL, one field over.
(After the pin, the surviving degenerate instances are honest-trivial —
histories with full locus — for which the note's display genuinely holds:
correct perimeter.)

**Finding 3 — GAP (R12 `c05PinWelldef`): PIN-WELLDEF's "status" leg dropped
silently.** Offending spec: "∀ Z, (K.pinnedIn H F Z).card = (K.pinnedIn H F'
Z).card" against the note's "PIN-WELLDEF as cardinality-and-status statistics
(C.0/C.0.5)" (R0-ledger). Only the cardinality statistic is typed; a status
statistic (minimally, invariance of the multiset {aDim H i : i ∈ pinnedIn H F
Z} across frames — typable from in-corpus vocabulary) is neither typed nor
recorded as a widening. The docstring quotes the full phrase while encoding
half of it.

**Finding 4 — GAP (R12/R19): a_δ double-booked; the note's (EQ-2) wiring of
the per-digit factors is absent.** `ReBased.aDim : (H) → Fin (mOf H) → ℕ`
("a_δ at each digit position ((EQ-2) def part)") and `AlphabetData.aDim :
ℕ+ → Pos → ℕ` are never related — no digit-position → Pos assignment, no
coherence law — although the note ties them: "|𝔸_δ| = p^{a_δ} per (EQ-2)'s
re-based-span definition" (R0-ledger). As typed, EQ2law/EQ2law_card (and
REL-n4's exponent leg, which "tests" (EQ-2)) say nothing about the exponents
c1 actually consumes. Underspecified Defs dependency; typable now (a
`posOfDigit` field + `aDim`-agreement law, or a recorded fence).

**Finding 5 — GAP (three sites): measurability side-conditions of the
displays dropped onto totalized functions, unrecorded.** (i) (a1)'s "as a
MEASURABLE product of O_δ-digit spaces" → `domIdent : S.Cont ≃ (freeCoords →
↥(Fsub p S.δ))`, a bare Equiv with no event-algebra compatibility; (ii)
REL2b's "the pushforward of the conditional continuation measure under Θ_j IS
the normalized O_{δ_j}-box measure" → the pullback `(Θ ∘ domIdent) ⁻¹' W` is
never required ∈ `S.AmbEvents` (condMass is total, so the equation holds
formally while Θ-measurability — part of the pushforward reading — is
untyped); (iii) SIBOdelta's pricing and (e3)'s `massEqEntry` consume
`V.vol {g | TgtRealizes …}` without `… ∈ V.events`, i.e. "the right side a
REL.1-theory mass" is asserted at a set where V's measure laws do not bind.
Each membership is typable now; none is typed or recorded.

**Finding 6 — GAP (R17 `massEqEntry`): (e3)'s vol is an arbitrary BoxVol, not
the REL.1 theory's.** Offending spec: "def REL2e.massEqEntry … (V : BoxVol p
S.δabs A.dRel) : Prop" — V a free parameter. The note's (e3): "IS the REL.1
mass vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j }" — the mass of the
REL.1 theory, i.e. `RB.C.V` of a REL1-satisfying `RB`. The F10 repair pattern
(`REL2b_linked`) exists in-corpus and was not applied to (e); as exported to
MovesS, `massEqEntry` can be consumed at a V unrelated to any REL1 instance.

**Finding 7 — GAP (R14 (a5) / D7): checklist items satisfiable by trivial
free data, and D7 overclaims the contrary.** (a5)'s `frame_compat` is
dischargeable with `FrameIdx := PUnit, ambT = tgtT = id` REGARDLESS of Θ — the
transports carry no unitriangularity law and no anchor to C.0.5's (the note:
"the displayed commutation of Θ_j with C.0.5's UNITRIANGULAR transports");
REL2d is likewise inhabitable with PUnit trees and empty word/read/verdict
lists. This free-data relativity is partly inherent to a statements-only
corpus (the ambient engine's transports/reads do not exist in Lean) and D9
correctly withholds instances-as-evidence — but D7's "its law fields make
junk inhabitants impossible" is FALSE as written, and the residue is not
recorded as a widening. Owed: either an order-anchored unitriangularity law
on `ambT` (freeCoords ⊆ ℕ × ℕ carries C.0's order) or an explicit widening
entry replacing D7's claim.

## 3. The flagged LST adjudication (the writer's judgment call)

ADJUDICATED AGAINST THE NOTE'S LST DISPLAY: REJECTED — subsumed as Finding 1
(CRITICAL). The note HAS a named LST display (Lemma LST, "level-set
scale-typing", MOVES 3728: ht-weight typing / interior floor constancy /
level-set selection); the blueprint's premise for widening (iv) — that LST
has no named display and must be typed from (REL.1-b)'s quantifier — is
factually wrong, and the resulting field is both non-LST in content and
entailed by REL1b (hence contentless inside REL1). This is not a defensible
head-shape widening like §B1's (whose typed residue IS part of §B1's
content); the stabilization Prop types no part of LST's content.

## 4. Counts and verdict

Repairs F1–F21: all 21 verified genuine; no repair regression found.
Fresh findings: 2 CRITICAL (Findings 1–2) / 5 GAP (Findings 3–7).

**REJECT (2 crit / 5 gap)**

All seven findings have concrete, local repair shapes (retype/fence lst; pin
count; type or fence the status leg, the aDim wiring, the three memberships,
the (e)-linked V; fix D7's claim + anchor or record (a5)) — a rev-3 batch, no
architectural change. The statement fence applies to all of them.
