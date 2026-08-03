# FORGE junc_bundle STAGE 2 — the first compiled e ≥ 2 junction attempt ADJUDICATES THE COMPILED CHAR-2, Φ₂-LANDING BUNDLE INSTANCE-FALSE AT ROW A: the parity wall (no e = 2 recording exists at the row-A read — the one char-free/Φnext-free wall), the Φ₂-landing wall (char-2, Φ₂-landing, all species/degree faces), the D0 flag CONFIRMED in Lean (gate hbundle unsatisfiable — definitional-equality certified at REV1, per-clause vacuity via gluePacket_false), clause (iii) POSITIVELY derivable at the read-pair pins — **REVISION 1 + REVISION 2 APPLIED (§R1–R4: row-A rescope, negation shape, D0 tie compiled, disposition + charter; REV2 = per-theorem scope + certification wording)**

**Unit:** FORGE junc_bundle stage 2 (wave 11; charter = stage 1's §S5 spec,
`JUNCFORGE_S1_2026-08-08.md`).  **Artifact:**
`lean/LeanUrat/Scaffold/HDischarge/H1/JuncForge.lean` — NEW declarations only; no
existing statement touched (`gate_glue_junction`/`gate_glue_conditional` displayed,
not edited); `lake env lean` green; every theorem `#print axioms` = Lean core
`{propext, Classical.choice, Quot.sound}`; zero sorries.
**Row-A data compiled:** f = X² + 4X + 28, Φ₁ = X + 2, Φ₂ = X² + 4X + 12 over ℤ₂;
the deep development f = 24 + Φ₁² (slots (24, 0, 1)) as `fA_eq`/`BA_dev`.

## S1. VERDICT — the §S5 discharge is IMPOSSIBLE: the compiled CHAR-2, Φ₂-LANDING `junc_bundle` at row A is instance-false

Executing the stage-1 spec against the Lean `SideReads` transcription did not
produce the chartered first compiled e ≥ 2 junction — it PROVED no such instance
can exist AT THE ROW-A READ: at any stage whose frame is keyed at Φ₁A (`hσΦ`),
reading the row-A classificand fA under a development at that frame (`hdev`).
The theorem scopes are NOT uniform \[REV2\]: only the e = 2 parity wall
(`juncforge_no_e2_junction`) holds for any finite residue field and any
designated Φnext; the landing wall (`juncforge_deep_wall`) additionally requires
(2 : F) = 0 and refutes the Φ₂ landing specifically; the packaged refutation
(`juncforge_junc_bundle_false`) further requires the interior Φ₂A pin — see the
scope column below.
\[REV1: the original sentence here ended "at any stage, for any recorded node
data" unqualified — bracketed as an overclaim; every wall binds the row-A fiber
(fA, Φ1A) through the `hσΦ` + `hdev` hypotheses. Outside that fiber (other
classificands, other keys) existence is OPEN.\]

| theorem | statement | scope |
|---|---|---|
| `juncforge_no_e2_junction` | any `SideReads` of f = fA at a Φ₁A-keyed frame has ν.e = 1 | the row-A fiber (fA, Φ1A): any finite F, any Φnext — char-free |
| `juncforge_deep_wall` (+ `_F4`) | no `SideReads` of f = fA at a Φ₁A-keyed frame lands Φ₂ | row-A fiber; any finite F with (2 : F) = 0; instantiated at F4 |
| `juncforge_junc_bundle_false` | the `junc_bundle` 3-conjunct CORE ∃ (dev + interior pin + SideReads) is FALSE at every continuation H₂ with base key Φ₁ and node-1 key Φ₂ | packaged form — row-A fiber, char-2 ((2:F)=0), interior Φ₂A pin \[REV2\]; negates the WEAKER core, which any fuller bundle implies, so refutes every fuller bundle under those restrictions; not a verbatim general ¬junc_bundle \[REV1\] |
| `juncforge_clauseIII_derivable` | clause (iii) alone IS derivable at the (2,3)-graded pins — the harness shape exact | positive fragment, conditional on the pins |
| `juncforge_D0_instanceFalse` | `gate_glue_junction`'s `hbundle` is unsatisfiable | the flagged D0 adjudication; DEFINITIONAL-EQUALITY certified at REV1 \[REV2 wording\] (`juncforge_gate_hbundle_false` + `juncforge_gluePacket_false`, §R1-G2/§R4) |

## S2. THE MECHANISM — the two-scale law becomes a PARITY contradiction inside one node

**(a) The parity wall (e = 2).**  Clause (ii)'s functional equalities at the stride
slots {0, 2} force `gam = 2·σ.w(24) = 2·ν.h`, so `σ.w(24) = ν.h` with
`gcd(2, ν.h) = 1` — ODD.  The key-power slot carries `σ.w(Φ₁²) = 2·σ.h` — EVEN.
The slots can never tie; `hRlt` collapses σ.R f to a single monomial (hS5 digit or
T^{2s}); clause (iii)'s anchored `Ranch = pat₀ + pat₁·z` (hpat0/hpatTop force BOTH
digits nonzero at width wSide/e = 1) needs two Laurent positions
(`monomial_ne_anchor`).  ⊥.  This is the e₁ = 2 ramification itself: w₁(24) = 3 is
odd, the flat tie needs it even — no ℤ-valued stage scale hosts clause (ii)'s
window functional and clause (iii)'s graded residual simultaneously AT THIS READ
\[REV1: proved at the row-A fiber; the odd-parent-weight generalization is a
mechanism-level expectation, not a theorem\].  The support
forcing (s0 = 0, wSide = 2) is itself derived (clause (ii) endpoints must sit on
the development support {0, 2}; wSide = 0 dies by hOrd against a constant Ranch).

**(b) The landing wall (e = 1, Φnext = Φ₂).**  With ν.e = 1 forced: recentering
face — Φ₂ = Φ₁ − lift has degree 1 ≠ 2; g = 1 lift face — Φ₁ + t₀ has degree
1 ≠ 2; g = 2 lift face — clause (ii) at k = 1 forces pat₁ = 0 (B₁ = 0 by Fact B),
so Ranch = pat₀ + pat₂·z², ψ ∣ Ranch at equal degree pins ψ.coeff 1 = 0, and
ψ = z² + c₀ is (X + √c₀)² over the finite char-2 residue field (squaring is
bijective — proved self-contained, no Frobenius API) — contradicting `hψirr`.
g ≤ 2 comes from ψ^μ ∣ Ranch with deg Ranch ≤ 2.

**(c) What remains OPEN (honest scope).**  `DIterJunctionSupplier` is NOT refuted:
its Φnext is existential, and Φnext-free e = 1 refinement-shaped recordings
(MacLane key improvement, the D4 stratum) are not excluded by (a)+(b).  The wall's
g = 2 leg is proved at the faithful char-2 ambient only; odd-residue-char
pathological stages (the interface does not tie char F to p) are out of scope and
displayed as such.  No claim at towers other than row A/ℤ₂.

## S3. THE D0 ADJUDICATION (the stage-1 §S2(c) flag) — DECIDED: INSTANCE-FALSE

`juncforge_D0_instanceFalse` negates the `hbundle` hypothesis of
`gate_glue_junction` at DEFINITIONAL EQUALITY \[REV3, superseding the REV1
"VERBATIM"/"COMPILED" wording per re-audit-2: the certification is elaboration of
the direct application — `juncforge_gate_hbundle_false` (statement matching the
gate binder, proof term = `juncforge_D0_instanceFalse` applied directly; Lean does
NOT compare source bytes, and the three-way source diff is editorial/unverified)
plus `juncforge_gluePacket_false` (the independent structure-field vacuity leg:
∀ H₁, ¬ GlueJunction U31.fq H₁ H₂rc recentering); see §R1-G2/§R4\]: at the compiled seam the junction frame's key IS the
classificand (f = fq = σ₁rec.Φ — the degenerate f-equals-key stratum), the unique
fq-adic development of fq has B₀ = 0 (`L0_FactB_unique` against the self-development
`BselfJ`), and clause (ii) at the recorded `hpat0` (pat 0 = −rcCenter ≠ 0,
`RCWitness.lean`) demands B₀ ≠ 0.  **`gate_glue_conditional` is therefore VACUOUS
at its compiled instance.**  Stage 1's flag is CONFIRMED, not refuted.  Per the
charter fence the gates are NOT edited — their DISPOSITION (display text, possible
re-instancing at a non-degenerate seam) is an orchestrator/ROOT matter.

## S4. THE SUPPORT KERNEL AND THE POSITIVE FRAGMENT

* **Development uniqueness (Fact A/B, priced by stage 1): PROVED — pre-existing.**
  The needed kernel is exactly `Moves.L0_FactB_unique` (already on file, Lean-core);
  this unit consumes it (`dev_pin`, D0).  No new sorry, no displayed hypothesis.
* **Clause (iii) is honest at the read-pair scale** (`juncforge_clauseIII_derivable`):
  at any stage with pins Φ = Φ₁, h = 3, (s,t) = (−1,1), wPrev(24) = 3, w(24) = 6,
  the interface derives σ.R f = C(c)·T⁻³ + T⁻² = T⁻³·(c + z) — consecutive
  positions −3/−2, anchor −3, ord_{z+c}(c+z) = 1 — the §S5 display exactly, from
  hS5 + hRΦ + hRmul + hRadd + hK1.  The stage-1 two-scale law survives in Lean;
  the contradiction is strictly the CO-HABITATION with clause (ii) in one node.
  The existence of a stage with these pins (the concrete (2,3)-graded junction
  stage) remains the open construction — moot for the bundle (S1), retained as the
  honest conditional.

## S5. WHAT junc_bundle's STATUS BECOMES

* At row A \[REV1: the original parenthetical "(and by the parity mechanism, at
  any genuinely ramified deep read with odd in-carrier parent weight)" is
  bracketed as an overclaim — a mechanism-level expectation, NOT proved; the
  theorems bind row A\]: **the compiled CHAR-2, Φ₂-LANDING `junc_bundle` is
  INSTANCE-FALSE as transcribed** \[REV2: the refutation binds (2:F)=0, the Φ₂
  landing, and the interior Φ₂A pin — not "junc_bundle simply false at row A"\]
  — the E-PHASE FLAG (HC2/Defs clause (iii) "may over-strengthen") lands as a
  proved INTER-CLAUSE CONTRADICTION ((ii) ⊥ (iii) at e = 2; (ii)+(iv) ⊥ at e = 1),
  not an over-strengthening of one clause.  Verdict of record (§R2): the CHAR-2,
  Φ₂-LANDING, interior-Φ₂A-pinned bundle INCONSISTENT AS TRANSCRIBED, COMPILED AT
  ROW A \[REV3: the restrictions repeated here per re-audit-2 — no unrestricted
  row-A refutation is claimed\].
* The C-e escapee is EXPLAINED AT ROW A: GlueRun's "no compiled e ≥ 2 instance
  exists on file to feed it" is now "none CAN exist AT THE ROW-A READ — fA against
  a Φ1A-keyed frame, any Φnext" (`juncforge_no_e2_junction` — the one theorem
  whose scope IS any-F/any-Φnext \[REV2\]).  \[REV1: the
  unqualified "none CAN exist (as the definition stands)" — including the same
  gloss in the JuncForge.lean file header and the 2026-08-08 ledger entry — is
  bracketed as an overclaim; other classificands/keys are OPEN.\]
* The RG-2 fence is unbreached and now double-walled at the seam: the glued-base
  (L₁ = 1) hosting of an e ≥ 2 junction read, the one shape the glue theorem
  permits, has no ROW-A inhabitant \[REV1 scope\].
* Any repair (re-scaling clause (ii)'s functional to the parent scale at graded
  frames, or re-keying clause (iii)'s residual) is a STATEMENT change on
  `SideReads` — ROOT authority, not this unit.

## S6. WHAT THIS UNIT DOES NOT CLAIM

No edit to any existing statement (gates displayed only); no repair proposal
adopted; no refutation of `DIterJunctionSupplier` (S2(c)); no odd-char claim; no
orders ≥ 3 claim; ITER-LAW untouched (never reached — the bundle dies before any
digit algebra fires; the stage-2 gate is ITER-LAW-free as the spec predicted, but
by falsity rather than degeneration).  The capstone path is untouched (new file
only; no existing module recompiled).

— FORGE junc_bundle stage 2, 2026-08-08 (wallclock 2026-08-03).

---

## R1. REVISION 1 (2026-08-08) — the JFS2-AUDIT corrections of record

Audit: `JUNCFORGE_S2_audit_report.md` (Codex, fresh context; verdict CRITICAL,
1C/3G).  All findings were PROSE/packaging defects — the six original Lean
theorems stand unedited; REVISION 1 adds two declarations and corrects the record.

* **(C1, CRITICAL — scope.)**  Every global-sounding claim in this note is
  RESCOPED to the proved row-A fiber: the walls hold AT THE ROW-A READ —
  classificand fA = X² + 4X + 28 read against a Φ1A = X + 2-keyed frame (the
  `hσΦ : ν.σ.Φ = Φ1A` hypothesis) under a development of fA at that frame
  (`hdev`).  \[REV2: the trailing "for ANY finite residue field and ANY
  designated Φnext" that stood here applied only to `juncforge_no_e2_junction`;
  `juncforge_deep_wall` requires (2 : F) = 0 and lands Φ₂A specifically, and
  `juncforge_junc_bundle_false` additionally requires the interior Φ₂A pin —
  see the §S1 scope table.\]  The honest headline: **no e ≥ 2 `SideReads`
  recording can exist AT THE ROW-A READ (fA, Φ1A fiber, any F, any Φnext —
  this e = 2 wall alone is char-free), and the compiled CHAR-2, Φ₂-LANDING
  bundle at row A is instance-false**.  The unqualified forms ("at any stage, for any
  recorded node data"; "none CAN exist as the definition stands") are bracketed
  inline above as overclaims (\[REV1\] markers).  Outside the fiber — other
  classificands, other keys — existence is OPEN.  The `JuncForge.lean` file-header
  glosses carry the same overclaim and are rescoped by this block (the header
  itself is untouched per the new-decls-only fence; the file's new §8 section
  comment points here).  The 2026-08-08 ledger entry's escapee sentence ("no
  compiled e ≥ 2 junction CAN exist as SideReads stands") is corrected of record
  by the REVISION 1 ledger append — the prior entry is not edited.

* **(G1 — negation shape.)**  `juncforge_junc_bundle_false` negates the WEAKER
  three-conjunct core (IsDevelopment ∧ interior-pin ∧ SideReads) under the row-A
  restrictions (`hΦ`, `hlen`, `hkey`, char 2) — it is NOT a verbatim
  `¬ GlueJunction.junc_bundle ...` and NOT a general refutation.  It is logically
  sufficient AT ROW A: the core is implied by any fuller bundle (the fourth,
  recentering-lift conjunct only strengthens the ∃-body), so its negation refutes
  every fuller bundle there.  Nothing more is claimed.

* **(G2 — D0 tie, now COMPILED.)**  \[REV2 wording: the certification here is
  DEFINITIONAL EQUALITY, not byte identity — see §R4.\]  The §S3 tie claim is
  no longer prose.  Two new Lean-core declarations (`JuncForge.lean` §8, new
  decls only; `lake env lean` green; `#print axioms` = {propext, Classical.choice,
  Quot.sound} for both):
  - `juncforge_gate_hbundle_false` — its statement is `gate_glue_junction`'s
    `hbundle` binder copied verbatim and negated (mechanical three-way diff of the
    GlueRun binder slice, the D0 statement body, and the tie copy: IDENTICAL
    modulo leading indentation — an UNVERIFIED editorial diff, see §R4); its
    proof term is `juncforge_D0_instanceFalse` applied DIRECTLY, no massaging —
    elaboration certifies the two propositions are DEFINITIONALLY EQUAL (Lean
    does not compare source bytes).
  - `juncforge_gluePacket_false` — the NON-TEXTUAL leg (per the
    extraction-decorrelation discipline): for EVERY base history H₁,
    `¬ GlueJunction U31.fq H₁ H₂rc ReadSpecies.recentering`, proved by projecting
    the structure's own `junc_bundle` FIELD (the gate's compiled binder type, not
    a copy) into the D0 verdict.  This makes "`gate_glue_conditional` is VACUOUS
    at its compiled instance" a THEOREM: the packet its conclusion route needs is
    uninhabited.

* **(G3 — disposition.)**  §R2 and §R3 below.

## R2. THE DISPOSITION (the audit's key finding)

**Verdict of record: the compiled CHAR-2, Φ₂-LANDING `junc_bundle` (with the
interior Φ₂A pin) is INCONSISTENT AS TRANSCRIBED AT ROW A.** \[REV3: the
restrictions stated in the verdict itself per re-audit-2 — the e = 2 parity leg
(`juncforge_no_e2_junction`) is char-free/any-Φnext, but the e = 1 landing leg
binds (2:F) = 0 + the Φ₂A landing, so the BUNDLE verdict carries those
restrictions.\]  What is proved is a fact about the LEAN TRANSCRIPTION of the
[T-5] side-read bundle: the clauses of THAT restricted bundle cannot cohabit one
recorded node at the row-A read.
It is NOT established that the FGMN source mathematics is false.  The
contradiction admits the INCOMPATIBLE-TRANSCRIPTION-SCALES reading: clause (ii)'s
window functional may be transcribed at the PARENT scale while clause (iii)'s
graded residual lives at the GRADED (read-pair) scale — exactly the two scales the
stage-1 two-scale law separates (wPrev(24) = 3 vs w(24) = 6 at the (2,3) pins),
and the positive fragment (`juncforge_clauseIII_derivable`) shows clause (iii) is
exactly right at the graded scale.  On this reading, a `SideReads` repair
(re-scaling clause (ii) at graded frames) could RESTORE the paper-source glue step
rather than alter its mathematics.  Deciding between "source glue step refuted at
row A" and "transcription mis-scaled" requires re-deriving the glue step from the
source — chartered in §R3.  Until that lands, this unit's result is: the compiled
char-2, Φ₂-landing transcription is inconsistent at row A; the source-level
question is OPEN.

## R3. CHARTER — the transcription-scale re-derivation design unit

Spec for the next dedicated unit (design genre):

* **Task:** re-derive the glue step from the FGMN source at the read-pair scale
  stage 1 measured — fixed points: the stage-1 two-scale law (wPrev vs w at the
  (2,3) pins) and the derivable clause (iii) (`juncforge_clauseIII_derivable`,
  the harness-exact shape).  Determine from the source text the correct scale for
  clause (ii)'s window functional at junction frames (parent vs graded), and
  whether clause (iii)'s residual keying is the derivable one.
* **Discipline (non-textual leg — standing corruption warning):** the shared
  extraction `/tmp/litunit/fgmn.txt` is BAD at Def 3.15 — do not cite it; every
  load-bearing formula needs a fresh `pdftotext -layout` leg PLUS a numeric
  cross-check (numerics as falsifiers only, never as proof).
* **Product:** the corrected `SideReads`/`junc_bundle` transcription as a
  PROPOSAL — a statement change (Asvin-flag genre): NO application to the corpus
  without ROOT adjudication.  Until adjudicated, the compiled `SideReads` stands
  as-is and every JuncForge theorem keeps its exact current meaning.

— JUNCFORGE S2 REVISION 1 + DISPOSITION, 2026-08-08 (wallclock 2026-08-03).

---

## R4. REVISION 2 (2026-08-08) — the JFS2-REAUDIT corrections of record

Reaudit: `JUNCFORGE_S2_reaudit_report.md` (Codex, fresh context; verdict
CRITICAL, 1C/1G).  Both findings are PROSE defects in REVISION 1 itself — no
Lean edit; the eight declarations of record stand unedited.  Counter stays 0/2
(no clean pass yet).

* **(C1, CRITICAL — residual any-F/any-Φnext scope.)**  Finding quoted: "§R1(C1)
  says 'the walls hold … for ANY finite residue field and ANY designated Φnext.'
  Only `juncforge_no_e2_junction` has that scope. `juncforge_deep_wall` requires
  `(2 : F) = 0` and specifically lands `Φ2A`; `juncforge_junc_bundle_false`
  additionally requires the interior `Φ2A` pin. Consequently, the headline/S1/S5
  assertion that `junc_bundle` is simply 'instance-false at row A' remains too
  broad."  FIXED: the headline, §S1 (verdict sentence + per-theorem scope
  table), §S5, and §R1(C1) now carry the per-theorem scopes — the any-F/
  any-Φnext (char-free) scope is attributed to `juncforge_no_e2_junction` ONLY;
  `juncforge_deep_wall` is stated with its (2 : F) = 0 hypothesis and Φ₂A
  landing; `juncforge_junc_bundle_false` with the additional interior Φ₂A pin.
  The instance-false headline of record reads: **the compiled CHAR-2,
  Φ₂-LANDING bundle at row A is instance-false**.

* **(G1 — "byte-identity kernel-certified" inaccurate.)**  Finding quoted:
  "Lean's kernel does not compare that copied source text with the binder's
  source bytes; the declaration never references `gate_glue_junction`'s
  parameter type."  FIXED: the certification claim of record is
  **DEFINITIONAL-EQUALITY certified** — `juncforge_gate_hbundle_false`'s
  statement elaborates and accepts `juncforge_D0_instanceFalse` applied
  directly, which certifies the two propositions are definitionally equal;
  byte-level agreement with the gate binder is only an unverified editorial
  three-way diff.  The structure-field vacuity is carried INDEPENDENTLY by
  `juncforge_gluePacket_false` (the gate's compiled `junc_bundle` field type
  itself, no copy), which is what makes the §S3 vacuity verdict a theorem.
  Headline, §S1 table, and §R1(G2) reworded accordingly.

— JUNCFORGE S2 REVISION 2, 2026-08-08 (wallclock 2026-08-03).

## R5. REVISION 3 (orchestrator-applied, per re-audit-2)

Re-audit-2 (JUNCFORGE_S2_reaudit_report.md follow-up round) found 1 critical + 1 gap
surviving REVISION 2: (C) §R2's verdict paragraphs and §S5's verdict-of-record line
recreated the unrestricted "inconsistent at row A" scope (omitting char-2 / Φ₂-landing /
interior-Φ₂A-pin); (G) §S3 still said "VERBATIM"/"now COMPILED" for the D0 identity tie.
After two delegated correction rounds on the same wording class, the orchestrator applied
the quoted fixes directly (the two-failed-corrections discipline): §S3 recast at
DEFINITIONAL EQUALITY with the accurate certification account; §S5 and both §R2 sites now
carry the restrictions inside the verdict text itself. The verified perimeter (Lean
theorems, §S1 scope table, §R1 negation-shape display, §R3 charter) untouched.
Acceptance counter stays 0/2; re-audit round 3 decides.
