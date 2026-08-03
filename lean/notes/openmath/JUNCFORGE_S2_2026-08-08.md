# FORGE junc_bundle STAGE 2 — the first compiled e ≥ 2 junction attempt ADJUDICATES THE BUNDLE INSTANCE-FALSE AT THE ROW-A READ: the parity wall (no e = 2 recording exists at the row-A read), the Φ₂-landing wall (char-2, all species/degree faces), the D0 flag CONFIRMED in Lean (gate hbundle unsatisfiable — byte-identity kernel-certified at REV1), clause (iii) POSITIVELY derivable at the read-pair pins — **REVISION 1 APPLIED (§R1–R3: row-A rescope, negation shape, D0 tie compiled, disposition + re-derivation charter)**

**Unit:** FORGE junc_bundle stage 2 (wave 11; charter = stage 1's §S5 spec,
`JUNCFORGE_S1_2026-08-08.md`).  **Artifact:**
`lean/LeanUrat/Scaffold/HDischarge/H1/JuncForge.lean` — NEW declarations only; no
existing statement touched (`gate_glue_junction`/`gate_glue_conditional` displayed,
not edited); `lake env lean` green; every theorem `#print axioms` = Lean core
`{propext, Classical.choice, Quot.sound}`; zero sorries.
**Row-A data compiled:** f = X² + 4X + 28, Φ₁ = X + 2, Φ₂ = X² + 4X + 12 over ℤ₂;
the deep development f = 24 + Φ₁² (slots (24, 0, 1)) as `fA_eq`/`BA_dev`.

## S1. VERDICT — the §S5 discharge is IMPOSSIBLE: `junc_bundle` at row A is instance-false

Executing the stage-1 spec against the Lean `SideReads` transcription did not
produce the chartered first compiled e ≥ 2 junction — it PROVED no such instance
can exist AT THE ROW-A READ: at any stage whose frame is keyed at Φ₁A (`hσΦ`),
reading the row-A classificand fA under a development at that frame (`hdev`), for
any finite residue field, any recorded node data, and any designated Φnext.
\[REV1: the original sentence here ended "at any stage, for any recorded node
data" unqualified — bracketed as an overclaim; every wall binds the row-A fiber
(fA, Φ1A) through the `hσΦ` + `hdev` hypotheses. Outside that fiber (other
classificands, other keys) existence is OPEN.\]

| theorem | statement | scope |
|---|---|---|
| `juncforge_no_e2_junction` | any `SideReads` of f = fA at a Φ₁A-keyed frame has ν.e = 1 | the row-A fiber (fA, Φ1A): any finite F, any Φnext — char-free |
| `juncforge_deep_wall` (+ `_F4`) | no `SideReads` of f = fA at a Φ₁A-keyed frame lands Φ₂ | row-A fiber; any finite F with (2 : F) = 0; instantiated at F4 |
| `juncforge_junc_bundle_false` | the `junc_bundle` 3-conjunct CORE ∃ (dev + interior pin + SideReads) is FALSE at every continuation H₂ with base key Φ₁ and node-1 key Φ₂ | packaged form — negates the WEAKER core, which any fuller bundle implies, so refutes every fuller bundle AT ROW A; not a verbatim general ¬junc_bundle \[REV1\] |
| `juncforge_clauseIII_derivable` | clause (iii) alone IS derivable at the (2,3)-graded pins — the harness shape exact | positive fragment, conditional on the pins |
| `juncforge_D0_instanceFalse` | `gate_glue_junction`'s `hbundle` is unsatisfiable | the flagged D0 adjudication; byte-identity KERNEL-CERTIFIED at REV1 (`juncforge_gate_hbundle_false` + `juncforge_gluePacket_false`, §R1-G2) |

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
`gate_glue_junction` VERBATIM \[REV1: this identity claim is now COMPILED, not
prose — `juncforge_gate_hbundle_false` (the gate binder text negated, proof term =
`juncforge_D0_instanceFalse` applied directly) and `juncforge_gluePacket_false`
(the non-textual leg: ∀ H₁, ¬ GlueJunction U31.fq H₁ H₂rc recentering, via the
structure's own `junc_bundle` field); see §R1-G2\]: at the compiled seam the junction frame's key IS the
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
  theorems bind row A\]: **`junc_bundle` is INSTANCE-FALSE as transcribed**
  — the E-PHASE FLAG (HC2/Defs clause (iii) "may over-strengthen") lands as a
  proved INTER-CLAUSE CONTRADICTION ((ii) ⊥ (iii) at e = 2; (ii)+(iv) ⊥ at e = 1),
  not an over-strengthening of one clause.  Verdict of record (§R2): INCONSISTENT
  AS TRANSCRIBED, COMPILED AT ROW A.
* The C-e escapee is EXPLAINED AT ROW A: GlueRun's "no compiled e ≥ 2 instance
  exists on file to feed it" is now "none CAN exist AT THE ROW-A READ — fA against
  a Φ1A-keyed frame, any Φnext" (`juncforge_no_e2_junction`).  \[REV1: the
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
  (`hdev`), for ANY finite residue field and ANY designated Φnext.  The honest
  headline: **no e ≥ 2 `SideReads` recording can exist AT THE ROW-A READ (fA,
  Φ1A fiber, any Φnext)**.  The unqualified forms ("at any stage, for any
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

* **(G2 — D0 byte-identity, now COMPILED.)**  The §S3 "byte-identical" claim is
  no longer prose.  Two new Lean-core declarations (`JuncForge.lean` §8, new
  decls only; `lake env lean` green; `#print axioms` = {propext, Classical.choice,
  Quot.sound} for both):
  - `juncforge_gate_hbundle_false` — its statement is `gate_glue_junction`'s
    `hbundle` binder copied verbatim and negated (mechanical three-way diff of the
    GlueRun binder slice, the D0 statement body, and the tie copy: IDENTICAL
    modulo leading indentation); its proof term is `juncforge_D0_instanceFalse`
    applied DIRECTLY, no massaging — elaboration itself certifies the two
    propositions coincide.
  - `juncforge_gluePacket_false` — the NON-TEXTUAL leg (per the
    extraction-decorrelation discipline): for EVERY base history H₁,
    `¬ GlueJunction U31.fq H₁ H₂rc ReadSpecies.recentering`, proved by projecting
    the structure's own `junc_bundle` FIELD (the gate's compiled binder type, not
    a copy) into the D0 verdict.  This makes "`gate_glue_conditional` is VACUOUS
    at its compiled instance" a THEOREM: the packet its conclusion route needs is
    uninhabited.

* **(G3 — disposition.)**  §R2 and §R3 below.

## R2. THE DISPOSITION (the audit's key finding)

**Verdict of record: `junc_bundle` is INCONSISTENT AS TRANSCRIBED, COMPILED AT
ROW A.**  What is proved is a fact about the LEAN TRANSCRIPTION of the [T-5]
side-read bundle: its clauses cannot cohabit one recorded node at the row-A read.
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
transcription is inconsistent at row A; the source-level question is OPEN.

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
