# The prover RCT — protocol (PREREGISTERED)

**Directive (Asvin, 2026-08-10, verbatim intent):** "for each thing to
be proved, lets randomly use either fable or the pro codex (a RCT!) and
observe the comparative advantages and disadvantages. Lets leave the
fixes as it is for now."

**Sealed before the first assignment.** Amendments are dated appends.

## 1. Population

Every new PROOF-COMPOSITION unit dispatched after this protocol's
commit: the simplification compression targets (T1–T5, as cleared by
the plan revision), the second-generation probes (SG-1..4), named open
lemmas (e.g. [GENTOW5-W(i)], the S8.1 member half, GENH5-DENS genre
aggregation), and distribution-arc composition units.

**Excluded (unchanged pipelines):** repair/fix/rider units (per the
directive), hostile verification passes (the 2-clean arc stays
Fable-verifier), Codex ratification legs, instrument-only units,
adjudications, exposition units.

## 2. Randomization (auditable coin)

Assignment = parity of the first hex digit of
sha256("PROVER-RCT-2026|<unit-name>"): even → FABLE, odd → CODEX.
The unit-name is the ledgered dispatch name (e.g. "S-1-T1-gauge-cocycle").
Computed and RECORDED in §6's table at dispatch time, before the unit
runs. Deterministic, so anyone can re-derive every assignment; no
discretion at assignment time. No re-rolls: if an arm cannot execute a
unit for a structural reason, the unit is recorded EXCLUDED-WITH-REASON,
never reassigned silently.

## 3. Arms

**FABLE:** the standing composer unit — composes the proof note AND
builds its own sealed instrument (two-commit seal, teeth), per the
established discipline.

**CODEX:** gpt-5.6-sol at model_reasoning_effort=high (the strongest
configuration available on the ChatGPT Team account; the -pro model is
rejected with a 400 — if an API key later enables it, the arm upgrades
by dated amendment). The unit = a self-contained brief (all context
pasted; Codex cannot read files here) charging COMPOSITION: statement +
full proof + a specified machine-verification plan (frames, predicted
exact values, teeth). A Fable LAB-TECH unit then transcribes the proof
into the repo note verbatim, implements the specified machine leg, and
seals it. THE TECH MAY NOT ALTER MATHEMATICAL CONTENT — transcription
and implementation only; any gap the tech hits is recorded in the note
and left for the arc (it is DATA, not something to quietly fix).

**Both arms downstream, identical:** the 2-clean fresh-context hostile
arc, same charge template, same acceptance rules; repairs by the
standing (Fable, re-derive) units regardless of composing arm.

## 4. Preregistered outcome measures

Per unit: (a) rounds to acceptance (passes + repair rounds); (b)
first-pass finding profile (CRITICAL/GAP/MINOR counts); (c) instrument
quality (teeth caught on first run, RED-run rate, tautology-audit
result); (d) later cross-model findings against the accepted text
(Codex findings on Fable proofs and vice versa); (e) cost: tokens (both
APIs) + wall-clock; (f) qualitative failure modes, one paragraph each,
written at acceptance time.

## 5. Analysis plan + honest confounds

Enumerative comparison table when either arm reaches 6 accepted units
or the campaign ends — NO significance claims at these n; we enumerate,
we do not infer. Confounds, declared: the arms' workflows differ
(tech-mediated vs direct — we are trialing the practical workflow, not
the isolated model; a pragmatic trial); unit difficulty is
heterogeneous (mitigation: a difficulty tag [routine/hard/frontier]
recorded at assignment time, before the arm is looked up); brief
quality varies (mitigation: briefs follow the standing self-contained
template). The known ratification asymmetry — Codex ratifying
Codex-composed proofs loses decorrelation — is accepted: the primary
decorrelated check for CODEX-arm units is the Fable hostile arc itself,
and this is recorded rather than patched.

## 6. Assignment ledger (append rows at dispatch)

| unit | difficulty (pre-tagged) | sha256 first hex | arm | dispatched | outcome |
|---|---|---|---|---|---|
| S-1-T1-gauge-cocycle | hard | 3 | CODEX | B23 2026-08-10 | |
| S-7-SG2-probe | frontier | b | CODEX | pending | |
| T2-sigma-ladder-master | frontier | 6 | FABLE | pending | |
| T3-cocycle-telescope | hard | f | CODEX | pending | |
| T4-certificate-witness | hard | f | CODEX | pending | |
| T5-w-frame-note | routine | e | FABLE | B23 2026-08-10 | |
| GENTOW5-W-i-lemma | hard | 2 | FABLE | B23 2026-08-10 | |
| S8.1-member-half | frontier | 7 | CODEX | pending | |
| GENH5-DENS-aggregation | hard | 2 | FABLE | pending | |

**Protocol deviation, disclosed (2026-08-10, minutes after sealing):**
the orchestrator PREVIEWED all nine arms above before recording
difficulty tags — the §2/§6 ordering (tag before arm lookup) was
violated for these nine rows. Mitigation: the difficulty tags above
were recorded immediately after, in this same commit, before any unit
ran — so tags still precede all outcomes, but tag-blindness to arm is
lost for these nine. The coin being deterministic, arm-blindness was
always weak; the promised ORDER was still broken and is recorded.
Units added later: tag first, then compute the arm.


## Amendment 1 (2026-08-10, owner directive)

Asvin, after round 1's results (verbatim intent): "Lets use codex for
the hard math for a while then, and see how it goes."

- HARD and FRONTIER tier units are assigned **CODEX by directive** for
  an observational period — the §2 randomization is SUSPENDED for
  those tiers (the trial becomes observational there; §4 outcomes are
  still recorded identically, and the arc stays arm-blind).
- ROUTINE tier units keep the §2 coin (preserving a randomized strand).
- Ledger flips under this amendment: T2-sigma-ladder-master
  (FABLE → CODEX), GENH5-DENS-aggregation (FABLE → CODEX). Reason
  column: owner directive, this amendment.
- The CODEX-arm workflow is unchanged (self-contained brief; one
  foreground high-effort call; lab-tech transcription with no content
  alteration; gaps recorded as data; the 2-clean Fable arc judges).
- Revisit trigger: when the arcs have judged ≥3 CODEX-arm hard units,
  fold the comparison and re-decide with Asvin.
