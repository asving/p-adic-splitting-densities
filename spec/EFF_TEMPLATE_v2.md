# EFF TEMPLATE v2 (2026-08-13, post-pilot-cross-read — GOVERNS all 0a runs after EFF-T3)

Changes from the pilot format, per runs/qgen/EFFT3_crossread.md (9 template changes):

1. **DERIVATION field (new, mandatory per statement unit):** the unit's proof from the
   effective text, resolved the same way as the statement (supersessions applied),
   quoted-or-[ASSEMBLED] under the same fidelity rules. Without it the chapter
   blueprints must re-read the notes and the compilation gate is defeated.
2. **XREF VERIFICATION (hard rule):** every XREF designation must be grep-verified to
   EXIST in the target note (`grep -cF '<designation>' <file>` ≥ 1, count recorded
   inline). An unverifiable designation is an OPEN-CALL, never an invented name.
3. **NON-IMPORTS section (new):** the note's explicit negative-import fences (what it
   declares it does NOT consume) — these are load-bearing for the DAG.
4. **TYPE ENUM widened:** add [absorption-record | battery-row | fence | table |
   changes-record | acceptance-box] to the unit kinds; boxed absorption displays
   (the pilot missed (T3-A0)) and §-tables are UNITS, not prose.
5. **TABLES:** transcribed as tables, flagged [TABLE], never prosified.
6. **TEETH inverse table (mandatory):** battery row → guarded unit(s), both directions;
   zero-orphan check stated.
7. **SCOPE SPLIT (header):** two distinct predicates, never conflated: (a) the
   append/consumption PROTOCOL scope; (b) the note's ABSORPTION/supply SET. Quote
   the governing text for each separately.
8. **CONSUMER EDGES:** the acceptance record's supplies-to list becomes explicit
   reverse-XREF rows (consumer note : designation), grep-verified like rule 2.
9. **SHARDING:** notes > ~80 KB are compiled per-section in multiple runs (shard
   charge names the section span + the shared header), then a MERGE run reconciles
   IDs/xrefs. Sequencing: T1, T2, GENTOW5, W12 shards first (straddle the codex
   reset); tag-sparse prose-proof notes (GRTJB, HE7, GENTOW5) get a boundary-choice
   self-audit section (the pilot validated only the tagged genre).
10. **CROSS-NOTE STATUS CLAIMS:** a claim that a correction/supersession in ANOTHER
    note is unlanded must be verified against that note's FULL append chain (dated
    annexes/appends at the note's tail), never by grepping the original pinned
    sentence — frozen text never disappears; absence of change at the pinned line is
    not evidence. Cite the landing commit where one exists.

Unchanged from the pilot: header (blob hash, resolution rules), CANONICAL STATEMENT
fidelity rules (verbatim-or-[ASSEMBLED]), RESOLUTION TRACE, CONDITIONALITY,
consumption table, self-audit with OPEN-CALLs, the compiler-not-author charge.

## v3 (2026-08-14, the prose-genre rules — GOVERN all remaining runs, prose notes especially)

Changes from v2, per the HE7 prose-genre pilot's three-shard BOUNDARY SELF-AUDIT (§6.3
of `spec/EFF-HE7-s1of3.md`, `-s2of3.md`, `-s3of3.md`, plus the SERIES finding at
`-s2of3.md` §6.1 item 2): an 18-item format verdict, each item a rule the pilot applied
to itself before recommending it. Codified below as rules 11–28.

11. **FORM sub-field (statement units):** every statement unit's CANONICAL STATEMENT
    carries a `FORM: display | bold-headed paragraph | bracketed rider | inline sentence`
    sub-field. Mandatory whenever the note is tag-sparse prose (no `\tag{}` display), so a
    downstream chapter cut can tell a theorem from a remark without re-reading the note.
12. **RESOLUTION TRACE, three slots:** when a unit's derivation is not attributable to one
    contiguous span — the proof lies hundreds of lines from its statement, as is routine in
    prose proofs — RESOLUTION TRACE records `statement lines` + `proof lines` +
    `correction sites` as three distinct ranges, never one range standing for all three.
13. **`supplier-finding` (new TYPE ENUM member):** use `supplier-finding`, not
    `changes-record`, for a unit whose content is a defect report against ANOTHER note,
    discharged at the source rather than a lemma, instance record, or scope record of the
    home note.
14. **Double-emission for ASCII displays (table rule extended):** a table rendered as a
    fixed-width ASCII block inside a source code fence is emitted TWICE — verbatim as the
    source display, then again as a `[TABLE]` Markdown transcription — never transcribed
    alone (loses the source bytes) and never quoted alone (violates the tables-are-units
    rule).
15. **NEAR-MISS XREF disposition:** when a cited designation fails fixed-string grep only
    on case, punctuation, or a period inside bold/markup, do not emit a clean XREF and do
    not suppress the citation; record a `NEAR-MISS` disposition instead — "designation
    absent as written; verified referent at `<file>:<line>` under `<actual string>`, count
    N" — distinct from both a clean XREF and an OPEN-CALL.
16. **PROOF-ONLY teeth row class:** the teeth inverse table (v2 rule 6) carries an explicit
    `PROOF-ONLY` row class for a guarded unit whose interesting content is its proof, not a
    battery; quote the note's own coverage-hole sentence for that row rather than leaving
    it blank.
17. **Scope split predicate C (inbound corrections):** header predicate B ("what has been
    landed on other notes", v2 rule 7) may be answered by an explicit NO-APPENDS
    declaration with its quotation; add predicate C — inbound corrections RECEIVED from
    supplier notes — since a note that discharges a box while receiving corrections has
    DAG edges neither predicate A nor B can record.
18. **SUPERSESSION KIND (mandatory field, 8 kinds):** every unit that supersedes prior text
    declares `SUPERSESSION KIND: replacement | license | wording-rider | provenance-rider |
    scope-pin | as-of scoping | counter re-reading | inventory completion`. Source riders
    phrased near-identically ("Read X as Y") are NOT interchangeable — conflating two kinds
    corrupts the DAG in a different way each time, so the kind is decided by function, never
    by matching the source's phrasing.
19. **`regression-record` retired; three replacement TYPE ENUM members:**
    `preregistration` (a stated-in-advance falsifier or threshold), `run-record` (an
    executed instrument's result), and `instrument-record` (a description of the testing
    apparatus itself), since the three carry different truth conditions and different
    failure modes under one name. Emit `preregistration` and `run-record` as two units
    whenever the source itself writes the prediction before the sealed run.
20. **Disclosure disposition vocabulary (4 labels):** the TEETH disposition enum, for a unit
    reporting an instrument's disclosure rather than a clean pass/fail, adds `signed
    vacuity disclosure` (tested on a vanishing or trivial fraction of cases), `disclosed
    non-repair` (a guard that never fired), `accepted-with-decorrelation-supplied`
    (answered only by an independent instrument), and `stale self-description` (a frozen
    self-description the instrument's own result falsifies).
21. **FREEZE PREDICATES (header list):** when a note carries more than one independent
    freeze — e.g. a text-freeze (acceptance) and an instrument-freeze (an artifact seal) —
    the header lists each as its own `FREEZE PREDICATES:` entry with its own quote and its
    own pin; one freeze predicate must never stand for both.
22. **Mandatory arithmetic audit on `[TABLE]` count tables:** every `[TABLE]` of counts
    gets a compiler-computed arithmetic-audit line — row sums, column totals, and
    cross-checks against every other number in the note that should match it — computed
    fresh, never assumed from the source's own labels.
23. **PIN VERIFICATION (rule 2 extended to commit hashes and artifacts):** a cited commit
    hash is verified with `git cat-file -t`; a cited artifact filename is verified to
    exist. A reported run backed by no filename at all gets an explicit `UNPINNED`
    disposition rather than a silent pass.
24. **TARGETS field (bivalent units):** a unit that is simultaneously a new statement and an
    instruction to re-read frozen text elsewhere carries a `TARGETS:` field listing
    `<shard>.<id>` for every span it supersedes, so a merge run can build the edge list
    mechanically instead of by re-reading prose.
25. **CHAIN representation with TERMINAL marker:** when a supersession has more than two
    layers (frozen text → rider → rider …), record the full `CHAIN:` in source order and
    mark which member is TERMINAL — the reading a chapter cut must actually use — since a
    flat "this supersedes that" field cannot say which of several links is current.
26. **STALE-SELF-DESCRIPTION conditionality tag:** when a note contains a frozen sentence
    describing its OWN status (e.g. "has not been through a hostile pass") that a later,
    unedited event falsifies, tag it `STALE-SELF-DESCRIPTION` in CONDITIONALITY rather than
    `superseded` — the sentence is not corrected under the freeze, but the reader must be
    told it is no longer true.
27. **Decorrelated-finding AUDIT disposition class:** the teeth vocabulary adds an `AUDIT`
    disposition — `decorrelated-model audit | in-house hostile pass | transfer audit |
    arithmetic recount` — for a finding no battery or tooth could have produced (an
    incoherent definition, an underived equivalence), quoting the note's own "no tooth
    applies" sentence where one exists. Flagged by the pilot as the single most important
    addition for prose-proof notes, since prose proofs fail in ways batteries cannot see.
28. **Dated-arc SERIES type:** a chronological sequence of dated entries continuing one box
    or record across sections, annexes, or shards is a `SERIES`, not one merged "arc
    record" unit and not independent units with no memory of each other: emit one unit per
    dated entry, but record the series membership and order explicitly, so a merge run
    spanning shards can reconstruct the order mechanically rather than by prose-reading.

## v3.1 (2026-08-14, the wave-3/4 accumulated rules)

Changes from v3, accumulated across the wave-3/4 compilations and merges — GENIND/GENH4
(queue 5, self-audit at `spec/EFF-GENIND-s1of3.md` §6.3 and `spec/EFF-GENIND-s3of3.md`
§6.3), GENHN/HE3/GRTW2 (queue 6), GRTJB/GRTJC (queue 7), and the HE7/GENIND/GENH4/
LIFTCORNER merge runs. Each compiler applied its own recommendation in its own spec file
before this codification, so where the one-line proposal is ambiguous, the cited file's
practice is the rule. Codified below as rules 29–39.

29. **SUPERSESSION KIND gains `withdrawal` (ninth kind) and a `deletion` marked sub-kind:**
    `withdrawal` names a claim or input that becomes UNAVAILABLE with nothing put in its
    place at that site — materially different from `replacement`, which substitutes one
    display for another. `deletion` names an explicit instruction to remove a sentence or
    clause that remains byte-intact at its frozen source line unless the edge is installed.
    Both were filed as bare `replacement` faute de mieux before this rule: GENIND's `.49`
    ("the scalar bound … is withdrawn") and `.56` ("Delete 'H>0, hence M★<N' from C2(ii)",
    the deleted string verified still present at source line 3382); GENHN's `[r2]`
    withdrawal of "No new mechanism" and "inheriting exactly GENHN.A's clause grades", with
    nothing substituted; GRTW2's E5 finding 1, `SUPERSESSION KIND: replacement (a
    withdrawal)`. A merge that reads any of these as an ordinary `replacement` will keep
    consuming a withdrawn input, or leave a deleted sentence readable as live text.
30. **Per-consumer TERMINAL markers (rule 25 extended):** a `CHAIN:` may carry MORE THAN
    ONE `TERMINAL` when different consumer classes require different current readings of
    the same chain — the v3 rule as written assumes exactly one. GENIND's (CS-1) hypothesis
    chain is the confirmed instance: `[r2]`-corrected (CS-1) is TERMINAL for
    menu/transport consumers, while `(CS-1Q), verified per genre` is TERMINAL for rate
    consumers (ledger row HYP.36); its five-layer CS-drain-rate chain shows the same
    two-terminal shape split by proof layer instead of by consumer class. Each TERMINAL is
    labelled with the consumer class it governs, and a chapter cut must carry all of them —
    a merge that installs only one edge misstates the other consumer class.
31. **`hostile-pass certification` — a positive AUDIT disposition (rule 27 extended):** the
    AUDIT class previously had only finding-shaped members (`decorrelated-model audit`,
    `in-house hostile pass`, `transfer audit`, `arithmetic recount`) and no member for a
    hostile pass whose result CERTIFIES rather than finds. GENH4's Remark 2 and its "the
    consumed surface was independently RE-DERIVED CLEAN by the pass" are exactly this
    shape; without the label, the strongest evidence in the note was unlabelled.
32. **Consumer-sweep bullets are first-class supersession vehicles (ruling on the
    GENIND/GENH4 OPEN-CALL):** an imperative consumer-sweep bullet ("In X, replace Y by
    Z", "Delete W from V") is a supersession, not a downstream reading note, and every
    named target MUST resolve to a unit ID. A target inside the home note gets the sweep's
    reading installed as CONDITIONALITY on that unit; a target in ANOTHER note becomes an
    XREF plus a protocol obligation, never an assumed landing — LIFTCORNER's settling
    practice: "Where an annex's consumer sweep names a target inside this note, the target
    unit carries the resulting reading in CONDITIONALITY; where it names a target in
    ANOTHER note, it becomes an XREF and a protocol obligation, never an assumed landing."
    A compilation that cannot resolve a sweep bullet's target by hand records the failure
    as an OPEN-CALL; it must never emit the sweep as an unaddressed reading note.
33. **`instrument-audit` — a new TYPE ENUM member:** for a unit whose content is the note
    auditing its OWN instrument and disclosing what it finds — not `run-record` (no run
    was executed), not `instrument-record` (the finding CONTRADICTS the instrument's own
    description rather than describing it), and not `changes-record` (no mathematical
    statement moves). HE3's four SELF-FOUND instrument audits (the sealed-vs-delivered
    shortfall, HE-T-NODE's mis-specification, P4's quasi-tautology, the N1 demo's dead
    geography) had no clean home in the existing enum; rule 27's `in-house hostile pass`
    is extended to cover self-audit of instruments as well as of prose.
34. **`AS-OF-PIN` — a pin-verification class distinct from PINNED/UNPINNED (rule 23
    extended):** for a cited hash or artifact that was honest, checkable evidence AT ITS
    OWN APPEND TIME but is un-recheckable now because the object it names has since
    changed BY DESIGN (an append-only file that keeps growing). Labelling such a pin
    UNPINNED misrepresents it as never having been checkable; labelling it verified
    misrepresents its current state. GENHN's four prefix-md5 declarations are the
    confirmed instance, excluded from the ordinary pinning ledger and recorded instead as
    as-of freeze evidence.
35. **`acceptance-scope enumeration` — a new FREEZE PREDICATE (rule 21 extended):** a
    note's explicit statement of WHICH claims a grade covers — including accepting an open
    box "as a box, not as a theorem" — is a freeze predicate distinct from a text-freeze or
    an instrument-freeze, and any unit reporting a grade must quote it. GRTW2's (F3) is the
    corpus's own proof of the rule's value: a certifier's CRITICAL against a later annex
    was rejected precisely because the acceptance's own scope enumeration excluded it —
    without (F3) the finding would have been arguable against the acceptance itself.
36. **`partial-withdrawal` — tenth SUPERSESSION KIND, replacement display attached:** for a
    supersession that re-issues a display with MOST of the clause surviving — distinct
    from full `withdrawal` (nothing replaces the claim), `replacement` (the whole clause
    moves), and `counter re-reading` (a gloss is re-read, no display is re-issued). The
    field MUST carry the replacement display verbatim. Confirmed independently across both
    notes before codification — GRTJB's E-3, and GRTJC's Annexes #4, #5, #6, and #8 (each
    annex's own record and, where a downstream lemma restates the correction, that lemma's
    unit too) — six occurrences by the compilers' own running tally ("five in GRTJC, one
    in GRTJB"), every one of them carrying a replacement display the field is now required
    to hold.
37. **MERGE-STAGE — the foreign-note citation guard:** before a shard-offset ID rewrite
    touches any bare `.NN` reference, it must first protect every citation of the form
    "`<Note>`'s shard N `.NN`" / "`<Note>` shard N `.NN`" that names ANOTHER note's own
    numbering scheme — such tokens must never receive this note's own offset. A bare
    in-range check cannot catch the failure mode: GENH4's first-pass rewrite silently
    shifted a foreign GENIND citation into a value that coincided with a genuine GENH4 unit
    ID (`.94`, plausible and wrong) plus one that landed out of range (`.126`); the fix
    recognizes and protects any `"<Capitalized-note-name>['s] shard N"` pattern before
    shifting, and the result is verified byte-identical to the source text at every
    protected site.
38. **MERGE-STAGE — the definitive-mapping audit for explicit shard-local citations:** a
    shard-offset rewrite must never apply a blind global substitution to bare `.NN` refs
    inside a shard's own prose. It must instead build an explicit table of every citation
    labelled as pointing into the OTHER (differently-offset) shard, by enumerating every
    occurrence of the labelling pattern in the source text (LIFTCORNER: 18 lines, 22
    protected tokens, built by reading all 35 "shard 1" occurrences in shard 2's text), and
    exempt exactly those tokens from the shift; a label's scope persists across a
    comma-separated list under one shared label and resets at the next unlabelled token.
    Audit afterward by an exhaustive regex sweep for leftover shard-local substrings and
    for out-of-range IDs.
39. **MERGE-STAGE — source-self-count errors are booked as defects, never silently
    reconciled:** when a shard's or note's own summary tally of its inventory (a stated
    count of units, designations, or marked occurrences) disagrees with a literal recount,
    the compilation records BOTH figures and flags the discrepancy as a defect; it never
    silently substitutes the recount for the stated figure or vice versa. LIFTCORNER's
    merge is the named instance: shard 2 twice asserts "fifteen" `[TRANSCRIBED —
    certifier]` units, but its own cited ranges sum to, and a fresh grep of every header
    line confirms, 20 — corrected in the merge rather than silently carried forward.
    GENH4's merge found the same shape independently: a shard's "27 distinct designations"
    claim reconciles against neither a literal recount by row (23) nor by
    slash-separated pattern (33); flagged as a merge-level defect with no individual
    designation's own grep count in doubt.
