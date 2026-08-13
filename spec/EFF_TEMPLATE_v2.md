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

Unchanged from the pilot: header (blob hash, resolution rules), CANONICAL STATEMENT
fidelity rules (verbatim-or-[ASSEMBLED]), RESOLUTION TRACE, CONDITIONALITY,
consumption table, self-audit with OPEN-CALLs, the compiler-not-author charge.
