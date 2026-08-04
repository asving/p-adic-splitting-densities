# RMENGINE pass PC6 report (Codex, round 6) — 2026-08-04

Object: the r5 text (cfb3648). Charge: /tmp/openmath/RMENGINE_PC6_charge.txt (144,606 chars). Raw stream: /tmp/openmath/rmengine_pc6_out.jsonl. Verbatim below.

---

I’ll audit the r5 remedies first, including a sweep of every historical disposition/head bracket for unresolved supersession, then re-derive the standalone spine and check the r5 diff’s S2–S7 hygiene. I’ll keep execution limitations note-only and will not modify anything.

=====MSG-BREAK=====

1. > “machine-output quotes carry their as-of commit (only the committed output file speaks for the current text)”

   > “with the HEAD figure (zones 13) displayed”

   > “machine-output quotes are re-quoted whenever a re-run changes any figure”

   **GAP — the standing rule is internally inconsistent and not future-proof.** The first rule correctly makes historical quotes commit-pinned and delegates current figures to the committed output file. The round-5 record instead uses the dynamic term “HEAD” for 13—while HEAD at cfb3648 has 15—and twice states a different rule requiring changed figures to be re-quoted. The r5 re-run changed 13 → 15, yet the note retains the r3 quote and only mentions 13. Either the as-of/file-arbiter rule or the re-quotation rule can work, but the record currently asserts both and does not satisfy the latter. Record-layer only; zero mathematical-chain impact.

2. > “bubblewrap is unavailable”

   **NOTE.** Repository execution was unavailable. Content inspection of Appendix B confirms that the r5 delta touches only head/record surfaces and no S2–S7 content. The three supersession brackets are accurate and sufficient; both gloss fixes are correct; and the standalone mathematical spine disclosed no defect.

RMENGINE-PC6 FINDINGS: 0 critical, 1 gaps
VERDICT: GAPS-ONLY
