# MovesU blueprint REV 6 — delta-confirmation audit

- **Date**: 2026-07-28 (run 2026-07-27 session)
- **Auditor**: fresh Fable #4 (delta-confirmation instance; no prior context)
- **Scope**: rev-6 delta only (`641c3e4` vs rev 5 `572a622`), the MOVES CL-10
  citation basis, and the U3/U4/U6 slice discipline in the current
  `lean/notes/MOVESU_LEAN_BLUEPRINT_2026-07-28.md`. The unchanged rev-5 text is
  NOT re-audited — two independent 0-critical sweeps (Codex FINAL#2 modulo the
  vpsound root cause; Fable #3 `c13b513`) stand on it.
- **Parallel**: a Codex final on rev 6 runs independently.

## 1. Delta verification (git) — CONFIRMED

`git diff 572a622 641c3e4 -- lean/notes/MOVESU_LEAN_BLUEPRINT_2026-07-28.md` shows
exactly: (a) header + REV 6 note paragraph; (b) one phrase in the §D12 slice prose
("— CL-10 WHOLE, `cl10_vpsound` included per REV 6 —"); (c) the one new `FinStack`
field `cl10_vpsound : VPSound X` with its docstring; (d) the projection updated to
`⟨L.cl7, L.cl10, L.cl10_vpsound, L.finiteness_stack⟩`; (e) §6 status/counts text;
(f) the appended CF2 disposition table. Nothing else. Working tree = rev 6 commit
(`git diff 641c3e4 HEAD` on the file is empty; HEAD `c13b513` postdates it).
`CapstoneLedger.cl10_vpsound` pre-exists (line 575, REV 3), so the projection is a
literal field selection; constructor order matches `FinStack`'s field order.

## 2. Citation verification (MOVES_2026-07-24.md) — CONFIRMED, whole-package

- **13140–13143** (the (U-n) display): "the UPPER side GIVEN the finiteness stack
  {SQ.0's budgets with TRACK-COUNT + D(n) + the genuine-increment sub-claim (CL-7);
  the [3t] package (CL-10)} AND the solve stack {E0 (CL-1); …}" — CL-10 is cited as
  the whole package, no VP-SOUND carve-out; VP-SOUND is absent from the solve-stack
  list (so `SolveStack` correctly omits it).
- **13281–13284** (CL-10's own ledger entry, whole entry read at 13253–13284): ends
  "…and VP-SOUND (a citation obligation — the PARI-oracle refuters test IT, never
  the caps). Without CL-10 the solve computes marked-branch totals, not densities" —
  VP-SOUND is a component OF CL-10.
- **13033** (inside §SQ.1, header at 13017): "the per-fiber MASS is [3t]
  TREE-EXP-fin GIVEN (SIB) — CL-10's tags ride every consumption." — the
  ride-every-consumption rule covers U3's partial-sum citation ("(SQ.0/CL-7) …
  (TREE-N/CL-10)", 13044–13045) as well.

Conclusion: no display encodes a VP-SOUND-free half of CL-10; the rev-6 placement
of `cl10_vpsound` in `FinStack` (hence riding U3, U4, U6) is exactly the note's
citation. The rev-6 note's quoted citations are accurate against the source lines.

## 3. Slice discipline (FinStack/SolveStack/LowerStack vs U3/U4/U6) — FAITHFUL

- **U3** consumes `FinStack` = {cl7; cl10; cl10_vpsound; finiteness_stack} — exactly
  the finiteness stack {CL-7; CL-10 whole} + the operative TREE-N identity
  (13040–13045 + the 13033 riding rule). Not too thick, no longer too thin.
- **U4** consumes `FinStack` + `SolveStack` (+ explicit RegP, p.Prime). `SolveStack`
  = CL-1/5/6/8/9/11/13–16/17/18/19 + the operative identification — the (U-n)
  upper solve-stack list verbatim (13142–13145); VP-SOUND correctly NOT a
  `SolveStack` field (it enters via `FinStack`). SolveStack docstring (line 650)
  "NO VP-SOUND" is correct as a slice description.
- **U6** consumes those + `LowerStack` = {cl4; rs4_checksum; rs4_eval} — "the LOWER
  side additionally GIVEN RS.4's inherited set (X.3/CL-4 included)" (13145–13146);
  the inherited set's other members (E0, CL-5, CL-17, CL-18) already ride in
  `SolveStack`. CL-2/CL-3 in no unit premise; rate form stays gate SQUEEZE-n3
  (13156–13158). Capstone-only fields (O3, cl4_env_tendsto) in no slice.

## Finding (1)

**F4-G1 — GAP.** Blueprint lines 788–789, U4 `hypothesis_fields`:
> "EXACTLY `FinStack` + `SolveStack` (the (U-n) upper side's displayed citation
> list, D12 — NO CL-2/CL-3/CL-4, NO RS.4, NO VP-SOUND, NO O3)"

The "NO VP-SOUND" is a stale rev-5 annotation: under rev 6 U4's premise DOES
include VP-SOUND (via `FinStack.cl10_vpsound`), and per §2 above the (U-n) upper
citation list DOES include it (CL-10 whole). The formal content (structure defs,
theorem signature, D12 prose) is correct; only this audit-contract gloss
contradicts it, and it is exactly the line an E-phase implementer checks U4's
premise against. Repair: delete "NO VP-SOUND" there (or reword: "VP-SOUND via
FinStack, not SolveStack"). Classification: justification/annotation gap — no
logical chain broken. (Line 650's "NO VP-SOUND" needs no change: it describes the
`SolveStack` slice alone, which is correct.)

## Counts + verdict

0 critical / 1 gap (F4-G1, one-phrase stale annotation at U4's hypothesis_fields).
The rev-6 delta itself is exactly as advertised, the citation basis is verified
whole-package at the source lines, and the three slices are faithful per display.

**REJECT (0 crit / 1 gap)**
