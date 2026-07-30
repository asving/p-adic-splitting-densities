# THE GOLF CAMPAIGN (2026-07-30) — baseline + worklist

Revert point: commit e9d2430. Fence artifacts: lean/notes/golf_baseline_2026-07-30/
(per-corpus #print-axioms dumps + sorry censuses, built by 13 fresh-context agents).
Baseline state: ~712 non-private theorems across 13 corpora (OM deferred), ALL
Lean-core; sorryAx only at the ten fenced sites + deprecated Moves files.

## PHASE-1 FRESH-EYES FINDINGS (fix-nothing audit; the golf watch-notes)

REPAIR QUEUE (adjudication items, NOT golf):
R1 [Moves, fence-rule class]: L6_measureExact_R4.lean:155 sorried private
   L5_landTwoSided_missing states StratumData ↔ LandingCylinder with NO
   anchor-exactness hypothesis — the corpus's own L5 headers document the Δ-shift
   countermodel against this shape; the ratified repair file (hexact) EXISTS but
   is unconsumed. Adjudicate: re-key the private to consume the repair, or
   delete-and-scope.
R2 [MovesGr, audit hazard]: superseded v1 modules (sorried) coexist with clean
   v2/v3 under COLLIDING names — #print axioms depends on import choice.
   Quarantine the superseded (repo convention) at repo-prep.
R3 [MovesT honesty]: E5's open content is an INTERNAL `have hD4R0K := by sorry`
   — signature reads unconditional (only sorryAx exposes it). Consider promoting
   to a declared hypothesis (statement change; consumers ripple) at repo-prep.
R4 [MovesS]: rs2_unique_interp's in-file "PENDING ORCHESTRATOR RATIFICATION"
   flag is STALE — ratified in the wave-B ledger commit. Docstring fix (golf-safe).

TOP GOLF TARGETS: HC2's 300-line byte-identical block duplicated U20c/U22E1
(+~100-line shared scaffold) — hoist. MovesC dep_thmC_a re-proves Thm C(a)
(~110 ln) — call the real one; C5 hRec duplicates C4; 3×/3× helper dups;
generic-named public helpers to private. MovesV comp_agg/rep_row: DEAD +
over-hypothesized, ctsM re-proves both INLINE (~160 ln each) — sanctioned
dead-decl hypothesis-trim + wire ctsM to call them. MovesSp dead
compCuts/lamMatrix pair. MovesS n2 helper dups → one shared file. MovesD
private-helper lifts (monic-finiteness ×2, pool bound ×3, lexLt ×2). MovesU
detHyp inline dup. STALE RECORDS EVERYWHERE: E-phase MANIFEST snapshots
(X/Sp/D/T/V/HC2) + wrong sorry-claiming headers (XE2/XE3/XD1, SP6, MovesC C5/C6,
HC2 K1) — wrong comments self-reinforce; refresh during golf.

DO NOT TOUCH: frozen statements (envelopeExp/Sqrt's disclosed unused hyps);
the ten fenced sorries; device-only n2 stubs (dead-on-arrival by design);
interface carrier fields (MovesRBase cyl etc.); deprecated Moves files (mark,
skip, quarantine later).
