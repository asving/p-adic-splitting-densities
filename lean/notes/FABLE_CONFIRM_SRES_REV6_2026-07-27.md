# FABLE CONFIRMING VERIFIER — §S-RESUM rev 6 (fresh instance, 2026-07-27)

Charge: (a) verify the (m, c) DISPATCH independently — rebuild the rev-5
census machinery WITH multi-member all-halted outcomes (m_H3/m_H12 type)
explicitly included; exactly-one-summand routing + census-level (K-SUB)
partition; (b) the agreement check (ii) derivation (block typing +
per-member degree law); (c) own-emphasis sweep. Text: live §S-RESUM
(m, c) CLASSIFICATION block (11793–11871) + pass-6 record (12832–52).
Predecessor: FABLE_CONFIRM_SRES_REV5 (CLEAN; its trichotomy was then
refuted by Codex pass 6). Dual shot: a Codex pass runs in parallel.

## A. Census with the (m, c) dispatch (rebuilt): ALL PASS

Rebuilt from the displayed sources ((B1)/(B3) 6114–23, (G1)/(G4)
6062–74, SP.1 flank/co-factor 5950–58), /tmp/sres_rev6_census.py:
stage (D, W), W·D ≤ 6; side (e, ℓ, s₀′); flank compositions; λ
multisets Σgμ = ℓ; members = flank parts (size s·D) + λ factors
(size e·g·μ·D). NEW vs rev 5: every member carries a halted/continuing
STATUS, all 2^m vectors enumerated — so m_H3/m_H12-type multi-member
all-halted outcomes are explicit census objects. 677 shapes, 9494
outcomes (638 of them multi-member all-halted = the pass-6 class).
RESULTS: routing exhaustive AND exclusive — every outcome matches
exactly ONE (m, c) row (route_none = route_multi = 0); census-level
(K-SUB) partition exact: K 39 + term 677 + split 8778 = 9494, no cell
in two summands; all 638 all-halted multi-member outcomes route to
b^term,fin (0 misroutes — the pass-6 critical cannot recur); (SCS)
0 violations (all 39 K outcomes: single λ factor, no flanks, size
= W·D exactly); degree law 0 violations (member sizes sum to W·D in
all 677 shapes; m ≥ 2 ⟹ every size < W·D, halted members included);
fence 0 violations (no e = g = 1, μ < W factor in any m = 1 shape;
703 such edges, all in m ≥ 2 shapes). Roster instances found: m_H3
(3,0) → term; m_H12 (2,0) → term; o_double (1,1) → K at size 2 = W·D.
NOTE (no finding): predecessor's summary said 571 shapes / 422 fence
edges; its exact enumeration bounds aren't pinned in its 20-line
report. My model is broader and its m = 1 sector matches exactly
(39 = 39, the load-bearing sector for (SCS)/K); a clean pass on the
broader census subsumes the narrower one.

## B. Agreement check (ii) derivation: HOLDS

Rebuilt independently. (1) BLOCK TYPING verbatim at the (iv) display
(8144–45: "K_e(q)_{(s,α),(s′,β)} := Σ_{m: s→s′} Σ_{o continuing}");
the solve is square on the block-e state list (S.0's typing), and
(D4) (8319–20) lands continuing targets in JREF^src(s′) — so a
K-column outcome has a member IN block e. (2) PER-MEMBER DEGREE LAW,
full roster: DEG-CONS display (8387–91) derives it from "M1's degree
identity applied to the cell's residual-factor degrees" — STATUS-BLIND
data (my census confirms: size arithmetic identical across all 2^m
status vectors) — and V.6.1 EXECUTES it on the all-halted rows
("m_H3: 3 children (1,1,1), Σ = 3 ≤ 3 ✓; m_H12: (1,2) ✓", 8825–26),
grounding K-TRI's "halted members included". Arithmetic: m ≥ 2, each
e_j ≥ 1, Σ ≤ e ⟹ e_j ≤ e − (m−1) ≤ e − 1 < e. So no m ≥ 2 outcome
has a block-e member ⟹ K-columns have m = 1, c = 1 — pass 6's missing
premise, now definitional AND consistent. Converse direction (bucket →
column exists) rides (SCS) + (D4)'s continuing-outcome coverage, both
in the consumed ledger; the text displays the dependence ("Without
(SCS) the (c = 1, m = 1) row would name a ... column that need not
exist"). Partition of {(m,c)}: checked by hand and by census. Closed.

## C. Own-emphasis sweep: CLEAN

(i) Consumer sync: S.0 K_e gloss (11657), b^term,fin (11681–91,
multi-member licitness displayed with m_H3/m_H12 instances), b^split
(11693), S.4 parenthetical (12183), S.6 bracket (12277) — all cite the
(m, c) rows; no consumer routes by roster letter. (ii) Stale-trichotomy
grep across MOVES + notes/ + docs/: survivors only in pass records and
the (K-SUB) bracketed refutation note (historical, marked REFUTED);
11620's "trichotomy" is (CUT-WD)'s unrelated node trichotomy. (iii) The
c-axis sourcing is honest: the roster letter is binary (c = 0 vs c ≥ 1
— m_H3 TERMINAL 8795, m_2+1 CONTINUING 8798), and routing needs ONLY
that binary + m (exact c ≥ 2 values never used) — no over-claim.
W1 (WATCH, display nicety): check (ii) states columns ⊆ bucket; the
bucket ⊆ columns direction is present but distributed ((SCS) sentence
+ (D4) cite) — a one-line "and conversely" would close it verbatim.

## Verdict

The rev-6 repair is GENUINE: the (m, c) dispatch is a displayed
definition whose routing is exhaustive/exclusive by construction and
verified exhaustively on a 9494-outcome census with the pass-6 class
explicitly present (638 outcomes, 0 misroutes); the K-column m = 1
property is DERIVED (block typing + status-blind full-roster degree
law), not assumed; (SCS) runs as verified; consumers synced. Counts:
0 critical, 0 gaps, 1 WATCH (W1 converse-direction display). CLEAN.
