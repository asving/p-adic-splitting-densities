# GENH4 RATIFICATION — ORCHESTRATOR PRE-VERDICT SCAFFOLD (written and committed BEFORE reading any Codex output)

Session of record: `019fe500-0ddc-7b52-9e32-c4dff01e560c` (gpt-5.6-sol, effort
high, read-only, launched ~04:50 UTC 2026-08-09; log
`/tmp/codex_genh4rat_stdin_1786253413.log`). Disclosed: a first launch
(019fe4fd-eb34) came up sandbox=workspace-write from the project trust config
and was killed ~2 min in, before any output; relaunched with explicit
`--sandbox read-only`. Brief: `genh4rat_brief_2026-08-09.txt` @ 57c9811
(128,625 chars, no trims).

This key records what I independently verified and what I predict, per the
brief's five attack surfaces, so the decorrelation record in the fold is
honest (the HE7 precedent).

## P-1 (GENH4.A census algebra, E/F seam): predicted CLEAN

Hand-verified before the run:

- **Full mass-conservation ledger at (q,N,k) = (2,7,1), genre F, empty
  history**, entry volume per ψ = 2^{4N−10k−4} = 16,384; slot strings A₁ m ∈
  [3,7] (comp 2,2,2,2,1 = 9), A₀ m ∈ [5,7] (comp 2,2,1 = 5), total 14 ✓ the
  entry exponent. Leaves: RAM(5) = (q²−1)·2^{12} = 12,288; RAM(7) =
  (q−1)·2⁷ = 128 (boundary-band pin, comp 1 — the [r2] clause, matches
  committed); 2SIDED(3,4) = 3·1·2⁷ = 384 (A₁ pin comp 2, A₀ pin at 7 comp 1;
  matches committed); SPLITEQ(3) = 3·2⁸ = 768, INERT(3) = 6·2⁸ = 1,536 (F₄
  censuses 3/6; both residual slots at heights 3, 6 ≤ N−1, always full-comp —
  a derived invariant the note does not display but honors); SPLTAIL(3) =
  3·2⁷ = 384 (matches committed); UND = 2⁷ = 128 (odd-N single power,
  matches committed); refine children 3·2⁸ = 768 (floored node {>3, >6}).
  Σ = 12,288+128+384+768+1,536+384+128+768 = 16,384 ✓ EXACT.
- RAM(5) @ (7,5,1): 21·6·7⁵ = 2,117,682 ✓ recomputed; free-slot exponent
  comp(3)+comp(4)+comp(5) = 2+2+1 = 5 ✓.
- The RAM(N) census q−1 = the in-window a₁-digit at position N−k ≠ 0; the
  complementary a₁ = 0 states are exactly the SPLTAIL/UND states — no
  overlap, no gap. A tie at m = N (out-of-window a₀ digit) cannot lower the
  value (res(a₁)ȳ ∉ F_q — GENH4-2(F)); value stable, residual not consulted
  at odd N. Consistent.

Weak corner flagged: the note never says explicitly that SPLITEQ/INERT
residual slots always sit below the boundary band (they do: readable needs
2dμ ≤ N−1); if Codex files anything on surface (1) I expect it there or on
the S6.1 gloss wording.

## P-2 (σ-labelling supply): predicted CLEAN with a possible GAP/MINOR at one site

Re-derived all six S7 bullets: RAM-E (u/4 with u odd ⟹ 4|e(L), forced
irreducible); RAM-F (2|e, 2|f, ef = 4); 2SIDED norm j = 2 (jw + (4−j)(u−w) =
2u ⟹ j(2w−u) = 2(2w−u), j = 2; the ANNEX A2 unit fix is right); the E-side
no-linear-factor step (v = h/2 ∉ ℤ) and the F-side parity-of-f step (F_{q²} ⊆
k_L kills both linear and cubic factors — 2 ∤ 3); SPLITEQ's one-refine-step
(R₂′(s₁) = s₁−s₂, char-2 = S₁ ≠ 0 by '11' separability ✓, and the new state
is per-lift 2SIDED for every lift incl. u′ = ∞ corner); INERT residue-degree
step; SPLTAIL-E; SPLTAIL-F = GENH4-7(b). The dictionary covers every decided
leaf class, and the supply matches W-12.D (A1) [r4]'s σ-labelling clause
quantifier (every disc ≠ 0 lift of every member) — the W-12 firing-table
n = 4 row's own ruling.

**My one candidate finding on this surface (pre-registered):** S7 cites
"(GENH4-2)" for v(A₁(θ)) = w/2, v(A₀(θ)) = u/2 at the QUARTIC's roots θ,
but LEMMA GENH4-2 is stated at roots of the KEY. The proof transfers (the
parity/independence argument needs only v(θ) = h/2 resp. res(θπ^{−k}) a root
of ψ — exactly the "two facts" S7 opens with), so content survives; the
citation is an overreach as displayed. Expected grade if found: MINOR
(possibly GAP if the verifier reads GENH4-2 strictly).

## P-3 (level-0 assembly): predicted CLEAN

- Census sum Σ = q⁴ verified BY HAND at q = 2 (0+1+0+4+3+0+2+1+2+2+1 = 16)
  and q = 3 (0+9+3+24+18+3+9+3+6+3+3 = 81), n₂ = (q²−q)/2, n₃ = (q³−q)/3,
  n₄ = (q⁴−q²)/4.
- The 11 shapes exhaust quartic factorization patterns over F_q (checked by
  partition enumeration); disjoint by definition of f̄, so no
  (2,2)-vs-(1,1,2) double count is possible at level 0 — the only way to
  double-count would be assigning one shape two block products, and each
  shape has exactly one product line.
- R_{(2,1)²} anchor: q²/(2(q+1)²Φ₂) at q = 2 = 4/126 = 2/63 ✓ matches; the
  2·2-shape term C(q,2)/q⁴·(q/(q+1))² = 1/36 at q = 2 leaves 1/252 = (1/8)·
  ν₄({(2,1)²}) for the 4-shape — structurally coherent (ν₄ not re-derivable
  by hand here; the engine tie carries it).
- μ_E re-derived from the A3 closed forms: RAM q²/Φ₂, 2SIDED 1/Φ₂, even-dμ
  q/Φ₂ split (q−2)/(2Φ₂) + q/(2Φ₂) + 1/Φ₂; aggregation ×Φ₂/(q²+q) gives
  exactly ( q/(q+1), 1/(2(q+1)), 1/(2(q+1)) ) ✓.

## P-4 (GENH4-7(c) two-lift witness): predicted CLEAN, one possible MINOR

Both lifts re-derived: u_lift = N via the free out-of-window a₀ digit at
position N (N ≤ 2w by hypothesis, so trichotomy leg (b) at odd N gives
RAM(N) → {(2,2)}); u_lift > 2w via zeroing out-of-window digits up to 2w and
freeing one above (positions ≥ N are all free — 2w ≥ N makes every height in
(2w, ∞) reachable), or A₀ = 0 → the corner → {(1,2),(1,2)}. Same in-window
state ✓; different σ ✓. Possible MINOR: the proof text does not explicitly
secure disc ≠ 0 on the two exhibited witnesses (generic deep digits do it;
"different deep lifts realize different residual classes" gestures at it).

## P-5 (free hunt): my own candidates, pre-registered

1. S6.3's genre-E "#A₁ ≥ N = ⌊(N+h)/2⌋ + ⌊N/2⌋ − … = N + (h−1)/2" — the
   "− …" ellipsis compresses the parity bookkeeping. I verified the closed
   form N + (h−1)/2 at both parities of N (h odd), so content is right;
   display sloppiness at most MINOR.
2. GENH4.B genre-F display "q^{2⌊N/2⌋+2k−1} + 1_{2|N}(q−1)q^{N+2k−1}" vs
   S6.3's factors: tied at (2,7,1) → 128 and (2,8,1) → 512+512 ✓ both. CLEAN.
3. The (Zp,2,11,h5) P-3 spot value: recomputed the full slot strings (A₀ even
   string EMPTY at 22 > 2N−2 = 20; 3 odd A₀ slots; 13 A₁ slots; RAM(21) free
   = 2+13 = 15 → 2^{15}) ✓ the committed half-drain row is law-consistent.
4. SPLITEQ decided leaf consumed by a refine-machinery step stated for '1sq'
   (S5) — S7 discloses "(the kill needs only R₂(s₁) = 0)"; MINOR at most.
5. S8's in-vitro cascade scoping and GENH4-6 liveness: inequalities re-checked
   at boundary (dμ = 2h+1, position (h+1)/2 ≥ (h+1)/2 ✓; F: dμ−k ≥ k+1 ⟺
   dμ ≥ 2k+1 ✓). CLEAN expected.
6. Stack-staleness surfaces (S10-BOX-1): as-of by standing disclosure; not
   findings.

## Predicted overall outcome

RATIFIED or RATIFIED-WITH-ANNEX (findings display-level at most; no frozen
number, no committed key, no density expected to move). The strongest
candidate for a Codex GAP is the GENH4-2-at-quartic-roots citation (P-2) or
some unit/parity slip I haven't found in the S6.1 X-exponent table (the one
surface I could NOT exhaustively re-derive by hand — only spot-checked at
(2,7,1), (7,5,1), (2,11,h5)).
