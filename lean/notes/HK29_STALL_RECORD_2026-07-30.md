# HK-29 — countermodel attempt STALLED, statement survives (2026-07-30)

UNIT: BP2 Block Z, HK-29 (`BRIDGE_BP2_HC2K1_2026-07-30.md` §Block Z) — search for a
coherent+realizable straddle against `HC2/U4_freshCover.levelSet_no_straddle`
(the N-6 option-(i) lemma; sorried, consumed by `mkFresh_cover`'s roster goal).
VERDICT: **STALLED — STATEMENT SURVIVES**, with the exact blocking clauses named
below, a machine probe (`verification/hk29_straddle_probe.py`, sealed predictions,
exit 0), and a WAVE-INVARIANCE argument that settles the gate for BOTH the current
and every candidate post-HK-06 semantics despite the HK-06 dep being unlanded.

## 0. Dependency disclosure (HK-06 pending) and why the verdict stands anyway

HK-29's spec says "against the POST-REPAIR semantics, deps: HK-06". As of this run
the wave has NOT landed (`MovesC/Defs.lean:634` is OLD-keyed; no `RegradeOf` in
tree). The finding-15 worry (pre-wave Block-Z searches are spuriously empty) applies
to searches that quantify over the transition-CORE clauses. This search does not:
the straddle geometry is governed entirely by clauses the HK-06 diff does not touch
(§1), and the probed class is a SUPERSET of the line data of every OLD-coherent AND
every candidate post-repair-coherent realizable history (RG-1/RG-2/E-a alike — the
wave only rewrites the IsNodeLift/TransitionCoreL/s-t-tie leg and `StageTransHyp`;
the §3.4/HK-31 blueprint route itself cites containment + width chain as surviving
coherence clauses). Emptiness over the superset settles the gate wave-independently.

## 1. The blocking clauses (the deliverable): why no straddle can exist

Notation per `MovesC/Defs.lean`: node m carries (e,h,g,μ,s0,w:=wSide,D:=Dwidth,line);
cw_m := e_m·g_m·D_m; STR_m = ∏_{r<m} e_r; staircase_m(b) = line_m.at((b/cw_m)·cw_m)
for b < μ_m·cw_m else ⊥; floorH_i(b) = max_{r<i} staircase_r(b); slotVal_i(j) =
line_i.at(j·D_i); window W_j = [j·D_i, (j+1)·D_i); prevRim(i) = μ_{i−1}·cw_{i−1};
Line.at(b) = intercept − slope·b.

Clauses used — ALL HK-06-invariant:
- (C1) root degree 1 ⇒ D_0 = 1 (coherence conj. 1 + `Node.hDwidth`);
- (C2) slope law slope_m·(e_m·STR_m·D_m) = h_m (coherence conj. 2) ⇒ slope_m > 0;
- (C5) window containment s0_{m+1}+w_{m+1} ≤ μ_m (coherence conj.-4 tail);
- (C6) width chain D_{m+1} = cw_m (coherence conj.-4 tail);
- (C7) strict slope steepening slope_m < slope_{m+1} (coherence conj.-4 tail);
- (NL) Node laws he/hh/hg/hμ/hcop/hEdvd + the hOrd arithmetic:
  ψ^μ ∥ Ranch ≠ 0 (hOrd, hpat0), deg Ranch = w/e (hRanch+hpatTop), deg ψ = g
  ⇒ **μ·e·g ≤ w** (with hEdvd); also w ≥ e ≥ 1 hence w ≥ 1;
- (SAE) `TransitionAdmissible` clause 3 (strict span-entry) at every consecutive
  pair, via `Realizable` — untouched by HK-06.

Derived chain (target node i ≥ 1, in-band member c at fine slot j):
- (F1) D_m ≥ 1 (C1+C6 induction); slope_m > 0 (C2).
- (F2) D_m ∣ D_{m'} for m ≤ m' (C6).
- (F3) RIM CHAIN: rim_m := μ_m·cw_m satisfies rim_{m+1} = μ_{m+1}e_{m+1}g_{m+1}·D_{m+1}
  ≤ w_{m+1}·D_{m+1} ≤ μ_m·D_{m+1} = rim_m (NL at node m+1, then C5, then C6). So
  rim_{i−1} ≤ rim_r for all r ≤ i−1: **every deeper truncation cliff lies at-or-right
  of prevRim(i) = rim_{i−1} — no ⊥ cliff inside the reachable region.**
- (F4) GRID DOMINANCE: for m+1 ≤ i−1 and x a D_{m+1}-multiple with x < rim_{i−1}:
  line_m.at(x) < line_{m+1}.at(x). Proof: x < rim_{m+1} ≤ w_{m+1}·D_{m+1} and
  x < rim_m = μ_m·D_{m+1}, so j'' := x/D_{m+1} < min(w_{m+1}, μ_m). If j'' ≥ s0_{m+1}:
  SAE cl. 3 directly (j'' is a span slot below μ_m). Else j'' < s0_{m+1}: SAE cl. 3 at
  slot s0_{m+1} (s0 < μ_m since s0+w ≤ μ_m, w ≥ 1) + C7 propagates the strict gap
  LEFTWARD (the steeper line grows faster as b decreases).
- (F5) **FLOOR WINDOW-CONSTANCY** (the sharper invariant): the in-band member forces
  j < μ_{i−1} (rim bound + D_i ≥ 1), hence W_j ⊆ [0, rim_{i−1}) entirely (aligned:
  cw_{i−1} = D_i by C6). For b ∈ W_j: the r = i−1 staircase is CONSTANT
  = line_{i−1}.at(j·D_i) (aligned grid, interior by j < μ_{i−1}); every r ≤ i−2
  staircase is interior (F3), evaluated at a grid point ≥ j·D_i (F2), so
  ≤ line_r.at(j·D_i) (slope > 0) < line_{i−1}.at(j·D_i) by chaining F4 at the fixed
  point j·D_i. Hence **floorH_i ≡ line_{i−1}.at(j·D_i) on the whole window** — the
  deep staircases NEVER contribute to the floor in the reachable region.
- (F6) NO STRADDLE: c' ∈ levelSet(j) has base ∈ W_j and htH = slotVal j. Rim leg:
  W_j ⊆ [0, prevRim) (F5, the corrected §3.4 arithmetic — machine-confirmed, zero
  misalignments). Floor leg: floorH at c'.base = the same constant that c witnessed
  < slotVal j. Height leg: equality. c' is in-band. ∎ (i = 0: floorH = ⊥, trivial.)

Recentering interleavings (the spec's named risk) are covered unchanged: C5/C6/C7 and
SAE are species-unconditional, and recenterings are just the e = g = 1 instances.
The U4-header countermodel skeleton (adversarial floorH increasing in b) is doubly
infeasible: coherent floors are non-increasing per node (slope > 0) and window-constant
(F5).

## 2. Machine probe (sealed before run; exit 0)

`verification/hk29_straddle_probe.py` — exact-rational search over the invariant
clause class (lengths 2–4, all targets i ≥ 1, both straddle legs checked), sealed
predictions P1–P3 in the header. Results 2026-07-30:
- P1 FULL: 3936 accepted configs, **0 straddles** — HOLDS.
- P2 FULL: floor constant on every reachable window; windows rim-aligned (0/0
  violations) — HOLDS (confirms F5 exactly).
- P3 ablations — each dropped clause immediately yields straddles, so the named
  clauses are exactly the blockers: AB-SAE 26 (deep line above the (i−1) staircase at
  the window edge), AB-C5 394 (broken rim chain lets deep variation in), AB-C6 2622
  (misaligned grids + mid-window ⊥ cliffs) — HOLDS.

## 3. Consequences (fence)

- HK-31 stays a PROVER unit; the repair adjudication branch (band-aware levelSet =
  N-6 option (ii), re-opening U3/U5/U6) is NOT triggered; no orchestrator escalation.
- HK-30/HK-31 route UPGRADE: prove F5 (floor window-constancy) instead of per-member
  dominance — the foldr-max induction collapses to (i) the aligned r = i−1 constancy,
  (ii) one strict grid-dominance chain at the window's left edge (F4), (iii) the rim
  chain F3 (whose Lean supply is the hOrd/hRanch degree arithmetic μ·e·g ≤ wSide —
  budget a helper lemma). No SAE clause at node i itself is needed, and NO spanSlot
  hypothesis is needed: the statement as sorried (quantifying over ALL j) is fine.
- The rim leg's corrected §3.4 route (REVISION 2 finding 2) is machine-confirmed.
- Wave-independence: this gate outcome holds under RG-1, RG-2, and E-a alike; the
  compiled Lean proving (HK-30/HK-31) still sequences post-HK-06 for build reasons
  only, not for semantic risk.
