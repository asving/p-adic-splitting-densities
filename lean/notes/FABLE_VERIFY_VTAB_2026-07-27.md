# FABLE FRESH-INSTANCE VERIFICATION — §V-TABLES rev 7 (2026-07-27)

Verifier: fresh Fable instance (dual bar; Codex half accepted at passes 6+7 clean).
Text: lean/notes/MOVES_2026-07-24.md §V-TABLES (lines ~7753–8993) + pass records.
Duties: (a) quote-and-classify sweep; (b) independent (U-A) re-derivation + break
attempt; (c) own-q table check (q outside the census list); (d) independent gate-B
dyadic recomputation; (e) fresh-emphasis sweep. Nothing fixed. Scripts: /tmp/
fable_vtab_ownq.py, /tmp/fable_vtab_gateB.py (own constructions, no reuse of
case_vn3_gate.py).

## (b) (U-A) re-derivation and break attempt — HELD

Re-derivation (independent, from the accepted §C text): C.1.5(1) gives the one-step
conditional mass as vol_nom(E_fresh); C.1 rev 9 defines E_fresh by pure ht-geometry
("no pin membership enters the selection"), so the clause skeleton is a function of
(floor F_i, species, height point) only; C.1.5's proof cuts each fresh strip by p^-1;
TYP(b)'s kernel-coset sentence ("an additive surjection onto its image has equal-size
fibers") makes every value clause cut (alphabet)^-1 with the SAME alphabet for every
emitted value in the image. Hence at ONE fixed realizable (ZC) prefix and one
transition-admissible read shape, every fresh assignment carries the common mass
q^-#strips · ∏(alphabet)^-1 — exactly (U-A). Corollary status CONFIRMED.
Break vectors attempted (all blocked):
 β1 value outside the image (cut 0 ≠ alphabet^-1): blocked — fresh digit cells are
   alphabet-valued by D.11's convention (TYP(b): |alphabet| = |piece|), and (U-A)
   quantifies over transition-admissible reads only;
 β2 inventory-equal pair, different clause skeleton at one prefix: impossible —
   skeleton is a function of (F_i, m, h), never of pinned values;
 β3 value-dependent alphabet: alphabet = piece image at δ', frame data, fixed history;
 β4 value-dependent strip count: floor is prefix node data, fixed;
 β5 zero digit vs nonzero digit (w = 0 encodes v(h₁) > λ — a strip-flavored value):
   the level-λ digit pin is one alphabet factor regardless of value; NUMERIC census
   (gate-B boxes, own code): o_double cell (u,w)=(1,0) vs o_inert cell (1,1), per
   history: 8 = 8 (N=3) and 64 = 64 (N=4) — masses EQUAL, break FAILED;
 β6 cross-history inventory-equal pair: masses could differ — but that is exactly
   (u-R), correctly HYPOTHESIZED in (XHD-u), not claimed by (U-A). No overreach found.

## (c) Own-q table verification — EXACT at q = 16 and q = 25

Both q outside the census list; q = 16 exercises char 2 at a non-prime q (the char-2
conventions), q = 25 an odd non-prime. Exhaustive enumeration, own GF implementation:
 A1 root block (all five closed forms + PART-1 sum = q³): q=16: 560/1920/1360/240/16;
   q=25: 2300/7500/5200/600/25 — ALL EXACT vs the displayed closed forms;
 B-step m₂ (split/inert/double): q=16: 105/120/15; q=25: 276/300/24 — EXACT, and the
   char-2 recounts coincide with the odd-q polynomials as displayed;
 A2 fiber constancy: every fiber of (u₀,u₂) ↦ −u₀/u₂ has size exactly q−1, image
   F_qˣ, T = (q−1)² — EXACT at both q.
Also rechecked: all 99 displayed nine-q grid integers match the closed forms.

## (d) Gate B dyadic chain — independent recomputation, EXACT

Own construction: brute unique coprime factorization f = (z²+h₁z+h₀)(z+l₀) over
Z/2^N per entrance class, class 2 recentered z ↦ z+1. Results: entrances 64+64 at
N=3 (ι = 128/512 = 1/4 = 2·2^-3, I^ent(2) = 2, A(ε) = 3 ✓); o_double cell at λ=1:
T(2) = 1 (cell (1,0) unique), E(h₁) = 3 re-derived (2 pins on h₀ + 1 on h₁), g = 1/8;
μ̂ = 1/32; marked pairs 16 (N=3, 8+8) and 128 (N=4, 64+64); marked-history count 2;
box-precision PASS (mod-8 projection of N=4 solutions = N=3 set, zero event-word
changes). Matches the seal and results/case_vn3_results.json (GateB 16:[8,8],
128:[64,64]) exactly. A2 weight formula E = (3(h₀+h₂)−1)/2 re-derived from the pin
census (E = 7 at (4,1); 32 = 2¹²·2⁻⁷ ✓); the A2 height domain L((4,1);{(3,1),(2,0)})
verified a BIJECTIVE parametrization of {h₂≥1, h₀>3h₂, h₀−h₂ odd}.

## (a)+(e) Sweep findings — 0 critical, 0 gaps; 2 observations (not counted)

Fresh-emphasis checks, all clean: every displayed degree bound holds (A1 deg ≤ 3,
A2 deg 2, s_blk2 deg ≤ 2 with |β₀| = q−1 ≤ W_state = 1; I^ent deg 2 ≤ W_ent = 3);
W_ent height-freeness consistent with (ENT-U)'s per-linear-set constancy being a
separate hypothesis; the ε̊/instantiation bijection double-counts nothing at gate B
(H(ε̊) = {()}); PART-2's n=3 zero-surplus argument re-verified (2+2 > 3); the
absorbing-column (terminal-final) extension type-checks at every consuming site
(K_e sums "o continuing" only; columns enter PART-2, b_e handover, probe step 2);
the [3t] fence intact (no [3t] theorem consumed; VP labels only; §T-ASSEMBLY status
line current vs the EOF record) and the [2a] fence intact ((i) + (iv)-PART carry the
pending SP-FIN/SP-OUT/SP-COMP inheritance; V.5(6)); pass-record chain coherent
(VTAB_PASS4 file exists, 0c/2g record gaps — matches the acceptance summary).
 OBS-1 (cosmetic): INIT-RAT's display (V.3(iii)) writes "Σ_{h ∈ c} p^{−A(ε̊[h])}"
   inside a ℚ(q)-membership conclusion; the intended interpolating form is q^{−A}
   (as gate B's own "ι(q) = q(q−1)·q^{−3}" reads), with p the evaluation. Meaning
   unambiguous under XHD-w's displayed q^{−E} = C.1.5-ratio identification.
 OBS-2 (cosmetic): the terminal-final template extension is displayed inside clause
   (v) but consumed by (vi)-typed events (the probe's COMP-h layer); the rev-4 record
   calls it "the (v)/(vi) signature" — a cross-reference asymmetry only.

## VERDICT

CLEAN — 0 critical, 0 justification gaps (2 cosmetic observations, non-blocking).
The (U-A) break attempt failed on all six vectors incl. a numeric two-cell census;
own-q tables exact at q = 16 and q = 25; gate B's dyadic chain reproduced exactly on
an independent construction. Fable half of the dual bar: ACCEPT on the rev-7 text,
under the note's own displayed perimeter (XHD/(XHD-u)/(ENT-U) owner [2b], HMC open
kernel probe-not-run, ENT-COUNT/INIT-RAT burdens, [2a] pending inheritance, the
[3t] fence, VALUE-Fq/VALUE-p standing).
