# FABLE CONFIRMING VERIFICATION of §C rev 14 (live text from '## §C REV 2', MOVES_2026-07-24.md)

Verifier: Fable (fresh instance; second half of the dual bar — independent of
Codex passes 14–16 and of the predecessor Fable pass recorded in
FABLE_VERIFY_C_2026-07-26.md). Date: 2026-07-27.
Method: quote verbatim; CRITICAL vs GAP; fix nothing.

## 1. Repair audit against predecessor Findings 1–5

F1 (SAE) — GENUINE. C.0 now displays the third condition: "(SAE) SPAN-ENTRY
INEQUALITY [rev 12 — the third condition]: the read side lies strictly above
the old box line at every span slot below the window vertex" (~3523), with
the single-endpoint reduction and the adjacent vertex-tie displayed, and
realizability = "the THREE side conditions" (~3511). Both circular sources
are replaced: DOM(2) now reads "[source: C.0's (SAE) — realizability; rev
12. The former source 'D.8's box' was CIRCULAR" (~3677); C.1(i)(α): "THE
LINE COMPARISON IS (SAE) ... supersedes the rev-10 endpoint chain ...
CIRCULAR for empty strata" (~3878); the non-adjacent hinge bullet: "((SAE),
realizability [rev 12 — the former source '(BOX) strict' was the same
circular f-citation" (~3957). F-EMPTY sits in C.0 as the independence REMARK
(62500 predicted vs 0 actual, ~3551). Arithmetic re-run: sec. 2 below.
F2 (node tuple) — GENUINE. The full tuple is displayed at C.0 (~3443–3465):
species; (e, h, g, μ) + anchor a; s₀', j*, w', stride positions p_j, SIDE
HEIGHT u* (adjacent: vertex-anchored); digit tuple (d_j); ψ_i; lift t_i.
DERIVED list adds γ_i and m̂_i [rev 13] with the Bézout pair renamed
(s^B, t^B) [rev 14] — the pass-15 t_i collision is really gone (the lift
t_i and t^B_i now distinct symbols; disambiguation sentence at ~3474–3481).
F3 (crossing-slot chain) — GENUINE. C.1.5(2) now: "indices ≥ j×D_{i+1} ≥
w'D_{i+1} ≥ μ_{i+1}D_{i+2} ... the chain is WEAK throughout — equality at
the adjacent s₀' = 0 boundary" (~4056–4060); each weak step checks: j× ≥
j* ≥ w' (span position; j* = s₀'+w'), and DOM(3) gives μ_{i+1}D_{i+2} ≤
w'D_{i+1}. Conclusion (future-rim leads) intact.
F4 (admissible Z) — GENUINE. C.2: "SOLVES FOR coordinates that are FREE on
Σ_k's locus — i.e. NOT among its determined coordinates" (~4077–4079). The
ambiguous "free-coordinate complement" is gone; the determined-set display
uses the species-correct tops [rev 13, pass-14 F3] consistent with (ZC-a).
F5 ((ZC-a) downset) — GENUINE. (ZC-a) now: "SPECIES-CORRECT TOPS ...
inclusive, zeros at ht ≤ F_i(b)" at (BOX)-type interior indices, "EXCLUSIVE,
zeros at ht < F_i(b) only" at value-carrying rim indices whose ht = F_i
level sets belong to DIG_i (~4004–4014). No consumer contradiction remains:
Z_i ∪ DIG_i is now consistent at the rim by the displayed formula itself.

## 2. (SAE) re-run: certified F-EMPTY vs the LIVE predicate; new empty-stratum search

Script /tmp/fable_confirm_rev14.py (2·10⁶ root-stratum members, seed
20260727; independent of the predecessor's /tmp/fable_c_check.py).
F-EMPTY RE-RUN: config B = the certified instance (old = (3,2,1,0),
side [0,2], (e,h) = (1,3), new = (7,4,1,−2)). Live predicate: non-adjacent
(j* = 2 < μ₀ = 3), so (SAE) ⟺ new(j*) > old(j*) ⟺ 1 > 1 — FAILS. The
history is now EXCLUDED from Theorem C's quantifier; brute force confirms
full stratum = 0 (nominal would be 15625 of 2M). Finding 1's instance is
closed by the live text, not merely narrated.
NEW EMPTY-STRATUM SEARCH: 8 configs against the root-recentering frame,
live predicate computed from data, stratum counted by brute force:
  REALIZABLE: A (e=2, h=5, side [0,2], u*=2 — STRETCH, half-integer
  heights), D (adjacent h=2), E (predecessor's node1, anchor), F (e=1,
  h=4, deep strips, m*=12), H (e=2, h=7, m*=10): ALL nonempty with mass
  = 2^{−m*} exactly (z = +0.78, −0.02, +1.57, +2.39, +1.22 — max |z|
  2.39 across 8 tests, unremarkable).
  EXCLUDED: B (F-EMPTY, (SAE)-fail), C ((NA)-tie: new(3) = 0 = old(3)),
  G (e=2 (SAE)-tie at the endpoint, nominal 2⁻² — would predict 500000
  members): ALL exactly 0.
So (i) I could NOT construct an (NA)+(HV)+(SAE)-passing history with an
empty stratum (two configs at the uncensused e=2 stretch species tried);
(ii) the live claim "failing any of the three ⇒ EMPTY joint stratum" is
confirmed at three distinct failure species, including a NEW dramatic
instance (config G: 500000 predicted by the pre-rev-12 text, 0 actual).

## 3. TRANSITION-ADMISSIBLE quantifier sweep

Every consumer of the data conditions located and its hypothesis checked:
- DOM: statement quantifies "For every realizable prefix (ν₀, …, ν_i)";
  the step at read ν_{i+1} proves the (i+1)-instance, whose own hypothesis
  (prefix through ν_{i+1} realizable) supplies (SAE)/(NA) AT ν_{i+1}.
  Complete without a separate transition clause. LST: "any realizable
  prefix"; consumes the conditions only through DOM at (ii). Complete.
- C.1: "realizable (C.0) and ... ν_{i+1} be any TRANSITION-ADMISSIBLE
  read" (~3842–3846) — (i)'s (α)/(β) cite (SAE), (γ) cites (NA), hinge
  cites (HV)/(SAE): all covered by the hypothesis. Complete.
- C.1.0(b)(iii): "hypothesis [rev 13 ...]: every later read
  TRANSITION-ADMISSIBLE, C.0 — the clause consumes (SAE) via DOM(2)"
  (~3623). Complete ((b)(i)/(ii)/(a)/(c) consume no data condition —
  (b)(ii)'s width bound is ψ-divisibility of pattern data).
- C.1.5: prefix (ZC) + realizable + "ν_{i+1} be a TRANSITION-ADMISSIBLE
  read" (~4024–4031). Complete.
- Theorem C: quantifies over REALIZABLE H; C.0's realizability is
  per-read ("at every read ν_{i+1} (i ≥ 0)"), so each appended read of H
  is transition-admissible for its prefix — C.1.5's hypothesis discharges
  at every induction step. Complete. C.2's admissibility: inside Theorem
  C's hypothesis. C.3 COVERED: classifier output satisfies all three
  (fence item 5). C.0.5/TYP: consume none. NO consumer found lacking the
  hypothesis; no hypothesis found weaker than its proof's consumption.

## 4. End-to-end conditional-mass trace (my own configuration; no record has it)

History (n = 4, p = 2): ν₀ = root RECENTERING (ψ₀ = z+1, all-ones
pattern, Φ₁ = x+2; landing box old = (3,2,1,0) — sanity 0/2M);
ν₁ = NON-ADJACENT e = 2 INCREMENT (side [0,2], h₁ = 5, u* = 2, new =
(7, 9/2, 2, −1/2); slot 1 OFF-LATTICE; (NA): −1/2 < 0; (SAE): 2 > 1;
m* = 7: strips 4,5,6 + dig(B₀,7)=1; zeros 3,4 at slot 1; dig(B₂,2)=1);
ψ₁ = z+1, Φ₂ = Φ₁² + 32, κ₁ = 5/2 (half-integer!), frame-2 box (7, 2);
ν₂ = ADJACENT tail (side [0,1], h₂ = 6 > 5 (I-aug), new₂ = (8,2); fresh:
strip zero dig(c01,5) = 0 at ht 7.5, value dig(c00,8) = 1 at ht 8 —
L₈(C₀) = {(c00,8)} alone, since 8 − 5/2 ∉ ℤ; m* = 2; (HV): lead =
vtx(ν₁) = 1). The combination recentering → non-adjacent STRETCH →
adjacent tail is in no record (predecessor: e=1, g=2; C15 S5: adjacent
chains; Case-L: mid-chain recentering).
RESULTS: P(ν₁|ν₀) = 0.0078610 vs 2⁻⁷ = 0.0078125 (z = +0.78);
inherited-floor + vertex-transport falsifiers (v(c00) ≥ 8 — floor 7 at
integer ht; v(c01) ≥ 5 — floor via κ₁ = 5/2; v(c10) = 2 with digit
= vtx(ν₁) = 1): 0 violations of 15722; P(ν₂|ν₁) = 0.24825 vs 1/4
(z = −0.51); joint 1.95·10⁻³ = 2⁻⁹ exactly; the coordinate one level
above the fresh value digit is free (rate 0.5001). The (ZC) mass
recursion, DOM's floor at half-integer κ, LST's level-set selection, and
the vtx transport are EXACT at this fresh census point.

## 5. Fresh sweep — my emphasis: the (s^B, t^B)/vtx/m̂ exponent arithmetic
   against §B2-DEF's displays, and the eight-item fence

- γ_i := e_i·u*_i + j*_i·h_i: internal identity checked (new(j) = u* +
  (j*−j)·h/e ⇒ e·new(j) + j·h = e·u* + j*·h at every side slot — constant,
  the side's total weight); matches (S5)'s stride argument p_j(γ) =
  (j − t·γ)/e (line ~1970) with γ = the slot's total weight. CLEAN.
- m̂_i := −t^B_i·h_i·g_i: verbatim against D.5's display (line ~2283:
  "R(Φ̂) = z^{m̂}·ψ(z), m̂ := −t·h·g"); Bézout form e·s + h·t = 1 matches
  (lines ~1911, ~2418). CLEAN.
- vtx(ν_i) vs D.8's pinned digit (line ~2483: dig'(B_μ) =
  z̄^{−μm̂}·((R(f)/ψ^μ) mod ψ)): with R(f) = z^{a}·R_anch (the anchor
  a = ord_z R(f), C.0's ANCHORING field), (R(f)/ψ^μ) mod ψ =
  z̄^{a}·((R_anch/ψ^μ) mod ψ) — C.0's extra z̄^{a_i} factor is exactly
  right, and my trace's vtx(ν₁) = 1 prediction was exact (0/15722). CLEAN.
- NIT (verdict-neutral, wording): C.0 says "the Bézout convention
  e_i·s^B_i + h_i·t^B_i = 1 forces s^B_i = 1, t^B_i = 0 (exactly D.5's
  e = 1 base case P2)". The EQUATION alone forces nothing at e = 1
  ((s, t) = (1 − h·k, k) all solve it); what fixes the pair is P2's t = 0
  convention at e = 1 stages ((S5) ~1968, base display ~2018) — which the
  sentence itself cites in the parenthetical. Content and source correct;
  the connective "forces" misattributes. No downstream damage (m̂ is
  computed from D.5's FIXED pair everywhere).
- FENCE (items 1–8): each verified live: (1) u* field ~3450; (2) DOM's
  old(j) as the data line ~3663; (3) exclusive rim tops ~4004; (4) C.2
  admissibility re-worded ~4077; (5) C.3's (SAE)-on-classifier-output
  clause; (6) β-strict "new(s₀') > old(s₀')" ~3893 — justified: w' ≥ 1
  forces s₀' < μ_i, so s₀' is an (SAE) span slot; (7) C.1.0(b)(iii)'s
  hypothesis ~3623; (8) C.1.5's weak chain ~4056 (each weak step checked:
  j× ≥ j* ≥ w' and DOM(3)). No further undeclared meaning change found in
  my read of the full body.
- Species-correct downsets vs DIG (predecessor F5's substance): (ZC-a)'s
  exclusive rim tops make Z_i ∪ DIG_i consistent by display; C.2's
  determined-set formula now matches (ZC-a) exactly; my trace exercised
  the rim value level set (c10 at ht 2 = F at the vertex block) against
  the interior inclusive top (c00 ≤ 7, c01 ht ≤ 7 ⟹ l ≤ 4.5): 0/15722.

## 6. Verdict

Verified text: MOVES_2026-07-24.md lines 3398–4160 (§C REV 2 body, rev-14
state; md5 of the slice d2287469b6bdc3738238a2fad994d9d7).
- Predecessor Findings 1–5: all five repairs GENUINE (sec. 1), with
  Finding 1 re-certified live: F-EMPTY now fails (SAE) and is excluded;
  its stratum confirmed empty (sec. 2).
- New adversarial search (incl. the uncensused e = 2 stretch species):
  NO realizable-with-empty-stratum instance found; the three-condition
  predicate matched brute-force emptiness on all 8 configs (sec. 2).
- TRANSITION-ADMISSIBLE: quantifier-complete across all consumers (sec. 3).
- End-to-end trace (recentering → non-adjacent e=2 increment →
  adjacent read; no record has it): exact at every step (sec. 4).
- Fresh sweep (exponent arithmetic, fence): clean; 1 verdict-neutral
  wording NIT recorded (sec. 5 — "forces" vs P2, source cited inline).
COUNTS: 0 critical, 0 justification gaps, 1 nit.
VERDICT: CLEAN.
