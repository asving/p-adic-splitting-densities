# WELDMASTER pass PE8 — hostile verification report (EIGHTH attempt; the accepting attempt after PE7's clean)

**Target:** `lean/notes/openmath/WELDMASTER_2026-08-08.md` AT HEAD (post-r6,
355a14f; unchanged since r6 — `git diff 355a14f..HEAD` empty on the note,
worktree clean; arc: seal b375f42 → verdict 0baeb3b → PE1 df00707 → r1
90db22d → PE2 1edb104 → r2 8f1c1f2 → PE3 07acb37 → r3 52d40bb → PE4 39e1eec
→ r4 14706f5 → PE5 f97bc78 → r5 f8c2c09 → PE6 7c3893f → r6 355a14f → PE7
0a2fb54 CLEAN, counter 1/2, ledger 93da1d1). **Verifier:** hostile pass PE8,
fresh context, wallclock 2026-08-07. Nothing fixed; offending passages
quoted and classified (CRITICAL ERROR / JUSTIFICATION GAP); fences and
honest boxes read as part of every statement; the stakes (a clean pass
accepts) applied NO softening — the bar identical to every pass. Sources
extracted at their pins via `git show`: [JB] 4c4ee56, [JC] 3870bc8, [JA]
ce0469a, [W2] 5463f2a, [ILN] ced7dbb, [SYN] f71cd68, LED-Λ 2ad7505. All
SEVEN prior reports read (routes catalogued: PE1/PE2 re-ran the note's own
computations + diff checks; PE3 re-derived WM-COB(i)–(iii)+WM-RHO against
[ILN]'s displays; PE4 WM-COB(i) by decomposition + the seed by raw Bézout;
PE5 WM-RHO by the E-pair; PE6 WM-CLASS by the σ-section; PE7 WM-FENCE by
the order-lattice). PE7's four observations adjudicated independently
(all four stand as no-action — §5).

## VERDICT LINE

**0 CRITICAL ERRORS · 1 JUSTIFICATION GAP (F-1) · 0 MINOR. NOT CLEAN — the
acceptance counter RESETS to 0/2.** THE GAP is a false mathematical
identity in the note's own voice, in SEALED text (present at b375f42,
untouched by r1–r6, escaped all seven passes — it is not a quote, so the
quote sweeps never touched it): the S0 setting line declares the harness
Bézout normalization as "ℓ_j h_j − ℓ′_j e_j = ±1 form as pinned (`bez`)",
but the pinned `bez` (and every pinned supplier) normalizes by
**ℓ_j h_j + ℓ′_j e_j = 1**; the displayed minus-form identity is FALSE on
the note's own frozen roster (reads (3,2) and (2,3) give 7 and 5 — towers
C2D/C3C/C3E/I4A/I4B) and contradicts the note's own S0.3 display two lines
below it. Blast radius NIL: no displayed theorem consumes the line (§F-1).
Everything else verified: the r6-state note is otherwise TRUE at HEAD —
THEOREM WELD-M's five faces verified statement-by-statement against the
pinned suppliers (§2), WM-COB/WM-RHO/WM-CLASS/WM-FENCE re-derived by hand,
TWO components re-derived by routes none of PE1–PE7 used (WM-RHO via the
proof-step/shift route at integer level with an independent split,
negative γ included; WM-CLASS via the cyclic-norm-invariant route) —
**20,398 checks / 0 violations, exit 0, all five teeth fired** (§3). The
sealed battery reproduces byte-identically; every figure exact (§1). Arc
accounting consistent and true (§4).

## §1. MACHINE LEGS (mandatory; re-run 2026-08-07)

* **Sealed battery.** Runner md5 `6b406f81c250d25f615f715fa9eff474`
  **intact** at HEAD; engine pins `iterlawn_pe_reimpl.py cae45db2…` /
  `grt_jc_probe.py 03811b69…` intact (= WM-PIN's own values). `git status`
  clean on `verification/` before and after. `python3
  weldmaster_checks.py` → **exit 0, VERDICT: ALL GREEN**; both re-written
  artifacts **byte-identical to the committed ones** (`git diff
  --exit-code` empty on `weldmaster_checks_output.txt` AND
  `weldmaster_checks_results.json`; elapsed 0.6 s reproduced).
* **Figures vs the note's S5 verdict block — EXACT at every figure:**
  WM-PIN 2/0 · WM-EPS 615/0 · WM-COB-I 1,885/0 · WM-COB-OFFW 513/0 ·
  WM-COB-F 1,885/0 · WM-COB-C 897/0 · WM-RHO 87/0 · WM-FENCE-XI 349/0 ·
  WM-FENCE-EQ 171/0 · WM-SHEAR 804/0 (342 multi-vertex) — Σ = 7,208/0 =
  the note's total. Teeth SIGN 374 · DELTA 861 · SHEAR 514 · XI 47, all
  fired. Census: fence rows 22 absolute / 9 slot-only / 26 neither; κ hist
  {0:292, 1:87, 2:18, 3:37, 4:6, 5:9, 6:2, 7:6}; 29 towers; 897 pairs;
  E up to 24 (C4C) and NR ∈ {2,3,4} confirmed from the run itself.
* **Fresh-route leg (this pass's two decorrelated components, §3):**
  `/tmp/wm_pe8/wm_pe8_fresh_legs.py` (md5
  `2eac682cbc11f534d84060030ed3cb43`), full 29-tower roster — **20,398
  checks / 0 violations, exit 0**; teeth T-A1 884 · T-A2 1,140 · T-B1 17 ·
  T-B2 12 · T-B3 6, all fired. Engine files consumed READ-ONLY at their
  pinned md5s (asserted in-script).
* Decorrelated spot-checks of the r6 brackets' byte-claims by my own
  extraction: [ILN] ced7dbb line 360 IS the S2 scope sentence ✓; [JB]
  4c4ee56 line 149 and [SYN] f71cd68 line 131 each carry "A fifth sweep
  would find a sixth site" ✓; runner line 222 is the WM-EPS β-range ✓.

## §2. STATEMENT-LEVEL TRUTH AT HEAD — THEOREM WELD-M's five faces vs the pinned suppliers (charge 2)

Each face-row citation, identification cell, and conditionality cell was
checked against the supplier statement at its pin (my own `git show`
extractions, not the prior reports' transcripts):

* **(M0).** [JA]† JA-PIN at ce0469a: "T(t) satisfies every clause of the
  [ILN]† S0.1 class pin EXCEPT the lift clause" with clause 8 = W-2
  consumption — exactly the face's identification cell; clauses 1–7 forced
  by print hypotheses ✓. [JB]† §0M rows 1–2 at 4c4ee56: row 1 JB-DEV(i)
  "same division, §2(i)"; row 2 the byte clause with (a2) "YES — this IS
  its hypothesis" — the face's "byte clause on `P≤q` only" ✓. W2-C1
  (representative legitimacy, §4 of [W2] at 5463f2a) ✓.
* **(M1).** JA-VAL: "w_m(A) = v_{m+1}(A)" PROVED unconditional on the
  shared-key perimeter ✓. JB-VTX(a)/(b) at the pin: "H(f) = Σ_q(U(f)) with
  Σ_q(i, u) = (i, e_q·u + h_q·i)", vertex-for-vertex via LEMMA JB-AFF ✓;
  the row-11 [r6, F-1] SPLIT carried in the face cell matches the pin's
  own bytes — (d1)/(d2) at `P<q`, (d3) at `P≤q` ("the BYTE-EQUAL CHAIN
  THROUGH q", bites at q = qcap on T3A/T3C/T3D/T3E/I4C) ✓; JB-VTX(d4)
  NO-LEG (row 12 (f) NONE) ✓. JA-GRID(a) with the u ≥ 0 proviso and (c)
  the carry clause = lattice crossing ✓; the narrowed membership residue
  quoted at rows 4/12 col (b) is byte-true at the pin ✓.
* **(M2).** JA-EPS at the pin: ε_m(β) = z_m^{−t_m(β)}, t_m = (ℓ_{m−1}β −
  s(β))/e_{m−1}, SIGN CONVENTION explicit (Prop-`construct` CHILD
  orientation; Def-`t(i)` opposite) — the note's S0 gloss ("NOT
  Def-`t(i)`'s opposite sign") is verbatim-faithful ✓; quantifier "every
  β ∈ ℤ in the level-m weight lattice" ✓ exactly as the [r1, F-4] block
  scopes it, with [ILN]† EXP-KIT(a) ("(s(β) − ℓβ)/e ∈ ℤ and ε(β) =
  z^{(s(β)−ℓβ)/e}", β unrestricted, ACCEPTED) as the off-lattice carrier ✓.
  JA-RES: "c_i = z_{m−1}^{−i·A_{m−1}} · C_i", "the law is UNCONDITIONAL at
  m = 2", per-digit proviso at m ≥ 3 ✓. W2-C2(a)/(b) + (HR-REC) exact,
  scalar on (C-coll) ✓. JA-BOX-1 per-slot-never-scalar inherited ✓.
* **(M3).** [JC]† at 3870bc8: header + W-7 box "OB-3 value (inner =
  ∏_{j≤m}z_j^{D_j}) PROVED general m on [ILN]†'s scored stratum" ✓; W-9
  "COROLLARY W-9. Given W-6, W-7, W-8: (i) c_{m+1} descends …" ✓ (WM-CLASS
  cites W-9(i) correctly); JC-LOC "(B ≅ gr_{K[x]}(w): B *is* the object
  FGMN's theorems speak about)" with B = gr(w)[in(π)^{−1}] ✓ byte-true;
  germ split "val law CONFIRMED on 27 stages; H-D REFUTED 138/669" ✓ =
  S2.3's figures; the §10.2 stack's "(ITER-LAW-LIFT)" residual and
  "§0 ladder + [T] pins" ✓ byte-stable at the pin, mirrored at S4 ✓.
* **(M4).** [W2]† §3.4 at 5463f2a: the displayed closed form ξ_{m+1} =
  χ_m^{γ_{m+1}}·z_m^{−e_m·A_m}, w_{m+1} = χ_m^{−g_m·γ_{m+1}}, c₁ =
  z_m^{−A_m} the Thm-`phir` constant ✓ — byte-identical to the face cell;
  §3.4 rk. 1 confirms the χ-multiplier IS the [ILN]† shift-recursion
  descent operator ("the SAME descent operator as the [ILN]† shift
  recursion S_{j−1} = D_jγ_j + S_j(ℓ′_{j−1} − ℓ_{j−1}w_{j−1}Φ_{j−1})") ✓.
  W2-C3 cited at the pin's own §5.2 statement ✓, at 0/2 with (C-coll)
  scalar fence, §4.3 ℓ-orbit fence, and W2-OPEN-1 OPEN carried ✓ (post-pin
  W2 motion: observation O-2, pin-protected). WM-FENCE(c)'s one-line
  derivation re-checked: ξ_Q at χ_{Q−1} = 1 equals z_{Q−1}^{−e_{Q−1}A_{Q−1}}
  = χ^{(Q−1)}_{e_{Q−1}} ✓.
* **[SYN] f71cd68:** §1.2's junction table = SUBSUMED-PLUS-SHARPENING at
  all four junctions with exactly the face assignments the note carries
  (J-A → M1/M2; J-B → M0/M1; J-C → M3; W-2 → M4) ✓; §1.3's
  organizing-umbrella honesty sentence ✓ ("(M) proves no new instance,
  discharges no open leg"); §2's LAW-1..LAW-4 = the note's four-laws
  block ✓. **LED-Λ 2ad7505:** the header fence quote "it does not edit,
  bracket, or retire them" byte-true ✓.
* **Hand re-derivations (every displayed proof):** WM-COB(i) — the
  three-line computation re-done from SHIFT-(n) (β″ = B + S) + the
  definitional abscissa tie + S0.3's D_j definition; every step integer,
  every sign consistent with the displayed ∂t orientation ✓; (ii) = z_j
  raised to (i) via EXP-KIT(a) ✓; (iii) regroups over j and substitutes
  the value law on its stratum ✓ (footprint ordering as claimed: (i)
  unconditional incl. DCX — [ILN]'s own "Unconditional at every rung and
  on ALL pairs (DCX included)" clause covers the integer layer ✓).
  WM-RHO's proof steps re-derived (§3, LEG A). WM-CLASS's arithmetic
  re-derived incl. the [r1, F-8] κ ≥ 0 warrant (WINDOW-(n) + minimality;
  in-window ⟹ γ ≥ 0 since γ = w_{n+1}(φ_γ) with nonneg generator
  weights, so the scan IS the minimal representative) ✓. WM-FENCE(a)/(b)
  citations byte-true at their pins (incl. the r4 root-inclusive range
  and the r5-restored head quote, re-checked); (c)'s substitution ✓;
  the seed identities' carry-freeness (e_{μ−1} | W_μ) ✓; "A_j = 0 ⟺
  e_{j−1} = 1" ✓ (0 ≤ ℓ < e forces ℓ ≥ 1 at e > 1). S2.3's TC-3 sentence
  at g_m = 1 ✓ (monic degree-1 ψ_m). S6 claims table consistent with the
  body row-by-row ✓.

## §3. FRESH RE-DERIVATIONS — two components by routes unused by all seven prior reports (charge 1)

**Component 1 — LEMMA WM-RHO via the PROOF-STEP (SHIFT) ROUTE.** PE5
derived the RESULT from WM-COB via the E-pair at field level; PE3 checked
it against [ILN]'s displays. Nobody verified the S2.1 proof's own three
internal claims as claims. This pass does, at INTEGER level only (no field
arithmetic), with an INDEPENDENT split implemented from [ILN] ced7dbb
S0.2's displayed recursion (my own `bez` from the pinned + normalization,
my own eq12, my own mirror recursion — engine `Tower.split` enters only as
a one-time spec guard), sampling γ ∈ [−2E, 2E) — NEGATIVE γ included (the
sealed WM-RHO family samples reps[:3] ≥ 0 only):

* (A0) my split == engine split, 1,140/0 (spec-divergence guard);
* (A1) s_j(γ+E) = s_j(γ) for ALL j = 1..n+1 — proof claim 1 — 3,736/0;
* (A2) u_j(γ+E) − u_j(γ) = E_{j−1} (j ≤ n), = E_n at the top — 3,736/0;
* (A3) β_j(γ+E) = β_j(γ) + E_j — proof claim 2 — 2,596/0;
* (A4) t_j(β_j + E_j) − t_j(β_j) = ℓ_{j−1}E_{j−1} — proof claim 3 —
  2,596/0;
* (A5) the exponent vector of E(γ+E)/E(γ) equals (−ℓ_{j−1}E_{j−1})_j
  EXACTLY per level — 2,596/0 — γ-independence at EXPONENT level,
  strictly stronger than the field display.

Hand-verification of the same steps: e_n | E gives s_{n+1} fixed and
u_{n+1} += E/e_n = E_n; e_{j−1} | E_j gives the induction; the t-increment
is ℓ_{j−1}E_j/e_{j−1}. The note's proof is CORRECT step by step. Teeth:
T-A1 (garbled mirror recursion, sign flip on the s·W term) disagrees with
the engine split 884 times; T-A2 (period garbled to E+1) breaks (A1)
1,140 times.

**Component 2 — COROLLARY WM-CLASS via the CYCLIC-NORM-INVARIANT ROUTE.**
PE6 keyed the σ-section identity pointwise on the class-pair grid. This
pass keys the H²(ℤ/E, K^*) NORM INVARIANT at the generator instead — an
aggregate the display must satisfy: from c = z̄^δ·ρ^{−κ}·∂Ẽ,
∏_{k=0}^{E−1} ∂Ẽ(k,1) telescopes to Ẽ(1)^E over the cyclic group, so

    N(c) := ∏_{k=0}^{E−1} c(σk, σ1)  =  Ẽ(1)^E · ∏_k z̄^{δ_k}·ρ^{−κ(k,1)}.

Engine leg: c(σk, σ1) = z̄^δ·∏_j z_j^{D_j} from committed
`Tower.constants`. Fresh legs: MY section σ (minimal in-window
representative computed with MY split), MY κ, MY cochain Ẽ, ρ from the
closed form. Results, all 29 towers: **B3-norm 29/0** (the identity exact
in the top field), **B4 29/0** (N(c)/N(z̄^δρ^{−κ}) is the EXPLICIT E-th
power Ẽ(1)^E — the constructive form of "[c] = [z̄^δ·ρ^{−κ}]"), pointwise
(k,1)-fiber 285/285, **B1: κ integral AND ≥ 0 on ALL E² class pairs**
(3,597/0 — the sealed census samples 4×4 per tower; this is the full
grid), B2 section guard vs `ITL.window_reps` semantics 29/0, all 285
section pairs dint_ok (scored-stratum claim confirmed at the section).
Teeth: T-B1 (δ_k+1 ⟹ ×z̄^E) fires on 17 towers, T-B2 (κ+1 ⟹ ×ρ^{−E}) on
12, T-B3 (drop the Ẽ(1)^E factor) on 6 — each ≥ 1 globally.

## §4. ARC-ACCOUNTING SYSTEM (charge 3) — CONSISTENT AND TRUE

All 16 arc hashes resolve with matching roles and strict clock order
(b375f42 08-06 08:22:56 → … → 355a14f 08-07 09:26:48 → PE7 0a2fb54
14:05:21 → ledger 93da1d1 14:06:40; full list re-pulled from `git log`
myself). The note at HEAD = 355a14f byte-identical; worktree clean.
Exactly ONE unstruck CURRENT status (r6); r1–r5 struck in place, content
preserved; strike census 19 spans = 38 `~~` tokens recounted exact. The
r6 STATUS's compressions of PE1–PE6 match the six report files; the r6
round record's byte-claims re-verified (§1 spot-checks). The note's two
live counter surfaces read "counter 0/2; PE7 is the next acceptance
attempt" (status line 110, footer line 938) — TRUE AS WRITTEN at r6, and
the arc's convention gives the note no edit event between r6 and this
pass (passes don't edit; only repair rounds / folds / acceptance records
do), so the current counter state (1/2 after PE7) lives where the
convention puts it: PE7's committed report + ledger 93da1d1 ("WM PE7
CLEAN (1/2 …; PE8 = accepting attempt)"). Consistent system-wide; same
adjudication PE7 gave the identical situation one round earlier. PE7's
findings: none; PE7's observations O-1..O-4 all correctly required no
action (§5). The counter now RESETS to 0/2 on F-1 below, per the charge.

## FINDINGS

### F-1. JUSTIFICATION GAP (S0's Bézout-normalization line displays a FALSE identity for the pinned convention — falsified on the note's own roster; internally inconsistent with the note's S0.3 display; blast radius nil)

The note, S0 (line 192, sealed text — present verbatim at b375f42,
untouched by r1–r6):

> "Tower T of the [ILN]† S0.1 class with reads (e_j, h_j, g_j), j = 0..n
> (NR = n+1 reads), normalized Bézout ℓ_j h_j − ℓ′_j e_j = ±1 form as
> pinned (`bez`), …"

The pinned `bez` (`iterlawn_pe_reimpl.py` line 242, md5-pinned by WM-PIN)
returns ℓ ∈ [0, e) with ℓh ≡ 1 (mod e) and ℓ′ = (1 − ℓh)/e — the
normalization **ℓ_j h_j + ℓ′_j e_j = 1**, which is also what every pinned
supplier displays for the harness: [ILN] ced7dbb line 157 ("Normalized
Bézout pairs (ℓ_j, ℓ_j′): ℓ_jh_j + ℓ_j′e_j = 1"), [W2] 5463f2a line 76,
[JA] ce0469a line 53. Under the pinned values, ℓh − ℓ′e = 1 − 2ℓ′e, which
lies in {±1} only when e = 1 or h = 1. The note's displayed minus-form
identity is FALSE at every read with e > 1 and h > 1 — realized on the
note's own frozen instrument: read (3, 2) gives (ℓ, ℓ′) = (2, −1) and
ℓh − ℓ′e = 7; read (2, 3) gives (1, −1) and 5; towers **C2D, C3C, C3E,
I4A, I4B** carry these reads (my machine check, this pass). The minus
form "ℓ_r h_r − ℓ′_r e_r = 1" is the PRINT-side convention with the
print's own (different, unpinned) ℓ′ ([JA] ce0469a line 35, FGMN tex
1285) — the sentence conflates the two calculi's conventions at exactly
the place that declares the harness normalization, and no "±" makes it
true of `bez`. Internal inconsistency: the note's own S0.3 display ten
lines below (line 202: S_{j−1} = D_jγ_j + S_j·(ℓ′_{j−1} − ℓ_{j−1}W_{j−1}),
byte-matching [ILN]) and the S5 gloss of the committed eps path (line
692: "the ℓ′s−ℓu exponent path") both REQUIRE the + convention's ℓ′, so
a reader who derives ℓ′ from line 192 computes a wrong S-chain and
breaks WM-COB(i) numerically.

**Blast radius: NIL for every displayed result** — ℓ′ enters no display
of this note except the S0.3 transcription (correct, byte-matching
[ILN]); t_j, ε_j, A_j, WM-COB, WM-RHO, WM-CLASS, WM-FENCE consume only ℓ,
e, s; every machine family is green under the + convention (the sealed
battery and both of my fresh legs). Not an honesty defect — an error.
Classification: JUSTIFICATION GAP (a false setting assertion the reader
must repair from the pin), not CRITICAL (nothing downstream depends on
it), not MINOR (unlike the r5/r6 species this is not a byte-fidelity slip
in a quote — the sentence asserts false mathematics about pinned
objects). One-line cure by the arc's own precedent: restore the pinned
byte-form "normalized Bézout ℓ_j h_j + ℓ′_j e_j = 1 (0 ≤ ℓ_j < e_j) as
pinned (`bez`)" with a bracket recording the sealed wording.

## OBSERVATIONS (not findings)

* **O-1 (PE7's four observations re-adjudicated).** O-1 (emphasis-token
  mirror): stands, no defect — same species both directions, formatting
  tokens are not quote content. O-2 (supplier motion pin-protected):
  stands (see O-2 below for the delta since PE7). O-3 (fresh-leg
  by-product offers): nothing owed, nothing taken. O-4 (collective
  bracket phrasing): nil, as adjudicated.
* **O-2 (supplier motion since PE7 — pin-protected; fold inventory
  unchanged in kind, +1 in count).** [W2] moved again (r4 94534df,
  14:20:00 — the P1-species vocabulary scoping; same species as its
  r2/r3, no WM sentence rides it). The W2-C3 HONEST RE-SCOPE (W2 r1
  8d5e3fa: proved-to-first-twist, MEASURED above, new box W2-OPEN-2)
  remains the one post-pin supplier delta in the WEAKENING direction;
  PE6 O-2 catalogued it with the fold obligation recorded supplier-side
  ("WM (M4) … fold annotations … orchestrator-owed") and PE7 passed
  clean on that state — pin-protected under the standing rule, but the
  next fold's [W2] pin update MUST carry the re-scope into the (M4)
  face's conditionality cell (flagged here so the fold cannot miss the
  direction). [JB]/[JC]/[ILN]/[SYN]/LED-Λ motion-free since PE7.
* **O-3 (fresh-leg by-products, offers only).** (i) The proof-step leg
  gives the note's S2.1 proof a per-claim machine key at negative γ
  (the sealed family keys the composite statement at γ ≥ 0 only);
  (ii) the norm-invariant leg's constructive form (the explicit E-th
  root Ẽ(1)^E) is the natural machine tie for any future JC-F1/ζ_T
  fold (the invariant ∏_k c(σk, σ1) IS the class datum WM-CLASS says
  carries everything). Script `/tmp/wm_pe8/wm_pe8_fresh_legs.py`, md5
  `2eac682cbc11f534d84060030ed3cb43`; reproduce-from-report if /tmp
  rotates. (iii) My ALL-pairs κ histogram (3,597 pairs; support 0..26)
  extends the sealed 4×4-sampled census — consistent with WM-CLASS,
  which correctly claims only κ ∈ ℤ_{≥0}.
* **O-4 (why seven passes missed F-1).** The arc's sweeps were
  quote-keyed (byte-fidelity at pins) and display-keyed (re-derivations
  of the theorem chain); line 192 is neither a quote nor consumed by any
  display — the first pass to machine-check the S0 setting identities
  themselves (γ-recursion, W-identity, and the Bézout line, this pass)
  found the one false one. The other S0 identities all verify TRUE on
  the roster (γ_1 = h_0; γ_{j+1} = e_jW_j + h_j; W_j = e_{j−1}g_{j−1}γ_j;
  A_j = 0 ⟺ e_{j−1} = 1; the abscissa tie).

## HONESTY GRADE

Above genre par, unchanged: the conditionality stack still understates
(JB/JC carried at 0/2 though ACCEPTED), the machine bracket is
byte-identical including elapsed time, the grade-cap and consumption-only
fences are honored everywhere I probed, and F-1 is a transcription-class
ERROR in sealed setting prose, not a misrepresentation — nothing in the
note trades on it. But the charge is exact: fences are part of the
statement, a false displayed identity about the pinned normalization is a
defect, and any finding resets the count.

**Counter: RESET to 0/2. PE9 is the next acceptance attempt, after an r7
that cures F-1.**

— PE8 verifier, fresh context, 2026-08-07.
