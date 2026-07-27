# HC1 BLUEPRINT REV 2 — FRESH-FABLE RE-AUDIT (2026-07-28)

ARTIFACT: `HC1_LEAN_BLUEPRINT_2026-07-28.md` REV 2 (1049 lines, 54 units), read in
full. HISTORY: rev 1 → REJECT 3 crit / 6 gap (`HC1_AUDIT_FABLE_2026-07-28.md`); rev 2
claims all nine folded (§1.1). GROUND TRUTH consulted: `MOVES_2026-07-24.md` —
§B2-DEF 1849–2745 (D.0–D.12 incl. 1992–2015 base, 2305–2352, 2419–2465, 2484–2546,
2551–2581, 2622–2670, 2672–2743), pass-7 carry spec 1456–1530, §C displays (C.1.0
3598–3632, scale declaration 3634–3642, DOM 3644–3726, LST 3728–3781, TYP 3783–3831),
Case-K v1 adjudication 2934–2972, Case-K v2 seal 3017–3045, REL.1/EQ-2 9379–9418 +
9560–9598; `MOVESGR_LEAN_BLUEPRINT_2026-07-26.md` §8.2; `MOVESR_AUDIT_FABLE3` findings
F3-1/2/3 + G3-1..4; the campaign ledger (wave-5 charge, MovesR PARKED entry);
`verification/CASE_K_SEALED_PREDICTIONS_V2_2026-07-26.md` + `case_k_gate_v2_p3.py`;
DISK (`grep sorry` over Moves/MovesGr/MovesC; file headers; `git log` 35bf18a/4b29f6e).
All five charge items verified BY COMPUTATION where flagged below.

## VERDICT: **ACCEPT (0 crit / 2 gap — both editorial one-liners, foldable at
E-phase without a revision loop)**

All nine rev-1 findings are genuinely folded, each verified independently (not from
the disposition table). The three rev-1 criticals are repaired exactly and correctly;
the §4 ledger now matches disk exactly. The two surviving findings below touch no
normative predicate, no dep list, and no fence.

---

## CHARGE ITEM 1 — the exclusive-STR convention (rev-1 C-1): VERIFIED BY COMPUTATION

* **(2,1) base recompute**: LST head (3731–3735) κ_r = h_r/(e_r·STR_r), base (3752)
  "w(x) = h₀/e₀ = κ₀ (STR₀ = 1)". Blueprint §2.2: STR₀ = 1, STR_{k+1} = STR_k·e_k
  (exclusive), κ_k = h_k/(e_k·STR_k). At (e₀,h₀) = (2,1): κ₀ = 1/(2·1) = **1/2** ✓
  (rev 1's inclusive paste gave 1/4 — repaired).
* **Two-ramified-level tower** (e₀,h₀) = (2,1), (e₁,h₁) = (2,1): exclusive STR₁ = 2,
  κ₁ = 1/(2·2) = 1/4; stage-1 valuation w′(p^l·φ^{s₀}·Φ̂₁^b) = e₁(e₀l + s₀h₀) + b·h₁
  = 4l + 2s₀ + b; strTop = STR₁·e₁ = 4; checked w′(m) = strTop·ht(c) on a full
  4×3×4 grid (script run, zero mismatches). The inclusive convention (κ₁ = 1/8)
  breaks already at (l,s₀,b) = (0,0,1): w′ = 1 vs strTop·ht = 1/2. The note's
  "κ_{i+1} = the v_p-slope of the side read" also recomputes to h₁/(e₁·STR₁) with
  the EXCLUSIVE prefix (frame-1 stage scale = e₀·absolute).
* **strTop's frame conversion at T3**: C.1.0(c) (3624–3628) declares str := "the
  product of the history's stretches e₀·e₁·… down to that frame" — inclusive of the
  frame's own read; blueprint strTop = STR_K·e_K = e₀·…·e_K matches, and the stage-K
  scale is exactly strTop (w_K(p) = e₀·…·e_K, checked at K = 0, 1). T3's K = 0 sanity
  line recomputed ✓; C2's δ′ := strTop·γ′ = TYP's δ′ := str·γ′ at the top frame ✓;
  T6's ⌊strTop·γ⌋ reindexing consistent ✓. **C-1 disposition CONFIRMED.**

## CHARGE ITEM 2 — S1(a)'s new base (rev-1 C-2): VERIFIED

* ψ = z² + z + 1 over K = F₂: ψ(0) = ψ(1) = 1 ≠ 0, degree 2 ⟹ **irreducible** ✓;
  z̄ = a primitive cube root in F₄ˣ satisfies z̄² + z̄ + 1 = 0 (F₄'s defining relation)
  ⟹ hroot ✓; [F : K] = 2 = g clears the RECORDED CONSTRAINT (hirr + hroot force
  [K⟮z̄⟯:K] = g ≤ [F:K] — the structural wall rev 1 found, now recorded) ✓.
* Discharge cites ON DISK, both sorry-free: `L3_liftExists` (:29) with threshold
  hypothesis `hthr : ∀ k < g, σ.wPrev σ.Φ < h·(g−k)` — at the degree-1 pin
  gaussVal(X) = 0 < 1, 2 ✓; `L3_liftWeight` (:36) `σ.w Φhat = e·h·g` — so
  w(Φ̂) = 1·1·2 = 2, h′ = 3, IAug: 3 > 1·2 ✓, gcd(1,3) = 1 ✓, every TransHyp field
  discharged as listed. Leg (b) provable by the `he'` projection ✓. The TransHyp
  interface = MOVESGR §8.2's proposed repair list verbatim (standard lift,
  irreducible ψ ≠ z, 1 ≤ e′, 1 ≤ h′, coprimality, IAug) + the harmless extra pins
  (monic, deg, root). **C-2 disposition CONFIRMED.**

## CHARGE ITEM 3 — G4 vs the Case-K v2 seal (rev-1 C-3): VERIFIED BY COMPUTATION

* d₀ = d₁² confirmed three independent ways: (i) the seal record (MOVES 3031–3032:
  "the unique both-rise is the Frobenius-matched τ = d₁ on each d₀ = d₁² cell — 8
  both-rise combos of 512"; same law in `CASE_K_SEALED_PREDICTIONS_V2` :37/:51);
  (ii) the script (`case_k_gate_v2_p3.py` :396 `d0 = f9mul(d1, d1)`; Q4 verdict
  string "the 8 cells d0=d1^2"); (iii) the char-3 algebra: double root of
  X² + d₁X + d₀ ⟹ 2τ + d₁ = 0 ⟹ τ = −d₁·2⁻¹ = d₁ (2⁻¹ = −1 in F₃), d₀ = τ² = d₁².
* Element-LIST pinning: leg (i)'s set equality {(d₀,d₁,τ) : d₀ = d₁² ∧ τ = d₁} =
  {(d₁²,d₁,d₁) : d₁ ∈ F9ˣ} is correct and the 8-of-512 count is demoted to a
  corollary; the {d₀ = d₁³} trap (also card 8; d₁³ = d₁² only at d₁ = 1) is named
  in-unit with the MOVES 2934 v1-adjudication warrant (verified on record at 2934).
  Leg (ii) pins per-cell solution lists. **C-3 disposition CONFIRMED** (one prose
  ambiguity — GAP-1 below).

## CHARGE ITEM 4 — the §4 re-census vs DISK (rev-1 G-1/G-2): EXACT MATCH

`grep sorry` over `lean/LeanUrat/Moves/` at this commit:

| §4 entry | blueprint claim | disk |
|---|---|---|
| 4.1 `L1_baseWeight_R3` | CLOSED (35bf18a, +823 lines) | 0 sorries ✓ |
| 4.2 `L2_iaugStep` | CLOSED (4b29f6e, +Irreducible) | 0 sorries ✓ |
| 4.3 `L4_TRANSv_R3` | CLOSED (fence-change APPROVED, re-pointed) | 0 sorries; header: "fence-change APPROVED … hcore : StageCore σ; import re-pointed to the CLEAN L4_TRANSviii_b_R4" ✓ |
| 4.4 `L5_landVertexDigit` | CLOSED | 0 sorries ✓ |
| 4.5 `L5_landTwoSided_repair` | RESOLVED, sorry-free, :755 with hexact | 0 sorries; theorem AT :755 with `hexact : ¬ X ∣ ∑ j ∈ range N, Cdig j * ψ ^ j` VERBATIM ✓; superseded `_R5` :964 sorry, not consumed ✓ |
| 4.6 `L6_measureExact_R4` | OPEN, :143/:189 | exactly 2 sorries :143/:189; :143 = the inlined `L5_landTwoSided_missing` (:130–:143) stated on `LandingCylinder` WITHOUT the exactness clause ✓ (so 4.5 does NOT discharge it — rev 2's correction of rev 1's error is right); :189 = the `exfalso; sorry` zero-coordinate leg with the in-file FLAG ✓ |

Both commits exist with matching messages. The only other sorried Moves files are
superseded/not-consumed (`L5_landTransport_R3`, `L6_moveReduceCommute_R3`,
`L4_TRANSviii_b_R3`, `L5_landTwoSided_R5`) ✓. Rev 1's gloss ("ord_z of the vertex
slot term = 0") is correctly STRUCK against rev-D¹¹ F4 (MOVES 2500–2505: the anchor
is the ord of the SUM) ✓. **G-1/G-2 dispositions CONFIRMED** (one stale adjective —
GAP-2 below).

## CHARGE ITEM 5 — fresh sweep of the 54 units, fences, doctrine: PASSES

* **Census**: 54 = 8+12+6+17+5+6 re-counted per layer; the §7 difficulty tallies
  re-added exactly (incl. T9 easy → medium at rev 2); hard total 10 as listed.
* **Fences**: all three MovesGr §8.2 certificates honored by construction (checked
  against the certificate text: faithful D.2 Gauss base T1; TransHyp = the e0-false
  cert's repair interface; `IsRecenteringCore` with `reps_eq`/`Tvec_eq` on disk at
  DefsCore :245–246, consumed by MoveWitness.rec/D8/S10/S15/S16; S8 derives the
  child T-law per the L4_TRANSvi cert's proposed repair). D.11's one-move scope
  clause (MOVES 2716–2718) kept; D9 = the literature note (2738–2743) verbatim,
  zero axiom candidates. Every reused identifier exists in Moves Defs*
  (IsStandardLift, IAug, StratumData, LandingCylinderL, K1At, IsSlotMinWeight,
  HasAnchorK, OrdPsiPoly, DigitSystem, CarryTransportL, carryDigit, StageCoreL,
  TransitionCoreL); MovesC sorry-free with C2_DOM_floorForm/Line/DomData/
  LevelClause/floorOf on disk; MovesGr = 2 live sorried v2 units, matching the
  header's "19 proved + 2 sorried + 5 held"; `add_def` landed.
* **Rev-2 changed units re-derived**: C6's dichotomy = MOVES 2160–2165 both
  directions incl. strict-smaller and the D.9(b) regime correctly demoted to an
  instance ✓ (G-4 folded). T9(b)'s mixed-radix leaf-address injectivity is correct
  mathematics (slot_lt = the degree-ratio digit bounds; slotBound = e_r·g_{r+1}
  matches D.3's deg Φ̂ = e·g·deg Φ; uniqueness by mixed-radix) and is the
  coordinate-partition content of (ii.3) at 2175–2188 ✓ (G-5 folded). S12's D.4
  derivation form matches the three bullets at 2217–2249 with the chord shape
  e·h·g·(μ−j) < w(B_j) − w(B_μ) (w(Φ̂) = ehg by L3_liftWeight) ✓ (G-6 folded).
  §2.2's recorded-decisions paragraph pins all four G-3 items, each checked against
  D.3/D.3(e) (top space C_{K+1} = the pending read's Ĉ per 2067–2068 — the
  unbounded-top-slot decision is forced; recentering ratio 1 per deg Φ′ = deg Φ̂ at
  2664; the root-eBirth divergence from pass-7 is recorded with its (S5) warrant) ✓.
* **Gates recomputed**: G1's value = MOVES 2318–2322 (z̄² = z̄+1; dig′(Φ² mod Φ̂) =
  z̄²) ✓; G3's Case-J instance verified symbolically over F₂ (P(z+1) =
  (z+1)·z²·(z²+z+1); a′ = 2 = μ; R′_anch = (z′+1)·h(z′+1); ψ′ = z+1 ∤ z·h since
  value at 1 is 1) ✓; G5 = MOVES 9580–9582 (F₃·1 + F₃·τ = F₉, card 9; single line 3)
  ✓; G2's carry table follows from carryExp (overflow indicator = ⌊(ρ+σ)/e⌋ on
  reps < e — the pass-7 cocycle 1465 exactly) ✓.
* **Spine/transport refs**: S2/S3/S4/S5 = D.7(i)–(iii) at 2329–2352 (incl. the F5
  no-renormalization clause) ✓; S6/S7/S8 = D.7(v)–(viii) at 2364–2463 (constant
  orbit, two-line recursion, I-aug at the PREVIOUS read) ✓; S9's close = 2464–2465
  verbatim ✓; S10 = TRANS-RS 2661–2670 ✓; S13 = D.9(a)–(d) 2551–2581 incl. the
  induction-order clause ✓; S14 = the well-typedness lemma 2636–2643 ✓; S15 = the
  anchored display 2644–2653 with the D8 quote (2668) verbatim ✓; S16/S17's hexact
  threading matches the landed repair theorem's actual signature, with the correct
  forward/backward asymmetry (the repair header's own countermodel analysis) ✓;
  S17's statement = D.11's display 2685–2705 incl. the D¹¹d dichotomy and the one
  unit system ✓. R-layer: F3-1/2/3 + G3-1..4 all present in `MOVESR_AUDIT_FABLE3`
  and implemented as claimed; REL.1's status = 9379–9418 (walk item (i) = R2's
  additive-not-linear typing at 9401–9407) ✓; EQ-2 "OPEN, REL.1-conditional" =
  9586–9588 verbatim ✓; MovesR PARKED + the wave-5 re-key charge on record in the
  campaign ledger ✓. TowerRealizable rides exactly where the note's quantifier
  demands (DOM(2)'s rev-12 SAE sourcing, 3670–3677) ✓.
* **Doctrine**: every interface false on note-rejected instances (TransHyp at
  e′ = 0/ψ = X/reducible ψ/non-IAug; IsBaseStage false on the wPrev = 0 clone —
  gaussVal(C p) = 1 ≠ 0; floorB/alphabet/ht by construction) ✓.

---

## SURVIVING FINDINGS (both editorial; neither warrants a loop)

### GAP-1 (unit G4, leg (ii) — ambiguous cardinality pairing). The clauses are named
"`2τ + d₁ = 0` / `R₂(τ) = 0`" but the corollary tuple "(56 / 64 / 8 both)" is in the
SEAL's order — which is the REVERSE: recomputed, |{R₂(τ) = 0}| = 8·7 = 56 (d₀ =
−τ(τ+d₁) ∈ F9ˣ forces d₁ ≠ −τ) and |{2τ + d₁ = 0}| = 8·8 = 64 (τ = d₁, d₀ free);
seal text: "R₂(τ) = 0 on 56, 2τ+d₁ = 0 on 64, both on 8" (MOVES 3026–3028). A
positional reading mispairs 56 ↔ 64. Self-catching (a mispaired list-vs-card decide
fails loudly — the silent-pass species of C-3 cannot recur), and the unit's NOTE
already subordinates transcription to the displayed predicates; still, swap the
clause order (or annotate each cardinality) at E-phase. ONE LINE.

### GAP-2 (§4 closing paragraph — stale adjective). "Superseded sorried files"
lists `L2_P6i_R5` and `L4_TRANSviii_a_R5`, which are sorry-free on disk (both among
35bf18a's "4 PROVED"). They are correctly NOT consumed (HC1 imports the `_final`s),
so no consumer is misdirected; the adjective is merely stale. Drop the two names or
re-title the list "superseded (some sorried)". ONE LINE.

---

DISPOSITION: ACCEPT. Fold GAP-1/GAP-2 as in-place editorial fixes at E-phase entry
(no re-audit needed — no normative predicate, dep, hypothesis field, or fence is
touched). The blueprint is ready for the E-phase gate per §7's process, with the
R-layer re-audit still gating MovesR's unparking as stated.
