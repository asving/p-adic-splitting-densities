# MovesS blueprint REV 8 — fresh-instance confirmation audit (Fable #6)

**Date:** 2026-07-28 · **Auditor:** fresh Fable instance #6, spawned via workflow
(zero shared context with the drafter or any prior auditor) · **Scope:** REV 8
confirmation pass per `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` (checklist below its
`---`), INCLUDING the independent adjudication of the R30 PolyGeom denominator
convention question on which the two rev-7 verdicts converged. Ground truth:
`MOVES_2026-07-24.md` §S-RESUM, lines 11557–12577, read in full. Blueprint:
`MOVESS_LEAN_BLUEPRINT_2026-07-28.md` REV 8, all 1592 lines read. Method:
verification by computation and display comparison, not plausibility.

**VERDICT: REJECT (0 crit / 4 gap)** — the five directed REV-8 checks all PASS
(convention adjudication CONFIRMED as a convention fix; gate window data exact by
computation; W2/W3 genuinely de-circularized; W7 CUT laws substantially faithful
with two residual under-pins; carriers typed/card-pinned/owner-tagged); four gaps
remain, all mechanical or pin-completeness, none touching the mathematics.

---

## 1. THE CONVENTION ADJUDICATION (charge item 1) — R30 CONFIRMED, convention fix, not a math error

**The note's (iv)-POLY display, quoted (S.3, lines 12129–12133):**
> "K_e/b_e^{term,fin} entries: T is one polynomial of degree ≤ W_loc(m) and each
> cell size one polynomial of degree ≤ W_state(s), valued correctly at every prime
> power — CTS-M(iv)-POLY (CL-6, with V.2's EXPONENT-MAP AUDIT); G ∈ ℚ(q) with
> geometric denominators (1 − q^{−a}) — XHD-s over the listed pairwise-disjoint
> components."

And S.0 (line 11662): "G := the XHD one-step resummed height mass (XHD-w
**monomials g** …)" — step weights are monomials in q⁻¹ (conditional masses ≤ 1).

**My adjudication (independent):** the display's class is written in the variable
q⁻¹ — the factors are (1 − q^{−a}) and the numerator atoms are monomials q^{−c}.
Cleared to the RatFunc variable X = q: q^{−c} ↦ 1/X^c (reduced denominator X^c);
1/(1 − q^{−a}) ↦ X^a/(X^a − 1). E.g. Σ_{h≥h₀} q^{−h} = q^{−h₀}/(1−q^{−1}) reduces
to 1/(X^{h₀−1}(X−1)) — a q-power times a geometric factor. So the faithful X = q
class is exactly **denom ∣ X^b · ∏(1 − X^a)**, q-powers required. The REV-3 law
(denom ∣ ∏(1−X^a) alone) genuinely excluded the note's own objects: X ∤ ∏(1−X^a)
for any exponent set (the product evaluates to 1 ≠ 0 at X = 0), so even G = q^{−c}
was unrepresentable. Blueprint-side error, note intact. R30's `PolyGeom.qpow` +
the corrected `geom_denom_dvd` law is the faithful rendering. **NO math-error
flag on the note.**

**Representability verified three ways (computed):**
- **The three gate masses:** q⁻³ = 1/X³ (denom X³ = X³·∅-product ✓); 1 − q⁻¹ =
  (X−1)/X (denom X ✓); q⁻¹ − q⁻³ = (X²−1)/X³ (denom X³ ✓). All inhabit the
  corrected class.
- **The CTS count/q^level form:** count · q^{−level} = count/X^level, denom
  X^level ∣ X^level·∅-product ✓; with XHD-s resummation factors, denom
  X^level·∏(X^a−1) ✓.
- **Adversary 1/(q−2) STILL FAILS:** if (X−2) ∣ X^b·∏(1−X^a) then the RHS
  vanishes at X = 2; but 2^b·∏(1−2^a) ≠ 0 (each 1−2^a ≤ −1). The class is not
  trivialized by adding qpow. ✓
- (Repeated-factor closure checked: (1−X^a)^k ∣ ∏_{j≤k}(1−X^{ja}) over DISTINCT
  Finset exponents, so `geomDenoms : Finset ℕ+` loses no multi-read height sums.)

## 2. The corrected gate window data (charge item 2) — R35 PASSES by computation

U-29b3: SCS data at o_K is **W = 2, D = 1, ℓ = g = μ = 1** (e = 2). Every SCSData
law computed: ℓpos 1 ≤ 1 ✓; window_comp W = e·ℓ + flankWidth: 2 = 2·1 + 0 ✓;
flank_zero (0,0) ✓; sel_mem (1,1) ∈ {(1,1)} ✓; res_sum 1·1 = 1 = ℓ ✓; stage_D
D′ = e·g·D = 2 ✓; stage_W W′ = μ = 1 ✓; cluster_parent W·D = 2 = e ✓;
cluster_child member size 2 = W′·D′ = 1·2 ✓ (U-5's law exact). The REV-7 μ = 2
genuinely violated the laws (res_sum forces g·μ = ℓ: 2 ≠ 1; or ℓ = 2 breaks
window_comp 4 ≠ 2; and W′D′ = 4 ≠ 2), and the diagnosis is note-grounded: lines
11857–60's "μ = 2 cluster into the size-2 block" is the ROOT-ENTRANCE typing
(entrance-side ε data), not the kcol outcome's in-block window. **Masses/det/β
UNCHANGED, verified:** row sum q⁻³ + (1−q⁻¹) + (q⁻¹−q⁻³) = 1 ✓; det(1−K) =
1−q⁻³ = (q−1)(q²+q+1)/q³ ✓; β_{(1,2)} = (q⁻¹−q⁻³)/(1−q⁻³) = (q²−1)/(q³−1) =
(q+1)/(q²+q+1) ✓; β_{(1,1)²} = (1−q⁻¹)/(1−q⁻³) = q²(q−1)/(q³−1) = q²/(q²+q+1) ✓;
sum = (q²+q+1)/(q²+q+1) = 1 ✓ — the note's displayed denominator q²+q+1 (line
11649) exactly; kcol mass 1/8 at q = 2 = the msW_eighth_le shadow ✓.

## 3. W2/W3 de-circularization (charge item 3) — R32 PASSES

`RS1Meas` (lines 717–723) carries **βmeas/β_bdd/βfull only** — no hypothesis
fields, verified. `RS1Bundle extends RS1Meas` adds xrb/recursion_meas/nsNull/
rexact. `W2_xrb (B₀ : RS1Meas)` and `W3_recursion (B₀ : RS1Meas)` are stated over
the RAW family with quantifiers IDENTICAL to the bundle fields (xrb: ∀ e he h h'
τ σ'; W3: same ∀ + pool-membership + `M.activeState` guard + ∀ h_ent as
`recursion_meas`) — the pins are the obligations that create the fields; nothing
at wave 2 constructs a bundle, and §3b's discipline line ("nothing proves toward
xrb; no PCI site is consumed by S.1-shaped content") holds across the DAG. The
note packages are quoted correctly at the pins: W2 carries S.1's STATUS LINE set
(XHD w/u/d/s + (JC-INV) + (SIB)/(JC-multi) + TB-CAP/VP + REL.2(a)/(b)/(d) +
(ns-null)) — verbatim vs lines 11998–12002 modulo a harmless elision of the
"(NEW at rev 2 — the joint-lumpability face" parenthetical; W3 carries S.2's
GIVEN-list verbatim vs lines 12016–12019. ✓

## 4. W7_cutWD vs (CUT-WD) clause by clause (charge item 4) — substantially faithful, TWO residual gaps

- (CUT-1) first-entrance uniqueness: clause 1 (onPath-antisymmetry on entrance
  nodes) + clause 2's ∃!-with-minimality render "the FIRST one (if any) is
  unique" ✓.
- (CUT-2) trichotomy: clause 2's disjunction (no entrance at-or-before ν) XOR
  (unique first entrance preceding every entrance on ν's root-path) — exhaustive
  and non-overlapping by content ✓. The (BDY) node/edge boundary rule is the
  separate pin W8_bdy over ReadLedger (entrance side INCLUSIVE of the entering
  read fe; β charges from fe+1) — matches (BDY)'s display ✓. **But the display's
  fence "Deep-recursion splits are never re-classified as shallow" has NO clause
  — GAP 3 below.**
- (CUT-1)'s σ₀ feed: clause 3 pins (shapeOf t).σ0 = the filterMap of leafHalt
  over exactly the SHALLOW nodes ✓ faithful.
- (CUT-3) choice-freeness: shapeOf is a function (structural) ✓, listed in F.Sh
  ✓. **But "entrance and halt boundary data retained" is only half-pinned — GAP
  2 below.**

## 5. The typed height carriers (charge item 5) — R34 PASSES on content

`shDom`/`shEvtH`/`visH`/`shEvt`/`shWeightH` are declared FIELDS of RS4Chain
inside §2.D's lean fence (lines 783–787, fence 686–830) ✓; `shweight_card` pins
shWeightH to event cards per fixed height (non-gameable, counting-native) ✓;
`shevt_grouping` pins shEvt to the biUnion of shEvtH over visH ✓; `wshval_card`
pins the total-mass face ✓; owner tags "[1v]/[3t]; CL-17(ii): 'the capstone may
not be accepted while it is open'" present ✓. W17ii's Prop is the XHD-s
height-sum face over these carriers with the residual production law honestly
kept owner-tagged OPEN ✓. **But W17ii sits OUTSIDE the closed code fence — GAP 4
below.**

## 6. Six spot-checks (charge item 6) — all PASS

1. **U-1 dispatch_spec** vs the (m,c) CLASSIFICATION (lines 11792–11803): the
   iff-triple under 1 ≤ m, c ≤ m reproduces (c=0,any m)/(c=1,m=1)/(c≥1,m≥2)
   exactly; "c ≥ 1 with m = 1 forces c = 1" ✓.
2. **U-8 ksub_regroup** vs (K-SUB) (lines 11769–11771): three-summand regroup
   with Σ_o J on splitOuts (the cell-level J, never marked T·G) and verdictImage
   closing the σ′-sum; "= 1" correctly displaced to U-9a (measured, guarded,
   part1 + rep_indep = the note's conditionality bracket) + U-9b (symbolic) ✓.
3. **U-16a1 bSplit_def** vs the b_e^split display (lines 11691–11698): J · the
   multiset convolution over member-indexed tuples (SIBLING INDEXING ✓), halted
   legs the factor-1/verdict-singleton indicator (§T.4 cited ✓), continuing legs
   powSubst δ (βlt …) with DELTA-ABS composing to the absolute index ✓.
4. **U-22 rs3_det_symbolic** vs S.4(ii) (lines 12198–12203): all-active locus,
   infinitude burden (allActive_infinite = the cofiniteness face), e bound inside
   both hypothesis and conclusion ✓.
5. **U-28 rs4_rational_step** vs RS.4 (lines 12248–12268): Σ_{σ∈Sigmas} Rsh = 1
   via eval-at-every-base-prime (x3_total + rs1_equates + rsh_interp) + U-27;
   RS4Chain carries the FULL inherited set (nine CL-5 inputs, RS.1's set, hns,
   pools_e0/legs_reg = E0 per pool, WshP, POLY-form RB) ✓.
6. **U-29d-iv n2_sigmas**: degree-2 multisets over vEquiv's pairs {(1,1),(1,2),
   (2,1)} are exactly {(1,1)², (1,2), (2,1)} — sig_exact forces the roster ✓.

Full-sweep extras verified: census arithmetic exact (70 = 9+4+16+10+6+25; easy
18+14 = 32, medium 38, 0 hard; per-unit labels consistent); n2 block-1 layer
present (R36); U-29d5's S = base primes matches consumedDeltas = {1} (closure of
δOf ≡ 1, no split legs) and all-activity at q₀ ≥ 2; U-24b written out in full
Lean with total coordinate coverage; [DecidableEq ι] present at U-15 (R36 batch
complete); MuHat fence has no Add; PART-2's surplus row has no carrier;
ESCAPE-UNIF does not exist; W1m gated per pool; the markedPairing/hdet arity
slack is self-documented (R29).

---

## FINDINGS (0 critical / 4 gaps)

**GAP 1 — stale `PolyGeom.count` accessor survives the R31 split (§2.C, line
613).** Quote: `ι_count : … ((ιP e τ ε).count.eval q₀ : ℚ) = M.entCount e τ ε
q₀`. R31 split `count` into `countT`/`countS` (lines 549–554); the field `count`
no longer exists, so `ι_count` cannot elaborate, and it is UNDERSPECIFIED which
object carries the ENT-COUNT tie ("per-shape ENT-COUNT polynomials of degree ≤
W_ent(ε)", S.3 line 12136 — ONE polynomial in the note). Repair: designate
(countT * countS).eval — or countT with countS pinned to 1 for ιP — and say
which. Classification: GAP (underspecified Defs dependency; R31 ripple missed).

**GAP 2 — (CUT-3)'s entrance-data retention is unpinned (§2.E W7_cutWD).** The
display (lines 12091–12093): "Ŝ := T's shallow layer with values and heights
forgotten, **entrance and halt boundary data retained**". The pin fixes the halt
half (clause 3: σ0 = the shallow leaf-verdict multiset) and listing (clause 4)
but has NO clause tying `shapeOf t`'s entrance legs (k/eOf/τOf/δOf) to the
tree's actual first-entrance data (`blockOf` at the clause-2 witnesses) — both
carriers exist, so the clause is statable and simply missing; a wave-4 discharge
of W7 as written would not guarantee the shape's convolution legs are the tree's
entered blocks. Classification: GAP (pin weaker than the display; no wave-2
consumer is corrupted).

**GAP 3 — the no-reclassification fence is comment-only (§2.E after W7_cutWD).**
The display (lines 12087–12090): "Deep-recursion splits are never re-classified
as shallow: b_e^split consumes them in-block by the ROUTING law". The blueprint
handles this as prose — "structural: b_e^split legs are NOT TreeIface entrances
(isEntrance's extension excludes them)" — but nothing in TreeIface distinguishes
deep-split legs from entrances (`blockOf`'s type fits both), so the exclusion is
an unstated wave-4 obligation on isEntrance's extension, while R33's ruling text
claims the fence is part of what W7 "states". Classification: GAP (display
clause without a formal counterpart; flagged in-text but not pinned).

**GAP 4 — W17ii sits OUTSIDE the §2.E code fence (lines 927–938).** The fence
opened at line 840 closes at 927; `def W17ii …` begins at 929 — contradicting
R34's executed-repair claim "`W17ii` moves inside the code fence". Phase E's
extraction of Interfaces.lean by fenced blocks would silently drop the CL-17(ii)
pin. Classification: GAP (mechanical; ruling not executed).

---

**Counts: 0 critical / 4 gaps.**
**VERDICT: REJECT (0 crit / 4 gap).**

Convention adjudication on record: R30 CONFIRMED — the note's (iv)-POLY class is
stated in q⁻¹ and, read in its own convention, contains every displayed object;
the faithful X = q class is denom ∣ X^b·∏(1−X^a); PolyGeom.qpow is the correct
fix; the REV-3 law was the error (blueprint-side, latent since REV 3); the class
remains non-trivial (1/(q−2) still excluded). No math-error flag on §S-RESUM.
