# MovesS Lean blueprint REV 12 — FRESH-INSTANCE ACCEPTANCE AUDIT (Fable #10)

*2026-07-28 (session date 2026-07-27). Auditor: fresh Fable instance; read-judge-fix-nothing.
Blueprint: `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` REV 12, read IN FULL (2081 lines).
Ground truth: `MOVES_2026-07-24.md` §S-RESUM, lines 11557–12577, read in full.
Charge: (1) the countS_cells deletion vs the note's cell-sum display; (2) U-22's
R51 re-scope vs the note's E0 display; (3) RS4Chain field ownership, enumerated;
(4) the settled arithmetic recomputed; (5) eight spot-checks; the fresh 95-unit
sweep; census 52/43/0.*

**VERDICT: NOT ACCEPTED — 0 critical / 2 gaps (+1 observation).** Every
architectural item of the rev-12 convergent list verifies: the R50 deletion is
the right call and is clean under grep; the R51 scope matches the note's E0
display exactly; the arithmetic and the census are exact. The two gaps are
bookkeeping residue of the R52 unit split — one RS4Chain data field lost its
owning unit in the split, and the retired collective unit name survives at
three live sites.

---

## V1. The countS_cells deletion (R50) — RIGHT CALL, VERIFIED; grep CLEAN

**The note's displayed aggregate for split outcomes is a cell-SUM.** S.0's
b_e^split display, verbatim (note 11699–11703):

> "where J_{τ,o}(q) := the CELL-LEVEL resummed branching mass — the sum, over
> the branching digit CELLS of outcome class o at state τ, of the XHD-resummed
> conditional cell mass ([3t] TREE-EXP's jvol(c│Σ) summed over the cell's XHD
> height classes), EACH CELL ONCE."

And (K-SUB)'s third summand (note 11771–11772): "the third summand being
exactly Σ_o J_{τ,o} — the (J-RAT) cell-level object supplied by PART-1, never
the marked offspring row". I searched §S-RESUM end to end for any aggregate
PRODUCT-of-cell-sizes display: none exists. The (iv)-POLY inventory (S.3) is
per-piece ("T is one polynomial … and each cell size one polynomial …"); the
per-cell deliverable is (J-RAT)'s PLAN-SYNC entry (note 12296–12301: "per
branching digit cell … the cell-count polynomial per the (iv)-POLY pattern +
its XHD-s height sum"). The deleted `countS_cells` (countS = ∏ per-cell cellP)
was an undisplayed strengthening — and for a multi-cell outcome the aggregate
count is the SUM of cell counts, not the product, so the product law was not
merely undisplayed but implausible for the intended instance (Fable#9-G-2's
spurious-denominator/degree analysis stands).

**The walk — the display IS carried without it:**
- `j_interp` (blueprint §2.C, 779–781): for `routeOf = .split`, eval of
  `(jP e τ o).val` at every pool = `M.rowVal e τ o q₀` — the symbolic J tied
  to the measured row.
- `rep_indep` (LedgerIV (4), 671–672): `rowVal e τ o q₀ = ∑ c ∈ cells o,
  μcell e τ x c q₀`, a Finset sum over `{c | cellOut c = o}` — EACH CELL ONCE,
  from every representative x (= RS.0(α)'s weighted grouping). `μcell`'s field
  comment (621) is the note's exact phrase "XHD-resummed conditional cell mass".
  Composition: eval jP = rowVal = Σ_cells μcell — exactly the S.0 display at
  the measured level. ✓
- R45's burden carried per cell: `act_iff` (811–812: activity ⟺ ∀ c,
  cellP.eval ≠ 0 — an empty cell cannot hide behind aggregate outcome mass;
  the note's own tie: "Per-shape emptiness at wild p is polynomial vanishing
  (CTS-M(ii); W1's pool-size effect)", S.3) + `cellP_nonzero` (801, the
  "not-identically-zero cell-size polynomial") + `cellP_deg` (800, ≤ W_state).
  U-22b consumes exactly these (its hyp line: cellP_nonzero + act_iff +
  pools_infinite). ✓
- Codex#8-1's residual demand landed as specified: `cellLvl`/`cellInst`
  carriers (613–615) + `cellP_count` (806–810) — the polynomial's value at an
  active pool IS the cell's instance-count at its own defining level, the
  accepted G4 pattern (mirrors `entLvl`/`entInst`/`ent_count_card`). ✓

**Grep (`countS_cells`, whole repo):** hits ONLY in the historical registers —
the R50 ruling itself (line 5), the two deletion-record comments (§2.C 803–805,
n2_activity 1647: "countS_cells is GONE, R50"), the cumulative findings tables
(2058, 2065, 2069), and the two rev-11 audit verdict files. NO live field, NO
unit obligation, NO consumer. The former `cellsize_nonzero` likewise survives
only in ruling history; the live field is `cellP_nonzero`. CLEAN. ✓

## V2. U-22's new scope (R51) vs the note's E0 display — EXACT

The note's kernel quantifier (S.4, 12163–12168): "For each RELEVANT POOL
q₀ = p^δ — δ ranging over 1 AND every base-change index a β_{e_j,τ_j}(q^{δ_j})
leg of b_e^split or RS.1-SH consumes ([2r] BASE-INDEX CONVENTION + (e2), δ
ABSOLUTE; δ = 1 the base instance) — and each e ≤ n …". The det-derivation
locus (S.4(ii), 12198–12202): "at all-active primes (cofinitely many — only
finitely many primes are roots of some not-identically-zero cell-size
polynomial) K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0; a rational function
vanishing at infinitely many prime evaluations is 0".

- **U-22 `rs3_det_symbolic`** now takes the base-pool locus (PP with the
  `prime_base` iff + `prime_sub`) and demands packages ONLY at
  `PP ∩ allActivePools M` — precisely S.4(ii)'s all-active-primes locus, which
  is the only place the note's det argument fires. U-22c (finiteness of
  non-all-active base pools, from U-22b through prime_sub) + prime infinitude
  give the infinitely-many/witness step. ✓
- **The consumed base-change legs** ride `legs_reg : ∀ p ∈ PrimePools, RegP …`
  with `RegP` quantifying over `consumedDeltas` — the multiplicative closure
  (U-16a3, DELTA-ABS) containing the empty product 1 (the note's "δ = 1 the
  base instance") and every effective nested index p^(δ₁·…·δ_k)
  (`nested_delta_mem`), i.e. "every base-change index a leg of b_e^split or
  RS.1-SH consumes". ✓
- **E0 at every prime-power pool is demanded NOWHERE**: `pools_e0` is
  re-quantified over `PrimePools ∩ allActivePools M` (962–966, field ordered
  after PrimePools); Pools membership itself carries no E0 demand; U-24a1
  takes its package as a hypothesis (RegP-supplied); ReadOffBundle's packages
  are data over a chosen S ⊆ allActivePools. ✓
- The per-pool (ii-c) read-off discipline is untouched: AVAgree per object
  (U-24a2, W1m gated per pool). ✓

Match to R51's ruling text: exact. PASS (one dep-line observation, O-1 below).

## V3. RS4Chain field ownership — ENUMERATED; ONE FIELD UNOWNED (GAP-1)

Every RS4Chain field (§2.D, 948–1034) against its owning gate unit:

| field(s) | owning unit |
|---|---|
| L (LedgerIV, 9 items) | U-29b-i…xiv (14 one-field units) ✓ |
| B (RS1Bundle: βmeas/β_bdd/βfull, xrb, recursion_meas, nsNull, rexact) | U-29d-i…iv (n2_beta/n2_recursion/n2_xrb/n2_rexact) ✓ |
| hns | the n2_rsh assembly paragraph (listed by name in "THE FULL RS4Chain IS INSTANTIATED" enumeration) ✓ |
| PrimePools, prime_sub, prime_base | n2_rsh assembly enumeration ✓ |
| pools_e0, legs_reg | U-29d2 `n2_pools_all` ✓ |
| Sigmas, sig_exact | n2_sigmas ✓ |
| WshP, wsh_ok, WshVal, wsh_interp | n2_wshp_device ✓ |
| shDom, shEvtH, visH, shEvt, shevt_grouping | n2_sh_events ✓ |
| **shWeightH** | **NO UNIT** ✗ — see GAP-1 |
| wshval_bdd, shDom_ne, sh_realized, shweight_card, wshval_card | n2_sh_laws ✓ (wshval_card = the Fable#9-G-1 repair, verified present) |
| Rval, r_bdd | n2_rsh assembly enumeration ✓ (n2_x3 constructs decidedTotal := Σ Rval from it) |
| decidedTotal, x3_total | n2_x3 ✓ |
| rs1_equates | n2_rs1eq ✓ |
| rsh_interp | n2_rsh ✓ |

**GAP-1 — `shWeightH` (RS4Chain data field, line 996) lost its owner in the
R52 split.** At REV 11 the single unit `n2_shallow_device` owned it by name
(R46's list, line 61: "device shDom/shEvtH/visH/shWeightH/shEvt with their
card/grouping laws"). R52 split that unit into three and enumerated the fields
per unit — `n2_wshp_device` (WshP/WshVal/wsh_ok/wsh_interp), `n2_sh_events`
(shDom/shEvtH/visH/shEvt + shevt_grouping), `n2_sh_laws` (wshval_bdd/shDom_ne/
sh_realized/shweight_card/wshval_card) — and `shWeightH` appears in NONE of
the three lists (ruling R52, lines 28–32, and §3 S5, lines 1697–1709, agree in
the omission). n2_sh_events's gloss "synthetic events whose cards realize the
weights" presupposes the weights but no unit defines the data field;
`shweight_card` (n2_sh_laws) is a LAW about it and cannot supply it. This is
exactly the defect class Fable#9-G-1 flagged for `wshval_card` — the full-chain
instantiation claim (R46) again has a field without a named owner. Fix is
one word: add `shWeightH` to n2_sh_events's field list.

## V4. The settled arithmetic — RECOMPUTED, ALL EXACT

- part1: q₀⁻³ + (1 − q₀⁻¹) + (q₀⁻¹ − q₀⁻³) = 1 ✓; row masses at q₀ ≥ 2:
  q₀⁻³ > 0, 1 − q₀⁻¹ ≥ 1/2, q₀⁻¹ − q₀⁻³ = (q₀²−1)/q₀³ > 0 ✓.
- det(1 − K) = 1 − q⁻³ = (q³−1)/q³ = (q−1)(q²+q+1)/q³ ≠ 0 ✓.
- Reduced solve: β_{(1,2)} = (q⁻¹−q⁻³)/(1−q⁻³) = (q²−1)/(q³−1) =
  (q+1)/(q²+q+1) ✓; β_{(1,1)²} = (1−q⁻¹)/(1−q⁻³) = q²(q−1)/((q−1)(q²+q+1)) =
  q²/(q²+q+1) ✓; sum = (q²+q+1)/(q²+q+1) = 1 ✓; the note's displayed
  denominator q²+q+1 exact ✓; eval at q₀: (q₀+1)/(q₀²+q₀+1) — R46's
  Fable-verified value reproduced ✓.
- E0: A = [q₀⁻³], entry 1/8 at q₀ = 2 (the msW_eighth_le shadow), < 1 at every
  q₀ ≥ 2 ✓.
- R35 window data at o_K: W=2, D=1, ℓ=g=μ=1: window_comp 2 = 2·1+0 ✓;
  res_sum g·μ = 1 = ℓ ✓; W′ = μ = 1, D′ = e·g·D = 2, W′D′ = 2 = WD = member
  size ✓.
- DegCons: member-size sums 2, 1+1, 2 all ≤ 2 ✓; (m,c) routing (1,1)/(2,0)/
  (1,0) → kcol/termFin/termFin ✓.
- n2_sigmas: vdeg (1,1)=1, (1,2)=2, (2,1)=2; degree-2 multisets = exactly
  {(1,1)², (1,2), (2,1)} ✓.
- PolyGeom under the R30 law (denom ∣ X^b·∏(1−X^a)): q⁻³ = 1/X³ (qpow 3) ✓;
  1−q⁻¹ = (X−1)/X (qpow 1) ✓; q⁻¹−q⁻³ = (X²−1)/X³ (qpow 3) ✓; det's q³ ✓.
- AVAgree hok denominators: q₀²+q₀+1 ≥ 7 and q₀³ ≥ 8 at q₀ ≥ 2, nonvanishing ✓.
- consumedDeltas at the instance: no split outcomes, δOf ≡ 1 ⟹ {1} ✓.

## V5. Eight spot-checks (blueprint vs note) — ALL PASS

1. **R50 adjudication quote** vs note 11699–11703: verbatim-compatible
   (ellipses honest); no aggregate-factorization display exists in §S-RESUM. ✓
2. **U-1/routeOf** vs the (m,c) CLASSIFICATION (11792–11803): if c=0 termFin,
   else if m=1 kcol, else split — matches the three-row routing; c ≤ m holds
   definitionally (filter length), so (c≥1, m=1) ⟹ c=1 as the note notes. ✓
3. **U-16a1 bSplit** vs the b_e^split display (11691–11698): J coefficient per
   split outcome; multiset convolution σ′ = Σ g j; member-indexed product over
   ALL members (Fin mem.length — SIBLING INDEXING, no symmetry factor);
   τ-halted members = indicator forcing σ_j to the verdict singleton, factor 1
   (§T.4's leaf convention, cited); continuing legs powSubst δ (βlt …). ✓
4. **U-8 (K-SUB)** vs 11769–11772: Kmat row + Σ_{verdictImage} bTerm +
   Σ_{splitOuts} J = routed total; = 1 evaluated at active states via part1 +
   rep_indep + the route-split interps (U-9a), symbolically via infinitude
   (U-9b) — the third summand is Σ_o J, never the marked T·G. ✓
5. **RS4Chain.xrb** vs the XRB display (11899–11903): h_ent-invariance of the
   measured conditional, pointwise at pools (R40) — never whole-ℚ-function. ✓
6. **U-28's route** vs S.5 (12248–12268): x3_total ("at each prime p the
   decided-mass series totals 1") + rs1_equates + rsh_interp + U-27
   ("a rational function equal to 1 at infinitely many prime powers is
   identically 1"); the full inherited tag set explicit in RS4Chain, with the
   R53 CL-17(ii) inheritance declared BOTH at the wsh_ok field block (978–984:
   denominator regularity only; production = seam pin W17ii/S-8; no
   unconditional marking while open) and in U-28's hypothesis line
   (1584–1586). ✓
7. **U-25 markedPairing** vs ORIENTATION (11724–11730): ι^T(1−K)⁻¹bTot in the
   MuHat fence (no Add, no coercion), identification with markedVal only via
   the pinned W1m — μ̂-typed, never a density. ✓
8. **U-17b's §3c display** (1796–1800) carries `q₀ ∈ M.Pools →` — the R47
   repair holds; and U-18's Rsh = Σ_Ŝ (WshP Ŝ).val · shConv matches RS.1-SH's
   convolution display (12027–12028). ✓

## V6. The fresh 95-unit sweep and the census — EXACT

Recount by layer: S0 = {U-1..U-6, U-7a/b/c} = 9 ✓ · S1 = {U-8, U-9a, U-9b,
U-10} = 4 ✓ · S2 = {U-11, U-12, U-12b/c/d, U-13, U-14, U-15, U-16a1/a2/a3,
U-16b/c, U-17a/b, U-18, U-18b} = 17 ✓ · S3 = {U-19, U-20, U-21a/b/c, U-22,
U-22b/c, U-23a/b/c/d} = 12 ✓ · S4 = {U-24a1/a2, U-24b, U-25, U-27, U-28} = 6 ✓
· S5 = 15 (construction batch — the R54 "FIFTEEN" label verified by count) +
7 (b-i…vii) + 7 (b-viii…xiv) + 1 (b3) + 1 (c) + 4 (d-i…iv) + 1 (d2) + 4
(RS4Chain batch) + 3 (shallow-device batch) + 1 (d5) + 3 (NOTE-W6 checks)
= 47 ✓. Total 9+4+17+12+6+47 = **95** ✓.

Difficulty: easy = 19 named wave-2 core + 33 named S5 = **52** ✓ (both lists
counted element-by-element; every member's §3 tag agrees); medium = 27 core +
U-22b + U-22c + 14 named S5 = **43** ✓ (cross-checked: core medium by layer =
2+4+12+7+4 = 29 = 27+2); hard = **0** ✓ (no unit tagged hard anywhere; U-24a1
remains closed at medium per R14). Census line 52/43/0 CONFIRMED. Seam = 11
§W4-SYNC entries incl. ex-U-29d6, not built ✓. R54's other two items verified:
the E-phase scope sentence reads the current 95 (1886–1888); the
statement-fence reads "§2/§W4-SYNC" (1892–1893).

## Findings

**GAP-1 (§3 S5, lines 1703–1705 + ruling R52 lines 28–32).** `shWeightH` —
an RS4Chain DATA field (line 996) — has no owning device unit after the R52
split; REV 11's collective unit owned it by name, the three successor units'
field lists all omit it. Same class as Fable#9-G-1. Fix: add `shWeightH` to
`n2_sh_events` (the carrier unit).

**GAP-2 (lines 1690, 1695, 1094).** The retired unit name `n2_shallow_device`
survives at three LIVE sites after R52's rename/split: n2_rsh's body ("the
DEVICE WshP from `n2_shallow_device`" — should be `n2_wshp_device`) and deps
line ("deps: the d-batch, U-29d2, `n2_shallow_device`" — should be the three
split units), and §W4-SYNC S-8's field-source parenthetical. A dep on a
non-census unit name is the Fable#8-F3 staleness class; mechanical rename.

**O-1 (line 1470 vs 1474).** U-22's body says "U-22c is now CONSUMED" but its
deps line lists U-22b, not U-22c (and §3b carries no U-22b/c edges). Content
is unaffected — the PP-face is one-line derivable from U-22b + prime_sub — but
the dep bookkeeping contradicts R51's consumption claim; harmless either way.

## Verdict

**NOT ACCEPTED: 0 critical / 2 gaps / 1 observation.** Zero architectural or
mathematical findings — the convergent rev-11 list is genuinely repaired (R50
deletion verified correct and clean; R51 scope exact; R52's intent correct but
its execution dropped one field name and left three stale pointers; R53
declared at both sites; R54 all three verified). The two gaps are one-line
mechanical fixes; after them this auditor's residue is empty.
