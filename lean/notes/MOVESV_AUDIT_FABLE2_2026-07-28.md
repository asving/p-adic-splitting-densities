# MOVESV BLUEPRINT REV 2 — FRESH-INSTANCE AUDIT (Fable, round 2)

*(2026-07-28. Auditor: Fable fresh instance, zero conversation history. ARTIFACT:
`lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` REV 2, 2313 lines, read in full.
GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` 7829–9054 (§V-TABLES rev 7) read in
full + the S.0/(K-SUB)/CL-18 displays (11685–11800, 13337–13446); the built
`MovesS/Defs.lean` (559 lines) + `MovesS/Interfaces.lean` (130 lines) read in full;
`MovesSp/Defs.lean` (Species/CollapsedWalk/EntranceShape/rankNat signatures);
`MovesD/Defs.lean` (ShapeRead/ShapePrefix/A'/W/PrefIdx/Presented/fiber) +
`D10_sumLaw.lean`; the round-1 audits (`MOVESV_AUDIT_CODEX_2026-07-28.md` C1–C29,
`MOVESV_AUDIT_FABLE_2026-07-28.md` A-1–A-7); the MovesS blueprint REV 13 (R45/R50
rows) for cellP semantics. Charge: read, judge, fix nothing; quote and classify.)*

## VERDICT: REJECT — 6 critical / 4 gap

All six criticals cluster in ONE region: the counting-native measured wiring behind
the seam units (§2.F/§2.G/§2.H derived defs; V5-7, V7-4, V7-5, V7-6). The A2 chart,
the doctrine repairs, the EntIx carrier itself, the V6 gate layer, and the unit DAG
outside that region survived every check I ran (verified-clean list at the end).
The pattern of failure is uniform: **box-event cardinalities conflated with
instance counts, and count factors dropped at the resummed layer** — each time
inside a def or law the blueprint newly displays as a rev-2 "repair" of C23/C24.
The gate-B numbers the blueprint itself re-derives (V6-4a) refute four of the six.

---

## CRITICAL FINDINGS

### F-1 — `ιshH` (§2.G) is mis-normalized: its body computes ι·q^{n·entLvl−A}, not ι; `LedgerIV.init_count` becomes false at the intended instance

Offending display (§2.G, lines 808–814), docstring vs body:

> ιshH(ε̊, h, β₀) := I^ent(ε̊[h])(q₀) · q₀^{−A(ε̊[h])}
> ```
> ((V.entEvt (writeHeights ε̊ h) β₀ q₀ (V.entLvl ε̊)).card : ℝ)
>     * (q₀ : ℝ) ^ (-(((writeHeights ε̊ h).A : ℕ) : ℤ))
> ```

The docstring is the note's ι (V.1(iii): ι = Σ over marked prefixes of the C(b)
mass q^{−A}; gate B: ι = I^ent·2^{−3} = 2·(1/8) = 1/4). The body substitutes
`card (entEvt at entLvl)` for I^ent. But the entrance EVENT's card at level N is
I^ent·q^{nN−A} (V3-6(c)'s own D10 tie: each marked prefix's fiber has card
p^{nN−A'}; blueprint gate arithmetic V6-4a(b): event cards scale as 2^{3N−…}).
So body = I^ent·q^{n·entLvl−A}·q^{−A} = ι·q^{n·entLvl−A} — equal to ι only on the
razor's edge n·entLvl(ε̊) = A(ε̊[h]), which NO field imposes and which CANNOT hold
across the instantiations of any template whose A is non-constant on its listed
height domain (M4a displays A as AFFINE in h — e.g. every entrance threaded
through the A2 block, where the pin count grows with (h₀,h₂)), nor whenever
n ∤ A(h).

Failure scenario, concrete: gate B with the V6-4c threshold reading entLvl = 3:
card(entEvt at 3) = ι·2⁹ = 128; ιshH-body = 128·2^{−3} = 16 ≠ 1/4. Then MovesS's
`LedgerIV.init_count` (ιshH·|Box(N)| = card(entEvtH at N) eventually) fails at
N = 3: LHS 16·512 = 8192 ≠ 128 = RHS. V7-6's supply line "init_count ← V3-6's D10
tie + the §2.G ιshH DEF" is therefore false as displayed; V3-8/V3-9c/XHDsEnt sum a
quantity that is not the note's ι. (The C24(4) repair claim fails.)

### F-2 — `entInst`/`entCount` (§2.F) identify the ENT-COUNT polynomial with a box-event card: `RatBurdens.ι_count + ι_degT + degT_le` jointly unsatisfiable, V3-9a's `EntCount` false at the intended instance

Offending display (§2.F, lines 673–681):

> `entInst i q₀ N := V.entEvt (writeHeights i.1.1 (component base)) β₀ q₀ N`
> `entCount i q₀ := (V.entInst i q₀ (V.entLvl i.1.1)).card`

The note (V.1(iii)): "I^ent_{ε,β₀}(q) := #{realized shallow entrance prefixes of
shape ε whose continuation lands in β₀} — a MARKED count … one polynomial in q of
degree ≤ W_ent(ε)". A prefix COUNT, not a box census. With the blueprint's def,
entCount(q₀) = I^ent(q₀)·q₀^{n·entLvl−A(base)}. `RatBurdens.ι_count` (no activity
guard, ∀ q₀ ∈ Pools — infinitely many points) forces `ιP.countT` to interpolate
exactly that function, so natDegree = Went + (n·entLvl − A(base)) whenever
n·entLvl > A(base) — contradicting `ι_degT` (degBoundT = Went) + `PolyGeom.degT_le`.
Gate-B numbers with entLvl = 3: entCount(q₀) = q₀(q₀−1)·q₀⁶, degree 8 > Went = 3.
With n·entLvl < A(base) the event is undetermined at that level and the card is not
the count either; equality demands n·entLvl = A(base) exactly — unconstrained, and
even then only at the base h (see F-1's affine-A argument for the rest of the
component). So `ent_count_card` is rfl but ties the WRONG object, and V7-5(c) /
V3-9a cannot be satisfied at the intended instance. The correct carrier is the
marked-prefix census (MovesD `PrefIdx`-side, D4R.4's finite level-N residue census
of the marks), which `CtsMeasured` does not carry.

### F-3 — the C24(2)-cluster ties are still missing AS TYPES: `meas_card`, `xhd_no_stray`, `xhd_no_orphan`, `d4r0` have no derivation from any displayed field

V7-6 claims (lines 2059–2065): "meas_card ← the counting law gwt·|Box| = |cellEvt|
eventually: … the per-assignment box-count law is the C15/XHD-w counting semantics
(X.w.w_eq + evtOf card at stabilized levels — the C24(2) tie, now derivable)".
It is not derivable: `w_eq`/`mass_factors` tie `massOf` to q^{−E}/F(inv); **no
field anywhere ties `evtOf`'s cards to `massOf`** (evtOf's only law is `evt_disj`).
"evtOf card at stabilized levels" names a law that exists in no structure.
Likewise:
- `xhd_no_stray`/`xhd_no_orphan` (MovesS: h ∈/∉ HDom c ⟷ cellEvt eventually
  nonempty / empty at ALL N) need CELL-level domain exactness — h ∈ cdom(mv,c) ⟷
  cntc(c,h) > 0 — but the XHD bundle has a d-face for TEMPLATES (`XHDd`) and for
  ENTRANCES (`XHDdEnt`) and NONE for digit cells (`XHDsC` is sums only; §2.F's
  comment "the [2b] packages assert their EXACTNESS" points at nothing typed);
  plus again the count→event-nonemptiness tie.
- `d4r0` (disjointness for (c,h) ≠ (c′,h′)) is claimed from "evt_disj + cellOfA",
  but `evt_disj` is same-(x,h)-across-assignments only; cross-HEIGHT disjointness
  of box events (h ≠ h′, same cell) follows from no displayed law.
Recurrence of C24 under a "REPAIRED" disposition-table entry: the ledger walk the
charge demanded fails on four of the nine inputs.

### F-4 — `XHDsC.cell_refine` equates count-bearing cell sums with the count-free template sum; V7-4's `kstep` drops the count factor; `kstep_one` unsatisfiable

Offending displays: §2.G (lines 771–772)

> `cell_refine : ∀ {αc βc} (mv : S.Move αc βc), (∑ c, ∑ j, Gcell mv c j) = ∑ j', Xs.Gc (.last mv) j'`

and V7-4 (lines 1986–1990)

> `kstep k τ β q₀ := Σ_{γ : length-k kcol templates τ→β} Σ_j evalAt (X.s.Gc γ j)`

`Gcell` sums cntc·g (Gcell_hasSum — count-bearing, the note's per-cell resummed
mass); `Gc` sums ∏g alone (Gc_hasSum over gProd; the note's XHD-s display
"Σ_h ∏ g_i(h_i)" — count-FREE, exactly so that the row is T·G with T separate).
cell_refine therefore forces T ≡ 1. Gate counterexample (A2): one digit cell,
count (q−1)²: Σ Gcell = (q−1)²·G ≠ G = Σ Gc. Correct identity: Σ_c Σ_j Gcell =
T_mv·Σ_j Gc — the count factor is dropped. Same drop in `kstep`: MovesS's
`kstep_one` demands kstep 1 τ β = Σ_{kcol o → β} rowVal o (count-bearing:
s_blk2 → β₁ gives (q−1)·G), while the def evaluates to G. The C24(3) supplier is
broken, and with it V7-6's kstep_one/hmc legs.

### F-5 — V7-5(d)'s rev-2 re-keying `cellP ← CellPolyPack` contradicts the frozen `RatBurdens`: `cellP_deg` violated at both gate blocks and `act_iff` false at q₀ = 2

Offending line (V7-5): "(d) `cellP` ← CellPolyPack (per DIGIT CELL — MovesS's
cellP_count demands the cell-instance card, NOT the state size; rev 1's sizeP
wiring was the wrong granularity, corrected here)".

Frozen MovesS: `cellP_deg : natDegree ≤ T.Wstate e τ`; MovesS blueprint R45 pins
the semantics: "PER-CELL **size** polynomials — 'EACH CELL SIZE one polynomial of
degree ≤ W_state(s)'", cellInst = "instance events whose card IS the cell size".
`CellPolyPack.deg` gives ≤ Wloc, and the blueprint's OWN V2-10(a) records
Wloc > Wstate at both gates (root 3 > 0; s_blk2 2 > 1) — digit-cell COUNT
polynomials (TH3 degree 3; (q−1)(q−2)/2 degree 2) cannot satisfy cellP_deg.
Worse, `act_iff` (active ⟺ ∀ c, cellP(c).eval q₀ ≠ 0) becomes FALSE at q₀ = 2
with count-valued cellP: the root state is active at 2 (|α₀| = 1; act_size), yet
the m_H3 digit cell's count evaluates to 0 there — the blueprint's own celebrated
falsifier refutes its own wiring. The rev-1 sizeP wiring satisfied all four cellP
laws (deg ≤ Wstate ✓, nonzero ✓ post-deletion, act_iff = the note's (ii) activity ✓,
cellP_count ✓ with cellInst = the state-instance census); round-1 C23 never named
cellP — this "correction" is a rev-2 regression. Note also: the supply line
"cellLvl/cellInst ← the stabilized level + cellEvt at it" references a per-cell
stabilization level that is NO field of `CtsMeasured` and an event that needs
(x, h) arguments cellInst does not have — the C7 repair is incomplete on exactly
the fields Codex listed as absent.

### F-6 — §2.H's `roster_tie` (bcells ⟺ emult ≥ 2) mis-defines the note's J: at n = 3 the blueprint's OWN V4-8 empties every roster, making Jval ≡ 0 and `j_interp` unsatisfiable

Offending display (§2.H): `roster_tie : … c ∈ bcells s m o α ↔ 2 ≤ emult V c`,
with `emult` = "the cell's eligible continuing-mark count" (the same emult V4-7's
surplus and V4-8's n = 3 census use).

The note (S.0/CL-18, 11691–11704): "J_{τ,o}(q) := the CELL-LEVEL resummed
branching mass — the sum, over the branching digit CELLS of outcome class o at
state τ, … EACH CELL ONCE. [o branching := the (c ≥ 1, m ≥ 2) row of (K-SUB)'s
(m, c) CLASSIFICATION]". "Branching" classifies the OUTCOME o, not a sub-roster of
its cells: (K-SUB)'s arithmetic (Σ_β K + Σ b^term + Σ_o J_{τ,o} = 1 = PART-1's
total over ALL cells) forces J_{τ,o} = the FULL cell mass of every split-route
outcome. The blueprint instead keeps only cells with ≥ 2 CONTINUING marks. These
differ everywhere at n = 3: V4-8 proves emult ≤ 1 over the whole gate roster, so
bcells = ∅ and Jval ≡ 0 — while the note's J at the root's m_2+1 outcome (m = 2,
c = 1: a split route with T = q(q−1)) is nonzero and is what `RatBurdens.j_interp`
must equal (rowVal at split routes, = MovesS's "the J cell-sum for split").
V5-7b/V7-5(b) are unsatisfiable as specced, and the §2.H carrier contradicts the
blueprint's own V5-7c algebra "(J + surplus = marked row)", which holds only for
the all-cells-once J. (The C8 repair fixed the (τ,o)-keying but broke the roster.)

---

## GAPS

**G-1 — misquoted display.** §0 repair-1 "(E = 6t+3u+1, the note's own display)"
and §2.I "per the note's own chart display \"E = 6t + 3u + 1\"" — the string
"6t+3u+1" appears NOWHERE in the frozen note (grep-verified). The note displays
E = (3(h₀+h₂)−1)/2 and the domain substitution "h₂ = t ≥ 1, h₀ = 3t + 2u + 1"
(line 8844); the (t,u) form of E is a (correct) derivation, not a display. V0-4's
moves_ref splices "= 6t+3u+1" into a quotation of V.6.2. Citation-integrity only —
the mathematics is right (see clean list).

**G-2 — F9 misdescribed.** §2.I calls x²+1 over F₃ a "standard Conway-polynomial
table"; the Conway polynomial C_{3,2} is x²+2x+2. Any irreducible works for the
census, but the provenance claim is false as stated.

**G-3 — the u\*-slot encoding is unpinned.** `EntTemplate.entDim` allots ℕ-slots
"two height slots (h_r, u*_r) per letter", but `MovesD.ShapeRead.ustar : ℚ`.
`writeHeights` must reconstruct a ℚ from an ℕ slot; no encoding (or determination
of u\* from prior reads) is displayed, and V3-5's bijection (both horns) leans on
it. E-phase risk on a HARD unit, undeclared.

**G-4 — pointer imprecision.** V3-6(c) cites "MovesD.thmC_top via D10's `key`";
`key` is a proof-internal `have` in `D10_sumLaw.lean` (not exported). The
consumable statements are `D4R1_SUM`/`D0b_thmCtop`.

---

## VERIFIED CLEAN (the charge's six probes, what passed)

1. **A2 chart (C3 repair) — CORRECT, fully re-derived.** chart(t,u) = (3t+2u+1, t):
   base ![1,0] ↦ (4,1) ✓; E(t,u) = 6t+3u+1 pulls back exactly to (3(h₀+h₂)−1)/2
   (12t+6u+3−1)/2 ✓; the division-free display identity 2·EA2.eval h =
   3(A2chart h 0 + A2chart h 1) − 1 is an exact ℕ-identity ✓; sealed E = 7 at
   (4,1) ✓; V6-2a's image set {h₂ ≥ 1, h₀ > 3h₂, h₀−h₂ odd} = the chart image
   (parity: h₀−h₂ = 2t+2u+1; strictness: h₀−3h₂ = 2u+1 ≥ 1; surjectivity via
   u = (h₀−3h₂−1)/2 ∈ ℕ) ✓; L((4,1);{(3,1),(2,0)}) = the image of the (t,u)
   lattice ✓; V0-4's GA2 = X²/((X⁶−1)(X³−1)) is the exact cleared double
   geometric sum q^{−7}/((1−q^{−6})(1−q^{−3})) ✓, denominator in the PolyGeom
   class ✓. No half-integral arithmetic survives. (Only G-1's attribution wart.)
2. **Doctrine repairs (C1/C2/A-2).** The empty-StepSys adversary FAILS: Cell :=
   Empty violates `cell_ne`; empty histories violate `hist_ne`; unrealizable cells
   violate `zc_ne`; menu-less states violate `out_ne`. `cntraw :=
   Fintype.card (Assign m x h)` is tied by definition ✓. `chainCount` encodes the
   note's V.0 definition "T_γ(x,h) := #{fresh-assignment chains from x realizing
   (γ,h)}" faithfully: base = cntraw/cntrawT, cons = Σ_a chainCount(γ, ext a,
   drop h) — chains ARE iterated extensions, and `ext`+`ext_zc` is the right
   carrier ✓. XHDd's exactness now quantifies over the real count ✓ (a junk-domain
   XHDd violates no_orphan at any realized height).
3. **EntIx carrier (A-1).** finE suppliable: Finite (EntTemplate n) is genuinely
   intrinsic (hWalk = CollapsedWalk's exact chain condition, verified against
   `MovesSp/Defs.lean:172`; rankNat strict increase along collapsed edges =
   SP4_dagWords; hEntry types against `Species.sel : Option (ℕ × ℕ)` ✓;
   selRec bounded by hlen/hmenu ✓) × Fin (comps.length) × decidable entLands ✓.
   The V3-3(c) bridge target `MovesSp.EntranceShape n gsel μsel` exists with
   word/hMem/hChain/hEntry ✓. The `hent : ℕ` adjudication is source-verified:
   no law in MovesS Defs/Interfaces reads `MeasuredSide.hent` (RS1Meas's h_ent
   argument is an independent ℕ) ✓; seam flag SF-1 is the right record. The
   carrier is right; what breaks is the counting DEFS over it (F-1/F-2).
4. **V6 gate layer.** censusQ = [2,3,4,5,7,8,9,11,13] = the note's nine ✓. All
   five root closed forms match V.6.1 (C(1/6)X(X−1)(X−2) etc.) and sum to X³
   (recomputed) ✓; the m_H3 row 0,1,4,10,35,56,84,165,286 recomputed at all nine
   q ✓ incl. the q = 2 falsifier ✓; s_blk2 forms match V.6.3, sum to X(X−1) ✓,
   split/inert/double counts re-derived combinatorially and all 27 evaluations
   match the note's table ✓; the A-4 repair is correct: f″ = 6z + 2a ≡ 0 (mod 2)
   makes the derivative test unusable at p = 2, and the (z−r)^k ∣ f divisibility
   predicate is char-free ✓; F4/F8/F9 constructions are legitimate fields (x²+x+1,
   x³+x+1 over F₂; x²+1 irreducible over F₃) ✓ (G-2 provenance wart); gate-B
   numbers all check: ι = 2·2^{−3} = 1/4, T_{o_double}(2) = 1, g = 2^{−3},
   μ̂ = 2^{−5}, shadow = 2, marked pairs 2^{3N−5} ↦ 16/128, I^ent = q(q−1) =
   q·|β₀| ✓; V6-4c's CoprimeLiftPack fields (unique coprime lift + determinacy,
   nothing stronger) match the note's displayed Hensel sentence ✓; h₀ ≡ 4 mod 8 /
   h₁ ≡ 0 mod 4 are the note's level-3 predicates ✓. V6-4c correctly excluded
   from §0's proved-outright banner (A-6 held) ✓.
5. **Seam-supply table.** Field lists verified verbatim against the built
   `MovesS/Defs.lean`: TableShape (VLabel = the vEquiv target subtype ✓), DegCons,
   KmatHyp (a Prop ✓ — C25's correction accurate), SCSData 12 data + 12 laws all
   named ✓, MeasuredSide all fields incl. the C7 pool laws ✓, RatBurdens/LedgerIV
   field names exact ✓, RS1Meas/RS1Bundle/RS4Chain/ReadOffBundle rows consistent
   with `Interfaces.lean` ✓. The §4.3 re-keyings amend only seam pins (no E-phase
   file for §W4-SYNC — verified in Interfaces.lean header) ✓; xhdStmt = ONE
   bundle Prop resolves C27 ✓; wsh_xhd_s_stmt + the tree_ne routing resolves C26's
   shape ✓. The table's CONTENT fails only where F-1..F-6 break the named
   suppliers (MeasuredSide row, RatBurdens ι/j/cell rows, LedgerIV row).
6. **71-unit sweep.** Count exact: V0[4] V1[8] V2[10] V3[11] V4[12] V5[9] V6[10]
   V7[7] = 71; difficulty census 31/35/5 recounted per unit and exact ✓; delta vs
   rev 1 (+V1-8 medium, V3-8 easy→medium) consistent ✓. Statements checked against
   their moves_refs across all layers; beyond the six findings no unit misstates
   its display or silently strengthens/weakens (V2-5's u_R/u_T route ✓, V2-8's
   structural part_eq ✓, V3-4 hypothesis-free ✓, V4-1's guard ✓, V4-6's four legs
   verbatim ✓, V4-8's ContTwo ✓, V4-12's one-directional adjudication ✓, V5-2/
   V5-4/V5-5/V5-6's ledger tags verbatim against V.1/V.4 ✓, V7-2's (v)-has-no-
   conclusion-field ✓). Round-1 dispositions spot-checked: C1–C6, C9–C22, C25–C29,
   A-2–A-7 genuinely repaired in the text; the false "REPAIRED" rows are C24
   (→ F-1/F-3/F-4), C23's cellP leg (→ F-5), and C8's roster (→ F-6).

## Note for the next revision (adjudication hints, not fixes)

The six criticals share two root causes and likely two mechanical remedies:
(i) an INSTANCE-CENSUS carrier distinct from the box events (the marked-prefix
census at level N — D4R.4's object) with the counting law card(event at N) =
count·q^{nN−A} as a typed field — this repairs F-1/F-2/F-3's meas_card face at
once (and the same law at cell level, plus a cell d-face and cross-(c,h)
disjointness, repairs the rest of F-3); (ii) the count factor restored at the
resummed layer (cell_refine = T·ΣGc; kstep with ∏T) — F-4; plus reverting cellP
to the sizeP wiring (F-5) and re-keying bcells to routeOf = split (F-6).

*(End of round-2 fresh-instance audit. REJECT: 6 critical / 4 gap.)*
