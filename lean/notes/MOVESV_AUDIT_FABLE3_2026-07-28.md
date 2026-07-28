# MOVESV BLUEPRINT REV 3 — FRESH-INSTANCE AUDIT (Fable, round 3)

*(2026-07-28. Auditor: Fable fresh instance, zero conversation history. ARTIFACT:
`lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` REV 3, 3107 lines, read in full.
GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` 7829–9054 (§V-TABLES rev 7) read in
full + the S.0/(K-SUB)/CL-18 displays (11685–11745); the BUILT
`MovesS/Defs.lean` (559 lines, read in full — TableShape/SCSData/DegCons/
MeasuredSide/LedgerIV/RatBurdens/PolyGeom/Kmat/PoolHyp/AVAgree verbatim) +
`MovesS/Interfaces.lean` (130 lines, read in full); `MovesD/Defs.lean`
(ShapeWF.gamTie/anchorTie, selRank, EligibleImage, mbar) + `D10_sumLaw.lean`
(`D4R1_SUM` exported statement) + E5/E6/E8/E9 name checks;
`MOVESS_LEAN_BLUEPRINT_2026-07-28.md` §W4-SYNC (S-5/S-8, W7_cutWD, TreeIface.
tree_ne, Wsh17Package fields) for the SF-2 adjudication; the git pair
f2f98c7 (REV 2) → 39862fc (REV 3) for byte-stability; the round-1/2 audits
(CODEX C1–C29, CODEX2 1–20, FABLE A-1–A-7, FABLE2 F-1–F-6/G-1–G-4).
Charge: re-run all six round-2 F-refutations; adjudicate SF-1/SF-2; verify the
V4-12 iff; byte-stability of the verified-clean cores; the 82-unit splits;
fresh sweep. Read, judge, fix nothing; quote and classify.)*

## VERDICT: REJECT — 3 critical / 2 gap

**All six round-2 F-refutations DIE against the rev-3 wiring** — every
displayed acceptance number checks (§B below), and the two seam-flag
adjudications are honest. The rejection is carried by THREE findings the
fresh sweep produced, none of them a recurrence of a round-2 item: two are
INHERITED defects that sat byte-identical in the rev-2 text through both
round-2 passes (the byte-stability check localizes them), one is a
definitional hole in the rev-3 kstep re-key. All three are E-phase hard
blockers on the V4/V7 assembly; the entrance/census cluster that rev 3
rebuilt is, by itself, correct.

---

## CRITICAL FINDINGS

### N-1 — `XHDd` + the definitional `chainCount` PROVE the open kernel: `HMC S D` is a THEOREM for every instance; V4-11's false-HMC toy and V4-12(c)'s fence are unsatisfiable; the (v)-conditionality architecture is formally defeated

Offending displays (§2.G; byte-identical since REV 2):

> ```
> no_orphan : … 0 < chainCount S γ x h → (dom γ).Mem h
> no_stray  : … (dom γ).Mem h → ∀ x : S.Hist α, 0 < chainCount S γ x h
> ```
> ```
> | _, .cons m γ, x, h =>
>     ∑ a : S.Assign m x (Hpt.take h), chainCount S γ (S.ext m x _ a) (Hpt.drop h)
> ```
> ```
> def HMC … : Prop := ∀ … (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔
>   (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂
> ```

Proof that `∀ S D, HMC S D` (four lines, both directions; uses only XHDd's
own fields + `hist_ne` + `finA` + `Fin.append_left/right`):

- (→) Mem(cons)(h₁++h₂): pick x₀ from `hist_ne`; `no_stray`(cons) gives
  0 < Σ_a chainCount γ (ext a) h₂, so `Assign m x₀ h₁` is NONEMPTY
  (⟹ cntraw > 0 ⟹ `no_orphan`(last m): h₁ ∈ dom) and SOME term is positive
  (⟹ `no_orphan`(γ) at the extended history: h₂ ∈ dom γ).
- (←) h₁ ∈ dom(last m), h₂ ∈ dom(γ): pick x₀; `no_stray`(last m) makes
  `Assign m x₀ h₁` nonempty; for each a, `no_stray`(γ) at `ext m x₀ h₁ a`
  makes chainCount γ (ext a) h₂ > 0; the sum is positive; `no_orphan`(cons)
  puts (h₁++h₂) in dom(cons). ∎

The C2/A-2 repair (chainCount a DEF, exactness quantified over it) plus the
note's own ∀-representative no-stray quantifier make the composite domain
EXACTLY the product — HMC's iff, both horns. Consequences, each concrete:

1. **V4-11 is unsatisfiable as specced**: "a toy StepSys with a 2-step
   template where `HMC` is FALSE (a coupled domain)" — no `D : XHDd n S`
   with false HMC exists; the false-instance leg cannot be built.
2. **V4-12(c) is unsatisfiable**: "at V4-11's false-HMC toy instance, ONE
   DISPLAYED weight system where the identity FAILS" — no false-HMC
   instance; moreover `FactorizesAll S D` is itself a theorem (via (a) +
   the HMC theorem), so no failing weight system exists at ANY instance.
   The gloss "the ∀-E quantifier in (a)/(b) is NOT removable (a
   single-system iff would be false — round-1 C19's content)" is now
   mathematically false: given the definitional count, dom(cons) ⊆
   dom(last)×dom(γ) always (the (→) computation above), and a positive-
   weight sum over a subset equal to the sum over the superset forces set
   equality — the single-system iff is TRUE. C19's falsifier lived in
   rev 1's FREE-chain regime and did not survive the rev-2 repair; the
   fence was carried forward without re-derivation.
3. **V4-12(b) is trivially provable** (HMC is true), so the HARD grading,
   the pre-approved (b-i)/(b-ii) generating-series split, and §0's banner
   line "the ⟹ leg the generating-series separation — HARD" describe a
   vacuity; the §5 HARD set and the difficulty census are keyed to it.
4. **The (v)-conditionality pin is defeated.** §0: "(v) HMC: OPEN KERNEL …
   NO unit proves them"; V7-4c: "LedgerIV.hmc stays V5-5's conditional
   content"; V7-6c: "hmc ← … hHMC explicit — no unconditional instance
   until (v) closes". Every consumer holding the XHD bundle (i.e. EVERY
   measured unit) can discharge `hHMC := hmc_theorem S X.d` — the corpus
   can prove the note's open kernel from [2b]'s package alone, which the
   frozen note explicitly refuses ("Until HMC closes, K_e(p)^k is NOT a
   theorem about the process", V.1(v)/V.5(2)). The hypothesis ledger the
   corpus exists to encode EXACTLY ({XHD-d} vs {XHD-d, HMC}) collapses;
   per the campaign doctrine "their TYPES must pin their content", HMC's
   type pins TRIVIAL content. `HMCAug` is likewise trivialized (any
   Refinement carrying any XHDd witnesses it), undoing the X-13 repair's
   point.

NOTE-SIDE FLAG (for the owners, not a blueprint duty): the same four-line
argument reads against the FROZEN note's own displays (V.0's (no stray)
"for EVERY representative x of α" + the T_γ chain recursion) — the note's
XHD-d appears to imply its (v), making the V.1 ledger's (COMP-hΣ)-vs-
(COMP-Σ) distinction empty. Either the note intends a weaker no-stray
quantifier at composite templates (then the blueprint's XHDd is a silent
STRENGTHENING and must be re-keyed), or the note carries a latent
redundancy that [2b]/[1v] must adjudicate before any faithful HMC
formalization exists. This is exactly a statement-fence matter: do NOT
repair it silently on the blueprint side.

### N-2 — the StepSys count layer is POOL-FREE while its laws quantify over the infinite `Pools`: `ValA.tbl_count`/`tgt_supported`, `CellPolyPack.count/countT`, V2-5(b), V5-3, and the §2.F event architecture force CONSTANT count polynomials — refuted by the gate tables; `valA_gate` and the V7-5/V7-6 instantiations are unsatisfiable at the intended instance

The carriers (§2.B): `Hist : Cell → Type`, `Assign : … → Type`,
`cntraw … : ℕ := Fintype.card (Assign m x h)` — NO pool index anywhere.
Offending law (V2-4(a), REV-3 re-key):

> `tbl_count : ∀ (d : MoveData n C) (β) (x : S.Hist _) (hzc : S.zc x)
> (q₀ ∈ V.Pools) (j …), ((C.T d.s d.m d.o d.α β).eval q₀ : ℚ)
> = S.cntraw (V.moveOf d) x (((V.mdom d).comps.get j).base)`

Fix x (exists: `zc_ne`) and j; the right side is ONE natural number; the
law forces `T.eval` CONSTANT on the infinite `V.Pools` (`pools_infinite` is
a CtsMeasured field), i.e. every table polynomial constant. Gate failure:
`T21 = X(X−1)` has eval 2 = 2 ≠ 6 = eval 3 — so the deferred
`theorem valA_gate : ValA 3 gateFam gateMeas` is FALSE, not merely open.
The same q₀-free count poisons, field by field:

- `CellPolyPack.count` (§2.H): `(P …).eval q₀ = V.cntc d x c h` ∀ q₀ ∈
  Pools — the A2 digit cell's count polynomial (X−1)² gives 1 = cntc at
  q₀ = 2 and 4 = cntc at q₀ = 3, one ℕ. Unsatisfiable; with it die V5-8's
  displayed derivation route ("Σ_{c∋h} P_c.eval = Σ_c cntc = cntraw"),
  V7-6a's meas_card leg ("P_c.eval = cntc on the domain"), and V7-5(a)'s
  tgP leg.
- `ValA.tgt_supported`: "¬ V.activeState q₀ β → S.cntraw … x h = 0" —
  inactivity at ONE pool kills the q₀-free count at ALL pools (the m_H3
  target is inactive at q₀ = 2 with nonzero counts at q₀ = 7).
- V2-5(b) `valB`: `(chainCount S γ x h : ℚ) = (pathProdPoly C γ).eval q₀`
  — same collapse at the path level; V5-3's count shadow inherits it.
- THE DEEPER HORN (no CellPolyPack needed): `cellEvt` is DEFINED (§2.F) as
  the biUnion over the q₀-free `Assign` fiber, and `evt_card` gives
  card(evtOf a q₀ N) = massOf·|Box| — so card(cellEvt q₀ N) =
  cntc·g·q₀^{nN} with cntc ONE number across pools, while the intended
  instance's cell-event cards scale as count(q₀)·q₀^{nN−E}. The
  conjunction {cellEvt-def, evt_card, evt_disj, LedgerIV.meas_card} is
  unsatisfiable at any instance with a non-constant cell count. The REV-3
  census repair (entInst/stInst, box-side, correctly q₀-indexed — F-1/F-5)
  stopped exactly one layer short: the CELL/assignment layer kept the
  pool-free carrier.

Two-horn closure (no reading escapes): if instead `Hist` is meant to
bundle the prime (x determines q₀), then `XHDu.u_R_cnt` (∀ x x',
cntraw m x h = cntraw m x' h) forces CROSS-PRIME count equality — false at
the intended instance (2 ≠ 6) — i.e. the [2b] hypothesis package becomes
uninstantiable instead. V2-4's own horn text ("at an entry inadmissible at
q₀ the base counts are 0") shows the intended semantics is q₀-varying
counts; the displayed types do not deliver it. Inherited verbatim from
rev 2 (rev 2's `tbl_count` had the same `S.cntraw` right side under a
`0 < cntraw` guard); both round-2 passes checked degree ledgers and
normalizations at ONE pool and never evaluated a count tie at two.

### N-3 — V7-4c's `kstep` has no k = 0 case: the template-sum def gives kstep 0 ≡ 0, falsifying the frozen `LedgerIV.hmc` at k = 0

Offending display (V7-4c):

> `kstep k τ β q₀ := Σ_{γ : length-k kcol templates τ→β}
> ((pathProdPoly C γ).eval q₀ : ℝ) · Σ_j evalAt (X.s.Gc γ j)`

`Template n S` has constructors `last/lastT/cons` — minimum length 1; there
is NO length-0 template, so the k = 0 sum is empty and `kstep 0 ≡ 0`. The
frozen law (`MovesS/Defs.lean` 243-244) quantifies ∀ k:

> `hmc : ∀ (k : ℕ) …, M.kstep (k + 1) e τ β q₀
>   = ∑ γ : T.State e, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀`

At k = 0 it forces `kstep 1 e τ β q₀ = Σ_γ 0 · kstep 1 = 0` — false at any
active pool with a nonzero kcol row (s_blk2's o_double: T_dbl(2) = 1 ≠ 0,
`kstep_one` pins kstep 1 to that row). The built MovesS device instance
documents the requirement the def misses (`N2Carriers.lean` 102: "so
kstep 0 = 1 and the HMC scalar law … holds"; `kstep := (…)^k`). Repair is
one line (kstep 0 := the Kronecker δ — the empty path's ∏T = 1, empty
height sum = 1), but as DISPLAYED V7-6c's hmc leg is unprovable and the
LedgerIV instance fails. (The k ≥ 1 recursion itself is fine given hHMC:
regroup length-(k+1) templates as prefix∘last and factor by V4-12(a).)
Present in rev 2's kstep display too; the F-4 re-key added ∏T without
touching the k = 0 hole.

---

## GAPS

**G-1 — V7-5(d)'s act_iff collapse silently needs `Nonempty (Cell e τ)`.**
"act_iff ✓ ← act_size (… with cellP constant in c the ∀-c iff collapses to
act_size)": the ⟸ direction (∀ c, sizeP.eval ≠ 0 → active) is VACUOUS at a
state with an empty cell type unless `Cell e τ = Σ o, DCellO (dataOf τ o)`
is inhabited. It IS derivable (zc_ne + the REV-3 productivity out_ne +
cellOfA/cellOfAT through moveOf_bij give an inhabitant at every state), but
no unit displays or claims this step — an E-phase surprise on a REVERT site
that was sold as "satisfying all four frozen laws".

**G-2 — V7-6a bundles SIX supply legs under the ≤ 4-lemma roster rule.**
The §3 preamble (C28 amendment) pins "an ENUMERATED LEMMA ROSTER (≤ 4
lemmas; each lemma one display)"; V7-6a derives six LedgerIV fields
(meas_card, xhd_no_stray, xhd_no_orphan, d4r0, init_count, ent_count_card)
with no roster declaration. Read as one suite-theorem it is one display;
read as lemmas it violates the rule the same revision installed. Declare
which.

---

## A. THE SIX ROUND-2 F-REFUTATIONS, RE-RUN — ALL SIX DIE

1. **F-1 (the gate-B 128) DEAD.** `ιshH := entCensus·q₀^{−A}` (§2.G) with
   the census carrier `entInst` + the typed law `ent_card` (card(entEvt at
   N)·q₀^A = census·q₀^{nN}, N ≥ entLvl). Recomputed: census I^ent(2) = 2;
   card at N = 3 is 2·2⁶ = 128; 128·2³ = 1024 = 2·2⁹ ✓; ιshH = 1/4;
   ιshH·|Box(3)| = (1/4)·512 = 128 = card ✓ (never 8192). `LedgerIV.
   init_count` (built shape: ∃N₀ ∀N ≥ N₀, ιshH·|Box| = card(entEvtH))
   derives with N₀ := entLvl from ent_card + box_card — shapes verified
   against `MovesS/Defs.lean` 251-254. The 128-vs-16 split (entrance event
   2^{3N−2} vs marked pairs 2^{3N−5}) is consistent with the note's V.6.4.
2. **F-2 (degree vs Went) DEAD.** `entCount` := the census; V3-9a/V3-9b
   re-keyed per CONCRETE ε against `entCensus`; the ι-ledger
   (ι_count/ι_countS_one/ι_degT/degT_le, built shapes verified) is jointly
   satisfiable GIVEN EntU/EntCount: countT := the (ENT-U) common census
   polynomial, gate degree 2 ≤ Went = 3 ✓; ι_interp = countT·1·Gent
   matches V7-4b's ιsh := entCount·evalAt(Gent) ✓.
3. **F-3 (the C24(2) suite as types) DEAD.** All four legs now derive
   field-by-field into the FROZEN LedgerIV shapes: meas_card (guarded by
   h ∈ HDom ✓) ← evt_card + w_eq + cp.count + no_strayC; xhd_no_stray ←
   no_strayC + evt_card + g > 0; xhd_no_orphan (unguarded ∀ q₀ N ✓) ←
   no_orphanC contrapositive + the biUnion def; d4r0 (cross-cell AND
   cross-height AND cross-outcome, one x ✓) ← the ONE AStep disjointness
   law + cellOfA + moveOf_bij. Derivability as TYPES is repaired; the
   INSTANTIABILITY of the cp.count input is the new N-2 — a different
   defect, recorded there.
4. **F-4 (the (q−1)² adversary) DEAD.** XHDsC/XHDsEnt re-keyed WEIGHT-ONLY
   (Gcell_hasSum/Gent_hasSum sum g alone — verified no cntc factor, no x);
   `cell_refine` demoted to the DERIVED unit V5-8 with the count factor on
   both sides (Σ_c P_c·ΣGcell = T·ΣGc): at A2, LHS = (q−1)²·G = TA2·G =
   RHS ✓ — no T ≡ 1 forcing. The identity is TRUE as displayed (Fubini
   over nonneg terms + the cell-partition of cntraw + u_T/tbl_count);
   its listed proof route crosses N-2. kstep carries ∏T (pathProdPoly);
   kstep_one = V5-8's length-1 identity ✓ (but see N-3 for k = 0).
5. **F-5 (cellP_deg + the m_H3 cell) DEAD.** cellP REVERTED to sizeP;
   stLvl/stInst/stInst_card added (box-side, correctly q₀-indexed).
   Against the frozen fields: cellP_deg ≤ Wstate ✓ (size_deg transported);
   cellP_nonzero ✓ (CellIdx post-deletion); cellP_count ✓ (stInst_card IS
   the demanded card law, activity-guarded either side); act_iff ✓ at
   q₀ = 2 (root active, sizeP ≠ 0, while the m_H3 DIGIT cell's emptiness
   contradicts nothing — cellP no longer reads digit-cell counts) — modulo
   G-1's undisplayed nonemptiness step. The rev-2 ActIff premise struck ✓.
6. **F-6 (gate-roster Jval) DEAD.** roster_tie re-keyed to
   `c ∈ bcells ↔ route = split` — verified FAITHFUL against the S.0/CL-18
   display (11700-11704: "the sum, over the branching digit CELLS of
   outcome class o …, EACH CELL ONCE", with "[o branching := the (c ≥ 1,
   m ≥ 2) row of (K-SUB)'s (m, c) CLASSIFICATION]" classifying the OUTCOME,
   and J's supply "= (iv)-PART-1's digit-cell partition" = ALL cells).
   Jval = Σ over ALL cells of count-poly × weight-sum = rowVal for split
   routes — exactly `j_interp`'s demand (built shape verified); the root's
   m_2+1 outcome gives the nonzero gate value ✓; V5-7c's algebra carries
   its (c ≥ 1) roster premise DISPLAYED ✓; route_eq ties to `MovesS.
   routeOf` (Route kcol/termFin/split — dispatch verified compatible) ✓.

## B. THE REMAINING CHARGE ITEMS

- **SF-1 (hent retained) — HONEST.** Re-verified at source: `grep hent
  MovesS/*.lean` shows the field declaration (Defs 179), the RS1Meas
  h_ent argument as an INDEPENDENT ℕ (Interfaces 36-37), and one device
  instance assignment — NO law reads `MeasuredSide.hent`. The V7-4b record
  states the round-2 disagreement, the resolution basis, the binding rule
  for MovesT, and the re-open trigger. Nothing is hidden.
- **SF-2 (owner-side open) — HONEST.** Verified against the MovesS
  blueprint §W4-SYNC: S-8's empty-menu demand ("F.Sh.Nonempty, or premise
  W7's tree_ne through S-5") is genuinely [3t]-side — `tree_ne` exists
  only in the unbuilt contract shapes (Interfaces.lean header: "§W4-SYNC
  … NOT built at E-phase"), and the displayed `W7_cutWD` still carries the
  obsolete `isDeepSplit → ¬ isEntrance` clause with S-5's retype demand
  pending. Rev 2's contradictory routing claim is replaced by an explicit
  open flag; MovesV's delivery (cts_counts := ValA ∧ EntCount + wsh_xhd_s
  as fields of the DISPLAYED `Wsh17PackageV`) matches the Wsh17Package
  field roster (c15_volumes stays §C/HC-2, sib_count stays [3t]/CL-10) ✓.
- **V4-12's restored iff** — the biconditional is restored at the ∀-weight
  quantifier with ⟸ proved / ⟹ labeled HARD + split, matching the note's
  V.4 sentence (8598-8602) read at the quantified adjudication, and the
  fence (c) is retained as charged. The verification is OVERTAKEN by N-1:
  (b) is trivially true, (c) is unsatisfiable, and the adjudication line
  "the only reading on which the sentence is true" is wrong (the
  fixed-system reading is also true given the definitional count). No
  silent weakening — the defect is upstream, in XHDd/HMC.
- **Byte-stability — VERIFIED.** Diffed f2f98c7 → 39862fc: `A2chart`/
  `A2dom`/`EA2`/`TA2` displays, `chainCount`, `XHDd`, `HMC`/`HMCAug`,
  `StepSys.ext`/`ext_zc`, `CtsMeasured.EntIx`, and the V6-1a/1b/2a/3a/4a/4b
  unit texts are byte-identical; changes adjacent to the clean cores are
  exactly the sanctioned repairs (G-1 attribution at §0/§2.I/V0-4, G-2
  Conway correction, F-1/F-2 census wiring, X-4 pathProdPoly). The
  stability check is also what certifies N-1 and N-2 as INHERITED (present
  verbatim in the rev-2 text both round-2 passes cleared).
- **The 82 splits — EXACT, one-display (one wart).** Recounted per unit:
  V0[4: 2e/2m] V1[10: 5e/5m] V2[10: 6e/4m] V3[11: 4e/5m/2h]
  V4[12: 4e/6m/2h] V5[10: 3e/6m/1h] V6[10: 5e/5m] V7[15: 4e/10m/1h] =
  82 = 33/43/6, matching §5's census exactly, delta vs rev 2 as recorded
  (V1-8→a/b/c, V7-2→a/b, V7-3→a/b/c/d, V7-4→a/b/c, V7-6→a/b/c, +V5-8,
  V3-3 and V4-12 re-graded HARD). Each split unit is one display except
  V7-6a (G-2). HARD set = {V3-3, V3-5, V4-6, V4-12, V5-2, V7-5} with
  splits pre-approved ✓.
- **Fresh sweep, additional passes:** V2-7's corrected cells partition the
  nonzero target ✓ (note's FL/FS verbatim); the σ_sel/selRank pin keys to
  real MovesD declarations (selRank/EligibleImage/E8_rankInj/mbar all
  source-verified) ✓; the G-3 zig/gamTie inversion matches the built
  `ShapeWF.gamTie` exactly (γ = e·(STR·u*) + (s0+wSide)·h — Defs 165-168),
  hatch recorded ✓; G-4's re-point lands on the exported `D4R1_SUM`
  (Σᶠ fiber cards · p^{A'} = card(PrefIdx) · p^{nN} — exactly ent_card's
  shape) ✓; the G-1/G-2 attribution repairs are in place and accurate
  (the note displays (3(h₀+h₂)−1)/2 + the substitution, never "6t+3u+1";
  C_{3,2} = x²+2x+2 acknowledged) ✓; V7-7's Wsh17PackageV, xhdStmt
  re-keying (all four XRBPackage fields to ONE Prop) ✓; the §4.1/4.2
  field lists re-verified against the built Defs/Interfaces (only sanctioned
  row changes) ✓; the conditionality banner correctly scopes V6-4c out ✓.

## C. DISPOSITION (hints, not fixes)

N-1 first, and NOT unilaterally: the defect reads back into the frozen
note's own V.0/(v) ledger, so the owners must adjudicate the no-stray
quantifier at composite templates before any blueprint re-key (weakening
XHDd is a statement-fence event; keeping it means (v) is XHD-d-implied and
the whole (v)-tag architecture — V4-11, V4-12, V5-5/V5-6, V7-6c's hmc leg,
§0's banner — must be re-drawn around a hypothesis with actual content,
e.g. exactness NOT assumed at composite templates). N-2 is mechanical but
wide: pool-index the §2.B carriers (Hist/Assign as per-q₀ families) or
re-key every count tie box-side (the blueprint's own entInst/stInst
pattern, extended to cells and moves); XHDu's twins re-read accordingly.
N-3 is one line (kstep 0 := δ). G-1/G-2 are wording/roster sweeps.

*(End of round-3 fresh-instance audit. REJECT: 3 critical / 2 gap.)*
