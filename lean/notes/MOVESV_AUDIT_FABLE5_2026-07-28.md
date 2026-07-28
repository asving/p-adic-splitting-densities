# MOVESV BLUEPRINT REV 5 — FRESH-INSTANCE AUDIT (Fable, round 5)

*(2026-07-28. Auditor: Fable fresh instance, zero conversation history.
ARTIFACT: `lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` REV 5, 4625 lines,
read in full. GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` 7829–9054 read at
every cited display (V.0 7899–7986 incl. 7921–7923/7948–7949; V.1 8021–8260
incl. HMC 8198–8213, HMC-AUG 8213–8220 — quoted below — and COMP 8222–8260;
V.2's VAL/CTS-T 8347–8394; V.3 8413–8558; V.4 8560–8686 incl. the naming
sentence 8596–8602; V.5 8687–8763; V.6 8765–9054 incl. 8841–8847 and the
V.6.1/V.6.3 rosters); the BUILT sources re-read this round:
`MovesS/Defs.lean` (Member/Outcome/routeOf 29–58, TableShape 66–80, SCSData
97–136, DegCons 138–143, MeasuredSide 149–192 incl. `Rep` 163 / `cellEvt` 170
/ `hent` 179, LedgerIV 210–262 — `xhd_no_orphan` 218–219 verified UNGUARDED
`∀ (q₀ : ℚ) (N : ℕ)`, `d4r0` 221–223 unguarded, `hmc` 243–244 ∀-k,
`kstep_one` 238–242 with its member condition, guarded suite 212–236/249–262;
PolyGeom 322–336; RatBurdens 342–376 incl. cellP/act_iff), `MovesS/
Interfaces.lean` (RS1Meas's OWN ℕ-typed h_ent 35–39; `hK : ∀ e, e ∈
Finset.Icc 1 n → KmatHyp T e` at 49/71/121), `MovesS/N2Carriers.lean` 95–125
(the kstep comment 101–105 "kstep 0 = 1 and the HMC scalar law … holds";
`hent := fun _ _ _ => 0` at 118), the fresh corpus-wide `hent` grep (Defs 179
declaration + N2Carriers 118 device + N2EntFlow 3 comment — NO law reads it),
`MovesD/Defs.lean` (ShapeRead 63–73 incl. `ustar : ℚ`, `mbar` 97, `gamTie`/
`anchorTie` 165–169, `selRank (w) (ν)` 296, PrefIdx 402, `reprOf` 430,
History `.nodes`, Presented/fiber/mult 464–490) + `D4R1_SUM`
(D10_sumLaw.lean 32), `MovesSp/Defs.lean` (Species fields incl. W/D/sel 37–52,
SuccStep 119, InCatalogue 124, SnRaw 128, Verdict 132, `Out : Set (Species ⊕
Verdict)` 139, rankNat 167, CollapsedWalk 172, collapseRuns 265,
EntranceShape hMem/hChain/hEntry 278–288), and
`MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (XRBPackage's 13 Prop fields 1236–1244;
Wsh17Package's three Prop fields c15_volumes/cts_counts/sib_count;
TreeIface.tree_ne + the `isDeepSplit → ¬ isEntrance` clause — SF-2's
owner-side objects, still blueprint-level/unbuilt).
CHARGE: (1) the tix binding — re-run the 0=2 junk-terminal refutation (must
no longer TYPE); (2) HMCAug TE-pinned — re-run the cooked identity-refinement
witness (tevt_cover must kill it) AND check the pin does not make HMCAug
derivable-from-HMC; (3) the completed pool ripple (V1-6/V1-7; the per-pool
Rep + off-pool-∅ walked against the frozen UNGUARDED xhd_no_orphan; the
no-constant-poly re-grep); (4) all six round-2 F-refutations + the round-4
trio re-armed; (5) six disposition spot-checks; (6) fresh sweep of the 95
units. Read, judge, fix nothing; quote and classify.)*

## VERDICT: REJECT — 0 critical / 3 gap (record/display class; the REV-5 mathematical content is otherwise CLEAN)

All five round-4 repairs LAND at the statement level: the junk-terminal
refutation no longer types (§A.1), the cooked HMCAug witness dies at
boxEq/tevt_cover — and, non-trivially, HMCAug is now FALSIFIABLE (I verified
¬HMCAug is provable at V4-11's coupled toy for EVERY refinement, §A.2) — the
pool ripple is complete with the per-pool `Rep` walk sound against the built
unguarded `xhd_no_orphan` (§A.3), all six round-2 F-refutations and the
round-3/round-4 batteries re-ran DEAD (§A.4), the sampled disposition rows
are accurate (§A.5), and the census is exactly 95 = 32/59/4 (§A.6). No
statement is false, no gate unsatisfiable, no open kernel discharged. The
rejection is carried by three gap-grade findings from the charge's own
hardest checks and the fresh sweep: the §2.G underivability line for HMCAug
overstates ("NOT a consequence of HMC" is UNATTAINABLE by any faithful
encoding — HMC ⟹ HMCAug is a ~30-line theorem via the identity refinement,
and I show the implication is semantically forced by the note's own
conditional, so the RECORD must be scoped, not the type changed); V7-4a's
displayed `cellEvt` handles the pool dite but not the `Hgt` Σ-dimension
mismatch that the SAME frozen unguarded laws force to ∅ (an undisplayed
zero-freedom twin of inventory slot 12 — as displayed the on-pool branch is
ill-typed at wrong-dimension heights and V7-6a1's no_orphan leg silently
assumes the resolution); and V5-7b's displayed datum constructor
mis-namespaces `cont_of_route` (a JCells-derived fact attributed to
`(C.bd s)`, which cannot see `route`). One record-and-display pass repairs
all three.

---

## A. THE CHARGE ITEMS

### A.1 The tix binding — the round-4 refutation NO LONGER TYPES; the binding is complete and note-faithful

**Re-run of the 0 = 2 junk-terminal refutation.** Round-4 instance: root
datum d = the T21 letter's (m_2+1, its continuing outcome, α₀), index
β = `.term ⟨(1,1),_⟩`. Under REV 5's §2.C:

> `| term (ht : ¬ B.cont m o) (v : VLabel n)`

the constructor demands `ht : ¬ cont m o`; d's outcome has
`cont` TRUE through `cont_iff` (the §2.I gate roster
{(2, δ, .inr s_blk2), (1, δ, .inl (1,1))} contains a continuing member), so
`.term` cannot be formed at this outcome — **the refutation instance fails
to elaborate. DEAD BY TYPE.** ✓ Codex-3's horn confirmed simultaneously.

**The binding.** `tbl_count` now reads
`((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) = S.cntraw (V.moveOf d) x (…base)`
— no free β anywhere; `MoveData.tix = .cell d.hc (tcell …)` and
`TermData.tix = .term d.ht v` (through `hv`) are the §2.C displayed defs,
the SAME object V2-5's `pathProdPoly` (per-step `.tix`), V5-8's RHS, and
V7-4c's kstep bind — the round-4 asymmetry is gone. The M-1 ripple the
predecessor demanded is present: V4-1's conclusion is at `d.tix` (the
datum's own column, explicit).

**The off-key clauses vs the note.** `tbl_offkey` forces
`(C.T … β).eval q₀ = 0` at every pool for β ≠ d.tix. Checked against VAL(a)
(MOVES 8354–8357, "each valued correctly at every prime power q") + the
tcell-enforced landing (§2.C/§2.F `moveOf`/`moveOf_bij`, unchanged): off the
(D4) landing the definitional count IS 0 at every prime power, and (with
`pools_infinite` at the consumer) the off-key polynomial is forced ≡ 0 —
note-correct, not an over-constraint. `tbl_offkeyT` likewise kills wrong
absorbing labels v′ ≠ vlabOf. DOCTRINE CHECK: the round-4 cooked-junk family
(off-key entries := the row count) now violates `tbl_offkey` — FALSE where
the note rejects, exactly the inversion M-1 demanded; the note-correct
family satisfies all fields — `valA_gate` is satisfiable again, with the
displayed T21 acceptance numbers (eval 2 = 2 = the F₂-fiber count, eval 3 =
6 = the F₃-fiber count).

### A.2 HMCAug TE-pinned — the cooked witness DIES (verified in detail); the Prop is now falsifiable AND satisfiable; but the underivability line needs scoping (finding G-A: HMC ⟹ HMCAug is a theorem, unavoidably)

**The note display, quoted and compared (MOVES 8213–8220):** "(HMC-AUG) — a
SEPARATE named redesign hypothesis, NOT a consequence of HMC (rev 2,
finding 12; ledgered V.5): if a global cone inequality couples successive
steps, ONE round of 𝒞_n refinement by finitely-valued boundary/gap data
restores the factorization; finite-memory repair need not be possible at
all — a second surviving coupling is R2's wall channel." The blueprint's
quotation at the `RefEvents` def site is VERBATIM (word-for-word check).

**Re-run of the round-4 cooked witness against the REV-5 type.** The
construction (B α := PUnit identity refinement; TE′ with `Box := PUnit`,
`tevt′ := if-membership-then-univ-else-∅`, product-partition domains) must
now supply `RE : RefEvents R TE`:
- `boxEq : TE'.Box q₀ N ≃ TE.Box q₀ N` kills the PUnit box outright at any
  TE with non-singleton boxes (the ledger's TE — MovesD.Box at the real
  instance, card q^{nN}).
- Retrying with real boxes: at the identity refinement `refTmpls R α' rfl γ`
  reduces to the singleton roster (exactly one surviving (β′, m′) per step —
  walked through the displayed filterMap), so `tevt_cover` forces
  `TE'.tevt = TE.tevt` (up to boxEq) at EVERY (γ, x′, h, N) and
  `tinst_cover` pins the censuses. With `pools_ne` + `zc_ne`, XHDd exactness
  pins any D′'s `dom` EXTENSIONALLY to TReal TE′ = TReal TE, so
  `HMC RE.TE' D'` reduces to the open kernel `HMC TE D` itself. **The
  cooked witness is DEAD.** ✓
- **Beyond the charge — non-identity cooking also dies; ¬HMCAug is provable
  at the coupled toy.** At V4-11's toy (base `tevt(.cons)` = ∅ at (0,0) at
  every N; both one-step events realized), for ANY refinement:
  `assign_cover` partitions each nonempty coarse fiber, so some refined
  clone pair has both one-step counts positive at (0, 0) — `tevt_last_iff`
  (TE′'s own tie) + `no_orphan` put 0 in both refined one-step domains;
  while `tevt_cover`'s union over the composite roster equals the base ∅ at
  (0,0), forcing every refined composite event empty there, so `no_stray`
  forbids (0,0) ∈ dom′(cons). HMC TE′ D′ FAILS for every (R, RE, D′) —
  **HMCAug S TE is FALSE at the coupled toy.** The Prop has genuine content
  (falsifiable), is satisfiable (V1-8b's HMC-true toy + the identity
  refinement + RE := transported-TE), and is NOT derivable from the XHD
  package (the package has no HMC field). M-2's core repair LANDED.

**The derivable-from-HMC check (the charge's second clause) — it IS
derivable, and no faithful encoding can avoid it (finding G-A).**
`theorem (D : XHDd n S TE) : HMC TE D → HMCAug S TE` is provable in the
REV-5 encoding: take R := the identity refinement (S′ := S, cellEq via
`Σ _ : α, PUnit ≃ α`; all projections id/rfl; assign_cover the evident
singleton-Σ bijection; twins likewise), RE := ⟨TE, Equiv.refl, tevt_cover/
tinst_cover by the singleton-roster reduction above⟩, D′ := D — then
`HMC RE.TE' D' = HMC TE D`, given. ~30 mechanical lines. Moreover this is
NOT a repairable defect of the pin: the note's hypothesis is a CONDITIONAL
("IF a global cone inequality couples … ONE round … restores"), whose
antecedent is empty when HMC holds — so even the conditional encoding
`¬HMC → ∃ …` is implied by HMC (vacuously). ANY encoding under which a
factorizing refinement witnesses AUG (which satisfiability requires) admits
the identity refinement as that witness at HMC-true instances.
Underivability-from-HMC is therefore UNATTAINABLE; the note's "NOT a
consequence of HMC" can only be carried as ledger-role bookkeeping (separate
line item, cite separately, never assumed), not as logical independence.
The TYPE is right; the blueprint's summary line is not — see G-A. No
in-corpus conditionality collapses either way: HMC is proved nowhere, and
HMCAug is consumed by nothing (fresh grep: V7-1's ledger line only).

### A.3 The pool ripple — COMPLETE; the per-pool Rep instantiation walked and sound; no constant-poly forcing anywhere

- **V1-6** now displays `{q₀} (hq : q₀ ∈ S.Pools) (x : S.Hist q₀ α) … (a a' :
  S.Assign m x h) : S.massOf m x h a = S.massOf m x h a'` — pooled `Hist`,
  no trailing ℚ on `massOf` — elaborates against the §2.B carriers ✓ and
  matches the note's (U-A) (one fixed history) ✓.
- **V1-7**'s fence: same-pool `(x x' : S.Hist q₀ α)`, nested ∃, massOf
  4-argument ✓. Both rev-3 signatures are gone (grep: no `S.Hist α`, no
  `massOf … q₀` survivor anywhere in §3).
- **V7-4a's Rep, walked against the BUILT laws** (re-read this round):
  `Rep e τ := ∀ q₀, q₀ ∈ V.Pools → {x : S.Hist q₀ (cellOf τ) // S.zc x}` is
  a pool-global Type ✓ fitting the frozen `Rep : ∀ e, T.State e → Type`
  (Defs.lean 163); `rep_ne` from per-pool `zc_ne` (through `pools_sub`) +
  Classical choice ✓ (Nonempty is a Prop — licit); the guarded LedgerIV suite
  (xhd_sum/meas_card/part1/rep_indep — all verified `q₀ ∈ M.Pools`-guarded at
  Defs.lean 212–236) reads the SAME-pool component `(x q₀ hq)` ✓; the frozen
  `xhd_no_orphan` is UNGUARDED exactly as claimed (Defs.lean 218–219:
  `h ∉ M.HDom e τ c → ∀ (q₀ : ℚ) (N : ℕ), M.cellEvt … = ∅`), so the OFF-POOL
  branch of `cellEvt` MUST be definitionally ∅ — the recorded slot-12
  decision, correct, and the Σ-typed one-pool alternative correctly
  rejected (junk-valued guarded laws); `d4r0` (unguarded, (c,h)-keyed —
  Defs.lean 221–223) holds off-pool with both sides ∅ ✓. ONE leg of the walk
  is incomplete: the `Hgt = Σ D, Hpt D` DIMENSION-mismatch branch — see
  finding G-B.
- **No-constant-poly re-grep** (every law equating a carrier value to a
  q₀-family, REV-5 additions included): `size_count` (Carrier q₀-indexed ✓),
  `stInst_card` ✓, `ent_card`/`entCensus` ✓, `evt_card` (massOf rides x) ✓,
  `box_card` ✓, `tbl_count`/`tbl_countT` (counts at x's pool) ✓,
  `CellPolyPack.count/countT` ✓, `EntCount`/`EntU` (census per q₀) ✓,
  `EntMassSummable` (per q₀ ∈ Pools) ✓, `evt_disj_cell` (one x, one pool) ✓,
  `u_R_*`/`u_T*` (same-pool, N-2's two-horn closure intact) ✓, `emult`
  pool-free BY DESIGN (multiplicity datum; no law equates it to a
  q₀-varying quantity) ✓, the REV-5 `omem`/`tcellM`/`tix` (symbolic data, no
  count law) ✓, `SelRankTie` (per (p, F, pol) instance) ✓, `tbl_offkey`
  (forces ≡ 0 off-key — note-CORRECT forcing, per A.1, not a defect) ✓.
  NO cross-prime forcing survives.

### A.4 Refutation batteries re-armed — ALL DEAD

**Round-2 F-refutations (all six):**
- **F-1** DEAD: ιshH := census·q^{−A} (§2.G def); gate B: ent_card gives
  128·2³ = 1024 = 2·2⁹ ✓ and init_count's (1/4)·512 = 128 ✓ — never 8192.
- **F-2** DEAD: entCount := the census; gate census q(q−1), degree 2 ≤
  Went = 3 ✓ — the ι_degT/degT_le ledger jointly satisfiable (checked
  against the built `RatBurdens.ι_degT` = Went).
- **F-3** DEAD: evt_card/box_card ties + XHDdC present; the REV-5 MINIMIZED
  `stepKey` still supplies the frozen `d4r0` — its (c, h) ≠ (c′, h′)
  quantifier IS a distinct-(Σ-cell, Σ-height)-key instance (the biUnion
  members' keys carry exactly their cellOfA-image and height), and
  meas_card's within-cell legs ride the DISPLAYED `MarkDisj`/`MarkDisjT`
  premises — suite derivable field-by-field, re-walked.
- **F-4** DEAD: XHDsC weight-only; V5-8 displays the count on BOTH sides
  ((q−1)²·G = TA2·G at the A2 check, pool-consistent 1-vs-4); V7-4c's kstep
  carries `(pathProdPoly C γ).eval` ✓.
- **F-5** DEAD: V7-5c's cellP := sizeP (state census; `stInst_card` wired);
  cellP_deg ≤ Wstate at both gates ✓; act_iff ← act_size with the
  `cell_ne_inst` nonemptiness step DISPLAYED ✓; the m_H3 empty digit cell
  at q = 2 contradicts nothing ✓.
- **F-6** DEAD: roster_tie route-keyed (ALL cells iff split); the root
  m_2+1 outcome is split-route (m = 2, c = 1 — verified against the built
  `routeOf`: c ≠ 0, m ≠ 1 ⟹ .split) with nonzero gate Jval ✓.

**Round-3 trio (re-verified standing):** the four-line HMC proof still
FAILS (XHDd exactness TReal-keyed; no composite law; slot-2/slot-9 fences
now mutually consistent); T21 2-vs-6 and (X−1)² 1-vs-4 displayed and
satisfiable; kstep k = 0 δ vs the frozen `hmc` at k = 0 (Defs.lean 243–244:
Σ_γ δ_{τγ}·kstep 1 γ β = kstep 1 τ β ✓ hypothesis-free) + the built
N2Carriers 101–105 cite verified verbatim.

**Round-4 trio:** M-1 dead by type + binding (A.1); M-2's cooked witness
dead (A.2); M-3's three sites repaired (A.3).

**Round-1/2 spot re-arms:** A2 chart recomputed (A2chart ![1,0] = ![4,1],
EA2.eval ![1,0] = 7 = the seal; 2·EA2 = 3(h₀+h₂)−1 as ℕ-identity;
GA2 = X²/((X⁶−1)(X³−1)) re-derived from the double geometric sum ✓);
V6-1b's m_H3 row (0,1,4,10,35,56,84,165,286) recomputed against
q(q−1)(q−2)/6 incl. the q = 2 falsifier ✓ vs MOVES 8825; V2-7's cells vs
MOVES 8336–8338 (FL = {x≠0, y=0}, FS = {x=0, y≠0}, nonzero-target
partition) ✓; V6-4a's 2^{3N−5} = 16/128 vs MOVES 8987 ✓; gate-B's
ι = 1/4, T = 1, g = 1/8, μ̂ = 1/32, shadow = 2 vs MOVES 8977–8979 ✓;
the s_blk2 omem literals vs V.6.3's outcome table (o_split (1,1)+(1,1);
o_inert one size-2 member labeled [1,2]; o_double size-2 continuing;
DEG-CONS sums ≤ 2) ✓; X-1's all-empty adversary dead at pool-guarded
out_ne + the REV-5 `pools_ne` (the empty-pool escape is also gone) ✓.

### A.5 Disposition rows spot-verified (eleven, incl. all three round-4 criticals)

- **M-1 row — ACCURATE** (per A.1; the V4-1/V2-5/V5-8 ripple named and
  present).
- **M-2 row — ACCURATE as to the repair** (RefEvents/refTmpls displayed
  closed; the cooked witness re-run and dead; the false comment struck) —
  EXCEPT the §2.G summary line's residual over-claim, G-A.
- **M-3 = Codex-1/14 row — ACCURATE** (V1-6/V1-7 re-signatured; the walk
  displayed; V7-6a1's off-pool leg explicit; slot 12 recorded) — with the
  dimension-branch residue G-B.
- **Codex-2 row — ACCURATE**: OMember mirrors the built `Member`
  (size/δ/status : V ⊕ State size — Defs.lean 32–35) field-for-field;
  `omem_ne` supplies the built `Outcome.hm` (mem ≠ [] — Defs.lean 40–42);
  V7-3a's odata map displayed with the omem_size cast; `omem_kcol`'s
  length-1 premise matches the built `routeOf`'s kcol arm (m = 1, c ≥ 1).
- **Codex-11 row — ACCURATE**: the frozen `XRBPackage` has 13 Prop fields
  (MOVESS blueprint 1236–1244); `xrbPackageOf`'s nine non-xhd Prop
  parameters (jc_inv/sib/jc_multi/tb_cap/vp/rel2_a/b/d/ns_null) match the
  roster EXACTLY; the four `*_Stmt` face-law Props type against the Prop
  fields; `frameOf`/`xhd_faces_of` give the discharge direction.
- **Codex-13 row — ACCURATE**: `kmat_all` scoped `∀ e, e ∈ Finset.Icc 1 n →`
  — verbatim the frozen consumption (`hK` at Interfaces.lean 49/71/121).
- **Codex-8 row — ACCURATE**: `EntMassSummable` a standalone named def whose
  body is rfl-identical to V3-8a's summand (checked token-wise against
  ιshH); XHDsEnt weight-only again; realized on V1-8c's toy.
- **Codex-16 row — ACCURATE** (CellIdx single-homed §2.C; V2-2 = instance +
  deleted_empty).
- **Codex-17 row — ACCURATE** (all 24 `*_Stmt` bodies displayed — counted;
  the prose-parenthesized cores rule-bound, recorded).
- **G-1 row — ACCURATE** (ONE only-if status corpus-wide: §0 and V4-12(b)
  both now carry (b′)'s OPEN-CLAIMED-NEITHER-WAY form; no contradictory
  sentence survives — grepped).
- **G-2/Codex-7 row — ACCURATE**: hentCode length-seeded
  (`Nat.pair reads.length (fold …)`) — injective on the retained
  (h, γ)-tuple lists (equal length: Nat.pair-induction; unequal: the seed);
  the gloss scoped to fixed-template consumption; SF-1's standing grep
  re-run THIS round against the built sources: `hent` = Defs.lean 179 +
  N2Carriers.lean 118 + one comment, NO law reads it; RS1Meas's h_ent is
  its own ℕ argument (Interfaces.lean 35–39) ✓.

### A.6 Fresh sweep — census EXACT; three new findings, all gap-grade

- **Census EXACT**: 95 = V0[4: 2e/2m] V1[10: 5e/5m] V2[10: 6e/4m]
  V3[17: 4e/11m/2h] V4[14: 3e/10m/1h] V5[12: 3e/8m/1h] V6[10: 5e/5m]
  V7[18: 4e/14m] — per-unit recount matches §5's table; hard set =
  {V3-3d, V3-5a, V4-6b, V5-2b} ✓; REV 5 adds no units, as claimed.
- V4-12(b′)'s coincidence recomputed (E-multisets {0,1,1,2} both;
  (1+q⁻¹)² ✓); V4-11's coupled domain partition recomputed
  (L((1,0);{(1,0),(0,1)}) ⊔ L((0,1);{(0,1)}) = ℕ²∖{(0,0)}, disjoint ✓);
  V2-6's power-image law, V6-3a's char-2 recount identities
  ((q−1)(q/2−1) = (q−1)(q−2)/2 ✓), V6-1a's PART-1 ring identity, and the
  F4/F8/F9 table shapes spot-checked (provenance note re x²+1 over F₃
  intact). The V7-6 derivations re-walked field-by-field against the built
  LedgerIV (meas_card through MarkDisj/MarkDisjT + evt_card + w_eq +
  cp.count; kstep_one through V5-8 + omem_kcol/tcellM_tgt against the
  built member condition `∃ μ ∈ mem, ∃ h : μ.size = e, h ▸ μ.status =
  Sum.inr β`; ent_count_card rfl; comp_once via (ENT-U)) — derivable as
  displayed, except the G-B leg.
- MovesSp/MovesD/MovesS name keys re-verified at source (roster in the
  header). `skBlk = s.sp.W * s.sp.D` — both Species fields exist (Defs
  39/41); slot-13 hatch appropriate. `EntShapeV.hentry/helig` type against
  ShapeRead's g/μ/len ✓; `SelRankTie`'s `selRank (branchingRead …).w ν`
  matches the built `selRank (w : ℕ) (ν : Node p F)` signature ✓.
- The sweep's new findings are G-A, G-B, G-C below. (Also noted, below
  finding-grade: V7-1's clause-(v) ledger-field phrasing "(v) OPEN +
  (HMC-AUG) separate" does not display whether the ledger carries an
  HMC-typed field — the displayed V7-2a/V7-6c consumers all take HMC as an
  explicit ANTECEDENT, which pins the intent; this is inside the recorded
  Y-16 residual (V7-1 a single structure-declaration unit) and is not
  counted.)

---

## GAPS

### G-A — the §2.G HMCAug underivability line over-claims: `HMC TE D → HMCAug S TE` is a theorem of the REV-5 encoding (identity refinement + transported RefEvents), and NO faithful encoding can avoid it — the record must be scoped, per the note's quoted display (MOVES 8213–8220)

Offending passage (§2.G, the HMCAug def comment):

> `-- HMCAug is again "NOT a consequence of HMC" and not of the XHD package
> -- either — satisfiable (a factorizing refinement witnesses it), provable
> -- by nothing in this corpus, consumed by nothing`

The "not of the XHD package" half is TRUE (verified — the package carries no
HMC field, and ¬HMCAug is provable at the coupled toy, §A.2). The "NOT a
consequence of HMC" half is FALSE as a Lean-derivability claim: given the
d-face `D : XHDd n S TE` (in scope wherever HMC TE D is even stated), the
identity refinement + `RE := ⟨TE-transported, Equiv.refl, cover-by-singleton-
roster⟩` + `D' := D` witness the ∃ — ~30 mechanical lines (§A.2's display).
The def site's own text concedes the reduction ("the cooked witness would
have to prove HMC TE D itself") — proving HMC TE D is exactly what the
HMC-antecedent supplies. And the implication is SEMANTICALLY FORCED: the
note's hypothesis is a conditional whose antecedent (a surviving coupling)
is empty under HMC, so even the literal `¬HMC → ∃ …` form is HMC-implied;
underivability-from-HMC is unattainable by any encoding that keeps the
factorizing-refinement witness (which satisfiability requires). "NOT a
consequence of HMC" therefore lives at the LEDGER level (separate named
line item, never assumed, never conflated), not at the derivability level.
CONSEQUENCE: none in-corpus (HMC is proved nowhere; HMCAug consumed
nowhere) — the defect is the false record line, the round-4 G-1 class.
(Disposition hint, not a fix: scope the comment — "not derivable from the
XHD package; the HMC ⟹ HMCAug implication is the vacuous-repair case,
inherent to the note's conditional and harmless while (v) is open" — and
carry the same one-sentence scope at V7-1's (v) ledger line and §0's
banner sentence "completed at REV 5 for (HMC-AUG) too".)

### G-B — V7-4a's `cellEvt` display handles the pool dite but NOT the `Hgt` Σ-DIMENSION mismatch; the same frozen UNGUARDED laws force that branch to ∅, an undisplayed zero-freedom twin of inventory slot 12, and V7-6a1's `xhd_no_orphan` leg silently assumes it

Offending displays:

> V7-4a: `cellEvt x c h q₀ N := if hq : q₀ ∈ V.Pools then (§2.F biUnion at
> (x q₀ hq).1) else ∅` … "the dite lands in the right Box fiber on both
> branches"
> V7-6a1: `xhd_no_orphan … : at q₀ ∈ Pools — h ∉ HDom → cntc = 0
> (X.dC.no_orphanC contrapositive) → the filter is empty → cellEvt = ∅ at
> EVERY N (definitional)`

`Hgt := Σ D : ℕ, Hpt D` (V7-4a) is ONE global type, while the §2.F biUnion
takes `h : Hpt (S.dim (V.moveOf d))` — so the displayed on-pool branch is
ill-typed at any h whose Σ-component differs from the cell's dimension, and
the E-phase def MUST carry a second (dimension) dite. Its value is FORCED:
the frozen `xhd_no_orphan` (UNGUARDED, `∀ (q₀ : ℚ) (N : ℕ)` — built
Defs.lean 218–219) quantifies over ALL h : Hgt, and a wrong-dimension h is
∉ HDom (the Σ-embedded cdom), so the branch must be ∅ (`univ` is
expressible via `boxpos` and would FALSIFY the law — the same
junk-vs-forced dichotomy that rejected the Σ-typed Rep at slot 12). V7-6a1's
derivation covers only matching-dimension heights (its "cntc = 0" step is
not even stateable at a mismatched h); `d4r0`'s off-key leg has the same
silent dependence. Zero design freedom, one-line E-phase content — but per
the blueprint's OWN slot-12 standard (a forced-by-the-frozen-law value is a
RECORDED design decision with its branch displayed), the branch and its
forcing belong in the V7-4a walk and the §5 inventory (amend slot 12 or add
slot 15), and V7-6a1's no_orphan roster needs the third leg ("wrong
dimension: ∅ by the dite").

### G-C — V5-7b's displayed datum constructor mis-namespaces `cont_of_route`: attributed to `(C.bd s)`, which cannot see `route` (a JCells datum) — it must derive from `J.route_cont`

Offending display (V5-7b):

> `= Jval J hcell XsC ⟨s, m, o, (C.bd s).cont_of_route hr, α⟩ q₀` — the
> datum is BUILT from the quadruple through `JCells.route_cont` (§2.H …;
> `cont_of_route` its one-line corollary)

`hr : J.route s m o = .split` mentions `J`; `BlockData` has no `route`
field, so no `(C.bd s).cont_of_route` can exist — the corollary lives on
`JCells` (e.g. `J.cont_of_route : route s m o = .split → (C.bd s).cont m o`,
from `route_cont` + `cont_iff`). The unit's own prose says exactly this;
the display token contradicts it. One-token fix, zero design content —
the Codex-15/Y-15 elaboration class.

---

## B. DISPOSITION (hints, not fixes)

All three are one-pass record/display repairs; no statement, type, or unit
changes force any ripple. G-A: scope the §2.G comment (and its §0/V7-1
echoes) to "not derivable from the XHD package" + the recorded vacuous-repair
implication — do NOT re-key the type (conditioning the ∃ on ¬HMC buys
nothing, per the analysis above, and would entangle the Prop with the
kernel's negation). G-B: display the dimension dite in V7-4a's cellEvt,
add the third leg to V7-6a1's no_orphan roster, and record the forced value
in the §5 inventory beside slot 12. G-C: `J.cont_of_route` (or inline
`J.route_cont … |> cont_iff-transport`) at V5-7b's display.

*(End of round-5 fresh-instance audit. REJECT: 0 critical / 3 gap —
statement-level content verified clean; the charge's three hard re-runs all
confirm the round-4 repairs landed.)*
