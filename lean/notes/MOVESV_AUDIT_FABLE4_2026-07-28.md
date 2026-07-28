# MOVESV BLUEPRINT REV 4 — FRESH-INSTANCE AUDIT (Fable, round 4)

*(2026-07-28. Auditor: Fable fresh instance, zero conversation history.
ARTIFACT: `lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` REV 4, 3817 lines,
read in full. GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` 7829–9054 read at
every cited display (V.0 7899–7986 incl. the T_γ/no-orphan/no-stray lines
7921–7923/7948–7949; V.1 8021–8260 incl. HMC 8198–8213, HMC-AUG 8213–8220,
COMP 8222–8260; V.4 8560–8686 incl. the naming sentence 8596–8602 and the
probe; V.5 8689–8763; V.6.2's 8841–8847); the BUILT sources: `MovesS/Defs.lean`
(TableShape/SCSData 66–139, MeasuredSide 160–192 incl. `hent` 179 and
`Rep`/`cellEvt` signatures, LedgerIV all nine inputs incl. `hmc`/`kstep_one`/
`init_count`/`ent_count_card`), `MovesS/N2Carriers.lean` 90–125 (kstep
`(…)^k`, `hent := 0` at 118), `MovesS/Interfaces.lean` 25–45 (RS1Meas's OWN
ℕ-typed h_ent argument), `MovesD` name checks (D4R1_SUM, D4R4_all,
eligible_card_le, selRank, EligibleImage, E8/E9 files, gamTie/anchorTie,
ShapeRead.mbar), and `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (Wsh17Package
three-field roster 1321–1325; W7_cutWD's surviving `isDeepSplit →
¬isEntrance` clause 1288; TreeIface.tree_ne 1174 — SF-2's owner-side
objects). CHARGE: (1) the HMC fix per the orchestrator adjudication (4-line
proof re-run must FAIL; one-way count route; underivability audit honesty;
V4-11/V4-12(c) satisfiable — construct); (2) the pool layer (both gate
refutations re-run; one-layer sufficiency); (3) kstep 0 vs the built N2
instance; (4) the V4-12 quantifier vs MOVES 8596–8602 exactly; (5) six
disposition rows incl. the three PARTIALs; (6) fresh sweep of the 95 units,
prior refutations re-armed. Read, judge, fix nothing; quote and classify.)*

## VERDICT: REJECT — 3 critical / 2 gap

The three ADJUDICATED repairs land: the four-line HMC proof now FAILS against
the process-keyed `XHDd` (re-derived below, §A.1), both N-2 gate refutations
DIE (§A.2), the kstep k = 0 Kronecker δ is correct against the frozen
`LedgerIV.hmc` and the built device instance (§A.3), and the V4-12 iff sits
at the note's exact quantifier (§A.4). All six round-2 F-refutations and the
round-3 acceptance numbers re-ran DEAD. The rejection is carried by three
fresh-sweep findings: one INHERITED statement bug that has sat in the same
display since rev 2 (the free-β `tbl_count` — it makes `valA_gate` false at
the note-correct gate family, the same defect class as round-3's N-2), one
residue of N-1 that rev 4 claims fixed but is not (`HMCAug` is derivable
from the XHD package by an explicit construction — the §2.G "unrelated
witness stays impossible" audit line is false), and an incomplete N-2 ripple
(three displays still carry rev-3 pool-free signatures, one of them the
load-bearing `Rep` instantiation).

---

## CRITICAL FINDINGS

### M-1 — `ValA.tbl_count` quantifies its table index β FREE with a β-independent right side: every TargetIx entry of a row — the tcell target, every off-target cell, every junk terminal label — is forced EQUAL to the datum's count; the note-correct gate family falsifies `valA_gate` (0 = 2 at q₀ = 2)

Offending display (V2-4(a); the (β) binder and the β-free right side are
byte-inherited from the rev-2/rev-3 texts — round 3's N-2 quoted this very
display and repaired only the pool index):

> `tbl_count : ∀ (d : MoveData n C) (β) {q₀} (x : S.Hist q₀ _)
> (hzc : S.zc x) (hq : q₀ ∈ V.Pools) (j : Fin (V.mdom d).comps.length),
> ((C.T d.s d.m d.o d.α β).eval q₀ : ℚ)
> = S.cntraw (V.moveOf d) x (((V.mdom d).comps.get j).base)`

β is universally bound, appears ONLY as `C.T`'s last index, and the right
side does not mention it. `TargetIx n (bd s) bd m o` (§2.C) contains, for a
continuing outcome, `.cell h β'` for EVERY cell β' of the target block AND
`.term v` for EVERY absorbing label v (the `.term` constructor carries no
continuing/terminal premise). So for one fixed datum d the law pins ALL of
these entries to the ONE number `cntraw (moveOf d) x base` — but the note's
VAL(a) valuation ("every entry T_{m,o}^{α,β} is ONE polynomial … valued
correctly at every prime power q") makes the off-target entries COUNT ZERO:
`moveOf d`'s assignments all land at the tcell image (`MoveData.tgt`,
enforced BY TYPE per §2.C/§2.F), so the correct value of T at β ≠ tcell(α)
— and at every `.term v` index of a continuing outcome — is 0. Consequences:

1. **`valA_gate : ValA 3 gateFam gateMeas` (deferred to V6) is FALSE at the
   note-correct gate family.** Root datum d = the T21 letter's: the
   note-correct family has `T d.s d.m d.o d.α (.term ⟨(1,1),_⟩) = 0`
   (VLabel 3 is nonempty: (1,1) exists), while tbl_count forces its eval at
   q₀ = 2 to equal the F₂ count 2 — `0 = 2`, false. The only way to
   inhabit ValA is to COOK every junk entry equal to the row count
   (`T(junk .term of the m21 row) := X(X−1)`), i.e. a table family the
   note's VAL(a) REJECTS — the doctrine inversion ("a faithful interface
   must be FALSE for instances the note would reject", not force them).
2. Every OTHER consumer of the tables binds the index to the datum: V2-5's
   `pathProdPoly C γ := ∏ᵢ C.T (step-i data) (its TargetIx)`, V5-8's RHS
   `C.T d.s d.m d.o d.α (its TargetIx)`, V7-4c's kstep. The asymmetry
   localizes the bug: tbl_count's β must be the datum's own TargetIx
   (continuing: `.cell d.hc (tcell image)`; twin: the `.term` of
   `TermData.hv`'s label), exactly as those units already write it. As
   DISPLAYED, ValA ∧ (note-correct junk entries = 0) is unsatisfiable
   whenever any count is nonzero — every measured unit taking `hVA` (V4-1,
   V4-2, V2-5, V5-8, V7-5a, V7-6c) inherits the wrong hypothesis.
3. `tbl_countT` ("the [+T] twin over mdomT/cntrawT") carries the same shape
   and needs the same binding through `TermData.hv`.

(Checked against the alternative reading that the note's T might carry
per-(α, β) landing counts for ALL β: it does — and that count IS 0 off the
tcell image, which is the refutation, not the rescue.)

### M-2 — `HMCAug` is DERIVABLE from the XHD package: an explicit identity-refinement witness with cooked composite events satisfies it at EVERY instance, so the §2.G audit line "an unrelated witness stays impossible" is FALSE and the Lean Prop does not pin the note's (HMC-AUG) — the un-repaired residue of round-3 N-1's item 4

Offending display + comment (§2.G):

> `def HMCAug {n : ℕ} (S : StepSys n) : Prop :=
>   ∃ (R : Refinement n S) (TE' : TmplEvents n R.S') (D' : XHDd n R.S' TE'),
>     HMC TE' D'`
> `-- an unrelated witness stays impossible: D' is exact against TE''s
> -- process realization, TE' is tied to R.S''s step layer at length 1 …
> -- the refinement is keyed to S by construction.`

The keying constrains R (moves/assignments/masses) — it does NOT constrain
`TE'`'s COMPOSITE events, which are free data. Construction (checked field
by field against §2.G's displayed structures): given ANY pair
⟨TE, D : XHDd n S TE⟩ — the d-component of the XHD bundle every measured
unit holds —

- R := the identity refinement (B α := PUnit; cellEq the evident
  equivalence; moveProj/assignOf identities; dim_eq/mass_eq rfl;
  assign_cover a subsingleton-Σ bijection; twins likewise);
- dom′ by recursion on γ: dom′(.last m) := D.dom(.last m), dom′(.lastT m)
  := D.dom(.lastT m), dom′(.cons m γ) := the PRODUCT partition
  {L × M : L ∈ dom(.last m).comps, M ∈ dom′(γ).comps} (base = append,
  periods = zero-padded union; membership factorizes EXACTLY through
  Hpt.take/drop, pairwise disjointness inherited factor-wise);
- TE′: Box := fun _ _ => PUnit; tevt′(.last m) x h N := if 0 < cntraw
  then univ else ∅ (dually .lastT); tevt′(.cons m γ) x h N := if
  dom′(.cons m γ).Mem h then univ else ∅ (Classical.dec; the witness is a
  Prop, noncomputable is licit); tinst′ := tevt′; tmplLvl := 0.

All four TE ties hold: tevt_last_iff by construction; real_marks by
construction; marks_chains reduces to «dom′-membership ⟹ 1 ≤ chainCount»,
proved by induction on γ using D's OWN length-1 exactness (Mem →
D.no_stray → TReal TE → tevt_last_iff → 0 < cntraw) and ext_zc for the
tail. D′ is exact against TReal′ (length 1 via D's exactness + both
last-iffs; composites by definition, x-independently). And `HMC TE′ D′`
holds by the product-membership factorization. Hence **HMCAug S is a
theorem given the XHD d-face** — in exactly the sense round-3 N-1 item 4
flagged ("any Refinement carrying any XHDd witnesses it, undoing the X-13
repair's point") and the rev-4 disposition row claims restored ("every
(v)-tag restored"). Against the note: (HMC-AUG) is "a SEPARATE named
redesign hypothesis, NOT a consequence of HMC … finite-memory repair need
not be possible at all" (MOVES 8213–8220) and "not assumed anywhere"
(V.5(2)) — the Lean Prop is TRUE at instances where no finite-memory repair
of the REAL refined process exists, i.e. true where the note's hypothesis
is meant to be open/false; the type pins trivial content. No unit consumes
HMCAug (checked: V4-11 only compiles shapes; V7-1 carries the (v) line),
so no in-corpus conditionality collapses — the defect is the false
underivability-audit claim plus the doctrine violation on a NAMED note
hypothesis, the exact class this campaign has treated as rejection-grade
since C1. (Disposition hint, not a fix: make TE′ a PARAMETER of HMCAug
rather than ∃-bound — the note's "the refined process's domains" is not
expressible with ∃-quantified free composite events — or record the
derivability honestly and strike the impossibility comment.)

### M-3 — the N-2 pool-indexing ripple is INCOMPLETE: V1-6 and V1-7 still display the rev-3 pool-free `Hist`/`massOf` signatures (they no longer elaborate), and V7-4a's `Rep e τ := {x // S.zc x}` leaves the pool index unbound — while the frozen `MeasuredSide.Rep` is POOL-GLOBAL, so the forced resolution is a design decision the blueprint does not record

Three sites (grep-verified: these are the only survivors):

> V1-6: `theorem UA (P : C15Pack n S) {α β} (m : S.Move α β)
> (x : S.Hist α) … (q₀ ∈ S.Pools) :
> S.massOf m x h a q₀ = S.massOf m x h a' q₀`
> V1-7: `… ¬ (∀ {α β} (m : S.Move α β) x x' h a a' (q₀ …),
> S.massOf m x h a q₀ = S.massOf m x' h a' q₀)`
> V7-4a: `Rep e τ := {x // S.zc x}` (rep_ne ← zc_ne)

Under the REV-4 §2.B carriers, `S.Hist α` does not typecheck (`Hist : ℚ →
Cell → Type`) and `S.massOf m x h a q₀` is ill-formed (massOf's trailing
ℚ argument was REMOVED: "the pool rides the history index — the rev-3 free
ℚ argument is out"). V1-6/V1-7 are mechanical re-keys — but V7-4a is not:
the BUILT `MeasuredSide` (Defs.lean 160–192, re-read this round) types
`Rep : ∀ e, T.State e → Type` with `cellEvt : Rep e τ → Cell e τ → Hgt →
∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)` and `LedgerIV` quantifies (x : Rep)
and q₀ INDEPENDENTLY — one representative must serve EVERY pool, while a
rev-4 history lives at ONE pool. `{x // S.zc x}` has an unbound q₀ and no
choice is recorded. The choice is load-bearing: a Σ-representative (one
pool) makes xhd_sum/meas_card/part1/rep_indep junk-valued at mismatched
pools and underivable; the workable instantiation is the PER-POOL FAMILY
`Rep e τ := ∀ q₀, q₀ ∈ V.Pools → {x : S.Hist q₀ (cellOf τ) // S.zc x}`
(rep_ne then needs choice over pools, fine) WITH the off-pool junk value
`cellEvt … q₀ N := ∅` for q₀ ∉ Pools — which is exactly what the UNGUARDED
frozen `xhd_no_orphan` (∀ (q₀ : ℚ), checked against the built law) needs
to remain derivable, since `XHDdC.no_orphanC`'s contrapositive only fires
at pools. V7-6a1's leg "cellEvt = ∅ at EVERY N (definitional)" silently
assumes this junk-value choice. As DISPLAYED, V7-4a cannot produce the
frozen type (the C7 class, rev-4 edition) and two V1 units cannot
elaborate — E-phase blockers with one genuine unrecorded design decision.

---

## GAPS

**G-1 — V4-12's only-if status is asserted two contradictory ways.** §0's
banner: "the ONLY-IF leg is process-scoped and recorded NOT
interface-derivable"; V4-12(b): "it is NOT an interface-general theorem, by
(b′)"; but V4-12(b′) itself, in the same unit: "whether (b) is
interface-derivable from the FULL tie set is OPEN and CLAIMED NEITHER WAY."
(b′) is a SUM-LEVEL coincidence whose naive lift the blueprint's own
computation shows DIES against marks_chains — it proves only that (b) is
not a sum-arithmetic consequence, not that (b) fails as an interface
theorem. The record must say one thing; the honest version is (b′)'s.
Nothing mathematical rests on it ((b) is consumed by nothing).

**G-2 — the `hentCode` injectivity gloss is false as stated.** §2.D/V7-4b:
"distinct retained tuples get distinct codes" for
`(reads.map (fun R => Nat.pair R.h (zig R.gam))).foldr Nat.pair 0`. Fixed
read count: injective (Nat.pair is). Across read counts it is NOT:
Nat.pair 0 0 = 0 and zig 0 = 0, so `[x]` and `[x, R₀]` with R₀.h = 0,
R₀.gam = 0 fold to the SAME code — and components of one template CAN
expand to different read counts (self-loop depth slots). Harmless today —
this round's re-grep confirms NO MovesS law reads `hent` (Defs.lean 179
declaration, N2Carriers.lean 118 device `:= 0`, one comment; RS1Meas's
h_ent is its own ℕ argument) — but the claim needs a scope ("per fixed
read count") or a length-seeded fold, or a cited WF fact h_r ≥ 1.

---

## A. THE CHARGE ITEMS

### A.1 The HMC fix per the adjudication — the four-line proof FAILS; the count route, the audit, and both toys check (modulo M-2's HMCAug residue)

**Re-run of the round-3 four-line proof against the REV-4 carriers** (XHDd
exactness now against `TReal TE`, the composite `tevt`/`tinst` free, ties =
{tevt_last_iff ×2, real_marks, marks_chains}):

- (→) at a composite tail γ: dom(cons).Mem(h₁++h₂) → no_stray →
  TReal(cons) → real_marks → 0 < tinst ≤ (marks_chains) chainCount(cons)
  = Σ_a chainCount γ (ext a) h₂ — this yields Assign m x h₁ NONEMPTY
  (hence, via tevt_last_iff → no_orphan, the HEAD membership) and SOME
  positive tail count; but chainCount > 0 → TReal is NOT available at
  composite γ (marks_chains is one-directional), so the TAIL membership
  is unreachable. **BLOCKED.**
- (←): needs no_orphan at (.cons), i.e. TReal(cons) — nothing composes
  one-step realizations into a composite tevt (no composite law exists).
  **BLOCKED at every length.** The proof fails. ∎

**The honest derivable fragment** is exactly what §2.G/V4-11 record: at
single-step tails BOTH conjuncts of ⊆ come through the mark facts +
tevt_last_iff (the head as above; the tail via cntraw/cntrawT positivity),
so the toy must couple ⊇ — which V4-11's toy does. At composite tails the
head conjunct of ⊆ is still derivable but the conjunction is not; "blocked
in BOTH directions at composite tails" is accurate for the implications.

**The one-way count route survives as licensed** (V1-3(b)
`mem_chainCount_pos`): Mem → no_stray → TReal → real_marks → 0 < tinst →
marks_chains → 0 < chainCount — note-definitional at each link (realized
events have marks; marks are chains, MOVES 8225–8232); consumed by
V2-5/V4-5/V5-8 with base realizability through `MDomTie.mdom_eq`. The
converse is stated nowhere. V5-1's `MarkFiberTie` is guarded by TReal of
the composite ITSELF — re-ran the leak check: the guard blocks the (←)
manufacture and adds nothing to (→) beyond the recorded fragment. No
second HMC leak through XHDdC (length-1 only, agreeing with the process
keying through tevt_last_iff).

**V4-11 constructed** (satisfiability verified): V1-8a's system, 2-step
template with terminal tail; one-step domains = ℕ (one component); coupled
composite domain = ℕ² ∖ {(0,0)} = L((1,0);{(1,0),(0,1)}) ⊔ L((0,1);{(0,1)})
— listable, disjoint; tevt(.cons) := ∅ at (0,0), nonempty on the coupled
set; Box := Fin 1 keeps tinst.card ≤ 1 ≤ chainCount on the coupled set;
all four ties hold; HMC fails at (h₁,h₂) = (0,0): memberships true, product
membership false — ⊇ fails, exactly the recorded coupling direction.
**V4-12(c) constructed**: at that toy with E = h+1-type gate weights,
Σ over ℕ²∖{(0,0)} of q^{−(h₁+1)−(h₂+1)} = (Σ_ℕ q^{−(h+1)})² − q₀⁻² <
the product — ¬Factorizes ∧ ¬HMC, norm_num-scale. Both toys satisfiable
again; V1-8b's HMC-true toy brackets the kernel. The (v) ledger is
restored FOR HMC — the `hmc_theorem`-style discharge is dead, V5-5's hHMC
is undischargeable, V7-6c's tag has content. The HMCAug half of the
restoration FAILS — finding M-2.

### A.2 The pool layer — both gate refutations DIE; one layer down suffices (M-3's ripple aside)

- **T21 (2-vs-6) DEAD**: tbl_count's count is now `S.cntraw (V.moveOf d) x
  base` with `x : S.Hist q₀ _` — at q₀ = 2 the F₂-fiber (2), at q₀ = 3 the
  F₃-fiber (6); different fibers, one polynomial X(X−1) with eval 2 = 2,
  eval 3 = 6 — satisfiable, and DISPLAYED as the V2-4 acceptance numbers.
  (The β-slip M-1 is orthogonal: it falsifies the gate through the JUNK
  entries, not through pool-constancy.)
- **(X−1)² (1-vs-4) DEAD**: `CellPolyPack.count`'s cntc reads x's pool;
  eval 2 = 1 vs eval 3 = 4 displayed at §2.H's N-2 acceptance note.
- **One layer is enough** — grepped every count tie for a pool-free carrier
  equated to a q₀-family: size_count (Carrier q₀-indexed ✓), stInst_card
  (✓), ent_card/entCensus/EntCount/EntU (✓), evt_card (massOf rides x ✓),
  box_card (✓), valB (chainCount at x's pool = pathProdPoly.eval q₀ ✓),
  V5-8 (per-pool ✓), tinst/marks_chains (same pool ✓), GenSpec.base/part/
  twistOf/Val (q₀-indexed ✓), ObsCheck (✓). `emult : DCellO → ℕ` is
  pool-free BY DESIGN and correctly so (a shape-level L5 mark count; no law
  equates it to a q₀-varying quantity — V4-7/V4-8 use it as a multiplicity
  only). Two-horn closure: u_R_cnt/u_T/u_R_mass and twins compare
  SAME-POOL histories only — no cross-prime forcing. The remaining
  pool-free displays are the M-3 staleness (V1-6/V1-7/V7-4a), a ripple
  omission, not a forcing.

### A.3 kstep 0 = the Kronecker δ — verified against the frozen law and the built instance

`kstep 0 τ β q₀ := if τ = β then 1 else 0` (V7-4c; TableShape.deq supplies
decidability). Frozen `LedgerIV.hmc` (built Defs, re-read): ∀ k, kstep
(k+1) = Σ_γ kstep k · kstep 1 — at k = 0 the δ collapses the sum to
kstep 1 τ β ✓ hypothesis-free, exactly the blueprint's claim. Built device
instance `N2Carriers.lean` 101–105: comment "kstep 0 = 1 and the HMC scalar
law … holds" with `kstep := (…)^k` on 1×1 blocks — δ ≡ 1 there ✓ the cite
is accurate. Semantics: the empty path's ∏T = 1 and empty height sum = 1 —
the identity-matrix convention, consistent with kstep_one's k = 1 pin and
the k ≥ 1 template reading (∏T restored at REV 3, untouched).

### A.4 V4-12 vs MOVES 8596–8602 — EXACT

The blueprint's quotation is verbatim (compared word-for-word against
8596–8602; the trailing "Until HMC closes…" sentence is carried by V5-5's
hHMC and the kstep anti-smuggle pin, correctly). Quantifier: the iff is
read at the FIXED XHD weight system, ∀ template — (a) proves IF exactly
there (`Factorizes X D`, cons-splitting form, which iterates to the note's
∏ form); the rev-3 ∀-E-family quantifier is struck per the round-3
directive; (b) carries ONLY-IF as the named process-scoped `UpgradeOnlyIf`,
proved by nothing, consumed by nothing; (c) the fence at the false-HMC toy.
No silent weakening; the single-system-iff trap of the rev-3 adjudication
is gone with the process re-key (Factorizes no longer follows from the
definitional count — there is none at composites). One record defect
survives: the derivability-status contradiction, G-1.

### A.5 Disposition rows spot-verified (six, incl. the three PARTIALs)

- **N-1 row — accurate** (per §A.1; EXCEPT the "every (v)-tag restored"
  clause, which M-2 narrows: the HMC tags are restored, the HMCAug record
  is not).
- **N-2 row — accurate** (per §A.2; the "extended one layer down" claim is
  true of §2.B/2.F/2.G/2.H; M-3 records the three missed displays).
- **N-3 row — accurate** (per §A.3; cite N2Carriers 101–105 verified).
- **Y-6 PARTIAL — HONEST.** Fresh grep this round: `hent` in built MovesS =
  Defs.lean 179 (declaration) + N2Carriers.lean 118 (`:= fun _ _ _ => 0`)
  + one comment (N2EntFlow.lean 3); NO law reads it. RS1Meas.βmeas's
  h_ent is its own ℕ argument (Interfaces 33–37), independence being
  W2_xrb's CONCLUSION — the two-verdict record is faithful, SF-1's binding
  rule and re-open trigger stand. The VALUE upgrade is real (hentCode
  replaces the lossy sum) — modulo G-2's over-claimed injectivity gloss.
- **Y-14 PARTIAL ("LARGELY REPAIRED") — HONEST.** Verified: gProd's
  recursion displayed (no `…` body); cellEvtT/cntcT displayed; F8/F9
  add/mul tables pasted (spot-checked row structure; F4's remaining `..`
  is the instance-skeleton convention with per-law decide recorded — the
  F8/F9 inv tables are the recorded "one line each" residue);
  StageLawBurden's twelve laws TRANSCRIBED VERBATIM against the built
  `MovesS.SCSData` (Defs.lean 115–139 — all twelve match field-for-field:
  ℓpos/window_comp/flank_zero/sel_mem/res_sum/memberOf_inj/
  memberOf_ne_sel/sel_continuing/stage_D/stage_W/cluster_parent/
  cluster_child). One citation wart: V7-3d says "Defs.lean 1509–1531 of
  the pasted source" — the built Defs.lean is 559 lines (SCSData at
  97–139) and the MovesS blueprint's paste sits at ~591; the content
  check passes, the line cite is stale. Residuals (Stmt transcription
  rule, cast/menu one-liners) recorded in §5's inventory as claimed.
- **Y-16 PARTIAL — HONEST.** All five suites promoted to real IDs with
  files and grades (V3-3a–d, V3-5a–c, V4-6a–c, V5-2a–c, V7-5a–c —
  present, one display each); V7-1/V7-2a remain single
  structure-declaration units with the rationale DISPLAYED and the
  disagreement recorded — nothing hidden.
- (Also checked in passing: Y-8's two-verdict note matches my predecessor's
  §B; Y-10's shared-parameter form is in V7-7/§4.3 as claimed; Y-11's
  three-field roster matches the MovesS blueprint's frozen
  `Wsh17Package` 1321–1325; SF-2's owner-side objects verified —
  `tree_ne` only in the unbuilt contract shapes, `W7_cutWD` still carrying
  `isDeepSplit → ¬isEntrance` at 1288.)

### A.6 Fresh sweep — census exact; prior refutations re-armed, all dead; the sweep's new findings are M-1/M-2/M-3/G-1/G-2

- **Census EXACT**: 95 units = V0[4: 2e/2m] V1[10: 5e/5m] V2[10: 6e/4m]
  V3[17: 4e/11m/2h] V4[14: 3e/10m/1h] V5[12: 3e/8m/1h] V6[10: 5e/5m]
  V7[18: 4e/14m] = 32/59/4, per-unit recount matches §5's table; the
  rev-3→4 delta is exactly the promoted splits + V3-8a/b + V7-6a1/a2 +
  the two re-grades (V4-11 e→m, V4-12 h→m — both justified: the toy is a
  build, the generating-series leg is gone).
- **Round-2 F-refutations re-run against REV 4 — ALL SIX STILL DEAD**:
  F-1 (128 = (1/4)·512; 128·2³ = 2·2⁹ ✓, never 8192), F-2 (census q(q−1)
  deg 2 ≤ Went 3 ✓), F-3 (the LedgerIV suite re-derived field-by-field
  under the REV-4 MarkDisj/evt_disj_cell re-key — meas_card ←
  hMD + evt_card + w_eq + cp.count + no_strayC; d4r0's cross-(c,h) keys
  all distinct-stepKey instances ✓), F-4 ((q−1)²·G = TA2·G ✓,
  pool-consistent 1-vs-4), F-5 (sizeP revert intact at V7-5c; cellP_deg
  0/1-vs-3/2 gates pass; act_iff's nonemptiness step now DISPLAYED —
  G-1(round-3) repaired as claimed), F-6 (route roster; root m_2+1
  nonzero Jval ✓).
- Round-1/2 spot re-arms: C3's A2 chart complex untouched and re-checked
  (chart image = {h₂ ≥ 1, h₀ > 3h₂, h₀−h₂ odd} ✓ both directions;
  EA2.eval ![1,0] = 7 = the seal; 2E = 3(h₀+h₂)−1 ✓; the G-1/Y-13
  attribution now clean — MOVES 8844 displays the substitution, never
  "6t+3u+1"); X-1's all-empty adversary dies at the pool-guarded out_ne;
  X-12's cells partition the nonzero target (verified against FL/FS
  nonzero-coordinate defs); V6-1b's m_H3 row (0,1,4,10,35,56,84,165,286)
  recomputed ✓ incl. the q = 2 falsifier; V6-4a's 16-vs-128 marked pairs
  vs the 128 entrance-event card are the CORRECT two different objects
  (2^{3N−5} vs 2^{3N−2}), consistent with the note's V.6.4 record.
- MovesD/MovesS name keys re-verified at source (D4R1_SUM, D4R4_all,
  eligible_card_le, selRank, EligibleImage, E8/E9, gamTie/anchorTie at
  ShapeWF, ShapeRead.mbar; TableShape/MeasuredSide/LedgerIV field rosters
  vs §4.1's rows incl. the Y-17 mechanical-instance row).
- Y-2/Y-3/Y-9 spot-verified: outcome-keyed Outc with m₂'s three outcomes
  representable (two TermData + one MoveData); evt_disj_cell's stepKey
  excludes the mark coordinate, matching the note's (iv)-MEAS marked-space
  scoping, with MarkDisj the named within-cell burden (decide at gates via
  emult ≤ 1); tgt_supported's active-source + zc guards match the note's
  (ii-a) sentence.
- V3-8a's new `mass_summable` face: a fair typing of the note's own
  "CONVERGENCE of the full aggregate … GIVEN XHD-s on the shallow layer"
  (weight-only convergence alone does NOT bound census-weighted sums
  without (ENT-U), which the note pointedly withholds from ENT-AGG) —
  summability-only, so INIT-RAT stays undecided; flagged as REV-4 content
  at its site, honestly.

## B. DISPOSITION (hints, not fixes)

M-1 first — one-token class fix (bind β to the datum's TargetIx in
tbl_count/tbl_countT, as V2-5/V5-8/V7-4c already do), but it must ripple
through V4-1's display (whose β/βc tie should become explicit at the same
time). M-3 is mechanical at V1-6/V1-7 and a RECORDED design decision at
V7-4a (per-pool representative family + off-pool ∅ events — the resolution
the frozen unguarded xhd_no_orphan forces; display it, and re-state
rep_ne's choice step). M-2 is N-1's last leg and needs the same
adjudication discipline as N-1 itself: either HMCAug takes its TmplEvents
as a parameter (the ledger's TE, transported through R — then the ∃ has
content again) or the derivability is recorded and the impossibility
comment struck; do NOT quietly add composite ties (the §5 slot-9 fence is
correct that they re-prove HMC). G-1/G-2 are one-sentence record repairs.

*(End of round-4 fresh-instance audit. REJECT: 3 critical / 2 gap.)*
