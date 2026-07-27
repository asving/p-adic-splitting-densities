# MovesS blueprint REV 3 — fresh-instance semantic audit (Fable)

Date: 2026-07-28 · Auditor: fresh Fable (no prior contact with any MovesS revision)
Scope: `lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md` REV 3 (898 lines, read in full)
against ground truth `lean/notes/MOVES_2026-07-24.md` lines 11557–12430 (§S-RESUM rev 6,
read in full; pass records excluded), INCLUDING the Mathlib name spot-check in
`lean/.lake/packages/mathlib`. Charge: `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` checklist +
the seven pressure points. Settled architecture (R7 event carrier, RatFunc ℚ + per-pool
OKat evaluation) executed, not re-litigated. I fix nothing.

## VERDICT: REJECT (2 crit / 4 gap)

---

## 1. Findings

### C1 (CRITICAL) — U-24a: the leg pools escape every hypothesis; the hard unit's
### statement is stronger than the note's display and its sketch cannot close it

Spec text (U-24a): "every ALL-ACTIVE pool q₀ ∈ allActivePools M … `(evalAt q₀
⟨blockSolve …⟩ : ℝ) = B.βmeas e he h_ent τ σ' q₀` (hok from entry_ok/tg_ok/j_ok
closure — the solve's entries are OK at all-active pools) … sketch: … split legs at
q₀^δ are handled by the induction hypothesis at smaller e — pools_closed keeps
q₀^δ ∈ Pools and the δ-leg pools all-active is NOT needed: legs enter through evalRe's
measured values directly".

Note displays (S.3, S.4):
> "NUMERIC evaluation of a leg at a pool q₀ = p^{δ_j} is guarded by S.4's PER-POOL
> E0/ACT (rev 3), never by this symbolic clause"
> "(e3)-FENCE … PRESUPPOSES that the evaluated entry β_{e_j,τ_j}(q^{δ_j}) is
> well-defined (per-pool E0/ACT, THIS kernel) and cannot SUPPLY that well-definedness"
> "symbolic det ≠ 0 prevents no zero or uncancelled pole at an individual q₀ = p^δ"

The defect, both halves:
(a) **hok is underivable.** `blockSolve e` contains `powSubst δ (blockSolve e')`
factors, whose reduced denominator can retain `det(1 − K_{e'})` composed with X^δ; its
evaluation at q₀ vanishes iff det_{e'}(q₀^δ) = 0 after cancellation. q₀ all-active
says NOTHING about q₀^δ: `pools_closed` gives only q₀^δ ∈ Pools, `pools_e0`/the U-24a
hypotheses supply PoolHyp (hence e0/U-21c) at ALL-ACTIVE pools only, and the note
explicitly allows junk-block det zeros at wild pools ("a zero is a FINDING"). A pole
surviving cancellation at a wild leg pool is exactly the open (ii-c) burden — the unit
asserts its absence with no hypothesis.
(b) **The equality needs the IH at q₀^δ.** The measured vector satisfies the evaluated
system with b̂ built from βmeas(q₀^δ) (recursion_meas); the evaluated blockSolve
satisfies the system with b built from eval_{q₀^δ}(blockSolve e'). Identifying the two
b's IS the induction hypothesis at pool q₀^δ — unavailable when q₀^δ is not all-active.
"Legs enter through evalRe's measured values directly" identifies only the FIRST
system's b; the dismissal is unjustified. Note-side, this identification at a wild pool
is the AVAgree/(ii-c) read-off — OPEN, per pool.

Corroborating symptom: `RegP` (§2.D) — the faithful per-relevant-pool package, the
exact quantifier of the note's ESCAPE(E0) display ("δ ranging over 1 AND every
base-change index a β_{e_j,τ_j}(q^{δ_j}) leg … consumes") — is defined and consumed by
NOTHING; `AVAgree` (W-6) is consumed only census-side (§4 item 8), never at U-24a's
legs. `RS4Chain.pools_e0`, commented "per-pool E0/ACT (CL-1)", narrows CL-1's
quantifier to the all-active locus. Repair R2-9 is genuine in direction (the βfam
circularity is gone; nothing proves toward `xrb`/`recursion_meas`; the consumption DAG
is acyclic) — but the replacement unit claims more than the note licenses. Fix shape
(not prescribed, for orientation only): either hypothesize PoolHyp + AVAgree-style
identification at every δ-leg pool (RegP-shaped), or restrict U-24a's locus to a
δ-closed all-active sub-locus with its own infinitude burden feeding U-24b.
U-24b inherits C1 through its dependence on U-24a; its own logic (U-18b uniqueness on
an infinite OK set) is sound.

### C2 (CRITICAL) — LedgerIV is jointly unsatisfiable at any pool with an inactive
### state: `act_row` asserts a condition the note nowhere displays

Spec text (§2.B): `act_row : ∀ e τ o q₀, q₀ ∈ M.Pools → ¬ M.activeState q₀ e τ →
M.rowVal e τ o q₀ = 0` together with `part1 : ∀ e ∈ Finset.Icc 1 n, ∀ τ x q₀, q₀ ∈
M.Pools → ∑ c, M.μcell e τ x c q₀ = 1` and `rep_indep : ∀ e τ o x q₀ … M.rowVal e τ o
q₀ = ∑ c ∈ cells o, M.μcell e τ x c q₀`, with `rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ,
Nonempty (Rep e τ)` (Rep pool-INDEPENDENT).

Derivation of the inconsistency: fix e ∈ Icc 1 n, τ, and q₀ ∈ Pools with τ inactive at
q₀; rep_ne gives x. Summing rep_indep over o and collapsing the cellOut fibers:
Σ_o rowVal = Σ_c μcell = 1 (part1). act_row gives each rowVal = 0, so 0 = 1. Hence any
LedgerIV instance must have EVERY state active at EVERY pool — the wild pools the note
insists exist ("At every NON-all-active pool q₀ (the wild pools; finitely many per e)",
S.4(ii)) are unrepresentable, W-11's real-CTS instantiation of LedgerIV is impossible
at n ≥ 2, and the whole ACT apparatus (act_spec, inactive_vanish, AVAgree, U-21c's
empty case) is dead code under the ledger. U-29's synthetic all-active n = 2 instance
cannot detect this.

Note displays: the only displayed vanishing is INTO inactive cells — S.7(iv):
> "the verified vanishing at p = 2, 3 of every entry into an inactive cell"
(= act_target, which is faithful), and the scoping is restriction, not zero rows:
> "Scope: realized states only; formal rows of cells empty at q₀ are OUTSIDE E0 and
> guarded by CTS-M(ii-c)" (S.4); "Every probabilistic claim … is about K_e restricted
> per CTS-M(ii) to the ACTIVE block" (S.0).
`act_row` (a zero-row law for unrealized sources) appears nowhere in the note; and
part1/rep_indep unguarded by activity silently strengthen the note's "per
representative" (= per REALIZED state) PART-1 into an assertion about masses of
non-events — the exact trap CL-5 item (1) names. Repair R2-6 is therefore PARTIAL:
kstep/activeState/entCount/comp_once genuinely added, but the act clause is wrong.
Fix shape: guard part1/rep_indep/xhd_sum/meas_card by `activeState q₀ e τ` (or make
Rep pool-indexed with rep_ne at active pairs), and drop act_row or restate it as the
note's realized-scope convention; keep act_target.

### G1 (GAP) — `kstep_one`'s `targets β` is not typeable inside LedgerIV as specified

Spec text: `kstep_one : … M.kstep 1 e τ β q₀ = ∑ o ∈ {o | routeOf (T.odata e τ o) =
.kcol ∧ targets β}.toFinset, M.rowVal e τ o q₀` with the design note "`targets β`
abbreviates the unique continuing member landing in β, elaborated with the `hK` cast at
phase E". LedgerIV's parameters are (T, M) only: no SCSData, no DegCons, no hK is in
scope, so the named "hK cast" cannot be used there. The predicate IS expressible
hK-free (∃ h : μ.size = e, h ▸ μ.status = Sum.inr β), but the blueprint does not pin
that form; as written the field's elaboration is unresolved. Note display it must
match: K_e entrywise "Σ_{m: s→s′} Σ_{o continuing} T·G" (S.0). One line pinning the
existential-cast form fixes it.

### G2 (GAP) — pinned W-1's first conjunct is definitionally vacuous

Spec text (§2.E): `def W1_RS1SH … : Prop := ∀ σ ∈ C.Sigmas, Rsh … σ = ∑ Ŝ ∈ F.Sh,
(C.WshP Ŝ).val * shConv … Ŝ σ ∧ …`. U-18 DEFINES `Rsh … (WshP) (σ) := ∑ Ŝ ∈ F.Sh,
(WshP Ŝ).val * shConv … Ŝ σ` — the conjunct is `rfl`-true, so the pin labeled "RS.1-SH
verbatim (S.2)" carries its entire content in the second (evaluation) clause. The note's
RS.1-SH is the identity for the DENSITY "R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ … ∏ β…" (S.2) — i.e.
the measured Rval clause; the symbolic conjunct should be struck or W-1's docstring
must say the symbolic half is definitional. Minor co-defects: the second `∀ σ ∈
C.Sigmas` shadows the first inside its body (misparenthesized as displayed), and the
`∃ hok` lacks the type ascription its sibling `rsh_interp` correctly carries. Not
mislabeled as an in-section derivation, so GAP not CRITICAL.

### G3 (GAP) — U-16a is a hidden multi-def unit and omits the halted-member clause

Spec text (U-16a): "defines `bSplit` … AND `evalRe` … AND `consumedDeltas`" (plus the
kTarget sorry region) — three load-bearing definitions in one "medium" unit, and the
spec nowhere states the display's routing of halted members inside the convolution:
> "the product ranges over ALL branch members — τ-halted members contribute FACTOR 1
> with σ_j their verdict value, per §T.4's leaf convention" (S.0, b_e^split).
REV 2 is retired and U-16a is not in §3c, so no surviving text pins whether a halted
member's σ_j is forced to its verdict singleton in the decomposition subtype — the
phase-E elaborator is left to reinvent the display. One displayed def-equation for
bSplit's summand (halted legs pinned, continuing legs via powSubst/blockSolve) closes it.

### G4 (GAP) — `entCount` has no counting-carrier tie

Spec text: `entCount : ∀ e τ, EntShape e τ → ℚ → ℕ` whose only law is `ι_count :
… ((ιP e τ ε).count.eval q₀ : ℚ) = M.entCount e τ ε q₀`. This equates the ENT-COUNT
polynomial with an otherwise-unconstrained data field — asserting it asserts nothing
about counts (contrast ιshH, which init_count ties to `card (entEvtH …)`). The note's
ledger item (8) demands products "tied to a cylinder mass or a full count …
ι_{e,ε,β₀} and I^ent_{ε,β₀}"; the mass tie (init_count) is present and faithful, so
this is a GAP, not a CRITICAL: the I^ent half is aspirational labeling until entCount
gets an event-card law (or the docstring assigns the tie to wave 4 explicitly).

---

## 2. Pressure-point record (charge items, including the clean ones)

1. **U-24a**: circularity genuinely gone (no symbolic β in RS1Bundle; nothing proves
   toward xrb/recursion_meas; DAG acyclic) — but CRITICAL C1 (leg pools).
2. **rep_indep**: faithful to RS.0(β)'s consumed RS.0(α) = "the MEASURED row (T·G) is
   identical from every representative of the cell (weighted form)" — row-level
   (per-outcome T·G/J), weighted (μcell masses, not cardinalities), ∀-representative,
   with rowVal naming the common value; no cellwise strengthening. Clean in itself;
   participates in C2 only through the missing activity guard.
3. **(K-SUB) orientation**: the NOTE has T·G on the NON-split routes (K_e columns +
   b^{term,fin}) and J on split ("This is NOT the marked per-continuing-branch T·G";
   "the third summand being exactly Σ_o J_{τ,o}"). The blueprint's routing (tg_interp
   guarded `≠ .split`, j_interp `= .split`, routedMass, U-10's derivation) MATCHES the
   note. The charge's parenthetical had it reversed; the repair is right.
4. **U-22 binders**: `e` bound inside both hypothesis quantifiers and the conclusion
   (∀ e ∈ Icc 1 n each); `hK e ‹_›` resolves against the same-binder membership;
   typeable. Sketch sound (one all-active pool suffices; U-27 in deps is harmless
   overlisting). Clean.
5. **(m, c) dispatch**: routeOf reproduces the note's three-row partition exactly;
   c ≤ m is structural (filter length), so "c ≥ 1 with m = 1 forces c = 1" holds;
   U-1's iff-triple provable by omega; multi-member terminal verdicts carried
   (Outcome.verdicts = ALL halted members' multiset, no m = 1 restriction — agreement
   check (i)); U-2/U-3 = (K-TRI)/K-column agreement verbatim; U-4's m = 1 argument now
   closes with memberOf_ne_sel + flank_zero (R2-1/2 genuine); U-6 delivers (SCS) and
   the hK argument. Clean.
6. **Ledger fields**: act_row CRITICAL (C2); kstep_one GAP (G1); entCount GAP (G4);
   xhd_sum/no_stray/no_orphan a faithful counting-native two-sided XHD-d (∀-x
   quantified both directions), d4r0 the (c,h)-pairwise event disjointness, meas_card
   the R7 idiom, init_agg = ENT-AGG, init_count the (COMP-h) cylinder tie, comp_once
   THE one height sum with (COMP-Σ) = hmc's duty (design note makes "no further height
   sum" structural), act_target = the note's displayed vanishing INTO inactive cells,
   PolyGeom restores the (iv)-POLY degree bounds + XHD-s geometric denominators in
   cleared form (the W6 denominator q² + q + 1 ∣ 1 − X³ instance fits). All clean.
7. **Pinned syncs**: W-1m typeable as written (unused B parameter, cosmetic); W-10
   typeable (he inferred from βmeas's dependent type; HasSum over FI.Fib needs no
   countability to state — ctbl carried separately); W-2/W-3/W-4/W-1e are the fields'
   own statements (discharge targets for the wave-4 construction — consistent design);
   W-11 as an explicit process gate is an honest carve-out (real-object instantiation
   is not internalizable); W-1 has GAP G2.

Also checked, clean: U-8/U-9a/U-9b's (K-SUB) chain traces the note's bracket (GIVEN
(iv) ledger + DEG-CONS + classification + (SCS)) with = 1 landing at U-9b via
infinitude; U-10's sub-distribution rows derived, not assumed (R2-12 genuine); (BDY)
U-7a/b/c + W-8 match the edge/node/inclusive-entering-read convention exactly
(Wcharge = Icc 0 fe, βcharge = Icc (fe+1) L); Shape/ShapeFam/W-7 = CUT-3's choice-free
one-shape-per-tree; U-16c's σ′-totalized bTot is the correct convolution total with
halted legs 1; U-25's markedPairing is ι-once-left with the MuHat no-Add fence and the
identification deferred to W-1m (never claimed); U-28 carries the full displayed
inherited set explicitly with the acceptance fence verbatim, and its
infinitely-many-evaluations step is sound with hden supplied by rsh_interp's hok;
U-29's claim honestly renamed (R11); EscapeE0 = the note's A^k𝟙 → 0 display; U-21b/c's
empty/nonempty split matches "realized states only"; census 41 = 15/25/1 consistent;
DAG acyclic.

## 3. Repair adjudication (the 20 REV-2 findings)

Genuine: R2-1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, and 18
(modulo G2's W-1 conjunct). PARTIAL: **R2-6** (kstep/activeState/counts added, but
act_row introduces C2 and kstep_one carries G1); **R2-9** (circularity genuinely
removed, but the replacement U-24a carries C1). 18 genuine / 2 partial; both partials
are the two criticals — the defect count is structural, not scattered.

## 4. Mathlib spot-check (pinned cache, `lean/.lake/packages/mathlib`)

All verified present, compatible signatures: `Polynomial.eq_zero_of_infinite_isRoot`
(Algebra/Polynomial/Roots.lean); `Matrix.cramer_eq_adjugate_mulVec` (Adjugate.lean:245),
`mul_adjugate`/`adjugate_mul`; `det_smul_inv_mulVec_eq_cramer`
(NonsingularInverse.lean:656), `isUnit_iff_isUnit_det` (:127), `inv_def` (:172),
`mul_nonsing_inv`/`nonsing_inv_mul` (:211/:217); `Matrix.det_isEmpty`
(Determinant/Basic.lean:94), `RingHom.map_det` (:318); `RatFunc.instField`
(FieldTheory/RatFunc/Basic.lean:480), `num_eq_zero_iff` (:999),
`denom_mul_dvd`/`denom_add_dvd` (:1062/:1067 — the OKat closure), `RatFunc.eval_add`/
`eval_mul` (AsPolynomial.lean:184/:203, hypothesis-carrying exactly as D4 says);
`IsFractionRing.lift` (RingTheory/Localization/FractionRing.lean:347; needs
`Injective g`, supplied by U-12's δ ≥ 1 argument); `Matrix.exists_mulVec_eq_zero_iff`
(ToLinearEquiv.lean — U-21c's unstated kernel step, available);
`Finset.sum_fiberwise` (BigOperators/Group/Finset/Basic.lean). No GAP/CRITICAL here.

## VERDICT: REJECT (2 crit / 4 gap)

Both criticals sit in the per-pool evaluation architecture (the wild/leg pools), not in
the combinatorial or symbolic layers, which are now faithful. A targeted REV 4
(activity-guarded ledger + a RegP-shaped or locus-restricted U-24a, plus the four gap
lines) is the indicated repair scope.
