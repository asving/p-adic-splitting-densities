# MovesS Lean blueprint REV 4 — fresh-instance confirmation audit (Fable #2)

- **Date:** 2026-07-28
- **Auditor:** fresh Fable instance #2 (no prior contact with any MovesS revision)
- **Scope:** REV 4 confirmation per `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, including
  the RS.2/S.4 re-derivation of U-24a1, the AVAgree ↔ (ii-c)/(e3)-FENCE identification,
  the R13 guard audit (both directions), a constructed minimal wild-pool instance,
  W-1/W-1m/W-10 typeability after the σ-index change, Mathlib name spot-checks in the
  pinned cache, and a fresh full sweep.
- **Texts:** blueprint `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` REV 4 (1019 lines, read in
  full); ground truth §S-RESUM rev 3+, `MOVES_2026-07-24.md` 11557–12430 (read in full,
  plus the adjacent pass records to 12577).

## Part I — the six charged verifications

### (1) U-24a1 re-derived from the note (CONFIRMED, one typing gap)

Re-derivation performed independently: fix a pool q₀ with package `P` and τA ∈ P.Act.
`recursion_meas` at (τA, q₀) gives βmeas(τA) = Σ_β evalK(τA,β)·βmeas(β) + evalBTerm(τA)
+ evalSplit(τA) (U-16a2's `evalRe`). Every `Kmat` entry is a finite sum of `tgP` values,
each in `OKat q₀` by `tg_ok` at every pool, and `OKat` is a Subring — so the `hok`
argument of `inactive_vanish` is dischargeable, and for β ∉ Act the coefficient dies.
`A_eval` renames the surviving coefficients to P.A. Hence β̂ = Â β̂ + b̂ with
b̂ = `bhatMeas` exactly (evalBTerm + split summand whose legs are the MEASURED values
`B.βmeas … (q₀^(δ:ℕ))`, well-typed by `pools_closed` — plain real numbers needing NO
package, NO activity, NO evaluation at the leg pool). `P.e0` + U-21c give
det(1 − Â) ≠ 0 (empty Act: the statement is vacuous over the empty index type, and
`Matrix.det_isEmpty` covers the det side); uniqueness of the solution of a nonsingular
linear system delivers β̂ = (1 − Â)⁻¹ b̂. **No leg needs all-activity the hypotheses
don't grant; no induction; no hok claim. The rev-3 C1 defect is genuinely repaired and
the former hard unit legitimately dissolves.** Residual: the ℚ/ℝ carrier mismatch
(Finding G1 below). Note also `act_target` is cited in U-24a1's hyp list but the
derivation needs only `inactive_vanish` (the symbolic-evaluated side) — harmless
over-citation, not a finding.

### (2) U-24a2 / AVAgree = the note's (ii-c) + (e3)-FENCE (CONFIRMED)

Blueprint: `AVAgree … v bA τ : Prop := ∃ hok : v ∈ OKat q₀, evalAt q₀ ⟨v, hok⟩ =
((1 - P.A)⁻¹ *ᵥ bA) τ`. Note (ii-c), S.4(ii): "the sealed check that the evaluated
object's q₀-value (R_σ(p) at δ = 1; a β_{e_j,τ_j}(p^{δ_j}) leg at δ > 1 — after
cancellation where needed) equals the active-subsystem solve there must pass BEFORE it
may be read off; a pole SURVIVING cancellation at a wild pool is (ii-c)'s FAIL."
The ∃ hok component IS "after cancellation where needed" (RatFunc is reduced;
denom.eval q₀ ≠ 0 = no surviving pole), and the equation IS "equals the
active-subsystem solve there". Note (e3)-FENCE, S.4: "REL.2(e3) … PRESUPPOSES that the
evaluated entry β_{e_j,τ_j}(q^{δ_j}) is well-defined (per-pool E0/ACT, THIS kernel) and
cannot SUPPLY that well-definedness." U-24a2 takes `hAV` as an explicit HYPOTHESIS and
its sketch is one rewrite through U-24a1 — the burden is consumed, never self-supplied;
"Uncancelled wild poles are EXCLUDED BY HYPOTHESIS — never claimed absent" is exactly
the fence's demand. **The rev-3 C1 half about U-24a self-supplying the (e3)-FENCE
burden is genuinely repaired.**

### (3) The activeState guards vs the note's scope (ONE UNDER-GUARD FOUND — Critical C1)

Note scope displays: "Scope: realized states only; formal rows of cells empty at q₀ are
OUTSIDE E0 and guarded by CTS-M(ii-c)" (S.4 kernel) and "Every probabilistic claim in
S.4/SQ.2 is about K_e restricted per CTS-M(ii) to the ACTIVE block" (S.0 ledger close).
Checked every guarded law both directions:
- `xhd_sum`/`xhd_no_stray`/`part1`/`rep_indep`/`meas_card`/`kstep_one`/`hmc`/
  `init_agg`/`init_count`/`ent_count_card`/`comp_once`: guards match the note's scope;
  every wave-2 consumer (U-9a at active states, U-9b through the all-active locus, U-10
  through `act_spec` on τA ∈ Act, U-24a1 at τA ∈ Act) fires them only where the guard
  holds — nothing is OVER-guarded relative to a consumer's need.
- `xhd_no_orphan`, `d4r0` unguarded: correct — emptiness/disjointness of events carries
  no realization content; satisfiable with all-empty events at unrealized states.
- `act_target` unguarded on the SOURCE: correct — it is S.7(iv)'s "verified vanishing
  … of every entry into an inactive cell" (target-side law); at unrealized sources the
  instance's kstep is conventional and 0 satisfies it.
- **UNDER-GUARDED: `RS1Bundle.recursion_meas` and its pinned twin `W3_recursion`** —
  the strongest per-(e, τ, q₀) measured claim in the corpus quantifies over ALL τ at
  ALL pools with no `activeState` guard. This is Finding C1 below: the R13 repair
  guarded LedgerIV but missed the measured fixpoint, which is exactly a "probabilistic
  claim … about K_e" in the note's sense.

### (4) Minimal wild-pool instance (CONSTRUCTED — instantiable EXCEPT through C1)

Constructed mentally at n = 1, `State 1 = Bool`, τ₁ inactive at q₀ = 2 only:
Pools = prime powers (closed, infinite) ✓; boxes nonempty ✓; all guarded ledger laws
vacuous at (τ₁, 2) and designable elsewhere ✓; `act_target` + `kstep_one` jointly force
measured rows into τ₁ to vanish at 2 — satisfiable by giving the relevant `tgP` a root
at 2 (note-faithful: "Per-shape emptiness at wild p is polynomial vanishing") ✓;
`tg_interp` at the unrealized source is satisfiable by defining `rowVal` as the formal
evaluation (consumed nowhere: `rep_indep`/`kstep_one` are guarded off) ✓;
`allActive_infinite` ✓; PoolHyp at 2 with Act = {τ₀}, `inactive_vanish` from the chosen
root, 1×1 EscapeE0 ✓; RatBurdens/SCSData/DegCons ✓. **The single unsatisfiable-in-
general law is the unguarded `recursion_meas`**: at (τ₁, 2) it demands βmeas solve the
junk-block row (I − D_{q₀})β_J = c with coefficients pinned to the formal evaluations by
`tg_interp`/`j_interp`; the note EXPLICITLY tolerates det(I − D_{q₀}) = 0 ("a zero is a
FINDING, not by itself a FAIL; a blanket det(I − D_{q₀}) ≠ 0 is NOT required", S.4(ii)),
and in that tolerated scenario the system can have no solution — the structure is then
uninstantiable at exactly the wild pools R13 set out to restore. See C1.

### (5) W-1/W-1m/W-10 typeability after the σ-index change (CONFIRMED)

σ everywhere `Multiset T.VType`; `Sigmas : Finset (Multiset T.VType)`. W1_RS1SH: `Rsh`
takes σ : Multiset VType (U-18) and `Rval : Multiset T.VType → ℚ → ℝ` — both sides
typecheck; the `∃ hok` is type-ascribed and `(evalAt p ⟨…⟩ : ℝ)` coerces ℚ → ℝ ✓.
W1m_marked: `markedPairing … : MuHat`, `.val : Qq`, evaluated against
`M.markedVal e q₀ : ℝ` ✓ (μ̂-to-μ̂ identification — the D8 fence is respected; the
unused `B` binder is cosmetic). W10_convergence: `HasSum` over the type `FI.Fib e τ σ'`
against `B.βmeas e he h_ent τ σ' q₀ : ℝ` ✓, matching S.2's unconditional CONVERGENCE
display. W-2/W-3/W-4/W-7/W-8 also re-typechecked ✓ (W-3 carries Finding C1's missing
guard; W-1m carries Finding G2's over-strength).

### (6) Mathlib names in the pinned cache (ALL VERIFIED)

`Matrix.cramer_eq_adjugate_mulVec` (Adjugate.lean:245) ✓ ·
`Matrix.det_smul_inv_mulVec_eq_cramer` (NonsingularInverse.lean:656) ✓ ·
`mul_adjugate`/`adjugate_mul` (Adjugate.lean:264/269) ✓ · `Matrix.isUnit_iff_isUnit_det`
✓ · `mul_nonsing_inv`/`nonsing_inv_mul` (NonsingularInverse.lean:217 ff.) ✓ ·
`Matrix.inv_def` (:172) ✓ · `Matrix.det_isEmpty` ✓ · `RatFunc.eval`/`eval_add`/
`eval_mul` hypothesis-carrying, exactly as D4 claims (AsPolynomial.lean:146/184/203) ✓ ·
`RatFunc.num_eq_zero_iff` (Basic.lean:999) ✓ · `Polynomial.eq_zero_of_infinite_isRoot`
(Roots.lean:145) ✓ · `IsFractionRing.lift` ✓ · `RingHom.map_det`
(Determinant/Basic.lean:318) ✓ · `Polynomial.eval_comp` ✓ · ℚ MetricSpace instance for
EscapeE0's Tendsto ✓ · U-9a's fiberwise cite exists as
`Finset.sum_fiberwise_of_maps_to`/`sum_fiberwise_eq_sum_filter` ✓.

## Part II — fresh-sweep confirmations (sample)

U-1/U-2/U-3/U-4/U-5/U-6 chain re-derived sound (m = 1 ⟹ `memberOf` domain empty via
`memberOf_ne_sel` + injectivity into Fin 1; singleton residual via `sel_mem`;
W′D′ = WD = e) — the R2-1/R2-2 repairs hold. U-8's regroup is definitional given
`verdictImage`'s by-construction coverage. U-16a1's `legFactor` indicator is exactly the
note's "τ-halted members contribute FACTOR 1 with σ_j their verdict value, per §T.4's
leaf convention" with member-indexed tuples (SIBLING INDEXING) and `powSubst μ.δ` the
(e2)-absolute base change. U-22's binder fix verified; its route needs only one
all-active pool and gets an infinite locus. U-27/U-28's checksum route is exactly S.5's
three displayed moves with the full inherited set explicit in RS4Chain and the
acceptance fence quoted. U-24b's `hread` honestly keeps the per-pool (ii-c) burden open
("activity alone does not discharge AVAgree at the legs" — correct as stated, since the
legs recurse through q₀^δ pools). The consumption-DAG discipline (nothing proves toward
`xrb`; U-24a1/a2/b consume it) matches S.1's binding CONSUMPTION form. Census total 45 =
18 easy + 27 medium verified by enumeration (but see G4). PART-2's surplus row has no
carrier ✓; ESCAPE-UNIF absent ✓; MuHat fence respected ✓; no `: True` / `∨ True` ✓.

## Part III — findings

### C1 (CRITICAL) — `recursion_meas` / `W3_recursion` lack the activity guard (the R13 repair's own residual)

Spec text (§2.D RS1Bundle; §2.E has the same quantifier):
> `recursion_meas : ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools) h_ent, βmeas e he h_ent τ σ' q₀ = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)`

Note displays: "Every probabilistic claim in S.4/SQ.2 is about K_e restricted per
CTS-M(ii) to the ACTIVE block" (S.0); "the junk-block determinants det(I − D_{q₀}) are
RECORDED (a zero is a FINDING, not by itself a FAIL; a blanket det(I − D_{q₀}) ≠ 0 is
NOT required)" (S.4(ii)).

The measured fixpoint is quantified over ALL τ at ALL pools. At a wild pool the rows at
INACTIVE τ demand that βmeas solve the junk-block system whose coefficients are pinned
to the formal evaluations by `tg_interp`/`j_interp`; when det(I − D_{q₀}) = 0 — a
scenario the note explicitly tolerates — that system can be inconsistent, making
RS1Bundle uninstantiable at exactly the wild pools the R13 ruling exists to make
instantiable, and making the pinned W-3 undischargeable by any measured argument (there
is no probabilistic content at an unrealized entrance). The field is silently STRONGER
than the note's displayed scope — the same defect class as the accepted Fable-C2, one
structure over. Repair is local: guard both by `M.activeState q₀ e τ`; U-24a1 is
unaffected (it fires the fixpoint at τA ∈ P.Act, where `act_spec` supplies the guard).

### G1 (GAP) — ℚ/ℝ carrier mismatch in the active-solve pairing

Spec text (U-24a1): `B.βmeas e he h_ent τA σ' q₀ = ((1 - P.A)⁻¹ *ᵥ bhatMeas P B σ'
h_ent) τA`; (§2.C): `AVAgree … (bA : P.Act → ℚ) … := ∃ hok, evalAt q₀ ⟨v, hok⟩ =
((1 - P.A)⁻¹ *ᵥ bA) τ`; (U-24a2): `hAV : AVAgree P (blockSolve …) (bhatMeas P B σ'
h_ent) τA`. `P.A : Matrix Act Act ℚ` but `bhatMeas` is ℝ-valued (its split legs are
`B.βmeas` values), so U-24a1's display does not typecheck and U-24a2 passes an ℝ-vector
where AVAgree demands `P.Act → ℚ`. Mechanical repair: `(1 - P.A.map (↑· : ℚ → ℝ))⁻¹`
(det preserved under `Rat.cast` by `RingHom.map_det` + injectivity), retype `bA :
P.Act → ℝ`, coerce `evalAt`'s output. No semantic content changes.

### G2 (GAP) — W1m_marked asserts pool-uniform read-off the note gates per pool

Spec text (§2.E): `def W1m_marked … : Prop := ∀ e he q₀ (h : q₀ ∈ M.Pools), ∃ hok :
(markedPairing …).val ∈ OKat q₀, (evalAt q₀ ⟨_, hok⟩ : ℝ) = M.markedVal e q₀`.
Note (S.4(ii)): "the sealed check … must pass BEFORE it may be read off; a pole
SURVIVING cancellation at a wild pool is (ii-c)'s FAIL". The pin demands ∃ hok (no
surviving pole) and value agreement at EVERY pool, wild included, with no (ii-c)-shaped
hypothesis — a discharge target stronger than the note's grant (the note makes passing
a gated burden, not a theorem). Consumed by nothing in wave 2 (U-25 explicitly defers),
so pin-fidelity only: thread an AVAgree-style hypothesis or restrict the pool family.

### G3 (GAP) — U-10's displayed signature omits `he : e ∈ Finset.Icc 1 n`

Spec text: `theorem ksub_pool (L : LedgerIV T M) (P : PoolHyp T M RB e hK q₀)
(τA : P.Act) : …` — but the sketch's chain (U-9a → `part1`, plus `rep_ne` for the
representative) requires e ∈ Icc 1 n (`part1 : ∀ e ∈ Finset.Icc 1 n, …`), and PoolHyp
carries no such bound. Add the binder (U-9a's own per-e scope is inherited from U-8,
which displays it).

### G4 (GAP) — stale layer headcounts after the REV-4 splits

Spec text: "Layer S2 — the ℚ(q) system and its solve [12]" (actual units 15 after
U-12b + the U-16a → a1/a2/a3 split); "Layer S4 — … [6]" (actual 7 after
U-24a → a1/a2). The global census "45 units = 18 easy / 27 medium" is CORRECT by
enumeration; only the two bracketed layer counts are stale. Bookkeeping.

## Part IV — REV-4 repair adjudication (the 6 round-3 findings)

- C1 (per-pool guards consumed): **GENUINE** — U-24a1/a2/b + `legs_reg` consume
  RegP/AVAgree exactly as required; the hard unit's dissolution is real (Part I(1)).
- C2 (act_row / guards): **GENUINE but INCOMPLETE** — the LedgerIV guards are right and
  match the quoted scope; the same scope was not applied to `recursion_meas`/W-3
  (new Critical C1 above is C2's residual, one structure over).
- G1 (kstep_one hK-free predicate): **GENUINE** — the existential-cast form
  `∃ h : μ.size = e, h ▸ μ.status = Sum.inr β` typechecks and needs no SCS/hK.
- G2 (W-1 rfl-conjunct struck): **GENUINE** — W1_RS1SH is the measured clause only;
  the symbolic half is definitional via U-18.
- G3 (U-16a split + halted-member indicator): **GENUINE** — the def-equation displays
  the factor-1/verdict-singleton clause verbatim against S.0's display.
- G4 (entLvl/entInst/ent_count_card): **GENUINE** — the count tie sits at the shape's
  own defining level; `ι_count` now has a counting referent.

## Counts and verdict

1 critical (C1) / 4 gaps (G1–G4). The critical is local (two missing guards, one
repair) but it breaks the blueprint's own R13 objective (wild-pool instantiability)
and the pinned W-3's dischargeability, so acceptance cannot stand on this text.

**REJECT (1 crit / 4 gap)**
