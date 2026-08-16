import Uniformity

/-!
# Chapter D — GAUGE + CERTIFICATE T-CHAIN: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-D_gauge_tchain.md` (68 nodes D.01–D.68; the T1 cocycle, the
T3 telescope, the T4 certificate witness and the T5 w-frame), landed in the isolated `leanspec`
environment **before** the chapter-D fleet fires, in the blueprint's node order.

**STATE: OPEN (stage-0e gate executed 2026-08-16).** Chapter D has landed nothing in
`leanfinal` (`grep` for `Density.Gauge` / `NormSection` / `GaugeArena` / `GentowW` over
`leanfinal/Uniformity/`: zero hits), so every theorem-shaped stub is in the UNLANDED state of
`Leanspec.lean`'s stub lifecycle — an `axiom` at the exact signed type. Nothing is retired;
there is no name collision with `Uniformity.*`.

**Wrapper choice, declared per GC-6.6:** wrapper `namespace LeanspecD` (the CHAP-B/`LeanspecB`
route that CHAP-D §12 itself prescribes), NOT the ChapG retire-to-examples route. Consequently
the blueprint's `namespace Uniformity.Density.Gauge` headers in the SIGNATURE blocks are
DROPPED here and every declaration is flat inside `LeanspecD`; the landed-side namespace
assignment (**everything** → `Uniformity.Density.Gauge`; chapter D declares no theorem about a
landed object) is what the fleet must land.

**This file is never imported by `leanfinal` or `leancheck`.** It carries `axiom`s by design;
it is an interface contract, not mathematics. `sorry` appears nowhere, `native_decide` appears
nowhere, and the file elaborates with `autoImplicit`/`relaxedAutoImplicit` **off**.
It is NOT wired into `leanspec/Leanspec.lean` by this unit (a ChapF gate agent was running
concurrently; the roll-up import is an ORCHESTRATOR item). Build it with
`lake build Leanspec.ChapD`.

**The B.42 binder rule is in force throughout:** every truth-bearing hypothesis is written
INLINE in its declaration's binder list. This file has NO section `variable` block at all, so
no ENV-D1…ENV-D5 under- or over-binding of the B.42 class is possible in it — and one of the
findings below (D-D4) is that rule biting at DEFINITION level.

## Census (mechanical, `grep` over this file)

| kind | count | note |
|---|---:|---|
| `structure` (real bodies) | **5** | `NormSection`, `GaugeArena`, `ReadBundle`, `BoundaryReadPort`, `CertFrame` |
| `def` / `noncomputable def`, blueprint | **30** | §12(b)'s def layer — §12's inventory names 29 and OMITS `varpiSection` (finding D-D10) |
| `def`, stub-side helpers | **2** | `levelOneHeight` (D.17), `GaugeArena.chiK` (D.39/D.40, whose signature §12 rule 5 explicitly leaves to stub time) |
| `axiom` stubs of theorem-shaped rows | **63** | one per signed theorem/lemma display, siblings expanded per each node's STATEMENT text (§12 estimated ≈ 48; the gap is the declared siblings) |
| `theorem`, PROVED (not stubs) | **11** | 4 kernel-membership helpers + `iexp_one` + `levelOneHeight_ker_dvd` + `chi_varpi_mem_ker` + `GaugeArena.rho_mem_ker` (all needed INSIDE `def` bodies or to state a signature at all) + the 2 D-D12 defect witnesses + `certWitness_touched` |
| gate-local / witness `def`s | **17** | §10's frames and the two non-vacuity witnesses; not blueprint declarations |
| gate `example`s, ALL EXECUTED | **40** | §10 (D.65–D.67) + the D.06 orientation-table block |

**98 signed blueprint declarations** (5 + 30 + 63). Nodes with NO declaration, exactly as the
blueprint signs them: **D.36, D.42, D.43, D.53, D.54, D.56, D.61, D.64** (tables, interfaces,
records) and D.06/D.65–D.68 whose Lean content is counted above. Per §12 rule 4, **no
`[supplied-by: chapter C]` row is axiomatized here** — axiomatizing a supplier's theorem would
fake the discharge.

## Gate order (GC-6.6(c) / CHAP-H §15) as actually run

(a) **the six FRAGILE signatures of §12 rule 1 first** — D.17 `levelOneArena` (`GaugeArena`
fields over `Multiplicative (ℤ × ℤ)` with `MonoidHom.ker`), D.08 (`res` on subtype elements,
membership as explicit `mem_ker` proofs and NOT tactic holes), D.28 (the
`Basis`/`repr`/`algebraMap` stack), D.39 `compData` (kernel proof terms inside a `def`), D.46
(`CertFrame`'s `Finsupp` codomain), and the D.65 𝔽₄ carrier; (b) the 30 `def` bodies + 5
structures, REAL; (c) **the numeric gates EXECUTED at `q = 2` AND `q = 3` (+ `p = 5`)** — 40
`decide` checks, every committed expected value reproduced; (d) only then the 63 `axiom` stubs.

**Executed values.** `q = 2` (F4-JOINT, `e₁ = 2, f₁ = 2, h = 1, u₂ = 3`, `η = ω` of order 3 —
GC-11's `e > 1 ∧ f > 1` witness): `iexp 2 1 · = · % 2` on `k = −3…5`; live wrap = odd/odd;
`⌊s·i(3)/2⌋ = (0,0,1,1)`; `Wfloor 2 1 3 3 · = (1,1,0)`; the telescope `(1,1,ω,ω)`; the `μ = 3`
canonical triple with **all three entries scored** — `Γ = (1,ω,ω)`, `u(β) = (ω,ω,ω²)`,
canonical `= (ω,ω²,1)`, and the slotwise cancellation `Γ_t·u(β_t) = w^s`; `ϑ₂ = ω ≠ 1` (the
gauge-naive kill); `ψ^{(w)}`'s coefficients `(ω,1)`. `q = 3` (X frame, `p = 3`, `e₁ = 2,
f₁ = 1, h = 1, η = 2, u₂ = 3`): `iexp`/`aexp`/`qexp` on `k = −2…6`; `(C2-wrap)`, `(C5-carry)`
and D.27's binary-carry law executed on grids INCLUDING negative heights; the telescope
`(1,1,2,2,1)` with the involution against a committed `Θ`; the D.28 criterion firing;
**`thresholdTheta 3 3 1 = (10,7,4)` — FR-M3's committed thresholds** — with the `[12,7,4]`
self-shadow separator (`ν₀ = 12 > 10 = Θ₀`, `ω₀ = 0`; `j = 1,2` attain) in `ℕ` and in `ℕ∞`,
and D.45's antitony. `p = 5` (FRAME-C): `ϑ = (1,1,2,2,4)` ASSEMBLED from D.18's formula,
`U = (1,3,2,1,4)` as literal data, both runner obligations `w^s = U(s)·ϑ_s` and
`U(s) = Θ_s·w^s` scored from the assembled definitions (never from the endpoint formula), **the
non-character check `χ(1)² = 1 ≠ 2 = χ(2)`**, `δ = χ(2) = 2`, `χ(6) = 3`, and the CMP
comparison `ρ_t = 3ρ̂_t2^{−t} = (3,3,1,4)`.

**THE ϑ TABLE IS NOW EXECUTABLE (GC-14 / append #54's trap).** The D.06 block scores, at
FRAME-C with `f₃ = 5`: the involution `Θ_s·ϑ_s = 1` on `s = 0…5`; the top-slot anchor
`ϑ(f₃−1) = 1`; **row 4's reciprocal relation `ϑ_{G2}(t)·vartheta_{f₃−t} = 1`** (the exact
GENTOW2/GENTOW5-A1 pair append #54 names); and the **numerical distinctness** of the two
orientations, so a silent row-1-for-row-4 swap is a failing `decide`. Two of these are new
teeth: the wrong-orientation B-law (`U(s) = ϑ_s·w^s`) now FAILS at `s = 2`, and the
orientation swap FAILS at `t = 1` and `t = 4`. **Verdict on the table itself: the four rows
plus the B-law direction block plus the top-slot anchor are MUTUALLY CONSISTENT** — checked
symbolically row by row and then executed. No sign error found.

## THE DEFECT LIST (stage-0e gate, 2026-08-16)

Recorded here and in the 0e report; **NOT repaired in the blueprint** (§12 rule 5 / CHAP-H §15
rule 5: elaboration failures in a stub are blueprint defects, versioned by dated append in the
blueprint, never patched in `leanspec`). Every stub-side adjustment is listed; nothing was
adjusted silently.

* **D-D12 — D.62's `(H-VARTHETA-RES)_i` CARRIER IS VACUOUS (refuted, machine-checked).**
  `HVarthetaRes G K N v := ∃ A : GaugeArena G K N, A.v = v`, and `GaugeArena` has NO field
  tying `res` to an ambient residue map, so the TRIVIAL hom `1 : ker v →* Kˣ` inhabits it. The
  two PROVED theorems `hvarthetaRes_of_exact_height` / `hvarthetaRes_iff` in §9 below show
  `HVarthetaRes G K N v ↔ ∀ k, v (N.n k) = ofAdd k` — the carrier says NOTHING about
  `ϑ_{i,s} ∈ K_iˣ` and is discharged by `⟨v, hv, 1⟩`. Chapter I would therefore carry a
  Display-A `∀ i ≥ 3` conjunct that is provable from an exact-height fact, and D.63's
  `VarthetaWConjunct` degenerates to `Wle` plus that fact. D-H3's "formally STRONGER than the
  sitewise clauses" holds for D.07 used as a THEOREM HYPOTHESIS but is FALSE in the existential
  direction D.62 uses. *Class: refuted statement (vacuous carrier).* **This is §14 item 2(iii)
  answered, and it is a stop-the-line item for chapter I's conjunct bookkeeping.** Repair
  direction (owner's, not applied): state `HVarthetaRes` against a GIVEN ambient residue datum
  and require the arena's `res` to agree with it on the ϑ-quotients, or state the sitewise
  clause directly. Needs a DECISION block in CHAP-D §9 and a re-signed D.62/D.63.
  **[EXECUTED at A-D.2, 2026-08-16 — see the RE-SIGN LOG below: DECISION D-2 picks the
  sitewise form; D.62 re-signed, the committed form kept as `HVarthetaResVoided` with the
  witnesses re-pointed at it.]**
* **D-D1 — the §10 gate lines DO NOT RUN as written: `iexp` is not `decide`-reducible (hard).**
  `iexp` goes through `(h : ZMod e₁)⁻¹`; `ZMod.inv` routes through `Nat.gcdA`/`Nat.xgcd`, which
  do not kernel-reduce. Even `((1 : ℕ) : ZMod 2)⁻¹ = 1` is not `decide`-able at the pin, so
  D.65/D.66/D.67's `:= by decide` lines all fail, and so does every `Θ_s = ϑ_s⁻¹` spelling.
  *Class: definition not computable for the gate it is gated by.* **Stub-side repair, no
  expected value changed:** a PROVED helper `iexp_one : iexp e₁ 1 k = ((k : ZMod e₁)).val`
  (all three gate frames have `h = 1`) plus `simp only [<local defs>, iexp_one]` before every
  `decide`; and `Θ` committed as literal data with the involution `Θ_s·ϑ_s = 1` as the check
  that it IS the inverse. **The fleet must not write the landed gates with a bare `decide`.**
* **D-D2 — D.17 `levelOneArena` is signed with NO body**, although §12 rule 2 requires the def
  layer to land real and D.17's PROOF gives the five-step construction. *Class: def with no
  body (the ChapG D2 / ChapB B-D2 / ChapE E-D5 class).* **Landed REAL here** (the height hom,
  the kernel-divisibility lemma `levelOneHeight_ker_dvd`, and `res = η^{i/e₁}` as a genuine
  `MonoidHom`) — which required one new public helper, `levelOneHeight`. **Consequence the DAG
  does not record:** `exact_height` can only be discharged from D.13's `iexp_aexp_spec`, so
  `levelOneArena`'s axiom footprint carries it (`#print axioms` in the census block shows
  `iexp_aexp_spec`) — a DEFINITIONAL dependency D.17 → D.13 that §11's edge census lists only
  as a lemma dependency.
* **D-D3 — D.39 `compData` is likewise signed with no body, and D.40's signature is explicitly
  schematic.** Landed real; this required a second new public name, `GaugeArena.chiK` (the
  blueprint's `chiK`, used unquoted in D.40's `(chiK-of-H₀-term)`), plus a proved helper
  `GaugeArena.rho_mem_ker`. D.40's two legs are now spelled against those names. *Class:
  elision the stub must resolve; §12 rule 5 licenses it, and this records what was chosen.*
* **D-D4 — ENV-D4's `{π : O}` cannot be implicit: `π` occurs only in `liftC6`'s BODY**, so
  every call site (`liftC6 e₁ h σ M l` in D.25 clauses 2–4, D.26, D.28) would leave an
  unsolvable implicit-argument metavariable. Made EXPLICIT and first, matching the landed
  convention (`Uniformity.Density.Leaf.digAt (π : O)`). *Class: binder that must be in the
  binder list — the B.42 lesson recurring at definition level.* `f₁` is made implicit in
  `liftC6` (it is determined by `l`) and stays explicit in `gammaCoord`, as the blueprint
  writes them.
* **D-D5 — D.28's `Basis` DOES NOT EXIST at the pin.** The constant is `Module.Basis`
  (`Module.Basis (Fin f₁) (ResidueField O) K₁`). *Class: stale API name (training-data smell,
  the E-D1 class).*
* **D-D6 — D.25b clause 3's `Finset.filter (fun r => l r ≠ 0)` has no `DecidablePred`** over an
  abstract residue field. `liftC6_support` is declared inside `section ClassicalSupport` /
  `open scoped Classical`. The fleet's landed form must carry that or switch to a
  `∀ j, j ∈ support ↔ ∃ r, l r ≠ 0 ∧ j = …` membership formulation. *Class: missing
  decidability.*
* **D-D7 — D.28's signature has four type slips under its `…` elisions.** (i) `Wfloor` takes
  `u₂ : ℤ` but D.28 binds `u₂ : ℕ` (cast supplied); (ii) `t : Fin f₂` is fed to `Wfloor`'s
  `t : ℕ` and to `f₂ - t` (casts supplied); (iii) `b.repr (…)` is a `Finsupp` where `liftC6`
  wants `Fin f₁ → ResidueField O` (coercion supplied, written `fun r => b.repr (…) r`);
  (iv) `(hσ : …)`/`(hπ : Irreducible π) …` are elided and expanded from the STATEMENT text.
  *Class: elision + spelling; no strength change.*
* **D-D8 — D.19's residue corollary and D.21 are UNSTATABLE if `levelOneArena` is opaque.**
  Both apply `(levelOneArena …).res` to a subtype element, whose membership proof needs
  `(levelOneArena …).v` to be transparent. With D-D2's real body plus the proved
  `chi_varpi_mem_ker` they are statable as signed. **Flag for the fleet: landing D.17 as an
  axiom would make D.19's `res_chi_varpi` and D.21's `levelOne_rho` unstatable without extra
  membership hypotheses.**
* **D-D9 — D.65 leg 3's three vectors are listed in ASCENDING `s` (= DESCENDING slot `t`), and
  the blueprint never says so.** Read in slot order the committed vectors are wrong: `Γ` in
  slot order is `(ω, ω, 1)` and `u(β)` is `(ω², ω, ω)`. The gate below scores them in the
  blueprint's order and says which. *Class: unstated indexing convention — the
  wrong-but-well-typed class §12 rule 3 warns a stub gate cannot catch mechanically (found by
  recomputing, then executed).*
* **D-D10 — census slips.** (i) §12's def inventory names **29** and omits `varpiSection`
  (D.19's sibling def); the true blueprint def count is **30**. (ii) §12's "`theorem` ≈ 48"
  undercounts: expanding the declared siblings per each node's STATEMENT text gives **63**
  theorem-shaped declarations. §13/§14 should count against the corrected figures.
* **D-D11 — D.41's clause 1 is `rfl` and carries no content.** `wtwist δ rhat = δ^{deg} •
  rhat.comp (C δ⁻¹ * X)` IS `wtwist`'s definition, so the informative half of `t3_route` is
  only the separability iff. Related spelling ambiguity, resolved here: the blueprint's
  `(w⁻¹ : K)` in D.34/D.41 is ambiguous between `((w : K))⁻¹` and `((w⁻¹ : Kˣ) : K)`; the
  `Kˣ`-inverse reading is signed (they are equal, and it makes D.41 clause 1 definitional).
* **D-D13 (minor) — D.21's `hu : 0 ≤ u₂` is unnecessary.** Lean's `Int./` and `%` are
  `ediv`/`emod` at the pin (`(-3)/2 = -2`, `(-3) % 2 = 1`), so `iexp u₂ = (i₀u₂) % e₁` and
  `qexp u₂ = (i₀u₂)/e₁` hold at every sign; the sign hypothesis is signed as given (faithful)
  but is dead weight. Same answer for §14 item 5's negative-height question, and the D.65/D.66
  tables execute it at `k < 0`.
* **D-D14 (minor) — D.29's `read_n` field is derivable from `ladder_mult` at `s = 1`.** Both
  are separate corpus clauses (`(C3-ladder-unit)`, `(C3-ladder-multiplicativity)`), so both are
  signed, but a `ReadBundle` instance need only supply one.

## RE-SIGN LOG (post-0e, blueprint-authorized amendments)

* **A-D.2 (2026-08-16, Display-A carrier adjudication — executes D-D12's owed re-sign).**
  **D.62 `HVarthetaRes` RE-SIGNED at the sitewise ambient-residue form** (blueprint DECISION
  D-2: `EFF.T1.09`'s display verbatim — the ambient residue of every ϑ-quotient lands in the
  level field, as a unit); the committed existential form is KEPT, named-and-voided, as
  `HVarthetaResVoided`, with the two D-D12 witnesses re-pointed at it
  (`hvarthetaResVoided_of_exact_height`/`hvarthetaResVoided_iff`). New PROVED theorem
  `hvarthetaRes_of_arena_agree` restores D-H3's "formally stronger" claim honestly (an
  ambient-agreeing arena discharges the sitewise clause). **D.63 `VarthetaWConjunct`:
  signature byte-unchanged; consumption re-signed** — `HVR` instantiates at the A-D.2 form
  only. Census deltas: `def` 30 → 31 (`HVarthetaResVoided`), proved `theorem` 11 → 12
  (`hvarthetaRes_of_arena_agree`; the 2 D-D12 witnesses renamed). Non-triviality
  countermodel: `verification/om4_resign_nontriviality.lean`. Full record: CHAP-D DECISION
  D-2 + amendment A-D.2 (§9 dated append).

## FINDINGS about the gate frames themselves (not blueprint defects — battery coverage)

* **D-F1 — the X frame cannot separate `aexp` from `qexp`.** At `h = 1` (hence `i₀ = 1`)
  `qexp ≡ aexp` identically, so D.66's leg-1 tables score the same function twice and an
  `aexp`/`qexp` confusion survives there. A frame with `h > 1` is needed to score D.15
  independently.
* **D-F2 — FRAME-C's committed `ϑ`/`U` tables run `s = 0…4`, but the D.06 table's
  `ϑ_{G2}(t) = Θ(f₃−t)` at the BOTTOM slot `t = 0` reads `s = f₃ = 5`** — one step beyond the
  committed range. The battery as declared does not cover the bottom slot. Extended here by the
  assembled formula (`ϑ₅ = 2^{⌊5/2⌋} = 4`, `Θ₅ = 4`) and executed.
* **D-F3 — FRAME-C has `ϑ₂ = ϑ₃ = 2`** (both floors `⌊s/2⌋` equal 1), so an index-shift mutant
  SURVIVES at the middle slots: `Θ_2 = Θ_3` is executed below as a warning. The orientation
  distinctness check must be scored at `t = 1` or `t = 4`. A fleet agent scoring only the
  middle of the table would miss the very mutant the table exists to catch.
* **Non-vacuity, executed:** `BoundaryReadPort` and `CertFrame` are both INHABITED (witnesses
  below), the latter with (FLOOR) satisfied AND its coordinate `j = 0` TOUCHED — so D.37/D.38
  and D.46–D.52 are not vacuous. The port witness's `U` is forced to `w^s·ϑ⁻¹`, i.e. D.38's own
  conclusion, from the port axioms alone.

## Stub-side decisions (SD-n), all recorded, none silent

* **SD-1** — the four kernel-membership facts (`mem_ker_div`, `varthetaEl_mem_ker`,
  `thetaEl_mem_ker`, `tau_mem_ker`) are PROVED, not stubbed: D.08's `def` bodies apply `A.res`
  to subtype elements, and an `axiom` inside a definition would put a stub in the def layer.
* **SD-2** — `levelOneHeight` is a new public name (D-D2).
* **SD-3** — `chi_varpi_mem_ker` is proved for the same reason (D-D8).
* **SD-4** — `π` explicit in `liftC6`/`gammaCoord` (D-D4).
* **SD-5** — `open scoped Classical` around `liftC6_support` (D-D6).
* **SD-6** — **the 𝔽₄ carrier choice, made here as §10's ⚠ instructs.** `GaloisField 2 2` and
  `AdjoinRoot (X²+X+1 : (ZMod 2)[X])` are quotient constructions with no computable
  `DecidableEq` at the pin, so no `decide` runs in them. The F4-JOINT legs run in the
  **discrete-log model**: `ω` has order 3 and every quantity in D.65's legs 2–4 is a power of
  `ω`, so `⟨ω⟩ ≅ (ZMod 3, +)` carries them faithfully — products become sums and every
  committed expected value is an exponent. The `q = 3` and `p = 5` frames need no such move
  (`ZMod 3`, `ZMod 5` are `Fin`-backed).
* **SD-7** — `Θ` tables committed as literal data with the involution as their certificate
  (D-D1), so no gate depends on `ZMod.inv`.

## Cross-chapter checks executed here

* **The GC-13 fence holds:** no `[supplied-by: chapter C]` content is axiomatized. D.42, D.43,
  D.53, D.54, D.56 and D.61 declare nothing (§12 rule 4), and no chapter-C/E/F node ID is
  guessed anywhere in this file.
* **The chapter-B consumption typechecks by name at the pin:**
  `Uniformity.Density.Leaf.suppVal` (B.14) is consumed at D.25/D.28 and
  `Uniformity.Density.Leaf.digAt` (B.21) at D.26, both at their landed signatures
  (`leanfinal/Uniformity/ChapB/B14.lean:55`, `B21.lean:46`). B.07/B.08/B.11/B.15/B.22 are
  proof-level dependencies of those nodes and appear in no signature.
* **The GC-6.2 namespace fence holds:** no `Uniformity.Density.Leaf`/`.Menu`/`.Induction`
  declaration is EXTENDED; chapter B's two names are READ, fully qualified.
* **`FactorizationType` is correctly absent.** GC-4 note: chapter D emits no σ, and no
  declaration here mentions `FactorizationType` — so chapter E's defect E-D8 (the wrong
  fully-qualified `Uniformity.Density.FactorizationType`) has no analogue in chapter D.

<!-- RESUME: chapter-D stub gate COMPLETE — 98 signed blueprint declarations (5 structures /
30 defs / 63 axiom stubs) + 11 proved helpers/witnesses + 40 EXECUTED gate examples;
`lake build Leanspec.ChapD` green, 0 errors, 0 warnings, 0 sorry, no native_decide.
Defect list D-D1…D-D14 + findings D-F1…D-F3 + decisions SD-1…SD-7 recorded above.
Next actions (orchestrator): (i) **D-D12 is stop-the-line for chapter I** — D.62/D.63 need a
re-signed carrier before I's Display-A block is written; (ii) dated append of this defect list
into `blueprint/CHAP-D_gauge_tchain.md`; (iii) wire `import Leanspec.ChapD` into
`leanspec/Leanspec.lean` once the concurrent ChapF gate lands; (iv) §13.4's retained
regressions `verification/chapD_frameC`, `chapD_f4joint`, `chapD_xframe`, `chapD_frm3_slack`,
`chapD_t1_countermodels` are still owed (Python mirrors); (v) the §14 codex cross-read items
1, 2 and 8 are now partly discharged mechanically (item 1: table consistent + executed;
item 2(iii): REFUTED, see D-D12; item 8: every expected value recomputed and executed) —
items 3, 4, 6, 7, 9, 10, 11, 12 remain. -->
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanspecD

/-! ## §3 — THE ABSTRACT COCYCLE ARENA AND THE ϑ ORIENTATION TABLE (D.01–D.12) -/

/-- **D.01** [def] A **normalizer section**: heights to monomials, normalized at height zero
(`(C2-zero-normalizer)`, `EFF.T1.02`; `N(0) = 1`, `EFF.T3.01`). -/
structure NormSection (G : Type*) [CommGroup G] where
  n : ℤ → G
  n_zero : n 0 = 1

/-- **D.02** [def] The T1 normalizer two-cocycle `τ_N(a,b) = N(a)N(b)/N(a+b)`
(`EFF.T1.08`, `EFF.T3.02`). -/
def NormSection.tau {G : Type*} [CommGroup G] (N : NormSection G) (a b : ℤ) : G :=
  N.n a * N.n b * (N.n (a + b))⁻¹

/-- **D.02** [lemma] Endpoint `τ(0,a) = 1`. -/
axiom NormSection.tau_zero_left {G : Type*} [CommGroup G] (N : NormSection G) (a : ℤ) :
    N.tau 0 a = 1

/-- **D.02** [lemma] Endpoint `τ(a,0) = 1` (the blueprint's "private corollary"; signed here). -/
axiom NormSection.tau_zero_right {G : Type*} [CommGroup G] (N : NormSection G) (a : ℤ) :
    N.tau a 0 = 1

/-- **D.03** [lemma] The cocycle law `(C2-cocycle)` (`EFF.T1.08`). -/
axiom NormSection.tau_cocycle {G : Type*} [CommGroup G] (N : NormSection G) (a b c : ℤ) :
    N.tau a b * N.tau (a + b) c = N.tau b c * N.tau a (b + c)

/-- **D.04** [def] T1's telescope orientation: the group element under
`ϑ_{i,s} = res(n̂(u)^s / n̂(su))` (`EFF.T1.09` `(C2-vartheta)`).
ORIENTATION: T1 two-index; see D.06 (`D-THETA-TABLE`). -/
def NormSection.varthetaEl {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) (s : ℕ) : G :=
  (N.n q) ^ s * (N.n (s * q))⁻¹

/-- **D.04** [def] The B-law orientation `Θ_N(s;q) = ϑ_N(s;q)⁻¹` (`EFF.T3.04` `(T1-THETA)`,
`EFF.T1.14` `(C3-Theta)`). ORIENTATION: inverse of `varthetaEl`; see D.06. -/
def NormSection.thetaEl {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) (s : ℕ) : G :=
  N.n (s * q) * ((N.n q) ^ s)⁻¹

/-- **D.05** [lemma] Telescope endpoint `ϑ_{i,0} = 1` (`EFF.T1.10`). -/
axiom NormSection.varthetaEl_zero {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) :
    N.varthetaEl q 0 = 1

/-- **D.05** [lemma] Telescope endpoint `ϑ_{i,1} = 1` (`EFF.T1.10`). -/
axiom NormSection.varthetaEl_one {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) :
    N.varthetaEl q 1 = 1

/-- **D.05** [lemma] The telescope recursion `(C2-recursion)`/`(T1-TEL)`, group level
(`EFF.T1.10`, `EFF.T3.03`). -/
axiom NormSection.varthetaEl_succ {G : Type*} [CommGroup G]
    (N : NormSection G) (q : ℤ) (s : ℕ) :
    N.varthetaEl q (s + 1) = N.varthetaEl q s * N.tau (s * q) q

/-- **D.06** ★ `D-THETA-TABLE`. The two telescope orientations are mutually inverse:
`Θ_N(s;q) · ϑ_N(s;q) = 1` (T3 §8.1 check 2's content, group level). Consumers: see the
four-way orientation table at blueprint anchor `D-THETA-TABLE` (CHAP-D node D.06). -/
axiom NormSection.thetaEl_mul_varthetaEl {G : Type*} [CommGroup G]
    (N : NormSection G) (q : ℤ) (s : ℕ) :
    N.thetaEl q s * N.varthetaEl q s = 1

/-- **D.07** [def] DECISION D-1's residue interface. Instantiations: level 1 = D.17
(η-powers); level 2 = GENTOW2's letter group `⟨γ₁, γ₂⟩` (`EFF.GENTOW2.42`, supplied by
chapter C); depth `i ≥ 3` = exactly the `(H-VARTHETA-RES)_i` conditionality (D.67 in
blueprint numbering = `HVarthetaRes`, D.62) — supplying this structure at depth IS the
hypothesis. FAITHFULNESS: formally stronger than the sitewise clauses; see CHAP-D honesty
item D-H3 and §13 item 2. -/
structure GaugeArena (G : Type*) [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) where
  v : G →* Multiplicative ℤ
  exact_height : ∀ k : ℤ, v (N.n k) = Multiplicative.ofAdd k
  res : MonoidHom.ker v →* Kˣ

/-! ### §3 kernel-membership helpers (real proofs — see stub-side note SD-1)

`D.08`'s and `D.39`'s `def` bodies apply `A.res` to subtype elements, so the membership facts
must be REAL (an `axiom` here would put a stub inside a definition). They are proved. -/

theorem GaugeArena.mem_ker_div {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) {x y : G} (h : A.v x = A.v y) : x * y⁻¹ ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

theorem GaugeArena.varthetaEl_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    N.varthetaEl q s ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.varthetaEl, map_mul, map_inv, map_pow, A.exact_height,
    A.exact_height, ← ofAdd_nsmul]
  simp

theorem GaugeArena.thetaEl_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    N.thetaEl q s ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.thetaEl, map_mul, map_inv, map_pow, A.exact_height,
    A.exact_height, ← ofAdd_nsmul]
  simp

theorem GaugeArena.tau_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (a b : ℤ) :
    N.tau a b ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.tau, map_mul, map_mul, map_inv, A.exact_height,
    A.exact_height, A.exact_height]
  simp [← ofAdd_add]

/-- **D.08** [def] The `K`-valued telescope, T1 orientation (`EFF.T1.09`). -/
noncomputable def GaugeArena.vartheta {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) : Kˣ :=
  A.res ⟨N.varthetaEl q s, A.varthetaEl_mem_ker q s⟩

/-- **D.08** [def] The `K`-valued telescope, B-law (inverse) orientation (`EFF.T3.04`). -/
noncomputable def GaugeArena.theta {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) : Kˣ :=
  A.res ⟨N.thetaEl q s, A.thetaEl_mem_ker q s⟩

/-- **D.08** [lemma] The residue recursion `(C2-recursion)`, `K`-half (`EFF.T1.10`). -/
axiom GaugeArena.vartheta_succ {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    A.vartheta q (s + 1) = A.vartheta q s * A.res ⟨N.tau (s * q) q, A.tau_mem_ker (s * q) q⟩

/-- **D.09** [lemma] The top-slot anchor, `s = 0` leg (`EFF.T3.03`, `EFF.GENTOW2.41`). -/
axiom GaugeArena.vartheta_zero {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) : A.vartheta q 0 = 1

/-- **D.09** [lemma] The top-slot anchor, `s = 1` leg — GENTOW2's `ϑ(f₃−1) = 1`. -/
axiom GaugeArena.vartheta_one {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) : A.vartheta q 1 = 1

/-- **D.10** [lemma] The orientation involution, `K`-valued (T3 §8.1 check 2). -/
axiom GaugeArena.theta_mul_vartheta {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    A.theta q s * A.vartheta q s = 1

/-- **D.10** [def] GENTOW2's single-argument slot-indexed ϑ (`D-THETA-TABLE` row 1):
`ϑ(t) = Θ(f−t)`. -/
noncomputable def GaugeArena.varthetaG2 {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (f t : ℕ) : Kˣ := A.theta q (f - t)

/-- **D.10** [lemma] The defining lemma of the row-1 alias. -/
axiom GaugeArena.varthetaG2_eq {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (f t : ℕ) :
    A.varthetaG2 q f t = (A.vartheta q (f - t))⁻¹

/-- **D.11** [lemma] The descending bracket telescope `(T3-BKT)`, group level
(`EFF.T3.15`). -/
axiom NormSection.tau_bracket_telescope {G : Type*} [CommGroup G]
    (N : NormSection G) (H₀ q : ℤ) (t : ℕ) :
    (Finset.range t).prod (fun r => N.tau (H₀ - (r + 1) * q) q)
      = N.n (H₀ - t * q) * (N.n q) ^ t * (N.n H₀)⁻¹

/-- **D.12** [def] The pointwise section ratio (`EFF.T3.12`; T3's `χ`, renamed from HETOW's
`τ` to avoid collision with the two-argument cocycle — the spec's own renaming). -/
def NormSection.chi {G : Type*} [CommGroup G] (Nhat N : NormSection G) (k : ℤ) : G :=
  Nhat.n k * (N.n k)⁻¹

/-- **D.12** [lemma] The coboundary law `(T3-COB)` (`EFF.T3.16`). ⚠ NO character law for `χ`
is asserted anywhere — see the executed non-character check in the D.67 gate. -/
axiom NormSection.chi_coboundary {G : Type*} [CommGroup G]
    (Nhat N : NormSection G) (a b : ℤ) :
    NormSection.chi Nhat N a * NormSection.chi Nhat N b * (NormSection.chi Nhat N (a + b))⁻¹
      = Nhat.tau a b * (N.tau a b)⁻¹

/-! ## §4 — THE LEVEL-1 GAUGE LAYER (D.13–D.28) -/

/-- **D.13** [def] `i(k)`: the reduced x-exponent of the level-1 normalizer
`n̂₁(k) = x^{i(k)}π^{a(k)}` (`EFF.T1.01`). -/
def iexp (e₁ h : ℕ) (k : ℤ) : ℕ := ((k : ZMod e₁) * (h : ZMod e₁)⁻¹).val

/-- **D.13** [def] `a(k)`: the π-exponent, fixed by the exact-height identity. -/
def aexp (e₁ h : ℕ) (k : ℤ) : ℤ := (k - iexp e₁ h k * h) / e₁

/-- **D.13** [lemma] The exact-height identity `i(k)h + a(k)e₁ = k`, `0 ≤ i(k) < e₁`. -/
axiom iexp_aexp_spec (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    iexp e₁ h k < e₁ ∧ (iexp e₁ h k : ℤ) * h + aexp e₁ h k * e₁ = k

/-- **D.13** [lemma, stub-side helper] `iexp` at `h = 1`. PROVED, and load-bearing for the
whole §10 gate programme: `ZMod.inv` routes through `Nat.gcdA` and does NOT kernel-reduce, so
no `decide` can evaluate `iexp` as defined (defect D-D1). Every gate frame of this chapter has
`h = 1`, where the `ZMod`-inverse disappears and the reduced form IS `decide`-able. -/
theorem iexp_one (e₁ : ℕ) (k : ℤ) : iexp e₁ 1 k = ((k : ZMod e₁)).val := by simp [iexp]

/-- **D.14** [def] The wrap bit `wrap(a,b) = ⌊(i(a)+i(b))/e₁⌋` (`EFF.T1.07`). -/
def wrap (e₁ h : ℕ) (a b : ℤ) : ℕ := (iexp e₁ h a + iexp e₁ h b) / e₁

/-- **D.14** [lemma] `(C2-wrap)`: the wrap identity and `wrap ∈ {0,1}` (`EFF.T1.07`). -/
axiom iexp_add_wrap (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    iexp e₁ h a + iexp e₁ h b = iexp e₁ h (a + b) + e₁ * wrap e₁ h a b
    ∧ wrap e₁ h a b ≤ 1

/-- **D.15** [def] The carry exponent `q(k) = (i₀k − i(k))/e₁` (`EFF.T1.19`). -/
def qexp (e₁ h : ℕ) (k : ℤ) : ℤ := (iexp e₁ h 1 * k - iexp e₁ h k) / e₁

/-- **D.15** [lemma] `(C5-carry)`: `q(a+b) = q(a)+q(b)+wrap(a,b)` (`EFF.T1.19`). -/
axiom qexp_add (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    qexp e₁ h (a + b) = qexp e₁ h a + qexp e₁ h b + wrap e₁ h a b

/-- **D.16** [def] The level-1 telescope exponent `W(t) = ⌊(f₂−t)i(u₂)/e₁⌋` (`EFF.T1.10`). -/
def Wfloor (e₁ h : ℕ) (u₂ : ℤ) (f₂ t : ℕ) : ℕ := (f₂ - t) * iexp e₁ h u₂ / e₁

/-- **D.17** [def, stub-side helper] The level-1 height homomorphism `v (i,a) = i·h + a·e₁`,
named so that `levelOneArena`'s body and its kernel lemma can be written (note SD-2). -/
def levelOneHeight (e₁ h : ℕ) : Multiplicative (ℤ × ℤ) →* Multiplicative ℤ where
  toFun g :=
    Multiplicative.ofAdd ((Multiplicative.toAdd g).1 * h + (Multiplicative.toAdd g).2 * e₁)
  map_one' := by simp
  map_mul' x y := by simp [← ofAdd_add]; ring

/-- **D.17** [def] The level-1 section `n k = x^{i(k)}π^{a(k)}`, in the exponent lattice
`Multiplicative (ℤ × ℤ)` (`EFF.T1.01`). -/
def levelOneSection (e₁ h : ℕ) : NormSection (Multiplicative (ℤ × ℤ)) where
  n k := Multiplicative.ofAdd ((iexp e₁ h k : ℤ), aexp e₁ h k)
  n_zero := by simp [iexp, aexp]

/-- **D.17** [lemma, stub-side helper] The kernel of the level-1 height hom lies in
`e₁ · ℤ` in its x-coordinate — the fact that makes `res` a homomorphism (D.17's PROOF step 4,
here PROVED because it is needed inside a `def` body). -/
theorem levelOneHeight_ker_dvd (e₁ h : ℕ) (hcop : Nat.Coprime h e₁)
    {g : Multiplicative (ℤ × ℤ)} (hg : g ∈ MonoidHom.ker (levelOneHeight e₁ h)) :
    (e₁ : ℤ) ∣ (Multiplicative.toAdd g).1 := by
  rw [MonoidHom.mem_ker] at hg
  have h0 : (Multiplicative.toAdd g).1 * h + (Multiplicative.toAdd g).2 * e₁ = 0 := by
    simp only [levelOneHeight, MonoidHom.coe_mk, OneHom.coe_mk, ofAdd_eq_one] at hg
    exact hg
  have hd : (e₁ : ℤ) ∣ (Multiplicative.toAdd g).1 * h :=
    ⟨-(Multiplicative.toAdd g).2, by linarith⟩
  exact (Nat.isCoprime_iff_coprime.mpr hcop.symm).dvd_of_dvd_mul_right hd

/-- **D.17** [def] The level-1 arena: height hom `v (i,a) = i·h + a·e₁`, residue hom
`(i,a) ↦ η^{i/e₁}` on the value-zero (cyclic) subgroup generated by the exponent pair of
`x^{e₁}/π^h` (`EFF.T1.01`, `EFF.T1.04`). -/
noncomputable def levelOneArena (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) :
    GaugeArena (Multiplicative (ℤ × ℤ)) K (levelOneSection e₁ h) where
  v := levelOneHeight e₁ h
  exact_height k := by
    simp only [levelOneSection, levelOneHeight, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    exact congrArg Multiplicative.ofAdd (iexp_aexp_spec e₁ h he hcop k).2
  res :=
    { toFun := fun g => η ^ ((Multiplicative.toAdd (g : Multiplicative (ℤ × ℤ))).1 / (e₁ : ℤ))
      map_one' := by simp
      map_mul' := by
        intro g₁ g₂
        have h1 := levelOneHeight_ker_dvd e₁ h hcop g₁.2
        simp only [Subgroup.coe_mul, toAdd_mul, Prod.fst_add]
        rw [Int.add_ediv_of_dvd_left h1, zpow_add] }

/-- **D.18** [lemma] `(C2-level-1)`: `ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}` — "the exponent has the
displayed positive sign" (`EFF.T1.10`). ORIENTATION: T1 two-index (D.06 row 2). -/
axiom levelOneArena_vartheta (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (u₂ : ℤ) (s : ℕ) :
    (levelOneArena e₁ h he hcop η).vartheta u₂ s = η ^ (s * iexp e₁ h u₂ / e₁)

/-- **D.19** [def] The `ϖ`-section `k ↦ ϖ^k` with `ϖ = n̂₁(1)` (`EFF.T1.19`). -/
def varpiSection (e₁ h : ℕ) : NormSection (Multiplicative (ℤ × ℤ)) where
  n k := (levelOneSection e₁ h).n 1 ^ k
  n_zero := zpow_zero _

/-- **D.19** [lemma, stub-side helper] The `χ`-ratio against the `ϖ`-section is value-zero
(needed to state D.19's and D.21's residue clauses at all — note SD-3). -/
theorem chi_varpi_mem_ker (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (k : ℤ) :
    NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k
      ∈ MonoidHom.ker (levelOneArena e₁ h he hcop η).v := by
  refine (levelOneArena e₁ h he hcop η).mem_ker_div ?_
  have h2 : (levelOneArena e₁ h he hcop η).v ((varpiSection e₁ h).n k)
      = Multiplicative.ofAdd k := by
    show (levelOneArena e₁ h he hcop η).v ((levelOneSection e₁ h).n 1 ^ k) = _
    rw [map_zpow, (levelOneArena e₁ h he hcop η).exact_height]
    simp [← ofAdd_zsmul]
  rw [(levelOneArena e₁ h he hcop η).exact_height, h2]

/-- **D.19** [lemma] `(C5-monomial-ratio)`: `n(k)/ϖ^k = (x^{e₁}/π^h)^{−q(k)}`
(`EFF.T1.19`). ⚠ direction: `chi Nhat N k = n̂(k)·(n(k))⁻¹` with `Nhat := levelOneSection`,
`N := varpiSection`, matching the corpus's `n(k)/ϖ^k`. -/
axiom chi_varpi (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k
      = Multiplicative.ofAdd ((-(qexp e₁ h k)) • ((e₁ : ℤ), -(h : ℤ)))

/-- **D.19** [lemma] The residue corollary: `res(n(k)/ϖ^k) = η^{−q(k)}`. -/
axiom res_chi_varpi (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (k : ℤ) :
    (levelOneArena e₁ h he hcop η).res
        ⟨NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k,
          chi_varpi_mem_ker e₁ h he hcop η k⟩
      = η ^ (-(qexp e₁ h k))

/-- **D.20** [lemma] `(C1-general)`: the letter factorization `z = η'·ρ` for three elements
of equal height (`EFF.T1.05`). FENCE: no arbitrary-depth canonical-letter monomiality
follows; `(C1-JA-specialization)` needs `(H-JA-CONJ)_i`, an inline hypothesis of consumers,
never stated here. -/
axiom GaugeArena.res_ratio_factor {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (a b c : G) (hab : A.v a = A.v b) (hbc : A.v b = A.v c) :
    A.res ⟨a * c⁻¹, A.mem_ker_div (hab.trans hbc)⟩
      = A.res ⟨a * b⁻¹, A.mem_ker_div hab⟩ * A.res ⟨b * c⁻¹, A.mem_ker_div hbc⟩

/-- **D.21** [lemma] `(C1-level-2)`: `ρ₁ = η^{−⌊ℓ₁u₂/e₁⌋}` (`EFF.T1.06`); with D.20 this
gives `z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}`. -/
axiom levelOne_rho (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (u₂ : ℤ) (hu : 0 ≤ u₂) :
    (levelOneArena e₁ h he hcop η).res
        ⟨NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) u₂,
          chi_varpi_mem_ker e₁ h he hcop η u₂⟩
      = η ^ (-((iexp e₁ h 1 * u₂) / e₁))

/-- **D.22** [lemma] `(C4-origin)`: `z^{t_Def} = z^ν·ε(β)` (`EFF.T1.16`). -/
axiom c4_origin {G : Type*} [CommGroup G] (z : G) (e ℓ β : ℤ) (he : 0 < e)
    (ν : ℕ) (s_act : ℤ) (hs : s_act = (ℓ * β) % e + ν * e) :
    z ^ ((s_act - ℓ * β) / e) = z ^ (ν : ℤ) * z ^ (-((ℓ * β - (ℓ * β) % e) / e))

/-- **D.22** [lemma] The exact root-of-unity criterion: raw equality holds iff `z^ν = 1`
(`EFF.T1.16`, `EFF.T1.32`). -/
axiom c4_origin_raw_iff {G : Type*} [CommGroup G] (z : G) (e ℓ β : ℤ) (he : 0 < e)
    (ν : ℕ) (s_act : ℤ) (hs : s_act = (ℓ * β) % e + ν * e) :
    z ^ ((s_act - ℓ * β) / e) = z ^ (-((ℓ * β - (ℓ * β) % e) / e)) ↔ z ^ (ν : ℤ) = 1

/-- **D.23** [lemma] `(C4-support)`: support transport under the JA conjugation, under the
INLINE hypothesis `(H-JA-RES-CONJ)` (`hHQ`/`hPQ`) — never proved here (`EFF.T1.17`). -/
axiom c4_support {K : Type*} [Field K] {H P Q : Polynomial K} (hH : H ≠ 0) (hQ : Q ≠ 0)
    (a b : Kˣ) (ν : ℕ)
    (hHQ : H = Polynomial.X ^ ν * Q)
    (hPQ : P = Polynomial.C (a : K) * Q.comp (Polynomial.C (b : K) * Polynomial.X)) :
    H.support = P.support.map (addLeftEmbedding ν)
    ∧ H.natDegree = P.natDegree + ν

/-- **D.24** [def] `(C6-lift)`, point-free: `L_M(λ) = Σ_r λ̃_r x^{i(M)+e₁r} π^{a−rh}`
(`EFF.T1.20`). ⚠ `π` is EXPLICIT (note SD-4); `f₁` is implicit, inferred from `l`. -/
noncomputable def liftC6 {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {f₁ : ℕ} (e₁ h : ℕ) (σ : IsLocalRing.ResidueField O → O) (M : ℕ)
    (l : Fin f₁ → IsLocalRing.ResidueField O) : Polynomial O :=
  ∑ r : Fin f₁,
    Polynomial.C (σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat)
      * Polynomial.X ^ (iexp e₁ h M + e₁ * (r : ℕ))

/-- **D.25a** [lemma] `(C6-lift)` clause 1, integrality of the π-exponents on the live
domain (`EFF.T1.20`). -/
axiom liftC6_exp_nonneg {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) :
    ∀ r : Fin f₁, 0 ≤ aexp e₁ h M - (r : ℕ) * h

/-- **D.25a** [lemma] `(C6-lift)` clauses 1–2: degree and exact height on the live domain
(`EFF.T1.20`, `EFF.T1.30`). The `(u,ℓ) = (h,e₁)` cleared support value IS the corpus's
`dv₁` (chapter B's B.14 at `φ = X`). -/
axiom liftC6_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → IsLocalRing.ResidueField O) (hl : l ≠ 0) :
    (liftC6 π e₁ h σ M l).natDegree < e₁ * f₁
    ∧ Uniformity.Density.Leaf.suppVal Polynomial.X (liftC6 π e₁ h σ M l) h e₁ = (M : ℕ∞)

/-- **D.25a** [lemma] `(C6-lift)` clause 2's zero branch (`EFF.T1.20`, `EFF.T1.30`). -/
axiom liftC6_zero {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (σ : IsLocalRing.ResidueField O → O) (hσ0 : σ 0 = 0) (M : ℕ) :
    liftC6 π e₁ h σ M (0 : Fin f₁ → IsLocalRing.ResidueField O) = 0

section ClassicalSupport
open scoped Classical

/-- **D.25b** [lemma] `(C6-lift)` clause 3, the A6/GENTOW6 x-support pin (`EFF.T1.30`).
⚠ stub-side note SD-5: the `Finset.filter` needs `DecidablePred (fun r => l r ≠ 0)`, which
does NOT exist over an abstract residue field — this declaration is therefore opened under
`open scoped Classical`. The fleet's landed form must carry that, or switch to a
`∀ j, j ∈ support ↔ …` membership formulation. -/
axiom liftC6_support {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → IsLocalRing.ResidueField O) (hl : l ≠ 0) :
    (liftC6 π e₁ h σ M l).support
      = (Finset.univ.filter (fun r : Fin f₁ => l r ≠ 0)).image
          (fun r : Fin f₁ => iexp e₁ h M + e₁ * (r : ℕ))

end ClassicalSupport

/-- **D.25b** [lemma] `(C6-lift)` clause 4, the x-free criterion `(C6-x-free)`
(`EFF.T1.20`). -/
axiom liftC6_xfree {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → IsLocalRing.ResidueField O) (hl : l ≠ 0) :
    ((liftC6 π e₁ h σ M l).natDegree = 0 ∧ (liftC6 π e₁ h σ M l).support = {0})
      ↔ (iexp e₁ h M = 0 ∧ ∀ r : Fin f₁, (r : ℕ) ≠ 0 → l r = 0)

/-- **D.26** [def] `(C5-gamma)`, point-free: the normalized coordinate read
`res(a_{i+e₁t} π^{−(k−(i+e₁t)h)/e₁})`, junk `0` where the corpus's term vanishes
(`EFF.T1.18`). -/
noncomputable def gammaCoord {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (k : ℕ) (A : Polynomial O) (t : Fin f₁) :
    IsLocalRing.ResidueField O :=
  let j := iexp e₁ h k + e₁ * (t : ℕ)
  let w : ℤ := ((k : ℤ) - j * h) / e₁
  if 0 ≤ w then Uniformity.Density.Leaf.digAt π w.toNat (A.coeff j) else 0

/-- **D.26** [lemma] `(C6-residue)`, point-free: `γ ∘ L = id` on coordinates over the live
domain (`EFF.T1.18`, `EFF.T1.20`). ⚠ The `ξ`-evaluation clauses `(C5-normalizer-read)` /
`(C5-varpi-read)` stay with chapter C (`EFF.T1.18 [supplied-by: chapter C]`). -/
axiom gammaCoord_liftC6 {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hh : 0 < h)
    (hf : 0 < f₁) (hcop : Nat.Coprime h e₁) (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → IsLocalRing.ResidueField O) (t : Fin f₁) :
    gammaCoord π e₁ h f₁ M (liftC6 π e₁ h σ M l) t = l t

/-- **D.27** [lemma] The A2/HETOW binary-carry composite law (`EFF.T1.26`). The supplier
interface `(H-HETOW-LOCAL)` is `EFF.HETOW [supplied-by: chapter C]` and is NOT stated here. -/
axiom qexp_binary_carry (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    (a b u₂ : ℤ) (c₂ : ℕ) (hc : c₂ ≤ 1) :
    qexp e₁ h (a + b - c₂ * u₂)
      = qexp e₁ h a + qexp e₁ h b + wrap e₁ h a b
        - c₂ * (qexp e₁ h u₂ + wrap e₁ h (a + b - c₂ * u₂) u₂)

/-- **D.28** [lemma] `(C3-level-1-key)` clause 1 — the A3 pin: the corrected level-1
coefficient has exact height `M_t` when `c_t ≠ 0`, and is `0` on the zero branch
(`EFF.T1.13`, `EFF.T1.27`). -/
axiom levelOne_corrected_key {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (e₁ h f₁ f₂ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hh : 0 < h) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁)
    {K₁ : Type*} [Field K₁] [Algebra (IsLocalRing.ResidueField O) K₁] (η : K₁ˣ)
    (b : Module.Basis (Fin f₁) (IsLocalRing.ResidueField O) K₁) (hb : ∀ r, b r = (η : K₁) ^ (r : ℕ))
    (σ : IsLocalRing.ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (u₂ : ℕ) (t : Fin f₂) (hM : e₁ * f₁ * h < (f₂ - (t : ℕ)) * u₂)
    (c : IsLocalRing.ResidueField O) :
    (c ≠ 0 → Uniformity.Density.Leaf.suppVal Polynomial.X
        (liftC6 π e₁ h σ ((f₂ - (t : ℕ)) * u₂)
          (fun r => b.repr (algebraMap (IsLocalRing.ResidueField O) K₁ c
            * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)) r)) h e₁
        = (((f₂ - (t : ℕ)) * u₂ : ℕ) : ℕ∞))
    ∧ (c = 0 → liftC6 π e₁ h σ ((f₂ - (t : ℕ)) * u₂)
        (fun r => b.repr (algebraMap (IsLocalRing.ResidueField O) K₁ c
          * (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)) r) = 0)

/-- **D.28** [lemma] `(C3-level-1-key)` clause 2 — the multiplicative coefficient is exactly
`c_t`: `Γ_t·ϑ_{1,f₂−t}⁻¹ = c_t` (`EFF.T1.13`, `EFF.T1.27`). -/
axiom levelOne_cmult (e₁ h f₂ : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K₁ : Type*} [Field K₁] (η : K₁ˣ) (u₂ : ℕ) (t : Fin f₂) (c : K₁) :
    (c * ((η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ)))
        * (((levelOneArena e₁ h he hcop η).vartheta (u₂ : ℤ) (f₂ - (t : ℕ)) : K₁))⁻¹ = c

/-- **D.28** [lemma] `(C3-level-1-key)` clause 3 — the naive/corrected agreement criterion
`c_t(ϑ_{1,f₂−t} − 1) = 0` (`EFF.T1.13`). The naive recipe is NOT a chapter object; only the
criterion is. -/
axiom levelOne_naive_agree_iff (e₁ h f₂ : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K₁ : Type*} [Field K₁] (η : K₁ˣ) (u₂ : ℕ) (t : Fin f₂) (c : K₁) :
    c * (((levelOneArena e₁ h he hcop η).vartheta (u₂ : ℤ) (f₂ - (t : ℕ)) : K₁) - 1) = 0
      ↔ c = 0 ∨ (η : K₁) ^ Wfloor e₁ h (u₂ : ℤ) f₂ (t : ℕ) = 1

/-! ## §5 — THE READ BUNDLE AND THE B-LAW (D.29–D.36) -/

/-- **D.29** [def] The sitewise C3 read bundle (`EFF.T1.03`): exactly the clauses the B-law
consumes, as fields. Instantiation = the external supplier's theorem (never proved in
chapter D): `i = 2` — GENTOW2-B′/B″ [supplied-by: chapter C]; `i ≥ 3` — `[GENTOW5-W(i)]`
behind `𝒲_{≤i}` plus `(H-VARTHETA-RES)_i`. The `w : Kˣ` typing carries BOTH
`(C3-read-codomain)` and `(C3-ladder-nonvanishing)` (D-H6). -/
structure ReadBundle {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) where
  R : G → K
  w : Kˣ
  read_n : R (N.n q) = w
  ladder_mult : ∀ s : ℕ, R ((N.n q) ^ s) = (w : K) ^ s
  scalar_cov : ∀ (X : G) (g : MonoidHom.ker A.v), R (X * (g : G)) = R X * (A.res g : K)

/-- **D.30** [def] The corrected key `Φ^{ef} − Σ_t k̂_t Φ^{et}` (`EFF.T1.12` `(C3-key)`). -/
noncomputable def correctedKey {S : Type*} [CommRing S] (Φ : Polynomial S) (e f : ℕ)
    (khat : Fin f → Polynomial S) : Polynomial S :=
  Φ ^ (e * f) - ∑ t : Fin f, khat t * Φ ^ (e * (t : ℕ))

/-- **D.30** [lemma] The corrected key is monic of degree `e·f·d`, including the boundary
case `e = 1, t = f−1` (`EFF.T1.12`). -/
axiom correctedKey_monic {S : Type*} [CommRing S] [Nontrivial S] {Φ : Polynomial S}
    (hΦ : Φ.Monic) (hd : 0 < Φ.natDegree) {e f : ℕ} (he : 0 < e) (hf : 0 < f)
    {khat : Fin f → Polynomial S} (hdeg : ∀ t, (khat t).natDegree < Φ.natDegree) :
    (correctedKey Φ e f khat).Monic
    ∧ (correctedKey Φ e f khat).natDegree = e * f * Φ.natDegree

/-- **D.31** [lemma] `(C3-dictionary)`: the coherent/multiplicative digit dictionary, as an
iff so neither orientation can be consumed without the other (`EFF.T1.11`, `EFF.T3.05`).
The `ϑ : Kˣ` argument IS `EFF.T1.09`'s unit condition; at `i ≥ 3` supplying it is
`(H-VARTHETA-RES)_i`. -/
axiom dict_iff {K : Type*} [Field K] (Γ c : K) (ϑ : Kˣ) :
    Γ = c * ϑ ↔ c = Γ * (ϑ⁻¹ : Kˣ)

/-- **D.32** [theorem] `(C3-Theta)`/`(C3-B-law)`: the B-law from the bundle,
`u(β_s) = Θ(s)·w^s` (`EFF.T1.14`). ORIENTATION: the B-law direction of D.06
(`FGMN = u · repo`), never the inverse. -/
axiom ReadBundle.blaw {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} (B : ReadBundle A q) (s : ℕ) :
    B.R (N.n (s * q)) = (A.theta q s : K) * (B.w : K) ^ s

/-- **D.33** [theorem] `(C3-canonical-read)`: the telescopes cancel slotwise,
`u(β_{f−t})·Γ_t = c_t·w^{f−t}` (`EFF.T1.15`, `EFF.T5.18`). The ONE place both orientations
meet — through D.10's involution. -/
axiom ReadBundle.canonical_coeff {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} (B : ReadBundle A q) (f t : ℕ) (ht : t < f) (c : K) :
    B.R (N.n ((f - t : ℕ) * q)) * (c * (A.vartheta q (f - t) : K))
      = c * (B.w : K) ^ (f - t)

/-- **D.34** [def] The w-twist `(WF-twist)`: `P(y) ↦ w^{deg P}·P(y/w)` (`EFF.T1.15`,
`EFF.T3.18`, `EFF.T5.05`). -/
noncomputable def wtwist {K : Type*} [Field K] (w : Kˣ) (P : Polynomial K) : Polynomial K :=
  (w : K) ^ P.natDegree • P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)

/-- **D.34a** [lemma] The twist is monic of the same degree. -/
axiom wtwist_monic {K : Type*} [Field K] (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    (wtwist w P).Monic ∧ (wtwist w P).natDegree = P.natDegree

/-- **D.34a** [lemma] The nonzero-constant-term clause. -/
axiom wtwist_coeff_zero {K : Type*} [Field K] (w : Kˣ) (P : Polynomial K) :
    (wtwist w P).coeff 0 = (w : K) ^ P.natDegree * P.coeff 0

/-- **D.34b** [lemma] Irreducibility transport. -/
axiom wtwist_irreducible {K : Type*} [Field K] (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    Irreducible (wtwist w P) ↔ Irreducible P

/-- **D.34b** [lemma] Separability transport. -/
axiom wtwist_separable {K : Type*} [Field K] (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    (wtwist w P).Separable ↔ P.Separable

/-- **D.34b** [lemma] The root map is `s ↦ w·s`. -/
axiom wtwist_eval {K : Type*} [Field K] (w : Kˣ) (P : Polynomial K) (s : K) :
    (wtwist w P).eval ((w : K) * s) = (w : K) ^ P.natDegree * P.eval s

/-- **D.34c** [lemma] The factor-multiset correspondence: multiplicativity on monics. -/
axiom wtwist_mul {K : Type*} [Field K] (w : Kˣ) {P Q : Polynomial K}
    (hP : P.Monic) (hQ : Q.Monic) :
    wtwist w (P * Q) = wtwist w P * wtwist w Q

/-- **D.35** [lemma] `(WF-psi)`: the twist coefficients
`w^f ψ(y/w) = y^f − Σ c_t w^{f−t} y^t` (`EFF.T5.06`). -/
axiom wtwist_psi {K : Type*} [Field K] (w : Kˣ) (f : ℕ) (c : Fin f → K) :
    wtwist w (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ))
      = Polynomial.X ^ f
        - ∑ t : Fin f, Polynomial.C (c t * (w : K) ^ (f - (t : ℕ)))
            * Polynomial.X ^ (t : ℕ)

/-! **D.36** [table] the C7 package interface and scope fence (anchor `D-C7-TABLE`) —
NO Lean declaration; the blueprint table is the artifact. `(C7-scope)`: T1 proves no
cross-face coherence theorem, no gauge uniqueness, no torsor classification. A node asking
chapter D for a cross-face compatibility square is a blueprint defect. -/
-- (no declaration)

/-! ## §6 — THE TELESCOPE PORT (T3) (D.37–D.44) -/

/-- **D.37** [def] The boundary-read port `(BR1)–(BR5)` (`EFF.T3.06`–`.11`). FENCE, as a
NON-field: "Neither the B-law nor a one-`w_i` power law is included among them" — the
structure has NO B-law field, and adding one is the §8.4(3) mutant. -/
structure BoundaryReadPort {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) where
  w : Kˣ
  ctR : K
  ctRQ : ℕ → K
  expSupport : Finset ℕ
  br1 : ctR = (w : K) ^ s
  br2 : ctR = ∑ j ∈ expSupport, ctRQ j
  br3 : ∀ j ≠ 0, ctRQ j = 0
  U : K
  digit : K
  br4 : ctRQ 0 = U * digit
  br5 : digit = (A.vartheta q s : K)

/-- **D.38** [theorem] `(T3-BR)`: the boundary-read telescope `U_i(β_s) = Θ_N(s;q)·w_i^s`
(`EFF.T3.14`). The endpoint equation is DERIVED, never supplied. -/
axiom BoundaryReadPort.t3_br {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {s : ℕ} (P : BoundaryReadPort A q s) :
    P.U = (A.theta q s : K) * (P.w : K) ^ s

/-- **D.39** [def, stub-side name] The `K`-valued section ratio `χ`, needed by D.39/D.40
(the blueprint's `chiK`, whose spelling §12 rule 5 fixes at stub time). -/
noncomputable def GaugeArena.chiK {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k) (k : ℤ) : Kˣ :=
  A.res ⟨NormSection.chi Nhat N k, A.mem_ker_div ((hNhat k).trans (A.exact_height k).symm)⟩

/-- **D.39** [lemma, stub-side helper] The assembled residual quotients have height zero
(`EFF.T3.13`) — PROVED because D.39's `def` body needs it. -/
theorem GaugeArena.rho_mem_ker {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (M : NormSection G)
    (hM : ∀ k : ℤ, A.v (M.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (t : ℕ) {x : G} (hx : A.v x = Multiplicative.ofAdd (H₀ - t * q)) :
    x * (M.n q) ^ t * (M.n H₀)⁻¹ ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_pow, hx, hM, hM, ← ofAdd_nsmul]
  simp

/-- **D.39** [def] The two-section comparison data `(ρ, ρ̂, δ)` (`EFF.T3.12`, `EFF.T3.13`). -/
noncomputable def compData {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t : Fin (D + 1), A.v (Acoef t) = Multiplicative.ofAdd (H₀ - (t : ℕ) * q)) :
    (Fin (D + 1) → Kˣ) × (Fin (D + 1) → Kˣ) × Kˣ :=
  (fun t => A.res ⟨Acoef t * (N.n q) ^ (t : ℕ) * (N.n H₀)⁻¹,
      A.rho_mem_ker N A.exact_height H₀ q (t : ℕ) (hA t)⟩,
   fun t => A.res ⟨Acoef t * (Nhat.n q) ^ (t : ℕ) * (Nhat.n H₀)⁻¹,
      A.rho_mem_ker Nhat hNhat H₀ q (t : ℕ) (hA t)⟩,
   A.chiK Nhat hNhat q)

/-- **D.40** [theorem] `(T3-CMP)` coefficient leg: `ρ_t = ρ̂_t·χ(H₀)·δ^{−t}`
(`EFF.T3.17`). -/
axiom compData_cmp {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t : Fin (D + 1), A.v (Acoef t) = Multiplicative.ofAdd (H₀ - (t : ℕ) * q))
    (t : Fin (D + 1)) :
    (((compData A Nhat hNhat H₀ q D Acoef hA).1 t : Kˣ) : K)
      = (((compData A Nhat hNhat H₀ q D Acoef hA).2.1 t : Kˣ) : K)
        * ((A.chiK Nhat hNhat H₀ : Kˣ) : K)
        * ((((compData A Nhat hNhat H₀ q D Acoef hA).2.2 : Kˣ) : K))⁻¹ ^ (t : ℕ)

/-- **D.40** [theorem] `(T3-CMP)` polynomial leg: `R(Z) = χ(H₀)·R̂(Z/δ)` (`EFF.T3.17`). -/
axiom compData_cmp_poly {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t : Fin (D + 1), A.v (Acoef t) = Multiplicative.ofAdd (H₀ - (t : ℕ) * q)) :
    (∑ t : Fin (D + 1),
        Polynomial.C ((((compData A Nhat hNhat H₀ q D Acoef hA).1 t : Kˣ) : K))
          * Polynomial.X ^ (t : ℕ))
      = Polynomial.C ((A.chiK Nhat hNhat H₀ : Kˣ) : K)
        * (∑ t : Fin (D + 1),
              Polynomial.C ((((compData A Nhat hNhat H₀ q D Acoef hA).2.1 t : Kˣ) : K))
                * Polynomial.X ^ (t : ℕ)).comp
            (Polynomial.C
                ((((compData A Nhat hNhat H₀ q D Acoef hA).2.2⁻¹ : Kˣ) : K))
              * Polynomial.X)

/-- **D.41** [lemma] `(T3-ROUTE)`: polynomial routing along the comparison — D.34's package
instantiated at `w := δ` and re-exported under T3's name (`EFF.T3.18`). -/
axiom t3_route {K : Type*} [Field K] (δ : Kˣ) {rhat : Polynomial K} (h : rhat.Monic) :
    wtwist δ rhat
      = (δ : K) ^ rhat.natDegree • rhat.comp (Polynomial.C ((δ⁻¹ : Kˣ) : K) * Polynomial.X)
    ∧ ((wtwist δ rhat).Separable ↔ rhat.Separable)

/-- **D.41** [lemma] `(T3-ROUTE)` root correspondence `ŝ ↦ δŝ` (`EFF.T3.18`). -/
axiom t3_route_roots {K : Type*} [Field K] (δ : Kˣ) {rhat : Polynomial K} (h : rhat.Monic)
    (s : K) :
    (wtwist δ rhat).eval ((δ : K) * s) = (δ : K) ^ rhat.natDegree * rhat.eval s

/-- **D.41** [lemma] `(T3-ROUTE)` rationality: the correspondence commutes with
`Polynomial.map (algebraMap K L)` for any field extension `L/K` (`EFF.T3.18`). -/
axiom t3_route_map {K L : Type*} [Field K] [Field L] [Algebra K L] (δ : Kˣ)
    {rhat : Polynomial K} (h : rhat.Monic) :
    (wtwist δ rhat).map (algebraMap K L)
      = wtwist (Units.map (algebraMap K L : K →+* L).toMonoidHom δ)
          (rhat.map (algebraMap K L))

/-! **D.42** [interface] `(ABS-G2)`: the `i = 2` discharge — chapter C's port construction
(`EFF.T3.19`; `EFF.GENTOW2.43/.34/.42 [supplied-by: chapter C]`). NO Lean declaration in
chapter D; per §12 rule 4 nothing is axiomatized here (axiomatizing a supplier's theorem
would fake the discharge). -/
-- (no declaration)

/-! **D.43** [interface] `(ABS-HE4)`: the HETOW comparison discharge (`EFF.T3.20`;
`EFF.HETOW [supplied-by: chapter C]`). NO Lean declaration. -/
-- (no declaration)

/-- **D.44** [def] The sitewise B-law predicate whose level-`i` tower instance is
`[GENTOW5-W(i)]` (`EFF.T3.21`). SUPPLY STATUS transcribed: "SUPPLIED by T3-A0 and §7;
consumption check + dated append outstanding." -/
def GentowW {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (R : G → K) (w : Kˣ) : Prop :=
  ∀ s : ℕ, R (N.n (s * q)) = (A.theta q s : K) * (w : K) ^ s

/-- **D.44** [theorem] `(ABS-G5W)`: a family of ports at every `s` yields the predicate
(`EFF.T3.21`). Nothing here discharges any instance. -/
axiom gentowW_of_ports {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {R : G → K} {w : Kˣ}
    (h : ∀ s : ℕ, ∃ P : BoundaryReadPort A q s, P.U = R (N.n (s * q)) ∧ P.w = w) :
    GentowW A q R w

/-! ## §7 — THE CERTIFICATE WITNESS (T4) (D.45–D.54) -/

/-- **D.45** [def] The composed threshold `Θ_j = (μ₂−j)E₂ + δ` (`EFF.T4.01`). -/
def thresholdTheta (μ₂ E₂ δ j : ℕ) : ℕ := (μ₂ - j) * E₂ + δ

/-- **D.45** [lemma] Strict antitony on the coordinate range (`EFF.T4.01`). -/
axiom thresholdTheta_anti (μ₂ E₂ δ : ℕ) (hE : 0 < E₂) {j j' : ℕ}
    (h : j < j') (h' : j' < μ₂) :
    thresholdTheta μ₂ E₂ δ j' < thresholdTheta μ₂ E₂ δ j

/-- **D.46** [def] T4's certificate frame (`EFF.T4.01`–`.13`, composite-read packaging per
the §7 design note). `M` carries NO discriminant hypothesis and no decidedness hypothesis
(`EFF.T4.05`). Instantiating `grΔ` = supplying COMPLETE assembly (every branch, carry,
recarry — `EFF.T4.07/.08`); instantiating `floor` = GENTOW-3(i) at 𝔐
[supplied-by: chapter C]. -/
structure CertFrame (Dv : Type*) [AddCommGroup Dv] (Slot : Type*)
    (K : Type*) [Field K] where
  μ₂ : ℕ
  Θ : ℕ → ℕ
  M : Set Dv
  fkey : Dv
  fkey_mem : fkey ∈ M
  grΔ : ℕ → ℕ → Dv →+ (Slot →₀ K)
  floor : ∀ f ∈ M, ∀ j < μ₂, ∀ m < Θ j, grΔ m j f = 0

/-- **D.47** [def] The first-discrepancy height, totalized: `ν_j(q)` with `min ∅ := +∞`
(`EFF.T4.12`). -/
noncomputable def CertFrame.nuIdx {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) (q : Dv) : ℕ∞ :=
  sInf {m : ℕ∞ | ∃ m' : ℕ, m = (m' : ℕ∞) ∧ F.grΔ m' j q ≠ 0}

/-- **D.48** [def] The certificate witness `ω_j` — the fully assembled height-`Θ_j` digit of
the key power (`EFF.T4.10`, r3 text). -/
noncomputable def CertFrame.omega {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : Slot →₀ K :=
  F.grΔ (F.Θ j) j F.fkey

/-- **D.48** [def] Touched: `ω_j ≠ 0` (`EFF.T4.10`). ⚠ Deliberately stronger than
"`ShC_j(Φ₂^{μ₂}) ≠ 0`": FR-M3 at `j = 0` is the committed separator (self-shadow pin `12`,
`Θ₀ = 10`, `ω₀ = 0`) — executed at the D.66 gate. -/
def CertFrame.Touched {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : Prop := F.omega j ≠ 0

/-- **D.49** [theorem] LEMMA T4.2(a): exact attainment for the key power (`EFF.T4.14`).
The statement is about `fkey` ALONE — no member-general converse is inferred. -/
axiom CertFrame.touched_iff_nu_eq {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) :
    F.Touched j ↔ F.nuIdx j F.fkey = (F.Θ j : ℕ∞)

/-- **D.49** [lemma] The untouched corollary, including the identically-zero case through
`ν_j(f_key) = +∞` (`EFF.T4.14`). -/
axiom CertFrame.nu_gt_of_untouched {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) (hu : ¬ F.Touched j) :
    (F.Θ j : ℕ∞) < F.nuIdx j F.fkey

/-- **D.50** [theorem] LEMMA T4.2(b): perturbation stability (`EFF.T4.15`). The withdrawn
"same shift" inference is NOT used. -/
axiom CertFrame.perturb_stable {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {g : Dv} (hf : F.fkey + g ∈ F.M)
    (hg : F.grΔ (F.Θ j) j g = 0) :
    F.grΔ (F.Θ j) j (F.fkey + g) = F.omega j

/-- **D.50** [lemma] The in-budget SPECIALIZATION: the margin enters ONLY as the displayed
hypothesis `hg`, whose discharge is the supplier's S8.1 box [supplied-by: chapter C]
(`EFF.T4.15`). -/
axiom CertFrame.perturb_nu_eq {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {g : Dv} (hj : j < F.μ₂) (hf : F.fkey + g ∈ F.M)
    (hg : ∀ m, m ≤ F.Θ j → F.grΔ m j g = 0) (ht : F.Touched j) :
    F.nuIdx j (F.fkey + g) = (F.Θ j : ℕ∞)

/-- **D.51** [lemma] LEMMA T4.2(c): the fully-exposed assembled-slot criterion
(`EFF.T4.16`). ⚠ The premise is ALL-PROVENANCE (`HYP.113`): uniqueness only among
single-extraction contributions does NOT discharge it — the burden sits in proving the
instance equation `(omega j) σ = ξ` against the complete `grΔ`. -/
axiom CertFrame.touched_of_exposed {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {σ : Slot} {ξ : K}
    (hexp : (F.omega j) σ = ξ) (hne : ξ ≠ 0) : F.Touched j

/-- **D.52** [lemma] LEMMA T4.2(d): the no-contribution criterion (`EFF.T4.17`).
⚠ (i) absence of single-extraction sources alone does NOT discharge the premise;
(ii) NO attainment statement for another member follows — entry-driven content may still
attain `Θ_j` (FR-M3's `W` member attains `Θ₀ = 10` while `ω₀ = 0`). `HYP.114`. -/
axiom CertFrame.omega_zero_iff_untouched {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : F.omega j = 0 ↔ ¬ F.Touched j

/-! **D.53** [interface] Instance `GT3-THRESHOLD` (`EFF.T4.18`–`.21`) —
`EFF.GENTOW3 [supplied-by: chapter C]`. NO Lean declaration. -/
-- (no declaration)

/-! **D.54** [interface] Instance `GT6-CERT-TOP` (`EFF.T4.22/.23/.41`), R5-63A discharged
"YES at the sealed scope — `f₁ = 1`, `μ₂ = 2`, `2i_{t*} ≥ D′` — and NO elsewhere";
`EFF.GENTOW6 [supplied-by: chapter C]`. NO Lean declaration. A fleet agent instantiating
CERT-TOP outside that scope must return BLOCKED. -/
-- (no declaration)

/-! ## §8 — THE W-FRAME (T5) (D.55–D.61) -/

/-- **D.55** [def] `𝒲_{≤i} = ⋀_{3≤q≤i}[GENTOW5-W(q)]` (`EFF.T3.22`, `EFF.T5.13/.29`).
CARRY (`HYP.63`); NEVER discharged — "Certification of the WI companion does not discharge
these conjuncts from the frozen GENTOW5 statements" (the r1 form; the stale opposite at
source L299 / `HYP.100` is NOT transcribed). -/
def Wle (W : ℕ → Prop) (i : ℕ) : Prop := ∀ q, 3 ≤ q → q ≤ i → W q

/-- **D.55** [lemma] `𝒲_{≤2}` is the EMPTY conjunction (`EFF.T5.13`, r4-G1 base repair). -/
axiom Wle_two (W : ℕ → Prop) : Wle W 2

/-! **D.56** [interface] `(WF-law₂)`: the unconditional base rung, supplied by LEMMA
GENTOW2-B″ (`EFF.GENTOW2.43 [supplied-by: chapter C]`; `EFF.T5.12`, `EFF.T5.15`).
NO Lean declaration in chapter D — D.44 named the predicate precisely so this row is a
C-side term, not a D-side axiom. -/
-- (no declaration)

/-- **D.57** [theorem] `(WF-lawᵢ)`: the rung-`i` law is the LAST CONJUNCT of the cumulative
hypothesis (`EFF.T5.14`, `EFF.T5.15`). The triviality is the POINT: hypothesis-retention in
Lean is conjunct extraction; anything more would be the r4-G1-refuted "induction from empty
base". -/
axiom wf_law_i (W : ℕ → Prop) (i : ℕ) (hi : 3 ≤ i) (h : Wle W i) : W i

/-- **D.58** [theorem] `(WF-realized)`: the realized-residual cancellation
`R_ν(Φ_{i+1}) = ψ_{i+1}^{(w_i)}` at the coefficient level (`EFF.T5.18`–`.20`). At `i = 2`
unconditional via D.56's instance; at `i ≥ 3` inside `Wle W i` (D.57, then this node). -/
axiom gentowW_realized {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {R : G → K} {w : Kˣ}
    (hW : GentowW A q R w) (f : ℕ) (c : Fin f → K) :
    (Polynomial.X ^ f
      - ∑ t : Fin f, Polynomial.C
          (R (N.n ((f - (t : ℕ) : ℕ) * q)) * (c t * (A.vartheta q (f - (t : ℕ)) : K)))
          * Polynomial.X ^ (t : ℕ))
    = wtwist w (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ))

/-- **D.59** [def] The clause-(b) corrected-index display (`EFF.T5.32` `(WF-index)`,
`EFF.T3.24` `(G5-TWIST)`). A CARRIER: instances are chapter C's; consumed under `Wle` per
D.60's chain. The corrected index is `ω_{j−1}`: the first-written `w_{n+1}` at the top term
EXCEEDED the assumed `𝒲_{≤n}`. No display uses the superseded `ψ_j^{(ω_j)}`. -/
def WfIndex {K : Type*} [Field K] (Rlev : ℕ → Polynomial K) (ψ : ℕ → Polynomial K)
    (ω : ℕ → Kˣ) (l : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j ≤ n + 1 →
    Rlev (j - 1) = (wtwist (ω (j - 1)) (ψ j)) ^ (∏ k ∈ Finset.Icc (j + 1) (n + 1), l k)

/-- **D.60** [def] The `(G5-COND)`/`(WF-chain)` implication chain (`EFF.T3.23`,
`EFF.T5.30/.31`). Stations supplied by chapter C; chapter I consumes the assembled
conditional. NO chapter-D node discharges a station. -/
def WfChain (P : Fin 8 → Prop) : Prop := ∀ k : Fin 7, P k.castSucc → P k.succ

/-! **D.61** [record] the per-level nonvanishing suppliers, the two-clause gate, and the
avatar fences (`EFF.T5.07/.09/.10/.16/.28`; `HYP.63/.66/.99/.100`) — NO Lean declaration.
`i = 2`: GENTOW2-B′(3)/B″. `i ≥ 3`: GENTOW5 S11.2's PROVED fixed-unit list, routed AROUND
`𝒲_{≤i}` — and per-grade fixedness alone does NOT prove (WF-law). `i = 1`: NONE.
The avatar fence: `w_i` is NOT a normalized uniformizer avatar (LW3: `w_av = 2 ≠ w₃ = 1`). -/
-- (no declaration)

/-! ## §9 — THE `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` CARRIERS (D.62–D.64)

**RE-SIGN LOG (A-D.2, 2026-08-16 — the Display-A carrier adjudication unit; executes
D-D12's owed re-sign per blueprint DECISION D-2).** D-D12 (header) machine-refuted the
committed D.62 (`∃ A : GaugeArena G K N, A.v = v`) as VACUOUS: the trivial hom
`1 : ker v →* Kˣ` inhabits it, making it equivalent to the exact-height fact.  D-D12's
repair fork was: (α) an ambient residue datum on the arena, or (β) the sitewise ϑ-clause
directly.  **DECISION D-2 picks (β), the sitewise form against a GIVEN ambient residue
datum** — it is the source display verbatim (`EFF.T1.09`:
"`(H-VARTHETA-RES)_i : res(n̂_i(u_{i+1})^s / n̂_i(su_{i+1})) ∈ K_i (s ≥ 0)`", with
`K_iˣ`-membership the supplier-dependent content per its CONDITIONALITY line and
`EFF.T5.10`), it leaves D.07 untouched (per A-D.1's D-D12 note: "This structure itself is
unaffected"), and D-H3's "formally stronger" claim is restored as the PROVED theorem
`hvarthetaRes_of_arena_agree` below (an ambient-agreeing arena discharges the sitewise
clause).  The voided existential form is KEPT under the name `HVarthetaResVoided` with its
two D-D12 witnesses, so the refutation record stays machine-checked.  Non-triviality
countermodel for the re-signed form: `verification/om4_resign_nontriviality.lean` (an
exact-height instance with an ambient datum whose ϑ-residue is NOT in the level field —
the old `⟨v, hv, 1⟩` recipe is not replayable).  Blueprint authority: CHAP-D DECISION D-2 +
amendment A-D.2 (§9 dated append). -/

/-- **D.62-VOID** [def, NAMED-AND-VOIDED at A-D.2] The committed D.62 carrier, byte-identical
under the voided name: REFUTED as a carrier (D-D12) — `hvarthetaResVoided_iff` below proves
it equivalent to the exact-height fact, so it tracks no `(H-VARTHETA-RES)_i` conditionality.
NEVER to be consumed by chapters E/I; kept solely as the machine-checked refutation record. -/
def HVarthetaResVoided (G : Type*) [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) (v : G →* Multiplicative ℤ) : Prop :=
  ∃ A : GaugeArena G K N, A.v = v

/-- **D.62** [def, RE-SIGNED at A-D.2 / DECISION D-2] The Lean carrier of
`(H-VARTHETA-RES)_i` (`EFF.T1.09` R9-2 fence), SITEWISE against a GIVEN ambient residue
datum: over the level's height data `(N, v)` and an ambient residue homomorphism
`ρ : ker v →* Lˣ` (`L` the ambient residue field, `K = K_i` the level field embedded in it),
every ϑ-quotient `n̂(q)^s/n̂(sq)` has value zero AND its ambient residue lands in `K_iˣ`
(as a unit: the witness `u : Kˣ`).  `q` is the level's fixed use-height `u_{i+1}` — a
parameter, exactly source scope.  The membership conjunct is exact-height arithmetic
(unconditional at any arena instance, D.08's `varthetaEl_mem_ker`); the supplier-dependent
content is the `K`-membership clause, exactly `EFF.T1.09`'s display.  Consumed by E (ladder
displays at `i ≥ 3`) and I (Display A's `∀ i ≥ 3` conjunct, via D.63) — at THIS form only;
the pre-A-D.2 existential form is `HVarthetaResVoided` and is VOID. -/
def HVarthetaRes (G : Type*) [CommGroup G] (K : Type*) [Field K] (L : Type*) [Field L]
    [Algebra K L] (N : NormSection G) (v : G →* Multiplicative ℤ)
    (ρ : MonoidHom.ker v →* Lˣ) (q : ℤ) : Prop :=
  ∀ s : ℕ, ∃ (h : N.varthetaEl q s ∈ MonoidHom.ker v) (u : Kˣ),
    ((ρ ⟨N.varthetaEl q s, h⟩ : Lˣ) : L) = algebraMap K L (u : K)

/-- **D.62** [lemma, PROVED at A-D.2] The D-H3 direction, restored honestly: a gauge arena
whose `res` AGREES with the ambient residue datum (through the level-field embedding)
discharges the sitewise carrier.  This is the exact sense in which D.07-as-theorem-hypothesis
is "formally stronger than the sitewise clauses" — the agreement leg is what the voided
existential form lacked. -/
theorem hvarthetaRes_of_arena_agree {G : Type*} [CommGroup G] {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] {N : NormSection G} (A : GaugeArena G K N)
    (ρ : MonoidHom.ker A.v →* Lˣ)
    (hagree : ∀ x : MonoidHom.ker A.v, ((ρ x : Lˣ) : L) = algebraMap K L ((A.res x : Kˣ) : K))
    (q : ℤ) : HVarthetaRes G K L N A.v ρ q :=
  fun s => ⟨A.varthetaEl_mem_ker q s, A.res ⟨N.varthetaEl q s, A.varthetaEl_mem_ker q s⟩,
    hagree _⟩

/-- **D.63** [def, consumption re-signed at A-D.2 — signature byte-unchanged] Display A's
`∀ i ≥ 3` conjunct, assembled (`EFF.T1.09` + `EFF.T3.22` + `EFF.T5.10/.13`). Per the Part V
owner ruling its terminal disposition in chapter I is DISCHARGE NODE or LITERATURE CITE;
this chapter only supplies the carrier.  CONSUMPTION FENCE (A-D.2): `HVR` must be
instantiated at the RE-SIGNED sitewise `HVarthetaRes` over the level-`i` ambient residue
datum (instantiations chapter C's); the pre-A-D.2 instantiation through the voided
existential form degenerates to `Wle` plus an exact-height fact (D-D12) and is VOID. -/
def VarthetaWConjunct (HVR W : ℕ → Prop) (i : ℕ) : Prop := HVR i ∧ Wle W i

/-! ### DEFECT WITNESS D-D12 — the VOIDED D.62 carrier is VACUOUS (machine-checked below)

`HVarthetaResVoided` (the committed D.62, named-and-voided at A-D.2) renders
`(H-VARTHETA-RES)_i` — a Display-A `∀ i ≥ 3` conjunct — as "an arena over the level's
height data EXISTS". But `GaugeArena` has NO field tying its `res` to any ambient residue
map, so the **trivial** homomorphism `1 : ker v →* Kˣ` already inhabits it. The two
theorems below are PROVED (not stubs): the voided carrier is EQUIVALENT to the
height-homomorphism being exact on `N`, and says nothing whatever about `ϑ_{i,s}` landing
in `K_iˣ`.

Consequence: as committed, chapter I would have carried a Display-A conjunct discharged by
`⟨v, hv, 1⟩`, and D.63's `VarthetaWConjunct` would have degenerated to `Wle` plus an
exact-height fact. D-H3's claim that the packaging is "formally STRONGER than the sitewise
clauses" holds for D.07 used as a THEOREM HYPOTHESIS (the §3/§5/§6 theorems are true for
any `res`), but is FALSE in the existential direction the committed D.62 used. §14 item
2(iii) asked exactly this question; this is the answer.  THE REPAIR IS EXECUTED at the
re-signed D.62 above (DECISION D-2 / amendment A-D.2). -/

theorem hvarthetaResVoided_of_exact_height {G : Type*} [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) (v : G →* Multiplicative ℤ)
    (hv : ∀ k : ℤ, v (N.n k) = Multiplicative.ofAdd k) :
    HVarthetaResVoided G K N v :=
  ⟨{ v := v, exact_height := hv, res := 1 }, rfl⟩

theorem hvarthetaResVoided_iff {G : Type*} [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) (v : G →* Multiplicative ℤ) :
    HVarthetaResVoided G K N v ↔ ∀ k : ℤ, v (N.n k) = Multiplicative.ofAdd k := by
  refine ⟨fun ⟨A, hA⟩ k => ?_, hvarthetaResVoided_of_exact_height K N v⟩
  rw [← hA]; exact A.exact_height k

/-! **D.64** [record] OPEN-CALL and orphan routing — the chapter's residual-obligation
table. NO Lean declaration. `JD0-BOX-2` → chapter I (zero T-unit cites); `HYP.01`/`HYP.12`
→ chapter I core-set (`HYP.98`); T1 OPEN-CALL 4 = T3 OPEN-CALL 1 (the surrounding tower
correctness theorem) → chapter I / the 0d trust boundary. -/
-- (no declaration)

/-! ## §10 — GATES (D.65–D.68), EXECUTED

Per GC-11: `q = 2` AND `q = 3`, plus the FRAME-C `p = 5` regression. Every check below is
`decide`, never `native_decide`.

⚠ **DEFECT D-D1, and its stub-side repair.** The blueprint's gate lines are written
`… := by decide` directly on `iexp`. That does not work: `iexp` is defined through
`(h : ZMod e₁)⁻¹`, `ZMod.inv` routes through `Nat.gcdA`/`Nat.xgcd`, and those do not
kernel-reduce, so `decide` gets stuck (`((1 : ℕ) : ZMod 2)⁻¹ = 1` is itself not `decide`-able
at the pin). Every gate line below therefore runs `simp only [<local defs>, iexp_one]` first —
`iexp_one` being the PROVED reduction at `h = 1`, which is the value of `h` at all three of
this chapter's gate frames — and then `decide`. No expected value is changed.

⚠ **𝔽₄ carrier (the §10 ⚠, decided here — stub-side decision SD-6).** `GaloisField 2 2` and
`AdjoinRoot (X^2+X+1 : (ZMod 2)[X])` are quotient constructions with no computable
`DecidableEq` at the pin, so no `decide` can run in them. The F4-JOINT legs therefore run in
the **discrete-log model**: `ω` has order 3 and every quantity in D.65's legs 2–4 is a power
of `ω`, so the multiplicative group `⟨ω⟩ ≅ (ZMod 3, +)` carries them faithfully — products
become sums and every committed expected value is an exponent. -/

/-! ### D.65 — the `q = 2` gate: the F4-JOINT frame (`e₁ = 2, f₁ = 2, h = 1, u₂ = 3`;
`K₁ = 𝔽₄`, `η = ω` of order 3) — `EFF.T1.33/.34`. -/

/-- leg 1: the `iexp` table at `e₁ = 2, h = 1` is `k % 2` — including negative heights
(§14 item 5's question, answered: `ZMod.val` is always the nonnegative representative). -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5] : List ℤ).map (fun k => iexp 2 1 k)
    = [1, 0, 1, 0, 1, 0, 1, 0, 1] := by simp only [iexp_one]; decide

/-- leg 1: the live wrap — `wrap 2 1 a b = 1` exactly on odd/odd. -/
example : ∀ a ∈ ([0, 1, 2, 3] : List ℤ), ∀ b ∈ ([0, 1, 2, 3] : List ℤ),
    (wrap 2 1 a b = 1 ↔ (iexp 2 1 a = 1 ∧ iexp 2 1 b = 1)) := by
  simp only [wrap, iexp_one]; decide

/-- leg 1: the telescope exponent table `⌊s·i(3)/2⌋ = (0,0,1,1)` for `s = 0…3`. -/
example : (List.range 4).map (fun s => s * iexp 2 1 3 / 2) = [0, 0, 1, 1] := by
  simp only [iexp_one]; decide

/-- leg 1: the same table through `Wfloor` at `f₂ = 3` (slot indexing `s = f₂ − t`). -/
example : (List.range 3).map (fun t => Wfloor 2 1 3 3 t) = [1, 1, 0] := by
  simp only [Wfloor, iexp_one]; decide

/-- gate-local data (D.65): the F4-JOINT discrete-log model, `ω^k ↦ k : ZMod 3`. -/
def gate65varthetaExp (s : ℕ) : ZMod 3 := ((s * iexp 2 1 3 / 2 : ℕ) : ZMod 3)

/-- gate-local data (D.65): the B-law-orientation exponent `Θ_s = ϑ_s⁻¹`. -/
def gate65thetaExp (s : ℕ) : ZMod 3 := -gate65varthetaExp s

/-- gate-local data (D.65): `w = ω`, so `w^s ↦ s`. -/
def gate65wExp (s : ℕ) : ZMod 3 := (s : ZMod 3)

/-- leg 2: the telescope vector `(ϑ_{1,0},…,ϑ_{1,3}) = (1, 1, ω, ω)` — `EFF.T1.34`'s
`μ = 3` leg, as exponents `(0,0,1,1)`. -/
example : (List.range 4).map (fun s => gate65varthetaExp s) = [0, 0, 1, 1] := by
  simp only [gate65varthetaExp, iexp_one]; decide

/-- leg 3: the `μ = 3` canonical vector, ALL THREE entries scored (`EFF.T1.39` check 5).
The three vectors are listed in ASCENDING `s` (= DESCENDING slot `t`) — the blueprint's own
order, which it never states; see defect D-D9. `Γ = (1, ω, ω)`. -/
example : ([1, 2, 3] : List ℕ).map (fun s => gate65varthetaExp s) = [0, 1, 1] := by
  simp only [gate65varthetaExp, iexp_one]; decide

/-- leg 3: `u(β) = (ω, ω, ω²)` — D.32's B-law `Θ_s·w^s` at the instance. -/
example : ([1, 2, 3] : List ℕ).map (fun s => gate65thetaExp s + gate65wExp s)
    = [1, 1, 2] := by
  simp only [gate65thetaExp, gate65varthetaExp, gate65wExp, iexp_one]; decide

/-- leg 3: the full canonical coefficient vector `(ω, ω², 1)`. -/
example : ([1, 2, 3] : List ℕ).map
    (fun s => gate65varthetaExp s + (gate65thetaExp s + gate65wExp s))
    = [1, 2, 0] := by
  simp only [gate65thetaExp, gate65varthetaExp, gate65wExp, iexp_one]; decide

/-- leg 3, the cancellation itself: `Γ_t·u(β_t) = c_t·w^s` for unit digits — D.33's
coefficient identity, exponentwise. -/
example : ∀ s ∈ ([1, 2, 3] : List ℕ),
    gate65varthetaExp s + (gate65thetaExp s + gate65wExp s) = gate65wExp s := by
  simp only [gate65thetaExp, gate65varthetaExp, gate65wExp, iexp_one]; decide

/-- leg 4: the corrected/naive separation — `ϑ₂ = ω ≠ 1`, so D.28 clause 3's criterion fires
and `R_naive ≠ R_corr` (the gauge-naive mutant's kill site). -/
example : gate65varthetaExp 2 ≠ 0 := by
  simp only [gate65varthetaExp, iexp_one]; decide

/-- leg 4: `ψ^{(w)} = y² + ωy + 1` from `(WF-psi)`'s coefficient law `c_t·w^{f−t}` at
`f = 2`, `w = ω`, `(c₁, c₀) = (1, ω)` — exponents `(0, 1) ↦ (1, 0)`. -/
example : ([(1, (0 : ZMod 3)), (0, (1 : ZMod 3))] : List (ℕ × ZMod 3)).map
    (fun p => p.2 + gate65wExp (2 - p.1)) = [1, 0] := by
  simp only [gate65wExp]; decide

/-! ### D.66 — the `q = 3` gate: the X frame (`p = 3`, `e₁ = 2, f₁ = 1, h = 1, η = 2 ∈ 𝔽₃,
u₂ = 3`) plus the T4 threshold table — `EFF.T1.33`, `EFF.T4.20`. -/

/-- leg 1: the `iexp` table on `k = −2 … 6`. -/
example : ([-2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => iexp 2 1 k)
    = [0, 1, 0, 1, 0, 1, 0, 1, 0] := by simp only [iexp_one]; decide

/-- leg 1: the `aexp` table on `k = −2 … 6` (Lean's `Int./` is `ediv` at the pin). -/
example : ([-2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => aexp 2 1 k)
    = [-1, -1, 0, 0, 1, 1, 2, 2, 3] := by simp only [aexp, iexp_one]; decide

/-- leg 1: the `qexp` table on `k = −2 … 6`. FINDING D-F1: at this frame (`h = 1`, so
`i₀ = 1`) `qexp = aexp` identically — the X frame does NOT separate D.13's `aexp` from
D.15's `qexp`, so it cannot on its own catch a `qexp`/`aexp` confusion. -/
example : ([-2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => qexp 2 1 k)
    = [-1, -1, 0, 0, 1, 1, 2, 2, 3] := by simp only [qexp, iexp_one]; decide

/-- leg 1: `(C5-carry)` EXECUTED on a grid (D.15), including negative heights. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    qexp 2 1 (a + b) = qexp 2 1 a + qexp 2 1 b + wrap 2 1 a b := by
  simp only [qexp, wrap, iexp_one]; decide

/-- leg 1: `(C2-wrap)` EXECUTED on the same grid (D.14). -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    iexp 2 1 a + iexp 2 1 b = iexp 2 1 (a + b) + 2 * wrap 2 1 a b
      ∧ wrap 2 1 a b ≤ 1 := by
  simp only [wrap, iexp_one]; decide

/-- leg 1: D.27's binary-carry composite law EXECUTED at `c₂ ∈ {0,1}`. -/
example : ∀ a ∈ ([-1, 0, 1, 2] : List ℤ), ∀ b ∈ ([-1, 0, 1, 2] : List ℤ),
    ∀ u ∈ ([1, 2, 3] : List ℤ), ∀ c ∈ ([0, 1] : List ℕ),
      qexp 2 1 (a + b - c * u)
        = qexp 2 1 a + qexp 2 1 b + wrap 2 1 a b
          - c * (qexp 2 1 u + wrap 2 1 (a + b - c * u) u) := by
  simp only [qexp, wrap, iexp_one]; decide

/-- gate-local data (D.66): the X-frame telescope in `𝔽₃ = ZMod 3` (`η = 2`). -/
def gate66vartheta (s : ℕ) : ZMod 3 := (2 : ZMod 3) ^ (s * iexp 2 1 3 / 2)

/-- leg 2: `(ϑ_{1,0},…,ϑ_{1,4}) = (1, 1, 2, 2, 1)`. -/
example : (List.range 5).map (fun s => gate66vartheta s) = [1, 1, 2, 2, 1] := by
  simp only [gate66vartheta, iexp_one]; decide

/-- gate-local data (D.66): the X-frame `Θ` table as LITERAL DATA. ⚠ `ZMod.inv` does not
kernel-reduce (defect D-D1), so `Θ` is NOT spelled `(ϑ s)⁻¹` here; it is committed as data and
the involution below is the check that it IS the inverse. `2⁻¹ = 2` in `𝔽₃`. -/
def gate66theta : List (ZMod 3) := [1, 1, 2, 2, 1]

/-- leg 2: the involution table `Θ_s·ϑ_s = 1` with `Θ = (1, 1, 2, 2, 1)` — D.10 EXECUTED. -/
example : ∀ s ∈ List.range 5, gate66theta.getD s 0 * gate66vartheta s = 1 := by
  simp only [gate66vartheta, gate66theta, iexp_one]; decide

/-- leg 3: the corrected/naive split — `ϑ₂ = 2 ≠ 1`, so D.28 clause 3's criterion fires. -/
example : gate66vartheta 2 ≠ 1 ∧ gate66vartheta 3 ≠ 1 := by
  simp only [gate66vartheta, iexp_one]; decide

example : ∀ c ∈ ([1, 2] : List (ZMod 3)), c * (gate66vartheta 2 - 1) ≠ 0 := by
  simp only [gate66vartheta, iexp_one]; decide

/-- leg 4: the T4 threshold table — **FR-M3's committed thresholds `[10,7,4]`**
(`EFF.T4.20`). -/
example : (List.range 3).map (fun j => thresholdTheta 3 3 1 j) = [10, 7, 4] := by decide

/-- leg 4: the separator arithmetic. FR-M3's self-shadow pins are `[12,7,4]`: at `j = 0`
`ν₀ = 12 > 10 = Θ₀` (untouched WITH SLACK, `ω₀ = 0` — D.48's fence), while `j = 1, 2`
attain. `EFF.T4.11`, `EFF.T4.20`. -/
example : thresholdTheta 3 3 1 0 < 12
    ∧ thresholdTheta 3 3 1 1 = 7
    ∧ thresholdTheta 3 3 1 2 = 4 := by decide

/-- leg 4: the same three facts in `ℕ∞`, the codomain of D.47's `nuIdx`. -/
example : ((thresholdTheta 3 3 1 0 : ℕ) : ℕ∞) < (12 : ℕ∞)
    ∧ ((thresholdTheta 3 3 1 1 : ℕ) : ℕ∞) = (7 : ℕ∞)
    ∧ ((thresholdTheta 3 3 1 2 : ℕ) : ℕ∞) = (4 : ℕ∞) := by decide

/-- leg 4: D.45's antitony EXECUTED at the FR-M3 frame. -/
example : thresholdTheta 3 3 1 2 < thresholdTheta 3 3 1 1
    ∧ thresholdTheta 3 3 1 1 < thresholdTheta 3 3 1 0 := by decide

/-! ### D.67 — the FRAME-C regression (`p = 5`): T3's declared battery frame, executed
(`EFF.T3.29`). Level-1 arena `e₁ = 2, h = 1, η = 2`; `w = 3`; `q_BR = 1`. -/

/-- gate-local data (D.67): FRAME-C's `ϑ`, ASSEMBLED from D.18's exponent formula at
`q_BR = 1` — never from the endpoint formula (`EFF.T3.29`'s own instruction). -/
def gate67vartheta (s : ℕ) : ZMod 5 := (2 : ZMod 5) ^ (s * iexp 2 1 1 / 2)

/-- gate-local data (D.67): the B-law-orientation telescope `Θ_s = ϑ_s⁻¹` (D.06 rows 2–3),
as LITERAL DATA (defect D-D1: `ZMod.inv` does not kernel-reduce, so the inverse cannot be
spelled; it is committed and then CHECKED against `ϑ` by the involution below). -/
def gate67thetaL : List (ZMod 5) := [1, 1, 3, 3, 4, 4]

def gate67theta (s : ℕ) : ZMod 5 := gate67thetaL.getD s 0

/-- gate-local data (D.67): FRAME-C's committed `U` table, as LITERAL DATA — so the two
identities below are genuine checks, not unfoldings (the §8.4(3) endpoint-as-input mutant's
kill). -/
def gate67U : List (ZMod 5) := [1, 3, 2, 1, 4]

/-- leg 1: `ϑ = (1, 1, 2, 2, 4)` on `s = 0…4` — `EFF.T3.29`'s committed table. -/
example : (List.range 5).map (fun s => gate67vartheta s) = [1, 1, 2, 2, 4] := by
  simp only [gate67vartheta, iexp_one]; decide

/-- leg 1, extension: FINDING D-F2 — the D.06 table's `ϑ_{G2}(t) = Θ(f₃−t)` at the BOTTOM
slot `t = 0` reads the telescope at `s = f₃ = 5`, one step BEYOND FRAME-C's committed
`s = 0…4` range, so the committed battery does not cover the bottom slot. The assembled
formula extends it: `ϑ_5 = 2^{⌊5/2⌋} = 4`, `Θ_5 = 4`. -/
example : gate67vartheta 5 = 4 := by simp only [gate67vartheta, iexp_one]; decide

/-- leg 1: the runner obligation `w^s = U(s)·ϑ_s`, all five `s`. -/
example : ∀ s ∈ List.range 5,
    (3 : ZMod 5) ^ s = gate67U.getD s 0 * gate67vartheta s := by
  simp only [gate67vartheta, gate67U, iexp_one]; decide

/-- leg 1: the runner obligation `U(s) = Θ_s·w^s`, all five `s` — the B-law orientation. -/
example : ∀ s ∈ List.range 5,
    gate67U.getD s 0 = gate67theta s * (3 : ZMod 5) ^ s := by
  simp only [gate67theta, gate67thetaL, gate67U]; decide

/-- leg 1: **the orientation tooth, EXECUTED.** Writing the B-law in the WRONG orientation
(`ϑ` where `Θ` belongs) fails at `s = 2` — the sign error `EFF.T1.45`/append #54 says no
battery catches now HAS a battery. -/
example : gate67U.getD 2 0 ≠ gate67vartheta 2 * (3 : ZMod 5) ^ 2 := by
  simp only [gate67vartheta, gate67U, iexp_one]; decide

/-- gate-local data (D.67): FRAME-C's `χ(k) = 2^{⌊k/2⌋}` (D.12's `chi` at the two
exponent-pair sections, residue via D.17). -/
def gate67chi (k : ℕ) : ZMod 5 := (2 : ZMod 5) ^ (k / 2)

/-- leg 2: **the non-character check** `χ(1)·χ(1) = 1 ≠ 2 = χ(2)` — D.12's "no character law
for χ is assumed" fence, EXECUTED. The character mutant dies here. -/
example : gate67chi 1 * gate67chi 1 ≠ gate67chi 2 := by decide

/-- leg 2: `δ = χ(2) = 2` and `χ(6) = 2³ = 3`. -/
example : gate67chi 2 = 2 ∧ gate67chi 6 = 3 := by decide

/-- gate-local data (D.67): the CMP leg's explicit `ρ̂` coefficients (`H₀ = 6`, `D = 3`). -/
def gate67rhoHat : List (ZMod 5) := [1, 2, 3, 4]

/-- gate-local data (D.67): `ρ_t = χ(H₀)·ρ̂_t·δ^{−t} = 3·ρ̂_t·2^{−t}` (D.40's coefficient
leg). -/
def gate67rho (t : ℕ) : ZMod 5 :=
  gate67chi 6 * gate67rhoHat.getD t 0 * (3 : ZMod 5) ^ t

/-- leg 2: the comparison `ρ_t = 3·ρ̂_t·2^{−t}` evaluated — the coefficient form of
`R(Z) = 3·R̂(Z/2)` in `𝔽₅[Z]` (D.40). -/
example : (List.range 4).map (fun t => gate67rho t) = [3, 3, 1, 4] := by decide

/-- leg 2: `δ⁻¹ = 3` in `𝔽₅`, the substitution scalar of `R̂(Z/δ)` — stated
multiplicatively (defect D-D1: `ZMod.inv` does not kernel-reduce). -/
example : (2 : ZMod 5) * 3 = 1 := by decide

/-! ### D.06 — THE ϑ FOUR-WAY ORIENTATION TABLE, EXECUTED at FRAME-C (`f₃ = 5`)

The table's four rows as arithmetic, at the one frame where every quantity is a concrete
`𝔽₅`-unit. Append #54's trap ("a sign error no battery catches") gets its battery here:
rows 1/2/3 are ONE object, row 4 is its RECIPROCAL at the reflected index, and the two are
numerically DISTINCT — so a silent swap is a failing `decide`. -/

/-- row 1 (GENTOW2 `ϑ(t)`) = rows 2/3 (`Θ(f−t)`), the reference. -/
def gate06varthetaG2 (f t : ℕ) : ZMod 5 := gate67theta (f - t)

/-- row 4 (GENTOW5-A1 `theta_t`) = T1's `ϑ_{i,t}` at argument `t`, NOT `f−t`. -/
def gate06A1theta (t : ℕ) : ZMod 5 := gate67vartheta t

/-- rows 2–3, as the involution `Θ_s·ϑ_s = 1` (D.06 / D.10) — this is what certifies that
`gate67thetaL` really is the inverse-orientation telescope. -/
example : ∀ s ∈ List.range 6, gate67theta s * gate67vartheta s = 1 := by
  simp only [gate67theta, gate67thetaL, gate67vartheta, iexp_one]; decide

/-- **the top-slot normalization anchor** `ϑ(f₃−1) = 1` (`EFF.GENTOW2.41`; both orientations
agree at `s ∈ {0,1}`). -/
example : gate06varthetaG2 5 4 = 1 ∧ gate67vartheta 1 = 1 ∧ gate67theta 1 = 1 := by
  simp only [gate06varthetaG2, gate67theta, gate67thetaL, gate67vartheta, iexp_one]; decide

/-- **row 4's RECIPROCAL relation** `ϑ(t) = vartheta_{f₃−t}⁻¹` at `λ = u₃`
(`EFF-GENTOW2.md:1072`) — the exact pair append #54 names, stated multiplicatively. -/
example : ∀ t ∈ List.range 5,
    gate06varthetaG2 5 t * gate06A1theta (5 - t) = 1 := by
  simp only [gate06varthetaG2, gate06A1theta, gate67theta, gate67thetaL, gate67vartheta,
    iexp_one]
  decide

/-- **the orientations are numerically DISTINCT** — a silent swap of row 1 for row 4 is
caught (`t = 2`: row 1 gives `3`, row 4 gives `2`). -/
example : gate06varthetaG2 5 2 ≠ gate06A1theta 2 := by
  simp only [gate06varthetaG2, gate06A1theta, gate67theta, gate67thetaL, gate67vartheta,
    iexp_one]
  decide

/-- and the reflection `t ↦ f₃−t` is not the identity either: `ϑ_{G2}(t) ≠ Θ(t)`.
⚠ FINDING D-F3: this must be scored at `t = 1` or `t = 4`, NOT at `t = 2`/`t = 3` — FRAME-C
has `ϑ₂ = ϑ₃ = 2` (both floors `⌊s/2⌋` equal 1), so an index-shift mutant SURVIVES at the
middle slots. A fleet agent scoring only the middle of the table would miss it. -/
example : gate06varthetaG2 5 1 ≠ gate67theta 1 ∧ gate06varthetaG2 5 4 ≠ gate67theta 4 := by
  simp only [gate06varthetaG2, gate67theta, gate67thetaL]; decide

example : gate67theta 2 = gate67theta 3 := by
  simp only [gate67theta, gate67thetaL]; decide

/-! ### NON-VACUITY WITNESSES (stub-side, not blueprint declarations)

The GC-11 gates score arithmetic; they cannot score whether a SCHEMA is inhabited. Two of
this chapter's three hypothesis-carrying structures are the ones whose emptiness would make
their theorems vacuous, so both are inhabited here — with the discriminating field TRUE. -/

/-- `BoundaryReadPort` is INHABITED for every arena, ladder step, exponent and unit, so
D.37/D.38 are not vacuous. Note the witness's `U` is forced to `w^s·ϑ⁻¹ = Θ·w^s` — D.38's
conclusion, arrived at from the port axioms alone. -/
noncomputable def portWitness {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) (w : Kˣ) : BoundaryReadPort A q s where
  w := w
  ctR := (w : K) ^ s
  ctRQ := fun j => if j = 0 then (w : K) ^ s else 0
  expSupport := {0}
  br1 := rfl
  br2 := by simp
  br3 := by intro j hj; simp [hj]
  U := (w : K) ^ s * ((A.vartheta q s)⁻¹ : Kˣ)
  digit := (A.vartheta q s : K)
  br4 := by
    simp only [if_pos]
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  br5 := rfl

/-- gate-local data: an additive `grΔ` layer over `ℤ` with a single canonical slot. -/
noncomputable def gradWitness (m : ℕ) : ℤ →+ (Unit →₀ ℚ) :=
  if m = 0 then AddMonoidHom.mk' (fun n => Finsupp.single () (n : ℚ))
    (by intro a b; simp [Finsupp.single_add]) else 0

/-- `CertFrame` is INHABITED, with (FLOOR) satisfied, so D.46–D.52 are not vacuous. -/
noncomputable def certWitness : CertFrame ℤ Unit ℚ where
  μ₂ := 1
  Θ := fun _ => 0
  M := Set.univ
  fkey := 1
  fkey_mem := Set.mem_univ 1
  grΔ := fun m _ => gradWitness m
  floor := by intro f _ j _ m hm; exact absurd hm (Nat.not_lt_zero m)

/-- …and its coordinate `j = 0` is TOUCHED, so D.48's `Touched` and D.49's equivalence are
both non-trivially satisfiable. -/
theorem certWitness_touched : certWitness.Touched 0 := by
  simp only [CertFrame.Touched, CertFrame.omega, certWitness, gradWitness]
  intro h
  have := congrArg (fun f => f ()) h
  simp at this

/-! ### D.68 — the chapter-D census gate (stub-stage form)

At stub stage every theorem-shaped node is an `axiom`, so `#print axioms` on a theorem is
uninformative by construction. What IS informative, and is the census's stub-stage content:
the **`def`/`structure` layer must be axiom-clean apart from the one definitional dependency
the blueprint itself creates** — `levelOneArena` consumes D.13's `iexp_aexp_spec` for its
`exact_height` field (finding D-D2). Every line below is a census assertion, not a proof.
`native_decide` appears nowhere in this file. -/

section Census

#print axioms LeanspecD.NormSection.tau
#print axioms LeanspecD.NormSection.varthetaEl
#print axioms LeanspecD.NormSection.thetaEl
#print axioms LeanspecD.NormSection.chi
#print axioms LeanspecD.GaugeArena.vartheta
#print axioms LeanspecD.GaugeArena.theta
#print axioms LeanspecD.GaugeArena.varthetaG2
#print axioms LeanspecD.iexp
#print axioms LeanspecD.aexp
#print axioms LeanspecD.iexp_one
#print axioms LeanspecD.wrap
#print axioms LeanspecD.qexp
#print axioms LeanspecD.Wfloor
#print axioms LeanspecD.levelOneSection
#print axioms LeanspecD.levelOneHeight
#print axioms LeanspecD.levelOneHeight_ker_dvd
#print axioms LeanspecD.levelOneArena
#print axioms LeanspecD.varpiSection
#print axioms LeanspecD.chi_varpi_mem_ker
#print axioms LeanspecD.liftC6
#print axioms LeanspecD.gammaCoord
#print axioms LeanspecD.correctedKey
#print axioms LeanspecD.wtwist
#print axioms LeanspecD.GaugeArena.chiK
#print axioms LeanspecD.GaugeArena.rho_mem_ker
#print axioms LeanspecD.compData
#print axioms LeanspecD.GentowW
#print axioms LeanspecD.thresholdTheta
#print axioms LeanspecD.CertFrame.nuIdx
#print axioms LeanspecD.CertFrame.omega
#print axioms LeanspecD.CertFrame.Touched
#print axioms LeanspecD.Wle
#print axioms LeanspecD.WfIndex
#print axioms LeanspecD.WfChain
#print axioms LeanspecD.HVarthetaRes
#print axioms LeanspecD.HVarthetaResVoided        -- A-D.2: the named-and-voided shadow
#print axioms LeanspecD.hvarthetaRes_of_arena_agree
#print axioms LeanspecD.VarthetaWConjunct

-- (iii) non-vacuity: the six carriers Display A / chapters E and I consume BY NAME,
-- `#check`ed at their stated types.
#check @GentowW
#check @Wle
#check @WfIndex
#check @WfChain
#check @HVarthetaRes
#check @VarthetaWConjunct

end Census

end LeanspecD
