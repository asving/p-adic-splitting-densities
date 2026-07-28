# MOVESV BLUEPRINT REV 1 — FRESH-INSTANCE AUDIT (Fable), 2026-07-28

**ARTIFACT.** `lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` (rev 1, 1594 lines, read in full).
**GROUND TRUTH.** §V-TABLES rev 7 (`lean/notes/MOVES_2026-07-24.md` 7829–9054, read in full);
consumed signatures spot-verified in source: `MovesSp/Defs.lean` (Species, InCatalogue/SnRaw,
StageLaws/SuccStep, Verdict z/ep/ns, Out = inl''Succ ∪ inr''univ, EntranceShape, SP2_finThm,
SP6_card53), `MovesD/Defs.lean` + `D10_sumLaw.lean`/`D11a_multSum.lean`/`D4R4all_wrapper.lean`
(ShapeRead retains `h : ℕ`, `ustar : ℚ`; ShapePrefix.W/A/A'; Shape n; PrefIdx; Presented/fiber/
mult; `D4R1_SUM`: Σᶠ card(fiber)·p^{A'} = card(PrefIdx)·p^{nN} at stabilized levels — the
blueprint's V3-6 tie is exactly its `key`), `MovesS/Defs.lean` + `MovesS/Interfaces.lean`
(TableShape/DegCons/MeasuredSide/LedgerIV/OKat/evalAt/PolyGeom/RatBurdens/EscapeE0/PoolHyp/
AVAgree/DetHyp/MuHat/Kmat/KmatHyp/RegP; RS1Meas/RS1Bundle/RS4Chain/ReadOffBundle), and the
MovesS blueprint's §W4-SYNC (XRBPackage/Wsh17Package/S-2/S-8/S-9/W-6/W-11).

**VERDICT: REJECT — 2 critical / 5 gaps.** The V-TABLES fidelity core is strong (XHD packages,
(U-A), the h_ent pin, the gate layer's numbers, the 70-unit census, the conditionality banner
all check out — see §B); the two criticals are Lean-side wiring/typing defects the E-phase
would hit as hard blockers, both in the entrance/step machinery.

---

## A. FINDINGS (quote → classify; nothing fixed here)

### A-1 CRITICAL — the entrance-side carrier granularity is broken across 2.F / V3-8 / V3-9c / V7-4 / V7-5(b) / V7-6

Quotes:
- §2.F: `ιval : EntShapeV n → S.Cell → ℚ → ℝ` (per CONCRETE ε; no aggregate carrier and no
  `ιsh` field is declared in 2.F).
- V3-8: "the ℝ-valued `ιval e β₀ = Σ_{ε̊} Σ_{h ∈ H(ε̊)} ιsh (ε̊[h]) β₀`" — `ιval` applied at
  a BLOCK index (e, β₀) and an undeclared `ιsh`: neither typechecks against 2.F. V3-9c's
  conclusion `… = V.ιval e τ q₀` has the same clash.
- V7-4: "EntShape := the (template-bounded) EntShapeV subtype with hent/Went/ιsh/ιval/
  entCount/entLvl/entInst from 2.E".

Why critical, verified against the Lean source:
1. `MovesS.MeasuredSide.finE : ∀ e τ, Fintype (EntShape e τ)` and
   `LedgerIV.init_agg : ιval e τ q₀ = ∑ ε : M.EntShape e τ, ιsh e τ ε q₀` (a FINITE sum).
   A concrete-ε carrier is infinite per template — the blueprint's OWN V3-5 exhibits the
   bijection H(ε̊) ≃ {concrete ε with template ε̊}, and H(ε̊) is an infinite semilinear set
   in general. So V7-4's wiring line cannot inhabit `MeasuredSide` as specced. The correct
   granularity is the TEMPLATE family ε̊ (finite by V3-4) with `ιDom ε̊ := H(ε̊)`,
   `ιshH ε̊ h := ι_{e,ε̊[h],β₀}` — which is what V7-6's own wiring already presumes
   ("comp_once ← V5-4 at length-0 continuation (the ι height sum)": `comp_once` is
   `HasSum (fun h : ιDom ε => ιshH …) (ιsh …)`, a template-level height sum). The blueprint
   contradicts itself between V7-4 and V7-6.
2. `MeasuredSide.hent : EntShape e τ → ℕ` (source-verified) vs `EntShapeV.hent :
   List (ℕ × ℚ)` — the transport "hent … from 2.E" is a type error; an encoding (or the
   template-level reading, where per-template `hent : ℕ` needs its own definition, and
   A(ε) — affine in h across instantiations, M4a — has NO per-template value) is nowhere
   adjudicated.
3. `MovesS.RatBurdens.ι_interp/ι_count/ι_countS_one/ι_degT/ι_degS` are PER-SHAPE fields
   (`… = M.ιsh e τ ε q₀`, `countT.eval q₀ = entCount e τ ε q₀` — source-verified), but V7-5
   leg (b) supplies "ιP from V3-9c (INIT-RAT)", whose stated conclusion is the AGGREGATE
   ι_{e,τ} ∈ ℚ(q). The per-shape PolyGeom (INIT-RAT's inner display: I^ent_c(q) × the XHD-s
   geometric per component, per template) is constructed inside V3-9c's sketch but not
   exposed by its statement — the seam row is unbuildable from the unit as stated.
4. `LedgerIV.init_count` (the counting-native fixed-height tie ιshH·|Box| = |entEvtH|,
   source-verified) is attributed by V7-6 to "V3-9a" — but V3-9a is the ENT-COUNT
   polynomial-burden def; the box tie's supplier is the V3-6/V7-4 counting semantics.
   Mis-keyed wiring.

Consequence: units V3-8/V3-9c need restatement (declare the aggregate carrier; expose the
per-template PolyGeom), and V7-4(b)/V7-5(b)/V7-6's entrance rows need the template-keyed
redesign. Downstream statements are salvageable — the note's content is not in question,
only the blueprint's carrier assignment.

### A-2 CRITICAL — the chain/history apparatus of `StepSys` cannot express the pinned chain recursion (V2-5, V5-2, XHDd.chain)

Quotes:
- §2.G `XHDd.chain : ∀ {α} (γ : Template n S α), S.Hist α → Hpt γ.D → ℕ` with "its tie to
  per-step cntraw is VAL(b)'s (XHD-u)-conditional content (unit V2-5), NEVER assumed here".
- V2-5: "the chain recursion is the `chain`-vs-`cntraw` tie FIELD the E-designer adds to
  XHDd (chain (cons m γ) = Σ over step-1 assignments of chain γ — recorded DESIGN FREEDOM;
  the note's chain count is defined by exactly that recursion)".
- V5-2 sketch: "per mark, induct along γ: each step contributes cnt·g by (U-A) at the fixed
  history + (u-R) across the histories reaching βᵢ".

Adjudication of design-freedom slot (2) (the charge's item 5): the note PINS the content —
V.0: "T_γ(x, h) := #{fresh-assignment chains from x realizing (γ, h)}" is a DEFINITION, so
the only freedom is Lean encoding. But the promised tie field is NOT STATEABLE against the
§2 `StepSys` as displayed: "Σ over step-1 assignments of chain γ" requires, per assignment
`a : Assign m x h₁`, a history of the TARGET cell (`chain γ (x·a) h₂`) — and `StepSys` has
NO history-extension operation `Hist α → Assign m x h → Hist β` (source of §2.B checked:
Cell/Move/MoveT/dim/Pools/Hist/zc/Assign/massOf/cntraw/inv — no extension). Without it the
base tie `chain (.last m) = cntraw m` PLUS the cons law cannot be written, V2-5's induction
and V5-2's per-mark induction have no carrier, and XHDd's exactness clauses (no_orphan/
no_stray) quantify over a `chain` that is otherwise FREE DATA — exactly the degenerate-
instance failure the wave-2 doctrine forbids ("a faithful interface must be FALSE for
instances the note would reject"). Resolution requires amending the NORMATIVE Defs (§2.B:
add `ext : ∀ {α β} (m) (x) (h), Assign m x h → Hist β`, or make Hist an inductive path
type) — not a leaf-level E-phase choice. Since §2's declaration order is declared normative
and two units (one HARD core, V5-2) are blocked, this is critical, not a recordable gap.

### A-3 GAP — V3-4's `WordBounded` under-pins the finiteness statement

Quote: "`Set.Finite {ε̊ : EntTemplate n | WordBounded n ε̊}` — words in the catalogue …,
selections in L5's finite menus (bounded lists over finite data)"; sketch: "finite words of
bounded length over a finite alphabet".
`EntTemplate` carries `gsel musel : ℕ` and `selRec : List ℕ` unbounded; a predicate named
and sketched as a WORD bound leaves the statement FALSE (infinitely many templates per
word). The note's finiteness cites "[2a]/M1 for the P̂-templates; L5's finite eligible-
continuation menus for the σ_sel's" — so `WordBounded` must also bound (gsel, musel) and
selRec (length AND values) by the L5 menus. The predicate's obligations are not displayed;
neither is any tie of `EntTemplate` to the consumed `MovesSp.EntranceShape` (listed in §1's
consumption map as consumed by "the (iii) template layer V3-3/V3-4" but used nowhere —
EntTemplate lacks hMem/hChain analogues).

### A-4 GAP — V6-1c's sketch predicate is char-dependent and fails at p = 2, the falsifier's own census point

Quote: "sketch: decide over Fin p³ with multiplicity predicates f(x) = 0 ∧ f′(x) = 0 (∧ f″
for triple)". Over ZMod 2, f″ = 6x + 2a ≡ 0 identically, so the "∧ f″ for triple" test
classifies every double root as triple: at q = 2 it would report m_3 = 4, m_2+1 = 0 against
the sealed 2 and 2. (Checked: f = z³ + z² = z²(z+1) has f(0) = f′(0) = f″(0) = 0 over
ZMod 2 yet is m_2+1.) The note's root block is deliberately char-free ("no discriminant
formula is used"). The STATEMENT (five class counts = closed-form values, decide per p) is
fine and decidable by factorization enumeration; only the sketch is wrong — but it is wrong
exactly at the m_H3 = 0 falsifier's point, so it must not survive into E-phase.

### A-5 GAP — the §5 design-freedom inventory is incomplete (2 declared, ≥ 4 flagged inline)

Quote (§5): "The two DESIGN-FREEDOM slots (StepSys.inv → C15Pack's carrier; XHDd.chain's
recursion tie in V2-5) are flagged inline for the audit round". Also flagged inline as
design freedom but MISSING from the inventory: §2.F's `moveOf` embedding + the fixed-h form
of `tbl_count` ("[DESIGN FREEDOM, audit round: `moveOf` is the CtsFamily→StepSys move
embedding …]"), V4-1's `lands_in` field ("recorded DESIGN FREEDOM"), V3-9c's PolyGeom-
closure vs OKat-landing route ("DESIGN FREEDOM recorded"). Per campaign §3(ii) each must be
resolved WITH the auditor; an under-counted inventory is how one slips through unadjudicated.

Adjudication of slot (1) (charge item 5), for the record: `StepSys.inv : ∀ {α β}, Move α β
→ Hpt 0 ⊕ Unit → Unit` is content-free as typed AND redundant — `C15Pack` already carries
the pinned carrier (`Inv`, `invOf`, `F`, `mass_factors`), which expresses exactly the note's
C.1(ii) role ("BOTH factors are functions of the read's NOMINAL DIGIT INVENTORY … NEVER of
which values the cell pins"). The freedom is real but should resolve to DELETING the stub;
nothing in the note demands an inventory slot on `StepSys` itself.

### A-6 GAP — §0's proved-outright banner overstates the V6 layer by one unit

Quote (§0): "the entire V.6 gate layer (V6-*: closed forms, PART-1 count faces, DEG-CONS
rosters, domain normal form, the gate-B dyadic arithmetic and two-history discipline) —
decide/ring/norm_num-native" under "WHAT IS PROVED OUTRIGHT HERE (no hypothesis fields)".
V6-4c (threshold N = 3) carries the typed premise `hensel : CoprimeLiftPack` (and the
declared published-axiom fallback). The parenthetical enumeration correctly omits the
threshold, but "the entire V.6 gate layer" sweeps it in; the corpus record's wording must
scope V6-4c out (as §5's WATCH list already does). Same banner, minor: V6-1c is decide-
native at the six PRIME census points only — correctly recorded at the unit, so no defect
there, but the banner sentence should carry the same scope note it gives nowhere.

### A-7 GAP — dangling-reference / display-hygiene cluster (one finding, several instances)

- §2.B comment "stated domain-conditionally at the XHD bundle (see `XHD.u_T_dom`)" —
  `u_T_dom` is defined nowhere (content derivable from raw u_T + XHDd.no_stray, but the
  named object must exist or the pointer go).
- §2.G `def HMCAug … : Prop := …` — body elided; the "∃-refinement" content of the ledgered
  hypothesis V.5(2) is not pinned by any display, though V4-11 requires instances of it.
- V1-7's display `∃ S P, (C15Pack n S) ∧ ¬ (…)` — `C15Pack n S` is a Type, not a Prop
  conjunct (E-phase shape: Σ/Nonempty).
- V0-1's display binds no `h` (`Function.update h i t` with h free).
- §2.C `IsPP` (prime-power predicate) used in `size_count`, never defined.
- `EntShapeV`'s (gsel, musel) carry no eligibility tie to P̂'s entry read (the note's b is
  "a designated CONTINUING branch" of P̂); only realizability-via-XHD-d (V3-5) constrains it.
- §4.2 row for `RS1Bundle.xrb` and V7-4's "from 2.E" section pointers are loose (ιval/
  entCount live in 2.F; hent/Went in 2.D).

None of these alone blocks a build; together they are exactly the class of blueprint noise
the E-designer mis-resolves silently — hence one recorded gap.

---

## B. VERIFIED CLEAN (the charge's items, with the checks performed)

1. **SEAM-SUPPLY field-by-field (§4).** Every MovesS field named in §4.1/§4.2 exists with
   the claimed shape in `MovesS/Defs.lean`/`Interfaces.lean` (TableShape 15 fields; DegCons;
   KmatHyp "kcol members size e" verbatim; MeasuredSide's full field list; RatBurdens'
   tgP/jP/ιP legs + cellP family + act_iff; LedgerIV's 13 fields all covered by V7-6's map;
   RS1Meas/RS1Bundle/RS4Chain/ReadOffBundle rows incl. shDom…wshval_card and the [3t]/[3]/
   [5] owner tags). The §4.3 re-keying list matches the MovesS blueprint's §W4-SYNC S-2/S-8/
   S-9/W-6/W-11 verbatim (XRBPackage's xhd_* are the four re-key targets; jc_inv/sib/tb_cap/
   vp/rel2_* stay [2b]/[3t]/[2r]; Wsh17Package.cts_counts ↦ ValA ∧ EntCount; c15_volumes
   stays §C/HC-2, sib_count [3t]). `VLabel n` = MovesS's vEquiv codomain LITERALLY (R20 pin,
   Equiv.refl-keyable). The μ̂ fence: `MovesS.MuHat` is the bare one-field wrapper claimed.
   EXCEPTIONS: the entrance-side rows — A-1.
2. **XHD packages as typed-field structures (§2.B/2.G) vs the V.0 displays.** XHDw: E/ET
   affine-positive DATA (weights ≥ 1 typed — degenerate weight-0 unsatisfiable), w_eq at ANY
   history/ANY assignment/at pools, source-AND-target indexing by `Move α β`'s type,
   terminal ET per the rev-4 extension — faithful. XHDu: u-R covers mass and count; the
   step-level typing (vs the note's template-level γ) is a displayed WEAKENING with the
   template level recovered at V2-5 — honest direction, and legitimate once A-2 is repaired.
   XHDd: listed pairwise-disjoint partition BY TYPE (`SemilinPart.disj`), two-sided
   exactness verbatim (orphan: some-representative; stray: EVERY representative). XHDs: per
   LISTED component, denom ∣ X^b·∏(1 − X^a) (= the note's (1 − q^{−a}) class cleared, the
   MovesS §2.C.1 diagnosis, sign-immaterial), HasSum at every pool. HMC: the membership
   factorization over cons/append with terminal-final templates BY CONSTRUCTOR — the
   probe-step-2 signature is a type instance as claimed. Non-degeneracy anchors present per
   package (V0-4 witness checked: Σ over L((4,1);{(3,1),(2,0)}) of q^{−E}, E = 6t+3u+1 in
   chart coords (base value 7 ✓), = q²/((q⁶−1)(q³−1)) — GA2's cleared form ✓ PolyGeom class).
3. **(U-A) as a PROVED unit (V1-6) + the fence (V1-7).** V1-6 is EXACTLY the note's (U-A):
   one fixed (ZC)-prefix (`hzc : S.zc x` matching C15Pack.mass_factors' guard), one (m, h),
   two assignments, common mass; proof = two mass_factors rewrites; conditional ONLY on the
   typed §C pack whose every field cites its display (C.1.5(1)+TYP(b), owner §C/HC-2 — the
   note's own GIVEN). V1-7 exhibits a C15Pack model with history-dependent inventory
   violating (u-R) — the machine fence that the pack does NOT yield (u-R), matching V.0's
   honest split ("NOT §C-derivable, HYPOTHESIZED in (XHD-u)"). Clean (modulo the A-7 Prop/
   Type cosmetic).
4. **h_ent projection-by-type (rev-4 pin).** `EntShapeV` has NO independent height field;
   `hent` is a def = `reads.map (fun R => (R.h, R.ustar))` over P̂'s retained reads —
   verified against `MovesD.ShapeRead` (fields `h : ℕ`, `ustar : ℚ`, L3 rev 9). A(ε) :=
   A'(P̂), W_ent := W(P̂) (height-free) — both defs exist with those exact names/shapes.
   V3-2 adds the projection + heights-retained discrimination laws; V3-1 post-split
   distinctness; the instantiation bijection (V3-5) carries the pass-3 F1 content with
   XHD-d-shallow as its displayed hypothesis. Faithful throughout.
5. **Design-freedom slots.** Adjudicated at A-5 (slot 1: real, resolve by deletion) and A-2
   (slot 2: content pinned by the note; the Lean encoding needs a Defs amendment — escalated
   to critical). Inventory undercount recorded at A-5.
6. **V6 gate layer vs the sealed V-n3 records — recomputed, all displayed numbers exact.**
   Root: TH3+TH12+TH3c+T21+T3 = X³ ✓ (coefficients recomputed); m_H3 row 0/1/4/10/35/56/84/
   165/286 ✓ incl. the m_H3 = 0 at q = 2 falsifier AS A NAMED LEMMA ✓; 45 = 5×9 entries ✓.
   A2: chart {h₂ = t ≥ 1, h₀ = 3t+2u+1} ⟺ {h₂ ≥ 1, h₀ > 3h₂, h₀−h₂ odd} ✓ (omega-checkable
   both ways); E = (3(h₀+h₂)−1)/2 = 6t+3u+1 ✓, sealed (4,1) ↦ 7 ✓; T = (X−1)², nine evals
   1…144 ✓. s_blk2: Tsplit+Tinert+Tdbl = X(X−1) ✓; char-2 recounts are the SAME polynomials
   ✓ ((X−1)(X/2−1) = (X−1)(X−2)/2). Gate B: ι = 2·2⁻³ = 1/4, T(2) = 1, g = 2⁻³, μ̂ = 2⁻⁵ =
   1/32, shadow = 2·1 = 2, marked pairs 2^{3N−5} ↦ 16/128, A(ε) = 3, W_ent = 3, I^ent =
   q(q−1) = q·|β₀| ≠ |β₀| ✓ all match V.6.4. Honest-scope split (Lean primes {2,3,5,7,11,13}
   re-derive the degree-≤3 identification; prime powers 4/8/9 stay the Python seal's) is
   recorded, deviation-free. B-side box census correctly NOT claimed in-kernel (§0 scopes
   "dyadic arithmetic and two-history discipline"). Two-history unit (V6-4b) carries the
   finding-6 discipline verbatim (per-history (U-A), inventory shift-free, commonality
   DERIVED). Exception: the V6-1c sketch predicate — A-4.
7. **Axiom candidate fenced.** Exactly one: V6-4c's `CoprimeLiftPack` — typed premise now,
   Mathlib-first, "published-axiom candidate per campaign §4 — flag at E-phase, do NOT
   silently strengthen", repeated in §5's WATCH list. No other axiom or statement-fence
   change anywhere (all structures additive; imports never edited). Clean, modulo the §0
   banner wording (A-6).
8. **Full sweep of 70 units.** Count exact: V0[4] V1[7] V2[10] V3[11] V4[12] V5[9] V6[10]
   V7[7] = 70; difficulty census recounted per unit: 32 easy / 33 medium / 5 hard EXACT,
   HARD set = {V3-5, V4-6, V5-2, V7-4, V7-5} matching §5, splits pre-approved on all five.
   Per-unit moves_refs verified against the V-TABLES text: V2-4/V2-5 (VAL(a)/(b) split with
   the rev-3 (XHD-u) tag and the unconditional W(γ) bound), V2-6 (m/gcd audit law), V2-7
   (VAL.1 worked instance FG/FL/FS = 1/0/0), V2-8 (anchor twist, Python evidence cited not
   claimed), V2-9/V2-10 (DEG-CONS, split bounds incl. the Wstate > Wloc instance), V3-6
   (ι as D4R.1-SUM sub-sum, division-free, μ̂-typed), V3-7/V3-8 (ENT-AGG's two halves with
   the exact conditionality split and (iv)-REP nowhere), V3-9a/b/c (ENT-COUNT/(ENT-U)/
   INIT-RAT ledger-exact, the I^ent = |β₀| fence displayed), V4-1..V4-12 (the (ii)/(iv)/(v)
   clauses: four PART-1 legs verbatim, PART-2 surplus with NO substochasticity, n = 3
   surplus ≡ 0 by 2+2 > 3, REP's ObsCheck proviso, MEAS marked-space retyping with the
   equal-f-projection witness, HMC false/true instance pair, the naming-discipline iff with
   its quantified-weights sharpening — a displayed, sound formal reading), V5-1..V5-7c
   (COMP-h/hΣ/Σ/AGG with hypothesis tags verbatim; J once-per-cell + (J-RAT) in the
   (iv)-POLY pattern + the not-marked-T·G fence both ways), V7-1/V7-2 (the ledger record and
   the [1v]-COND capstone with (v) never concluded), V1-5 (discharge = INHABITATION, no
   True-collapse, the no-substitution fence). Ownership fences hold: no unit proves XHD/
   (ENT-U)/HMC/ENT-COUNT; nothing states a per-f density; every μ̂ export MuHat-wrapped;
   (JC-INV)/CL-19 absent as promised. §0's [2a]-discharge upgrade claim is legitimate:
   MovesSp has no live `sorry` (source-checked); MovesD core likewise; MovesS carries its
   own declared open N2/RS2 sorries, consumed only as vocabulary. Exceptions: the units
   named in A-1/A-2/A-3.

## C. DISPOSITION

REJECT for repair of A-1 and A-2 (both are carrier/Defs-level; no V-TABLES content is
implicated), with A-3–A-7 folded into the same revision. Expected repair shape (for the
writer, not binding): (i) re-key the MeasuredSide entrance instantiation to the bounded
template family with ιDom = H(ε̊), declare the aggregate ι-carrier in 2.F, restate V3-8/
V3-9c against it and expose V3-9c's per-template PolyGeom; (ii) add the history-extension
operation to StepSys (or make Hist path-inductive) and display the chain base+cons ties as
XHDd fields; (iii) complete the design-freedom inventory; (iv) fix V6-1c's sketch to
factorization enumeration; (v) sweep A-6/A-7's wording and danglers.

*(Fable fresh-instance audit, 2026-07-28. Read/judged only; nothing edited.)*
