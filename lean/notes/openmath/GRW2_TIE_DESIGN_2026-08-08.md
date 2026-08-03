# gr(w₂) TIE-LAYER DESIGN — the obligation binding the accepted ITER-LAW's harness values to the graded-ring gr(w₂) semantics, split into a harness-side carrier instantiation (GRT-1, priced S/M) and the open semantic tie proper (GRT-2 = grTie, priced L, obligation package displayed); DESIGN ONLY — nothing asserted, nothing proved, no .lean touched

**Unit:** gr(w₂) tie-layer design note (SYNTHESIS PASS 8 queue #4; charter =
`docs/SYNTHESIS_PASS8_2026-08-08.md` §S4 item 4 + §S3(ii): "the gr(w₂) carrier tie
(DITER §S3's displayed-missing layer, J3b's prerequisite) should be DESIGNED as a
consumer of the accepted ITER-LAW's L6 ANCHOR-VAL + L7 PAIR-VAL plus the accepted GRB
retarget"). **Genre: DESIGN NOTE.** Every Lean or display block below is a CANDIDATE
STATEMENT under the trust boundary — new-statement sites, review-owed at E-phase;
no proof is claimed, no gate fires, no acceptance counter exists for this note's
candidates. **Author:** Fable design unit, campaign date 2026-08-08 (wallclock
2026-08-03).

## S0. Spec gate, inputs, and the standing citation

**Spec gate EXECUTED (the plan-level-adversarial rule; charter: "Codex plan-review
before drafting; no new mechanism admitted").** The v0 architecture plan (the
two-layer harness/semantics split of §S1 below, with three candidate shapes) was
passed to Codex in a fresh context BEFORE this note was drafted. Verdict: **12
CRITICAL / 17 GAP findings on the v0 plan** — none refuting the two-layer split
itself, option (i) (representative transport) ratified as "the more honest
construction", every finding a foldable design constraint. Full report archived at
`lean/notes/openmath/GRW2_TIE_DESIGN_codex_planreview_2026-08-08.txt`; the fold map
is displayed at S0.1. All 29 findings are folded into the sections below; where a
finding names an obligation this note cannot discharge by design (it designs, it
does not prove), the obligation is DISPLAYED as part of the candidate's price.

**THE STANDING CITATION (the VC36b rider: pasted from the ledger's defined-term
block, never re-typed from memory).** From
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, entry "## ITER-LAW ACCEPTED —
2026-08-03 (orchestrator adjudication; 2-clean model-diverse bar met)":

> Scope as accepted: the harness
> tower class (superset of DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence
> restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1;
> gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3 untouched.

and, same ledger, the r36 acceptance-sweep wording of record (the full-qualifier
form):

> SCOPE AS ACCEPTED:
> proved and ACCEPTED on the harness tower class (standard-lift; a STRICT
> SUPERSET of DITER_RESTATE §S2's pinned E₂ = e₀e₁ > 1 setting; coincides
> with the §S2 display on the nose restricted to E₂ > 1; the E₂ = 1 leg a
> harmless COR-3-covered extension outside the statement of record);
> RESIDUALS ALL THREE at every site: (ITER-LAW-LIFT) open exactly at
> g₀ = 1 ∧ δ₁ = 1; the gr(w₂) semantics wrapper rides the accepted GRB
> retarget consumer-side; orders ≥ 3 untouched.

Abbreviation used at every display site below (Codex finding 1 [CRITICAL] folded —
the citation rides EVERY candidate, not a dead-ends footnote): **[ITER-LAW-CIT]** :=
the full-qualifier form above, verbatim. Any consumer copying a candidate out of
this note must copy the tag's expansion with it.

**Inputs and their standings (nothing else is consumed):**

1. **ITER-LAW [ITER-LAW-CIT]** — proof note `ITERLAW_2026-08-08.md` (acceptance
   brackets at its S0): the harness calculus S0 (eq12 both levels, ε₁, R₁/R₂ reads,
   val, anchors φ_γ = π^{u₁(γ)}Φ₀^{s₁(γ)}Φ₁^{s₂(γ)}, window W = {γ : u₁(γ) ≥ 0}),
   L1 EQ12-ADD, L2 INNER-SHIFT, L3 WINDOW, L4/L5 ε-layer, L6 ANCHOR-VAL
   (val(φ_γ) = ε₁(γ₁(γ)) ≠ 0 on W), L7 PAIR-VAL
   (val(φ_γφ_{γ′}) = z̄^{δ₂}ε₁(γ₁(γ))ε₁(γ₁(γ′)) on W×W), the THEOREM on W×W, and
   COR-1 (integrality), COR-2 (cocycle identity), COR-3 (degenerations), COR-4
   (ℤ/E₂ descent: γ+E₂ fixes s₁,s₂, shifts u₁ by 1, φ_{γ+E₂} = π·φ_γ exactly;
   mixed-block supplement `iterlaw_cor4_mixed.py` 18,396/0), COR-5 (W-MULT on
   anchor pairs).
2. **The accepted GRB retarget** (`GRB_ORDER2_2026-08-05.md`, ACCEPTED leaf;
   conditional throughout on its §0 ladder inputs (V1)_{≤i+1}, (KP)_{≤i−1},
   (H-CHAIN) + the standing §3.3 [T] pins): clause (0) structure (Thm 4.8/Cor 4.9:
   Δ = K_i[ȳ], K_{i+1} = K_i[z̄] via the ψ-quotient), clause (0′) anchors +
   Lemma CARRY-1 (ϕ_γϕ_{γ′} = ϕ_{γ+γ′}·ȳ^δ **in the LOCALIZED gr(w_{i+1})**),
   Lemma D-REAL (the gauged p ↦ 1 anchor system at the LAST-READ layer is
   K_{i+1}[u]/(u^{e_i} − z̄), abscissa-coset indexed; the gauge is an [F.0] stage
   datum), S6a (W-MULT) with the domain-cancellation proof (rank-one freeness of
   gr_γ(w) over Δ, Thm 4.2 — GRB §R7.1). N-1 = the accepted harness-faithfulness
   legs (harness operators = FGMN print operators at order 2, family-ledger scope).
3. **DITERSUP_STMT_2026-08-08.md** §S3 (the `DIterCarrier`/`IterLaw` interface
   displays + the "missing tie" paragraph this note designs) and §S2/S4 (the J3b
   discharge shape and gate row; J3b = BLOCKED-ON-APPLICATION +
   BLOCKED-ON-CARRIER-TIE, its r36b three-residual erratum bracket).
4. **DITER_RESTATE_2026-08-08.md** §S2 (statement of record) + §S3 (consumable
   spec: 𝒟₂ carrier, both constants + fibration term, the three sanity gates, the
   cyclic fence).

**What is NOT an input:** the MOVES §B2-FINAL formalism (NOT accepted — §S4 dead
ends), any orders-≥ 3 template, any non-standard-lift form of ITER-LAW, any claim
that an order-2 graded-carrier layer (R₂/w₂ at composite stages) exists in the Lean
corpus (it does not — PROJECT_STATE standing obligation 2).

### S0.1 The plan-review fold map (all 29 findings; C = critical, G = gap)

| finding | fold |
|---|---|
| C1 (residuals not at every use) | [ITER-LAW-CIT] tag mandatory at every candidate display (S2) |
| G2, G3, G5, G6 (totalization ≠ COR-4 alone; cofinality; well-definedness; normalization) | GRT-1 split into named sub-obligations 1a–1f with exact accepted cites (S2.1) |
| C4 (option (ii) vacuity) | option (i) is the design of record; option (ii) REJECTED; the interface weakness displayed as P1-FLAG-1 (S3.1) |
| G7, G8, G9, G10, G11 (carrier field obligations; "canonical" relative to the framed tower; hper not from COR-4; γ₂ Nat-typing; E₂ > 1 repeated downstream) | folded into GRT-1a/1b displays + the framed-tower convention (S2.1); E₂ > 1 repeated at every downstream statement |
| C12, C13 (actual vs localized vs gauged gr; p ↦ 1 not a ring map) | the target chain TC-1/2/3 displayed with exact per-step status (S2.2) |
| C14, C17, C18, C19 (iso needs a faithfulness/basis package; the inner z₁ source; tautology risk; grading typing) | GRT-2's obligation package OB-1..OB-6 (S2.2) |
| C15 (N-1 not a blanket bridge) | OB-6 separates N-1's operator-level content from the missing carrier identification (S2.2) |
| C16 ("D-REAL one level up" is the theorem, not an input) | OB-1/OB-3 named as GRT-2's own content; nothing cited for them (S2.2) |
| C20 (grTie two-conjunct def too weak) | grTie re-bundled with the derivation certificate + semantic clause (S2.3) |
| C21 (consumption map mis-assigned) | corrected map (S3): GRT-1 → hcarrier AND hIter; GRT-2 → the semantic clause consumed by J3b's PROOF; J3B-FLAG-1 raised |
| C22, C23, G24, G25 (circularity fences; falsifier honesty) | tautology fence in OB-5; falsifiers redesigned with independent legs + honest "not numerically falsifiable" display (S2.1/S2.2) |
| G26, C27 (prices) | GRT-1 re-priced S/M aggregate; GRT-2 re-priced **L** (math), Lean-blocked (S2) |
| G28 (binder decision) | GRT-3 displayed as NOT statable-complete until the σ₁/H₁ attachment decision (S2.3) |
| C29 (no premature retirement) | S5: BLOCKED-ON-CARRIER-TIE does NOT retire with this note (S3/S5) |

## S1. THE OBLIGATION, stated exactly (charter item (a))

**Site.** DITERSUP §S3 displays the interface pair `DIterCarrier`/`IterLaw` and
then the missing layer: "the clause binding `c` to the ACTUAL degree-0 composite
digit algebra of gr(w₂) — anchor monomials φ_γ = π^{u₁}Φ₀^{s₁}Φ₁^{s₂}, class
values val(φ) = (R_{2,w₂(φ)}(φ))(y ↦ z̄) ∈ K₂,
c(γ,γ′) = val(φ_γ·φ_{γ′})/val(φ_{γ+γ′})". Gate J3b's discharge shape
(`dIterJunctionSupplier'_of_iterLaw`, DITERSUP §S2) takes hypotheses
(hcarrier, hIter); its docstring fence requires the digits computed IN 𝒟₂. The
tie is J3b's only non-application prerequisite (synthesis pass 8 §S4 item 4).

**The obligation (one sentence).** For `IterLaw` to be dischargeable AS THE
INTENDED SEMANTIC FACT (not vacuously — S0.1 C4), every standard-lift order-2
tower instance T with E₂ := e₀e₁ > 1 must yield (α) CANONICAL carrier data D(T)
whose s₁/s₂/ℓ₀/γ₂ fields are DERIVED from T's eq-(12-int) data, (β) a TOTAL
cocycle c_T : ℤ → ℤ → K₂ˣ that agrees on W × W with the harness value cocycle
val(φ_γφ_{γ′})/val(φ_{γ+γ′}) and satisfies IterLaw D(T) c_T as a THEOREM, and
(γ) the identification of (⊕_{γ∈ℤ/E₂} K₂·u_γ, c_T) with the degree-0 anchor
subalgebra of the ACTUAL graded ring gr(w₂), reached through a defined
localize–gauge–quotient chain — (α)+(β) from ITER-LAW [ITER-LAW-CIT] alone,
(γ) riding the accepted GRB retarget consumer-side with its ladder
conditionality displayed.

**The two-layer split (the design's spine).** (α)+(β) =: the HARNESS LEG — every
ingredient is inside the accepted ITER-LAW note; no graded ring is mentioned; this
is candidate GRT-1. (γ) =: the SEMANTIC LEG — this is what "the gr(w₂) semantics
wrapper rides the accepted GRB retarget consumer-side" (residual (ii) of
[ITER-LAW-CIT]) means concretely; it is candidate GRT-2 = `grTie` proper, and its
Lean home additionally requires the order-2 graded-carrier layer (R₂/w₂ at
composite stages) that the corpus does not have (standing obligation 2). The
split is exactly §S3(ii)'s "PAIR-VAL's content read functorially", made honest:
the functorial reading is not free — it is GRT-2's displayed obligation package.

## S2. THE CANDIDATES (charter item (b))

Conventions for all three candidates. T ranges over the harness tower class of
`ITERLAW_2026-08-08.md` S0 (standard-lift; O a DVR; reads (e₀,h₀,ψ₀), (e₁,h₁,ψ₁);
gcd conditions; K₂ = K₁[z̄]) RESTRICTED to E₂ = e₀e₁ > 1 — the restriction is
repeated in every downstream statement (S0.1 G11), matches `DIterCarrier.hE₂`, and
is exactly the locus where [ITER-LAW-CIT]'s class coincides with DITER_RESTATE
§S2's pinned setting on the nose. "Canonical" always means canonical RELATIVE TO
THE FRAMED TOWER T, with the derivation proved at construction time; nothing is
claimed recoverable from an arbitrary `DIterCarrier` (S0.1 G8). Every displayed
definition and statement below carries: **[STATEMENT-REVIEW FLAG — new-statement
site under the trust boundary; review-owed at E-phase against the harness's exact
conventions (grb_order2_check.py / iterlaw_check.py) before any Lean landing.]**

### S2.1 GRT-1 — the canonical carrier instantiation + the totalized value cocycle (the harness leg)

**Citation carried by this candidate:** ITER-LAW [ITER-LAW-CIT]. Consumed
clauses: S0 calculus (definitions), L1, L3, L6, L7, THEOREM (W×W), COR-1, COR-2,
COR-4 (+ its mixed-block supplement). Nothing outside the accepted note is
consumed. Residual guards ON this candidate: standard-lift only (residual (i)
displayed wherever a lift enters — the canonical D(T) is only claimed on the
standard-lift class); order 2 only (residual (iii)); the candidate makes NO
gr(w₂) claim (residual (ii) untouched here — that is GRT-2).

**Display (candidate statement, review-owed).** For T as above:

    (GRT-1a) CANONICAL FIELDS.  D(T) : DIterCarrier K₂ with
      e₀, e₁ := T's read indices;  z₁ := the frame letter (unit: ψ₀(0) ≠ 0,
      K₂ a field);  z̄ := the read letter (unit: ψ₁(0) ≠ 0);
      ℓ₀ := the normalized Bézout inverse (exists, unique with 0 ≤ ℓ₀ < e₀,
      by gcd(e₀,h₀) = 1 — harness `bezout`; the GMN-print attribution is
      TR3-S1 S0's standing displayed hypothesis, not consumed);
      γ₂ := e₁·w₁Φ₁ + h₁ = e₁e₀g₀h₀ + h₁ ∈ ℕ  (Nat-typing: every factor ≥ 1
      in the harness class — ITERLAW S0 derived data; S0.1 G10);
      s₁ := γ ↦ s(γ₁(γ)),  s₂ := γ ↦ s₂(γ)  (the iterated eq-(12-int) split).
      Field obligations, each a named sub-lemma, none a consequence of the
      IterLaw equation itself (S0.1 G7):
        hs₁/hs₂: eq-(12-int) uniqueness gives 0 ≤ s < e at both levels;
        hper:    derived DIRECTLY from the two eq12 decompositions —
                 E₂ ≡ 0 (mod e₁) fixes s₂ and shifts u₂ by e₀, hence γ₁ by
                 e₀, fixing s₁ (the computation recorded inside COR-4's
                 proof, re-derived here from eq12 so the dependency runs
                 eq12 → hper → descent, never backwards; S0.1 G9).

    (GRT-1b) W-COFINALITY.  u₁(γ + mE₂) = u₁(γ) + m for all m ∈ ℤ (COR-4's
      recorded shift law), hence every γ ∈ ℤ has W-representatives γ + mE₂
      for all m ≥ −u₁(γ) — the cofinality clause displayed as its own
      sub-lemma, not folded silently into "descent" (S0.1 G3).

    (GRT-1c) TOTALIZATION (option (i) OF RECORD — representative transport).
      c_T(γ,γ′) := val(φ_{γ+mE₂}·φ_{γ′+m′E₂}) / val(φ_{(γ+γ′)+(m+m′)E₂})
      for ANY m, m′ making both numerator anchors W-resident (the denominator
      is then W-resident by L3 WINDOW).  WELL-DEFINEDNESS — under INDEPENDENT
      changes of the two representatives, with the induced change of the sum
      representative (S0.1 G5) — is NOT COR-4 alone (S0.1 G2): it is proved by
      evaluating BOTH sides with the accepted THEOREM on W×W and observing
      the closed form depends only on (γ mod E₂, γ′ mod E₂) via GRT-1a's
      hper.  I.e. the totalization consumes the accepted theorem itself;
      it is ordinary descent, no new mechanism.  (Numerically pre-tested at
      exactly this clause: the COR-4 mixed-block supplement, 18,396/0.)

    (GRT-1d) NORMALIZATION.  c_T(0,γ) = c_T(γ,0) = 1 (eq12 at 0 gives
      s₁(0) = s₂(0) = 0, so δ₂ = 0 and the inner exponent telescopes to 0) —
      the unital clause a K₂-algebra needs, displayed (S0.1 G6).

    (GRT-1e) THE HARNESS TIE.  IterLaw D(T) c_T  ∧  D(T).InnerIntegral —
      every c_T value equals a W×W value cocycle evaluation (1c), which
      equals ITER-LAW's closed form (the accepted THEOREM), which equals
      IterLaw's right side at the same residues (hper);  InnerIntegral is
      COR-1 extended over ℤ by hper.

    (GRT-1f) COCYCLE IDENTITY ON ℤ.  c_T(a,b)·c_T(a+b,t) = c_T(b,t)·c_T(a,b+t)
      — COR-2 transported through 1c.

**Price: S for 1c–1f given 1a/1b; S/M AGGREGATE** (S0.1 G26 folded — the eq12
bookkeeping sub-lemmas 1a/1b are part of this candidate's bill, not free). Lean
home: rides P1 (the carrier Defs unit, DITERSUP §S5 — application-independent);
consumes NO graded-carrier layer, NO application, NO Asvin gate.

**What refutes it cheaply (falsifier design; S0.1 G24/G25 folded).** A small
exact-arithmetic runner over the iterlaw_check row roster + 2 fresh rows:
(i) INDEPENDENT-representative test — for sampled (γ,γ′) with γ,γ′ ranging over
[−3E₂, 3E₂] including u₁ < 0 points and near-boundary u₁(γ) = 0 points, compute
c_T via TWO independently chosen representative pairs (m₁,m₁′) ≠ (m₂,m₂′) BEFORE
any quotienting and compare; (ii) compare against IterLaw's closed form on the
same samples; (iii) unital and cocycle spot rows; (iv) control rows at e₀ = 1 and
e₁ = 1 (COR-3 shapes); the g₀ = 1 ∧ δ₁ = 1 stratum included ONLY on standard-lift
towers, with the (ITER-LAW-LIFT) residual displayed in the runner header.
Prediction: 0 violations in every family — any RED refutes GRT-1c/1e as designed.
HONESTY: this tests the descent arithmetic and the design's internal consistency;
it does not re-test the accepted theorem (already sealed 35,232/0 + 89,056/0
F2c + 18,396/0 mixed).

### S2.2 GRT-2 — `grTie` proper: the semantic identification with gr(w₂) (the open tie)

**Citation carried by this candidate:** ITER-LAW [ITER-LAW-CIT] + the accepted
GRB retarget (S0 input 2), the latter CONDITIONAL on its §0 ladder inputs
((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN)) and the standing §3.3 [T] pins — that
conditionality is part of GRT-2's display forever, not removable by this note.
Residual guards: standard-lift only; order 2 only; E₂ > 1; this candidate IS
residual (ii)'s content, designed — not discharged.

**The target chain TC (S0.1 C12/C13 folded — each step an exact object, each
step's status displayed).** Fix T. The claimed target is reached from the actual
graded ring in three steps:

    TC-1 LOCALIZE.  gr(w₂) → gr(w₂)[p⁻¹] — the home where CARRY-1 is recorded
      (GRB S5.2: "in the localized gr(w_{i+1})").  STATUS: accepted
      construction at the last-read layer; its COMPOSITE-stage instance
      (localizing the order-2 graded ring at the class of π) is OB-1 below.
    TC-2 GAUGE.  The [F.0] weight gauge p ↦ 1 — ONE global unit choice fixing
      the reference normalizer per weight period (D-REAL's stage datum,
      GRB S5.3).  NOT a graded-ring homomorphism from TC-1's output alone
      (S0.1 C13): it is the passage from the ℤ-weight-graded localization to
      its quotient by the unit subgroup p^ℤ (p is a weight-E₂ unit after
      TC-1 — harness check: w₂(π) = e₁·w₁(π) = e₁e₀ = E₂, matching COR-4's
      φ_{γ+E₂} = π·φ_γ), collapsing the grading ℤ → ℤ/E₂.  The precise
      composite-stage formulation is ITSELF part of OB-1; the accepted
      precedent is D-REAL's "well-defined: two such γ differ by a multiple
      of e_i, and ϕ_{γ+e_i} = ϕ_γ·p is gauged away", one level down.
    TC-3 RESIDUE QUOTIENT.  ȳ ↦ z̄ via K₁[ȳ]/(ψ₁) = K₂ — clause (0)'s
      polynomial ring Δ quotiented by the read's ψ₁ (Thm 4.8 + Cor 4.9,
      accepted).  A quotient/base-change construction, NOT a relabeling —
      it has a kernel (ψ₁'s ideal), displayed.

At order 2 the composite-stage instances of TC-1/TC-2 are NOT accepted
constructions — they are the "D-REAL one level up" that S0.1 C16 correctly
identifies as the theorem to prove, not an input. GRT-2 owns them.

**Display (candidate statement, review-owed; the note's named deliverable).**

    (GRT-2 / DIterCarrier.grTie, semantic form)  For T (standard-lift,
    order 2, E₂ > 1) satisfying the GRB §0 ladder inputs: with D(T), c_T
    per GRT-1, and u_γ := [φ_γ]_{TC} (the anchor class through TC-1/2/3),
    the K₂-linear extension of u_γ ↦ [φ_γ]_{TC} is an isomorphism of
    K₂-algebras

        Ψ : (⊕_{γ ∈ ℤ/E₂} K₂·u_γ, multiplication u_γu_{γ′} = c_T(γ,γ′)u_{γ+γ′})
              ≅  𝒜(T) := the K₂-span of the anchor classes inside the
                 degree-0 component of the TC-transported gr(w₂),

    where 𝒜(T)'s multiplication is gr(w₂)'s OWN ring multiplication
    transported through TC — never c_T, never ITER-LAW's closed form
    (the tautology fence, S0.1 C22/C18).

**The obligation package (what "read functorially" actually costs — S0.1
C14/C15/C16/C17/C18/C19 displayed as named opens; GRT-2 is PROVED only when ALL
of these are):**

    OB-1 (target exists).  TC-1/TC-2 are legitimate ring-level operations at
      the COMPOSITE stage, and the degree-0 component + its grading are
      well-defined after the gauge (which ℤ/E₂-indexing survives — S0.1 G19:
      the abscissa-pair (s₁,s₂) coset indexing, the fibred ℤ/E₂ of
      DITER_RESTATE §S3 obligation 1).  The D-REAL construction one level up;
      no accepted clause supplies it.
    OB-2 (map well-defined).  [φ_{γ+E₂}]_{TC} = [φ_γ]_{TC} — φ_{γ+E₂} = π·φ_γ
      (COR-4, exact) + TC-2 gauging π away.  Rides OB-1's gauge legitimacy.
    OB-3 (multiplicativity).  [φ_γ]·[φ_{γ′}] = c_T(γ,γ′)·[φ_{γ+γ′}] in 𝒜(T).
      The OUTER z̄^{δ₂} factor is CARRY-1's ȳ^δ through TC-3 (accepted at the
      last-read layer).  The INNER z₁ factor is NOT supplied by CARRY-1
      (S0.1 C17): it requires the graded-side counterpart of the ε₁
      normalization identity — the anchor-normalization law INSIDE the
      graded algebra whose harness-side shadow is exactly L6/L7 (accepted).
      The graded-side identity is OB-3's own content, riding GRB (0′)/S6a +
      OB-6, not riding the harness.
    OB-4 (independence).  The classes {u_γ} are K₂-linearly independent in
      𝒜(T) — the composite-stage analogue of Thm 4.2's rank-one freeness of
      gr_γ(w) over Δ (the same fact S6a's domain-cancellation used, GRB
      §R7.1).  Independence is the NON-tautological half of the iso: spanning
      of 𝒜(T) is definitional and carries no content (S0.1 C18 displayed).
    OB-5 (tautology fence).  𝒜(T) and its multiplication are defined through
      TC from gr(w₂)'s own structure BEFORE c_T is mentioned; any draft that
      presents 𝒜(T) by generators-and-relations from the closed form has
      assumed the conclusion and is rejected at statement review.
    OB-6 (harness-val compatibility).  val(φ) = the TC-read of [φ] for anchor
      products — the identification of the harness calculus with the actual
      composite graded read.  N-1's accepted legs give OPERATOR-level order-2
      print faithfulness (family-ledger scope) — a commuting-diagram fact,
      NOT this carrier identification (S0.1 C15); the remainder is precisely
      the R₂/w₂ carrier layer, i.e. PROJECT_STATE standing obligation 2's
      territory.  OB-6 is where the tie and the deep-wild order-≥ 2
      classifier obligation MEET; neither subsumes the other.

**Price: L (math) — re-priced per S0.1 C27** (the v0 plan said M; the review is
right that OB-1 + OB-3 + OB-4 + OB-6 are the deep semantic obligations, not
corollaries). Lean home: BLOCKED on the order-2 graded-carrier layer (standing
obligation 2); no Lean statement of GRT-2 should be attempted before that layer
exists — only the harness-side GRT-1 compiles today. **BLOCKED-ON-CARRIER-TIE
does NOT retire with this note and does not retire until GRT-2 is proved and
survives its own hostile-pass arc (S0.1 C29).**

**What refutes it cheaply (falsifier design — PARTIAL by nature; S0.1 C23
displayed rather than papered over).** Numerically reachable: (i) OB-3's scalar
shadow — compare harness val ratios against an INDEPENDENT from-print
implementation of the composite read (the N-1 genre: FGMN operators transcribed
fresh, not imported from grb_order2_check.py), on fresh rows including e₀ = 1,
e₁ = 1 controls and near-boundary anchors; (ii) OB-4's shadow — exact rank of
the anchor-value tables over sampled weight windows (rank deficiency would
refute independence cheaply). NOT numerically reachable: OB-1's legitimacy
(localization/gauge as ring operations) and OB-6's carrier identification —
structurally unfalsifiable by sampling; only proof + hostile-pass review reach
them. A falsifier that claimed to test the whole of GRT-2 would be the circular
check S0.1 C23 rejects.

### S2.3 GRT-3 — the J3b feed bundle (consumption shape only)

**Citation carried:** ITER-LAW [ITER-LAW-CIT]; GRB conditionality via the GRT-2
component. E₂ > 1 repeated (S0.1 G11).

**Display (candidate definition, review-owed; re-bundled per S0.1 C20 — the v0
two-conjunct form was too weak):**

    (GRT-3 / grTie, bundled Prop)  grTie (T, D, c) : Prop :=
      (i)   D = D(T)  — the canonical-derivation certificate relative to the
            framed tower T (GRT-1a; canonical means canonical-to-T, S0.1 G8);
      (ii)  D.InnerIntegral  and  c = c_T  (GRT-1c: the totalized VALUE
            cocycle — never free closed-form data; the option-(ii) trap
            fenced);
      (iii) the SEMANTIC clause: Ψ per GRT-2 is an isomorphism onto 𝒜(T)
            (the full OB-1..OB-6 package);
      (iv)  IterLaw D c  (then a THEOREM given (i)–(ii), by GRT-1e).

    (GRT-3-feed, shape only)  Every order-2 junction fiber with E₂ > 1
    arising in a ReadsOf′ history carries (D, c) with grTie — GRT-1 + GRT-2
    specialized at junction stages, PLUS the binder-attachment decision
    (how D attaches to σ₁/H₁ — DITERSUP §S2's flagged E-phase design
    decision).

**Status: NOT statable-complete (S0.1 G28)** until the binder decision is fixed;
that decision is E-phase, adjudicated with the application diff. The feed's
consumption site is **BLOCKED-ON-APPLICATION** (the Asvin P0 gate, DITERSUP §S0
banner). **Price: statement S once the binder decision lands; discharge = L and
equals GRT-2's bill plus junction-stage specialization.** GRT-3's role TODAY is
to fence the consumption shape so no future discharge quietly substitutes bare
(hcarrier, hIter) data for the semantic bundle.

## S3. THE CONSUMPTION MAP (charter item (c); corrected per S0.1 C21)

| candidate | feeds | how |
|---|---|---|
| GRT-1a | **P1** (DITERSUP §S5 carrier Defs, price M) | discharges P1's E-phase flag "the s₁/s₂ tracks must be DERIVED from eq12 data, not free fields, when the gr(w₂) tie lands" — GRT-1a IS that derivation, statable with P1, application-independent |
| GRT-1c–1e | **J3b hcarrier AND hIter** (both — the v0 map mis-assigned hIter-only) | hcarrier: canonical 𝒟₂ data exists at every standard-lift E₂ > 1 fiber (the D(T), c_T pair); hIter: IterLaw D(T) c_T is GRT-1e's THEOREM, so the hypothesis discharges on canonical carriers — SUBJECT to J3B-FLAG-1 below |
| GRT-1f | **JS1** (price S) | the compiled-instance cocycle identity; the general identity already rides accepted COR-2 — GRT-1f transports it to the totalized c_T |
| GRT-1 falsifier rows | **JS3** (price M) | the row-N/row-X value tables {z₁, z̄, z̄z₁^b} re-derivable from the closed form at the compiled falsifier target (accepted S6.6 display, unchanged) |
| GRT-2 | **J3b's PROOF + the docstring fence** | the digits computed IN 𝒟₂ (GlueRun.lean:852–874 fence) presuppose the semantic clause; GRT-2 is consumed by the DISCHARGE ARGUMENT, not by the currently displayed hypothesis pair — see J3B-FLAG-1 |
| GRT-3 | **J3b's E-phase statement** | the corrected hypothesis bundle; makes J3b statable-complete AFTER the binder decision + P0 |
| — | **JS2** | unaffected (definitional collapse; no tie content) |

### S3.1 The two interface flags this note RAISES (feedback to statement review; no statement is edited — statement fence honored)

**P1-FLAG-1 (from S0.1 C4, the option-(ii) vacuity).** As displayed in DITERSUP
§S3, `IterLaw D c` is bare equality with a closed form in D's free fields — so
(hcarrier, hIter) is inhabitable by defining c := the closed form on ANY typed
fields, consuming no ITER-LAW, no anchors, no values, no gr(w₂). This is a
WEAKNESS OF THE INTERFACE, not of the accepted mathematics: the interface cannot
tell the semantic cocycle from freely cooked data. P1's statement review should
either (a) bind c to value data inside the carrier bundle (GRT-3's clause (ii)),
or (b) keep `IterLaw` as-is and route ALL consumption through `grTie` (GRT-3),
never through bare (hcarrier, hIter). This note recommends (b) — it keeps P1's
Defs byte-stable with DITERSUP's displays.

**J3B-FLAG-1 (from S0.1 C21).** J3b's displayed shape
`dIterJunctionSupplier'_of_iterLaw (hcarrier) (hIter)` under-specifies its own
docstring fence: the fence demands computation IN 𝒟₂ (the semantic algebra),
but the hypothesis pair does not force c to be the gr(w₂) cocycle. At J3b's
E-phase the hypothesis bundle should be grTie (GRT-3), aligning statement with
fence. Flag rides to the J3b unit; nothing here edits DITERSUP.

## S4. DEAD ENDS — what the tie CANNOT be built from (charter item (d))

**(1) The MOVES §B2-FINAL formalism bridge — the S3(ii) refutation, spelled
out.** The rejected alternative was ONE transport lemma covering "the remaining
TWIST/DIG legs" by bridging the MOVES carry-algebra/(z+c)^a anchor-monomial
language to the harness eq12/ε₁ calculus. It fails today on two independent
facts. (α) FORMALISM MISMATCH: the accepted ITER-LAW lives entirely in the
harness calculus (eq12 pairs, ε₁ units, R₁/R₂ reads); the MOVES DIG legs live in
the [F.0]/[F.2] carry-algebra language with (z+c)^a anchor-monomial transport —
a tie routed through MOVES needs a formalism bridge FIRST, which is a second tie
of the same difficulty. (β) THE HOME IS NOT ACCEPTED: MOVES §B2-FINAL — the
consolidation the DIG legs live in — was NOT accepted (pass 8: 5 critical /
2 gaps, STRUCTURAL; `MOVES_2026-07-24.md` §B2-FINAL PASS RECORD), and its faulted
points are EXACTLY the obligations a tie needs: critical 1 = the coset-progression
typing is not an invariant of the stated stage data (the grading obligation =
our OB-1/G19); critical 2 = one-anchor-unit normalization does not trivialize a
coset progression (the normalization obligation = our OB-3's inner factor);
critical 3 = the general new-stage digit algebra is not defined (the target
obligation = our OB-1); critical 4 = the aligned quotient/remainder identity
asserted, not proved. Building the tie on B2-FINAL would import, unproved, the
same four obligations this note displays as GRT-2's package — plus the
unaccepted formalism's risk. HONESTY DISPLAY: MOVES §B2-DEF (bottom-up tower
induction, ACCEPTED 2026-07-26, passes 20+21 consecutive clean) SUPERSEDED
B2-FINAL for the induction itself — but B2-DEF is not the anchor-monomial DIG-leg
transport home, and §S3(ii)'s refutation targets the B2-FINAL-language BRIDGE;
nothing in this note touches, re-prices, or borrows from the accepted B2-DEF.

**(2) The single-ζ′ cyclic carrier.** ADJUDICATED FALSE at the canonical
(dig-consumed) anchor alphabet at mixed stacked ramification — NOT-CYCLIC at
22/28 towers, kill-shot row N value set {z₁, z̄, z̄z₁^b} (byte-frozen record,
STRATA_PROBE §S2; DITER_RESTATE §S1). The cyclic fence binds grTie: no draft of
GRT-2/GRT-3 may present 𝒜(T) as F′[u′]/(u′^{E₂} − ζ′) at composite stages. The
information-free abstract crossed-product iso remains information-free.

**(3) ITER-LAW outside its accepted scope.** No candidate may consume: a
non-standard lawful lift at g₀ = 1 ∧ δ₁ = 1 (residual (i), open — the corner is
wave-18 queue #5's separate probe); any orders-≥ 3 form (residual (iii) — the
iterated template is conjectural, TWIST-3/TR3-S4 territory); the E₂ = 1 leg as
statement-of-record content (outside it; the carrier's hE₂ enforces E₂ > 1).

**(4) Unconditional semantics.** There is no route to GRT-2 that skips the GRB
§0 ladder conditionality ((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN) + [T] pins) — the
retarget is the ONLY accepted print bridge, and it is conditional. Likewise no
Lean route exists today: the R₂/w₂ graded-carrier layer is absent from the
corpus (standing obligation 2), so any "compiled grTie" claim before that layer
lands is spurious by construction.

**(5) Bare-interface discharges (the option-(ii) trap, found by this note's
plan review).** A "tie" that inhabits (hcarrier, hIter) with closed-form-defined
c is vacuous — it consumes nothing and certifies nothing (S0.1 C4). Fenced by
GRT-3 clause (ii) + P1-FLAG-1/J3B-FLAG-1.

## S5. What this unit does NOT do

No `.lean` file touched; no proof of GRT-1/2/3 or any sub-obligation; nothing
asserted beyond design shape; no gate fired; no acceptance arc opened. No edit
to any statement, record, or byte-frozen artifact (DITERSUP/DITER_RESTATE/
ITERLAW/GRB/MOVES all read-only here; the two S3.1 flags are RAISED, not
applied). BLOCKED-ON-CARRIER-TIE stands; BLOCKED-ON-APPLICATION stands; the
Asvin P0 gate stands. No new mechanism: every construction displayed is either
an accepted-clause consumption or a NAMED OPEN obligation (OB-1..OB-6). No
orders-≥ 3 claim, no non-standard-lift claim, no E₂ = 1 claim, no (H1) status
change. The recommended execution order for successors: GRT-1 with P1 (S/M,
application-independent) → GRT-2 as a dedicated math unit (L, hostile-pass bar,
after or alongside the ITER-LAW-r probe's outcome) → GRT-3 at J3b's E-phase
(post-P0, post-binder-decision).

— gr(w₂) tie-layer design unit, campaign date 2026-08-08 (wallclock 2026-08-03).
