# DIterJunctionSupplier STATEMENT — the supplier's corrected interface displayed against the σ.wPrev-keyed clause (SideReads′, the accepted FGMN diagnosis), carrying the DITER §S3 obligations; EVERY GATE BLOCKED-ON-APPLICATION (the three-token repair is Asvin-gated, NOT applied; the old-clause gates stay refuted/vacuous per the byte-frozen JuncForge record); post-application work priced S/M/L per gate

**Unit:** DIterJunctionSupplier STATEMENT (synthesis-7 queue #9, RE-PRICED per the
r34/§39 standing against the ACCEPTED FGMN diagnosis; charter =
`docs/SYNTHESIS_PASS7_2026-08-08.md` queue #9 + `docs/ROOT_ASSEMBLY_2026-08-02.md`
r34/§39 wave-15-remainder display: "the `DIterJunctionSupplier` statement — re-priced
against the accepted FGMN diagnosis, its §S6 gate display accepted content").
**Genre: STATEMENT-ONLY.**  No proofs; no `.lean` file touched; every Lean block
below is a DISPLAY (Lean-ready, verbatim-typed in this note, NOT committed code).
**Author:** Fable statement unit, campaign date 2026-08-08 (wallclock 2026-08-03).

## S0. Spec gate + the standing inputs (what is accepted, what is gated)

Charter located (above); not previously executed (no `DITERSUP*` note or commit
existed).  The four inputs this note composes, with their exact standings:

1. **The FGMN diagnosis is ACCEPTED** (`FGMN_REDERIVATION_2026-08-08.md`, accepted at
   REVISION 10, commit ec64503; 14 passes / 10 revisions, model-diverse, three
   executed legs): the compiled `SideReads` double-scales the stride weight — its
   clause (i)/(ii) window functional reads `ν.e * ν.σ.w (B j) + j * ν.h` where the
   print (FGMN Thm 4.2 / Def 3.16 / eq (13)) keys the window at the PARENT valuation,
   i.e. `ν.e * ν.σ.wPrev (B j) + j * ν.h`; the source glue step FIRES at row A (THE
   ROW-A SOURCE VERDICT); the compiled parity/landing walls are transcription
   artifacts.  **The repair is a THREE-TOKEN diff (`ν.σ.w` → `ν.σ.wPrev` at
   HC2/Defs.lean:285/287/292), Asvin-gated, NOT APPLIED** — the application
   change-set is the gated application unit's deliverable (FGMN REVISION-9 scope
   cut), in the RECOMMENDED new-definition mode (FGMN REVISION 2): a NEW `SideReads'`
   + primed mirrors (`SideClauseR1'`/`sideReads_r1'`, the R2 pair, the Window/CU1
   ring) + the glue route restated, with `SideReads` and every JuncForge theorem
   byte-frozen as the historical record of the mis-scale.
2. **DITER_RESTATE §S3** (`DITER_RESTATE_2026-08-08.md`): the supplier obligations —
   𝒟₂ carrier on the canonical ℤ/E₂ fibred anchor indexing; the (ITER-LAW) cocycle
   with BOTH constants (z̄ outer, z₁ inner) AND the fibration term ℓ₀γ₂δ₂; the three
   sanity gates (B0a associativity; D-REAL degeneration at e₀ = 1; NOT-CYCLIC on the
   row-N value pattern); the cyclic fence (no single-ζ′ carrier at composite stages).
   (ITER-LAW) itself is an OPEN LEMMA (instance-true, 0/804): consumable only as a
   displayed hypothesis.
3. **JUNCFORGE_S2** (`JUNCFORGE_S2_2026-08-08.md`, REVISIONS 1–4): the byte-frozen
   row-A refutation theorems binding the OLD clause —
   `juncforge_no_e2_junction` (any old-clause `SideReads` of fA at a Φ1A-keyed frame
   has ν.e = 1; char-free, any Φnext), `juncforge_deep_wall`/`_F4` (no old-clause
   recording lands Φ₂A; char 2), `juncforge_junc_bundle_false` (the 3-conjunct core
   false; char-2 + interior Φ₂A pin), `juncforge_D0_instanceFalse` +
   `juncforge_gate_hbundle_false` + `juncforge_gluePacket_false` (the compiled
   RCW-seam gate pair vacuous), and the positive fragment
   `juncforge_clauseIII_derivable` (clause (iii) exact at the (2,3) read-pair pins).
   Under the new-definition route ALL of these retain their exact compiled meanings
   forever (the FGMN REVISION-10 acceptance list (c) fixed point).
4. **The current supplier** (`H1/GlueRun.lean:875`, `DIterJunctionSupplier` — stated,
   never asserted) and the compiled gate pair
   (`gate_glue_junction`/`gate_glue_conditional`, GlueRun.lean:1105/1161) at the
   RCW D0-degenerate seam.

**THE HONEST GATING BANNER (applies to EVERY display in this note):**
`SideReads'` and every primed name below names NOTHING in the corpus today.  Every
gate in §S4 is **BLOCKED-ON-APPLICATION**: it can fire only after (α) the Asvin gate
approves the three-token repair AND (β) the application unit lands the primed-mirror
change-set (the scratch-worktree diff + post-application hostile pass, per the FGMN
REVISION-9 cut).  Until then the ONLY compiled truths in this area are the old-clause
gates, and those stay exactly where JUNCFORGE_S2 left them: the e ≥ 2 junction gates
REFUTED at the row-A fiber, the compiled glue gate pair VACUOUS at its D0 seam.
Nothing below weakens, edits, or supersedes any byte-frozen statement.

## S1. The corrected clause context: `SideReads'` (DISPLAY — the application unit's definition, shown here so the gates are readable)

The new-definition route introduces `SideReads'` = the compiled `SideReads`
(HC2/Defs.lean:280–314) verbatim EXCEPT the three re-keyed tokens (marked).  Clauses
(iii)–(vi) are byte-identical to the compiled originals — displayed abbreviated here,
with the full text pinned by the FGMN §S3 NEW block + Defs.lean:296–314:

```lean
-- DISPLAY ONLY — NOT COMMITTED.  The application unit's deliverable.
def SideReads' {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) : Prop :=
  -- (i) SIDE — window functional at the PARENT scale (FGMN eq (13) / Thm 4.2)
  ((∀ j : ℕ, j < Nd → B j ≠ 0 →
      ν.gam ≤ (ν.e : ℤ) * ν.σ.wPrev (B j) + (j : ℤ) * (ν.h : ℤ)) ∧   -- token 1
   (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * ν.σ.wPrev (B j) + (j : ℤ) * (ν.h : ℤ) = ν.gam →   -- token 2
      ∃ k : ℕ, k ≤ ν.wSide / ν.e ∧ j = ν.s0 + ν.e * k ∧ ν.pat k ≠ 0)) ∧
  -- (ii) DIGITS — functional-equality leg at the PARENT scale
  (∀ k : ℕ, k ≤ ν.wSide / ν.e → ν.pat k ≠ 0 →
      B (ν.s0 + ν.e * k) ≠ 0 ∧
      (ν.e : ℤ) * ν.σ.wPrev (B (ν.s0 + ν.e * k))                     -- token 3
          + ((ν.s0 + ν.e * k : ℕ) : ℤ) * (ν.h : ℤ) = ν.gam ∧
      ν.σ.R (B (ν.s0 + ν.e * k)) = LaurentPolynomial.C (ν.pat k) *
        LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (B (ν.s0 + ν.e * k)))) ∧
  -- (iii) ANCHOR/ORDER — UNCHANGED (σ.R f at the GRADED stage; Thm 4.2's H_µ(g);
  --       the derivable fixed point, juncforge_clauseIII_derivable)
  (HasAnchorK (ν.σ.R (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j)) ν.a ν.Ranch ∧
   OrdPsiPoly ν.ψ ν.Ranch ν.μ) ∧
  -- (iv) DESCENT WITNESS — UNCHANGED:  LandingKey ν Φnext
  -- (v) LIFTS + ROOT NORMALIZATION — UNCHANGED
  -- (vi) VERTEX READ-OFF — UNCHANGED
  ⟨(iv)–(vi) byte-identical to SideReads, Defs.lean:300–314⟩
```

The two-scale law this encodes is the print's own (FGMN §S1): the window/digit side
lives at the parent valuation µᵢ₋₁ (values in Γᵢ₋₁), the residual side in the current
graded algebra Gr(µᵢ) — one node holds BOTH scales, glued by Thm 4.2.  At every
compiled positive instance on file (U31 base read, HK25 e = 1 seam) w = wPrev
pointwise, so `SideReads'` agrees with `SideReads` there; the two definitions diverge
exactly at genuinely graded e ≥ 2 junction frames — the locus where the old clause is
refuted (`juncforge_no_e2_junction`) and the corrected clause is numerically
satisfiable (FGMN R1/R3: the scale-sensitive window/support check GREEN at all 336
sites + the row-A record; NOT full-bundle satisfiability — that Lean construction is
exactly gate J1 below).

Primed mirrors riding the same change-set (FGMN REVISIONS 3–5, informative map):
`ReadsOf'` (the run predicate with `SideReads'` in place of `SideReads` — displayed in
§S2 since the supplier binds it), `SideClauseR1'`/`sideReads_r1'`,
`SideClauseR2'`/`sideReads_r2'`, the Window/Locality σ.w-restatement twins, the
(†)/hdag transfer layer re-derivations, and the glue route: `TruncRunFrom'`
(TruncRunFrom binds `SideReads` by name at its [T-5] interior clause,
TruncatedRun.lean:230 — verified this unit), `GlueJunction'`, `readsOf_glue'`,
`FTiedTruncLanding'`/`ftie_extends'`.  The
change-set's completeness is adjudicated ON THE DIFF at the Asvin gate (REVISION-9
cut); this note prices only the proof work AFTER that diff lands.

## S2. The corrected supplier interface (DISPLAY — verbatim-typed, not committed)

The run predicate mirror first (the supplier binds it; `ReadsOf` is in the FGMN
REVISION-6 pinned intermediary set):

```lean
-- DISPLAY ONLY — NOT COMMITTED
def ReadsOf' (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (f : Polynomial ℤ_[p]) (H : History p F) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ HistoryCoherent H ∧
  ∀ (i : ℕ) (hi : i < H.nodes.length),
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
      IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd ∧
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      SideReads' (H.nodes[i]'hi) B Nd Φnext
```

**The supplier, re-keyed** — textually the compiled `DIterJunctionSupplier`
(GlueRun.lean:875–884) with exactly three name substitutions (`ReadsOf` → `ReadsOf'`,
`SideReads` → `SideReads'` twice); antecedent shape, the `σ₁.Φ.natDegree < n`
depth guard, and the conclusion's ∃-shape stay verbatim:

```lean
-- DISPLAY ONLY — NOT COMMITTED.  Named open: stated, NEVER asserted.
def DIterJunctionSupplier' (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] :
    Prop :=
  ∀ (n : ℕ) (f : Polynomial ℤ_[p]) (σ₁ : Stage p F) (H₁ : History p F),
    ReadsOf' p F n f H₁ →
    (∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      IsDevelopment H₁.lastNode.σ.Φ f B Nd ∧ SideReads' H₁.lastNode B Nd σ₁.Φ) →
    σ₁.Φ.natDegree < n →
    ∃ (ν : Node p F), ν.σ = σ₁ ∧ ν.species = ReadSpecies.root ∧
      ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
        IsDevelopment σ₁.Φ f B Nd ∧ SideReads' ν B Nd Φnext
```

**The docstring fence carries over verbatim** (the compiled supplier's ITER-LAW fence,
GlueRun.lean:852–874, re-pointed at the primed name): any discharge computes f's deep
digits through the iterated development — a computation in the order-2 COMPOSITE digit
algebra 𝒟₂ of gr(w₂), whose measured law is the TWO-CONSTANT (ITER-LAW) with the
fibration term; the single-constant cyclic presentation is ADJUDICATED FALSE (22/28,
kill-shot row N) and fenced OUT.  The corrected clause changes the supplier's
DISCHARGE LANDSCAPE (FGMN §S6, accepted content), not its obligations.

**The discharge shape (ITER-LAW as the displayed hypothesis — DITER §S3 rule).**  Any
GENERAL discharge theorem must take the form

```lean
-- DISPLAY of the SHAPE only — the binder discipline (how carrier data D attaches to
-- the junction stage σ₁ and the tower reads of H₁) is an E-phase design decision,
-- flagged for statement review; no complete Lean statement is claimed here.
theorem dIterJunctionSupplier'_of_iterLaw
    (hcarrier : ⟨each order-2 junction fiber carries canonical 𝒟₂ data D per §S3⟩)
    (hIter    : ⟨IterLaw holds on each such D — the OPEN LEMMA, DITER §S2⟩) :
    DIterJunctionSupplier' p F
```

— the conditionality NAMES (ITER-LAW) explicitly; asserting the supplier without it
(or through a cyclic-form carrier) is fenced out.  The FIRST compiled discharge
instance (gate J3a below) is at row A, where e₀ = 1: the cocycle degenerates to the
theorem-backed D-REAL leg, so that instance is ITER-LAW-FREE with the degeneration
displayed (FGMN §S6.2, accepted content).

## S3. The 𝒟₂ carrier interface (DISPLAY — the §S3-obligation layer the sanity gates live on)

No order-2 composite digit algebra exists in the Lean corpus today; the sanity gates
need this definitional layer first (priced in §S5).  Lean-ready display, transcribing
DITER_RESTATE §S2 — every definition below is a NEW-statement site and carries the
trust-boundary flag (definitions are where errors hide; each is review-owed at
E-phase against the probe harness's exact conventions):

```lean
-- DISPLAY ONLY — NOT COMMITTED
/-- 𝒟₂ carrier data on the canonical (dig-consumed) anchor alphabet.  Indexing is
ℤ/E₂ FIBRED: outer s₂-track mod e₁, inner s₁-track mod e₀ (the iterated eq-(12-int)
split) — NEVER a single-constant cyclic F′[u′]/(u′^{E₂} − ζ′) carrier (the 22/28
byte-frozen refutation, DITER_RESTATE §S1).  [E-phase spelling flags: ℤ-indexing
with E₂-periodicity vs ZMod E₂; units vs field carrier; the s₁/s₂ tracks must be
DERIVED from eq12 data, not free fields, when the gr(w₂) tie lands.] -/
structure DIterCarrier (K₂ : Type u) [Field K₂] where
  e₀ e₁ : ℕ
  he₀ : 0 < e₀
  he₁ : 0 < e₁
  hE₂ : 1 < e₀ * e₁                 -- composite stage: E₂ > 1
  z₁ zbar : K₂ˣ                     -- INNER constant (frame letter) / OUTER constant (last-read wrap)
  ℓ₀ : ℕ                            -- normalized Bézout inverse (0 ≤ ℓ₀ < e₀, ℓ₀h₀ ≡ 1 [e₀])
  hℓ₀ : ℓ₀ < e₀
  γ₂ : ℕ                            -- level-2 abscissa-step generator weight e₁·w₁(Φ₁) + h₁
  s₁ s₂ : ℤ → ℕ                     -- the fibred digit tracks (iterated eq-(12-int) split)
  hs₁ : ∀ γ, s₁ γ < e₀
  hs₂ : ∀ γ, s₂ γ < e₁
  hper : ∀ γ, s₁ (γ + (e₀ * e₁ : ℤ)) = s₁ γ ∧ s₂ (γ + (e₀ * e₁ : ℤ)) = s₂ γ

/-- δ₂ — the OUTER carry. -/
def DIterCarrier.δ₂ (D : DIterCarrier K₂) (γ γ' : ℤ) : ℕ := (D.s₂ γ + D.s₂ γ') / D.e₁

/-- The B1 INTEGRALITY clause (probe row B1, sealed): the inner exponent is exact. -/
def DIterCarrier.InnerIntegral (D : DIterCarrier K₂) : Prop :=
  ∀ γ γ', (D.e₀ : ℤ) ∣
    ((D.s₁ γ : ℤ) + D.s₁ γ' - D.s₁ (γ + γ') + D.ℓ₀ * D.γ₂ * D.δ₂ γ γ')

/-- (ITER-LAW) as the carrier's cocycle law — THE OPEN LEMMA (DITER_RESTATE §S2;
0/804 instance-true; e₀ = 1 leg theorem-backed by Lemma D-REAL).  BOTH constants AND
the fibration term ℓ₀γ₂δ₂; the §S2 degenerations are the only collapses. -/
def IterLaw (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ) : Prop :=
  ∀ γ γ', c γ γ' = D.zbar ^ (D.δ₂ γ γ') *
    D.z₁ ^ (((D.s₁ γ : ℤ) + D.s₁ γ' - D.s₁ (γ + γ') + D.ℓ₀ * D.γ₂ * D.δ₂ γ γ') / D.e₀)
```

**The missing tie (displayed open, NOT priced as a gate):** the clause binding `c` to
the ACTUAL degree-0 composite digit algebra of gr(w₂) — anchor monomials
φ_γ = π^{u₁}Φ₀^{s₁}Φ₁^{s₂}, class values val(φ) = (R_{2,w₂(φ)}(φ))(y ↦ z̄) ∈ K₂,
c(γ,γ′) = val(φ_γ·φ_{γ′})/val(φ_{γ+γ′}) — requires an order-2 graded-carrier layer
(R₂/w₂ at composite stages) that the corpus does not have; it is the deep-wild
order ≥ 2 classifier obligation (PROJECT_STATE standing obligation 2), OUT OF SCOPE
here and displayed so no gate silently pretends to it.  The carrier above is the
INTERFACE layer: strong enough to state the three sanity gates and the ITER-LAW
hypothesis, honest that the gr(w₂) semantics is a separate open layer.

**The cyclic fence (standing negative obligation on every gate):** no discharge,
gate, or instance may present the composite-stage carrier as `F′[u′]/(u′^{E₂} − ζ′)`
with a single structure constant on the canonical alphabet — refuted at nature
(NOT-CYCLIC at 22/28 mixed towers; the 22 exact tables are the JSON falsifier
record).  Survivors: the e_b = 1/E_i = 1 stratum (D-REAL's proved scope) and the
information-free abstract crossed-product iso — neither licenses a cyclic kernel.

## S4. THE JUNCTION GATES against the corrected clause (each: display + honest gating + old-clause status + price)

Shared row-A data (all compiled TODAY, byte-frozen in `JuncForge.lean` §1 and
reusable as-is): `fA = X² + 4X + 28`, `Φ1A = X + 2`, `Φ2A = X² + 4X + 12` over ℤ₂;
`BA` the deep development fA = 24 + Φ1A² (`fA_eq`/`BA_dev`, Nd = 3).  The row-A
record (FGMN §S4, THE ROW-A SOURCE VERDICT):
(e,h,gam,s0,wSide,pat,μ,vtx) = (2,3,6,0,2,(1,1),1,1); corrected functional at slots
{0,2} = {2·3+0, 0+2·3} = {6,6} = gam.  The junction-stage pin bundle
(`juncforge_clauseIII_derivable`'s hypotheses — the S1 §S5 open construction):

```lean
-- DISPLAY ONLY — NOT COMMITTED
/-- The row-A (2,3)-graded junction-stage pins. -/
def RowAJunctionStage (σ : Stage 2 F4) : Prop :=
  σ.Φ = JuncForge.Φ1A ∧ σ.h = 3 ∧ σ.s = -1 ∧ σ.t = 1 ∧
  σ.wPrev (Polynomial.C 24) = 3 ∧ σ.w (Polynomial.C 24) = 6
```

### GATE J1 — the row-A e ≥ 2 recording (the C-e escapee, compiled at last)

```lean
-- DISPLAY ONLY — NOT COMMITTED
theorem gateJ1_rowA_e2_recording :
    ∃ (σ₁A : Stage 2 F4), RowAJunctionStage σ₁A ∧
      ∃ (ν₁A : Node 2 F4), ν₁A.σ = σ₁A ∧
        ν₁A.e = 2 ∧ ν₁A.h = 3 ∧ ν₁A.gam = 6 ∧ ν₁A.s0 = 0 ∧ ν₁A.wSide = 2 ∧
        ν₁A.μ = 1 ∧
        SideReads' ν₁A JuncForge.BA 3 JuncForge.Φ2A
```

The first genuinely graded e ≥ 2 junction recording, landing Φ₂A.  Content: build
the (2,3)-graded stage (the open construction), then discharge all six `SideReads'`
clauses at the BA development — clauses (i)/(ii) are the corrected-scale arithmetic
(numerically pre-verified: FGMN R1/R3, 336 sites + the row-A record); clause (iii)
is `juncforge_clauseIII_derivable` re-run against the primed definition (expected
verbatim — the diff never touches clause (iii)); clauses (iv)–(vi) need the landing
witness for Φ₂A, the lift/root normalization, and the vertex read-off at μ = 1
(vtx = 1) — the residual risk sits in (vi).
**BLOCKED-ON-APPLICATION** (banner §S0).  **Old-clause status: FALSE, byte-frozen**
— `juncforge_no_e2_junction` forces ν.e = 1 at this fiber (char-free, any Φnext)
and `juncforge_deep_wall_F4` refutes the Φ₂A landing outright; those theorems keep
saying exactly that forever (they bind `SideReads`, not `SideReads'`).
**Price: M.**

### GATE J2 — the corrected junction packet + glue fire at a NON-degenerate seam

```lean
-- DISPLAY ONLY — NOT COMMITTED
theorem gateJ2_rowA_glue :
    ∃ (σ₁A : Stage 2 F4), RowAJunctionStage σ₁A ∧
      ∃ (H₁A H₂A : History 2 F4),
        ReadsOf' 2 F4 2 JuncForge.fA H₁A ∧
        TruncRunFrom' σ₁A JuncForge.fA H₂A ∧
        ∃ hJ : GlueJunction' JuncForge.fA H₁A H₂A H₂A.headNode.species,
          -- junc_bundle' DISCHARGED CONCRETELY (no hypothesis) — deviation D-1's
          -- wall crossed at a genuinely deep frame, NOT hypothesized as in
          -- gate_glue_junction; the glued run then compiles via readsOf_glue'.
          True
```

The first NON-VACUOUS glue instance: unlike the compiled `gate_glue_conditional`
(whose seam is D0-degenerate, f = key, `hbundle` UNSATISFIABLE under EITHER scale —
FGMN §S5 D0 row: eq (14) is the source's own degeneracy, NOT resurrected by the
re-key), this gate sits at the row-A seam where the classificand fA is genuinely
deeper than the junction key.  Needs: a compiled full `ReadsOf'` run for fA reaching
σ₁A (a U31-scale tower unit — fA's base read, landing Φ1A... then the junction), the
continuation history, every `GlueJunction'` structural leg, and J1's recording as
the `junc_bundle'` field.  **BLOCKED-ON-APPLICATION.**  **Old-clause status:
REFUTED/VACUOUS, byte-frozen** — the 3-conjunct core is false at every such
continuation (`juncforge_junc_bundle_false`, char-2 + interior Φ₂A pin), and the one
compiled old-clause gate pair stays vacuous at its RCW seam
(`juncforge_D0_instanceFalse`/`juncforge_gate_hbundle_false`/
`juncforge_gluePacket_false`).  **Price: L.**

### GATE J3a — the supplier's conclusion instantiated at row A (ITER-LAW-FREE)

```lean
-- DISPLAY ONLY — NOT COMMITTED
theorem gateJ3a_rowA_supplier_instance :
    ∃ (σ₁A : Stage 2 F4), RowAJunctionStage σ₁A ∧
      ∃ (ν : Node 2 F4), ν.σ = σ₁A ∧ ν.species = ReadSpecies.root ∧
        ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ) (Φnext : Polynomial ℤ_[2]),
          IsDevelopment σ₁A.Φ JuncForge.fA B Nd ∧ SideReads' ν B Nd Φnext
```

Exactly the ∃-shape of `DIterJunctionSupplier'`'s conclusion at the row-A input —
the supplier's first inhabited instance (root-specied node, per the H₂rc/respec
pattern).  Rides J1 (take ν = ν₁A root-respecied, B = BA, Φnext = Φ2A).  DITER §S3
honest scope: row A has e₀ = 1, so the digit-algebra content degenerates to the
theorem-backed D-REAL leg — this instance consumes NO (ITER-LAW), and its display
must SAY so (the degeneration displayed, not hidden).  **BLOCKED-ON-APPLICATION.**
**Old-clause status: unprovable at any e ≥ 2 recording (J1's wall); the supplier
itself was never refuted (its Φnext is existential — JUNCFORGE_S2 §S2(c)), it was
undischargeable at genuinely graded frames.**  **Price: M (mostly shared with J1).**

### GATE J3b — the GENERAL supplier discharge (stays the named open; shape only)

The §S2 discharge shape (`dIterJunctionSupplier'_of_iterLaw`): ITER-LAW enters as
the displayed hypothesis on §S3 carrier data; the proof computes an arbitrary deep
classificand's digits through the iterated development IN 𝒟₂.  NOT statable-complete
today: the gr(w₂) tie layer (§S3, "the missing tie") does not exist in the corpus,
and (ITER-LAW) is an open lemma.  This gate is displayed to fence the obligation —
it is NOT part of the S/M/L queue below beyond its prerequisite line.
**BLOCKED-ON-APPLICATION + BLOCKED-ON-CARRIER-TIE + CONDITIONAL-ON-ITER-LAW.**
**Price: L, AFTER the M-priced tie layer AND the ITER-LAW unit (queue #6) — no
agent should be assigned this gate without both.**

**[CROSS-REFERENCE BRACKET (2026-08-08, wallclock 2026-08-03; applied at ROOT
r35; ADDITIVE): the ITER-LAW unit (queue #6) has since EXECUTED — (ITER-LAW)
is PROVED AT ATTEMPT GRADE on the harness tower class (standard-lift towers,
the class DITER_RESTATE §S2 pins; note `ITERLAW_2026-08-08.md`; seal ab7c31c,
run 242ba1e ALL GREEN FIRST PASS). J3b's CONDITIONAL-ON-ITER-LAW leg MAY now
cite ITER-LAW proved-on-class instead of a bare displayed hypothesis,
PROVIDED (a) the instance is standard-lift (all compiled ones are), (b) the
citation says ATTEMPT GRADE — acceptance counter 0, hostile passes in
flight, NOT accepted — and (c) the (ITER-LAW-LIFT) residual (general lawful
lifts, open exactly at g₀ = 1 ∧ δ₁ = 1) is displayed wherever a non-standard
lift could enter. The BLOCKED-ON-APPLICATION and BLOCKED-ON-CARRIER-TIE legs
are UNCHANGED — the gate still does not fire.]**

**[SECOND CROSS-REFERENCE BRACKET (2026-08-03; applied at ROOT r36;
ADDITIVE): (ITER-LAW) is now **ACCEPTED** — the hostile-pass arc closed at
the 2-clean model-diverse bar (PC1 NOT-CLEAN 1C/1G acc955a → PE1 CLEAN
64ac340 → errata round 1 7566ccd: S0 scope erratum + COR-4 mixed-block
supplement 18,396/0, sealed falsifier md5-untouched → PC2 CLEAN 804b88a +
PE2 CLEAN c40a1da; adjudicated 33373cb). J3b's CONDITIONAL-ON-ITER-LAW leg
MAY now cite **ITER-LAW ACCEPTED-on-class** — superseding clause (b) of the
bracket above (no longer attempt grade / counter 0). Clauses (a) and (c)
STAND: (a) the instance must be standard-lift (all compiled ones are), and
(c) the (ITER-LAW-LIFT) residual (open exactly at g₀ = 1 ∧ δ₁ = 1) is
displayed wherever a non-standard lift could enter; SCOPE AS ACCEPTED: the
harness tower class (standard-lift; a STRICT SUPERSET of DITER_RESTATE
§S2's pinned E₂ = e₀e₁ > 1 setting; coincides with the §S2 display on the
nose restricted to E₂ > 1; the E₂ = 1 leg a harmless COR-3-covered
extension outside the statement of record); the third residual (the gr(w₂)
semantics wrapper rides the accepted GRB retarget consumer-side) is exactly
this note's §S3 "missing tie" — still MISSING. The BLOCKED-ON-APPLICATION
and BLOCKED-ON-CARRIER-TIE legs are UNCHANGED; the gate still does not
fire; the Asvin application gate (P0) stands.]**

### GATES JS1–JS3 — the three DITER §S3 sanity gates (any discharge instance must reproduce them)

```lean
-- DISPLAY ONLY — NOT COMMITTED
-- JS1 (B0a): the 2-cocycle (associativity) identity.
theorem gateJS1_cocycle_assoc (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ)
    (hLaw : IterLaw D c) (hInt : D.InnerIntegral) :
    ∀ γ γ' γ'', c γ γ' * c (γ + γ') γ'' = c γ' γ'' * c γ (γ' + γ'')

-- JS2: the D-REAL degeneration at e₀ = 1 (the theorem-backed leg; ℓ₀ < e₀ = 1
-- forces ℓ₀ = 0 and s₁ ≡ 0, so the inner factor is trivial).
theorem gateJS2_dreal_degeneration (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ)
    (hLaw : IterLaw D c) (he₀ : D.e₀ = 1) :
    ∀ γ γ', c γ γ' = D.zbar ^ (D.δ₂ γ γ')

-- JS3: NOT-CYCLIC on the row-N value pattern — the compiled falsifier target.
-- RowNPattern: K₂ = K₁[z̄] a genuine degree-2 extension, cocycle value set
-- {z₁, z̄, z̄·z₁^b}; CyclicPresentation: a single non-1 value ζ′ whose positions
-- are the carry pattern of SOME relabeling of ℤ/E₂ (the DITER §S1
-- operationalization).  Both defs are E-phase statement sites, review-owed
-- against the 22-table JSON record.
theorem gateJS3_rowN_not_cyclic :
    ∃ (K₂ : Type) (_ : Field K₂) (D : DIterCarrier K₂) (c : ℤ → ℤ → K₂ˣ),
      RowNPattern D c ∧ ¬ ∃ ζ' θ, CyclicPresentation D c ζ' θ
```

JS1/JS2 are theorems ABOUT the interface (provable as soon as the §S3 carrier layer
compiles — they do not need the application, but they are gates OF the supplier
program, so they carry the same banner for queue discipline; JS2's arithmetic is
definitional collapse; JS1 is the carry-bookkeeping identity, finite-checkable at
compiled instances, and in general the first lemma of any ITER-LAW proof).  JS3
compiles the kill-shot row N (2;2,1,1;2,1,2) into Lean — the falsifier that keeps
every future discharge honest: a cyclic-form kernel cannot inhabit the carrier.
**Prices: JS1 S (compiled instances; the general identity rides the ITER-LAW
unit) · JS2 S · JS3 M (the row-N table + the no-single-ζ′ argument in Lean).**

## S5. The post-application pricing table (queue #9's re-priced deliverable)

| item | what fires | prereqs | price |
|---|---|---|---|
| P0 (NOT this note's gate) | the application unit itself: `SideReads'` + primed mirrors (`ReadsOf'`, R1/R2 pairs, Window/CU1 ring, (†)/readCeil re-derivations, `TruncRunFrom'`/`GlueJunction'`/`readsOf_glue'`/`ftie_extends'`) + mandatory gate re-runs (U31 etc., expected verbatim) | the ASVIN GATE on the scratch-worktree diff | **L** |
| P1 | §S3 carrier layer (`DIterCarrier`, `δ₂`, `InnerIntegral`, `IterLaw`, `RowNPattern`, `CyclicPresentation`) — pure new Defs, no application dependency, but statement-review-owed | none (can precede application) | **M** |
| J1 | the row-A e ≥ 2 `SideReads'` recording (stage construction + 6 clauses) | P0 | **M** |
| J2 | the corrected junction packet + first non-vacuous glue fire | P0 + J1 + a compiled fA full run | **L** |
| J3a | the supplier's first inhabited instance (ITER-LAW-free, D-REAL degeneration displayed) | P0 + J1 | **M** |
| J3b | the general supplier discharge under displayed ITER-LAW | P0 + P1 + the gr(w₂) tie layer (M, out of scope here) + the ITER-LAW unit (queue #6, L) | **L** |
| JS1 | B0a cocycle identity (compiled instances) | P1 | **S** |
| JS2 | D-REAL degeneration collapse | P1 | **S** |
| JS3 | row-N NOT-CYCLIC compiled falsifier | P1 | **M** |

Recommended post-application order: P1 → JS2/JS1 → (application lands) → J1 → J3a →
JS3 → J2; J3b only after queue #6 resolves ITER-LAW and the tie layer is designed.

## S6. What this unit does NOT do

No `.lean` file touched; no proof of anything; no gate asserted.  No application of
the three-token repair (Asvin-gated; the change-set is the application unit's
deliverable per the FGMN REVISION-9 scope cut — this note's displays of `SideReads'`
and the primed mirrors are READABILITY COPIES, not the normative diff, whose
completeness is adjudicated on the actual scratch-worktree diff).  No edit to any
byte-frozen statement: `SideReads`, `DIterJunctionSupplier`, the JuncForge walls,
and the GlueRun gates keep their exact compiled meanings.  No claim that
(ITER-LAW) is proved (open lemma, 0/804 instance-true), no orders ≥ 3 claim, no
claim that the D0 seam is resurrected (it is not — either scale), no gr(w₂)
order-2 semantics claim (the tie layer is displayed as missing).  The E-phase
spelling flags in §S3/§S4 are genuine statement-review obligations: every displayed
definition is a new-statement site under the trust-boundary discipline.

— DIterJunctionSupplier STATEMENT unit, 2026-08-08 (wallclock 2026-08-03).
