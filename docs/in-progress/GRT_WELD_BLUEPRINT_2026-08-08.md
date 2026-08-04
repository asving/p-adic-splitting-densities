# GRT WELD BLUEPRINT — the semantic weld (GRT-2 = grTie proper, priced L) tying the harness model-class corpus ([IL]†/[IL3]/[ILN]†/[RMG]†/the carry-law chain) to the Okutsu–Montes classifier objects, decomposed into FOUR junction families (dictionary / tree / carry-algebra / density) and TWELVE priced lemmas — DESIGN ONLY: nothing proved, nothing discharged, no .lean touched

**Unit:** GRT WELD BLUEPRINT (Q4 campaign opener; standing directive: the weld is
THE most central open mathematics — it decides whether the model-class corpus
transfers to the actual Okutsu–Montes objects; Lean formalization of the semantic
layer waits on it). **Genre: DESIGN NOTE / BLUEPRINT.** Every displayed statement
below is a CANDIDATE under the trust boundary — a new-statement site, review-owed
before any proof unit consumes it. No proof is claimed, no gate fires, no
acceptance counter exists for this note's candidates. **Author:** Fable blueprint
unit, campaign date 2026-08-08 (wallclock 2026-08-04).

**Authority chain honored:** `docs/PROJECT_STATE.md` (standing obligation 2 = the
order-≥ 2 classifier-faithfulness territory this weld meets);
`docs/ROOT_ASSEMBLY_2026-08-02.md` §44.(ii)/§45.(vi) (the closure program: Q4 =
"the GRT weld (GRT-2 priced L)"); the wave-18 design of record
`lean/notes/openmath/GRW2_TIE_DESIGN_2026-08-08.md` (GRT-1/GRT-2/GRT-3 split at
order 2 — THIS note generalizes it to the full weld and adds the junction/risk
decomposition; nothing there is superseded, its Codex-ratified constraints all
ride); `docs/MATH_COMPLETION_TREE_2026-08-01.md` (the gap-tree homes the weld
feeds: the GD-1..GD-8 families, the IFK faces O-1..O-5, the (H1) group).

## S0. What the weld is, and the standing citations

### S0.1 The two sides

**The HARNESS side (the model class — where the corpus is proved).** The
(n+1)-read standard-lift harness class of [ILN]† S0.1: O a DVR, uniformizer π,
residue field k₀; abstract reads (e_j, h_j, g_j) with e_j, h_j, g_j ≥ 1 and
gcd(e_j, h_j) = 1; residue chain K_{j+1} = K_j[z_{j+1}]/(ψ_j), ψ_j monic
irreducible with ψ_j(0) ≠ 0; weights γ_{j+1} = e_j·w_jΦ_j + h_j (uniformizing
convention γ₁ := h₀); the STANDARD lift Φ₁ and the canonical ε-corrected lifts
Φ_{m+1} (build_Phi2/3/4 pattern, certified by REALIZE-(m)/WELL-DEF-(n)); the
mirror-recursion calculus (w_m, reads R_{m,λ}, units ε_m, the iterated
eq-(12-int) split); anchors φ_γ = π^{u₁}Φ₀^{s₁}⋯Φ_n^{s_{n+1}}, window W_{n+1},
cocycle c_{n+1}(γ,γ′) = val(φ_γφ_{γ′})/val(φ_{γ+γ′}). On this class sit: [IL]†
(ACCEPTED 2026-08-03, full package: harness tower class, standard-lift, strict
superset of DITER_RESTATE §S2's E₂ = e₀e₁ > 1 pin, on-the-nose at E₂ > 1;
residuals (ITER-LAW-LIFT) at g₀ = 1 ∧ δ₁ = 1 / gr(w₂)-wrapper rides GRB
consumer-side / orders ≥ 3 untouched); [ILN]† (ACCEPTED, the uniform recursion
c_{n+1} = z̄^δ·∏ⱼ z_j^{D_j} for all n ≥ 1, with the S7 conditionality ledger;
COR-A: unconditional-on-(RM) on T-class(n)); [RMG]† (ACCEPTED at round 7: the
four (RM-m) box clauses level-generically on T-scope(m) = d₀ = 1 ∨ (e₀ ≥ 2 ∧
eᵢ ≥ 2 below top); d₀ ≥ 2 ∧ (e₀ = 1 ∨ ∃ flat) corners FENCED); the S2.2
correction tree = [RMG]'s cell tree / E1-priority tree computing the canonical
division f·Ĉ_m = R + Q·Φ_m with the L-LINE edge quanta; and the carry-algebra
language D = F[u]/(u^e − z̄) (the pass-7 verifier-specified algebra; its ACCEPTED
realization is GRB's Lemma D-REAL at the LAST-READ layer only — see S2.3).

**The CLASSIFIER side (the real objects — what the densities are about).** The
Okutsu–Montes/GMN objects as the project states them: types of order r with
per-level data (φ_i, λ_i = h_i/e_i in lowest terms, ψ_i of degree f_i), φ-adic
developments and the MacLane/GMN valuations v_i, Newton polygons `N_i(f)` with
sides (slope, length), residual polynomials R_λ(f) over the residue tower
F_{i+1} = F_i[y]/(ψ_i). Repo formalizations/statements: `docs/HUMAN_PROOF.md`
§§8–10 (L2core per-shape cluster volumes = L4 lattice q-power × L3 residual
count × child volumes, self-loop resummed; L5fix menu; L6M4 linear system);
`lean/LeanUrat/OM/OMType.lean` (`OMType`, `ResidueTower`, `OMCell`, `shapeOf`),
`OM/NewtonPolygon.lean` (`Side`, `Side.e` = slope.den, `Side.h` = slope.num),
`OM/ResidualPolynomial.lean` (`ResidualFactorization`, `needsDescent`),
`OM/Development.lean`/`DevelopTower.lean` (φ-adic expansions), the classifier
engine (`OM/Classifier.lean`, SideReads/ReadsOf histories); ground truth
`verification/quartic_oracle.py` (PARI factorpadic (e,f)-multisets). The density
objects: `OMCountV2.omMenu n σ` / `omCount T q'` feeding the capstone
`OM.RealInstanceV2.montes_unconditional` (order-0 slice machine-checked,
σ-keyed, value 1/4 at n = 2 inert; htameFE + hExhaust conditionality per
PROJECT_STATE), and mathematically α(n,σ;p) = R_σ(p) (U-DENS, the root).

### S0.2 The weld, one sentence

**GRT-2 (the semantic weld):** the system of theorems under which every harness
quantity in S0.1's first paragraph IS (canonically, provably, with displayed
conditionality) the corresponding classifier quantity in the second — so that
[IL]†/[ILN]†/[RMG]† and the carry-law chain BECOME theorems about the
classifier's residual arithmetic at orders ≥ 2, the input the density chain
(GD families → IFK faces → L2core/L6M4 → U-DENS) is missing at exactly the
deep-wild orders. Priced **L** (ROOT §45.(vi), standing). This blueprint
decomposes L into junctions J-A..J-D and lemmas W-0..W-11.

### S0.3 Citation discipline

Every candidate below rides the FULL acceptance packages: [IL]†/[ILN]† as
pasted in S0.1 (harness tower class, standard-lift, E₂-pin relation, all three
residuals); [RMG]† with its T-scope and fenced corners; the GRB retarget
CONDITIONAL on its §0 ladder ((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN)) + the §3.3
[T] pins — none of that conditionality is removable by this note. LAW-DCX v2,
(EMPTY-(m+1)), (INV-n), (ITER-LAW-n) beyond proved rungs = conjecture-grade,
consumed NOWHERE below. PID† = attempt grade (0/2 clean), consumed nowhere
below. Nothing in this blueprint asserts any junction; it prices them.

## S1. Honest scope: what the weld does and does NOT reach

The weld's output is the harness → classifier leg ONLY. Even with GRT-2 fully
proved, splitting-density statements still require (i) the classifier →
semantic-factorization leg = the IFK faces (completion tree O-1 K-READ, O-2
K-DICT with K-DICT-OB1/OB2, O-3 K-RUN, O-5 K-HALT, composed per CU-1..CU-7)
and (ii) the density assembly (L2core/L5fix/L6M4/M1/L7, modulo the Appendix-A
citations). The weld's exact contribution to the chain: it lets the accepted
carry-law corpus discharge the (H1) graded-dictionary group's residue-structure
package — (GR-B), GD-2/GD-3's one open input at orders ≥ 2 — which gates
order-≥ 2 classifier faithfulness, which the per-shape volumes (L2core's
residual-count leg at wild orders) and the omMenu growth (PROJECT_STATE Phase B)
consume. Any claim that the weld alone yields density theorems is FALSE and
fenced here.

## S2. THE JUNCTION LIST (deliverable (a)) — four families, each with the exact candidate statement, its consumers, and its break-analysis

### S2.1 J-A — THE DICTIONARY (harness reads ↔ classifier types/slopes/residual degrees)

**(J-A) [candidate, review-owed].** For every separable monic f ∈ O[x] (O = ℤ_p
or F_p[[t]], the harness's DVR instances) and every OM type t of order r
realized on f — GMN data (φ_i, λ_i, ψ_i)_{i≤r}, λ_i = h_i/e_i > 0 in lowest
terms, f_i = deg ψ_i — the induced harness tower datum

    T(t) := ( Φ₀ := φ₁-reduction data at order 0;  reads (e_i, h_i, g_i := f_i),
              i = 1..r;  residue chain K_{i+1} := K_i[z_{i+1}]/(ψ_i) )

lies in the [ILN]† S0.1 class pin EXCEPT possibly the lift clause (which is
junction W-2, priced separately), and under it the harness operators equal the
classifier operators:

    (i)   w_m  =  the GMN/MacLane valuation v_m of the type prefix, in the
          GD-2 frame normalization (the SHEARED reading — the T-F machine
          check's 7,472 violations of the unsheared reading make the
          convention pin load-bearing);
    (ii)  R_{m,λ}  =  c·R_λ^{GMN} with c ∈ F^× slot-independent (GD-3: the
          MIN CORE ord_{ψ̂}(in f) = ord_ψ(R_λ(f)) plus the FULL slot-wise
          form where value data is consumed);
    (iii) ε_m  =  the print normalization unit of the anchored march
          ((GR-B)'s frame tie, FGMN Thm 4.2 genre);
    (iv)  the eq-(12-int) split (s_m, u_m) = the classifier's side/abscissa
          coordinates: s-digits = abscissa classes mod e_m on the realized
          side, carries δ^{pl} = side-lattice crossings (GD-8's exact-key
          polygon seam at ord ≥ 1).

Class-pin conformance notes (free or near-free): gcd(e_i, h_i) = 1 holds by
construction on the classifier side (`Side.e` = slope.den, `Side.h` =
slope.num); ψ_i(0) ≠ 0 = the GMN ψ_i ≠ y convention for continuing types;
h_i ≥ 1 = the PRINCIPAL-polygon restriction — slope-0 sides are dispatched by
Hensel/L1 at order 0 BEFORE types start (machine-checked leg of the capstone),
so the weld quantifies over principal reads only, displayed.

**Consumers:** every corpus theorem's transfer rides J-A — [ILN]†'s recursion
becomes a statement about the classifier's residual-coefficient carries; [RMG]†
becomes the correction-digit engine of the classifier's own division steps;
N-1's accepted legs (harness operators = FGMN print operators at order 2,
family-ledger scope) are J-A(i)–(iii)'s accepted partial; GD-5 (order-1
conformance, NEARLY CLOSED: VAL1/KEY1/DIV1/ROOT-M/WGEO + (D3), residue = the
S-1 transcription audit) is its order-1 layer.

**Break-analysis:** if J-A fails beyond a normalization (an operator genuinely
differing from print), the corpus survives as model-class mathematics but the
(H1) retarget path collapses: the GRB retarget's N-1 legs were the canary, so a
J-A failure contradicts an accepted result — i.e., the realistic failure mode
is SCOPE (the family-ledger perimeter of N-1 not extending), not falsity.
Restatement surface: the S0.2 calculus would need re-keying to print operators
and the value-layer proofs re-run ([IL] L4–L7, [ILN] S4).

### S2.2 J-B — THE TREE CORRESPONDENCE (the S2.2 correction tree ↔ φ-adic expansions)

**(J-B) [candidate, review-owed].** Under J-A, for every level m ≤ r:

    (i)   the harness Φ_m-development f = Σ_j A_j Φ_m^j (unique, Φ_m monic)
          IS the classifier's φ_m-adic expansion, and w_{m+1}(f) =
          min_j (e_m·w_m(A_j) + j·γ_{m+1}) computes v_{m+1} side-for-side:
          the harness window polygon = N_{m+1}(f) VERTEX-FOR-VERTEX (GD-2's
          displayed clause, T-F-tested 41,720/0);
    (ii)  the [RMG]† S2.2 cell tree (the E1-priority correction tree, with
          the L-LINE promotion-edge quanta and the 𝔷-multiplicativity
          kernel) computes the canonical division f·Ĉ_m = R + QΦ_m INSIDE
          the classifier's expansion arithmetic — each cell = a set of
          expansion slots, each edge = one classifier division step, the
          exact line quanta = the polygon's lattice geometry;
    (iii) [RMG]†'s (C-READ) clause transports: multiplying a read digit by
          the canonical correction digit shifts the CLASSIFIER's residual
          read by τ_m with the level-m EPS-carry z_m^{ε′}.

**Consumers:** [RMG]†'s transfer (via (ii)/(iii)) is what the order-≥ 2
residual-dictionary march (GR-B) needs at descent steps; the SideReads Lean
transcription (JuncForge) is the compiled shadow of (i) — and its S2 lesson
binds here: the parity wall `juncforge_no_e2_junction` killed the junc_bundle
TRANSCRIPTION, not the mathematics, so J-B must be stated against the semantic
classifier objects, never against SideReads as it stands (any SideReads repair
= statement change, ROOT authority).

**Break-analysis:** (i) failing would contradict the T-F machine check's pinned
convention — near-zero risk as stated, HIGH risk if a draft silently uses the
unsheared frame. (ii)/(iii) failing leaves [RMG]† internally true (its tree is
self-contained arithmetic) but severs the correction engine from the
classifier's division flow; the (RM-m)-conditional legs of [ILN]† would then
certify carries of a tree with no classifier meaning. Restatement surface:
none on the corpus text; total loss on the transfer claim.

### S2.3 J-C — THE CARRY-ALGEBRA REALIZATION (D and the c_T-carrier ↔ the residual towers / gr(w))

**(J-C) [candidate, review-owed; = the GRW2_TIE_DESIGN GRT-2 display generalized
to every composite stage].** Under J-A/J-B, for every level m with
E_{m+1} := e₀⋯e_m > 1:

    (i)   LAST-READ LAYER (the accepted precedent, GRB Lemma D-REAL,
          conditional on the GRB §0 ladder): the gauged (p ↦ 1) anchor
          system at the last read is K_{m+1}[u]/(u^{e_m} − z̄) — the carry
          algebra D = F[u]/(u^e − z̄) with F := K_{m+1}, abscissa-coset
          indexed. The weld consumes this as accepted, one layer at a time.
    (ii)  COMPOSITE STAGES (the open content): the fibred carrier
          (⊕_{γ ∈ ℤ/E_{m+1}} K_{m+1}·u_γ, u_γu_{γ′} = c_{m+1}(γ,γ′)u_{γ+γ′})
          built from the canonical D(T)/c_T of GRT-1 is isomorphic, via
          u_γ ↦ [φ_γ]_{TC} through the localize–gauge–quotient chain
          TC-1/TC-2/TC-3, to the K_{m+1}-span 𝒜(T) of the anchor classes in
          the degree-0 component of the actual graded ring gr(w_{m+1}) —
          with 𝒜(T)'s multiplication gr's OWN, never c_T (the tautology
          fence). THE CYCLIC FENCE IS LAW: at composite stages 𝒜(T) is NOT
          F′[u′]/(u′^{E} − ζ′) (adjudicated NOT-CYCLIC at 22/28 towers,
          value set {z₁, z̄, z̄z₁^b}, byte-frozen); only the last-read layer
          is cyclic.
    (iii) the residue chain K₀ ⊂ K₁ ⊂ … ⊂ K_{m+1} IS the classifier's
          residual tower F₀ ⊂ … ⊂ F_{m+1} (`ResidueTower`), identification
          compatible with (i)/(ii)'s scalars.

The order-2 instance of (ii) is EXACTLY the GRW2_TIE_DESIGN obligation package
OB-1..OB-6 (target exists / map well-defined / multiplicativity incl. the inner
z₁ normalization factor / rank-one independence (Thm 4.2 analogue) / tautology
fence / harness-val-equals-TC-read). This blueprint adds only: the general-m
statement shape, and the identification (iii) as its own displayed clause.

**Consumers:** DITERSUP §S3 / gate J3b (BLOCKED-ON-CARRIER-TIE — retires only
when (ii) is proved and survives its hostile arc); the compiled P1 layer
(`Scaffold/HDischarge/H1/DIterCarrier.lean`, JS1 proved with the honest hTrack
hypothesis, JS2 proved) = the harness-side carrier J-C instantiates; MOVES
B2-DEF's accepted induction gains its intended semantic home; the (H1)(a)
GR-B package's carry side.

**Break-analysis:** if (ii) fails, c_{n+1} remains a true, defined ratio of
harness reads (no corpus text falsified) but has NO ring-theoretic meaning in
the classifier; the semantic Lean layer (standing obligation 2's R₂/w₂ carrier)
becomes unbuildable as designed; J3b stays blocked permanently. The known
failure modes are already fenced: the cyclic shortcut (dead, S4 of the design
note), the MOVES B2-FINAL bridge (dead: NOT accepted, 5C/2G structural, its
faults = the OB package itself), bare-interface discharges (the option-(ii)
vacuity trap, P1-FLAG-1/J3B-FLAG-1).

### S2.4 J-D — THE DENSITY BRIDGE (which harness counting statement equals which splitting-density statement)

**(J-D) [candidate, review-owed; two legs].** The honest form — the harness
corpus proves NO density statement directly; its density content routes through
two displayed equalities:

    (J-D1) THE FAITHFULNESS HANDOFF. Under J-A/J-B/J-C, the accepted
      carry-law corpus proves the (H1) residue-structure package at orders
      ≥ 2: the anchored-march frame tie + residual dictionary ((GR-B)'s
      displayed content, both FGMN-4.2 pairings) hold at every realized
      composite stage of every classifier tower IN THE WELDED CLASS — i.e.
      GD-2/GD-3's one open input becomes a theorem there, and with it the
      GD-1 representative-admissibility and order-≥ 2 KEY1 members ((H1)
      members (b)/(d)) inherit the corpus's proofs where the dictionary
      reaches.
    (J-D2) THE COUNT EQUALITY. For every decided order-r shape T in the
      (grown) menu and prime power q: the classifier stratum count that
      L2core's per-cell coefficient consumes (the L3 residual-factorization
      count over F_r × the L4 lattice q-power) equals the model-side count
      computed from T's (e_j, h_j, g_j) data through the welded read — the
      order-0 instance IS the machine-checked capstone leg (density m σ q' =
      Σ_{T ∈ omMenu m σ} omCount T q', realF2; value 1/4 at n = 2 inert),
      and the order-≥ 1 instances are the omMenu growth obligation
      (PROJECT_STATE Phase B) stated as mathematics. The carry-law corpus
      enters (J-D2) as the no-cancellation/level-detection warrant for the
      residual reads at wild composite stages (the mechanism clause O-1's
      statement already cites: the carry-algebra spine supplies
      no-cancellation + level-detection).

**Consumers:** (J-D1) → the (H1) row (its retirement path), then the IFK faces
O-2/O-3 through the GD carriers, then CU-1..CU-7; (J-D2) → omMenu/omCount
growth, `DecidedOmCountTie` genre, `montes_unconditional_exhaustive`'s hExhaust
program, and mathematically L2core → L6M4 → U-DENS.

**Break-analysis:** if (J-D1) fails, the density campaign falls back to proving
the (H1) package directly from print (the pre-corpus position — the whole point
of the model-class detour is lost, but nothing is falsified). If (J-D2) fails
at some order-≥ 1 shape, either the menu is wrong (a Phase-B Lean matter) or a
residual count is not universal — which would contradict L3/L2core's verified
instances (empirically confirmed through OM order 4, BB3 counts exact over 8
fields); a (J-D2) failure is therefore evidence of a WELD error upstream, and
the falsifiers below are ordered to catch it there first.

## S3. THE LEMMA SET (deliverable (b)) — per-lemma pricing, dependency order, the highest-risk junction

### S3.1 The twelve lemmas

| id | statement (compressed; full quantified forms per S2) | junction | price | depends on | accepted partials |
|---|---|---|---|---|---|
| **W-0** | class-pin conformance: every realized principal-read OM type t yields T(t) satisfying every [ILN]† S0.1 clause EXCEPT the lift clause (gcd auto; ψ(0) ≠ 0; g ≥ 1; DVR base; slope-0 legs routed to Hensel/L1, displayed) | J-A | **S** | — | the class-pin conventions themselves |
| **W-1** | the operator dictionary at all orders: w_m = v_m (sheared frame), R_{m,λ} = c·R_λ^{GMN}, ε_m = the print unit — J-A(i)–(iii) | J-A | **M/L** | W-0 | N-1 (order 2, family-ledger, ACCEPTED); GD-5 order-1 layer (VAL1/KEY1/DIV1/ROOT-M/WGEO + D3, nearly closed); T-F 41,720/0 |
| **W-2** | THE LIFT JUNCTION: the classifier's canonical key polynomial at each level equals the harness canonical ε-corrected lift Φ_{m+1} — or, failing byte-equality, an explicit unit-covariance law transporting all value-layer statements across GMN-admissible representatives | J-A | **L — HIGHEST RISK (S3.2)** | W-0, W-1 | GD-1 partial (GMN Thm 2.11 SOME representative; KEY1 at degree-1 first transitions); (ITER-LAW-LIFT) fence |
| **W-3** | development identity + polygon tie: harness Φ_m-developments = φ_m-adic expansions; window polygon = N_{m+1}(f) vertex-for-vertex — J-B(i) | J-B | **M** | W-1 | GD-2 spine (OL-2(a)+(b), (V1)/(V2) verbatim at order 1; VAL1+DIV1 outright at degree-1 first transitions) |
| **W-4** | grid/side coordinates: eq-(12-int) digits = abscissa classes mod e on the realized side; plain carries = side-lattice crossings — J-A(iv) | J-A/J-B | **S** | W-3 | GD-8 order-1 proof (871 forced exact-divisibility samples, 0 findings) |
| **W-5** | correction-tree transfer: the [RMG]† S2.2 cell tree computes the classifier's division steps; (C-READ) transports as the classifier's residual-read shift — J-B(ii)/(iii) | J-B | **M** | W-1, W-3, W-4 | [RMG]† itself (the harness-side arithmetic, accepted); L-LINE/L-NORM displays |
| **W-6** | carry-target existence at composite stages: TC-1 (localize) + TC-2 (gauge p ↦ 1, grading collapse ℤ → ℤ/E) are legitimate ring-level operations at every composite stage; degree-0 component + fibred ℤ/E-indexing survive = GRT-2 OB-1 generalized | J-C | **L** | W-3 | GRB D-REAL at the last-read layer (ACCEPTED, conditional §0 ladder); COR-4's φ_{γ+E} = π·φ_γ |
| **W-7** | anchor-transport isomorphism: Ψ : (⊕ K·u_γ, c_T) ≅ 𝒜(T) — well-defined (OB-2), multiplicative incl. the INNER normalization factor (OB-3), K-linearly independent (OB-4, Thm 4.2 rank-one analogue), tautology-fenced (OB-5) | J-C | **L** | W-6, GRT-1 | CARRY-1 (outer ȳ^δ leg, last-read, ACCEPTED); GRB S6a domain-cancellation |
| **W-8** | harness-val = TC-read (OB-6): the harness calculus IS the composite graded read; the residue chain = `ResidueTower` (J-C(iii)) | J-C | **L** | W-6, W-7, W-1 | N-1's operator-level commuting diagram (NOT the carrier identification — the design note's C15 separation stands) |
| **W-9** | cocycle semantics: [ILN]†'s c_{n+1} = the classifier's graded carry cocycle; COR-2 = gr-associativity; COR-4 monodromy = the gauge period | J-C | **S** (given W-6..W-8) | W-6..W-8 | [ILN]† COR-2/COR-4 (harness side, accepted) |
| **W-10** | count equality at decided shapes: classifier stratum count (L3 × L4 leg) = model-side count from (e_j,h_j,g_j) through the welded read, order ≥ 1 — J-D2 | J-D | **M** | W-1, W-3, W-5 | the ORDER-0 instance machine-checked (realF2 capstone legs); DecidedOmCountTie genre; L3/BB3 counts exact over 8 fields |
| **W-11** | menu tie: decided order-r shapes ↔ grown omMenu entries (typeOf-keyed), hExhaust program stated as mathematics | J-D | **M** | W-10 | omMenu order-0 slice (Lean, capstone); L5fix menu finiteness (math) |
| **W-12** | the faithfulness handoff (J-D1): under W-0..W-9 the corpus proves the (H1) residue-structure package at orders ≥ 2 on the welded class — the composition display, consuming the IFK faces downstream, owning nothing of them | J-D | **S** (composition; conditional on IFK downstream) | all above | (GR-B) RE-ACCEPTED print package at its own perimeter |

Aggregate: consistent with the standing GRT-2 = **L** pricing; the S/M members
are the welds' bookkeeping shell, the four L's (W-2, W-6, W-7, W-8) are the
weld proper.

**Dependency order (execution order for successor units):**
W-0 → W-1 → {W-3 → W-4} → W-2 → W-5 → {W-6 → W-7 → W-8 → W-9} → {W-10 → W-11} → W-12,
with GRT-1 (the harness leg, S/M, application-independent — rides the compiled
P1 layer) available first and independently. W-2 is deliberately scheduled
AFTER W-1/W-3 (its falsifier needs the operator dictionary to even compare) and
BEFORE the J-C block (no point building the graded target on lifts the
classifier does not use).

### S3.2 THE HIGHEST-RISK JUNCTION: W-2, the lift junction

**Why it is the one most likely to force corpus revision.** Every value-layer
theorem in the corpus — [IL]† L6/L7, [ILN]†'s whole S4 value layer, c_{n+1}
itself, [RMG]†'s Ĉ_m (defined through ε_m-normalized realize) — is pinned to
the CANONICAL ε-corrected lifts, with (ITER-LAW-LIFT) open at g₀ = 1 ∧ δ₁ = 1
as the standing warning that lift-freedom is NOT free. The classifier
constructs its key polynomials by its own recipe (GMN Def 2.12 representatives;
the engine's `LiftKeyExt` genre). NO accepted result says these coincide: N-1
is operator-level; GD-1 gives SOME admissible representative (GMN Thm 2.11),
not THE harness one; every sealed numeric confirmation of the corpus
(35,232/0 + 89,056/0 F2c + 18,396/0 mixed + the 133k level-3 samples) ran on
HARNESS-built lifts. The weld's entire value transport crosses this seam, and
it is the ONE seam with zero direct evidence on the classifier's side of it.
If the lifts differ by a lawful-but-non-canonical correction, anchor values
change by uncontrolled units, and c_T computed on classifier lifts need not
satisfy the [ILN]† closed form as displayed.

**Failure consequence (exact):** the corpus stays internally true (proved on
its own lifts) — but its APPLICABILITY claim to the classifier fails as
stated; the (ITER-LAW-LIFT) residual effectively expands from one corner to
the whole transfer, and the weld must add a gauge/covariance layer (a genuinely
new mechanism, not priced anywhere today) or the corpus value layer must be
restated on classifier lifts and re-proved.

**The concrete falsification test (cheap, decisive, decorrelated).** A sealed
exact-arithmetic runner, prereg before run, two independent legs (the
extraction-corruption rule: no verbatim pin against a shared extraction —
one leg must be a fresh from-print transcription, NOT imported from
grb_order2_check.py):

    (T1) LIFT COMPARISON. Roster: realized order-2 and order-3 types on
      concrete f over ℤ₂/ℤ₃ (the F2c row towers + wild quartic-oracle
      shapes, e.g. the x⁴−2/ℚ₂ chain; PARI (e,f) ground truth per row).
      For each level m: construct Φ_{m+1}^{harness} (build_Phi2/3 verbatim)
      and Φ_{m+1}^{cls} (fresh GMN Def 2.12 transcription / the engine's
      key-lift step). Record byte-equality of coefficient valuations, and
      where unequal, the exact unit ratio.
    (T2) COCYCLE TRANSPORT. On every roster tower, compute c_T on the
      CLASSIFIER lifts over in-window anchor pairs (both levels' digit
      ranges covered, near-boundary u₁ = 0 rows included) and compare to
      the [ILN]† closed form z̄^δ·∏ z_j^{D_j} evaluated at the same
      (γ, γ′). PREDICTION under W-2-as-stated: 0 violations. ANY RED at
      T2 = W-2 falsified as byte-equality; the T1 unit-ratio table then
      decides whether a covariance law exists (systematic ratios) or the
      transfer is genuinely broken (unsystematic).

The test is decisive for the design decision (byte-equality vs covariance
layer) BEFORE any of the L-priced units are attempted — it should be the
first executed unit of the weld campaign.

**Runner-up risk, named:** W-7's inner normalization factor (OB-3's z₁ leg —
CARRY-1 supplies only the outer z̄^δ; the graded-side ε-identity is new
content), and W-6's composite-stage gauge legitimacy — both already displayed
as the GRW2_TIE_DESIGN obligation package with Codex-ratified pricing (L);
they are proof-hard but NOT corpus-revision risks: their failure blocks the
semantic layer without forcing any restatement of accepted texts. W-2 is the
only junction whose failure rewrites corpus-facing claims; hence it is THE
highest-risk junction.

## S4. RELATION TO THE EXISTING PARTIAL WELDS (deliverable (c))

What already exists, exactly, and what each does NOT cover:

1. **The capstone realF2 tie at order 0 (machine-checked, the deepest existing
   weld).** `OM.RealInstanceV2.montes_unconditional` through `realF2`:
   density m σ q' = Σ_{T ∈ omMenu m σ} omCount T q', σ-keyed, non-vacuous
   (1/4 at n = 2 inert; split ≠ inert at q' = 3), Lean-core footprint;
   conditionality: htameFE hypothesis + hExhaust behind
   `montes_unconditional_exhaustive`. This IS lemma W-10/W-11 at order 0.
   NOT covered: any order ≥ 1 shape (omMenu is the order-0 slice), any carry
   content (order 0 has no composite stage).
2. **N-1, the accepted harness-faithfulness legs (inside the GRB retarget):**
   harness operators = FGMN print operators at order 2, family-ledger scope —
   the accepted core of W-1 at order 2. NOT covered: the carrier
   identification (the design note's C15 separation: a commuting-diagram
   fact, not OB-6), orders ≥ 3, the lift construction (W-2).
3. **The accepted GRB retarget (conditional on its §0 ladder):** clause (0)
   Δ = K_i[ȳ], K_{i+1} = K_i[z̄]; clause (0′) + CARRY-1 (ϕ_γϕ_{γ′} =
   ϕ_{γ+γ′}·ȳ^δ in the LOCALIZED gr); Lemma D-REAL (the gauged anchor system
   at the LAST-READ layer = K_{i+1}[u]/(u^{e_i} − z̄)); S6a W-MULT with
   rank-one domain cancellation. This is W-6/W-7's accepted precedent ONE
   LEVEL DOWN — the composite-stage instances are exactly what it does not
   supply (the design note's C16: "D-REAL one level up" is the theorem, not
   an input).
4. **GRT-1 + the compiled P1 layer:** the harness leg (canonical D(T),
   totalized c_T, IterLaw as theorem) designed S/M, application-independent;
   `Scaffold/HDischarge/H1/DIterCarrier.lean` compiled; JS1 PROVED with the
   honest hTrack hypothesis (bare display false, compiled countermodel), JS2
   PROVED. NOT covered: everything semantic (GRT-1 makes NO gr claim by
   construction).
5. **The H7 forge line (the compiled-instance frontier):**
   - `H7Forge.lean` (wave 16): the FIRST non-vacuous compiled (H7) decision
     instance — five-site depth-1 TreeModel at (p,n,N,m) = (2,2,2,4), both
     rfl-degeneracies broken, slope-keyed KLoc proved + pooled form refuted
     (compiled twin of the N-H7-1 pin 1), first contentful KLocCounts.
   - `H7ForgeDepth2.lean` (wave 18): the depth-2 transplant REFUTED AT THE
     BOX — (2, ZMod 2) prime-field ambient forces g = 1 at every node, no
     2-node chain realizable; F4 relocation required; (H7) stays [M].
   - `JuncForge.lean` S1/S2: the first compiled e ≥ 2 junction attempt
     ADJUDICATED junc_bundle INSTANCE-FALSE at row A (the parity wall:
     SideReads' clause structure cannot host an e = 2 junction as
     transcribed); D0 confirmed vacuous at its compiled instance.
   LESSONS BOUND INTO THIS BLUEPRINT: compiled welds die on
   transcription-level walls, not mathematics — so the junctions J-A..J-D are
   stated against SEMANTIC classifier objects, and no W-lemma consumes
   SideReads/TreeModel as-is; ambient-field expressiveness (the ZMod 2 g = 1
   wall) must be checked at roster-design time in every falsifier (T1/T2
   rosters run over towers with genuine g ≥ 2 levels, over F4-capable
   ambients).
6. **MOVES:** §B2-DEF ACCEPTED (the bottom-up tower induction — a harness-side
   asset the weld will eventually give semantic meaning); §B2-FINAL NOT
   accepted (5C/2G structural) and its language is a DEAD END for the weld
   (the GRW2_TIE_DESIGN S4(1) refutation stands: its four faulted points ARE
   the OB package).
7. **GD-5 (order-1 conformance, nearly closed)** + KEY1/VAL1/DIV1 at degree-1
   first transitions + the T-F/GD-8 machine checks: the order-1 floor of
   W-1/W-3/W-4 — the weld's induction base is largely in hand; the content
   of the weld is orders ≥ 2.

## S5. REVISION-RISK ASSESSMENT (deliverable (d)) — per junction: if it fails AS STATED, what corpus surface restates

| junction | failure mode | corpus surface needing restatement | severity |
|---|---|---|---|
| J-A / W-1 | an operator genuinely ≠ print beyond normalization | would CONTRADICT accepted N-1 (order 2) — realistic mode is scope-failure at orders ≥ 3 only: then the S0.2 calculus needs re-keying to print operators at high orders and the [ILN]† S4 value layer re-runs there; rungs ≤ 2 texts stand | MODERATE (bounded by N-1's acceptance) |
| J-A / W-2 | classifier key lifts ≠ canonical lifts, NO systematic covariance | NO accepted text falsified (all are proved on their own lifts) — but every value-layer APPLICABILITY claim restates: (ITER-LAW-LIFT)-style residual expands to the whole transfer; a new gauge/covariance mechanism becomes mandatory before any semantic consumption; GRT-3/J3b feed shape changes | **HIGHEST for the campaign** (the weld is the campaign; zero for internal corpus truth) |
| J-B / W-3 | development/polygon tie fails | would contradict the T-F 41,720/0-checked sheared convention — near-nil as stated; the live risk is DRAFT error (unsheared frame), caught at statement review | LOW |
| J-B / W-5 | correction tree ≠ classifier division flow | [RMG]† stands internally; its transfer claim dies; (RM-m)-conditional rungs of [ILN]† lose classifier meaning; the (H1) march loses its descent-step engine | HIGH for transfer, NIL for texts |
| J-C / W-6..W-9 | composite-stage graded target illegitimate / iso fails / val ≠ TC-read | none — the corpus never asserted the semantics (residual (ii) was always displayed); J3b stays BLOCKED-ON-CARRIER-TIE permanently; standing obligation 2's Lean layer unbuildable as designed; the fibred-carrier DESIGN would need a new target | HIGH for the program, NIL for texts |
| J-D / W-10..W-12 | count equality fails at some order-≥ 1 shape | evidence of an upstream weld error (L3/L2core instances are verified through OM order 4) — diagnose upstream first; if genuinely the menu: a Phase-B Lean matter, no corpus text | LOW direct; diagnostic value HIGH |
| (cross-cutting) | [RMG]† T-scope fence vs REAL towers | NOT a failure but a standing GAP this blueprint surfaces: classifier towers with intermediate flat reads (e_i = 1, residue-degree-only growth) are COMMON real objects, and they sit exactly in [RMG]†'s fenced d₀ ≥ 2 ∧ ∃-flat corners; on those towers the welded transfer of the (RM-m)-conditional legs does not fire until the Q3 corner units land. The weld makes the Q3 corners MANDATORY for full coverage, not optional polish | — (scope, not risk) |

## S6. What this unit does NOT do, and the recommended order

No `.lean` touched; no junction asserted; no gate fired; no statement edited;
no acceptance arc opened; BLOCKED-ON-CARRIER-TIE and BLOCKED-ON-APPLICATION
(the Asvin P0 gate) both stand; the GRW2_TIE_DESIGN note remains the design of
record at order 2 — this blueprint layers the campaign decomposition over it
without superseding one line. Conjecture-grade material (LAW-DCX v2, INV-n,
orders-≥ 3 templates beyond proved rungs) consumed nowhere.

**Recommended execution order:** (1) the W-2 falsification runner T1/T2
(sealed, prereg, decorrelated legs) — decides byte-equality vs covariance
BEFORE any L unit; (2) GRT-1 with P1 (S/M, independent); (3) W-0/W-1/W-3/W-4
as one dictionary unit (M, hostile-pass bar), riding N-1/GD-5; (4) W-2 proper
per the runner's verdict (L); (5) W-5 (M); (6) the J-C block W-6→W-9 as the
dedicated GRT-2 math unit (L, the design note's OB package, hostile-pass bar);
(7) W-10/W-11 with the omMenu Phase-B growth; (8) W-12 as a composition
display at the (H1) row. Every unit's statements are review-owed at E-phase
against the harness's exact conventions before any Lean landing.

— GRT WELD BLUEPRINT unit, campaign date 2026-08-08 (wallclock 2026-08-04).
