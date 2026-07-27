# MovesR FINAL CONFIRMATION (rev 4, re-architecture) — Codex audit, 2026-07-28
Verdict: REJECT (15 crit / 2 gap). Full transcript below (note: model emitted the final numbered findings block twice; content identical both times).

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa418-8295-7f43-8f90-9e3dee7ec438
--------
user

You are the semantic auditor for a Lean formalization blueprint. You verify
FAITHFULNESS of proposed Lean statements to a frozen mathematical note; you fix
nothing. Quote each offending unit spec and classify: CRITICAL (the Lean
statement says something different from, weaker than, stronger than, or vacuously
satisfiable relative to the note's display) vs GAP (ambiguity, missing
hypothesis-field, underspecified Defs dependency). Then give counts and a verdict
line 'ACCEPT' or 'REJECT (n crit / m gap)'.

Check EVERY unit spec for, in one pass:
1. FAITHFULNESS: the `statement` field says exactly what the quoted `moves_ref`
   display says — same quantifier order, same side conditions, same edge cases
   (empty menus, m = 1, N = 0, the (BDY) conventions).
2. NON-VACUITY: no statement satisfiable by an empty/degenerate instance of its
   own hypothesis structures (the trap that killed the pre-rebase chain — check
   each structure has an inhabitation story or an explicit instance unit).
3. HYPOTHESIS FIDELITY: every open kernel the note attaches to a claim appears in
   `hypothesis_fields` — never silently dropped, never silently strengthened into
   a definition, never smuggled into an axiom (the axiom policy allows PUBLISHED
   statements only).
4. DEFS SOUNDNESS: the proposed Defs skeleton — no definition that secretly
   decides an open question (a def that computes what the note only hypothesizes
   exists); typing plausible in Lean 4 + Mathlib.
5. DECOMPOSITION: units genuinely short (one display each); flag any unit whose
   sketch cannot fit its statement (a hidden multi-lemma unit).

The note text is the sole ground truth. Do not trust the blueprint's prose
summaries of the note; check against the quoted displays and the pasted note.
Write NOTHING to disk. Output: the numbered findings, counts, verdict.
This is the FINAL CONFIRMATION on REV 4, a RE-ARCHITECTURE. History: your rev-1 audit (15/6), an independent 2/5, your rev-3 final (15/5) vs an independent 0/0 — the split was systematic (you read the blueprint's fences as dropped content; the other auditor read them as declared pointers). The orchestrator adjudicated: the fences are now GONE — MovesR is parameterized by a CInterface: a GradedCarrier (abstract Coeff/graded pieces/K1-chain weight w/initial-form map inγ + laws) and eleven one-display §C statement definitions (LSTStmt carries chain-weight typing AND the inγ/level-set content in full), with REL.1 = the CStatements record at base δ — a typed mutatis-mutandis pointer whose instantiation is HC-1's declared deliverable. This resolves your CF6/CF7/CF16 class by construction. The other 17 of your rev-3 findings were folded as repairs (triage table in the blueprint). VERIFY: (a) each of the eleven statement defs against its §C source display — especially LSTStmt against Lemma LST (all three clauses incl. chain-weight typing and inγ level-set dependence) and DOMStmt/TYPStmt; (b) the GradedCarrier laws suffice to TYPE those statements (no residual fence, no smuggled strength); (c) your 17 folded findings are genuinely repaired; (d) statements-only vacuity: a Prop trivially true regardless of subject is a critical. Sweep end to end. A clean pass = ACCEPTED (the corpus otherwise PARKS until wave 4).

THE FROZEN NOTE (ground truth):
## §R-LEDGER — the relative ledger under base change (assembly note 5, = plan [2r])

*(2026-07-27. Assembly note [2r] per ASSEMBLY_PLAN_2026-07-26.md §3r (REV 3:
the REL.2 obligation family — the plan counts four; FIVE named
obligations (a)–(e) since rev 2 added (e), this note's convention
throughout — and the decision-independent gate REL-n4; REV 9:
obligation (c) re-homed to [3t]'s (SIB), one owner). Consumes: the
DUAL-ACCEPTED §C (rev 14 — Theorem C, C.0/C.0.5, C.1, C.1.5/(ZC), LST, TYP,
DOM, C.3) and the DUAL-ACCEPTED §B2-DEF (rev D¹¹d — the D.0 stage tower,
D.3(e), D.11) as the TEXTS TO BE RE-SCOPED — nothing here re-proves them;
the dual-accepted §T-ASSEMBLY §T.3, whose (SIB) statement's O_δ quantifier
is consumed FROM this note at acceptance (its record lists [2r] as a
standing blocker); [2a] §M-SPECIES for the species alphabet. Consumed by:
[3t]-COND (the plan's acceptance event "[3t]-COND after [1] and [2r]"),
PCI's O_{δ_j}-identification leg, [3]'s b_e^split and RS.1-SH mixed legs
β_{e_j,·}(q^{δ_j}), [4] SQ.2 through REL.3, and §V-TABLES' conditionality
record. SCOPE FENCE: everything below is statement + obligation bookkeeping
+ gate spec — NO obligation of this note is discharged in this draft. The
plan's kernel (REL.1's derivation-grade re-scoping pass, fresh context,
accepted §C text in hand) has NOT been run, and "by inspection" is claimed
nowhere (risk R6's REV-2 clause). The XRB height-elimination package is
SEPARATE (plan REV 13, owner [3] as RS.0(β)/CL-9): nothing height-related
is owed or supplied here.)*

**Why this note exists (the plan's C6 finding).** The accepted Theorem C is
stated for monic f over ℤ_p. RESUM's mixed legs and SQUEEZE's domination
induction consume β_m(q^δ) — cluster laws over the unramified degree-δ
extension — and (SIB)'s per-sibling factors are continuation theories "over
O_{δ_j}". The ALGEBRA q ↦ q^δ was never the problem (it preserves ℚ(q);
plan §8's non-failure list). What is MISSING is the MEASURE statement:
nothing certified says the sub-cluster continuation IS the MOVES measure
theory over O_δ. This note states that ledger — the re-based objects, the
five REL.2 obligations (a)–(e), the (SIB)-quantifier deliverable, the
REL.3 transfer, and the sealed gate — every clause fenced open until its
pass lands.

### R.0 The base-change setting (= plan REL.1's scope), one object at a time

Fix δ ≥ 1. O_δ := W(F_{p^δ}), the unramified extension of ℤ_p of degree δ;
residue field F_δ := F_{p^δ}; q_δ := p^δ = |F_δ|. The uniformizer is STILL
p — unramified base change leaves the AMBIENT v_p-scale untouched (value
group ℤ, levels counted in powers of p); MOVES height bookkeeping (side
heights, stretches, κ_r) is NOT asserted here — (R0-tower)'s PREDICTED
bracket below governs it (rev 4, Fable-pass Finding 2); δ = 1 is the
accepted theory verbatim. Under ⊗O_δ:

 (R0-box) THE BOX. Monic degree-n f ∈ O_δ[x]; coefficient box O_δ^n with
   normalized Haar measure vol_{O_δ}(O_δ^n) = 1. A base coordinate (ℓ, i)
   (C.0's global order, unchanged) now carries an O_δ-DIGIT — one
   F_δ-valued coordinate, the ATOM of the relative ledger (no statement
   below unpacks it into its δ F_p-components; C.0's BLOCK CONVENTION
   unpacks tower F-digits into BASE digits, and over O_δ "base digit"
   means F_δ-valued). Level-N counting: f mod p^N ranges over q_δ^{nN}
   residue points — Theorem C(b)'s normalization p^{nN} reads q_δ^{nN}.

 (R0-tower) THE CLASSIFIER TOWER (§B2-DEF D.0's stage data, re-based).
   A = O_δ[x]; a stage σ = (w, Φ, C, U, T, F, z) under the SAME axioms
   (S1)–(S6). The base residue field is F₁ := F_δ[x]/(φ̄) — §A's
   F_Q = F_p[x]/(φ̄) with F_p replaced by F_δ — and the tower
   F_{k+1} = F_k[z]/(ψ_k) climbs by residual factors COMPUTED OVER THE
   NEW BASE — the re-based tower is built afresh, NOT by scalar-extending
   the ℤ_p tower (a residual polynomial irreducible over F_p can split
   over F_δ). Every graded ring gr_w(A), localization L, and degree-1
   unit T is the same construction run over the new base. PREDICTED
   (walked in REL.1's pass, not asserted here): value groups and scale
   bookkeeping (D.0's stretches, κ_r = h_r/(e_r·STR_r)) unchanged
   (p unramified: the same ℤ-normalized w).

 (R0-reads) THE READS. Species (increment / recentering), C.0's node
   datum fields (SHAPE (e, h, g, μ), anchor a, SIDE endpoints/height and
   stride positions, DIGITS (d_j), branch factor ψ, recentering lifts),
   realizability (NA)+(HV)+(SAE), and TRANSITION-ADMISSIBILITY are the
   SAME GRAMMAR — integer, lattice, and residue-datum fields; the
   VALUE SETS of the digit fields and of ψ are RECONSTRUCTED over the
   re-based tower (digits in D.3(e)-alphabets over F_δ; ψ monic
   irreducible over the tower field) — NO MONOTONICITY CLAIMED (pass-2
   critical 1): re-basing can SPLIT old residual factors, so there is
   no canonical inclusion of the old value sets into the new ones.
   PREDICTED, not asserted (= (EQ-1) below, fenced into REL.1's pass):
   no new species arise and none disappear.

 (R0-ledger) THE DIGIT LEDGER. Digit systems, pins, vol, and PIN-WELLDEF
   as cardinality-and-status statistics (C.0/C.0.5) — the same
   definitions, each constrained digit contributing the factor |𝔸_δ|⁻¹
   of its ATTAINABLE alphabet at its height — |𝔸_δ| = p^{a_δ} per
   (EQ-2)'s re-based-span definition, a q_δ-power only under (EQ-2)'s
   OPEN prediction; masses in vol_{O_δ}; C.1.5's (ZC) invariant and Theorem C(b)'s
   product formally as before with p^{nN} ↦ q_δ^{nN}.

**(REL.1) Theorem C over O_δ [OPEN KERNEL — the re-scoping pass].** For
every δ ≥ 1: §A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b) with
C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM — hold over O_δ under
(R0-box)–(R0-ledger) MUTATIS MUTANDIS, NOT verbatim (pass-1 gap 2):
every residue-theoretic object — base residue field, residual
polynomials, tower fields, graded pieces, attainable images,
irreducibility conditions, residue bases — is RECONSTRUCTED over F_δ,
never obtained by substituting a cardinality (the re-based tower is not
the scalar extension of the old one); only the base-independent skeleton
(coefficient order, unitriangular polynomial identities, valuation
geometry, pin-status arguments, additive equal-fiber counting) carries
over as written. Masses in vol_{O_δ} and

  (REL.1-b)   #{ f mod p^N ∈ S(H, Z) } = q_δ^{nN} · ∏_{i=0}^{k}
              vol(E_fresh(ν_i)) · vol(Z)      for every N ≥ N(H, Z),

every per-digit alphabet factor computed over F_δ. STATUS: a NEW THEOREM
with its own verification passes — not a corollary, not "by inspection"
(plan risk R6 REV-2). ROUTE (the plan's kernel charge, verbatim): a
derivation-grade RE-SCOPING PASS in a fresh context, accepted §C text in
hand, listing every step that touches the base. Walk order — the one
flagged hiding spot FIRST:
 (i) TYP(a)'s per-digit linearity: the accepted text reads "per-digit
   𝔽_p-linear on the base coordinates after C.0's block expansion"; over
   O_δ this must RETYPE to per-digit ADDITIVE on O_δ-digit blocks
   (F_δ-linearity is the EXPECTED outcome, walked not available by
   fiat; additivity is all TYP(b) consumes — the
   additive-surjection ⇒ equal-size-kernel-cosets count is field-free).
   The retyping is the pass's first checkpoint, walked not asserted.
 (ii) Fact A/B division bookkeeping, with C.0.5's unitriangularity and
   PIN-WELLDEF: expected base-free — carries are ring-polynomial
   identities in strictly ≺-earlier coefficients, nowhere consuming the
   residue field's size.
 (iii) C.0's BLOCK CONVENTION: per-position residue bases now over F_δ;
   D.3(e)(ii)'s attainable accounting re-read on F_δ-blocks.
 (iv) D.3(e)(i)'s pieces and D.11's nominal counts: the RE-BASED slot
   images' cardinalities p^{a_δ}, a_δ computed in the re-based tower;
   whether the re-based maps are F_δ-linear and a_δ = δ·a is (EQ-2)'s
   OPEN prediction — an output of this walk, never an input.
Until this pass lands and is verified, EVERY consumer below is conditional
on REL.1, displayed per site.

### R.1 REL.2 — the sub-cluster base change (FIVE NAMED obligations (a)–(e); plan REV 3 counted four, (e) added at rev 2; (c) re-homed at REV 9)

BASE-INDEX CONVENTION (pass-1 critical 7 + gap 8's repair; ALL indices
ABSOLUTE). Fix an algebraic closure F̄_p once; F_m is THE subfield of
order p^m and O_m := W(F_m) ⊂ W(F̄_p). Nested base changes then compose
LITERALLY as subrings — O_δ ⊂ O_{δδ′}, no per-pair embedding choices —
and "(O_δ)_{δ′} = O_{δδ′}" is bookkeeping inside W(F̄_p), never an
identification up to isomorphism.
SETTING. Ambient base O_δ (δ = 1 at the root instance; any δ recursively
— the obligations must COMPOSE across nested base changes), a realized
prefix η over O_δ, state cylinder Σ (frame Ψ_η), digit cell c of Σ, and
a branch b_j of c's branch set (individuated per §T-ASSEMBLY's SIBLING
INDEXING — the (side, ψ)-selection). Write δ_j^rel := the product of the
residual degrees g down b_j's branch MEASURED OVER F_δ (the whole
unramified part absorbed into ONE base change), d_j := the O_δ-degree of
b_j's cluster, and δ_j := δ·δ_j^rel, the ABSOLUTE accumulated residue
degree. The target base is O_{δ_j} — ABSOLUTE index, pool size
q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}; at the root δ = 1 this is the plan's
reading. Every consumer display below and in [3]/[3t]/[4] carries the
ABSOLUTE index. CLAIM SHAPE (the plan's REL.2 head): the conditional
continuation measure of b_j's cluster, GIVEN the cell event Σ_c, is
measure-exactly the REL.1 theory over O_{δ_j} — JOINT-D1's q ↦ q^w
clause, now THROUGH Theorem C. NOT a consequence of REL.1 (pass-2
concern 4): REL.1 re-bases the AMBIENT theory; REL.2 identifies a
CONDITIONED SLICE of the ℤ_p theory WITH a re-based ambient theory. Five
obligations (a)–(e), each separately on the record — (c)'s content
re-homed to [3t]'s (SIB), so THIS note's proof burden is (a)/(b)/(d)/(e):

 (REL.2a) COORDINATE IDENTIFICATION [OPEN — pass-1 critical 4: rev 1
   named no map, no domain, no conventions; (a) is now a DELIVERABLES
   CHECKLIST, and nothing short of all six items is "(a) stated", let
   alone proved]. The pass that closes (a) must EXHIBIT:
    (a1) DOMAIN: the explicit list of continuation coordinates on Σ_c —
      which base coordinates (ℓ, i) are free (not fixed by Σ_c) — as a
      measurable product of O_δ-digit spaces;
    (a2) TARGET: the coefficient box of monic degree-d_j^rel polynomials
      over O_{δ_j}, d_j^rel := d_j/δ_j^rel, with its own C.0-order digit
      coordinates (integrality of d_j^rel is part of the obligation,
      EXPECTED from the tower data, walked in (a)'s pass, not asserted
      here (rev 4, Fable-pass Finding 1): with E := ∏_r e_r and
      F := ∏_r g_r the ramification/residue invariants accumulated over
      b_j's reads — C.0's SHAPE fields (e, h, g, μ), the accumulation
      §T-ASSEMBLY (τ-irr)/(OM-SAT) consumes — the saturation identity
      cluster degree = E·F·μ would give E·F ∣ d_j);
    (a3) EMBEDDING CONVENTION: the named F_{δ_j} ↪ (tower residue field)
      embedding and the canonical-lift (Teichmüller/Frobenius)
      convention, fixed per the BASE-INDEX CONVENTION;
    (a4) FORMULA: the target coefficients as explicit functions of the
      (a1)-coordinates — the map Θ_j itself;
    (a5) FRAME COMPATIBILITY: the displayed commutation of Θ_j with
      C.0.5's unitriangular transports;
    (a6) READ DICTIONARY: letter-for-letter transport of b_j's
      continuation READS to O_{δ_j}-classifier reads ((EQ-1)'s
      dictionary), displayed per read field.
 (REL.2b) NORMALIZATION / JACOBIAN [OPEN; stated RELATIVE to (a1)–(a4),
   which supply its domain and target — and only for cells with
   μ(Σ_c) > 0, the only cells any (SIB) display conditions on]. The
   conditioned ambient mass equals the vol_{O_{δ_j}} mass — a MEASURE
   COMPARISON, not a bijection alone: for every REL.1-measurable
   continuation event W over O_{δ_j} (digit cylinders generate),
     μ( Θ_j⁻¹(W) │ Σ_c ) = vol_{O_{δ_j}}(W),
   i.e. the pushforward of the conditional continuation measure under
   Θ_j IS the normalized O_{δ_j}-box measure. This is where a hidden
   Jacobian/normalization defect would live; nothing short of the display
   above is accepted as "(b) done".
 (REL.2c) SIBLING INDEPENDENCE — RE-HOMED (plan REV 9; pass-8 concern 2:
   one precise joint statement, one owner). The content of (c) IS the
   (SIB) kernel, stated ONCE in §T-ASSEMBLY §T.3 with its base-changed
   quantifier (unramified O_δ) built in; OPEN there in its measure-level
   (SIB-STEP) form (CL-10; gate PASSED 32/32, supports not closes).
   [2r]'s duty under (c) reduces to supplying (a)/(b)/(d) so that (SIB)'s
   per-sibling factors ARE the REL.1 theory over O_{δ_j}. This clause
   CITES (SIB) and never re-states it.
 (REL.2d) LIFT-POLICY COMPATIBILITY [OPEN — pass-1 critical 5: well-posed
   only AFTER (a1)–(a6) exist; until then (d) is a named obligation with
   the acceptance criterion below, not a statement]. ACCEPTANCE
   CRITERION: a displayed COMMUTATIVE SQUARE — vertices: b_j's
   continuation data on Σ_c; the O_{δ_j} coefficient box; b_j's
   continuation subtree of T_can(f) ([1]'s canonical tree, REV 8's
   per-branch form); the O_{δ_j}-engine's canonical tree
   T_can^{O_{δ_j}}(Θ_j(·)) — with horizontal maps Θ_j ((a4)) and a
   SPECIFIED node-data correspondence (species word, node datum fields,
   τ-verdicts, via (a6)'s dictionary + (EQ-2)'s alphabets), the
   canonical residue-field-lift handling of [1]'s policy re-based per
   (a3). The square commutes for every f ∈ Σ_c. Without (d), a
   prescribed-subtree event S_j has no canonical O_{δ_j}-side meaning
   and (SIB-Oδ) below is ill-typed.
 (REL.2e) β-IDENTIFICATION [OPEN — pass-1 gap 15's repair, completed
   at rev 3 (pass-2 critical 2): the typing the R.2 closing sentence
   consumes, previously smuggled into it].
   Five displayed requirements: (e1) STATE-INDEX CORRESPONDENCE — an
   explicit dictionary sending [3]/[3t]'s state index τ_j(c) at cell c
   to a REL.1-side state over O_{δ_j}, compatible with (a6)'s read
   dictionary; (e2) DEGREE CONVENTION — the β-argument is p^{δ_j} with
   δ_j ABSOLUTE (BASE-INDEX CONVENTION), = q_δ^{δ_j^rel}; (e3) MASS =
   ENTRY — the displayed equation that [3]'s table entry
   β_{e_j, τ_j(c)}(p^{δ_j}) IS the REL.1 mass
   vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j }, keyed so this
   is [3]'s definition or a cited theorem, never a notational overlap;
   (e4) FIRST-INDEX DICTIONARY (pass-2 critical 2: e_j is nowhere
   defined in the REL.2 setting) — an explicit definition of the
   entry's first index e_j from b_j's data (candidate: (a2)'s
   O_{δ_j}-degree d_j^rel — owed, not assumed), displayed to agree
   with [3]'s table convention for the first index; (e5)
   SUBTREE/OUTCOME TYPING (pass-2 critical 2: per-state vs
   per-subtree) — the entry's indices must DETERMINE the prescribed
   subtree T_j: either a displayed proof that (e_j, τ_j(c)) determines
   T_j, or T_j added as an explicit further index of the entry (with
   [3]'s tables re-keyed to match); without (e5), distinct prescribed
   subtrees at the same cell would share one β entry and (e3)'s
   equation is ill-typed.
   PLAN-SYNC FLAG: CL-8 currently reads REL.2(a)/(b)/(d), and the
   plan's REV 3 phrase is "the four-obligation REL.2"; (e) is owed
   from here and must be ledgered there, AND the count is superseded —
   FIVE named obligations (a)–(e) since rev 2 (this note's convention;
   see R.1 head). Both updates owed to the plan at the next CL-8 sync.

**The equivariance trio (what PCI's [2r]-leg actually cites — WHICH ledger
quantities are BASE-CHANGE EQUIVARIANT, each derived or fenced).**
 (EQ-1) SPECIES/MENU SYNTAX INVARIANT. The species alphabet and menu are
   the SAME finite syntax over every O_δ: species letters are defined by
   stage tuples (e, h, g, μ), side/lattice data, and polygon conventions
   — a grammar parameterized by integers and residual-degree data, never
   by the residue field's SIZE ([2a]'s catalogue bounds consume degree
   budgets only). What changes under ⊗O_δ is the REALIZATION multiplicity
   of each letter (bigger digit alphabets), never the letter set. STATUS:
   PREDICTED — nothing derived here (pass-1 critical 1); the formal
   check ("no species definition consumes q") is a named checkpoint of
   REL.1's re-scoping pass, where it is walked, not asserted.
 (EQ-2) ALPHABETS: THE RE-BASED-SPAN FORM (pass-1 critical 3's repair —
   the rev-1 "|𝔸_δ| = q_δ^a by the same span computation" law is
   RETIRED as unjustified). DEFINITION (unconditional): the O_δ-ledger's
   alphabet 𝔸_δ at a shape position is the attainable additive
   image/span of the RE-BASED slot maps, computed inside the RE-BASED
   tower over F_δ (D.3(e)(i)/C.3 run over O_δ) — NOT a scalar extension
   of the ℤ_p-alphabet 𝔸: tower fields change under re-basing
   (F_{p^k} ⊗_{F_p} F_{p^δ} decomposes when gcd(k, δ) > 1), and §C
   certifies |𝔸| = p^a only as an additive-span cardinality, with no
   subfield structure. Unconditionally |𝔸_δ| = p^{a_δ}, a_δ := the
   F_p-additive-span dimension of the re-based images. PREDICTION
   (OPEN — a theorem to prove, never a residue-degree default; REL.1
   walk item (iv), tested by REL-n4's exponents), COMPARISON DOMAIN
   PINNED (rev 4, Fable-pass Finding 3: the re-based tower is rebuilt
   afresh with no canonical inclusion (R0-reads), so "the same
   position" needs saying — the prediction is PER POSITION CLASS): at
   a fixed shape position WHOSE SPECIES IS δ-STABLE (persists under
   re-basing, matched per (a6)/(EQ-1)'s owed dictionary), the re-based
   piece maps are F_δ-linear and a_δ = δ·a, i.e. |𝔸_δ| = q_δ^a = |𝔸|^δ
   — whence exponent preservation in base q_δ for every per-digit
   factor, vol(E_fresh), (ZC-c) mass, and Theorem C(b) product ("the
   algebra q ↦ q^δ", attached to measure objects). At a position whose
   residual factor SPLITS under re-basing the comparison is NOT
   well-posed: the old alphabet re-distributes across the NEW branch
   species. The Fable pass's worked instance (δ = 2, ψ = z² + 1 over
   F₃, splitting over F₉): the shallow position a = 1 gives a_δ = 2 =
   δ·a NUMERICALLY — but ψ's split changes the species at BOTH
   positions, so even the shallow comparison is OUT-OF-DOMAIN by this
   pin's own clause (the Fable confirm's G1: no in-domain instance is
   exhibited here; the law's first in-domain test is the gate's);
   the full position a = 2 gives each re-based branch
   𝔸_δ = F₉, i.e.
     a_δ = 2 ≠ δ·a = 4,
   which refutes NOTHING — the species did not persist, so the
   position is OUTSIDE the pinned domain (its per-cluster mass
   bookkeeping recombines across the new branches: REL.2/(SIB)
   territory, fenced there). STATUS: definition unconditional; the
   a_δ = δ·a law OPEN, REL.1-conditional, on the pinned
   per-position-class domain.
 (EQ-3) CONDITIONAL MASSES TRANSPORTED. REL.2(b) verbatim — the
   conditioned masses are vol_{O_δ} masses on the nose. STATUS: open
   kernel (b); no weaker reading (bijection-only, or level-matching
   without normalization) counts.
PCI BOOKKEEPING (plan REV 13): PCI = REL.2(a)/(b)/(d) — plus (e), the
β-typing leg added at rev 2, completed to (e1)–(e5) at rev 3,
plan-sync flagged — + CTS-M(iv)-REP + XRB.
This note owes the FIRST leg only; CTS-M(iv)-REP is [2b]/CTS-side,
and XRB (height elimination) is a displayed HYPOTHESIS at [3t]-COND,
proved in [3] as RS.0(β)/CL-9 — neither is restated or discharged here.

### R.2 The (SIB) O_δ quantifier — this note's deliverable to [3t]

§T.3's (SIB) reads: at a branching cell c with branch set {b₁, …, b_m},
each S_j the event that b_j's continuation realizes a prescribed finite
subtree T_j — "S_j determined by b_j's own continuation reads, base-changed
to O_{δ_j} per [2r] REL.2(a)/(b)/(d)" — and asserts, conditionally on Σ_c,

  (SIB)   μ( ⋂_{j=1}^m S_j │ Σ_c ) = ∏_{j=1}^m μ( S_j │ Σ_c ).

The LAW is owned by [3t] (OPEN kernel, (SIB-STEP) joint-vector form,
CL-10). What THIS note owes — the exact sentence [3t]-COND's acceptance
record waits on — is the well-typedness of its quantifier:

  (SIB-Oδ) [FENCED = REL.1 + REL.2(a)+(b)+(d), composed; derived nowhere
  yet]. For EVERY realized prefix η, EVERY branching cell c, EVERY branch
  b_j — simultaneously over every unramified O_δ that arises (all δ ≥ 1
  in one statement; no per-δ case analysis) — the event S_j IS an
  O_{δ_j}-statement: (REL.2a) identifies b_j's continuation with the
  monic degree-d_j^rel box over O_{δ_j}; (REL.2d) identifies the
  prescribed subtree T_j with a canonical O_{δ_j}-subtree of the re-based
  engine; (REL.2b) prices
    μ( S_j │ Σ_c ) = vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j },
  the right side a REL.1-theory mass. RECURSION CLAUSE: the same typing
  applies at every descendant branching cell inside T_j, ABSOLUTE
  indices throughout — a branch of relative accumulated degree δ″ at
  ambient O_{δ_j} targets O_{δ_j·δ″}, literally a subring chain in
  W(F̄_p) per the BASE-INDEX CONVENTION (unramified over unramified is
  unramified) — which is what TREE-EXP's induction consumes.

Under (SIB)'s product law AND GIVEN (REL.2e), the per-sibling factors
are the base-changed state-indexed values β_{e_j, τ_j(c)}(p^{δ_j})
(δ_j ABSOLUTE) that [3]'s b_e^split multiset convolution and RS.1-SH's
shallow convolution consume (plan §4/§4t) — (e1) supplies the state
index, (e2) the exponent, (e3) the equality of mass and table entry,
(e4) the first index e_j, (e5) the typing that the entry's indices
determine the prescribed subtree T_j; each such β-substitution cites
PCI, whose [2r]-leg is REL.2(a)/(b)/(d) + (e) per the bookkeeping
above.

### R.3 REL.3 — positivity/domination transfer (stated separately, per the plan)

  (REL.3) [DEFERRED-STATEMENT OBLIGATION — pass-1 gap 14's repair]. The
  [4]-side displays (SQ.0–SQ.2's actual events, quantifiers, and
  inequalities) DO NOT EXIST YET — the plan gives routes, not displays —
  so no theorem statement is possible here; rev 1's "covering and
  monotone-domination statements" wording was a placeholder wearing a
  specification's clothes, and it is RETIRED.

What IS fixed now, from the plan alone: SQ.2's cluster-size induction
(plan §6) consumes each base-changed leg β_m(p^δ) as a CERTIFIED
O_δ-statement — the induction hypothesis is an input theorem about
vol_{O_δ}, never the formal substitution q ↦ q^δ in a ℤ_p-display (plan
pass-1 obstruction 6). ACCEPTANCE CRITERION for stating REL.3: once [4]
drafts SQ.0–SQ.2, REL.3's revision restates each consumed display
verbatim with the base re-scoped to O_δ (ABSOLUTE indices), then is
passed like REL.1. [2r] OWNS the obligation; [4] names the consumption
sites. CL-8 is the ledger line: REL.1 + REL.2(a)/(b)/(d)/(e) + REL.3,
with (c)'s content at CL-10's (SIB) ((e) plan-sync flagged).

### R.4 Sealed gate REL-n4 — decision-independent (plan REV 3; OUTLINED — RUNNABLE SPEC OWED; retyped at rev 2, pass-1 critical 11)

INSTANCE: p = 2, n = 4. Condition on root reads whose residual factor is
an irreducible QUADRATIC over F₂ (δ = 2, the smallest nontrivial base
change; O_δ = W(F₄)).
OUTLINE (unchanged but for the rev-4 domain note): seal, before any
census, the conditional refinement law of that quadratic cluster
computed from the W(F₄) formulas — the engine's q ↦ q² layer; ONE ledger
family, computed at q = 2 (the ambient accepted ledger, supplying the
conditioning frame) and at q² = 4 (the claimed relative ledger, (EQ-2)'s
PREDICTED exponents — the exponent test INHERITS (EQ-2)'s PINNED
comparison domain (rev 4): a_δ = δ·a instances are sealed only at
δ-stable-species positions; a position whose residual factor splits
under re-basing enters through its own re-based families in (g2), never
as an exponent-comparison instance); censuses compared against the
sealed q²-side masses of each refinement outcome.
RUNNABLE SPEC, OWED BEFORE THE SEAL (pass-1 critical 11: the rev-1 prose
admitted implementations counting different objects; the gate is NOT
"specced" until a spec sheet displays all of):
 (g1) the exact conditioning congruences on the coefficients mod 2^{N₀};
 (g2) the complete finite list of refinement families/outcomes
   [spec-sheet notes from the Fable confirm: N1 — μ is unpinned and
   μ = 1 gives a trivial degree-1 box, pin μ ≥ 2 or justify; N2 —
   z² + z + 1 splits over F₄, so the exponent leg may have an EMPTY
   in-domain instance set at this family: (g2) must exhibit at least
   one δ-stable-species position or pick a different family];
 (g3) the sealed rational mass of each outcome, displayed fractions;
 (g4) the matching-level rule: which N each census runs at, and whether
   the test is at EVERY N ≤ 5 or one pinned N;
 (g5) the map from factorpadic output (factor degrees, e/f data) to
   each refinement outcome — the gate tests ONLY refinement events that
   are FUNCTIONS of the factorization data (pass-1 critical 12's
   residue: PARI factor data need not recover MOVES refinement history;
   any outcome not so expressible is OUT of the gate's scope);
 (g6) the W(F₄) representation, coefficient encoding, and comparison
   map for side (ii);
 (g7) the DETECTION-CAP POLICY (pass-1 gap 13; the campaign's uniform-
   cap discipline): the census level N with a CERTIFIED determination
   radius — every level-N box's refinement verdict constant on the box
   — OR the displayed default: any box undetermined at the cap is a
   SPEC FAIL (re-spec at larger N before sealing), never silently
   binned.
VERIFY TWO WAYS — INDEPENDENCE RETYPED (pass-1 critical 12):
 (i) the ℤ₂ side WITHOUT MOVES strata: conditioning by raw coefficient
   congruences (g1) (Theorem-C-certified vocabulary only), refinement
   read off the PARI factorpadic DECISION oracle via (g5), on the
   exhaustive level-N slice (2^{4N} boxes, N per (g4)). THIS SIDE ALONE
   carries the gate's independence claim, and only at the DECISION
   level — it shares no normalization with the sealed formulas.
 (ii) a DIRECT W(F₄)-side enumeration of the corresponding MOVES strata
   at matching level — RETYPED: an INTERNAL CONSISTENCY CENSUS (it runs
   the classifier whose relative interpretation is under test), NOT an
   independent oracle; "two-way independence" is NOT claimed.
PASS = exact equality of BOTH censuses with the sealed law, every family,
zero tolerance. RECORDED RESIDUE (carried from the plan): the
history-level identification stays REL.2(a)–(e)'s proof burden, not the
gate's. A PASS supports, never closes, any obligation of this note; a
FAIL is adjudicated first against the seal's own arithmetic, then against
REL.2's identification, then structural (plan §7's order).

### R.5 Honest perimeter

DERIVED IN THIS NOTE: nothing — and at rev 4 that is LITERALLY true of
every display (pass-1 critical 1's sweep; pass-2 critical 1 caught the
one residual unfenced assertion, R0-reads' "value sets enlarge"
monotonicity claim, now replaced by the neutral RECONSTRUCTED
statement; the Fable dual pass caught the last two unfenced residues —
(a2)'s E·F ∣ d_j parenthetical and R.0's strong "heights untouched"
reading, both fenced at rev 4): every equality or invariance formerly asserted in
R.0/(EQ-1)/(EQ-2) is now typed PREDICTED, REL.1-conditional, or neutral
at its own site. This is the ledger's STATEMENT layer.
OPEN, with owners: REL.1 (here; the fresh-context re-scoping pass is the
next [2r] work unit) · REL.2(a)/(b)/(d)/(e) (here; (a) a six-item
deliverables checklist, (d) an acceptance-criterion square, (e) a
five-item β-typing checklist (e1)–(e5) — plan-sync flagged, count
change included) · REL.2(c) = (SIB)/CL-10 (owner [3t];
OPEN there, gate-supported) · REL.3 (here; DEFERRED-STATEMENT until
[4]'s displays exist) · REL-n4 (OUTLINED; runnable spec (g1)–(g7) owed
before sealing). Status of the trio: (EQ-1) PREDICTED, fenced into
REL.1's pass; (EQ-2) re-based-span DEFINITION unconditional, the
a_δ = δ·a law OPEN on its rev-4 pinned per-position-class domain;
(EQ-3) = REL.2(b), open.
CONSUMER EDGES (each conditional on the named obligations closing):
[3t]-COND's acceptance ("after [1] and [2r]" — (SIB-Oδ) is the consumed
sentence) · PCI's O_{δ_j} leg (β-substitution sites only, per [3t]'s
consumption scope) · [3]'s b_e^split / RS.1-SH legs β_{e_j,·}(q^{δ_j}) ·
[4] SQ.2 via REL.3 · §V-TABLES' record.
CROSS-NOTE WATCH (Fable dual pass, 2026-07-27 — duties owed ELSEWHERE,
recorded here because [2r]'s displays inherit them):
 (W1) "realizes T_j" — rooted-prefix containment vs exact truncation
   fiber are two readings with different masses on concrete instances;
   the DEFINITION duty sits at §T.3/[1] (per this note's fence: no
   re-statement of (SIB)'s product law here). (e3)'s displayed equation
   and (SIB-Oδ)'s pricing line must inherit whichever reading [1]/[3t]
   pin — owed at the CL-10 sync.
 (W2) §T.3's inline "residue degree δ_j" carries no ABSOLUTE annotation
   (this note's BASE-INDEX CONVENTION requires consumer displays to
   carry absolute indices) — one word owed to §T.3 at the next
   §T-consuming revision, NOT an edit to the dual-accepted §T now.
NOT CLAIMED: anything beyond plan §3r — no ramified base change; no
uniformity-in-δ statement beyond the displayed quantifiers; no
height-elimination content (XRB is [3]'s); no menu/exhaustion claims; no
discharge of any obligation by the gate; and no re-statement of (SIB)'s
product law, which lives at §T.3 alone.


THE §C SOURCE DISPLAYS (LST/TYP/DOM context):
design; D.8 at the landing]. The next frame's box line IS the read line:
old_{i+1} = new as affine base-index functions. INTERCEPT: w'(f) :=
min_j(e_{i+1}·w(B_j) + j·h_{i+1}) (D.7, on the frame-(i+1) development)
= e_{i+1}·new(0), because every development slot lies weakly above the
new line — window slots by the stratum's (α)/(β)/(γ) clauses, transport
slots j > μ_i by w(B_j) ≥ old(j) (K1(Φ̂_i/w)) and old(j) > new(j) ((2))
— with equality attained at the span endpoints; the new stage scale is
e_{i+1}·str, so the absolute intercepts agree. SLOPE: w'(Φ̂_{i+1}) =
e_{i+1}h_{i+1}g_{i+1} (D.5's equal weights at the new stage) per
frame-(i+2) slot of D_{i+2} = e_{i+1}g_{i+1}·D_{i+1} base indices =
h_{i+1}/e_{i+1} per D_{i+1} — the read side's own per-index slope. Equal
intercept, equal slope. The ROOT instance (frame-1 box line = the root
read line) is the same computation at D.4's ROOT case. [At a RECENTERING
ν_{i+1}: e_{i+1} = g_{i+1} = 1, D_{i+2} = D_{i+1}; (1)–(2) run verbatim
against the standing frame's box, (3) is trivial, and (PU) holds with
D.10's RS-landing box (v = v'; the primed key's weight is the consumed
side's value — D.10/D.4), by the same support argument.]
CLOSE. Base i = 0 [completed at rev 11, pass-10 gap 1 — the spaced form of
the sentence had dodged the first guarded edit; root display now inserted at
the live site]: there is no earlier LINE (no m < 0), but Z₀ also carries the
CLUSTER ZEROS (every box coordinate pinned at level 0 — floor height 1). On
the window's interior slots j < μ₀ the root line has height ≥ λ₀·1 ≥ 1 (D.4's
ROOT case: every side slope ≥ 1), so the line dominates the cluster floor at
every box coordinate of the window (the monic lead is not a box coordinate):
F₀(b) = old₀(slot(b)) on the interior, with the cluster zeros absorbed — the
induction starts from the staircase form. Step, at any b in the next interior and any
m ≤ i: line_{i+1}(b) = new(b) [definition] ≥ line_i(b) [(1)+(2), since
b ≤ j*·D_{i+1} by (3); old = line_i by DEFINITION at rev 12, with (PU)
one step down — the root included — identifying it with the frame's box
line on the stratum] ≥ line_m(b) [induction hypothesis; b is in the current
interior by (3)]. FLOOR FORM: (ZC-a)'s F compares STEP functions — node
m's staircase top at b is line_m at the LEFT EDGE of b's frame-(m+1)
block. Blocks nest (D_{m+1} | D_{i+2}), so the coarser edge x ≤ the
finer edge y ≤ b, and line_{i+1}(x) ≥ line_{i+1}(y) [lines descend]
≥ line_m(y) [the line comparison, at y ≤ b in the next interior]: the
current staircase dominates every earlier one per index, and F_{i+1} =
old_{i+1}'s staircase (= line_{i+1}'s, by (PU)) on [0, μ_{i+1}·D_{i+2}). ∎

**Lemma LST (level-set scale-typing) [rev 9 — the pass-7 finding-5 residue,
now displayed; derivation C15 S5/S7].** Let (ν₀, …, ν_i) be any realizable
prefix (increments and recenterings in any interleaving), in frame-(i+1)
tower coordinates. Each inner tower level r carries the weight
κ_r := h_r/(e_r·STR_r) FIXED AT THE READ THAT AUGMENTED that level's key
(the increment read on that key's window; recenterings create no inner
level and change no κ — the CURRENT key never enters off); as declared,
ht(b, l) := l + off(b), off(b) := Σ_r innerslot_r(b)·κ_r. Then:
 (i) TYPING: ht(b, l) is the K1-chain weight of the coordinate's basis
   monomial p^l·∏_r Φ̂_r^{innerslot_r(b)}; hence for every current-window
   slot coefficient B, w(B) = min{ht(b, l) : (b, l) ∈ blk(B), y_{(b,l)} ≠ 0}
   (the iterated slot-minimum), and for every γ ∈ ℚ the weight-γ initial
   form in_γ(B) is a function of exactly the LEVEL SET
   L_γ(B) := {(b, l) ∈ blk(B) : ht(b, l) = γ} (typed in Lemma TYP below:
   it lives in D.3(e)(i)'s graded piece at γ's stage index);
 (ii) FLOOR CONSTANCY ON THE INTERIOR: on the factor interior — where all
   fresh content lives (C.1's rim bullet) — F_i(b) = old_i(slot(b)):
   ht-constant on each current block;
 (iii) SELECTION: for a factor-interior slot coefficient B with
   γ' > old_i(slot(B)), the ENTIRE level set L_{γ'}(B) lies strictly above
   the floor downset {ht ≤ F_i} — after ARBITRARY augmentations, the
   absolute-height formula selects the whole weight-γ' level set.
*Proof — induction on i (the per-key κ update discipline made explicit).*
BASE i = 0: the frame-1 tower coordinate (b, l) has monomial p^l·x^b; the
root read fixes w(x) = h₀/e₀ = κ₀ (STR₀ = 1), and K1(Φ̂₁/w) evaluates w of
any inner coefficient as the slot minimum of l + b·κ₀ over its nonzero
digits — ht IS the chain weight, and the ht-grading is the grading whose
pieces D.3(e)(i) describes: (i) holds. STEP at an INCREMENT ν_{i+1} (stage
data (e_{i+1}, h_{i+1}), e·g > 1): the frame-(i+2) tower adds exactly ONE
inner level — the just-read key Φ̂_{i+1} — at weight κ_{i+1} :=
h_{i+1}/(e_{i+1}·STR_{i+1}), the v_p-slope of the side ν_{i+1} READ; this
is the moment that κ is SET (beforehand only ν_i's landing bound
w(Φ̂_{i+1}) ≥ old_i(μ_i) is known, and computing with THAT value is the
stale-κ artifact, derivation S5). TRANS (D.7) builds the augmented
valuation with the read side value at the new key and touches no inner
weight (keys r ≤ i are never re-read); so off gains the single term
innerslot_{i+1}·κ_{i+1}, and ht = l + off is again the K1-chain weight of
the monomial: (i) persists. STEP at a RECENTERING ν_{i+1} (e_read = 1,
degree unchanged): the key is REPLACED (Φ̂ ↦ Φ̂ + t), the tower depth and
every inner κ_r are unchanged (the replaced key is the CURRENT one, absent
from off); the primed frame is reached by a C.0.5 unitriangular map at
fixed labels (C.1.0(a)) and D.10's frame valuation v = v' carries the
primed development: (i) transfers verbatim. (ii): on the factor interior
the current line dominates every earlier staircase (Lemma DOM's floor
form, displayed above; the C10B machine-check stands as instance
evidence only), so
F_i(b) = old_i(slot(b)) there: one ht-value per current slot, constant per
block. (iii): by (i) every coordinate of L_{γ'}(B) has ht = γ' >
old_i(slot(B)) = F_i on blk(B) (block-constant by (ii)); the floor downset
on the block is {ht ≤ F_i}: disjoint. ∎
[Exercised: S5.1's level sets {(0,5),(1,4)} at γ' = 5 and {(2,3),(3,2)} at
γ' = 11/2 (κ₁ = 5/2 CURRENT — the stale value 2 is the rev-7 artifact);
S5.2's designed p = 3 collision dissolves; S5.3 re-derives every recorded
label verdict. C.1.5's proof consumes (iii) at its strip and value steps.]

**Lemma TYP (the degree-γ' initial form, typed) [rev 10 — pass-9 gap 2].**
Fix a frame with accumulated stretch str, a current-window slot
coefficient B ∈ Ĉ, and γ' ∈ ℚ; set δ' := str·γ' — the stage-scale index
of the absolute height γ' (C.1.0(c)/the scale declaration: the two
scales differ by the factor str at fixed labels; equalities and strict
inequalities transfer).
(a) THE OBJECT. The weight-γ' level-set content of B lives in
gr^{Ĉ}_{δ'} — D.3(e)(i)'s graded piece at δ'; the absolute scale
relabels the piece index, nothing else. Display: B is literally its
tower expansion B = Σ_c y′_c·m_c (D.3(e)(ii)/Fact A: the iterated
development down to ℤ_p-digit coordinates; m_c := the basis monomial
p^l·∏_r Φ̂_r^{innerslot_r(b)} of c = (b, l), y′_c := the unit lift of
the digit y_c), and each nonzero summand has weight ht(c) (LST(i): ht is
the K1-chain weight; unit lifts of F_Qˣ multiply pieces integrally,
D.3(e)(i)). On any locus where blk(B)'s coordinates of ht < γ' vanish
(the literal downset — C.1.5), every surviving summand has weight ≥ γ',
so w(B) ≥ γ' and, taking classes in the piece (the class map is additive
and kills weight > δ' — D.1),
  in_{γ'}(B) = Σ_{c ∈ L_{γ'}(B)} y′_c·in(m_c)  ∈ gr^{Ĉ}_{δ'}:
an ADDITIVE function (per-digit 𝔽_p-linear on the base coordinates after
C.0's block expansion; NO F_Q-module structure on individual base digits is
claimed — the F_Q-structure enters only through the target alphabet, which is
all that TYP(b)'s additive-surjection/kernel-coset count consumes; retyped at
rev 11, pass-10 gap 2) of exactly the level-set
digits (y_c)_{c ∈ L_{γ'}(B)} and of no other coordinate. If γ' is
achievable at no coordinate of the block (off the lattice), L_{γ'}(B) =
∅ and the piece receives nothing — matching C.1's on-lattice inventory.
CONSEQUENCE: gr^{Ĉ}_{δ'} is the F_Q-span of {in(m_c) : c ∈ L_{γ'}(B)}
(any B of weight δ' has, by LST(i)'s min formula, no nonzero digit below
ht γ', so the display applies to it unconditionally).
(b) USE 1 — C.1.5's counting consumes exactly this object. The fresh
value clause at exact valuation γ' is R_{δ'}(in_{γ'}(B)) = v, R_{δ'} :=
D.3(e)(i)'s piece map at δ'. The composite (level-set assignments) → L₀,
(y_c)_c ↦ Σ_c y′_c·R_{δ'}(in(m_c)), is additive with image = the
additive span of the slot images (by (a)'s CONSEQUENCE) = the digit's
ALPHABET (D.3(e)(i); D.11's per-digit convention — same piece, same map;
in particular the emitted pattern value v lies in the image). An
additive surjection onto its image has equal-size fibers (kernel
cosets), so the clause cuts exactly (alphabet)^{−1} among the level-set
assignments; R_{δ'}'s injectivity on the piece (D.3(e)(i)) is what makes
|alphabet| = |piece| the D.11-nominal cardinality. No basis, address, or
leading-coordinate claim enters.
(c) USE 2 — LST's selection consumes exactly this object. LST(iii)
selects the weight-γ' content of a factor-interior B with γ' >
old_i(slot(B)): by (a) that content is a function of exactly L_{γ'}(B),
so selecting it selects the WHOLE level set, which LST(iii) places
strictly above the floor downset — the typed object's coordinates are
free on Σ_i, and it is the object (b) counts. §C consumes "degree-γ'

THE BLUEPRINT UNDER FINAL CONFIRMATION (REV 4):
# MovesR LEAN BLUEPRINT — REV 4 (re-architecture per stuck-rule adjudication #1)

SOURCE (ground truth): `lean/notes/MOVES_2026-07-24.md` §R-LEDGER, rev 5, DUAL-ACCEPTED
2026-07-27; Lemma LST's §C display (MOVES 3728–3781) a consulted source since rev 3.
AUDIT TRAIL: rev 1 → Codex REJECT 15c/6g (all repaired rev 2); rev 2 → Fable REJECT
2c/5g, Codex repairs verified genuine (all repaired rev 3); rev 3 → MAXIMAL SPLIT:
fresh-Fable #2 ACCEPT 0/0 (`MOVESR_AUDIT_FABLE2_2026-07-28.md`, FF1–FF7 verified
leg-by-leg) vs Codex FINAL REJECT 15c/5g (`MOVESR_AUDIT_CODEX_FINAL_2026-07-28.md`).
ORCHESTRATOR ADJUDICATION (campaign ledger, stuck-rule #1): the split is systematic —
Codex reads explicit fences (K1-chain/in_γ internals, §B1 graded machinery) as DROPPED
CONTENT; Fable reads them as faithful declared pointers; unresolvable at the
statements-only level because §R-LEDGER's clauses genuinely POINT INTO §C machinery
with no Lean form. RESOLUTION = THIS REV: the §C machinery gets a minimal abstract
interface (`GradedCarrier` + per-lemma statement defs + `CStatements`), so every
clause field's TYPE is the cited lemma's full statement — no fence; instantiating the
interface from the OM engine is HC-1's declared deliverable. Codex-FINAL findings are
each triaged in §5 (survived → folded in / resolved-by-rearchitecture / note-rejected
after the ordered note-checks). The
campaign-wide lesson driving this revision: **STATEMENTS-ONLY ≠ CONTENT-FREE** — a
faithful obligation statement must be FALSE for instances the note would reject. So
every carrier structure now carries the note's own laws as fields (measure laws,
normalized-cylinder masses, nonemptiness/finiteness, typed clause content), and every
open kernel remains a named Prop that consumers hypothesize — nothing is discharged.
Units are definitions + elaboration checks; proof burden = the base-index layer only
(U2–U6, U12, U41). Unit format per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2.
Files land under `lean/LeanUrat/MovesR/`.

## 0. Design decisions

**(D1) WITT-VECTOR BASE LAYER: CONCRETE MATHLIB ROUTE — no axioms, no interface.**
(Unchanged from rev 1 except the card decision, overruled per finding 1.)
- Mathlib HAS: `WittVector p R`, `WittVector.map` + `map_injective`/`map_coeff`/
  `map_id` (`RingTheory/WittVector/Basic.lean`); `WittVector.teichmuller`
  (`Teichmuller.lean`); `AlgebraicClosure (ZMod p)`; `RingHom.eqLocusField`
  (`Algebra/Field/Subfield/Basic.lean:477`); `iterateFrobenius`
  (`Algebra/CharP/Lemmas.lean:327`); `Subfield.inclusion`; `AdjoinRoot`.
- Mathlib LACKS: a finite-subfields-of-F̄_p lattice, W(F_q)/unramified API, and
  `WittVector.map_comp` (3-line local ext lemma via `map_coeff`).
- DECISION: ambient `W(F̄_p) := WittVector p (AlgebraicClosure (ZMod p))`; `F_m` :=
  the fixed field of the m-th Frobenius iterate (`eqLocusField`, membership
  definitionally `x ^ p ^ m = x`); `O_m := (WittVector.map (F_m).subtype).range`.
  Composition law "(O_δ)_{δ′} = O_{δδ′}": `relExt m δ′ := O (m·δ′)` makes the display
  `rfl`/`mul_assoc` ("bookkeeping inside W(F̄_p), never an identification up to
  isomorphism"); the substantive content is `O_le : d ∣ m → O_d ≤ O_m` (provable)
  and `qq_mul : q_{mδ′} = q_m^{δ′}` (`pow_mul`). FALLBACK if the `ExpChar` instance
  fights: `(frobenius _ p) ^ (m : ℕ)` in the RingHom monoid, or the raw carrier
  `{x | x ^ p ^ m = x}` with closure proved once.
- **FINDING-1 REPAIR (rev-1 "deliberate non-unit" overruled):** the display "F_m is
  THE subfield of order p^m" includes the CARD FACT. New provable unit **R6**:
  `Fsub_card : Nat.card ↥(Fsub p m) = p ^ (m : ℕ)` (roots of the separable
  `X^{p^m} − X` in an algebraically closed field; `galois_poly_separable` +
  root-counting; difficulty hard). Stated NOW, proved by the wave-3 fleet.

**(D2) CARRIERS WITH LAWS; PARAMETERIZED REALIZED FAMILIES.** The ambient δ-based
MOVES theory does not exist in Lean (REL.1 is the kernel saying it does). Obligations
are typed over carrier structures whose fields are the note's objects AND the note's
laws about them (finding 2's lesson): `Setting` carries the realized-measure laws
(mass bounds, additivity on its event class, conditional normalization at positive
cells); `BoxVol` is a genuine normalized content function pinned on digit cylinders;
every carrier the note treats as nonempty/finite is typed nonempty/finite.
Quantification over realized instances is via `SettingsFamily` — a structure with
nonemptiness, a root (δ = 1) member, and TYPED descendant closure (findings 19/20).
Degenerate instances that survive (e.g. `cellMass = 0` cells) are exactly those the
note's own provisos exclude, and every display carries the proviso as its guard.

**(D3) MASS CODOMAIN ℚ.** All masses/entries (vol, condMass, β) are `ℚ`: the note's
masses are exact rationals ("sealed rational mass, displayed fractions"); β entries
are ℚ(q) evaluated at q = p^{δ_j} ∈ ℕ. No `ℝ≥0∞`.

**(D4) REL.1 = THE CInterface (REV-4 RE-ARCHITECTURE; supersedes the rev-2/3 clause
ledger and its fences).** Three layers:
(a) **`GradedCarrier p δ`** — the D.3(e)/§C graded vocabulary as ABSTRACT TYPES WITH
LAWS, ≤ ~10 fields, NO construction: coefficients, graded pieces Gr γ, the K1-chain-
weight function w, the initial-form/class map in_γ, ultrametric additivity of w,
additivity of in_γ at its weight, kills-weight-above, weight-detection. Instantiating
it from the OM engine is **HC-1's declared deliverable** (campaign plan §1).
(b) **Per-lemma statement defs + `CStatements`** — one named def per §C lemma the
ledger cites (`SecAStmt, SecB1Stmt, SecB2Stmt, ThmCaStmt, ThmCbStmt, C05Stmt, C1Stmt,
C15Stmt, LSTStmt, TYPStmt, DOMStmt`), each def's body = the lemma's FULL statement
over the carrier bundle at the base params — LST's def carries ALL of (i) including
the K1-chain-weight typing (`G.w (mono i) = ht i`) and the initial-form/level-set
functionality, plus (ii) and (iii), typed once, NO FENCE. `CStatements p Sp AD δ n K`
is the record with one field per lemma, each field's type the named def.
(c) **REL.1's ledger := `CStatements` at base δ** — a TYPED POINTER, the note's own
"MUTATIS MUTANDIS" (`def REL1 … := CStatements …`, with `ThmCbStmt` = the (REL.1-b)
display over the DEFINED count — FF2's pin retained). EQ-1/EQ-2 are ATTACHED to
REL.1 per the note (CF17): `REL1PassDeliverable := REL1 ∧ EQ1` (EQ-1 is "a named
checkpoint of REL.1's re-scoping pass") and `EQ2lawIfREL1 := REL1 → EQ2law` (the
note's "OPEN, REL.1-conditional" status, typed).
Retained from rev 3 (Fable-verified, re-keyed onto the interface): the count
definition (FF2), the (Sp, AD) wiring `posOfDigit`/`aDim_eq` (FF4), pin-statistics
invariance — now over a proper STATUS carrier (CF9) — the memberships (FF5), the
`_linked` pattern (FF6), and the unitriangularity anchors (FF7).

**(D5) THE (e) KEYING (findings 13/14 + CF13/CF14 repair).** `entryFirst : ℕ` is
FIXED per branch (the note: e_j defined "from b_j's data"). REV 4 (CF14): `consumed`
is NO LONGER an inhabitant-chosen field — it is a PARAMETER of the (e)-Props, supplied
by [3]/MovesS's export exactly like `tableConv` (the prescriptions [3]'s tables
actually consume at this key; choosing it here was the vacuity Codex flagged). (e5)'s
first disjunct `determines` says the consumed class is a singleton; (e3) `massEqEntry`
is stated GIVEN `determines` and prices every consumed prescription at THE REL.1 mass
(`_linked`, FF6). The re-keying escape stays a STATEMENT-FENCE EVENT. (e4)'s
obligation is `e4agrees (tableConv)` — [3]'s exported convention — ONLY; REV 4
(CF13): `firstIdxCandidate` is DEMOTED to a named CANDIDATE definition that NO
consumer may hypothesize (the note: "candidate … owed, not assumed"; it is removed
from the D7 hypothesis list and marked non-obligation in its docstring). (e1)'s
(a6)-compatibility stays typed (`stateDict_compat`).

**(D6) NON-UNITS (deliberate, with reasons).**
- **REL.3 (finding 21 repair — the rev-1 pseudo-statement is DELETED).** The note:
  "the [4]-side displays (SQ.0–SQ.2 …) DO NOT EXIST YET — … so no theorem statement
  is possible here". Rev 1's `SQConsumptionSite`/`REL3` invented a satisfiable shape
  (`REL3 []` was true) — exactly the "placeholder wearing a specification's clothes"
  the note itself retired at its rev 1. REV-2 DISPOSITION: NO Lean object for REL.3.
  It is a recorded non-unit: when [4] drafts SQ.0–SQ.2, REL.3's revision restates
  each consumed display verbatim re-scoped to O_δ (ABSOLUTE indices), enters THIS
  corpus as new audited units, and is passed like REL.1. What IS fixed from the plan
  ("the induction hypothesis is an input theorem about vol_{O_δ}, never the formal
  substitution q ↦ q^δ") is a discipline on those FUTURE units, recorded here and in
  the Defs file as a fenced comment block, not a Prop. Honest absence over fake shape.
- REL.2(c): re-homed to [3t]'s (SIB) (plan REV 9); the note "CITES (SIB) and never
  re-states it" — no sibling-independence Prop here; MovesT owns it.
- Gate REL-n4 + spec sheet (g1)–(g7): census-side numeric artifact (PARI/W(F₄)),
  runnable spec still OWED in the note; not a Lean object; nothing here consumes it.
- (R0-tower)'s PREDICTED bracket (value groups/stretches/κ_r) and (R0-reads)'
  reconstruction prose: fenced as REL.1-pass content — doc-comments only (typing
  them now would invent the API the pass must walk; asserting them would break the
  note's PREDICTED fences).

**(D7) HYPOTHESIS vs DELIVERABLE (explicit; per unit below).**
- HYPOTHESES (open kernels; named Props consumers hypothesize — never proved or
  axiomatized here): `REL1` (= `CStatements` at base δ; + `REL1PassDeliverable`,
  `EQ2lawIfREL1`), `REL2b`, `REL2e.massEqEntry` (e3), `REL2e.determines` (e5),
  `REL2e.e4agrees` (e4), `EQ1`, `EQ2law`, `EQ3`, `SIBOdelta`.
  (`firstIdxCandidate` REMOVED from this list at REV 4 — CF13: a candidate, not an
  obligation; no consumer may hypothesize it.)
- DELIVERABLES (data a future pass must EXHIBIT; the structure's INHABITANT is the
  deliverable): `REL2a` ((a1)–(a6) with `teich_pin` a FIELD), `REL2d` (square +
  typed node-data correspondence), `REL2e`'s data ((e1) dictionary + compat, β
  table, `entryFirst`, `consumed`), `BoxVol`, `ReBased`/`TowerData`,
  `SettingsFamily`. **Accuracy correction (FF7 — the rev-2 "law fields make junk
  inhabitants impossible" claim was FALSE and is withdrawn):** what the law fields
  actually enforce is that every inhabitant SATISFIES the note's typed laws
  (measure laws, cylinder pins, unitriangularity anchors, letter/word/verdict
  preservation, the Teichmüller pin); free-data inhabitants respecting those laws
  remain possible wherever the ambient engine's objects (transports, trees, reads)
  do not exist in Lean — RECORDED as widening (v) in §3. Full pinning of those
  objects is REL.1-pass territory, not this corpus's.
- PROVABLE NOW (the only proof burden): U2–U6, U12, U41.

**(D8) REUSE OF EXISTING CORPORA (new; supports D4).** `DigitSystem n α`
(`Moves/DefsT.lean:187`) is digit-polymorphic — instantiated at `α := ↥(Fsub p δ)`
(the F_δ-digit ATOM of (R0-box)). `IsUnitriangular` (`MovesC/Defs.lean:241`,
polymorphic `[Add R]`), `CoordPrec` (`MovesC/Defs.lean:221`, C.0's order on ℕ × ℕ
— the (a5) unitriangularity anchor, FF7), `Line` + `DomData` (`MovesC/Defs.lean:255/278`, base-free
ℚ-data — the note's "valuation geometry … carries over as written" is the warrant)
are imported, NOT re-declared. Exact namespaces/qualifications resolved at E-phase;
any semantic mismatch discovered there re-enters the audit loop.

**(D9) ELABORATION-CHECK POLICY (revised).** Carrier structures with honest trivial
instances (`Setting`, `SettingsFamily`, `SpeciesSyntax`, `AlphabetData`) get
instance `example`s (well-formedness only, never evidence — the surviving trivial
instances are exactly proviso-excluded or vacuous-by-the-note's-own-fences cases).
Structures whose inhabitation IS the obligation or HC-1's deliverable (`REL2a1`–
`REL2a6` + bundle, `REL2d`, `REL2e`, `BoxVol`, `GradedCarrier`, `ReBased`,
`TowerData`, `SIBPkg`) get `#check` type-correctness elaborations ONLY —
their inhabitation story is the future pass, and that is the point (audit charge:
"an inhabitation story OR an explicit instance unit"; the story is recorded per
structure in its docstring).

## 1. Defs skeleton (normative for content; E-phase fixes syntax only, statement fence applies)

```lean
import Mathlib
import LeanUrat.Moves.DefsT      -- DigitSystem (polymorphic)
import LeanUrat.MovesC.Defs      -- IsUnitriangular, CoordPrec, Line, DomData (base-free)
namespace MovesR
variable (p : ℕ) [hp : Fact p.Prime]

/-! ## R0. Base-index convention (file Base.lean; units R1–R6) -/

/-- `F̄_p`, fixed ONCE. -/
abbrev Kbar := AlgebraicClosure (ZMod p)
/-- `W(F̄_p)` — every base below is a LITERAL subring of this one ring. -/
abbrev Wbar := WittVector p (Kbar p)

/-- `F_m` — THE subfield of `F̄_p` of order `p^m` (fixed field of the m-th Frobenius
iterate; membership definitionally `x ^ p ^ m = x`; the order fact is unit R6). -/
def Fsub (m : ℕ+) : Subfield (Kbar p) :=
  RingHom.eqLocusField (iterateFrobenius (Kbar p) p (m : ℕ)) (RingHom.id _)

/-- `O_m := W(F_m) ⊂ W(F̄_p)`: "nested base changes then compose LITERALLY as
subrings … no per-pair embedding choices". -/
def O (m : ℕ+) : Subring (Wbar p) :=
  (WittVector.map (Subfield.subtype (Fsub p m))).range

/-- `q_m := p^m = |F_m|` (the note's `q_δ := p^δ`; = |F_m| by R6). -/
def qq (m : ℕ+) : ℕ := p ^ (m : ℕ)

/-- degree-δ′ unramified base change of `O_m` inside `W(F̄_p)` — BY THE CONVENTION
this IS `O_{m·δ′}` (ABSOLUTE indices; "never an identification up to isomorphism"). -/
def relExt (m δ' : ℕ+) : Subring (Wbar p) := O p (m * δ')

theorem Fsub_le {d m : ℕ+} (h : d ∣ m) : Fsub p d ≤ Fsub p m := sorry            -- R2
theorem O_le {d m : ℕ+} (h : d ∣ m) : O p d ≤ O p m := sorry                     -- R3
theorem relExt_eq (m δ' : ℕ+) : relExt p m δ' = O p (m * δ') := rfl              -- R4
theorem relExt_relExt (m δ' δ'' : ℕ+) :
    relExt p (m * δ') δ'' = relExt p m (δ' * δ'') := by rw [relExt, mul_assoc]   -- R4
theorem O_le_relExt (m δ' : ℕ+) : O p m ≤ relExt p m δ' := O_le p ⟨δ', rfl⟩      -- R4
theorem qq_mul (m δ' : ℕ+) : qq p (m * δ') = qq p m ^ (δ' : ℕ) := sorry          -- R5
theorem Fsub_card (m : ℕ+) : Nat.card ↥(Fsub p m) = p ^ (m : ℕ) := sorry         -- R6

/-- The level-N digit cylinder at `g` in the degree-n coefficient box over `O_m`:
agreement of the first N Witt coordinates (F_m perfect ⇒ p^N W(F_m) = V^N W(F_m),
so this IS "f mod p^N" — (R0-box)'s level-N counting). -/
def cyl (m : ℕ+) {n : ℕ} (N : ℕ) (g : Fin n → ↥(O p m)) : Set (Fin n → ↥(O p m)) :=
  {h | ∀ (j : Fin n) (i : ℕ), i < N → ((h j : Wbar p)).coeff i = ((g j : Wbar p)).coeff i}

/-! ## The R.1 SETTING (file Interface.lean; units R7–R8) -/

/-- One realized instance of the note's SETTING ("Ambient base O_δ …, a realized
prefix η, state cylinder Σ (frame Ψ_η), digit cell c of Σ, and a branch b_j …").
η/Σ/c/b_j are absorbed into carriers; the REALIZED-MEASURE LAWS are fields
(finding 2): masses in [0,1], a conditional content on an event algebra,
normalized exactly at the positive-mass cells the note conditions on. -/
structure Setting where
  δ : ℕ+                                  -- ambient ABSOLUTE index (root: δ = 1)
  δrel : ℕ+                               -- δ_j^rel (residual degrees g over F_δ down b_j)
  d : ℕ+                                  -- d_j, the O_δ-degree of b_j's cluster
  Cont : Type                             -- continuation points of Σ_c
  contNe : Nonempty Cont
  AmbEvents : Set (Set Cont)              -- the ambient event algebra on Σ_c
  univ_mem : Set.univ ∈ AmbEvents
  compl_mem : ∀ E ∈ AmbEvents, Eᶜ ∈ AmbEvents
  union_mem : ∀ E ∈ AmbEvents, ∀ E' ∈ AmbEvents, E ∪ E' ∈ AmbEvents
  cellMass : ℚ                            -- μ(Σ_c)
  cellMass_nonneg : 0 ≤ cellMass
  cellMass_le_one : cellMass ≤ 1
  condMass : Set Cont → ℚ                 -- μ( · │ Σ_c )
  condMass_nonneg : ∀ E, 0 ≤ condMass E
  condMass_empty : condMass ∅ = 0
  condMass_univ : 0 < cellMass → condMass Set.univ = 1
  condMass_add : ∀ E ∈ AmbEvents, ∀ E' ∈ AmbEvents,
    Disjoint E E' → condMass (E ∪ E') = condMass E + condMass E'
  PTree : Type                            -- prescribed finite subtrees T_j for b_j
  prescNe : Nonempty PTree
  SEvent : PTree → Set Cont               -- S_j(T); (W1)'s reading kept opaque
  SEvent_mem : ∀ T, SEvent T ∈ AmbEvents
  StateIdx : Type                         -- [3]/[3t]'s state indices
  τ : StateIdx                            -- τ_j(c)
  /-- (CF10) the AMBIENT C.0.5 frame family at the cell ("state cylinder Σ (frame
  Ψ_η)"): frames and their transports on continuation points are SUPPLIED BY THE
  AMBIENT THEORY — (a5)'s commutation quantifies over THIS family, so no inhabitant
  can substitute a private identity-only family. -/
  FrameC : Type
  frameCNe : Nonempty FrameC
  reframe : FrameC → FrameC → Cont → Cont

/-- `δ_j := δ·δ_j^rel` — ABSOLUTE accumulated residue degree; target base O_{δ_j}. -/
def Setting.δabs (S : Setting) : ℕ+ := S.δ * S.δrel
/-- (a2)'s target degree `d_j^rel := d_j/δ_j^rel` (ℕ-division; integrality is
(a2)'s obligation `REL2a2`). -/
def Setting.dRel (S : Setting) : ℕ := (S.d : ℕ) / (S.δrel : ℕ)
/-- (e2)'s DEGREE CONVENTION pinned: "the β-argument is p^{δ_j} with δ_j ABSOLUTE". -/
def Setting.βarg (S : Setting) : ℕ := qq p S.δabs

/-- The REALIZED family the (SIB-Oδ) quantifier ranges over (findings 19/20):
nonempty, contains the root (δ = 1) reading, and is CLOSED UNDER DESCENT with the
absolute re-indexing — "the same typing applies at every descendant branching cell
inside T_j, ABSOLUTE indices throughout". Supplied by the ambient theory. -/
structure SettingsFamily where
  mem : Set (Setting p)
  ne : mem.Nonempty
  root_mem : ∃ S ∈ mem, S.δ = 1
  /-- (CF1; NOTE-CHECK RESULT recorded) the note displays NO positive-cell
  existence law; its only positivity text is (b)'s proviso "μ(Σ_c) > 0, the only
  cells any (SIB) display conditions on". `mem_pos` types exactly that FAMILY
  SCOPE: the family IS the family of (SIB)-conditioning sites, so its members are
  the positive-mass cells — the advertised all-zero-mass singleton is dead
  (ne + mem_pos), with no existence claim beyond the already-parameterized `ne`. -/
  mem_pos : ∀ S ∈ mem, 0 < S.cellMass
  desc : (S : Setting p) → S ∈ mem → S.PTree → Set (Setting p)
  desc_sub : ∀ S hS T, desc S hS T ⊆ mem
  desc_amb : ∀ S hS T, ∀ S' ∈ desc S hS T, S'.δ = S.δabs
```

```lean
/-! ## The equivariance trio (file Eq.lean; units R18–R21) — carriers before REL.2,
which consumes them (findings 11/12/15/16/17) -/

/-- (EQ-1) carrier: species letters are FINITE SYNTAX — "defined by stage tuples
(e, h, g, μ), side/lattice data, and polygon conventions … never by the residue
field's SIZE". `shape` exposes the stage tuple (the grammar anchor); `menu δ` is a
FINSET (finiteness typed — finding 15) and nonempty (species exist at every base). -/
structure SpeciesSyntax where
  Letter : Type
  shape : Letter → ℕ × ℕ × ℕ × ℕ          -- the stage tuple (e, h, g, μ)
  /-- (CF4) the rest of the note's grammar: "species letters are DEFINED BY stage
  tuples (e, h, g, μ), side/lattice data, and polygon conventions" — side/lattice
  and polygon-convention data as declared carriers, with `letter_det` typing
  "defined by": the full datum determines the letter. -/
  SideData : Type
  side : Letter → SideData
  PolyConv : Type
  poly : Letter → PolyConv
  letter_det : Function.Injective (fun l => (shape l, side l, poly l))
  menu : ℕ+ → Finset Letter               -- the realized menu over O_δ
  -- (CF3, NOTE-CHECK RESULT: rev-3's `menuNe` was a STRENGTHENING — the note
  -- asserts menu INVARIANCE only, and R.5 says "no menu/exhaustion claims".
  -- REMOVED; empty menus are back in the statement's range.)

/-- **(EQ-1)** [PREDICTED — "nothing derived here"; walked in REL.1's pass]:
"the species alphabet and menu are the SAME finite syntax over every O_δ …
What changes … is the REALIZATION multiplicity …, never the letter set." -/
def EQ1 (Sp : SpeciesSyntax) : Prop := ∀ δ : ℕ+, Sp.menu δ = Sp.menu 1

/-- (EQ-2) carrier (findings 16/17 repair): the alphabet 𝔸_δ at a position class is
typed as an actual ADDITIVE SPAN — a carrier group per (δ, position) with the
attainable image as an additively-closed subset — "the attainable additive
image/span of the RE-BASED slot maps"; `card_eq` is the note's UNCONDITIONAL
definition part |𝔸_δ| = p^{a_δ}. `posLetter` is the species letter realized at the
position over O_δ — the (a6)/(EQ-1) matching dictionary AS DATA — and `Stable` is
DEFINED from it (species persistence), not a free field. -/
structure AlphabetData (Sp : SpeciesSyntax) where
  Pos : Type                              -- shape position classes
  posNe : Nonempty Pos
  Carrier : ℕ+ → Pos → Type               -- the re-based receiving group
  [carrierGrp : ∀ δ x, AddCommGroup (Carrier δ x)]
  [carrierMod : ∀ δ x, Module ↥(Fsub p δ) (Carrier δ x)]   -- F_δ-structure (CF6)
  /-- (CF5) the RE-BASED SLOT MAPS themselves, as declared data ("D.3(e)(i)/C.3
  run over O_δ"): abstract domains with F_δ-structure and the piece maps. -/
  SlotDom : ℕ+ → Pos → Type
  [slotDomGrp : ∀ δ x, AddCommGroup (SlotDom δ x)]
  [slotDomMod : ∀ δ x, Module ↥(Fsub p δ) (SlotDom δ x)]
  slotMap : ∀ δ x, SlotDom δ x → Carrier δ x
  alpha : ∀ δ x, Set (Carrier δ x)        -- 𝔸_δ
  /-- (CF5) ATTAINABILITY, typed as span-generation equality: 𝔸_δ IS "the
  attainable additive image/span of the RE-BASED slot maps" — not an arbitrary
  additively-closed subset of the right size. -/
  alpha_attain : ∀ δ x,
    alpha δ x = ↑(AddSubgroup.closure (Set.range (slotMap δ x)))
  aDim : ℕ+ → Pos → ℕ                     -- a_δ: F_p-additive-span dimension
  card_eq : ∀ δ x, Nat.card (alpha δ x) = p ^ aDim δ x
  posLetter : ℕ+ → Pos → Sp.Letter        -- the realized species letter (owed dictionary, typed)

/-- δ-STABLE-SPECIES position (rev-4 comparison-domain pin), DEFINED: the species
letter persists under re-basing. Split positions fail this and are OUT-OF-DOMAIN
(the F₉ instance recombines across new branches — "REL.2/(SIB) territory"). -/
def AlphabetData.Stable {Sp} (AD : AlphabetData p Sp) (δ : ℕ+) (x : AD.Pos) : Prop :=
  AD.posLetter δ x = AD.posLetter 1 x

/-- **(EQ-2) the law ON THE PINNED PER-POSITION-CLASS DOMAIN** [OPEN,
REL.1-conditional; attachment typed as `EQ2lawIfREL1`]: "at a fixed shape position
WHOSE SPECIES IS δ-STABLE …, the re-based piece maps are F_δ-linear AND a_δ = δ·a"
— BOTH conjuncts typed (CF6: the linearity half is now stateable, the slot maps
being declared data with F_δ-module structure). -/
def EQ2law {Sp} (AD : AlphabetData p Sp) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AD.Stable δ x →
    IsLinearMap ↥(Fsub p δ) (AD.slotMap δ x) ∧
    AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x

/-- (EQ-2)'s displayed consequence "|𝔸_δ| = q_δ^a = |𝔸|^δ" on the pinned domain —
PROVABLE (R20) from `card_eq` + hypothesized `EQ2law` by `pow_mul`. -/
theorem EQ2law_card {Sp} (AD : AlphabetData p Sp) (h : EQ2law p AD) :
    ∀ (δ : ℕ+) (x : AD.Pos), AD.Stable δ x →
      Nat.card (AD.alpha δ x) = qq p δ ^ AD.aDim 1 x ∧
      Nat.card (AD.alpha δ x) = Nat.card (AD.alpha 1 x) ^ (δ : ℕ) := sorry
      -- (proof consumes h's DIMENSION conjunct only; pow arithmetic as before)

-- (EQ-3) is declared after REL2b (it aliases it verbatim); see Rel2 block.
```

```lean
/-! ## REL.1 (file Rel1.lean; units R9–R13) -/

/-- The vol_{O_m} box-measure interface (finding 8 repair): a genuine normalized
finitely-additive content on an event algebra CONTAINING every digit cylinder, with
the cylinder masses PINNED to (R0-box)'s normalization ("coefficient box O_δ^n with
normalized Haar measure … = 1; f mod p^N ranges over q_δ^{nN} residue points").
`vol_cyl` rules out dummy measures. Inhabitation story: the Haar construction of
the REL.1 pass; no instance is built in MovesR. -/
structure BoxVol (m : ℕ+) (n : ℕ) where
  events : Set (Set (Fin n → ↥(O p m)))
  univ_mem : Set.univ ∈ events
  compl_mem : ∀ W ∈ events, Wᶜ ∈ events
  union_mem : ∀ W ∈ events, ∀ W' ∈ events, W ∪ W' ∈ events
  cyl_mem : ∀ (N : ℕ) (g : Fin n → ↥(O p m)), cyl p m N g ∈ events
  vol : Set (Fin n → ↥(O p m)) → ℚ
  vol_nonneg : ∀ W, 0 ≤ vol W
  vol_empty : vol ∅ = 0
  vol_univ : vol Set.univ = 1
  vol_add : ∀ W ∈ events, ∀ W' ∈ events,
    Disjoint W W' → vol (W ∪ W') = vol W + vol W'
  vol_cyl : ∀ (N : ℕ) (g : Fin n → ↥(O p m)),
    vol (cyl p m N g) = ((qq p m : ℚ) ^ (n * N))⁻¹
  /-- (CF15) LEVEL DETERMINATION: every event is, at some level, a finite union of
  level-N cylinders — so `vol` on the WHOLE event class is FORCED by additivity +
  `vol_cyl`: it IS the normalized Haar mass, not merely Haar-on-cylinders with
  freedom elsewhere. This is the finitely-additive reading of "(digit cylinders
  generate)", and it is the note's own discipline: (g7)'s "CERTIFIED determination
  radius — every level-N box's … verdict constant on the box" is exactly the
  requirement that priced events be level-determined. -/
  events_level : ∀ W ∈ events, ∃ (N : ℕ) (G : Finset (Fin n → ↥(O p m))),
    W = ⋃ g ∈ G, cyl p m N g

/-- **THE CInterface, layer (a) — `GradedCarrier`** (REV 4, D4): the D.3(e)/§C
graded vocabulary as abstract types with laws; NO construction — instantiation
from the OM engine is HC-1's declared deliverable. Fields: coefficients, graded
pieces, the K1-chain-weight function, the initial-form/class map, and its laws
(ultrametric weight, additivity at weight, kills-weight-above, weight detection). -/
structure GradedCarrier (δ : ℕ+) where
  Coeff : Type                             -- slot coefficients B
  [coeffAdd : AddCommGroup Coeff]
  Gr : ℚ → Type                            -- D.3(e)(i)'s graded pieces
  [grAdd : ∀ γ, AddCommGroup (Gr γ)]
  w : Coeff → WithTop ℚ                    -- the K1-chain-weight function
  inγ : (γ : ℚ) → Coeff → Gr γ             -- the initial-form / class map
  w_add : ∀ B B', min (w B) (w B') ≤ w (B + B')
  inγ_add : ∀ (γ : ℚ) (B B'), (γ : WithTop ℚ) ≤ w B → (γ : WithTop ℚ) ≤ w B' →
    inγ γ (B + B') = inγ γ B + inγ γ B'    -- additivity at weight γ
  inγ_kills : ∀ (γ : ℚ) B, (γ : WithTop ℚ) < w B → inγ γ B = 0  -- kills weight above
  inγ_detects : ∀ (γ : ℚ) B, w B = (γ : WithTop ℚ) → inγ γ B ≠ 0  -- weight detection

/-- (R0-tower) carrier: the re-based classifier tower of one history — "built
afresh, NOT by scalar-extending the ℤ_p tower". Base shape F₁ = F_δ[x]/(φ̄), climb
F_{k+1} = F_k[z]/(ψ_k), residual factors OVER THE NEW BASE (the polynomials live
over the actual tower carriers). Laws split §A / §B1 / §B2-DEF for the ledger. -/
structure TowerData (δ : ℕ+) where
  len : ℕ
  Res : Fin (len + 1) → Type              -- F₁, …, F_{len+1}
  [resField : ∀ k, Field (Res k)]
  baseEmbed : ↥(Fsub p δ) →+* Res 0
  stepEmbed : ∀ k : Fin len, Res k.castSucc →+* Res k.succ
  φbar : Polynomial ↥(Fsub p δ)           -- §A's φ̄, over F_δ
  ψ : ∀ k : Fin len, Polynomial (Res k.castSucc)  -- residual factors ψ_k over F_k

/-- §A re-based, the typed base-shape laws: φ̄ monic irreducible OVER F_δ and
F₁ ≃ F_δ[x]/(φ̄) compatibly with the base embedding. -/
structure TowerData.BaseLaws {δ} (T : TowerData p δ) : Prop where
  monic : T.φbar.Monic
  irr : Irreducible T.φbar
  pres : ∃ e : T.Res 0 ≃+* AdjoinRoot T.φbar,
    ∀ x : ↥(Fsub p δ), e (T.baseEmbed x) = algebraMap _ _ x

/-- §B2-DEF (D.0) re-based, the typed climb laws: each ψ_k monic irreducible over
the ACTUAL stage field, each step the quotient presentation F_{k+1} = F_k[z]/(ψ_k). -/
structure TowerData.ClimbLaws {δ} (T : TowerData p δ) : Prop where
  monic : ∀ k, (T.ψ k).Monic
  irr : ∀ k, Irreducible (T.ψ k)
  pres : ∀ k, ∃ e : T.Res k.succ ≃+* AdjoinRoot (T.ψ k),
    ∀ x, e (T.stepEmbed k x) = AdjoinRoot.of _ x

/-- §B1 re-based, the typable residue ("the same construction run over the new
base"): finite stage carriers of characteristic p. The graded internals
(gr_w(A), L, T) are (R0-tower)-fenced to REL.1's pass — recorded, not typed. -/
structure TowerData.StageCarrierLaws {δ} (T : TowerData p δ) : Prop where
  fin : ∀ k, Finite (T.Res k)
  charP : ∀ k, CharP (T.Res k) p

/-- Counting interface for (REL.1-b) (fixed box degree n; nonempty carriers; vols
THROUGH the pinned BoxVol; loci indexed by their history). NOTE (FF2): the display's
LHS `#{f mod p^N ∈ S(H,Z)}` is NOT a field — it is DEFINED (`ReBased.count` below)
from the classifier locus and the cylinder partition, so no instance can supply a
count unrelated to any classifier. -/
structure REL1Counting (δ : ℕ+) (n : ℕ) where
  V : BoxVol p δ n                        -- vol_{O_δ}, cylinder-pinned
  Hist : Type                             -- re-based histories H
  histNe : Nonempty Hist
  Locus : Hist → Type                     -- digit loci Z in H's frame
  locusNe : ∀ H, Nonempty (Locus H)
  kIdx : Hist → ℕ                         -- k, top node index
  Nmin : (H : Hist) → Locus H → ℕ         -- N(H, Z)
  freshEvent : (H : Hist) → ℕ → Set (Fin n → ↥(O p δ))    -- E_fresh(ν_i)
  freshEvent_mem : ∀ H i, freshEvent H i ∈ V.events
  locusEvent : (H : Hist) → Locus H → Set (Fin n → ↥(O p δ))  -- Z as a box event
  locusEvent_mem : ∀ H Z, locusEvent H Z ∈ V.events
```

```lean
/-- The re-based theory carriers ((R0-box/tower/reads/ledger) as typed objects):
digit spaces are F_δ-valued (the O_δ-digit ATOM), jets expand box points into
digit coordinates (C.0's block expansion over F_δ), towers per history, frames
with transports, per-position alphabet dimensions a_δ — WIRED to (EQ-2)'s
`AlphabetData` via `posOfDigit`/`aDim_eq` (FF4) — pin sets, (ZC) statistic, the
base-free floor lines for DOM, and the height/block/floor carriers Lemma LST's
legs consume (FF1). -/
structure ReBased (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) (δ : ℕ+) (n : ℕ) where
  C : REL1Counting p δ n
  mOf : C.Hist → ℕ                        -- digit count of H's jet frame
  mOf_pos : ∀ H, 0 < mOf H
  jet : (H : C.Hist) → (Fin n → ↥(O p δ)) → (Fin (mOf H) → ↥(Fsub p δ))
  tower : C.Hist → TowerData p δ          -- (R0-tower), per history
  Frame : C.Hist → Type                   -- C.0.5's frames
  frameNe : ∀ H, Nonempty (Frame H)
  T : (H : C.Hist) → Frame H → Frame H →  -- the frame transports
      (Fin (mOf H) → ↥(Fsub p δ)) → (Fin (mOf H) → ↥(Fsub p δ))
  SHZ : (H : C.Hist) → C.Locus H → Set (Fin n → ↥(O p δ))   -- the classifier locus S(H,Z)
  SHZ_mem : ∀ H Z, SHZ H Z ∈ C.V.events
  digitLocus : (H : C.Hist) → C.Locus H → DigitSystem (mOf H) ↥(Fsub p δ)  -- Z as digit system
  aDim : (H : C.Hist) → Fin (mOf H) → ℕ   -- a_δ at each digit position ((EQ-2) def part)
  /-- (FF4) the (R0-ledger)↔(EQ-2) wiring: each digit position sits at an
  `AlphabetData` position class, and its per-digit exponent IS that class's a_δ —
  "|𝔸_δ| = p^{a_δ} per (EQ-2)'s re-based-span definition". EQ2law now speaks about
  the exponents c1 consumes; REL-n4's exponent leg tests exactly these. -/
  posOfDigit : (H : C.Hist) → Fin (mOf H) → AD.Pos
  aDim_eq : ∀ H i, aDim H i = AD.aDim δ (posOfDigit H i)
  /-- (CF9) PIN STATUS as a proper carrier: each coordinate's pin-status datum
  (C.0/C.0.5's "cardinality-and-STATUS statistics"), with the pinned set DEFINED
  from it — alphabet dimensions are ledger weights, not statuses. -/
  Status : Type
  pinStatus : (H : C.Hist) → Frame H → C.Locus H → Fin (mOf H) → Status
  constrained : Status → Prop
  pinnedIn : (H : C.Hist) → Frame H → C.Locus H → Finset (Fin (mOf H))
  pinnedIn_spec : ∀ H F Z i, i ∈ pinnedIn H F Z ↔ constrained (pinStatus H F Z i)
  zcStat : (H : C.Hist) → Frame H → C.Locus H → ℤ            -- C.1.5's (ZC) statistic
  lines : (H : C.Hist) → ℕ → Line         -- base-free floor lines (MovesC, D8)
  interiorEnd : C.Hist → ℕ
  /-- THE CInterface ATTACHMENT (D4(a)): the graded carrier this instance's §C
  statements quantify over. -/
  G : GradedCarrier p δ
  /-- LST carriers (FF1, upgraded at REV 4): absolute height, block assignment,
  floors, factor-interior blocks, the engine's floor downset — PLUS the objects
  the previously-fenced LST(i) clauses need: each coordinate's BASIS MONOMIAL in
  the carrier and each block's SLOT COEFFICIENT at a digit vector (the engine's
  weight is now `G.w (slotCoeff …)`, not a free field). -/
  ht : (H : C.Hist) → Fin (mOf H) → ℚ
  blkOf : (H : C.Hist) → Fin (mOf H) → ℕ
  floorC : (H : C.Hist) → Fin (mOf H) → ℚ
  floorB : (H : C.Hist) → ℕ → ℚ
  interiorB : (H : C.Hist) → ℕ → Prop
  floorSet : (H : C.Hist) → ℕ → Set (Fin (mOf H))
  mono : (H : C.Hist) → Fin (mOf H) → G.Coeff
  slotCoeff : (H : C.Hist) → ℕ → (Fin (mOf H) → ↥(Fsub p δ)) → G.Coeff
  /-- (CF8) the note's own interior anchor: "on the factor interior — where ALL
  FRESH CONTENT lives (C.1's rim bullet)" — constrained digits sit on
  factor-interior blocks, so `interiorB ≡ False` forces the degenerate all-free
  perimeter instead of silently discharging the LST legs. -/
  interior_fresh : ∀ H (F : Frame H) Z, ∀ i ∈ pinnedIn H F Z, interiorB H (blkOf H i)

/-- `#{ f mod p^N ∈ S(H, Z) }` — the (REL.1-b) LHS, DEFINED from in-corpus
vocabulary (FF2 repair: kills the free-count instances): the number of level-N
cylinder classes meeting the classifier locus. For N ≥ N(H,Z) these are exactly
the level-N residue points of S(H,Z). -/
noncomputable def ReBased.count {Sp AD δ n} (K : ReBased p Sp AD δ n)
    (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ) : ℕ :=
  Nat.card {W : Set (Fin n → ↥(O p δ)) // ∃ f ∈ K.SHZ H Z, W = cyl p δ N f}

/-! **THE CInterface, layer (b): per-lemma statement defs** (D4; CF18's
decomposition — ONE display per def, each its own unit). Each def's body is the
cited lemma's FULL statement over the carrier bundle; the fences are gone. -/

/-- §A re-based: the base tower shape over F_δ (φ̄ monic irr, F₁ = F_δ[x]/(φ̄)). -/
def SecAStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H, (K.tower H).BaseLaws
/-- §B1 re-based (CF16): the graded vocabulary is now TYPED — `K.G` carries the
pieces/class map/weight WITH their laws (its structure fields), so §B1's citation
is a typed pointer, not a fence; the statement asserts the stage-carrier laws AND
the block expansion's additivity into the carrier (slot coefficients additive in
the digit vector — the D.3(e) attachment). Localization L / degree-1 unit T ride
as HC-1 instantiation obligations, recorded in D4. -/
def SecB1Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  (∀ H, (K.tower H).StageCarrierLaws) ∧
  (∀ H (B : ℕ) (x y : Fin (K.mOf H) → ↥(Fsub p δ)),
    K.slotCoeff H B (x + y) = K.slotCoeff H B x + K.slotCoeff H B y)
/-- §B2-DEF re-based: the D.0 climb, residual factors OVER THE NEW BASE. -/
def SecB2Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H, (K.tower H).ClimbLaws
/-- Theorem C(a): classifier locus = jet-preimage of the digit-system locus. -/
def ThmCaStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H Z, K.SHZ H Z = (fun f => K.jet H f) ⁻¹' {x | (K.digitLocus H Z).IsSolution x}
/-- Theorem C(b) = (REL.1-b), LHS the DEFINED count (FF2): "#{ f mod p^N ∈ S(H,Z) }
= q_δ^{nN} · ∏_{i=0}^{k} vol(E_fresh(ν_i)) · vol(Z) for every N ≥ N(H, Z)". -/
def ThmCbStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ), K.C.Nmin H Z ≤ N →
    (K.count H Z N : ℚ) = (qq p δ : ℚ) ^ (n * N) *
      ((∏ i ∈ Finset.range (K.C.kIdx H + 1), K.C.V.vol (K.C.freshEvent H i)) *
        K.C.V.vol (K.C.locusEvent H Z))
/-- C.0.5 + PIN-WELLDEF: transports unitriangular; pin statistics frame-invariant —
cardinality AND STATUS (CF9: over the `Status` carrier, pinned sets DEFINED from
it) AND the aDim ledger-weights c1 consumes. -/
def C05Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H (F F' : K.Frame H), IsUnitriangular (K.T H F F') ∧
    ∀ Z, (K.pinnedIn H F Z).card = (K.pinnedIn H F' Z).card ∧
      Multiset.map (K.pinStatus H F Z) Finset.univ.val
        = Multiset.map (K.pinStatus H F' Z) Finset.univ.val ∧
      (K.pinnedIn H F Z).val.map (K.aDim H) = (K.pinnedIn H F' Z).val.map (K.aDim H)
/-- C.1: "each constrained digit contributing the factor |𝔸_δ|⁻¹ of its ATTAINABLE
alphabet" — the locus mass is the per-pinned-digit product. -/
def C1Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H (F : K.Frame H) Z, K.C.V.vol (K.C.locusEvent H Z) =
    ∏ i ∈ K.pinnedIn H F Z, ((p : ℚ) ^ (K.aDim H i))⁻¹
/-- C.1.5's (ZC) invariant: the statistic is transport/frame-invariant. -/
def C15Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H F F' Z, K.zcStat H F Z = K.zcStat H F' Z
/-- Lemma LST (level-set scale-typing), FULL statement (§C display MOVES 3728;
CF7 RESOLVED-BY-REARCHITECTURE — the previously-fenced clauses are typed over the
carrier): (i-a) TYPING: "ht(b, l) is the K1-chain weight of the coordinate's basis
monomial" — `G.w (mono i) = ht i`; (i-b) "w(B) = min{ht(b, l) : (b, l) ∈ blk(B),
y ≠ 0} (the iterated slot-minimum)"; (i-c) "the weight-γ initial form in_γ(B) is a
function of exactly the LEVEL SET L_γ(B)"; (ii) FLOOR CONSTANCY ON THE INTERIOR;
(iii) SELECTION via the ht-downset. -/
def LSTStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ (H : K.C.Hist),
    (∀ i, K.G.w (K.mono H i) = ((K.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ (B : ℕ) (x : Fin (K.mOf H) → ↥(Fsub p δ)),
      K.G.w (K.slotCoeff H B x) = (Finset.univ.filter fun i =>
        K.blkOf H i = B ∧ x i ≠ 0).inf fun i => ((K.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ (γ : ℚ) (B : ℕ) (x y : Fin (K.mOf H) → ↥(Fsub p δ)),
      (∀ i, K.blkOf H i = B → K.ht H i = γ → x i = y i) →
      K.G.inγ γ (K.slotCoeff H B x) = K.G.inγ γ (K.slotCoeff H B y)) ∧
    (∀ i, K.interiorB H (K.blkOf H i) → K.floorC H i = K.floorB H (K.blkOf H i)) ∧
    (∀ B, K.interiorB H B →
      K.floorSet H B = {i | K.blkOf H i = B ∧ K.ht H i ≤ K.floorB H B} ∧
      ∀ (γ' : ℚ), K.floorB H B < γ' →
        ∀ i, K.blkOf H i = B → K.ht H i = γ' → i ∉ K.floorSet H B)
/-- Lemma TYP: walk item (i)'s retyping (per-digit ADDITIVE on O_δ-digit blocks) +
TYP's graded leg at cardinality granularity: each digit position's ATTAINABLE
image has the alphabet's size p^{a_δ} ("SURJECTIVE onto the digit alphabet (image
= the additive span of the slot images, D.3(e)(i))"), tied to (EQ-2)'s data via
`aDim_eq`. F_δ-linearity stays EXPECTED, walked — not asserted (the note). -/
def TYPStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  (∀ H (i : Fin (K.mOf H)) (f g : Fin n → ↥(O p δ)),
    K.jet H (f + g) i = K.jet H f i + K.jet H g i) ∧
  (∀ H (i : Fin (K.mOf H)),
    Nat.card (Set.range fun f => K.jet H f i) = p ^ K.aDim H i)
/-- Lemma DOM: base-free floor domination, MovesC's `DomData` verbatim
("valuation geometry … carries over as written"). -/
def DOMStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H, ∀ i ≤ K.C.kIdx H, DomData (K.lines H) i (K.interiorEnd H)

/-- **THE CInterface, layer (b)-record: `CStatements`** — one field per §C lemma
the ledger cites; each field's type IS the named statement def. The note's clause
list, typed with no fence: "§A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b)
with C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM". -/
structure CStatements (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop where
  secA : SecAStmt p K
  secB1 : SecB1Stmt p K
  secB2 : SecB2Stmt p K
  thmCa : ThmCaStmt p K
  thmCb : ThmCbStmt p K
  c05PinWelldef : C05Stmt p K
  c1 : C1Stmt p K
  c15ZC : C15Stmt p K
  lst : LSTStmt p K
  typ : TYPStmt p K
  dom : DOMStmt p K

/-- **THE CInterface, layer (c): (REL.1) := `CStatements` at base δ** — the typed
mutatis-mutandis pointer [OPEN KERNEL — "a NEW THEOREM with its own verification
passes"]. Instantiating the carrier package = HC-1's deliverable; consumers
hypothesize per instance, ABSOLUTE index displayed per site. -/
def REL1 (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  CStatements p Sp AD δ n K
/-- (CF17) the pass's full deliverable: EQ-1 is "a named checkpoint of REL.1's
re-scoping pass, where it is walked" — attached, typed. -/
def REL1PassDeliverable (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  REL1 p Sp AD δ n K ∧ EQ1 Sp
/-- (CF17) (EQ-2)'s "OPEN, REL.1-conditional" status, typed. -/
def EQ2lawIfREL1 (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  REL1 p Sp AD δ n K → EQ2law p AD
```

```lean
/-! ## REL.2 (file Rel2.lean; units R14–R17) -/

/-! **(REL.2a) — SIX SUB-DELIVERABLES (a1)–(a6)** (CF19's decomposition: one
checklist item per structure, composed by the bundle; "nothing short of all six
items is '(a) stated'"). Inhabitation story: the future (a)-pass. -/

/-- (a1) DOMAIN + MEASURABILITY (FF5(i)): the free base coordinates (ℓ, i)
(infinitely many — Σ_c fixes finitely many digits), the identification with the
"measurable product of O_δ-digit spaces" ((R0-box)'s ATOM), the product-side
event algebra with digit cylinders, and event-algebra compatibility. -/
structure REL2a1 (S : Setting p) where
  freeCoords : Set (ℕ × ℕ)
  freeCoords_inf : freeCoords.Infinite
  domIdent : S.Cont ≃ (freeCoords → ↥(Fsub p S.δ))
  prodEvents : Set (Set (freeCoords → ↥(Fsub p S.δ)))
  prodCyl_mem : ∀ (E : Finset (ℕ × ℕ)) (v : (ℕ × ℕ) → ↥(Fsub p S.δ)),
    {x | ∀ c : freeCoords, (c : ℕ × ℕ) ∈ E → x c = v c} ∈ prodEvents
  domIdent_meas : ∀ W, W ∈ prodEvents ↔ (fun f => domIdent f) ⁻¹' W ∈ S.AmbEvents

/-- (a2) TARGET integrality of `d_j^rel := d_j/δ_j^rel` — "part of the obligation,
EXPECTED from the tower data, walked in (a)'s pass" (E·F ∣ d_j route EXPECTED only). -/
structure REL2a2 (S : Setting p) : Prop where
  drel_dvd : (S.δrel : ℕ) ∣ (S.d : ℕ)
  drel_pos : 0 < S.dRel

/-- (a3) EMBEDDING CONVENTION: the named F_{δ_j} ↪ (tower residue field) embedding
and the canonical-lift convention, PINNED to Mathlib's Teichmüller (a field). -/
structure REL2a3 (S : Setting p) where
  TowerRes : Type
  [towerResField : Field TowerRes]
  embed : ↥(Fsub p S.δabs) →+* TowerRes
  teich : ↥(Fsub p S.δabs) → ↥(O p S.δabs)
  teich_pin : ∀ x, ((teich x : ↥(O p S.δabs)) : Wbar p)
    = WittVector.teichmuller p (x : Kbar p)

/-- (a4) FORMULA: the map Θ_j itself, on (a1)'s coordinates. -/
structure REL2a4 (S : Setting p) (A1 : REL2a1 p S) where
  Θ : (A1.freeCoords → ↥(Fsub p S.δ)) → (Fin S.dRel → ↥(O p S.δabs))

/-- (a5) FRAME COMPATIBILITY over the AMBIENT family (CF10 repair): the transports
are S's OWN C.0.5 family (`S.reframe`, supplied by the ambient theory), conjugated
to the digit side through (a1) — an inhabitant can no longer substitute a private
identity-only family. Deliverables: the target-side transports and the displayed
commutation, with unitriangularity anchors on BOTH sides (FF7; `CoordPrec` = C.0's
order on the free coordinates, Fin-order on the target coefficients). -/
structure REL2a5 (S : Setting p) (A1 : REL2a1 p S) (A4 : REL2a4 p S A1) where
  tgtOf : S.FrameC → S.FrameC →
    ((Fin S.dRel → ↥(O p S.δabs)) ≃ (Fin S.dRel → ↥(O p S.δabs)))
  ambT_unitri : ∀ (F F' : S.FrameC) (x y : A1.freeCoords → ↥(Fsub p S.δ))
      (c : A1.freeCoords),
    (∀ c' : A1.freeCoords, CoordPrec (c' : ℕ × ℕ) (c : ℕ × ℕ) → x c' = y c') →
    A1.domIdent (S.reframe F F' (A1.domIdent.symm x)) c - x c
      = A1.domIdent (S.reframe F F' (A1.domIdent.symm y)) c - y c
  tgtT_unitri : ∀ (F F' : S.FrameC) (x y : Fin S.dRel → ↥(O p S.δabs))
      (j : Fin S.dRel),
    (∀ j' < j, x j' = y j') → tgtOf F F' x j - x j = tgtOf F F' y j - y j
  frame_compat : ∀ (F F' : S.FrameC) (f : S.Cont),
    A4.Θ (A1.domIdent (S.reframe F F' f)) = tgtOf F F' (A4.Θ (A1.domIdent f))

/-- (a6) READ DICTIONARY, PER READ FIELD (CF11 repair): (R0-reads)' node-datum
fields — "SHAPE (e, h, g, μ), anchor a, SIDE endpoints/height and stride
positions, DIGITS (d_j), branch factor ψ, recentering lifts" — with the
integer/lattice fields PRESERVED (the SAME GRAMMAR) and the residue-datum fields
(digits, ψ, lifts) transported by DECLARED per-read maps (RECONSTRUCTED over the
re-based tower — no canonical inclusion, so a transport map, never an equality). -/
structure REL2a6 (S : Setting p) (Sp : SpeciesSyntax) where
  AmbRead : Type
  ambReadNe : Nonempty AmbRead
  TgtRead : Type
  readDict : AmbRead → TgtRead
  readDict_inj : Function.Injective readDict
  ambLetter : AmbRead → Sp.Letter
  tgtLetter : TgtRead → Sp.Letter
  readDict_letter : ∀ r, tgtLetter (readDict r) = ambLetter r
  ambShape : AmbRead → ℕ × ℕ × ℕ × ℕ
  tgtShape : TgtRead → ℕ × ℕ × ℕ × ℕ
  readDict_shape : ∀ r, tgtShape (readDict r) = ambShape r
  ambAnchor : AmbRead → ℕ
  tgtAnchor : TgtRead → ℕ
  readDict_anchor : ∀ r, tgtAnchor (readDict r) = ambAnchor r
  ambSide : AmbRead → (ℚ × ℚ) × List ℕ
  tgtSide : TgtRead → (ℚ × ℚ) × List ℕ
  readDict_side : ∀ r, tgtSide (readDict r) = ambSide r
  AmbResDat : AmbRead → Type
  TgtResDat : TgtRead → Type
  resDict : ∀ r, AmbResDat r → TgtResDat (readDict r)

/-- **(REL.2a) the bundle** — all six items or nothing. -/
structure REL2a (S : Setting p) (Sp : SpeciesSyntax) where
  a1 : REL2a1 p S
  a2 : REL2a2 p S
  a3 : REL2a3 p S
  a4 : REL2a4 p S a1
  a5 : REL2a5 p S a1 a4
  a6 : REL2a6 p S Sp

/-- **(REL.2b) NORMALIZATION / JACOBIAN** [OPEN KERNEL]: "for every REL.1-measurable
continuation event W over O_{δ_j} (digit cylinders generate — V's `cyl_mem`),
μ( Θ_j⁻¹(W) │ Σ_c ) = vol_{O_{δ_j}}(W)", with the "only for cells with μ(Σ_c) > 0"
proviso as guard. Non-vacuous: `V.events` contains univ and every cylinder, and
`V.vol` is cylinder-pinned. FF5(ii): the Θ-pullback of every event is required IN
the ambient event algebra — the Θ-measurability half of "the PUSHFORWARD of the
conditional continuation measure … IS the normalized O_{δ_j}-box measure". -/
def REL2b (S : Setting p) (Sp : SpeciesSyntax) (A : REL2a p S Sp)
    (V : BoxVol p S.δabs S.dRel) : Prop :=
  0 < S.cellMass →
    ∀ W ∈ V.events,
      (fun f => A.a4.Θ (A.a1.domIdent f)) ⁻¹' W ∈ S.AmbEvents ∧
      S.condMass ((fun f => A.a4.Θ (A.a1.domIdent f)) ⁻¹' W) = V.vol W

/-- (b) WITH ITS REL.1 CONDITIONALITY TYPED: the target measure IS the REL.1
theory's (`RB.C.V`), and REL.1 at (δ_j, d_j^rel) rides as an explicit conjunct —
"EVERY consumer below is conditional on REL.1, displayed per site". -/
def REL2b_linked (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) (RB : ReBased p Sp AD S.δabs S.dRel) : Prop :=
  REL1 p Sp AD S.δabs S.dRel RB ∧ REL2b p S Sp A RB.C.V

/-- **(EQ-3) CONDITIONAL MASSES TRANSPORTED** — "REL.2(b) verbatim … no weaker
reading (bijection-only, or level-matching without normalization) counts."
(Alias inherits the finding-9 repair.) -/
abbrev EQ3 (S : Setting p) (Sp : SpeciesSyntax) (A : REL2a p S Sp)
    (V : BoxVol p S.δabs S.dRel) : Prop := REL2b p S Sp A V
```

```lean
/-- **(REL.2d) LIFT-POLICY COMPATIBILITY — the acceptance-criterion COMMUTATIVE
SQUARE**, with the node-data correspondence SPECIFIED (findings 11/12): the
horizontal `nodeCorr` must preserve the species word ((EQ-1) letters), transport
the reads through (a6)'s dictionary, and preserve τ-verdicts; the (EQ-2) alphabet
wiring is the `posOf` assignment into `AD`; the (a3) lift policy enters through
`A.teich_pin` (a field of `A`). Also supplies the prescribed-subtree
identification, without which "(SIB-Oδ) below is ill-typed". -/
structure REL2d (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) where
  AmbTree : Type                          -- b_j's continuation subtrees of T_can(f)
  ambTreeNe : Nonempty AmbTree
  ambTcan : S.Cont → AmbTree
  TgtTree : Type                          -- the O_{δ_j}-engine's canonical trees
  tgtTcan : (Fin S.dRel → ↥(O p S.δabs)) → TgtTree
  nodeCorr : AmbTree → TgtTree            -- the SPECIFIED correspondence
  /-- "The square commutes for every f ∈ Σ_c." -/
  square : ∀ f : S.Cont, nodeCorr (ambTcan f) = tgtTcan (A.a4.Θ (A.a1.domIdent f))
  /-- node-data content of the correspondence: species word preserved … -/
  ambWord : AmbTree → List Sp.Letter
  tgtWord : TgtTree → List Sp.Letter
  corr_word : ∀ t, tgtWord (nodeCorr t) = ambWord t
  /-- … reads transported via (a6)'s dictionary … -/
  ambReads : AmbTree → List A.a6.AmbRead
  tgtReads : TgtTree → List A.a6.TgtRead
  corr_reads : ∀ t, tgtReads (nodeCorr t) = (ambReads t).map A.a6.readDict
  /-- … τ-verdicts preserved … -/
  ambVerdict : AmbTree → List Bool
  tgtVerdict : TgtTree → List Bool
  corr_verdict : ∀ t, tgtVerdict (nodeCorr t) = ambVerdict t
  /-- … and (EQ-2)'s alphabets: each target read sits at an `AD` position class. -/
  posOf : A.a6.TgtRead → AD.Pos
  /-- (CF12) posOf is CONSTRAINED: the position class assigned to a target read
  carries that read's species letter — the (EQ-2)-alphabet wiring is the read's
  own, not a free assignment. -/
  posOf_letter : ∀ r, AD.posLetter S.δabs (posOf r) = A.a6.tgtLetter r
  /-- canonical O_{δ_j}-side prescribed subtrees, T_j's identification, and the
  target realization predicate ((W1)'s reading inherited from [1]/[3t]). -/
  TgtSub : Type
  subtreeCorr : S.PTree → TgtSub
  TgtRealizes : TgtTree → TgtSub → Prop

/-- **(REL.2e) β-IDENTIFICATION, (e1)–(e5)** (findings 13/14 repairs: `entryFirst`
FIXED per branch; `consumed` = the prescriptions [3]'s entry actually consumes;
(e1)↔(a6) compatibility typed). Inhabitation story: the future (e)-pass with [3]'s
tables in hand. -/
structure REL2e (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) (D : REL2d p S Sp AD A) where
  /-- (e1) REL.1-side states over O_{δ_j} + the dictionary from τ_j(c) … -/
  RelState : Type
  relStateNe : Nonempty RelState
  stateDict : S.StateIdx → RelState
  /-- … "compatible with (a6)'s read dictionary", TYPED: states carry their
  defining reads; the dictionary transports them letter-for-letter. -/
  stateReadsAmb : S.StateIdx → List A.a6.AmbRead
  stateReadsRel : RelState → List A.a6.TgtRead
  stateDict_compat : ∀ s, stateReadsRel (stateDict s) = (stateReadsAmb s).map A.a6.readDict
  /-- [3]'s table, in [3]'s own keying: (first index, state, argument) ↦ entry. -/
  β : ℕ → S.StateIdx → ℕ → ℚ
  /-- (e4) the first index e_j, FROM b_j's DATA — one value per branch (finding 13).
  (CF14: the consumed-prescription set is NOT a field — it is a parameter of the
  (e)-Props below, supplied by [3]/MovesS exactly like `tableConv`.) -/
  entryFirst : ℕ

/-- (e4)'s agreement with [3]'s table convention, TYPED against the convention as
a parameter ([3]/MovesS's export — D5): a typed claim, not prose. -/
def REL2e.e4agrees {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (tableConv : ℕ → Prop) : Prop := tableConv E.entryFirst
/-- (e4)'s CANDIDATE ["candidate: (a2)'s O_{δ_j}-degree d_j^rel — owed, not
assumed"]. (CF13) DEMOTED: a NAMED CANDIDATE definition only — NOT an obligation,
REMOVED from D7's hypothesis list; NO consumer may hypothesize it. (e4)'s
obligation is `e4agrees` alone. -/
def REL2e.firstIdxCandidate {S Sp AD A D} (E : REL2e p S Sp AD A D) : Prop :=
  E.entryFirst = S.dRel
/-- (e5) first disjunct: "the entry's indices must DETERMINE the prescribed
subtree T_j". (CF14) `consumed` — the prescriptions [3]'s tables actually consume
at this key — is a PARAMETER supplied by [3]/MovesS's export, like `tableConv`:
choosing it here was the vacuity Codex flagged. Re-keying stays a statement-fence
event (D5). -/
def REL2e.determines {S Sp AD A D} (_E : REL2e p S Sp AD A D)
    (consumed : Set S.PTree) : Prop :=
  ∀ T ∈ consumed, ∀ T' ∈ consumed, T = T'
/-- (e3) MASS = ENTRY, stated GIVEN (e5): β_{e_j, τ_j(c)}(p^{δ_j}) IS **the REL.1
mass** (FF6 `_linked`: the vol is `RB.C.V` of a REL1-hypothesized package;
FF5(iii): the realization event ∈ `RB.C.V.events`; CF14: `consumed` is [3]'s
parameter). -/
def REL2e.massEqEntry {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (consumed : Set S.PTree) (RB : ReBased p Sp AD S.δabs S.dRel) : Prop :=
  REL1 p Sp AD S.δabs S.dRel RB ∧ E.determines p consumed ∧ ∀ T ∈ consumed,
    {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)} ∈ RB.C.V.events ∧
    E.β E.entryFirst S.τ (S.βarg p) =
      RB.C.V.vol {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}
/-- (CF20) THE COLLECTING CONJUNCTION — one Prop gathering the (e)-obligations
((e2) is the definitional `βarg_eq`; (e1) is E's data + `stateDict_compat` field):
the single hypothesis interface consumers cite. -/
def REL2eObligations {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (tableConv : ℕ → Prop) (consumed : Set S.PTree)
    (RB : ReBased p Sp AD S.δabs S.dRel) : Prop :=
  E.e4agrees p tableConv ∧ E.determines p consumed ∧ E.massEqEntry p consumed RB
```

```lean
/-- (e2) as the checkable identity behind `Setting.βarg`: "the β-argument is
p^{δ_j} with δ_j ABSOLUTE …, = q_δ^{δ_j^rel}" (provable via `qq_mul`, part of R5). -/
theorem βarg_eq (S : Setting p) : S.βarg p = qq p S.δ ^ (S.δrel : ℕ) := qq_mul p _ _

/-! ## R.2 — (SIB-Oδ) (file Sib.lean; units R22–R23) -/

/-- **(SIB-Oδ)** [FENCED = REL.1 + REL.2(a)+(b)+(d), composed; derived nowhere yet].
"For EVERY realized prefix η, EVERY branching cell c, EVERY branch b_j —
simultaneously over every unramified O_δ that arises (all δ ≥ 1 in one statement)
— the event S_j IS an O_{δ_j}-statement", with (REL.2b)'s pricing
  μ( S_j │ Σ_c ) = vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j },
the right side a REL.1-THEORY mass (the REL.1 conjunct is explicit — finding 20).
Quantifier = the realized `SettingsFamily` (nonempty, root δ = 1, descent-closed
with absolute re-indexing — findings 19/20); the positive-cell guard is the note's
own conditioning proviso; the first conjunct of the ∀T clause is the "S_j IS an
O_{δ_j}-statement" typing itself (S_j = the Θ-pullback of the target realization
event); the second is the pricing, at a realization event required IN
`RB.C.V.events` (FF5(iii)) so the REL.1 measure laws bind there.
REV 4 (CF1/CF2): the quantifier is over a `mem_pos`-restricted family (the
conditioning sites — the zero-mass singleton is dead), the identification data is
ONE COHERENT PACKAGE FUNCTION over the whole family with ONE (Sp, AD) — (EQ-1)'s
same-syntax-over-every-base — and the RECURSION CLAUSE is now TYPED COMPOSITION:
each descendant's AMBIENT theory IS the parent's TARGET theory (same base index by
`desc_amb`, same box degree, same carrier package up to the index transport) —
"the obligations must COMPOSE across nested base changes"; `O_chain` supplies the
literal subring chain TREE-EXP's induction consumes. -/
structure SIBPkg (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) (S : Setting p) where
  A : REL2a p S Sp
  D : REL2d p S Sp AD A
  ambDeg : ℕ                                    -- the ambient box degree at S's cell
  ambK : ReBased p Sp AD S.δ ambDeg             -- the AMBIENT REL.1 carrier (base O_δ)
  RB : ReBased p Sp AD S.δabs S.dRel            -- the TARGET REL.1 carrier (base O_{δ_j})

def SIBOdelta (F : SettingsFamily p) : Prop :=
  ∃ (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (pkg : ∀ S ∈ F.mem, SIBPkg p Sp AD S),
    ∀ S (hS : S ∈ F.mem), 0 < S.cellMass →
      REL1 p Sp AD S.δ (pkg S hS).ambDeg (pkg S hS).ambK ∧      -- ambient REL.1 (δ = 1: verbatim)
      REL1 p Sp AD S.δabs S.dRel (pkg S hS).RB ∧                -- target REL.1
      REL2b p S Sp (pkg S hS).A (pkg S hS).RB.C.V ∧
      (∀ T : S.PTree,
        {g | (pkg S hS).D.TgtRealizes ((pkg S hS).D.tgtTcan g) ((pkg S hS).D.subtreeCorr T)}
            ∈ (pkg S hS).RB.C.V.events ∧
        S.SEvent T = (fun f => (pkg S hS).A.a4.Θ ((pkg S hS).A.a1.domIdent f)) ⁻¹'
            {g | (pkg S hS).D.TgtRealizes ((pkg S hS).D.tgtTcan g) ((pkg S hS).D.subtreeCorr T)} ∧
        S.condMass (S.SEvent T) =
          (pkg S hS).RB.C.V.vol
            {g | (pkg S hS).D.TgtRealizes ((pkg S hS).D.tgtTcan g) ((pkg S hS).D.subtreeCorr T)}) ∧
      -- (CF2) COMPOSITION across nested base changes: descendant ambient = parent target
      (∀ (T : S.PTree) (S' : Setting p) (hS' : S' ∈ F.desc S hS T),
        (pkg S' (F.desc_sub S hS T hS')).ambDeg = S.dRel ∧
        HEq (pkg S' (F.desc_sub S hS T hS')).ambK (pkg S hS).RB)

/-- R23: the recursion clause's ring-side witness — "a branch of relative
accumulated degree δ″ at ambient O_{δ_j} targets O_{δ_j·δ″}, literally a subring
chain in W(F̄_p)". (Family-closure is `SettingsFamily.desc*`; this is the
ring-theoretic half, not a substitute — finding 20.) -/
theorem O_chain (S : Setting p) (δ'' : ℕ+) :
    O p S.δ ≤ O p S.δabs ∧ O p S.δabs ≤ O p (S.δabs * δ'') := sorry

/-! ## R.3 — (REL.3): NO LEAN OBJECT (finding 21; blueprint D6).
"The [4]-side displays (SQ.0–SQ.2 …) DO NOT EXIST YET — … so no theorem statement
is possible here." When [4] drafts SQ.0–SQ.2, REL.3's revision restates each
consumed display verbatim, base re-scoped to O_δ (ABSOLUTE indices), and enters
this corpus as NEW AUDITED UNITS. Discipline fixed now (plan): each consumed leg
β_m(p^δ) must arrive as a CERTIFIED vol_{O_δ}-statement (a `REL1`-conditional
theorem about `BoxVol`-masses), NEVER the formal substitution q ↦ q^δ in a
ℤ_p-display. This comment block is the whole of REL.3 in MovesR. -/

/-! ## Elaboration checks (per D9) -/
section Elab
-- Carrier instances (honest trivial cases only). REV-4 note: a trivial
-- `SettingsFamily` now needs a POSITIVE-mass member (mem_pos + ne) — use
-- cellMass := 1, condMass := indicator laws; desc _ _ _ := ∅ stays lawful.
--   example : Setting 2 := ⟨…, cellMass := 1, …, FrameC := PUnit, ⟨⟨⟩⟩,
--     reframe := fun _ _ => id, …⟩
--   example : SettingsFamily 2 := singleton on the above (mem_pos by rfl-arith)
--   example : SpeciesSyntax := ⟨PUnit, fun _ => (1,1,1,1), PUnit, fun _ => ⟨⟩,
--     PUnit, fun _ => ⟨⟩, injective-into-constant …, fun _ => ∅⟩  -- empty menus OK (CF3)
--   example : AlphabetData 2 Sp₀ := degenerate-lawful (alpha = closure of range of
--     the zero slotMap = {0}; card_eq : 1 = 2^0; aDim ≡ 0)
-- Obligation/deliverable structures: #check only (inhabitation = the pass/HC-1):
--   #check @GradedCarrier  #check @CStatements  #check @REL1  #check @LSTStmt
--   #check @REL2a  #check @REL2b_linked  #check @REL2d  #check @REL2eObligations
--   #check @SIBPkg  #check @SIBOdelta  #check @BoxVol  #check @ReBased.count
end Elab
end MovesR
```

SKELETON STATUS: NORMATIVE FOR CONTENT, not character-exact — E-phase fixes syntax
(instance-field bracketing, `Fin 0`-index forms, implicit-argument threading,
namespace qualification for `DigitSystem`/`IsUnitriangular`/`Line`/`DomData`)
WITHOUT changing any quantifier, equality, guard, or field list; anything beyond
syntax re-enters the audit loop (statement fence).

## 2. Unit specs (41 units; compact REV-4 format — id · statement · moves_ref key · deps · difficulty)

Files/import order: `Base` → `Interface` → `Eq` → `CInt` (GradedCarrier + statement
defs + CStatements) → `Rel1` → `Rel2` → `Sib`; `Defs.lean` re-export shim. Per-unit
acceptance: definitions land verbatim-from-skeleton + D9 elaboration compiles.
moves_ref keys quote §R-LEDGER (rev 5) unless marked §C (= the LST/TYP/DOM displays
at MOVES 3728–3831, consulted sources per the adjudication).

BASE (U1–U6; provable U2–U6):
- U1 base_defs: `Kbar/Wbar/Fsub/O/qq/relExt/cyl` · "F_m is THE subfield of order
  p^m and O_m := W(F_m) ⊂ W(F̄_p)" · — · easy.
- U2 Fsub_le · U3 O_le: nesting · "compose LITERALLY as subrings" · U1 · medium.
- U4 relExt_comp (`rfl`/`mul_assoc`/`O_le_relExt`) · "'(O_δ)_{δ′} = O_{δδ′}' is
  bookkeeping inside W(F̄_p)" · U1,U3 · easy.
- U5 qq_mul + βarg_eq · "q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}" + (e2) · U1,U7 · easy.
- U6 Fsub_card: `Nat.card ↥(Fsub p m) = p^m` · "THE subfield of order p^m" · U1 ·
  hard (wave-3).

INTERFACE (U7–U8):
- U7 Setting + δabs/dRel/βarg + FrameC/reframe (CF10's ambient family) + measure
  laws · the SETTING paragraph + "frame Ψ_η" · U1 · medium.
- U8 SettingsFamily + mem_pos (CF1, note-checked: the (b) proviso's "the only
  cells any (SIB) display conditions on") + desc closure · "(SIB-Oδ)" quantifier +
  recursion clause · U7 · medium.

EQ (U9–U12; provable U12):
- U9 SpeciesSyntax (shape/side/poly + letter_det — CF4; menuNe REMOVED — CF3) +
  EQ1 · "(EQ-1) … SAME finite syntax … never the letter set" · — · medium.
- U10 AlphabetData + slotMap/alpha_attain (CF5) + posLetter/Stable · "(EQ-2)
  DEFINITION (unconditional): … attainable additive image/span of the RE-BASED
  slot maps" · U1,U9 · medium.
- U11 EQ2law (BOTH conjuncts — F_δ-linearity + a_δ = δ·a, CF6) · "the re-based
  piece maps are F_δ-linear and a_δ = δ·a" (pinned domain) · U10 · easy-medium.
- U12 EQ2law_card · "|𝔸_δ| = q_δ^a = |𝔸|^δ" · U5,U11 · easy (provable).

CINTERFACE (U13–U29; one display per unit — CF18):
- U13 BoxVol + events_level (CF15: Haar characterized on the WHOLE event class;
  (g7)'s determination-radius discipline cited) · "(R0-box) … vol_{O_δ}(O_δ^n)=1;
  … q_δ^{nN} residue points" · U1 · medium.
- U14 GradedCarrier (D4(a): Coeff/Gr/w/inγ + 4 laws; ≤10 fields, no construction;
  instantiation = HC-1) · "(R0-tower) graded rings … D.3(e)(i)'s graded piece"
  (via §C consumption) · — · medium.
- U15 TowerData + Base/Climb/StageCarrier laws · "(R0-tower) F₁ := F_δ[x]/(φ̄) …
  F_{k+1} = F_k[z]/(ψ_k) … built afresh" · U1 · medium.
- U16 REL1Counting (no count field — FF2) · "(REL.1-b)" carriers · U13 · easy.
- U17 ReBased (carriers: jet/tower/frames/Status+pinStatus (CF9)/aDim wiring
  (FF4)/G attachment/LST carriers + mono/slotCoeff/interior_fresh (CF8)) +
  `ReBased.count` def (FF2) · (R0-box/tower/reads/ledger) · U9,U10,U14,U15,U16 ·
  hard (carrier only — no Props beyond laws).
- U18 SecAStmt · §A base shape · U17 · easy. — U19 SecB1Stmt (CF16: graded
  vocabulary typed via G; slotCoeff additivity) · "§B1 … same construction run
  over the new base" · U17 · easy-medium. — U20 SecB2Stmt · D.0 climb · U17 · easy.
- U21 ThmCaStmt · "Theorem C(a)" locus = jet-preimage · U17 · easy.
- U22 ThmCbStmt · "(REL.1-b)" verbatim over the DEFINED count · U17 · medium.
- U23 C05Stmt (unitri + card AND STATUS multiset (CF9) + aDim multiset) ·
  "C.0.5/PIN-WELLDEF … cardinality-and-status statistics" · U17 · medium.
- U24 C1Stmt · "(R0-ledger) … factor |𝔸_δ|⁻¹ of its ATTAINABLE alphabet" · U17 ·
  easy. — U25 C15Stmt · "C.1.5's (ZC) invariant" · U17 · easy.
- U26 LSTStmt (FULL: chain-weight typing + slot-min + in_γ/level-set + interior
  constancy + selection — CF7 resolved, no fence) · §C Lemma LST (i)/(ii)/(iii),
  MOVES 3728 · U14,U17 · hard (typing).
- U27 TYPStmt (additivity + attainable-image cardinality = p^{a_δ}) · §C Lemma
  TYP + walk item (i) · U17 · medium.
- U28 DOMStmt · §C Lemma DOM via MovesC `DomData` ("valuation geometry … carries
  over as written") · U17 · easy.
- U29 CStatements + REL1 (:= CStatements at δ — the typed mutatis-mutandis
  pointer) + REL1PassDeliverable/EQ2lawIfREL1 (CF17 attachments) · "(REL.1) …
  hold over O_δ … MUTATIS MUTANDIS" + (EQ-1)/(EQ-2) status lines · U18–U28 · easy.

REL.2 (U30–U39; one checklist item per unit — CF19/CF20):
- U30 REL2a1 (a1 + FF5(i)) · "(a1) DOMAIN … measurable product" · U7 · medium.
- U31 REL2a2 (a2) · "(a2) … integrality of d_j^rel" · U7 · easy.
- U32 REL2a3 (a3 + teich_pin) · "(a3) EMBEDDING CONVENTION … Teichmüller" · U1 ·
  easy-medium.
- U33 REL2a4 (a4) · "(a4) FORMULA: … Θ_j itself" · U30 · easy.
- U34 REL2a5 (a5 over the AMBIENT family — CF10; unitri anchors — FF7) · "(a5) …
  C.0.5's unitriangular transports" · U7,U30,U33 · medium.
- U35 REL2a6 (a6 PER READ FIELD — CF11: shape/anchor/side preserved, residue-datum
  transports declared) · "(a6) READ DICTIONARY … displayed per read field" +
  (R0-reads) · U9 · medium.
- U36 REL2a bundle · "nothing short of all six items" · U30–U35 · easy.
- U37 REL2b (+ FF5(ii) membership) + REL2b_linked + EQ3 · "(REL.2b)" display +
  "(EQ-3) … REL.2(b) verbatim" · U13,U29,U36 · medium.
- U38 REL2d (square + word/reads/verdict corr + posOf_letter — CF12) · "(REL.2d)
  … COMMUTATIVE SQUARE … SPECIFIED node-data correspondence" · U36,U9,U10 · hard.
- U39 REL2e + e4agrees/firstIdxCandidate(demoted — CF13)/determines/massEqEntry
  (consumed = [3]'s parameter — CF14) + REL2eObligations (CF20 conjunction) ·
  "(REL.2e) … (e1)–(e5)" · U29,U36,U38 · medium-hard.

SIB (U40–U41; provable U41):
- U40 SIBPkg + SIBOdelta (family package function + ambient/target REL1 + the CF2
  composition clause: descendant ambient = parent target, HEq up to index
  transport) · "(SIB-Oδ)" + "the obligations must COMPOSE across nested base
  changes" · U8,U29,U36,U37,U38 · hard.
- U41 O_chain · "literally a subring chain in W(F̄_p)" · U3,U7 · easy (provable).

(REL.3: NO UNIT — D6. REL.2(c), REL-n4, PREDICTED brackets: non-units, D6.)

## 3. Audit notes (wave-2 re-audit; budget: exactly one pass)

- FAITHFULNESS ANCHORS: every docstring quotes the rev-5 display it encodes; the
  moves_refs above are the check keys. Only `theorem`s: U2–U6, U12, U41 (base-index
  bookkeeping + the card fact + one hypothesis-conditional pow identity).
- DELIBERATE RESIDUAL WIDENINGS (each recorded): (i) `Setting` absorbs η/Σ_c/b_j
  into carriers-with-laws; the realized quantifier is `SettingsFamily` (supplied by
  the ambient theory; closure typed; conditioning sites per `mem_pos`).
  (ii) SUPERSEDED AT REV 4: the §B1/LST fences are GONE — the CInterface types the
  graded vocabulary (`GradedCarrier`) and each cited lemma's full statement
  (`*Stmt` defs); what remains recorded is that the interface's INSTANTIATION from
  the OM engine is HC-1's deliverable (localization L / degree-1 unit T ride
  there), not this corpus's.
  (iii) (e5)'s second disjunct (re-keying) is a statement-fence event, not a Prop
  disjunct (D5). (iv) WITHDRAWN at REV 3 (FF1); the rev-4 `LSTStmt` types ALL
  legs including the formerly-fenced clauses.
  (v) free-data relativity (FF7), NARROWED at REV 4: the ambient engine's
  transports are no longer inhabitant-chosen ((a5) quantifies over `S.reframe`,
  CF10); trees/reads/floors remain free data constrained by their typed laws
  (anchors, preservation, cylinder pins, teich_pin, `posOf_letter`, `mem_pos`,
  `interior_fresh`, attainability). Law-respecting junk remains constructible
  exactly where the engine has no Lean form; D7 says this accurately; full pinning
  = HC-1 + the REL.1 pass.
- CROSS-NOTE WATCHES INHERITED: (W1) `SEvent`/`TgtRealizes` stay opaque — every
  MovesR statement is neutral to the [1]/[3t] "realizes" pin; the pinned reading
  lands as the supplier's definition at the CL-10 sync, no statement changes.
  (W2) absolute indices enforced by construction (`δabs`, `βarg`, `relExt`).
- PLAN-SYNC FLAG (note R.1): CL-8 owes the (e) leg + the five-count; MovesR carries
  the five-obligation convention ((c) absent by re-homing).
- CONSUMER EDGES: MovesT consumes `SIBOdelta`/`Setting`/`SettingsFamily`/`O_chain`;
  MovesS consumes `REL2e` + `βarg_eq` and EXPORTS `tableConv` AND `consumed`
  ((e4)'s and (e5)'s parameters — CF14); MovesU consumes the future REL.3 units
  (none yet — D6); MovesV cites `REL1` (= `CStatements`); HC-1 owes the
  `GradedCarrier`/`ReBased` instantiation. Import direction: those corpora import
  MovesR, never conversely.

## 4. File map + status ledger

  lean/LeanUrat/MovesR/Base.lean       U1–U6   (defs + 5 provable lemmas + card)
  lean/LeanUrat/MovesR/Interface.lean  U7–U8   (Setting+FrameC+laws, SettingsFamily+mem_pos)
  lean/LeanUrat/MovesR/Eq.lean         U9–U12  (SpeciesSyntax+grammar, AlphabetData+spans, EQ-1/2)
  lean/LeanUrat/MovesR/CInt.lean       U13–U29 (BoxVol, GradedCarrier, TowerData, counting,
                                                ReBased+count, the 11 *Stmt defs, CStatements+REL1)
  lean/LeanUrat/MovesR/Rel2.lean       U30–U39 ((a1)–(a6)+bundle, (b)+EQ-3, (d), (e))
  lean/LeanUrat/MovesR/Sib.lean        U40–U41 (SIBPkg+SIBOdelta, chain)
  lean/LeanUrat/MovesR/Defs.lean       re-export shim
  (REL.3: no file, no object — D6.)

## 5. Findings → repairs (Codex audit 2026-07-28, 15 crit / 6 gap)

  F1  (crit, R1 card omitted)        → unit R6 `Fsub_card` stated (D1; overruled non-unit).
  F2  (crit, Setting degenerate)     → realized-measure law fields; nonempty Cont/PTree (R7).
  F3  (crit, ledger slots vacuous)   → ten TYPED clause fields over ReBased/TowerData (R12, D4).
  F4  (crit, counting vacuous/n)     → fixed n param; nonempty Hist/Locus; vols through pinned V (R11).
  F5  (crit, REL1 vacuous)           → REL1 := typed clauses ∧ display over non-degenerate carriers (R13).
  F6  (crit, (a5)/(a6) vacuous)      → nonempty FrameIdx/AmbRead; readDict injective + letter-preserving (R14).
  F7  (gap, teich pin external)      → `teich_pin` now a FIELD of REL2a; compat Props typed (R14).
  F8  (crit, BoxVol dummy)           → event algebra + content laws + `vol_cyl` cylinder pin (R10).
  F9  (crit, REL2b vacuous)          → events cylinder-populated; guard = the note's proviso (R15).
  F10 (gap, REL1 link prose-only)    → `REL2b_linked` conjoins REL1 at (δ_j, d_rel) (R15).
  F11 (crit, REL2d junk corr)        → corr_word/corr_reads/corr_verdict typed; PUnit example dropped (R16).
  F12 (gap, (a3)/(EQ-2) deps absent) → A.teich_pin field + AD parameter + posOf wiring (R16).
  F13 (crit, entryFirst varies)      → `entryFirst : ℕ` FIXED; `consumed` set carries the T-multiplicity (R17, D5).
  F14 (gap, (e1)/(e4) compat absent) → stateDict_compat typed; e4agrees(tableConv) parameterized (R17).
  F15 (crit, EQ1 infinite menus)     → Finset menu + menuNe + stage-tuple anchor (R18).
  F16 (crit, EQ2 arbitrary numbers)  → alphabets as additive spans; card_eq; Stable DEFINED via posLetter (R19).
  F17 (gap, Stable dictionary)       → posLetter = the owed dictionary AS DATA; Stable = letter persistence (R19).
  F18 (crit, EQ3 inherits vacuity)   → alias of the repaired REL2b (R15).
  F19 (crit, SIB empty/unguarded)    → SettingsFamily (ne, root, desc-closure); 0 < cellMass guard (R8, R22).
  F20 (gap, REL1/closure missing)    → REL1 conjunct in the ∃; closure typed in family; O_chain = ring half only (R22, R8, R23).
  F21 (crit, REL3 pseudo-statement)  → DELETED; REL.3 = recorded non-unit with acceptance path (D6).

Fresh-Fable audit (`MOVESR_AUDIT_FABLE_2026-07-28.md`, 2 crit / 5 gap; all 21
Codex repairs verified genuine there):

  FF1 (crit, lst mislabeled + entailed by REL1b) → `lst` RETYPED as Lemma LST's
      three legs (slot-min TYPING / interior FLOOR CONSTANCY / floor-downset
      SELECTION) over new ht/blk/floor carriers, per the §C display MOVES 3728;
      stabilization reading withdrawn; §3 widening (iv) withdrawn (R12, D4).
  FF2 (crit, count free data → lawful-junk REL1b) → count field DELETED;
      `ReBased.count` DEFINED from SHZ + cyl (level-N cylinder classes meeting
      the classifier locus); REL1b consumes the definition (R11, R12, R13).
  FF3 (gap, PIN-WELLDEF status leg dropped) → c05PinWelldef gains the second leg:
      frame-invariance of the pinned aDim-multiset (cardinality AND status) (R12).
  FF4 (gap, a_δ double-booked) → ReBased parameterized by (Sp, AD);
      `posOfDigit` + `aDim_eq` tie c1's exponents to (EQ-2)'s AlphabetData (R12).
  FF5 (gap, three measurability memberships dropped) → (i) REL2a gains
      prodEvents + digit-cylinder anchor + domIdent_meas; (ii) REL2b gains the
      Θ-pullback ∈ AmbEvents conjunct; (iii) SIBOdelta + massEqEntry require the
      realization event ∈ RB.C.V.events (R14, R15, R17, R22).
  FF6 (gap, (e3)'s vol arbitrary) → massEqEntry retyped on `RB : ReBased` with
      the REL1 conjunct — the _linked pattern; the mass is THE REL.1 theory's (R17).
  FF7 (gap, (a5) unanchored + D7 overclaim) → ambT_unitri/tgtT_unitri
      (CoordPrec-anchored unitriangularity); D7's false claim withdrawn and
      replaced; residue recorded as widening (v) (R14, D7, §3).

Codex FINAL audit on rev 3 (`MOVESR_AUDIT_CODEX_FINAL_2026-07-28.md`, 15 crit /
5 gap; parallel fresh-Fable #2: ACCEPT 0/0) — per-finding TRIAGE (adjudication #1;
S = survived, folded in · R = resolved-by-rearchitecture · N = note-rejected):

  CF1  (crit, zero-mass singleton)   S → `mem_pos` family-scope law (NOTE-CHECK: the note has
       NO positive-cell existence law; the (b) proviso "the only cells any (SIB) display
       conditions on" is the warrant — family = conditioning sites) (U8, U40).
  CF2  (crit, composition untyped)   S → ONE coherent package function per family + the typed
       composition clause: descendant AMBIENT theory = parent TARGET theory (ambDeg equality
       + HEq across desc_amb's index transport) (U40).
  CF3  (crit, menuNe strengthens)    S — NOTE-CHECK CONFIRMS CODEX ("no menu/exhaustion
       claims", R.5) → `menuNe` REMOVED; empty menus back in range (U9).
  CF4  (crit, species grammar)       S → SideData/PolyConv carriers + projections +
       `letter_det` injectivity ("letters are DEFINED BY …") (U9).
  CF5  (crit, alpha not attainable)  S → declared `slotMap` + `alpha_attain` span-generation
       equality (U10).
  CF6  (crit, EQ-2 linearity half)   R → the slot maps now EXIST as data with F_δ-module
       structure; EQ2law types BOTH conjuncts (U10, U11).
  CF7  (crit, LST incomplete)        R → `LSTStmt` types ALL legs over `GradedCarrier`:
       chain-weight typing `G.w (mono i) = ht i`, slot-min, in_γ/level-set functionality,
       (ii), (iii) — no fence (U14, U26).
  CF8  (crit, interiorB vacuous)     S → `interior_fresh` ("on the factor interior — where
       all fresh content lives"): constrained digits sit on interior blocks (U17).
  CF9  (crit, pin status ≠ aDim)     S → `Status` carrier + `pinStatus` + `pinnedIn_spec`;
       C05Stmt's status-multiset invariance leg (aDim multiset retained as the ledger
       weight) (U17, U23).
  CF10 (crit, (a5) identity family)  S → (a5) quantifies over the AMBIENT `S.reframe`
       family (Setting-supplied); deliverable = target transports + commutation (U7, U34).
  CF11 (crit, (a6) letter-only)      S → per-read-field typing: SHAPE/anchor/SIDE preserved;
       DIGITS/ψ/lifts as declared per-read transports (RECONSTRUCTED, per (R0-reads)) (U35).
  CF12 (crit, (d) unconstrained)     S (typable layer) → `posOf_letter` pins the alphabet
       wiring; reads structured via U35; the full canonical-tree/lift-policy pinning to the
       ENGINE = HC-1's instantiation, recorded in D4/§3(v) (U38).
  CF13 (crit, candidate promoted)    S → `firstIdxCandidate` DEMOTED (named candidate, no
       consumer may hypothesize it; removed from D7's list); (e4) = `e4agrees` alone (U39).
  CF14 (crit, consumed free)         S → `consumed` re-keyed as [3]/MovesS's exported
       PARAMETER, like `tableConv` (U39, §3 consumer edges).
  CF15 (crit, BoxVol not Haar)       S → `events_level`: every event a finite cylinder union
       at some level, so vol is FORCED everywhere by additivity + `vol_cyl` ((g7)'s
       determination-radius discipline cited) (U13).
  CF16 (gap, §B1 fenced)             R → `GradedCarrier` types the graded vocabulary + laws;
       `SecB1Stmt` adds slotCoeff additivity; localization/degree-1 unit ride at HC-1,
       recorded (U14, U19).
  CF17 (gap, EQ unattached)          S → `REL1PassDeliverable := REL1 ∧ EQ1` (the pass's
       named checkpoint) + `EQ2lawIfREL1 := REL1 → EQ2law` ("OPEN, REL.1-conditional") (U29).
  CF18 (gap, R12 multi-lemma)        S → split into U13–U29: carriers, count, and ELEVEN
       one-display statement defs, each its own unit.
  CF19 (gap, R14 multi-lemma)        S → split into U30–U36: one checklist item per
       structure + the bundle.
  CF20 (gap, R17 split ambiguity)    S → e-Props separated + `REL2eObligations` as THE single
       collecting conjunction consumers cite (U39).

  TRIAGE COUNTS: 17 SURVIVED (folded in) · 3 RESOLVED-BY-REARCHITECTURE (CF6, CF7,
  CF16) · 0 NOTE-REJECTED (both ordered note-checks resolved FOR the repair: CF1's
  law does not exist in the note — family-scope mechanism used instead; CF3's
  strengthening confirmed and removed).

STATUS (2026-07-28): REV 4 WRITTEN (re-architecture per stuck-rule adjudication #1)
— Codex 21/21 (rev 2) + Fable 7/7 (rev 3, confirmed genuine by Fable #2) + Codex
FINAL 20/20 triaged (17 folded / 3 by re-architecture). 41 units: 7 provable
(U2–U6, U12, U41), 34 statements-only; the CInterface (GradedCarrier + 11 *Stmt
defs + CStatements) replaces every fence; HC-1 owes the instantiation. No axioms;
no kernel discharged; statement fence in force. This corpus PARKS here pending the
campaign's next gate.

codex
I’m auditing the 41 unit specs directly against the frozen displays, with particular attention to the eleven §C statement definitions and whether their abstract carriers actually make every clause meaningful.
exec
/usr/bin/bash -lc 'rg -n "def DomData|structure DomData|abbrev DomData|def IsUnitriangular|structure DigitSystem" lean/LeanUrat/MovesC/Defs.lean lean/LeanUrat/Moves/DefsT.lean' in /data/users/asvin/math-and-lean/p-adic-splitting-densities
 succeeded in 0ms:
lean/LeanUrat/Moves/DefsT.lean:187:structure DigitSystem (n : ℕ) (α : Type*) where
lean/LeanUrat/MovesC/Defs.lean:241:def IsUnitriangular {m : ℕ} {R : Type*} [Add R] (Θ : (Fin m → R) → (Fin m → R)) : Prop :=
lean/LeanUrat/MovesC/Defs.lean:278:structure DomData (lines : ℕ → Line) (i : ℕ) (interiorEnd : ℕ) : Prop where

exec
/usr/bin/bash -lc "sed -n '215,295p' lean/LeanUrat/MovesC/Defs.lean; sed -n '180,215p' lean/LeanUrat/Moves/DefsT.lean" in /data/users/asvin/math-and-lean/p-adic-splitting-densities
 succeeded in 0ms:
/-- A **base coordinate** `c = (ℓ, i)`: `c.1 = ℓ` the p-adic level, `c.2 = i` the coefficient
(base) index (§C.0). -/
abbrev Coord : Type := ℕ × ℕ

/-- The **global order** `≺` (§C.0): `(ℓ,i) ≺ (ℓ',i')` iff `ℓ < ℓ'`, or `ℓ = ℓ'` and `i > i'`
(within a level, from the TOP coefficient down — Fact A's elimination order). -/
def CoordPrec (c c' : Coord) : Prop := c.1 < c'.1 ∨ (c.1 = c'.1 ∧ c'.2 < c.2)

/-- A **§C locus**: a unitriangular digit system over `m = n·N` base digits in ≺-SORTED
coordinates (`Fin m`-order = `≺`, witnessed by `JetSetup.coordOf_sorted`), alphabet `ZMod p`
(the BLOCK CONVENTION: an `F`-digit of residue degree `d` is its `d` base equations, each a
factor `p⁻¹`). Reuses the accepted `DigitSystem` (DefsT); its solution set is the cylinder. -/
abbrev Locus (p m : ℕ) : Type := DigitSystem m (ZMod p)

/-- The **mass** of a locus: the number of its solutions among the `p^m` box points
(`= p^{m−numPinned}`, `C0.digitSystemMass`). -/
noncomputable def Locus.mass {p m : ℕ} (D : Locus p m) : ℕ :=
  Nat.card {x : Fin m → ZMod p // D.IsSolution x}

/-- The full box mass `p^{nN} = p^m`. -/
def boxMass (p m : ℕ) : ℕ := p ^ m

/-- **A move map is unitriangular for `≺`** (§C.0.5): `(Θx)_i = x_i + φ_i(x_j : j ≺ i)` — the
diagonal is the identity and the correction is an arbitrary function of ≺-earlier coordinates
(in ≺-sorted `Fin m` coordinates, `j < i`). This is the shape Fact A's division accounting
produces, in both directions. -/
def IsUnitriangular {m : ℕ} {R : Type*} [Add R] (Θ : (Fin m → R) → (Fin m → R)) : Prop :=
  ∀ i : Fin m, ∃ corr : ((j : Fin m) → j < i → R) → R,
    ∀ x, Θ x i = x i + corr (fun j _ => x j)

/-- The **pullback** of a locus `D` by a move `Θ` (`Θ*(E)` of the §C.0.5 pin-transport
corollary): the points whose `Θ`-image solves `D`. `C0.pinTransport` re-presents it as a
digit system with the SAME pinned coordinates (per-coordinate status, rev-9 PIN-WELLDEF). -/
def Locus.pullback {p m : ℕ} (D : Locus p m) (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) :
    Set (Fin m → ZMod p) := {x | D.IsSolution (Θ x)}

/-! ## C1. Lines, staircases, heights (absolute v_p-scale, §C.1.5 scale declaration) -/

/-- A **read-side line** as an AFFINE function of the base index, absolute v_p-scale (§C DOM):
`at b = intercept − slope·b` with `slope > 0` in genuine instances (lines DESCEND). -/
structure Line where
  intercept : ℚ
  slope : ℚ

/-- Evaluate a line at a base index. -/
def Line.at (L : Line) (b : ℕ) : ℚ := L.intercept - L.slope * (b : ℚ)

/-- The **absolute-height** map `ht(ℓ, i) = ℓ + off(i)` (§C.1.5 scale declaration): a base
coordinate's v_p-height in the current frame. DEFERRED CONTENT (flag): that a `JetSetup`'s `ht`
is the genuine K1-chain weight of the coordinate's basis monomial (`off(i) = Σ_r innerslot·κ_r`,
κ current — LST(i)) is the unbuilt jet-coordinate bridge. -/
abbrev HtMap : Type := Coord → ℚ

/-- The pointwise max of a family of lines over `[0, i]` (§C DOM's floor of RAW lines; the
step-function floor of a history is `History.floorH` below). -/
noncomputable def floorOf (lines : ℕ → Line) (i b : ℕ) : ℚ :=
  Finset.sup' (Finset.range (i + 1)) (by simp) (fun m => (lines m).at b)

/-- **DOM interface** (§C Lemma DOM): the two displayed inputs of the affine induction — the
(I-aug) strict-steepness chain and the vertex-entry endpoint inequality. `HistoryCoherent`
supplies `steeper` for the history's recorded lines (`C3.steeperChain`); `vertex_entry` is
D.8/D.4 geometry (per-instance input). `C2.DOM` derives interior domination; `C2.DOM_floorForm`
the floor form. -/
structure DomData (lines : ℕ → Line) (i : ℕ) (interiorEnd : ℕ) : Prop where
  /-- (I-aug): the current line descends strictly faster than every earlier one. -/
  steeper : ∀ m, m < i → (lines m).slope < (lines i).slope
  /-- vertex-entry (§C DOM(2)): at the interior end the current line dominates every earlier
  one — the endpoint inequality that seeds the affine induction. -/
  vertex_entry : ∀ m, m ≤ i → (lines m).at interiorEnd ≤ (lines i).at interiorEnd

/-! ## C2. The address-free clause layer (Route B, §C.1.5′/rev 9)

A fresh clause never names a pin address. It is carried by a SUPPORT (the strip region or the
weight-γ′ level set), a CODIMENSION, and an exact-fiber-count law — the only three statistics
the counting consumes (C15 S4b). Strip zeros are the `codim = 1`, singleton-support case;
fresh VALUE clauses come from `TypObject` (the graded piece map) via `C1.TYP_toClause`. -/

/-- **A level-set clause** (§C.1.5′ fresh content, address-free): a constraint `sat` that
(i) depends only on the coordinates of its `support` (`dep`), and (ii) cuts EXACTLY
`p^{−codim}` among the support assignments (`count`, division-free on the supported
representatives). The `count` law is self-policing: it forces satisfiability and exactness, so

/-! ## 6. Unitriangular digit systems (P6ii, the ledger) -/

/-- **A unitriangular digit system** (D.3(e)(ii), D.11): `n` digit coordinates over an alphabet
`α`, of which a subset are PINNED; each pinned coordinate is a function `solve` of the STRICTLY
EARLIER coordinates (the accumulated affine carries are the unitriangular part).  This is the
structure the audit demanded in place of "cardinality invariance under an arbitrary equivalence". -/
structure DigitSystem (n : ℕ) (α : Type*) where
  /-- which of the `n` coordinates are pinned by an equation -/
  pinned : Fin n → Bool
  /-- a pinned coordinate's value, as a function of the strictly-earlier coordinates -/
  solve : (i : Fin n) → ((j : Fin n) → j < i → α) → α

/-- `x` solves the digit system: each pinned coordinate equals its `solve`-value on the earlier
coordinates. -/
def DigitSystem.IsSolution {n : ℕ} {α : Type*} (D : DigitSystem n α) (x : Fin n → α) : Prop :=
  ∀ i : Fin n, D.pinned i = true → x i = D.solve i (fun j _ => x j)

/-- The number of pinned coordinates (`k` in the `|α|^{n−k}` count). -/
def DigitSystem.numPinned {n : ℕ} {α : Type*} (D : DigitSystem n α) : ℕ :=
  (Finset.univ.filter (fun i => D.pinned i)).card

end LeanUrat.Moves

codex
1. > “U8 SettingsFamily + mem_pos … + desc closure · ‘(SIB-Oδ)’ quantifier + recursion clause”
   >
   > “U40 SIBPkg + SIBOdelta … descendant ambient = parent target”

   **CRITICAL.** `desc` may be empty for every subtree. Thus a family containing only its root can satisfy the proposed recursion clauses while checking no descendant branching cell and no further absolute base index. The note requires the typing at every actual descendant branching cell and says the obligations compose across nested base changes. Neither actual-descendant coverage nor nonemptiness of `desc` is stated.

2. > “U13 BoxVol + events_level … Haar characterized on the WHOLE event class”
   >
   > “U37 REL2b … ‘for every REL.1-measurable continuation event W’”

   **CRITICAL.** `events_level` restricts every measurable event to a finite union of cylinders at one finite level. “Digit cylinders generate” does not say every measurable event is finite-level; (g7)’s determination-radius rule applies to gate outcomes, not the entire REL.1 measurable event class. Consequently U37 can quantify over a strictly smaller event class than the REL.2b display.

3. > “U14 GradedCarrier (D4(a): Coeff/Gr/w/inγ + 4 laws …)”

   **CRITICAL.** This does not provide enough graded structure to state the cited §C displays. `Gr γ` is only an additive group: there is no graded-ring multiplication, unit-lift/scalar action, basis-monomial construction, stage-scale index `str·γ`, piece map `Rδ′`, or attainable-image attachment. Those objects occur explicitly in LST/TYP. The missing localization and degree-1 unit are declared to “ride at HC-1,” leaving a residual fence contrary to the re-architecture’s premise.

4. > “U15 TowerData + Base/Climb/StageCarrier laws · ‘(R0-tower) F₁ := … F_{k+1} = … built afresh’”

   **CRITICAL.** The note’s stage is `(w, Φ, C, U, T, F, z)` under the same axioms `(S1)–(S6)`, with graded rings, localization, and degree-1 unit. `TowerData` contains only residue fields, embeddings, and residual polynomials; `StageCarrierLaws` says only finite and characteristic `p`. This is substantially weaker than the R0-tower and §B1/§B2-DEF statements.

5. > “U19 SecB1Stmt … graded vocabulary typed via G; slotCoeff additivity”

   **CRITICAL.** It replaces §B1 with finite/characteristic stage fields plus global additivity of `slotCoeff`. The source asserts additivity of the degree-`γ′` initial-form map on level-set digit assignments—not additivity of reconstructed coefficients over arbitrary digit vectors. Teichmüller/digit reconstruction generally has carries, so this is also an unjustified strengthening.

6. > “U25 C15Stmt · ‘C.1.5’s (ZC) invariant’”

   **CRITICAL.** `∀ H F F' Z, zcStat H F Z = zcStat H F' Z` merely makes an arbitrary integer field frame-invariant. It omits the displayed (ZC) floor/downset, fresh-clause, selection, and mass content consumed later. A constant `zcStat` satisfies it independently of the classifier.

7. > “U26 LSTStmt (FULL: chain-weight typing + slot-min + in_γ/level-set + interior constancy + selection …)”

   **CRITICAL.** It is not the full LST display:

   - `mono` is an arbitrary coefficient, not the basis monomial `p^l·∏ Φ̂_r^innerslot`.
   - There are no `κ_r`, `STR_r`, read-time fixation, or recentering discipline.
   - `G.Gr γ` omits the required stage index `str·γ`.
   - The interior clause equates two arbitrary floor fields and does not state the displayed blockwise `ht` constancy.
   - `interiorB` may be false on every block when there are no pinned digits, vacuously discharging clauses (ii)–(iii), although LST quantifies over the factor interior independently of whether a locus pins anything.
   - The selection clause becomes tautological after `floorSet` is defined by the same inequality, without identifying it with the engine’s floor downset.

8. > “U27 TYPStmt (additivity + attainable-image cardinality = p^{a_δ})”

   **CRITICAL.** This says that the whole jet is additive and that each coordinate range has a given cardinality. Lemma TYP instead states the tower expansion, the downset-vanishing hypothesis, the formula
   `inγ′(B) = Σ y′c·in(mc) ∈ grδ′`, dependence on exactly `Lγ′(B)`, the off-lattice empty case, the spanning consequence, the piece map `Rδ′`, equal-size fibers, and LST selection. Almost all displayed content is absent, while global jet additivity is not the source claim.

9. > “U28 DOMStmt · §C Lemma DOM via MovesC `DomData`”

   **CRITICAL.** `DomData` contains the steepness and vertex-entry hypotheses of the affine induction. `DOMStmt` asserts those inputs, not Lemma DOM’s conclusion that the current line/staircase dominates all earlier ones on the interior, including the floor form. It therefore says a different proposition.

10. > “U29 CStatements + REL1 (:= CStatements at δ — the typed mutatis-mutandis pointer) …”

    **CRITICAL.** Since `SecB1Stmt`, `C15Stmt`, `LSTStmt`, `TYPStmt`, and `DOMStmt` are not their cited displays, `REL1 := CStatements` is strictly weaker/different from “§A, §B1, §B2-DEF, and §C … hold over `Oδ`.” A typed record does not repair inaccurate field types.

11. > “U30 REL2a1 (a1 + FF5(i)) · ‘(a1) DOMAIN … measurable product’”

    **CRITICAL.** `freeCoords` is an arbitrary infinite set and `domIdent` an arbitrary equivalence. `Setting` has no base-coordinate/fixed-coordinate data against which it can express “which base coordinates `(ℓ,i)` are free.” Thus the required explicit continuation-coordinate list can be replaced by an unrelated coding of `Cont`.

12. > “U32 REL2a3 (a3 + teich_pin)”
    >
    > “U34 REL2a5 … C.0.5’s unitriangular transports”

    **CRITICAL.** `REL2a3.TowerRes` is an arbitrary field unrelated to the target `TowerData`. Likewise, U34’s `tgtOf` is privately supplied and is never identified with the target `ReBased.T`. Hence the embedding and commuting square need not concern the re-based tower or its actual C.0.5 transports.

13. > “U35 REL2a6 (a6 PER READ FIELD … shape/anchor/side preserved, residue-datum transports declared)”

    **CRITICAL.** Digits, branch factor `ψ`, and recentering lifts are collapsed into one opaque dependent type and an unconstrained function `resDict`. No projections identify those fields, enforce monicity/irreducibility for `ψ`, or encode the canonical lift convention. This is not the required letter-for-letter transport displayed per read field.

14. > “U38 REL2d (square + word/reads/verdict corr + posOf_letter …)”

    **CRITICAL.** No law mentions `A.a3.teich` or connects `nodeCorr` to the canonical lift policy. `subtreeCorr` and `TgtRealizes` are also arbitrary and unrelated to `nodeCorr`, `ambTcan`, or `tgtTcan`; choosing `TgtRealizes := True` can trivialize the prescribed-subtree meaning. The required canonical-tree/lift-policy square is therefore not stated.

15. > “U39 REL2e + e4agrees/firstIdxCandidate(demoted …)/determines/massEqEntry (consumed = [3]’s parameter …)”

    **CRITICAL.** The unit remains vacuous or under-keyed:

    - `consumed := ∅` makes `determines` and every subtree-pricing equation vacuous; no nonemptiness or inclusion of the prescribed `T_j` is required.
    - `entryFirst` is arbitrary per structure, not an explicit function of branch data as demanded by (e4).
    - `tableConv := fun _ => True` discharges `e4agrees`.
    - `RelState` and `stateDict` have no connection to the supplied REL.1 package.
    - The mass event is not shown to be the outcome determined by the state key `(entryFirst, τ)`.

16. > “U29 CStatements + REL1 … + REL1PassDeliverable/EQ2lawIfREL1”

    **GAP.** This single unit contains the eleven-field record, the REL.1 definition, the EQ-1 pass conjunction, and the separate EQ-2 implication—multiple distinct displays with different consumer roles. It violates the claimed one-display decomposition.

17. > “U39 REL2e + e4agrees/firstIdxCandidate … + REL2eObligations”

    **GAP.** Five separately displayed requirements, an external table convention, an external consumed-subtree collection, a demoted candidate, and the collecting interface are packed into one unit. The exact MovesS definitions of `tableConv` and `consumed` are only promised in prose, leaving the unit’s dependency contract underspecified.

Counts: **15 CRITICAL / 2 GAP**

**REJECT (15 crit / 2 gap)**
tokens used
60,394
1. > “U8 SettingsFamily + mem_pos … + desc closure · ‘(SIB-Oδ)’ quantifier + recursion clause”
   >
   > “U40 SIBPkg + SIBOdelta … descendant ambient = parent target”

   **CRITICAL.** `desc` may be empty for every subtree. Thus a family containing only its root can satisfy the proposed recursion clauses while checking no descendant branching cell and no further absolute base index. The note requires the typing at every actual descendant branching cell and says the obligations compose across nested base changes. Neither actual-descendant coverage nor nonemptiness of `desc` is stated.

2. > “U13 BoxVol + events_level … Haar characterized on the WHOLE event class”
   >
   > “U37 REL2b … ‘for every REL.1-measurable continuation event W’”

   **CRITICAL.** `events_level` restricts every measurable event to a finite union of cylinders at one finite level. “Digit cylinders generate” does not say every measurable event is finite-level; (g7)’s determination-radius rule applies to gate outcomes, not the entire REL.1 measurable event class. Consequently U37 can quantify over a strictly smaller event class than the REL.2b display.

3. > “U14 GradedCarrier (D4(a): Coeff/Gr/w/inγ + 4 laws …)”

   **CRITICAL.** This does not provide enough graded structure to state the cited §C displays. `Gr γ` is only an additive group: there is no graded-ring multiplication, unit-lift/scalar action, basis-monomial construction, stage-scale index `str·γ`, piece map `Rδ′`, or attainable-image attachment. Those objects occur explicitly in LST/TYP. The missing localization and degree-1 unit are declared to “ride at HC-1,” leaving a residual fence contrary to the re-architecture’s premise.

4. > “U15 TowerData + Base/Climb/StageCarrier laws · ‘(R0-tower) F₁ := … F_{k+1} = … built afresh’”

   **CRITICAL.** The note’s stage is `(w, Φ, C, U, T, F, z)` under the same axioms `(S1)–(S6)`, with graded rings, localization, and degree-1 unit. `TowerData` contains only residue fields, embeddings, and residual polynomials; `StageCarrierLaws` says only finite and characteristic `p`. This is substantially weaker than the R0-tower and §B1/§B2-DEF statements.

5. > “U19 SecB1Stmt … graded vocabulary typed via G; slotCoeff additivity”

   **CRITICAL.** It replaces §B1 with finite/characteristic stage fields plus global additivity of `slotCoeff`. The source asserts additivity of the degree-`γ′` initial-form map on level-set digit assignments—not additivity of reconstructed coefficients over arbitrary digit vectors. Teichmüller/digit reconstruction generally has carries, so this is also an unjustified strengthening.

6. > “U25 C15Stmt · ‘C.1.5’s (ZC) invariant’”

   **CRITICAL.** `∀ H F F' Z, zcStat H F Z = zcStat H F' Z` merely makes an arbitrary integer field frame-invariant. It omits the displayed (ZC) floor/downset, fresh-clause, selection, and mass content consumed later. A constant `zcStat` satisfies it independently of the classifier.

7. > “U26 LSTStmt (FULL: chain-weight typing + slot-min + in_γ/level-set + interior constancy + selection …)”

   **CRITICAL.** It is not the full LST display:

   - `mono` is an arbitrary coefficient, not the basis monomial `p^l·∏ Φ̂_r^innerslot`.
   - There are no `κ_r`, `STR_r`, read-time fixation, or recentering discipline.
   - `G.Gr γ` omits the required stage index `str·γ`.
   - The interior clause equates two arbitrary floor fields and does not state the displayed blockwise `ht` constancy.
   - `interiorB` may be false on every block when there are no pinned digits, vacuously discharging clauses (ii)–(iii), although LST quantifies over the factor interior independently of whether a locus pins anything.
   - The selection clause becomes tautological after `floorSet` is defined by the same inequality, without identifying it with the engine’s floor downset.

8. > “U27 TYPStmt (additivity + attainable-image cardinality = p^{a_δ})”

   **CRITICAL.** This says that the whole jet is additive and that each coordinate range has a given cardinality. Lemma TYP instead states the tower expansion, the downset-vanishing hypothesis, the formula
   `inγ′(B) = Σ y′c·in(mc) ∈ grδ′`, dependence on exactly `Lγ′(B)`, the off-lattice empty case, the spanning consequence, the piece map `Rδ′`, equal-size fibers, and LST selection. Almost all displayed content is absent, while global jet additivity is not the source claim.

9. > “U28 DOMStmt · §C Lemma DOM via MovesC `DomData`”

   **CRITICAL.** `DomData` contains the steepness and vertex-entry hypotheses of the affine induction. `DOMStmt` asserts those inputs, not Lemma DOM’s conclusion that the current line/staircase dominates all earlier ones on the interior, including the floor form. It therefore says a different proposition.

10. > “U29 CStatements + REL1 (:= CStatements at δ — the typed mutatis-mutandis pointer) …”

    **CRITICAL.** Since `SecB1Stmt`, `C15Stmt`, `LSTStmt`, `TYPStmt`, and `DOMStmt` are not their cited displays, `REL1 := CStatements` is strictly weaker/different from “§A, §B1, §B2-DEF, and §C … hold over `Oδ`.” A typed record does not repair inaccurate field types.

11. > “U30 REL2a1 (a1 + FF5(i)) · ‘(a1) DOMAIN … measurable product’”

    **CRITICAL.** `freeCoords` is an arbitrary infinite set and `domIdent` an arbitrary equivalence. `Setting` has no base-coordinate/fixed-coordinate data against which it can express “which base coordinates `(ℓ,i)` are free.” Thus the required explicit continuation-coordinate list can be replaced by an unrelated coding of `Cont`.

12. > “U32 REL2a3 (a3 + teich_pin)”
    >
    > “U34 REL2a5 … C.0.5’s unitriangular transports”

    **CRITICAL.** `REL2a3.TowerRes` is an arbitrary field unrelated to the target `TowerData`. Likewise, U34’s `tgtOf` is privately supplied and is never identified with the target `ReBased.T`. Hence the embedding and commuting square need not concern the re-based tower or its actual C.0.5 transports.

13. > “U35 REL2a6 (a6 PER READ FIELD … shape/anchor/side preserved, residue-datum transports declared)”

    **CRITICAL.** Digits, branch factor `ψ`, and recentering lifts are collapsed into one opaque dependent type and an unconstrained function `resDict`. No projections identify those fields, enforce monicity/irreducibility for `ψ`, or encode the canonical lift convention. This is not the required letter-for-letter transport displayed per read field.

14. > “U38 REL2d (square + word/reads/verdict corr + posOf_letter …)”

    **CRITICAL.** No law mentions `A.a3.teich` or connects `nodeCorr` to the canonical lift policy. `subtreeCorr` and `TgtRealizes` are also arbitrary and unrelated to `nodeCorr`, `ambTcan`, or `tgtTcan`; choosing `TgtRealizes := True` can trivialize the prescribed-subtree meaning. The required canonical-tree/lift-policy square is therefore not stated.

15. > “U39 REL2e + e4agrees/firstIdxCandidate(demoted …)/determines/massEqEntry (consumed = [3]’s parameter …)”

    **CRITICAL.** The unit remains vacuous or under-keyed:

    - `consumed := ∅` makes `determines` and every subtree-pricing equation vacuous; no nonemptiness or inclusion of the prescribed `T_j` is required.
    - `entryFirst` is arbitrary per structure, not an explicit function of branch data as demanded by (e4).
    - `tableConv := fun _ => True` discharges `e4agrees`.
    - `RelState` and `stateDict` have no connection to the supplied REL.1 package.
    - The mass event is not shown to be the outcome determined by the state key `(entryFirst, τ)`.

16. > “U29 CStatements + REL1 … + REL1PassDeliverable/EQ2lawIfREL1”

    **GAP.** This single unit contains the eleven-field record, the REL.1 definition, the EQ-1 pass conjunction, and the separate EQ-2 implication—multiple distinct displays with different consumer roles. It violates the claimed one-display decomposition.

17. > “U39 REL2e + e4agrees/firstIdxCandidate … + REL2eObligations”

    **GAP.** Five separately displayed requirements, an external table convention, an external consumed-subtree collection, a demoted candidate, and the collecting interface are packed into one unit. The exact MovesS definitions of `tableConv` and `consumed` are only promised in prose, leaving the unit’s dependency contract underspecified.

Counts: **15 CRITICAL / 2 GAP**

**REJECT (15 crit / 2 gap)**
