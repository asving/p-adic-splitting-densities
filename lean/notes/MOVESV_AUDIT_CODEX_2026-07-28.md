OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: read-only
reasoning effort: none
reasoning summaries: none
session id: 019fa9cf-c75d-7761-b333-c883af92843b
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

CORPUS: MovesV
NOTE: §V-TABLES

This corpus SUPPLIES the MovesS interface — audit the SEAM-SUPPLY table
HARDEST of all: check every field of MovesS's `Defs.lean`/`Interfaces.lean`
(both pasted below, verbatim, as the ground-truth signatures) is mapped to an
explicit supplier unit or an explicit owner in MovesV's §4 SEAM-SUPPLY table,
with no field silently dropped, silently self-supplied where the field's true
owner is a different corpus (per the included MovesS §W4-SYNC seam-contract
section, also pasted below), or supplied by a unit whose statement does not
actually produce that field's type.

The (J-RAT)/CL-18 per-cell deliverable is the note's PLAN-SYNC obligation
(owner [1v]): check that the V5-7 units (V5-7a/b/c) carry it EXACTLY — the
per-cell rational coefficients J_{τ,o} ∈ ℚ(q), not the marked T·G aggregate,
with the XHD-s + cell-count hypotheses displayed as explicit hypothesis
fields, not folded into a definition or silently discharged.

The ONE flagged axiom candidate in this corpus — the Hensel/coprime-lift
hypothesis at V6-4c (`CoprimeLiftPack`) — must remain a FENCED PROPOSAL per
the campaign axiom policy (a typed hypothesis field, explicitly flagged as a
published-axiom candidate if Mathlib's exact form is missing, NEVER silently
declared as an unconditional axiom or silently discharged as a plain
definition). Flag any deviation from fenced-proposal form as CRITICAL.

This doctrine (SEAM-SUPPLY-hardest, J-RAT exactness, axiom-candidate fencing)
is BINDING on this audit pass — apply it in addition to, not instead of, the
five-point check above.

THE FROZEN NOTE (ground truth — §V-TABLES, rev 7, lean/notes/MOVES_2026-07-24.md lines 7829-9054):

## §V-TABLES — the measured value tables, XHD-conditional (assembly note 4, = plan [1v]-COND)

*(2026-07-27. Assembly note [1v] per ASSEMBLY_PLAN_2026-07-26.md §2v, drafted
in its strictly marked-μ̂, XHD-CONDITIONAL form — the [1v]-COND acceptance
event of the plan's REV 7 split, under the REV 9/10 sharpenings (h_ent an
explicit argument everywhere — RETYPED at REV 4: a displayed projection
of ε, V.1(iii); POST-SPLIT ι typing; RS.1-DEEP/SH/MARKED
downstream routing; the branch-cell decision; marked-μ̂ typing binding).
REV 2 (2026-07-27, same day): the pass-1 findings (VTAB_PASS1_2026-07-27.md,
7 critical / 7 gaps) repaired IN PLACE; plan citations follow REV 12 —
the shape-level multinomial is STRUCK, member-indexed convolution
everywhere, (NS-ROUTE) scoping at every (ns) site.
REV 3 (2026-07-27, same day): the pass-2 findings (VTAB_PASS2_2026-07-27.md,
3 critical / 3 gaps) repaired IN PLACE — the DISJOINT-COMPONENT convention
on every semilinear domain (F1), (iv)-MEAS retyped to the marked source
space (F2), Theorem VAL(b) relabeled (XHD-u)-conditional (F3), PART-1's
countable-partition/null-remainder route displayed (F4), the HMC-probe
step 2 pinned (F5), gate B's two-history attribution corrected (F6).
REV 4 (2026-07-27, same day): the pass-3 findings (VTAB_PASS3_2026-07-27.md,
2 critical / 1 gap) repaired IN PLACE — the entrance-height DOUBLE
PARAMETRIZATION UNIFIED (F1: a §D4-R shape-prefix P̂ already RETAINS its
per-node heights h_r and per-read side heights u*_r — §D4-R L3, rev 9 —
so ε is CONCRETE and h_ent(ε) is a displayed PROJECTION of ε's retained
data, never an independent parameter; heights are ranged via the finite
height-forgetting TEMPLATES ε̊ and the instantiation bijection —
ENT-AGG/INIT-RAT/(ENT-U)/COMP-h/COMP-AGG/VAL(b) re-indexed, every h_ent
occurrence swept); the HMC-probe's terminal step 2 given its EXIT-OBJECT
typing (F3: terminal-final templates displayed in the (v)/(vi)
signature). F2 (V-n3 not yet run) is GOVERNANCE, not text: no V.6 sealed
value changed — the census runs against the unchanged seal.
Consumes: the DUAL-ACCEPTED §C (rev 14 — C.0's coordinates/(SAE)/(NA)/(HV)
and the vtx display, C.0.5 transport, C.1/C.1.5 with (ZC), Theorem C(b),
C.3), the DUAL-ACCEPTED §D4-R (rev 9 — T_can(f), L2/L5/L11/L12, D4R.1-SUM/
-EV, D4R.4-SUM/-EV, W(P̂), mult_P̂), §M-SPECIES (rev 4,
acceptance pending — under its pass spiral; the catalogue 𝒮_n^raw, SP-FIN,
SP-OUT's syntactic successor menus), and the plan's §1s/§2v notation. This note proves CTS-M's clauses EACH
GIVEN EXACTLY the hypothesis set displayed in V.1's per-clause ledger
(rev 2, pass-1 finding 7: "CTS-M GIVEN XHD" alone was not clean — some
clauses also need ENT-COUNT, computed tables, or per-instance checks,
and clause (v) is an open kernel, not a proved clause): XHD is [2b]'s
theorem (M4a-X + M4a's affine weights + M4b-T's compatibility), NEVER this
note's duty; the recorded discharge of the hypotheses upon [2b]'s acceptance
is the separate event [1v]-FULL (no new mathematics). CTS-M(v) HMC is an
OPEN KERNEL with its own probe, consumed as a displayed hypothesis by
COMP-Σ. This note does NOT own and nowhere re-derives what [3t]
§T-ASSEMBLY owns: the verdict pin VP, TB-CAP, TREE-EXP/ONE-F — the SOLE
marked→per-f conversion (plan §1s REV 9). Everything below is conditional
on the standing perimeter (§C + §B2-DEF + §D4-R acceptance conditions,
[2a]'s pending acceptance) and, where flagged, on XHD and HMC.)*

**What this note is.** The retired torus lemma was the only bridge from
Theorem C's per-branch masses to p-independent COEFFICIENTS; the pass-1
review demolished it, and the honest rebuild is a TRANSITION SYSTEM: one
fixed p-independent state space of syntactic cells (V.2), one polynomial
table family T counting per-cell fresh-assignment transitions (V.2), and
ONE measured theorem — CTS-M (V.1) — that types how counts (T), fixed-height
weights (g), resummed weights (G), entrance masses (ι), and marked masses
(μ̂) compose. Every left-hand side in this note is a MARKED-BRANCH mass μ̂
(§1s REV 9: μ̂(E) := Σ_η μ({f : (f,η) ∈ E}) — a sum over marks BY
DEFINITION, no disjointness claimed; one f may carry several marks), never
an f-event mass and never a density. What this note hands downstream: to
[3] RESUM, the kernel entries K_e = Σ T·G, the entrance vectors ι_e with
INIT-RAT, and the COMP identities; to [3t]/[4], marked branch masses per
(ε, γ, h) (ε concrete, carrying its entrance heights h_ent(ε) — rev 4)
and the count tables. What it does NOT claim: per-f
densities (RS.1-SH's object, assembled in [3] via [3t]'s TREE-EXP), tree
pruning or verdict semantics (VP — [3t]), finite-cap detectability
(TB-CAP — [3t]), exhaustion ([5]), or any unconditional probabilistic
reading of K_e (the nine-input ledger, CL-5, lives at [3] RS.PRE).

### V.0 The XHD hypothesis package, and the acceptance split

**(XHD) THE EXACT-HEIGHT-DOMAIN PACKAGE (named hypotheses of CTS-M's
measured clauses; owner [2b] — plan §2v REV 7; stated here in the exact
form this note consumes).** Throughout, a HEIGHT POINT h of a step or
template is the tuple of its reads' ℕ-height parameters (the parameters
[2a] SP.1 forgets; d_i height slots at step i).

Ambient objects, defined here so the package is CLOSED and refutable
(pass-1 finding 1): a LINEAR SET in ℕ^D is L(h₀; P) := {h₀ + Σ_{v∈P}
n_v·v : n_v ∈ ℕ} with base h₀ ∈ ℕ^D and a FINITE period list P ⊂ ℕ^D;
SEMILINEAR := a finite union of linear sets, consumed only with the
bases and period lists EXPLICITLY LISTED per template (the "congruence-
class translates of cone lattices" gloss is struck for this definition).
THE DISJOINT-COMPONENT CONVENTION (rev 3 — pass-2 finding 1: overlapping
listed sets double-count every shared point, and inclusion-exclusion is
NOT available since intersections need not be listed): every semilinear
domain this package consumes is a PARTITION — the listed linear sets are
required PAIRWISE DISJOINT, and [2b] proves XHD-d in exactly that form
(an explicitly listed disjoint decomposition). EVERY sum over components
in this note reads this convention: Σ over listed components = Σ over
the union, term by term, no overlap correction anywhere.
REALIZABILITY is per representative: for a source representative x of α
and h ∈ ∏_i ℕ^{d_i}, T_γ(x, h) := #{fresh-assignment chains from x
realizing (γ, h)} — a finite count at each level.

> **(XHD-w) WEIGHTS.** For every step datum (m, o) with source cell α and
> target cell β, and every height point h of that step's parameter space,
> a FIXED-HEIGHT weight monomial
>     g^{α,β}_{m,o}(h) = q^{−E(h)},   E affine in h with positive weights,
> EQUAL to the per-assignment C.1.5 fresh-volume ratio at height h — the
> conditional mass, given the source cylinder at ANY representative of α
> under ANY admissible history reaching it, of one fresh assignment
> realizing (m, o, β) at h. Indexed by SOURCE AND TARGET cells (pass-6
> concern 1: (m, o) alone is under-indexed).
> **(XHD-u) UNIFORMITY (NEW at rev 2 — pass-1 findings 2–3; the count/
> domain rectangularity neither XHD-w nor XHD-d stated).** For every
> template γ with source cell α: (u-R) REPRESENTATIVE UNIFORMITY — the
> per-assignment ratio of XHD-w and the count T_γ(x, h) depend on x and
> its history ONLY through (α, β⃗, m⃗, o⃗, h); (u-T) HEIGHT RECTANGULARITY —
> T_γ(x, h) = ∏_i T_{m_i,o_i}^{β_{i−1},β_i}(q) for EVERY h ∈ H(γ):
> the count is one h-independent value per step, and every assignment
> chain counted at one h has a counterpart at every other h ∈ H(γ).
> Consumed by every T·g and T·G display below ((iv) STEP, (vi) COMP).
> **(XHD-d) DOMAINS.** For every finite template γ (length 1 included),
> the EXACT realizable height domain H(γ) ⊆ ∏_i ℕ^{d_i} is SEMILINEAR
> with its bases/periods explicitly listed and its listed components
> PAIRWISE DISJOINT (a listed PARTITION of H(γ) — the rev-3 convention),
> and EXACT two-sidedly:
> (no orphan) T_γ(x, h) > 0 for some representative x ⟹ h ∈ H(γ);
> (no stray) h ∈ H(γ) ⟹ T_γ(x, h) > 0 for EVERY representative x of α.
> **(XHD-s) SUMS.** Per listed linear set, Σ_{h} ∏_i g_i(h_i) ∈ ℚ(q)
> with geometric denominators (1 − q^{−a}), convergent at every prime
> power evaluation (positive weights). By XHD-d's disjointness the
> finitely many component sums ADD EXACTLY to the H(γ)-sum — no overlap
> terms exist (rev 3); every union-sum below reads this convention.

WHAT §C ACTUALLY SUPPLIES, displayed (the honest split of XHD-w —
pass-1 finding 2). PROVED from the accepted §C, C.1.5(1) + Lemma
TYP(b), and displayed here as this note's one §C-derivable clause:

  (U-A) ASSIGNMENT UNIFORMITY AT A FIXED HISTORY. Fix ONE realizable
  prefix satisfying (ZC) and one transition-admissible read shape
  (species m, height point h). C.1.5(1) gives, for EACH fresh
  assignment (digit cell) of that read, conditional mass
  vol_nom(E_fresh) = q^{−#(strip pins)} · ∏_slots (alphabet size)^{−1},
  and BOTH factors are functions of the read's NOMINAL DIGIT INVENTORY
  (C.1(ii)) — the strip-pin count from the shape's staircase gap, the
  alphabet sizes from TYP(b)'s piece-map images — NEVER of which values
  the cell pins. Hence all fresh assignments realizing (m, o, β) at h
  FROM THAT PREFIX carry one common conditional mass. ∎

  NOT §C-derivable, HYPOTHESIZED in (XHD-u) (they are lumpability
  assertions about histories §C never compares): (u-R) — that the
  inventory depends on the history only through the retained cell pair —
  and (u-T)'s rectangularity. Both are [2b] territory (M4a's affine
  uniformity is exactly the inventory-through-state claim); both sit in
  this note's ledger (V.5) until [2b] discharges them.

At any SINGLE FIXED height point AND fixed history, XHD-w's
identification is therefore §C content via (U-A); XHD's genuine open
content is (XHD-u), the domain exactness (XHD-d), and the closed-form
sums (XHD-s) plus E's affine form — [2b] M4a/M4a-X/M4b-T territory
(the package as displayed EXTENDS [2b]'s deliverable by (XHD-u); plan
sync flagged for the next plan rev). This note's gate V-n3 (V.6) fixes
its height points and TWO entrance histories, EACH checked separately
with the common branch-frame inventory displayed (rev 3 — pass-2
finding 6), consuming only the (U-A) face per history.

**THE ACCEPTANCE SPLIT (plan REV 7, displayed — the status discipline
binding on every consumer of this note):**

  [1v]-COND  :=  acceptance of THIS NOTE — Theorem CTS-M proved GIVEN
                 XHD. Proof-duty split by clause:
                 XHD-FREE duties of this note: (i) SYNTAX, (ii) ACT,
                 (iii)'s mass vector (ι well-typed, ENT-AGG, INIT-RAT's
                 assembly shape), and the T-half of (iv)-POLY (Theorem
                 VAL(a) ONLY: tables + cell sizes polynomial at split
                 degree bounds — VAL(b)'s chain identification is NOT
                 XHD-free, rev 3);
                 XHD-CONDITIONAL duties, proved here GIVEN XHD
                 (INCLUDING (XHD-u) — rev 2): the G-bearing clauses —
                 (iv) STEP/PART/REP/MEAS, Theorem VAL(b)'s chain-count
                 identification (rev 3 — pass-2 finding 3: the count
                 layer beyond VAL(a) is (XHD-u)-conditional), and (vi)
                 COMP ((COMP-hΣ)
                 GIVEN XHD-d/s; (COMP-Σ) additionally GIVEN (v));
                 (v) HMC: an OPEN KERNEL — stated, probed, never proved
                 here; COMP-Σ and every kernel-power identity carry its
                 tag;
                 ENT-COUNT ((iii)): a NAMED COMPANION BURDEN, per
                 entrance shape.
  [2b]       :=  proves XHD (M4a, M4a-X, M4b/M4b-T).
  [1v]-FULL  :=  the RECORDED DISCHARGE of the XHD hypotheses upon
                 [2b]'s acceptance — a bookkeeping event, no new
                 mathematics; until it is recorded, every measured
                 clause below carries the XHD tag displayed at its site.

Downstream discipline (plan REV 6): M2's τ, RS.0, RS.PRE, SQ.2 condition
on CTS cells and on NOTHING finer or coarser; [3] RESUM consumes K_e and
ι_e from this note's clauses only (no source-mass division anywhere).

### V.1 Theorem CTS-M — the measured transition system (five conditional clauses + one open kernel)

Fix n. Let 𝒞_n be the branch-cell state space and T the table family, both
constructed at V.2. PER-CLAUSE HYPOTHESIS LEDGER (rev 2 — finding 7;
each clause is asserted GIVEN exactly its listed set, nothing less):
    (i)   GIVEN [2a] SP-FIN/SP-OUT (pending) + the computed lists (D1)–(D4)
          at each consumed skeleton;
    (ii)  (ii-a/b) GIVEN (iv)-POLY's correct valuation; (ii-c) a finite
          per-(n, q₀) AGREEMENT check, per instance;
    (iii) mass primitives hypothesis-free; ENT-AGG's aggregate GIVEN
          XHD-s (shallow); ENT-COUNT a named burden; INIT-RAT GIVEN
          XHD (shallow) + (ENT-U);
    (iv)  T-half GIVEN the computed tables (Theorem VAL(a); VAL(b)'s
          chain count additionally GIVEN (XHD-u) — rev 3); PART-1
          additionally GIVEN D4R.0 totality + countable additivity +
          the null no-finite-height remainder (rev 3, V.3(iv)); measured
          faces GIVEN XHD-w + (U-A) + (XHD-u); resummed forms also
          GIVEN XHD-d/s;
    (v)   OPEN KERNEL — never proved here; (HMC-AUG) a separate named
          redesign hypothesis;
    (vi)  (COMP-h) GIVEN XHD-w's (U-A) face + (XHD-u); (COMP-hΣ) also
          GIVEN XHD-d/s; (COMP-Σ) also GIVEN (v); the solve sentence
          also GIVEN ENT-COUNT, INIT-RAT, ESCAPE(E0), (ii-c).
Then:

> **(i) SYNTAX — fixed state set, partition displayed.** 𝒞_n is ONE finite
> p-INDEPENDENT SYMBOLIC index set: Out(s) is the SYNTACTIC successor menu
> ([2a] SP-OUT — never field-evaluated; a species inadmissible at a
> particular p keeps its label and contributes empty landing sets, handled
> by (ii)); every JREF_m^source is a uniformly labelled finite partition
> with its cell predicates DISPLAYED per V.2's computed-partition duty (a
> list of relation NAMES is not a partition with polynomial
> cardinalities); and for each m : s → s′ the TARGET-CELL MAP is displayed
> and lands in JREF^src(s′) under the SAME global definition — matrix
> indices type-check, and no species-relative cell ever appears as an
> index. [Ledgered: CL-13.]
>
> **(ii) ACT — active/empty-cell semantics at every prime.** For each
> prime power q₀, Act_{q₀} := {(s, α) ∈ 𝒞_n : |α|(q₀) > 0} (|α| = the
> cell-size polynomial). Then: (ii-a) NO-ENTRY — for every source active
> at q₀, every table/kernel entry INTO a target inactive at q₀ evaluates
> to 0 there (a landing forces a concrete target state), and ι of (iii)
> is supported on Act_{q₀}; (ii-b) DELETION COMPATIBILITY — ordering
> states active-first, K_e(q₀) is block-triangular [[A, 0],[C, D]]: the
> realized system at q₀ IS the A-block ("chain" struck at rev 2 — rows
> are MARKED OFFSPRING rows per (iv)-PART-2, a branching-kernel reading,
> not a stochastic chain), every measured statement
> of (iii)–(vi) reads ONLY the A-block, so deleting empty rows/columns at
> each prime is COMPATIBLE with the one fixed symbolic matrix; (ii-c)
> ACTIVE-VALUE — the realized value at each q₀ is DEFINED through the
> active subsystem alone (β_A = A·β_A + b_A, the ι-pairing reading only
> A-block coordinates); the burden is AGREEMENT: at the finitely many q₀
> with empty cells, the symbolic ℚ(q)-solution's value component, after
> cancellation, EVALUATES to the active-subsystem value — any
> det(I − D)(q₀) = 0 checked REMOVABLE on that component. A formal row
> out of an empty cell is NEVER cited as a probability; no division by a
> zero cell mass occurs anywhere.
>
> **(iii) INIT — entrance mass AND entrance count, both refined by
> ENTRANCE SHAPE; entrance heights RETAINED IN ε (rev 4 — pass-3
> finding 1: h_ent is a displayed PROJECTION of ε, never an independent
> parameter).** An ENTRANCE SHAPE ε
> into (e, β₀) is a NEW object of this note (rev 2 — finding 9: it is
> NOT a §D4-R shape-prefix, which forgets selection data): the TRIPLE
> ε := (P̂, b, σ_sel) of a shallow CONCRETE §D4-R shape-prefix P̂ —
> which RETAINS its per-node heights h_r (the (e, h, g, μ, a) tuples)
> and its per-read side heights u*_r (§D4-R L3, rev 9) — a designated
> continuing branch b entering the size-e block landing in cell β₀, and
> the branch-selection record σ_sel = (s_r at every shallow branching
> cell b passed — L11's encoding data, lifted into the label), so
> entrances are POST-SPLIT objects: at a shallow split each sibling
> carries its OWN ε and its OWN mark.
> HEIGHT PROJECTION (the rev-4 unification): h_ent(ε) := the tuple of
> ε's RETAINED height data — the (h_r, u*_r) pair vector over P̂'s reads
> (exactly the ℕ-height parameters [2a] SP.1 forgets) — a FUNCTION of ε,
> displayed, no free height variable anywhere: one concrete ε FIXES its
> entrance heights. TEMPLATE/INSTANTIATION (how heights are ranged):
> ε̊ := ε's height-forgetting TEMPLATE (SP.1 applied to P̂, selection
> data kept); the family {ε̊} is FINITE ([2a]/M1 for the P̂-templates;
> L5's finite eligible-continuation menus for the σ_sel's); H(ε̊) := the
> exact realizable entrance-height domain of the template (XHD-d on the
> shallow layer); and the INSTANTIATION MAP h ↦ ε̊[h] (write the heights
> h into the template's retained slots) is a BIJECTION from H(ε̊) onto
> {concrete ε with template ε̊} — D4R.1-SUM is cited ONLY at concrete ε,
> where P̂ is a genuine §D4-R shape-prefix (pass-3 F1's two horns
> closed: no duplication, and the instantiation map displayed).
> Primitives, per CONCRETE ε (h_ent(ε) determined by ε):
>     ι_{e,ε,β₀}(p) := the D4R.1-SUM MARKED mass μ̂ of the
>       entrance family refined by ε (each summand Theorem
>       C(b); an f entering twice carries two marks — a μ̂-object,
>       never an f-event mass);
>     I^ent_{ε,β₀}(q) := #{realized shallow entrance prefixes of
>       shape ε whose continuation lands in β₀} — a MARKED
>       count, with ledger exponent A(ε) := §D4-R's A(P̂) (a function
>       of ε since u*_r ∈ P̂ — L3; affine in h_ent(ε) across each
>       template's instantiations, [2b] M4a) and pool dimension
>       W_ent(ε) := Σ_{r ∈ reads(ε)} w_r·d_r (= §D4-R's W(P̂) —
>       height-free, L3 rev 9: W consumes no u*_r, so ONE degree bound
>       per template).
> ENT-COUNT (named burden): each I^ent_{ε,β₀} is one polynomial
> in q of degree ≤ W_ent(ε), computed as a CTS path count through the
> shallow layer. I^ent_{ε,β₀} = |β₀| is NOT general — a per-family
> theorem, displayed wherever used. Counts at different ε are NEVER
> added raw (distinct A(ε)). ENT-AGG (the derived aggregate — masses DO
> aggregate; rev 2, finding 10 — its conditionality split; RE-INDEXED
> at rev 4 on the template/instantiation pair): ι_{e,β₀} :=
> Σ_{ε̊} Σ_{h ∈ H(ε̊)} ι_{e,ε̊[h],β₀} — entrance heights are summed HERE
> and nowhere else, each concrete ε hit EXACTLY ONCE (the instantiation
> bijection). The primitives and every FINITE partial sum are
> hypothesis-free (μ̂-additivity over disjoint mark families — distinct
> concrete ε give distinct marked pairs); CONVERGENCE of the full
> aggregate (infinitely many instantiations per template) is GIVEN
> XHD-s on the shallow layer,
> and (iv)-REP is invoked ONLY where a common continuation factor is
> pulled out ((COMP-AGG)), never for the sum's definition.
> INIT-RAT (named burden): each ι_{e,(s,α)} ∈ ℚ(q), hence
> ι_e ∈ ℚ(q)^{𝒞_n} — GIVEN XHD on the shallow layer; CITED by RS.2.
> The pairing ι_e^T β_e is the μ̂-typed MARKED-entrance total over
> post-split marks — consumed by (COMP-AGG) and the gates, NEVER a
> clause of the density R_σ (RS.1-SH assembles R_σ — [3]).
>
> **(iv) STEP — correctly normalized measured rows.** One-step kernel
> entry, from ONE representative x ∈ α:
>     K_e(q)_{(s,α),(s′,β)} := Σ_{m: s→s′} Σ_{o continuing}
>       T_{m,o}^{α,β}(q) · G^{α,β}_{m,o}(q)    — NO source-mass division,
> G^{α,β}_{m,o} := Σ_{h ∈ H(γ¹)} g^{α,β}_{m,o}(h) the resummed one-step
> height mass over XHD-d's exact length-1 domain (well-typed from XHD
> alone; no HMC at k = 1; rationality = XHD-s per component over the
> PAIRWISE DISJOINT listed components, finitely many — rev 3). UNIFORMITY CONSUMPTION, displayed at the
> product (rev 2 — findings 2–3: T·G is NOT licit from XHD-w/d alone):
> the height-resolved row is Σ_{h ∈ H(γ¹)} T_{m,o}^{α,β}(h)·g(h) with
> T(h) := #{fresh assignments producing (m, o, β) at h}; it equals
> T·G because (U-A) makes g one constant per (m, o, β, h) at the fixed
> history, (XHD-u)(u-R) makes that constant and the count depend only on
> (α, β, m, o, h), and (XHD-u)(u-T) makes T(h) = T one h-independent
> count — Σ_h T(h)·g(h) = T·Σ_h g(h) is EXACTLY (u-T), else false in
> general. Each g-summand is ALREADY conditional on the
> source cylinder (XHD-w = the C.1.5 ratio); dividing again inflates the
> conditional. K_e is entrance-height-FREE: entrance heights ride in ε
> (retained data, rev 4), hence in ι alone.
> Sub-clauses: (iv)-POLY — every entry T is one polynomial of degree
> ≤ W_loc(m) and every cell size one polynomial of degree ≤ W_state(s)
> (SPLIT bounds — a source-cell size belongs to (s, α), not to any
> outgoing m), valued correctly at every prime power, with V.2's
> EXPONENT-MAP AUDIT; (iv)-PART — RETYPED at rev 2 (finding 5: one digit
> cell may carry SEVERAL eligible (side, ψ) continuations — D4-R L5 —
> so the (m, o, β)-indexed sets do NOT partition the pool). Two faces:
> (PART-1, the partition identity, per representative) the DIGIT CELLS
> of the read partition the fresh pool (D4R.0/L5), each cell counted
> ONCE; summing the per-cell conditional masses over the whole partition
> (all shapes, heights, values, terminal cells included) gives 1 —
> a COUNTABLE partition across heights, mass 1 by the rev-3 route at
> V.3(iv) (fixed-height pools finite via C.1.5(1), countable additivity,
> null no-finite-height remainder — NOT a finite-pool identity). (PART-2, the marked offspring row)
> the kernel row Σ_{m,o,β} T·G counts each branching cell once PER
> eligible continuing mark, so Σ_{m,o,β} T·G + (terminal conditional
> mass) = 1 + (branch surplus), surplus := the mass of continuing marks
> beyond each cell's first — a MARKED OFFSPRING mass, possibly > 1: NO
> substochasticity is claimed for K_e's rows; any substochastic reading
> routes through PART-1 alone. (At n = 3 the surplus vanishes
> identically — two continuing clusters need sizes ≥ 2 + 2 > 3, so no
> digit cell carries two continuing marks; first possible surplus at
> n = 4. Verified over the V.6 rosters.)
> (iv)-REP — WEIGHTED representative independence: the MEASURED
> row (T·G)_{m,o,β} is identical from every representative of α
> (cardinality-row equality alone is insufficient) — the lumpability
> clause M2(ii) consumes; (iv)-MEAS — RETYPED at rev 3 (pass-2 finding
> 2: ordinary-source disjointness contradicts D4-R L5 — one digit cell
> may carry two eligible (side, ψ) continuations whose next-node strata
> are literally EQUAL as f-sets; PART-2 exists because these sets do
> NOT partition): every (m, o, β, height-class) summand is a measurable
> sub-event of the MARKED source space {(f, η)} — a finite-level digit-
> cell union (D4R.0/L12) with the continuation mark ADJOINED to the
> finite-level map — and the summands are pairwise disjoint IN THE
> MARKED SPACE; as f-events only the DIGIT CELLS are disjoint. No
> ordinary-source disjointness is claimed anywhere.
>
> **(v) HMC — height-domain Markov compatibility. OPEN KERNEL, displayed
> hypothesis.** For every template γ, the whole-template exact domain
> FACTORS stepwise:
>     H(γ) = ∏_i H(γ¹_i),   γ¹_i := (β_{i−1} →^{m_i,o_i} β_i),
> each factor depending ONLY on the retained state β_{i−1} and the step
> data — never on earlier height choices — so Σ_{h ∈ H(γ)} ∏ g_i(h_i) =
> ∏_i G^{β_{i−1},β_i}_{m_i,o_i}. TERMINAL-FINAL EXTENSION (rev 4 —
> pass-3 finding 3, the displayed signature): templates INCLUDE those
> whose FINAL step carries a terminal outcome o_k; there β_k := the
> absorbing column label [o_k] — an EXIT OBJECT ((iv)-PART's absorbing
> columns; verdict semantics [3t]'s, the label consumed only as a
> column index) — the step's height coordinates, weight g, and count T
> typed as for any read, H(γ¹_k) and G_k reading verbatim, and NO
> target-cell map consumed ((D4)'s duty covers continuing outcomes
> only). The pinned HMC probe's step 2 (V.4) is a literal instance of
> THIS signature. (HMC-AUG) — a SEPARATE named redesign
> hypothesis, NOT a consequence of HMC (rev 2, finding 12; ledgered
> V.5): if a global cone inequality couples successive steps, ONE round
> of 𝒞_n refinement by finitely-valued boundary/gap data restores the
> factorization; finite-memory repair need not be possible at all — a
> second surviving coupling is R2's wall channel. Until HMC closes,
> K_e(p)^k is NOT a theorem about the process and only the unfactored
> per-template sum (COMP-hΣ) holds.
>
> **(vi) COMP — the composition identities, μ̂-typed.** For every
> finite path template γ = (β₀ →^{m₁,o₁} β₁ → … → β_k) in block e and
> every CONCRETE entrance shape ε into (e, β₀) (ε carrying its retained
> entrance heights h_ent(ε) — rev 4): the MARKED EVENT of
> (ε, γ, h) is the family of marked pairs (f, η) — its MARK-INDEX
> family (the realized histories η) is FINITE per level and its level-N
> residue census is finite (D4R.4); the f-fibers are p-adic boxes,
> generally INFINITE (rev 2, finding 13 — never "finitely many f") —
> whose branch η has entrance shape ε (entrance heights h_ent(ε)),
> template γ, height point
> h; its mass is μ̂ := Σ_η μ(S(η, ⊤)) (V.4 — a sum over marks; equal-
> strata branches each contribute their own summand). Then:
>     (COMP-h)  at every concrete ε and fixed h ∈ H(γ):
>       μ̂(marked event of (ε, γ, h) at p) = ι_{e,ε,β₀}(p)
>         · ∏_{i=1}^k [T_{m_i,o_i}^{β_{i−1},β_i} ·
>                       g^{β_{i−1},β_i}_{m_i,o_i}(h_i)](p);
>     count shadow: I^ent_{ε,β₀}·∏_i T (same concrete ε).
>     (COMP-hΣ)  GIVEN XHD-d/s, NO HMC (rev 2, finding 11 — the
>       unfactored height sum carries its OWN name; "COMP-Σ" is ONLY
>       the factored form): Σ_{h ∈ H(γ)} μ̂(…) = ι_{e,ε,β₀} ·
>       Σ_{h ∈ H(γ)} ∏_i [T·g(h_i)] — a well-defined XHD-s series,
>       per template;
>     (COMP-Σ)  GIVEN additionally (v) HMC — the factored form:
>       Σ_{h ∈ H(γ)} μ̂(…) = ι_{e,ε,β₀} · ∏_{i=1}^k [T·G]_i;
>     (COMP-AGG)  summing (COMP-Σ) over entrance heights (via the
>       instantiation bijection) then over templates ε̊ via ENT-AGG
>       (licit by (iv)-REP): Σ_{ε̊} Σ_{h ∈ H(ε̊)} (COMP-Σ at ε̊[h]) =
>       ι_{e,β₀} · ∏ (T·G) — the
>       FAM-side μ̂-identity RS.PRE/RS.1 consume; masses aggregate,
>       counts do NOT.
> COMPOSITION-TYPING DUTY: every consumer sums entrance heights EXACTLY
> ONCE (ENT-AGG's instantiation sum) and path heights EXACTLY ONCE,
> via (COMP-h)→(COMP-hΣ)→(COMP-Σ) — G never at a height point, g never
> in a kernel entry. GIVEN XHD, (i)–(v), ENT-COUNT, INIT-RAT, (ii-c),
> and ESCAPE(E0) on the
> ACTIVE submatrix: ρ(A) < 1 at each prime evaluation, the Neumann
> series converges, and det(I − K_e) ≢ 0 in ℚ(q) — hence the rational
> solve exists; every downstream fixpoint assertion carries this
> conditionality until E0 and (v) close.

### V.2 The state space 𝒞_n, the branch-cell decision, and the tables T

**(CTS-S) THE STATE SPACE.** A SKELETON s is a bounded current-state datum:
residual degrees/multiplicities, anchor a, tower phase — the [2a] SP.1
stage/side/residual-shape fields of the CURRENT node, values and heights
forgotten. Out(s) := the finite p-INDEPENDENT SYNTACTIC menu of outgoing
move-species labels emittable from s ([2a] SP-OUT + M1 bookkeeping ALONE,
evaluated over NO residue field). The SOURCE partition of s's concrete
states is the MEET over the WHOLE menu:
    JREF^src(s) := ⋀_{m ∈ Out(s)} JREF_m^source,
JREF_m^source := the common refinement of
 (a) the per-coordinate ANCHOR-TWISTED VAL.1 cell partitions of the
     residual-factor value tuple (below), and
 (b) the RELATIONAL strata of exactly the finitely many polynomial
     relations m's displayed evaluation/admissibility maps mention:
     factor collision/distinctness (φ_i = φ_j), hinge-ratio cells (the
     twisted cell of t_i/t_j), and the norm/trace strata tested by
     (NA)/(HV) (§C C.0) and the nonzero-endpoint convention
— EVERY source observable used by EVERY syntactically-listed outgoing
species, admissibility judged over no field (an m inadmissible at some p
keeps its label; its landing sets are empty there — (ii)'s zero-extension
is built into the definition). The CTS states are 𝒞_n := {(s, α) :
α ∈ JREF^src(s)}; finiteness follows from finiteness of Out(s) (a finite
meet of finite partitions); cells with IDENTICALLY-zero size polynomial
are deleted from 𝒞_n once, symbolically.

**BRANCH-CELL DECISION (plan REV 8, binding).** A CTS cell is a
BRANCH-CELL: its concrete states are states of ONE continuing branch of
T_can(f) in that branch's own frame, and the CTS walks SINGLE branches —
every transition consumes the branch's next read, T counts per-branch
fresh assignments from one representative, every measured step factor is
a per-branch Theorem C(b)/C.1.5 object. The alternative (f-cells with
set-valued transitions) is REJECTED: §C has no mass theorem for
joint-over-branch loci and the tables would not be §C-citable.
CONSEQUENCE (binding on FAM): BRANCHING EXITS TO THE FAM LAYER — a read
whose digit cell carries several eligible (side, ψ) continuations
contributes each continuation as a SEPARATE branch entry, composed
multiplicatively by [3t]'s (SIB)/TREE-EXP at the REV-10 routing sites
(b_e^split at DEEP splits; RS.1-SH's convolution at ROOT/SHALLOW splits),
never a raw sum of separately-inserted child entrances; MULTIPLICITY
WEIGHTS (mult, D4R.1) are carried by the FAM aggregation — never inside
T, never inside a single-branch path product.

**THE COMPUTED-PARTITION DUTY (CTS-M(i)'s deliverable — CL-13; what must
be COMPUTED, displayed).** The meet symbol above is a construction
RECIPE; the clause-(i) deliverable, per skeleton s consumed by any
downstream instance claim, is the DISPLAYED LIST:
 (D1) the menu Out(s) — the [2a] SP-OUT letters from s;
 (D2) the GENERATOR LIST — every (a)-generator (one twisted VAL.1
      partition per residual coordinate, the twist exponent displayed)
      and every (b)-generator (each relation named WITH its polynomial
      and its exceptional-characteristic convention, e.g. the char-2
      collapse of a distinctness stratum);
 (D3) the MEET LIST — the resulting finite uniform partition: explicit
      cell predicates as boolean combinations of (D2)'s generators,
      fixed labels, per-cell size polynomials |α|(q) (degree ≤
      W_state(s));
 (D4) the TARGET-CELL MAP per m : s → s′, displayed, landing in
      JREF^src(s′) under the same global definition.
This note displays the recipe and computes (D1)–(D4) IN FULL at V.6.1–
V.6.3 for the three gate blocks (rev 2 — finding 14: displayed in the
note, not referred to a seal); the FULL per-skeleton lists at each
consumed n are the TABLE-BUILD deliverable — [1v]-COND acceptance
requires them for every skeleton any downstream instance claim
consumes (V.5).

**VAL.1 (the stratified fiber calculus — the (a)-generators).** For each
node species the EVALUATION MAP V sends the node's side-pattern value
tuple to its transported vertex value (C.0's display: vtx =
z̄^{−μm̂}·z̄^{a}·((R_anch/ψ^μ) mod ψ)); the fiber-count function
c_V : Fˣ → ℕ, c_V(t) := #{pattern values : V = t}, is NOT constant (the
pass-1 counterexample: values 0 and 1 at fixed shape). VAL.1's content:
c_V is CONSTANT on the cells of an explicit p-independent stratification
of the target. Worked instance (V(A,B) = Aα + B, A, B ∈ F_qˣ; target
coordinates t = xα + y in the basis {α, 1} of F_{q²}/F_q): THREE cells —
FG = {x ≠ 0, y ≠ 0}, c_V = 1; FL = F_qˣ·α (y = 0), c_V = 0 (B = 0
prohibited); FS = F_qˣ (x = 0), c_V = 0 (A = 0 prohibited). ANCHOR
ALIGNMENT (probe-forced, binding): at anchor exponent a_eff ≠ 0 the cells
apply to the TWISTED target α^{−a_eff}·t, never to t in the fixed frame —
fixed-frame cell counts are PROVABLY char-dependent (the value probe,
verification/value_probe.py + results: 32 non-universal series, a q mod 3
split at a_eff = 2), while TWISTED cells are fiber-constant EXACTLY at
all 24 census q. Cell sizes and counts are universal polynomials; the L3
necklace/Gauss counts are the depth-0 instance.

**(CTS-T) THE TABLES.** For every source cell α ∈ JREF^src(s), species
m : s → s′ ∈ Out(s), full outcome label o (next-node data + all
hinge-value cells + collision pattern, or a terminal label — the [2a]
L5-case letters; verdict SEMANTICS is [3t] VP's, consumed here only as
absorbing column labels), and target cell β ∈ JREF^src(s′):
    T_{m,o}^{α,β}(q) := #{fresh assignments producing (m, o, β) │ one
                          representative source state in α}.
**Theorem VAL (the count layer — split degree bounds).** (a) LOCAL: every
entry T_{m,o}^{α,β} is ONE polynomial in ℚ[q] of degree ≤ W_loc(m), and
every cell size |α| ONE polynomial of degree ≤ W_state(s), each valued
correctly at every prime power q. (b) CHAIN — GIVEN (XHD-u)'s COUNT
FACE (RELABELED at rev 3, pass-2 finding 3: NOT XHD-free): for each
finite path template γ, the PER-REPRESENTATIVE linked count from one
fixed source representative EQUALS the PATH PRODUCT C_γ(q) =
∏_i T_{m_i,o_i}^{β_{i−1},β_i}(q). Clause (i)'s one global partition
makes the product a DEFINED matrix operation (typing only); the
IDENTIFICATION with the actual linked count needs every concrete
target representative inside each intermediate cell to emit the SAME
next-step count — exactly (u-R)'s count clause + (u-T), hypothesized
in (XHD-u), never proved here (alternative discharge: the table build
proves representative-uniform count rows per species and the ledger
cites that proof). The degree bound ≤ W(γ) = Σ_i W_loc(m_i) holds for
the ACTUAL linked count unconditionally (per-step pools bound it); the
FULL realization count is PER (concrete) ENTRANCE SHAPE: Ĉ_{ε,γ}(q) =
I^ent_{ε,β₀}(q)·C_γ(q) (same (XHD-u) tag, plus ENT-COUNT), degree
≤ W̄(ε,γ) = W_ent(ε) + W(γ) — the entrance factor never omitted, never
smuggled into T, never replaced by |β₀| without the displayed
one-unrestricted-copy theorem, never summed raw across entrance shapes
with different A(ε). NO path product is a mass or a full count without
its initial factor: ∏ T counts extensions from ONE representative.

**EXPONENT-MAP AUDIT (a (iv)-POLY burden, displayed).** Every norm/trace/
ratio/collision exponent map in every table's evaluation chain is audited
for congruence factors (e.g. the image size of t ↦ t^a on F_{q^g}ˣ is
(q^g − 1)/gcd(a, q^g − 1)); "triangular/monomial shape" alone is NOT
accepted as a polynomiality argument — each such factor either cancels
against a displayed cell-size factor or splits the cell into displayed
congruence sub-cells with their own labels ((D2)'s conventions).

**DEG-CONS (per-outcome degree conservation — the [3t]/[3] display duty
executed at THIS note's table build; CL-11).** For EVERY branching
outcome o in the CTS outcome roster: m ≥ 2 children, each child cluster
size e_j ≥ 1, Σ_j e_j ≤ e — per member, from M1's degree identity applied
to the cell's residual-factor degrees. The check runs over the FULL
roster of each computed table block ((D1)–(D4)); an analogy to "the same
degree identity" is not the check. Executed and DISPLAYED for the V-n3
blocks (V.6.1–V.6.3); a full-roster obligation of the table build at
each consumed n.

**(†) epistemics at the count layer (recalled, binding).** Per table
entry/row (degree bound W_loc(m)), per cell size (W_state(s)), per finite
template (W(γ)), per full count (W̄(ε,γ)): 0 ≤ C(q) ≤ q^W at every prime
power, so agreement with any R ∈ ℚ(q) at all prime powers forces R
polynomial of degree ≤ W — the unique interpolant through any W+1 census
points; one exact census mismatch surviving adjudication CONCLUSIVELY
refutes ℚ(q)-universality (refute-or-support; support at surplus
m − W − 1 is evidence, never proof). Aggregates only via (†-AGG): the
marked level-N count marked(N) := Σ_{(ε,γ): thr ≤ N} Ĉ_{ε,γ}(q)·
q^{nN−A(ε)−A(γ)} — each summand at its OWN displayed normalization, a
μ̂-object NEVER identified with decided_σ(N) (instance (2), which is
[3t]/[4] territory via input (vii)'s tree-shape sum). Rev 3: the
per-template and full-count rows read the ACTUAL linked counts — the
bounds are unconditional, while the identification with ∏T and
I^ent·∏T carries VAL(b)'s (XHD-u) tag; a census mismatch there indicts
the conjunction, per V.6.5's attribution discipline.

### V.3 The measured clauses — proof routes and per-clause status

**(i) SYNTAX — XHD-free; status RESTATED at rev 2 (finding 6: full-depth
SYNTAX was overstated).** What is proved HERE: the meet of finitely many
finite uniform partitions is finite and uniform, and labels are fixed by
(D2)/(D3)'s conventions — GIVEN finiteness and p-independence of Out(s),
which is [2a] SP-FIN/SP-OUT (syntactic menus over the budget
inequalities (B1)–(B5), no field evaluated) and INHERITS [2a]'s PENDING
acceptance. What is NOT proved here: the uniform partitions themselves,
polynomial cell sizes, target maps, and exponent audits at any skeleton
whose lists are uncomputed — each is a PER-SKELETON burden, executed in
this note ONLY for the three V.6 gate blocks (displayed there in full).
Clause (i) at full depth is therefore CONDITIONAL on [2a] + the
table-build deliverable (CL-13), never "proved by construction" bare.

**(ii) ACT — XHD-free; status: (ii-a)/(ii-b) proved GIVEN (iv)-POLY's
correct valuation; (ii-c) a displayed per-instance burden.** (ii-a): a
table entry counts fresh assignments landing ON a concrete target state;
at q₀ with |β|(q₀) = 0 there is no state to land on, the definitional
count is 0, and (iv)-POLY's "valued correctly at every prime power"
forces the polynomial's value there to be 0; ι's support claim is the
same argument at the entrance layer. (ii-b): order states active-first;
by (ii-a) every active-source → inactive-target entry vanishes at q₀, so
K_e(q₀) = [[A, 0],[C, D]] and every measured statement reads the A-block
(the realized process has no mass on inactive cells — their defining
predicates are unsatisfiable over F_{q₀}). (ii-c) AGREEMENT is a
FINITE per-(n, q₀) verification duty (finitely many q₀ have empty
cells): symbolic-solution value = active-subsystem value after
cancellation, det(I − D)(q₀) = 0 checked removable on that component —
exercised by RESUM-n3's wild-p ACTIVE-VALUE layer ([3]'s gate), recorded
here as the clause's standing check, never a blanket det ≠ 0 claim. NO
general deletion-compatibility theorem for the rational solution is
claimed anywhere (finding 8): agreement is per-instance, finite,
ledgered at V.5(5).

**(iii) INIT — per-concrete-ε primitives hypothesis-free; the
aggregate GIVEN XHD-s (shallow); ENT-COUNT, (ENT-U), INIT-RAT displayed
burdens.** WELL-TYPEDNESS of ι_{e,ε,β₀} (proved): ε = (P̂, b,
σ_sel) is V.1(iii)'s refined entrance label — a CONCRETE §D4-R
shape-prefix P̂ (retaining its heights h_r, u*_r — L3 rev 9) with a
designated continuing branch and recorded
selection data s_r (L11), the triple a NEW object of this note (finding
9) — so the entrance family is a sub-family of
Pref(P̂) cut by the landing-cell condition on the continuing branch
(cell data, L5); the entrance heights h_ent(ε) are NOT a separate cut
but ε's OWN retained data (rev 4 — pass-3 finding 1: h_ent lives IN P̂
via (h_r, u*_r), no independent height parameter);
each member is a single realized branch prefix η with its Theorem C(b)
mass μ(S(η,⊤)), and ι is their SUM — a D4R.1-SUM sub-sum, hence a
μ̂-object; an f entering twice carries two marks, matching the
per-branch solve. POST-SPLIT TYPING (proved by construction): siblings
at a shallow split differ in s_r, hence carry DISTINCT ε — ι never
aggregates a pre-split f-event or a joint-sibling locus. ENT-AGG
(finite partial sums proved hypothesis-free; the full aggregate GIVEN
XHD-s on the shallow layer — finding 10): μ̂ is additive over disjoint
mark families (distinct concrete ε give distinct marked pairs;
the instantiation bijection hits each ε once);
convergence over the infinitely many instantiations is XHD-s's, and
(iv)-REP enters ONLY when the aggregate is paired with a common
continuation factor ((COMP-AGG)), never for the sum itself. ENT-COUNT
(BURDEN, per template): each I^ent_{ε,β₀} is one polynomial of degree ≤
W_ent(ε) (= W(P̂), height-free — L3)
— Theorem VAL's machinery applied to the shallow cascade (root cells =
the L3 depth-0 instance; each shallow read a table step; the
landing-cell refinement a target-cell condition). (ENT-U) (BURDEN,
NAMED at rev 2 — finding 4: without it INIT-RAT is NOT derivable, since
XHD-s covers products of the g_i, not an arbitrarily entrance-height-
varying polynomial multiplier): over each listed linear set c of
H(ε̊) (the template's entrance-height domain), the
polynomial I^ent, viewed across the instantiations ε̊[h] with h ∈ c,
=: I^ent_c is ONE polynomial CONSTANT in
h on c — [2b] M4b's h_ent-constancy clause, never assumed here.
INIT-RAT (BURDEN, GIVEN XHD on the shallow layer + (ENT-U)):
ι_{e,(s,α)} = Σ_{ε̊} Σ_{c ⊆ H(ε̊)} I^ent_c(q) · Σ_{h ∈ c}
p^{−A(ε̊[h])}, c ranging over XHD-d's PAIRWISE DISJOINT listed
components of H(ε̊) (the rev-3 partition convention — each
instantiation counted exactly once, no overlap correction), with
A(ε̊[h]) affine in h
(M4a) — the inner sum XHD-s geometric, the outer sums finite — hence
∈ ℚ(q); CITED by RS.2.

**(iv) STEP — T-half XHD-free (Theorem VAL(a) ONLY; VAL(b)'s chain
identification is (XHD-u)-conditional — rev 3); measured sub-clauses
GIVEN XHD-w's (U-A) face + (XHD-u), resummed forms also XHD-d/s (the
V.1 ledger).**
 (iv)-POLY: the T-half is Theorem VAL(a) — VAL.1 twisted-cell constancy
   makes each (m, o, β) count a product of cell sizes and fiber counts
   over the displayed strata, polynomial after the EXPONENT-MAP AUDIT
   (V.2); the split bound W_state(s) covers source-cell sizes (a source
   cell belongs to (s, α), not to any outgoing m, and may exceed some
   W_loc(m)). Status: mechanism displayed; per-entry closed forms are
   the table-build deliverable, gate-sealed at V.6.
 (iv)-PART (PART-1 GIVEN XHD-w's (U-A) face at fixed history + D4R.0
   totality + countable additivity + the null remainder + XHD-d/s —
   rev 3; the resummed faces GIVEN XHD-d/s + (XHD-u)) — retyped per
   finding 5, route COMPLETED per pass-2 finding 4 (mass 1 is NOT a
   finite-pool consequence of C.1.5(1)): AT EACH FIXED height point
   the fresh pool is finite and its DIGIT-CELL datum is a total
   single-valued function of the fresh assignment (digit cells
   partition — D4R.0/L5; the menu is total per [2a] SP-COMP,
   conditional on its stated perimeter); ACROSS heights the digit-cell
   decomposition of the source cylinder is COUNTABLE. PART-1's route,
   displayed: (a) TOTALITY — outside the no-finite-height locus every
   source point lies in exactly ONE digit cell (D4R.0); (b) COUNTABLE
   ADDITIVITY of the conditional measure over this countable
   partition; (c) NULL REMAINDER — the no-finite-height locus
   (all-window degeneracy) lies in the decreasing intersection of the
   height-≥-H strip cylinders, whose conditional masses → 0 (C.1.5
   strip volumes; XHD-s positive weights), hence μ-null; (d) each
   fixed-height block sums by C.1.5(1)'s conditional exactness —
   together, the per-cell ratios over the whole partition sum to 1.
   The CONTINUATION datum is NOT
   single-valued (L5's multi-eligible cells), so the (m, o, β)-indexed
   row is PART-2's marked offspring row: = 1 − (terminal mass) +
   (branch surplus), surplus ≡ 0 at n = 3 (V.1(iv)); no substochastic
   claim survives except through PART-1.
 (iv)-REP (GIVEN XHD-w's (U-A) face + (XHD-u)(u-R) — REP is (u-R)'s
   row-level consequence, restated as the checkable clause M2(ii)
   consumes): the measured row from x ∈ α is a function of
   (a) x's twisted VAL.1 cell data and (b) x's relational strata — by
   construction JREF^src(s) refines EVERY observable every listed
   species consumes, so the row is cell-constant PROVIDED the species'
   evaluation maps mention no observable outside the (a)/(b) generator
   list. That proviso is a PER-SPECIES CHECK of the table build
   (executed with (D2); refuter: JOINT-probe below); weighted (T·G)-row
   equality, not cardinality-row equality, is what is checked.
 (iv)-MEAS (stated lemma, GIVEN XHD-d; RETYPED rev 3 — pass-2 finding
   2): each (m, o, β, height-class) summand's f-PROJECTION is a
   finite-level digit-cell union (D4R.0 strata realized at the finite
   level L12/D4R.4 provides); the summand ITSELF is that union with
   the continuation mark ADJOINED — the fiber of a finite-level map ON
   THE MARKED SPACE {(f, η)}, the branch label a coordinate of the
   map. Disjointness holds in the marked space ONLY; two summands'
   f-projections can be literally EQUAL (D4-R L5). Multi-step events
   are the (vi) marked-event displays: finite mark-disjoint unions of
   finite-level marked cylinders, never single cylinders.

**ENTRANCE-HEIGHT THREADING (the REV 9 rule, RETYPED at rev 4 —
pass-3 finding 1: entrance heights are ε's retained data, not a free
argument).** K_e and every T/G/g factor are entrance-height-FREE; ι
is indexed by the CONCRETE ε (whose retained h_ent(ε) is displayed,
not a separate argument); (COMP-h) fixes ε and the path height h and
displays both; (COMP-Σ) sums h ONLY; ENT-AGG/(COMP-AGG) sums over the
instantiations ε̊[h] (i.e. entrance heights) EXACTLY ONCE.
Height elimination from the block unknowns (β carries no height index)
is RS.0(β)'s bisimulation — [3]'s theorem (CL-9), nowhere assumed here.

### V.4 COMP — the composition identities, HMC, and the [3t] interface

**The marked event, fully typed (the (vi) left side; plan §1s REV 9).**
The MARKED-BRANCH SPACE is M := {(f, η) : η ∈ T_can(f)}. The marked
event of (ε, γ, h) at p is the family of pairs (f, η) whose
branch η has entrance shape ε (entrance heights h_ent(ε), ε's retained
data — rev 4), template γ
(the CTS path of its in-block reads — single-branch, V.2's decision),
and height point h; its MARK-INDEX family is FINITE at each level and
its level-N residue census is finite (D4R.4) — the f-fibers themselves
are p-adic boxes, generally infinite (finding 13) — and its
mass is the MARKED MASS μ̂ := Σ_η μ(S(η,⊤)) — a sum over the mark index
BY DEFINITION: same-shape branches with literally EQUAL strata each
contribute their own summand (F1's instance is not an obstruction but
the typing's reason). NO ordinary event mass μ appears anywhere in
clause (vi); no disjointness across marks is claimed or needed.

**(COMP-h) — proof route (GIVEN XHD-w's (U-A) face + (XHD-u); ε concrete
and path height h FIXED).** Group the marked event by its entrance
prefix: each member extends exactly one ε-shaped entrance (heights
h_ent(ε)) landing in β₀. Per
entrance mark, the continuation mass along γ at h is the C.1.5
conditional chain — per step, (U-A) makes each fresh assignment's ratio
one common value at the fixed history, (XHD-u)(u-R) makes that value and
the count the SAME across representatives and histories reaching β₀
(the hypothesized lumpability face — findings 2–3, displayed, not
derived), giving T_{m_i,o_i}^{β_{i−1},β_i}·g(h_i) per step. Summing
over the entrance marks gives ι_{e,ε,β₀}·∏ T·g — the displayed
identity; the count shadow I^ent·∏ T is the same grouping at the count
layer (Theorem VAL(b) — carrying its (XHD-u) count-face tag, rev 3 —
+ ENT-COUNT, the same concrete ε on both sides — a marked-history
count). At a FIXED path height point AND one fixed entrance history, the
identity consumes only (U-A)'s §C-derivable content; V-n3 gates that
per-history face at each of its TWO entrance histories SEPARATELY,
with the common inventory displayed (V.6.4 — rev 3).

**(COMP-hΣ)/(COMP-Σ) — the naming discipline (finding 11).** Summing
(COMP-h) over h ∈ H(γ) GIVEN XHD-d/s yields the unfactored per-template
series (COMP-hΣ) — always well-defined, no HMC. The right side factors
into ∏(T·G), i.e. (COMP-hΣ) upgrades to (COMP-Σ), IF AND ONLY IF the
whole-template domain factors stepwise with state-only dependence —
exactly (v) HMC, a displayed open hypothesis. Until HMC closes, only
(COMP-hΣ) holds, and K_e^k is not a theorem about the process.

**HMC-probe (exploration-class, specced-and-pinned with this draft — NOT
yet run, no result claimed; the rev-8 spec,
typing-safe; tested family PINNED at rev 2, finding 12).** THE FAMILY:
p = 2, the V.6 objects — entrance ε := the A1 root entrance (designated
branch = the μ = 2 track; retained h_ent(ε) = (), V.6.4), source cell β₀, two
consecutive s_blk2 steps: step 1 := (m₂, o_double, β₁) at heights
h₁ = (k₀ = 2λ₁), λ₁ ranging over the censused domain {1, 2, 3}; step 2
— PINNED at rev 3 (pass-2 finding 5): SOURCE = β₁ (V.6.3 (D4): the
⊤-cell of the refined-cluster skeleton s_blk2⁽²⁾, recentered at y*,
|β₁| = 1); the depth-2 window is again NP over (0, v(h₀⁽²⁾)),
(1, v(h₁⁽²⁾)), (2, 0) in the RECENTERED branch frame (the s_blk2 form
one level down at the AUGMENTED anchor — tower phase depth 2; the
anchor exponent recorded from C.0.5 transport at the instance, a
monitored probe datum, exactly where HMC may fail); SPECIES m₂⁽²⁾ :=
the one-side stride-1 residual-degree-2 letter (V.6.3 (D1)'s m₂ read
at s_blk2⁽²⁾); sealed OUTCOME o₂ := o_inert (absorbing label
[e=1, f=2] — a TERMINAL-FINAL step in the (v)/(vi) signature (rev 4 —
pass-3 finding 3): its EXIT OBJECT is the absorbing column β₂ := [o₂]
(the [e=1,f=2] label as a target index — verdict semantics [3t]'s),
so the template γ = (β₀ →^{m₂,o_double} β₁ →^{m₂⁽²⁾,o_inert} [o₂]) IS a
literal instance of the displayed HMC/COMP template (β₂ typed, height
coordinate h₂ and weight g⁽²⁾ read verbatim; NO continuing target-cell
map is consumed because (D4) covers continuing outcomes only — the
terminal step needs none, not one that is "not needed");
HEIGHT COORDINATE h₂ := (k₀⁽²⁾ = 2λ₂), the depth-2 side height in the
recentered frame; source generators at s_blk2⁽²⁾ expected EMPTY by
V.6.3's executed check (the letter reads only h⁽²⁾'s own digits) —
the census READS the actual dependence rather than assuming it.
SEALED HMC-EXPECTED conditional domain and law, per fixed h₁: domain
{k₀⁽²⁾ = 2λ₂ : λ₂ ≥ 1} INDEPENDENT of λ₁; per-h₂ conditional mass
T_{o_inert}·g⁽²⁾ = [q(q−1)/2]·q^{−3λ₂}│_{q=2} = 2^{−3λ₂} (E⁽²⁾ = 3λ₂,
the V.6.3 affine form one level down). Censused pairs (λ₁, λ₂):
λ₁ ∈ {1, 2, 3}, all λ₂ whose event data are determined at box level
≤ N = 7 (the gate-B feasibility bound); the seal records the per-pair
determination levels BEFORE the census runs, and pairs undetermined at
N = 7 are recorded OUT OF SCOPE, never partially censused. Two layers: (a) COMP-h layer (typing check, no
HMC content) — sealed height pairs (h₁, h₂), exact census of
fixed-height marked masses vs ι·T·g(h₁)·T·g(h₂), only fixed-height
monomials g appearing; (b) HMC layer — for each FIXED h₁ across its
exact one-step domain, census the CONDITIONAL step-2 height domain and
per-h₂ mass law given (m₁, o₁, β₁ at h₁): HMC predicts both INDEPENDENT
of h₁ given β₁; after summing over h₂ ONLY, the fixed-h₁ two-step
marked mass equals ι·T·g(h₁)·(T·G)₂ — G only after the h₂-sum, h₁ never
summed. SCOPE (finding 12): the probe is a ONE-INSTANCE REFUTER testing
the CONJUNCTION {HMC at this template + XHD-w/(U-A)/(XHD-u) + (iv)-REP};
it cannot support (v)'s universal "every template" quantifier, and a
pass is evidence only. Any surviving h₁-dependence beyond the retained
state refutes the conjunction and — if adjudication (V.6's order)
localizes it to (v) — triggers (HMC-AUG)'s one refinement round, itself
a hypothesis (V.1(v)); a second coupling is R2's wall channel.

**(COMP-AGG) — GIVEN (COMP-Σ) + (iii).** Sum over the instantiations
ε̊[h] (h ∈ H(ε̊), i.e. entrance heights) then over templates ε̊ via
ENT-AGG: Σ_{ε̊} Σ_{h ∈ H(ε̊)} (COMP-Σ at ε̊[h]) = ι_{e,β₀}·∏(T·G) —
entrance heights summed exactly once, the FAM-side μ̂-identity. Counts
do NOT aggregate this way (distinct A(ε) across templates — V.1(iii)).

**THE [3t] INTERFACE (what this note HANDS OVER, and what it does NOT
claim — the plan's ownership fence, restated as binding).**
 HANDED to [3]/[3t]/[4]: (1) marked branch masses per (ε, γ, h) (ε
   concrete, carrying h_ent(ε) — rev 4)
   and their resummed forms — the (COMP-h)/(COMP-Σ)/(COMP-AGG)
   identities, every left side μ̂-typed; (2) the count tables T, C_γ,
   Ĉ_{ε,γ}, I^ent with their degree bounds; (3) K_e and ι_e as [3]
   RS.PRE consumes them (no source-mass division; ι paired once on the
   left; b_e is [3]'s object — this note supplies its T·G entries via
   (iv)-PART's absorbing columns, not its multilinear split formula);
   (4) DEG-CONS's per-outcome roster check at the computed blocks.
 NOT CLAIMED here: per-f densities or f-counts — every output of this
   note is a μ̂-object or a marked count; the marked→per-f conversion
   is [3t]'s TREE-EXP ALONE (its (ONE-F) dictionary, its tree fibers),
   and the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed MARKED-
   entrance total (RS.1-MARKED) — consumed by (COMP-AGG) and gates,
   NEVER summed into R_σ (the density is RS.1-SH's shallow convolution,
   [3]). Equating any μ̂ quantity of this note with an f-event mass or
   an f-count is a TYPE ERROR except through [3t]'s displayed
   conversion. VP, TB-CAP, tree pruning: [3t]'s, consumed only as
   terminal outcome LABELS in o. STATUS NOTE (2026-07-27): §T-ASSEMBLY
   is DUAL-ACCEPTED (Codex pass 8 + Fable confirm, both CLEAN on the
   rev-7 text — the EOF record); nothing in THIS note consumes a [3t]
   THEOREM — only the plan-level typing rule (§1s REV 9) and the
   ownership fence, so [3t]'s repair rounds do not propagate here.

### V.5 Honest perimeter (what is conditional, on what, and what is only evidence)

CONDITIONAL ON, named per the acceptance-record rule (plan §7):
 (1) XHD — OPEN, owner [2b] (M4a/M4a-X/M4b-T), INCLUDING the rev-2
   clause (XHD-u) (findings 2–3: representative uniformity (u-R) +
   height rectangularity (u-T) — hypothesized, NOT §C-derivable; the
   package extension is flagged for the next plan rev) AND the rev-3
   DISJOINT-COMPONENT form of XHD-d (pass-2 finding 1: [2b] proves the
   listed decomposition PAIRWISE DISJOINT — the partition convention
   every component sum reads). (XHD-u) also carries Theorem VAL(b)'s
   chain-count identification and the full-count formula Ĉ (rev 3 —
   pass-2 finding 3: the count layer beyond VAL(a) is never XHD-free).
   Every G-bearing
   clause ((iv) measured faces, (vi) COMP) is proved here GIVEN its
   V.1-ledger set; the discharge is the separate recorded event
   [1v]-FULL. Only (U-A) — assignment uniformity at a fixed history —
   is §C-derivable now (V.0, displayed derivation); domains and sums
   are not anticipated anywhere in this note.
 (2) HMC (CTS-M(v)) — OPEN KERNEL, its probe (family pinned) at V.4.
   Until it closes: (COMP-hΣ) per template only, K_e^k not a process
   theorem, and every downstream fixpoint claim carries the tag ([3]'s
   nine-input ledger, CL-5, item 6). (HMC-AUG) — the finite-memory
   augmentation REPAIR — is a SEPARATE named hypothesis (finding 12),
   not a consequence of HMC and not assumed anywhere.
 (3) ENT-COUNT, (ENT-U), and INIT-RAT — named burdens of clause (iii):
   shallow-layer polynomiality per entrance shape (degree ≤ W_ent(ε));
   per-linear-set h_ent-constancy ((ENT-U), owner [2b] M4b — finding 4:
   INIT-RAT is underivable without it); ℚ(q) assembly GIVEN XHD +
   (ENT-U). RS.2 cites INIT-RAT; it is not yet proved.
 (4) The VAL.1/JREF deliverables — the computed-partition lists
   (D1)–(D4) per consumed skeleton, the per-entry closed forms with the
   EXPONENT-MAP AUDIT, the per-species (iv)-REP observable check, and
   DEG-CONS's full-roster check: DISPLAYED duties of the table build,
   executed in this note only for the three V.6 gate blocks (displayed
   IN FULL there — rev 2, finding 14; nothing is "pinned in the seal"
   that is not also derivable from the note text).
   [1v]-COND acceptance requires the lists for every skeleton any
   downstream instance claim consumes at its n.
 (5) (ii-c) ACTIVE-VALUE agreement — a finite per-(n, q₀) check,
   exercised by RESUM-n3's wild-p layer ([3]); recorded, not proved.
 (6) Inherited: §C (rev 14 conditions incl. (SAE)'s dual-pass status as
   recorded at its acceptance), §B2-DEF, §D4-R (D4R.0-K's residual is
   [3t]/VP territory), and [2a] §M-SPECIES — acceptance PENDING; this
   note's (iv)-PART cites SP-COMP's per-read totality and so carries
   SP-COMP's conditionality (D4R.0-K, (SAE)) until [2a] is accepted.
 (7) ESCAPE(E0) — [3]'s duty; cited only inside (vi)'s conditional
   solve sentence, never claimed.
EVIDENCE, NOT PROOF (the probe roster; exploration-class, no seals):
 - the VALUE probe (verification/value_probe.py + results): all 15
   probed linked totals interpolated UNIVERSAL with surplus ≥ 15;
   twisted-cell fiber constancy EXACT at all 24 census q while
   fixed-frame cells are provably char-dependent — the anchor-alignment
   clause is probe-forced and now part of VAL.1's statement;
 - JOINT-probe (runs with this draft): one species with k = 2 linked
   children sharing a parent + one sibling-collision condition, exact
   F_q joint census over the 24-q list — row constancy on JREF^src
   cells vs on products of marginal cells; a marginal-constant/
   joint-varying finding refutes any state type lacking relational
   strata;
 - COMPOSE-probe (same run): one two-step family, step-1 target cell
   consumed as step-2 source — exact census of two-step linked counts
   vs the matrix product of sealed one-step tables, the count layer
   carrying its sealed entrance factor at ONE sealed ε (any
   I^ent = |β₀| identification displayed as sealed per-family, never a
   rule); an exact mismatch refutes the conjunction {(i)'s typing +
   VAL CHAIN's (XHD-u) count face} at k = 2 (rev 3 — CHAIN is
   (XHD-u)-conditional, so the probe tests that face too);
 - HMC-probe (V.4).
THE REDESIGN BRANCH (VAL.3 — unexercised): if some table entry or
template count is PROVEN non-polynomial (a census refutation per (†))
AND aggregate cancellation is PROVEN, the aggregate-block architecture
[3′] replaces [3] (plan §2v VAL.3 — 3+ units, own verification); a
proved NON-cancellation at some σ and wild p is the R1 wall. Probe
status keeps the trigger unexercised; the branch stays specified and
unbudgeted. The plan's VALUE-Fq (24-q sealed table layer) and VALUE-p
(n = 5 p-adic shadow) gates REMAIN STANDING obligations of the full
table build, distinct from and additional to V-n3 below.

### V.6 Sealed gate V-n3 (the obligation — table block both ways + one COMP-h instance)

**GATE STATUS: PASSED (2026-07-27) — 178 exact checks, 0 failures.** The
seal (`verification/CASE_VN3_SEALED_PREDICTIONS.md`, transcribed from
V.6.1–V.6.4 before any census code) and the census
(`case_vn3_gate.py`, results json committed): A1 — all 45 root-table
entries exact at the nine q, Σ = q³ per q, m_H3 = 0 at q = 2 exactly;
A2 — T = (q−1)² at all nine q, the p = 2 digit census 32 = 2¹²·2⁻⁷
exact; the s_blk2 rows identical at both representatives ((iv)-REP);
gate B — 16 marked pairs at N = 3 and 128 at N = 4, μ̂ = 2⁻⁵ exact,
count shadow 2, box-precision exact (zero event-word changes). Cited as
support, not closure: XHD/(XHD-u)/(ENT-U)/HMC remain open hypotheses
with their owners; VALUE-Fq/VALUE-p remain standing obligations.

Spec discipline: seal-before-census (Case-K), FREE CHOICES pinned
BELOW IN THE NOTE (rev 2, finding 14: nothing lives only in an external
seal — every predicted number is derivable from THIS section's
displays), predictions EXACT integers/dyadic rationals, attribution a
CONJUNCTION (TASM pass-1 finding 14: no scheme may claim to isolate a
clause its layers only jointly exercise). The seal file
verification/CASE_VN3_SEALED_PREDICTIONS.md TRANSCRIBES V.6.1–V.6.4 and
is written before the census script case_vn3_gate.py runs. Census
q-list: q ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13} (prime powers deliberately
included); every entry below has degree ≤ 3, so the nine-point census
carries per-entry surplus ≥ 5 per (†).

**V.6.1 Block A1 — the root skeleton s₀ (n = 3), computed.** The root
node: no history, fresh read = the reduction f̄ = z³ + āz² + b̄z + c̄
over F_q (three fresh digits; pool q³; W_loc(root) = 3; W_state(s₀)=0).
 (D1) Out(s₀) — five letters, the monic-cubic reduction geometries:
   m_H3 [three distinct linear factors] TERMINAL (3 Hensel tracks);
   m_H12 [linear × irreducible quadratic] TERMINAL ([1,1]+[1,2]);
   m_H⟨3⟩ [irreducible cubic] TERMINAL ([e=1,f=3]);
   m_2+1 [ψ²χ, ψ ≠ χ linear] CONTINUING — μ = 2 cluster into the
     size-2 block (+ sibling Hensel track, FAM's);
   m_3 [ψ³, deg ψ = 1] CONTINUING — μ = 3 cluster into the size-3 block.
 (D2) source generator lists (a)/(b): EMPTY — the root source is the
   empty history, so the meet is trivial; the letters' own strata are
   factorization-type predicates (char-free; no discriminant formula is
   used, so NO exceptional-char convention is needed at this block).
 (D3) meet list: JREF^src(s₀) = {α₀}, predicate ⊤, |α₀|(q) = 1
   (degree 0 ≤ W_state(s₀) = 0). One representative — the "two
   representatives" census clause is VACUOUS here (recorded).
 (D4) target maps: m_2+1 ↦ β₀ ∈ JREF^src(s_blk2) (V.6.3): the
   assignment f̄ = (z−α)²(z−β) lands at hinge value t := β̄ − ᾱ ∈ F_qˣ,
   always in β₀ = the ⊤-cell (t ≠ 0 by distinctness); m_3 ↦ β_3 :=
   the single ⊤-cell of the size-3 entry skeleton, |β_3| = 1 (recentering
   at the triple root retains no residual value).
 TABLE (one row; closed forms; each degree ≤ W_loc = 3):
   T_{m_H3}   = q(q−1)(q−2)/6      T_{m_H12}     = q²(q−1)/2
   T_{m_H⟨3⟩} = (q³−q)/3           T_{m_2+1}^{α₀,β₀} = q(q−1)
   T_{m_3}^{α₀,β_3} = q
 PART-1 count face, displayed: (q³−3q²+2q)/6 + (3q³−3q²)/6 + (2q³−2q)/6
   + (6q²−6q)/6 + 6q/6 = q³ = pool. ✓
 DEG-CONS (full roster): m_H3: 3 children (1,1,1), Σ = 3 ≤ 3 ✓;
   m_H12: (1,2) ✓; m_2+1: (2,1) ✓; m_H⟨3⟩, m_3: single-child (m = 1,
   no branching check applies). ✓
 PREDICTED EVALUATIONS at the nine census q (rows in the (D1) order;
 final row = the PART-1 sum q³):
   q:        2    3    4    5     7     8     9    11    13
   m_H3:     0    1    4   10    35    56    84   165   286
   m_H12:    2    9   24   50   147   224   324   605  1014
   m_H⟨3⟩:   2    8   20   40   112   168   240   440   728
   m_2+1:    2    6   12   20    42    56    72   110   156
   m_3:      2    3    4    5     7     8     9    11    13
   Σ = q³:   8   27   64  125   343   512   729  1331  2197
**V.6.2 Block A2 — the wild-heavy side skeleton s₁, computed (the SP.1
data formerly "pinned in the seal", now DISPLAYED).** After the root
letter m_3 (f̄ = z³, recentered: f = z³ + az² + bz + c with v(a), v(b),
v(c) ≥ 1), the size-3 window is the NP over (0, v(c)), (1, v(b)),
(2, v(a)), (3, 0). s₁ := the branch state riding the SIDE from (0, h₀)
to (2, h₂) of STRIDE e = 2: slope (h₀−h₂)/2 with h₀ − h₂ ODD
(fractional; WILD at p = 2 since p │ e); the third root rides the
sibling side (2, h₂)–(3, 0) (a separate branch, FAM's). Anchor exponent
a_eff = 0 (untwisted vertex values at this node); tower phase: depth 1,
first window.
 HEIGHT DOMAIN (displayed ILLUSTRATION of XHD-d's format — the gate
 FIXES its heights and consumes no domain hypothesis): realizability =
 {h₂ ≥ 1 (vertex), h₀ > 3h₂ (hull strictness), h₀ − h₂ odd}; with
 h₂ = t ≥ 1, h₀ = 3t + 2u + 1 (u ≥ 0) this is the ONE linear set
 L((4,1); {(3,1), (2,0)}) in coordinates (h₀, h₂) — base and periods
 explicitly listed; a ONE-component decomposition, so the rev-3
 disjointness convention holds vacuously.
 FRESH VALUES at fixed (h₀, h₂): u₀ := the level-h₀ digit of c ∈ F_qˣ,
 u₂ := the level-h₂ digit of a ∈ F_qˣ (side support = endpoints only:
 the interior point (1, (h₀+h₂)/2) is half-integral — no lattice digit);
 v(b) ≥ (h₀+h₂+1)/2 is pure STRIP. Pool (F_qˣ)²; W_loc(m_w) = 2.
 (D1) Out(s₁) = {m_w} — ONE letter: residual R(y) = u₂y + u₀ (degree
   length/e = 1), root y₀ = −u₀/u₂ ∈ F_qˣ, ALWAYS multiplicity 1 —
   the branch's factor is certified irreducible, absorbing verdict
   label [e = 2, f = 1] (label only; VP semantics [3t]'s; μ = 1
   certification is wildness-independent — A2's wild-heavy content is
   the parity class, the p = 2 census point, and the (D2) convention).
 (D2) source generators: EMPTY (see D3). Outcome hinge-value cell: the
   untwisted (a_eff = 0) VAL.1 cell of y₀ — one cell F_qˣ with fiber
   count c_V ≡ q − 1 (for fixed y₀, #{(u₀,u₂) : −u₀/u₂ = y₀} = q−1; a
   worked two-variable VAL.1 instance, char-free). Exceptional-char
   convention: at char 2 the sign in y₀ = −u₀/u₂ collapses (−1 = 1);
   no cell and no count changes — displayed as the convention.
 (D3) meet list: JREF^src(s₁) = {α₁}, predicate ⊤, |α₁|(q) = 1
   (recentering retains no residual value), W_state(s₁) = 0.
 (D4) no continuing letter — vacuous. DEG-CONS: vacuous over Out(s₁)
   (no m ≥ 2 outcome); the window-level sibling split upstream has
   children 2 + 1, Σ = 3 ≤ 3 ✓ (M1's degree identity), recorded at the
   entrance layer.
 TABLE: T_{m_w, [y₀-cell]}^{α₁, [e=2,f=1]} = (q−1)², degree 2 ≤ 2 ✓;
   PART-1: (q−1)² = pool ✓ (one letter).
 WEIGHT (the (U-A) face, displayed derivation — used at the census
 heights): new digit pins beyond the entry cylinder {v(a),v(b),v(c)≥1}:
 c: (h₀−1) strip zeros + 1 value pin; a: (h₂−1) + 1; b: (h₀+h₂−1)/2
 strip zeros; so g(h₀,h₂) = q^{−E}, E = (3(h₀+h₂)−1)/2 — affine,
 positive weights. Sealed census height point: the base (h₀,h₂) =
 (4, 1): E = 7, per-assignment conditional mass q^{−7}.
 PREDICTED EVALUATIONS, T = (q−1)²:
   q:      2    3    4    5     7     8     9    11    13
   T:      1    4    9   16    36    49    64   100   144

**V.6.3 Block B-step — the size-2 block skeleton s_blk2, computed
(displayed IN the note because gate B consumes its table).** s_blk2 :=
the m_2+1 target: in the branch frame f = u·h with h = z² + h₁z + h₀
the distinguished quadratic (v(h₀), v(h₁) ≥ 1) and u the unit cotrack;
concrete states = the hinge value t ∈ F_qˣ; window = NP over
(0, v(h₀)), (1, v(h₁)), (2, 0).
 (D1) Out(s_blk2) — three letters:
   m₂ [one side (0, 2λ)→(2, 0), λ ∈ ℤ≥1, stride 1, residual degree 2]:
     fresh (u, w) ∈ F_qˣ × F_q (u := level-2λ digit of h₀; w := level-λ
     digit of h₁ — w = 0 encodes v(h₁) > λ); R(y) = y² + wy + u;
     outcomes: o_split (two distinct roots in F_qˣ — 2 terminal
     tracks), o_inert (irreducible — terminal [e=1,f=2]), o_double
     (double root y* ∈ F_qˣ — CONTINUING, μ = 2 refined cluster → β₁);
   m_w2 [one side, slope k₀/2, k₀ odd, stride 2]: fresh u ∈ F_qˣ,
     residual degree 1 — terminal certified [e=2,f=1] (the V.6.2
     pattern one level down);
   m_vv [two sides, vertex (1, k₁), 2k₁ < k₀]: fresh (u₀,u₁) ∈ (F_qˣ)²
     — two degree-1 sides, 2 terminal tracks at distinct heights.
 (D2) source generators: EMPTY — none of the three letters' displayed
   evaluation maps reads t (residual coefficients are h's OWN digits;
   the lead at (2,0) is monic — no hinge/anchor twist, a_eff = 0);
   this is the executed per-species (iv)-REP observable check for this
   block. Outcome strata (they live in o, not in the source): for m₂,
   odd q: the square class of disc := w² − 4u (split ⟺ nonzero
   square, inert ⟺ nonsquare, double ⟺ 0); char 2: the
   Artin–Schreier convention — double ⟺ w = 0; for w ≠ 0, split ⟺
   Tr_{F_q/F_2}(u/w²) = 0, inert ⟺ Tr = 1. DISPLAYED
   exceptional-char convention; the closed forms below are the SAME
   polynomials under both.
 (D3) meet list: JREF^src(s_blk2) = {β₀}, predicate ⊤ on the state
   space F_qˣ (t ≠ 0), |β₀|(q) = q − 1, degree 1 ≤ W_state = 1.
   Representatives censused: t = 1, and t = 2 at q ≥ 3 ((iv)-REP's
   count face; at q = 2 the cell has one state — recorded).
 (D4) m₂/o_double ↦ β₁ := the ⊤-cell of the refined-cluster skeleton
   (recentered at y*; no retained residual value; |β₁| = 1); all other
   letters absorbing.
 TABLE for m₂ (pool q(q−1) per representative; degrees ≤ W_loc(m₂)=2):
   T_{o_split} = (q−1)(q−2)/2   [pairs {r,s} ⊆ F_qˣ, r ≠ s; char-2
     recount (q−1)(q/2 − 1) — equal];
   T_{o_inert} = q(q−1)/2   [all monic irreducible quadratics — the
     constant is automatically nonzero; char-2 recount (q−1)·q/2];
   T_{o_double}^{β₀,β₁} = q − 1   [(y−r)², r ∈ F_qˣ; char 2: w = 0,
     u ∈ F_qˣ — equal].
   PART-1 count face: (q−1)(q−2)/2 + q(q−1)/2 + (q−1) = q(q−1) ✓.
   Other letters: T_{m_w2} = q − 1; T_{m_vv} = (q−1)².
 DEG-CONS (full roster): m₂/o_split children (1,1), Σ = 2 ≤ 2 ✓;
   m_vv (1,1) ✓; o_double single child size 2, m_w2 single child —
   no branching check. ✓
 PREDICTED EVALUATIONS:
   q:          2    3    4    5     7     8     9    11    13
   o_split:    0    1    3    6    15    21    28    45    66
   o_inert:    1    3    6   10    21    28    36    55    78
   o_double:   1    2    3    4     6     7     8    10    12
   Σ = q(q−1): 2    6   12   20    42    56    72   110   156
   m_w2:       1    2    3    4     6     7     8    10    12
   m_vv:       1    4    9   16    36    49    64   100   144
**V.6.4 Gate B — ONE COMP-h instance vs a §D4-R fiber mass, p = 2, all
heights fixed, every number displayed (consumes only (U-A)'s
§C-derivable face at TWO fixed entrance histories, EACH checked
separately, the common inventory displayed below — rev 3, pass-2
finding 6: the gate is an aggregate over two histories, never a
one-history exercise — V.0/V.4).**
 ENTRANCE: ε := (P̂ = the root m_2+1 prefix, b = the μ = 2 branch,
   σ_sel = its (side, ψ)-selection at the root cell) — V.1(iii)'s
   refined label; landing cell β₀ (V.6.3). The root read carries d = 0
   height slots, so ε RETAINS no height data: h_ent(ε) = () and the
   template ε̊ = ε with H(ε̊) = {()} (rev 4's unified typing — the root
   read is HEIGHT-FREE, so the projection h_ent(ε) is the empty tuple
   and the instantiation is trivial; supersedes rev 1's "minimal
   realizable root-side height"); ledger exponent A(ε) = 3 (three
   reduction digit pins), W_ent(ε) = 3.
 ENTRANCE COUNT/MASS: I^ent_{ε,β₀}(q) = T_{m_2+1} = q(q−1)
   (every ψ²χ entrance lands in β₀ — V.6.1 (D4)), degree 2 ≤ 3 ✓;
   note I^ent = q·|β₀| ≠ |β₀| — the displayed instance of
   "I^ent = |β₀| is NOT general". ι_{2,ε,β₀}(q) = q(q−1)·q^{−3}
   (each entrance mark carries the D4R.1-SUM summand q^{−3});
   AT p = 2: I^ent(2) = 2 (the two marked histories: f̄ = z²(z+1) and
   f̄ = (z+1)²z), ι = 2·2^{−3} = 1/4.
 TWO-HISTORY DISCIPLINE (rev 3 — the finding-6 repair): (U-A) is
   applied PER HISTORY, separately to each of the two marked entrance
   histories. Both land at the SAME β₀ state (t = β̄ − ᾱ = 1 for
   z²(z+1); t = −1 = 1 at p = 2 for (z+1)²z), and in EACH history's
   branch frame (recentered at that history's double root) the step
   read carries the SAME nominal digit inventory: the window NP over
   (0, v(h₀)), (1, v(h₁)), (2, 0), fresh (u, w), pins E = 3λ — a
   function of the window shape ALONE (C.1(ii)), which the recentering
   shift never enters. Hence T = 1 and g = 2^{−3} for each history BY
   DISPLAY, and the aggregate 2·2^{−3}·(step factor) exercises no
   (XHD-u) content — the commonality is DERIVED, not assumed.
 STEP: γ¹ = (β₀ →^{m₂, o_double} β₁) at sealed λ = 1, i.e. height
   point h₁ = (k₀ = 2). From V.6.3: T_{o_double}(2) = q−1│_{q=2} = 1 —
   the unique cell (u, w) = (1, 0): R = y² + 1 = (y+1)², y* = 1.
   WEIGHT: new pins beyond {v(h₀) ≥ 1, v(h₁) ≥ 1}: h₀ — one strip zero
   (level 1) + the level-2 value pin; h₁ — the level-1 digit w = 0:
   E(h₁) = 3λ = 3, g = 2^{−3} = 1/8 (general E = 3λ — affine ✓).
 SEALED EXACT PREDICTIONS:
   μ̂(marked event) = ι·T·g = (1/4)·1·(1/8) = 2^{−5} = 1/32 (the
     dyadic mass); count shadow = I^ent(2)·T(2) = 2·1 = 2.
 THRESHOLD N := 3, with the derivation displayed: the entrance datum is
   f mod 2; f̄ has the double and simple roots reduction-separated, so
   the coprime (Hensel) factorization f = u·h lifts uniquely with
   h mod 2^k determined by f mod 2^k for EVERY k; the step data are
   v(h₀) = 2 with unit digit (h₀ ≡ 4 mod 8 — level 3) and v(h₁) ≥ 2
   (h₁ ≡ 0 mod 4 — level 2). So level 3 determines every event datum.
 PREDICTED CENSUS COUNTS: marked pairs among the 2^{3N} residues =
   μ̂·2^{3N} = 2^{3N−5}: N = 3: 16; N = 4: 128 (= 16·2³ EXACTLY, zero
   event-word changes — BOX-PRECISION, the SIB-gate B22 pattern);
   marked-history count = 2 at both levels.

**V.6.5 Census duties (definitional side; scripts written AFTER the
seal transcribes V.6.1–V.6.4).**
 (A-side, blocks V.6.1–V.6.3) exhaustive enumeration over F_q at the
   nine census q of all fresh assignments, from ≥ 2 representatives per
   active cell WHERE the cell has ≥ 2 states (β₀ at q ≥ 3; vacuities
   recorded above). CHECKED EXACTLY, zero tolerance: every entry value
   against its closed form (per-entry surplus ≥ 5 per (†)); the
   PART-1 count identity per representative; identical rows from
   distinct representatives ((iv)-REP's count face); every landing
   inside the displayed (D4) target cell ((i)); the m_H3 zero at q = 2
   (a genuine falsifier: the census must find EXACTLY 0). NO displayed
   cell size vanishes at any census q (sizes 1, q−1, 1) — (ii-a)'s
   empty-cell check is VACUOUS at these blocks, recorded honestly (the
   wild-p ACTIVE-VALUE layer remains RESUM-n3's, V.5(5)).
 (B-side, V.6.4) exhaustive enumeration of f mod 2^N (box 2^{3N},
   N = 3 then N = 4; feasible through N = 7), counting MARKED pairs —
   per mark, an f realizing the event on two branches counted twice,
   exactly as μ̂ demands. PASS = marked count 16 (N = 3) and 128
   (N = 4), and marked-history count 2, ALL EXACT.

 ATTRIBUTION (sealed with the predictions — finding-14 discipline).
   Layers A and B JOINTLY test the conjunction {the computed partition
   (D1)–(D4) + the closed-form tables ((iv)-POLY, T-half) + target
   typing ((i)) + the partition/representative count faces ((iv)-PART/
   REP count faces) + the COMP-h typing at fixed heights and TWO fixed
   entrance histories checked separately ((vi), (U-A)'s §C-derivable
   face PER HISTORY, the common inventory displayed at V.6.4 — no
   (XHD-u) content is exercised; per-h counts censused directly)
   + the upstream §C/§D4-R laws they consume}. A surviving
   mismatch INDICTS THE CONJUNCTION — no layer isolates one clause.
   Adjudication order (sealed): (1) prediction-derivation error
   (Case-K); (2) re-run the upstream face on the same box (D4R.4-SUM
   count for B; raw pool totals for A) — if upstream reconfirms, the
   failure localizes to THIS note's layer but NOT to a single clause;
   (3) a theory error triggers plan §8 R1's isolation experiment BEFORE
   any further RESUM work, and the (†) protocol decides any
   non-polynomiality claim (one exact mismatch, surviving (1)–(2),
   refutes universality of that entry conclusively).
 GOVERNANCE. [1v]-COND may NOT be accepted before V-n3 passes; V-n3
   joins the plan §7 roster beside the standing VALUE-Fq/VALUE-p
   obligations (V.5). This note's acceptance record must name: the XHD
   tag ([1v]-FULL pending [2b]), HMC's open status + probe result,
   ENT-COUNT/INIT-RAT status, computed-list coverage (which skeletons),
   both gate results, the [2a] pending-acceptance inheritance, and the
   probe roster as evidence-only — per the acceptance-record rule.

CONSOLIDATED ACCEPTANCE-RECORD PERIMETER (rev 7, per V.6.5's rule —
what any acceptance record of this note must name): the XHD package
(XHD-w/-d/-s, owner [2b]) + (XHD-u) (representative-uniformity +
height-rectangularity, owner [2b]) + (ENT-U) (owner [2b], M4b) as OPEN
hypotheses — the XHD tag ([1v]-FULL pending [2b]); (U-A) PROVED here; HMC an OPEN kernel (its probe is
specced-and-pinned at V.4 but has NOT run — no result is claimed;
evidence-only when it does); ENT-COUNT + INIT-RAT as this note's named
burdens (INIT-RAT rederived GIVEN XHD + (ENT-U)); the computed-list
coverage duty (CTS-M(i)/CL-13: the V.6 skeletons cover THREE cells'
lists (s₀/α₀, s₁/α₁, s_blk2/β₀), not the full n = 3 partition — the full
(D1)–(D4) table build for every consumed skeleton is THIS note's
[1v]-COND/CL-13 burden (PENDING), resting on [2a]'s SP-FIN/SP-OUT (the
PENDING syntactic-menu inheritance underlying clause (i))); the V-n3 gate PASSED with BOTH
components (the definitional table census A-side and the COMP-h gate B)
— support, never closure; VALUE-Fq/VALUE-p standing; the probe roster
evidence-only. Nothing in this note claims per-f content ([3t]'s fence).

*(End of §V-TABLES, rev 7 — 2026-07-27: the pass-2 repairs (disjoint

==================================================================
THE MovesS Defs/Interfaces SIGNATURES (ground-truth consumed interface;
this corpus MUST supply exactly these fields per §4 SEAM-SUPPLY):
==================================================================

--- lean/LeanUrat/MovesS/Defs.lean (full) ---
/-
MovesS/Defs — shared vocabulary for MOVES §S-RESUM (the depth resummation core).

E-phase transcription of `lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (REV 13,
core accepted by adjudicated closure) §2.A–§2.C + the §2.D Defs-part (MuHat/ReadOwner/
Shape/ShapeFam/consumedDeltas/RegP).  Declaration order = spec.  The skeleton defs the
blueprint displays with `sorry` bodies (OKat/evalAt, kTarget, Kmat, bTerm,
consumedDeltas) are FILLED here per the E-phase discipline (Defs sorry-free); their
LAW units (U-19, U-16a3, …) stay sorried in their own files.  Nothing in this file
asserts mathematics — it fixes the vocabulary §S-RESUM's statements are typed in.
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix Polynomial

/-- D1: the symbolic carrier ℚ(q). -/
abbrev Qq := RatFunc ℚ

variable {n : ℕ}

/-! ## §2.A Combinatorial layer (owner MovesV/MovesSp rosters) -/

/-- A branch member.  `δ` is the base-change FACTOR contributed at this nesting step;
the SEMANTIC index rel. the base prime is the product along the chain (CONVENTION
DELTA-ABS, R17; [2r] (e2)); no δ = 0. -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+
  status : V ⊕ State size

def Member.continuing {V : Type*} {State : ℕ → Type*} (μ : Member V State) : Prop :=
  μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

section OutcomeDefs
variable {V : Type*} {State : ℕ → Type*}

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ :=
  (o.mem.filter (fun μ => μ.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  ((o.mem.filterMap fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split
  deriving DecidableEq

/-- The (m, c) dispatch: exhaustive and exclusive by construction. -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

end OutcomeDefs

/-- Block states + rosters.  NO SigSet (R9): σ′ ranges over all of `Multiset VType`;
finite σ′-sums use `verdictImage` below.  `vEquiv` is the R20 STRUCTURAL PIN: verdict
types ARE the (e, f) pairs of degree e·f ≤ n; `vdeg_spec` reads degree through it.
`Wloc`/`Wstate` are the note's degree-bound data, FIXED here before any burden (R27). -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  finV   : Fintype VType
  vdeg   : VType → ℕ+
  vEquiv : VType ≃ {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ n}
  vdeg_spec : ∀ v, (vdeg v : ℕ) = ((vEquiv v).1.1 : ℕ) * ((vEquiv v).1.2 : ℕ)
  Out    : ∀ e, State e → Type
  finO   : ∀ e (τ : State e), Fintype (Out e τ)
  odata  : ∀ e (τ : State e), Out e τ → Outcome VType State
  Wloc   : ∀ e (τ : State e), Out e τ → ℕ
  Wstate : ∀ e, State e → ℕ

attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finV
  TableShape.finO

open scoped Classical

/-- The finitely many verdict multisets the (e, τ) roster's terminal outcomes emit —
the index Finset of (K-SUB)'s Σ_{σ′} b^{term,fin} (replaces REV 2's SigSet). -/
noncomputable def verdictImage (T : TableShape n) (e : ℕ) (τ : T.State e) :
    Finset (Multiset T.VType) :=
  Finset.image (fun o => (T.odata e τ o).verdicts)
    {o : T.Out e τ | routeOf (T.odata e τ o) = .termFin}.toFinset

/-- (SCS) supply — owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via SP.2.  Data first
(R2-3); `∨ True` artifact deleted (R2-1); `flank_zero` added (R2-2); `resFactors`
a Multiset with position-indexed `memberOf` (REV 10, Codex#6-10). -/
structure SCSData (T : TableShape n) where
  W  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  ℓ  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  g  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  μsel : ∀ e (τ : T.State e), T.Out e τ → ℕ
  W' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankCount : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankWidth : ∀ e (τ : T.State e), T.Out e τ → ℕ
  resFactors : ∀ e (τ : T.State e), T.Out e τ → Multiset (ℕ × ℕ)
  selIdx : ∀ e (τ : T.State e) (o : T.Out e τ), Fin (T.odata e τ o).mem.length
  memberOf : ∀ e (τ : T.State e) (o : T.Out e τ),
    (Fin (flankCount e τ o) ⊕
      Fin ((resFactors e τ o).erase (g e τ o, μsel e τ o)).card) →
    Fin (T.odata e τ o).mem.length
  -- laws
  ℓpos : ∀ e (τ : T.State e) (o : T.Out e τ), 1 ≤ ℓ e τ o
  window_comp : ∀ e (τ : T.State e) (o : T.Out e τ),
    W e τ o = e * ℓ e τ o + flankWidth e τ o
  flank_zero : ∀ e (τ : T.State e) (o : T.Out e τ),
    flankCount e τ o = 0 → flankWidth e τ o = 0
  sel_mem : ∀ e (τ : T.State e) (o : T.Out e τ),
    (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e (τ : T.State e) (o : T.Out e τ),
    ((resFactors e τ o).map (fun x => x.1 * x.2)).sum = ℓ e τ o
  memberOf_inj : ∀ e (τ : T.State e) (o : T.Out e τ),
    Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e (τ : T.State e) (o : T.Out e τ) i,
    memberOf e τ o i ≠ selIdx e τ o
  sel_continuing : ∀ e (τ : T.State e) (o : T.Out e τ),
    routeOf (T.odata e τ o) = .kcol →
    ((T.odata e τ o).mem.get (selIdx e τ o)).continuing
  stage_D : ∀ e (τ : T.State e) (o : T.Out e τ), D' e τ o = e * g e τ o * D e τ o
  stage_W : ∀ e (τ : T.State e) (o : T.Out e τ), W' e τ o = μsel e τ o
  cluster_parent : ∀ e (τ : T.State e) (o : T.Out e τ), W e τ o * D e τ o = e
  cluster_child : ∀ e (τ : T.State e) (o : T.Out e τ)
    (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o

/-- DEG-CONS (CL-11, [1v]): full-roster per-member degree law. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e (τ : T.State e) (o : T.Out e τ),
    ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-! ## §2.B The measured side (R7 event carrier).  Owner [1v] CTS-M / [2b] XHD / [5].
Intended instance: the CTS cell space over the level-N residue boxes of the O_δ
theory (the MovesC counting idiom), wave 4. -/

structure MeasuredSide (T : TableShape n) where
  -- pools: prime powers, closed under the base-change legs (R2-7, R2-14)
  Pools : Set ℚ
  pools_prime_pow : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p : ℚ) ^ (δ : ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ Pools
  pools_infinite : Pools.Infinite
  -- the counting carrier (R7): level-N boxes, events as Finsets
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  -- cells, representatives, heights
  Cell : ∀ e, T.State e → Type
  finC : ∀ e (τ : T.State e), Fintype (Cell e τ)
  cellOut : ∀ e (τ : T.State e), Cell e τ → T.Out e τ
  Rep : ∀ e, T.State e → Type
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e, Nonempty (Rep e τ)
  cellLvl : ∀ e (τ : T.State e), Cell e τ → ℕ
  cellInst : ∀ e (τ : T.State e), Cell e τ → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  Hgt : Type
  HDom : ∀ e (τ : T.State e), Cell e τ → Set Hgt
  gwt : ∀ e (τ : T.State e) (c : Cell e τ), Hgt → ℚ → ℝ
  cellEvt : ∀ e (τ : T.State e), Rep e τ → Cell e τ → Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  μcell : ∀ e (τ : T.State e), Rep e τ → Cell e τ → ℚ → ℝ
  rowVal : ∀ e (τ : T.State e), T.Out e τ → ℚ → ℝ
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ
  activeState : ℚ → ∀ e, T.State e → Prop
  decA : ∀ q₀ e, DecidablePred (activeState q₀ e)
  -- entrance side
  EntShape : ∀ e, T.State e → Type
  finE : ∀ e (τ : T.State e), Fintype (EntShape e τ)
  hent : ∀ e (τ : T.State e), EntShape e τ → ℕ
  Went : ∀ e (τ : T.State e), EntShape e τ → ℕ
  entEvtH : ∀ e (τ : T.State e), EntShape e τ → Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  ιDom : ∀ e (τ : T.State e), EntShape e τ → Set Hgt
  ιshH : ∀ e (τ : T.State e), EntShape e τ → Hgt → ℚ → ℝ
  ιsh : ∀ e (τ : T.State e), EntShape e τ → ℚ → ℝ
  ιval : ∀ e, T.State e → ℚ → ℝ
  entCount : ∀ e (τ : T.State e), EntShape e τ → ℚ → ℕ
  entLvl : ∀ e (τ : T.State e), EntShape e τ → ℕ
  entInst : ∀ e (τ : T.State e), EntShape e τ → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  markedVal : ∀ _e : ℕ, ℚ → ℝ

attribute [instance] MeasuredSide.finB MeasuredSide.finC MeasuredSide.finE
  MeasuredSide.decA

variable {T : TableShape n}

/-- The DEFINED all-active locus (R2-7/R9): only its infinitude is a burden (U-22b). -/
def allActivePools (M : MeasuredSide T) : Set ℚ :=
  {q₀ ∈ M.Pools | ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e, M.activeState q₀ e τ}

/-- `cells o` — the outcome's cell fiber (the blueprint's LedgerIV notation). -/
noncomputable def MeasuredSide.cells (M : MeasuredSide T) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Finset (M.Cell e τ) :=
  {c | M.cellOut e τ c = o}.toFinset

/-- CL-5, all nine inputs as contentful Props (R2-4/5/6).  ACTIVITY GUARDS THROUGHOUT
(R13): every per-(e,τ,q₀) mass claim carries `M.activeState q₀ e τ` — the note's
"realized states only" scope; NO zero-row law for inactive sources exists (act_row
DELETED — undisplayed).  The ONLY height summations in the corpus are `xhd_sum` and
`comp_once` — (COMP-Σ)'s "no further height sum" is structural. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  -- (1) XHD [2b], guarded; two-sided exactness representative-quantified (R2-4):
  xhd_sum : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
  xhd_no_stray : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    ∃ N₀, ∀ N ≥ N₀, (M.cellEvt e τ x c h q₀ N).Nonempty
  xhd_no_orphan : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∉ M.HDom e τ c → ∀ (q₀ : ℚ) (N : ℕ), M.cellEvt e τ x c h q₀ N = ∅
  -- (2) D4R.0 (event disjointness needs no realization; unguarded is harmless):
  d4r0 : ∀ e (τ : T.State e) (x : M.Rep e τ) (q₀ : ℚ) (N : ℕ)
    (c c' : M.Cell e τ) (h h' : M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (M.cellEvt e τ x c h q₀ N) (M.cellEvt e τ x c' h' q₀ N)
  -- (3) (iv)-PART-1 [1v], GUARDED:
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (x : M.Rep e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
  -- (4) (iv)-REP = RS.0(α) verbatim (weighted grouping), GUARDED:
  rep_indep : ∀ e (τ : T.State e) (o : T.Out e τ) (x : M.Rep e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.rowVal e τ o q₀ = ∑ c ∈ M.cells e τ o, M.μcell e τ x c q₀
  -- (5) (iv)-MEAS counting-native (R7), GUARDED:
  meas_card : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.gwt e τ c h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.cellEvt e τ x c h q₀ N).card : ℝ)
  -- (6) CTS-M(v) HMC (OPEN) + the base tie, target predicate PINNED hK-FREE (G1):
  kstep_one : ∀ e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o : T.Out e τ | routeOf (T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, M.rowVal e τ o q₀
  hmc : ∀ (k : ℕ) e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep (k + 1) e τ β q₀ = ∑ γ : T.State e, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
  -- (7) CTS-M(ii) ACT — ONLY the displayed law (S.7(iv)):
  act_target : ∀ e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools →
    ¬ M.activeState q₀ e β → M.kstep 1 e τ β q₀ = 0
  -- (8) CTS-M(iii) INIT + ENT-COUNT, guarded; the I^ent tie at ε's OWN level (G4):
  init_agg : ∀ e (τ : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.ιval e τ q₀ = ∑ ε : M.EntShape e τ, M.ιsh e τ ε q₀
  init_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (h : M.Hgt),
    h ∈ M.ιDom e τ ε → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.ιshH e τ ε h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.entEvtH e τ ε h q₀ N).card : ℝ)
  ent_count_card : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    (M.entInst e τ ε q₀ (M.entLvl e τ ε)).card = M.entCount e τ ε q₀
  -- (9) COMP-TYPING, heights once: (COMP-h) = init_count's fixed-height objects;
  -- (COMP-hΣ) = THE one height sum; (COMP-Σ)'s factorization is hmc's duty:
  comp_once : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)

/-! ## §2.C Evaluation, rationality burdens, kernel, pools -/

private theorem eval_ne_zero_of_dvd {p q : Polynomial ℚ} {x : ℚ} (hdvd : p ∣ q)
    (hq : q.eval x ≠ 0) : p.eval x ≠ 0 := by
  intro h0
  obtain ⟨c, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, h0, zero_mul] at hq
  exact hq rfl

/-- The evaluation-regular subring at q₀: {f | f.denom.eval q₀ ≠ 0} (U-19's object;
OKat membership is post-cancellation — RatFunc num/denom are reduced). -/
def OKat (q₀ : ℚ) : Subring Qq where
  carrier := {f : Qq | f.denom.eval q₀ ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := @fun a b ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact eval_ne_zero_of_dvd (RatFunc.denom_add_dvd a b)
      (by rw [Polynomial.eval_mul]; exact mul_ne_zero ha hb)
  mul_mem' := @fun a b ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd a b)
      (by rw [Polynomial.eval_mul]; exact mul_ne_zero ha hb)
  neg_mem' := @fun a ha => by
    simp only [Set.mem_setOf_eq] at *
    have hdvd : (-a).denom ∣ (-1 : Qq).denom * a.denom := by
      simpa [neg_one_mul] using RatFunc.denom_mul_dvd (-1 : Qq) a
    have h1 : (-1 : Qq).denom = 1 := by
      rw [show (-1 : Qq) = algebraMap (Polynomial ℚ) Qq (-1) by simp]
      exact RatFunc.denom_algebraMap _
    exact eval_ne_zero_of_dvd hdvd (by rw [h1, one_mul]; exact ha)

theorem mem_OKat_iff {q₀ : ℚ} {f : Qq} : f ∈ OKat q₀ ↔ f.denom.eval q₀ ≠ 0 :=
  Iff.rfl

private theorem eval₂_denom_ne_zero_of_mem {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀) :
    Polynomial.eval₂ (RingHom.id ℚ) q₀ f.denom ≠ 0 := by
  rw [Polynomial.eval₂_id]; exact hf

/-- D4: partial evaluation on the regular subring (RatFunc.eval_add/eval_mul are
hypothesis-carrying; the memberships supply the hypotheses). -/
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ where
  toFun f := RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq)
  map_one' := by simp
  map_mul' a b := by
    push_cast
    exact RatFunc.eval_mul (RingHom.id ℚ) q₀
      (eval₂_denom_ne_zero_of_mem a.2) (eval₂_denom_ne_zero_of_mem b.2)
  map_zero' := by simp
  map_add' a b := by
    push_cast
    exact RatFunc.eval_add (RingHom.id ℚ) q₀
      (eval₂_denom_ne_zero_of_mem a.2) (eval₂_denom_ne_zero_of_mem b.2)

/-- The (iv)-POLY/XHD-s presentation pattern — R30/R31: TWO independently bounded
count polynomials × a height part in the note's OWN denominator class (q-powers
allowed — the §2.C.1 diagnosis: the note's class in q⁻¹, cleared to X = q, is
denom ∣ X^b · ∏ (1 − X^a)). -/
structure PolyGeom where
  countT : Polynomial ℚ
  degBoundT : ℕ
  degT_le : countT.natDegree ≤ degBoundT
  countS : Polynomial ℚ
  degBoundS : ℕ
  degS_le : countS.natDegree ≤ degBoundS
  geom : Qq
  qpow : ℕ
  geomDenoms : Finset ℕ+
  geom_denom_dvd : geom.denom ∣
    Polynomial.X ^ qpow * ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a : ℕ))

noncomputable def PolyGeom.val (P : PolyGeom) : Qq :=
  algebraMap (Polynomial ℚ) Qq (P.countT * P.countS) * P.geom

/-- The rationality burdens: ℚ(q) data in (iv)-POLY form + interpolation to the
measured rows.  Owners: CL-6 (iv)-POLY [1v] (tgP + tg_interp); (J-RAT) [1v]/[2b]
(jP + j_interp); INIT-RAT [1v] (ιP + ι_interp); + the cofinite-activity face
(cellP family, R45/R50 — per-cell, `act_iff` keyed to it). -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  tgP : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
  jP  : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
  ιP  : ∀ e (τ : T.State e), M.EntShape e τ → PolyGeom
  tg_ok : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (tgP e τ o).val ∈ OKat q₀
  j_ok  : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (jP e τ o).val ∈ OKat q₀
  ι_ok  : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (ιP e τ ε).val ∈ OKat q₀
  tg_interp : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    routeOf (T.odata e τ o) ≠ .split →
    ((evalAt q₀ ⟨(tgP e τ o).val, tg_ok e τ o q₀ h⟩ : ℚ) : ℝ) = M.rowVal e τ o q₀
  j_interp : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    routeOf (T.odata e τ o) = .split →
    ((evalAt q₀ ⟨(jP e τ o).val, j_ok e τ o q₀ h⟩ : ℚ) : ℝ) = M.rowVal e τ o q₀
  ι_interp : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(ιP e τ ε).val, ι_ok e τ ε q₀ h⟩ : ℚ) : ℝ) = M.ιsh e τ ε q₀
  ι_countS_one : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).countS = 1
  ι_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    ((ιP e τ ε).countT.eval q₀ : ℚ) = (M.entCount e τ ε q₀ : ℚ)
  tg_degT : ∀ e (τ : T.State e) (o : T.Out e τ), (tgP e τ o).degBoundT = T.Wloc e τ o
  tg_degS : ∀ e (τ : T.State e) (o : T.Out e τ), (tgP e τ o).degBoundS = T.Wstate e τ
  j_degT  : ∀ e (τ : T.State e) (o : T.Out e τ), (jP e τ o).degBoundT = T.Wloc e τ o
  j_degS  : ∀ e (τ : T.State e) (o : T.Out e τ), (jP e τ o).degBoundS = T.Wstate e τ
  ι_degT  : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).degBoundT = M.Went e τ ε
  ι_degS  : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).degBoundS = M.Went e τ ε
  cellP : ∀ e (τ : T.State e), M.Cell e τ → Polynomial ℚ
  cellP_deg : ∀ e (τ : T.State e) (c : M.Cell e τ), (cellP e τ c).natDegree ≤ T.Wstate e τ
  cellP_nonzero : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (c : M.Cell e τ), cellP e τ c ≠ 0
  cellP_count : ∀ e (τ : T.State e) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ((cellP e τ c).eval q₀ : ℚ) = ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)
  act_iff : ∀ q₀ ∈ M.Pools, ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e,
    M.activeState q₀ e τ ↔ ∀ c : M.Cell e τ, (cellP e τ c).eval q₀ ≠ 0

variable {M : MeasuredSide T}

noncomputable abbrev RatBurdens.TG (RB : RatBurdens T M) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Qq := (RB.tgP e τ o).val
noncomputable abbrev RatBurdens.J (RB : RatBurdens T M) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Qq := (RB.jP e τ o).val
noncomputable def RatBurdens.ι (RB : RatBurdens T M) (e : ℕ) : T.State e → Qq :=
  fun τ => ∑ ε : M.EntShape e τ, (RB.ιP e τ ε).val

noncomputable def splitOuts (T : TableShape n) (e : ℕ) (τ : T.State e) :
    Finset (T.Out e τ) :=
  {o : T.Out e τ | routeOf (T.odata e τ o) = .split}.toFinset

section KTarget
variable {V : Type*} {St : ℕ → Type*}

private theorem kcol_route_c_ne (o : Outcome V St) (hk : routeOf o = .kcol) :
    o.c ≠ 0 := by
  intro h
  unfold routeOf at hk
  rw [if_pos h] at hk
  exact Route.noConfusion hk

private theorem kcol_route_m_one (o : Outcome V St) (hk : routeOf o = .kcol) :
    o.m = 1 := by
  have hc := kcol_route_c_ne o hk
  unfold routeOf at hk
  rw [if_neg hc] at hk
  by_contra h
  rw [if_neg h] at hk
  exact Route.noConfusion hk

/-- In a kcol outcome (c ≥ 1, m = 1) the single member is continuing. -/
private theorem kcol_head_isRight (o : Outcome V St) (hk : routeOf o = .kcol) :
    (o.mem.head o.hm).status.isRight = true := by
  have hall : ∀ μ ∈ o.mem, μ.status.isRight = true := by
    have hsub : (o.mem.filter (fun μ => μ.status.isRight)).Sublist o.mem :=
      List.filter_sublist
    have hle : o.c ≤ o.m := hsub.length_le
    have hc := kcol_route_c_ne o hk
    have hm := kcol_route_m_one o hk
    have hlen : (o.mem.filter (fun μ => μ.status.isRight)).length = o.mem.length := by
      have h1 : o.c = (o.mem.filter (fun μ => μ.status.isRight)).length := rfl
      have h2 : o.m = o.mem.length := rfl
      omega
    have heq := hsub.eq_of_length hlen
    intro μ hμ
    have hμf : μ ∈ o.mem.filter (fun μ => μ.status.isRight) := by
      rw [heq]; exact hμ
    exact (List.mem_filter.mp hμf).2
  exact hall _ (List.head_mem o.hm)

private theorem isRight_cast {a b : ℕ} (h : a = b) (x : V ⊕ St a) :
    (h ▸ x : V ⊕ St b).isRight = x.isRight := by
  subst h; rfl

end KTarget

/-- The kcol outcome's target state (the single continuing member's state, cast to
block size e via the SCS-supplied `hK`). -/
noncomputable def kTarget (T : TableShape n) (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e :=
  Sum.getRight
    ((hK ((T.odata e τ o).mem.head (T.odata e τ o).hm)
        (List.head_mem (T.odata e τ o).hm)) ▸
      ((T.odata e τ o).mem.head (T.odata e τ o).hm).status : T.VType ⊕ T.State e)
    (by rw [isRight_cast]; exact kcol_head_isRight _ hk)

/-- The per-block hypothesis U-6 (`scs`) produces: every kcol member has size e. -/
abbrev KmatHyp (T : TableShape n) (e : ℕ) : Prop :=
  ∀ (τ : T.State e) (o : T.Out e τ), routeOf (T.odata e τ o) = .kcol →
    ∀ μ ∈ (T.odata e τ o).mem, μ.size = e

/-- K_e: the kernel-column matrix — Σ_{kcol o → β} RB.TG e τ o. -/
noncomputable def Kmat (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (e : ℕ) (hK : KmatHyp T e) : Matrix (T.State e) (T.State e) Qq :=
  fun τ β => ∑ o : T.Out e τ,
    if hk : routeOf (T.odata e τ o) = .kcol then
      (if kTarget T e τ o hk (hK τ o hk) = β then RB.TG e τ o else 0)
    else 0

/-- b_e^{term,fin}(σ′): Σ_{termFin o, verdicts o = σ'} RB.TG e τ o (any σ';
supported on `verdictImage`). -/
noncomputable def bTerm (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq :=
  fun τ => ∑ o : T.Out e τ,
    if routeOf (T.odata e τ o) = .termFin ∧ (T.odata e τ o).verdicts = σ'
    then RB.TG e τ o else 0

/-- ESCAPE(E0) at an evaluated kernel: nonneg entries + escaping total mass.
`[DecidableEq ι]`: Matrix `1`/`^` need it (Fable#4-F1 batch, R29). -/
structure EscapeE0 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) :
    Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ)))
    Filter.atTop (nhds 0)

/-- Per-pool package (S.4).  `Act` is DETERMINED by CTS-M(ii)'s classification
(R2-8: `act_spec` is an iff — an empty Act needs the note's own no-realized-state
situation, never a modeling choice). -/
structure PoolHyp (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (e : ℕ) (hK : KmatHyp T e) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  act_spec : ∀ τ, τ ∈ Act ↔ M.activeState q₀ e τ
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok τ.1 β.1 τ.2 β.2⟩
  inactive_vanish : ∀ τ β (hok : Kmat T RB e hK τ β ∈ OKat q₀), τ ∈ Act → β ∉ Act →
    evalAt q₀ ⟨Kmat T RB e hK τ β, hok⟩ = 0
  e0 : EscapeE0 A

/-- D11's ONE coercion point (R19): the active matrix over ℝ.  Det transported by
`RingHom.map_det` + `Rat.cast_injective` (the E-phase simp lemma `Aℝ_det_iff` lives
with U-24a1's plumbing). -/
noncomputable def Aℝ {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀) : Matrix P.Act P.Act ℝ :=
  P.A.map (algebraMap ℚ ℝ)

/-- CTS-M(ii-c)'s per-pool read-off gate, ℝ-typed via Aℝ (R19): "the evaluated
object's q₀-value (after cancellation — OKat membership is post-cancellation)
equals the active-subsystem solve there".  Junk-block determinants stay
census-side: recorded, never required nonzero. -/
def AVAgree {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀) (v : Qq) (bA : P.Act → ℝ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, ((evalAt q₀ ⟨v, hok⟩ : ℚ) : ℝ) = ((1 - Aℝ P)⁻¹ *ᵥ bA) τ

/-- The global determinant hypothesis every solve consumer carries (U-22's target). -/
abbrev DetHyp (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n), (1 - Kmat T RB e (hK e he)).det ≠ 0

/-! ## §2.D (BDY), shapes, RegP (the Defs-part; RS1Bundle/RS4Chain/ReadOffBundle
live in `MovesS/Interfaces.lean` per R25/R29 — the §W4-SYNC pins have NO E-phase
file). -/

/-- The μ̂ fence (no Add, no coercion). -/
structure MuHat where val : Qq

inductive ReadOwner | entrance | block
  deriving DecidableEq

def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance

/-- Length-matched shape record (REV 2); `δOf` per CONVENTION DELTA-ABS (R17). -/
structure Shape (T : TableShape n) where
  k    : ℕ
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)
  δOf  : Fin k → ℕ+
  σ0   : Multiset T.VType

/-- [2a] finiteness; CUT-3's image is the intended instance (W-7, seam). -/
structure ShapeFam (T : TableShape n) where
  Sh : Finset (Shape T)

/-- The δ-factor pool: split-leg δ's over the full roster ∪ the shape legs' δ's. -/
noncomputable def deltaFactors (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ :=
  ((Finset.Icc 1 n).biUnion fun e =>
    (Finset.univ : Finset (T.State e)).biUnion fun τ =>
      (Finset.univ : Finset (T.Out e τ)).biUnion fun o =>
        if routeOf (T.odata e τ o) = .split
        then ((T.odata e τ o).mem.map Member.δ).toFinset else ∅)
  ∪ F.Sh.biUnion fun Ŝ => Finset.image Ŝ.δOf Finset.univ

/-- MULTIPLICATIVE CLOSURE (R17, DELTA-ABS): all products of AT MOST n factors from
`deltaFactors`, incl. the empty product 1 (finite; (K-TRI) bounds nesting depth by n).
The closure lemma `nested_delta_mem` is U-16a3's spec obligation. -/
noncomputable def consumedDeltas (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ :=
  (fun s : Finset ℕ+ => s ∪ Finset.image₂ (· * ·) (deltaFactors T F) s)^[n] {1}

/-- CL-1's per-pool quantifier along one base prime: E0/ACT packages at δ = 1 AND
every consumed base-change leg pool p^δ. -/
def RegP (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M) (p : ℕ)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (F : ShapeFam T) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n), ∀ δ ∈ consumedDeltas T F,
    Nonempty (PoolHyp T M RB e (hK e he) ((p : ℚ) ^ (δ : ℕ)))

end LeanUrat.MovesS

--- lean/LeanUrat/MovesS/Interfaces.lean (full) ---
/-
MovesS/Interfaces — §2.D's hypothesis interfaces: RS1Meas, RS1Bundle, RS4Chain,
ReadOffBundle (R25/R29: THE one canonical location; elaborated AFTER the S2/S4
definition units so `evalRe`/`Rsh`/`markedPairing`/`bhatMeas` are in scope).
The §W4-SYNC seam entries (W-pins, TreeIface/FiberIface/ReadLedger, the packages)
are NOT built at E-phase — this file contains NOTHING from that section.
Blueprint: lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md (REV 13) §2.D.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef
import LeanUrat.MovesS.EvalReDef
import LeanUrat.MovesS.ConsumedDeltas
import LeanUrat.MovesS.BlockSolve
import LeanUrat.MovesS.BlockSolveTot
import LeanUrat.MovesS.RshDef
import LeanUrat.MovesS.MarkedDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

-- The abstract box carrier has no computable equality; `shevt_grouping`'s biUnion
-- takes the classical one (proof-irrelevant, last-resort priority).
attribute [local instance 0] Classical.decEq

variable {n : ℕ}

/-- The RAW measured family (R32): NO hypothesis fields — the carrier the W-2/W-3
pins are stated OVER, so the pins are obligations, not projections.  βmeas is the
h_ent-indexed measured conditional subtree value (owner [3t]). -/
structure RS1Meas (T : TableShape n) (M : MeasuredSide T) where
  βmeas : ∀ e, e ∈ Finset.Icc 1 n → ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
  β_bdd : ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βmeas e he h_ent τ σ' q₀ ∈ Set.Icc (0 : ℝ) 1
  βfull : ∀ e, e ∈ Finset.Icc 1 n → ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ

/-- RS.1's interface — NO symbolic β input (R8/R2-9): measured objects only.
Instantiating this at wave 4 requires PROVING the pinned W-2/W-3 for the raw
family from their displayed packages (R32) — the fields cannot be self-supplied.
`xrb` is (XRB) CL-9 OPEN, POINTWISE AT POOLS (R40); `recursion_meas` is
ACTIVITY-GUARDED (R16(i)) — junk-block rows at wild pools make NO demand
(det(I − D_{q₀}) = 0 stays a tolerated FINDING); discharge = the pinned W-3. -/
structure RS1Bundle (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    extends RS1Meas T M where
  xrb : ∀ e (he : e ∈ Finset.Icc 1 n) (h h' : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βmeas e he h τ σ' q₀ = βmeas e he h' τ σ' q₀
  recursion_meas : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∀ h_ent : ℕ, βmeas e he h_ent τ σ' q₀
      = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
  nsNull : Prop
  rexact : nsNull → ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀

/-- RS.4's chain — the FULL displayed inherited set as explicit components (R2-19),
σ-index = verdict multisets (R2-11).  `pools_e0` is RE-SCOPED to all-active BASE
pools (R51); `legs_reg` carries CL-1's full per-pool quantifier at EVERY base prime
(R21); `wsh_ok` is denominator regularity ONLY (R53) — CL-17(ii)'s production burden
is the seam pin W17ii (S-8), its inheritance the NAMED TYPED field `wsh17_pin`
(R57): wave 4 instantiates it with W17ii's statement; U-28 takes `h17 : C.wsh17_pin`
as an explicit premise; NO unconditional marking while it is open. -/
structure RS4Chain (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (F : ShapeFam T) where
  L : LedgerIV T M
  B : RS1Bundle T M RB hdc hK
  hns : B.nsNull
  PrimePools : Set ℚ
  prime_sub : PrimePools ⊆ M.Pools
  prime_base : ∀ q₀, q₀ ∈ PrimePools ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)
  pools_e0 : ∀ e (he : e ∈ Finset.Icc 1 n), ∀ q₀ ∈ PrimePools ∩ allActivePools M,
    Nonempty (PoolHyp T M RB e (hK e he) q₀)
  legs_reg : ∀ p : ℕ, (p : ℚ) ∈ PrimePools → RegP T M RB p hK F
  Sigmas : Finset (Multiset T.VType)
  sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n
  WshP : Shape T → PolyGeom
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, (WshP Ŝ).val ∈ OKat q₀
  wsh17_pin : Prop
  WshVal : Shape T → ℚ → ℝ
  wsh_interp : ∀ Ŝ (hŜ : Ŝ ∈ F.Sh), ∀ q₀ (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(WshP Ŝ).val, wsh_ok Ŝ hŜ q₀ h⟩ : ℚ) : ℝ) = WshVal Ŝ q₀
  wshval_bdd : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, WshVal Ŝ q₀ ∈ Set.Icc (0 : ℝ) 1
  -- TYPED SHALLOW CARRIERS (R34 — fields, not prose):
  shDom  : Shape T → Set M.Hgt
  shEvtH : Shape T → M.Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)
  visH   : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset M.Hgt
  shEvt  : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)
  shWeightH : Shape T → M.Hgt → ℚ → ℝ
  shevt_grouping : ∀ Ŝ (q₀ : ℚ) (N : ℕ),
    shEvt Ŝ q₀ N = (visH Ŝ q₀ N).biUnion (fun h => shEvtH Ŝ h q₀ N)
  shDom_ne : ∀ Ŝ ∈ F.Sh, (shDom Ŝ).Nonempty
  sh_realized : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ allActivePools M,
    ∃ N₀, ∀ N ≥ N₀, (shEvt Ŝ q₀ N).Nonempty
  shweight_card : ∀ Ŝ ∈ F.Sh, ∀ h : M.Hgt, h ∈ shDom Ŝ → ∀ q₀ ∈ M.Pools,
    ∃ N₀, ∀ N ≥ N₀, shWeightH Ŝ h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((shEvtH Ŝ h q₀ N).card : ℝ)
  wshval_card : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, ∃ N₀, ∀ N ≥ N₀,
    WshVal Ŝ q₀ * (Fintype.card (M.Box q₀ N) : ℝ) = ((shEvt Ŝ q₀ N).card : ℝ)
  Rval : Multiset T.VType → ℚ → ℝ
  r_bdd : ∀ σ (q₀ : ℚ), q₀ ∈ M.Pools → Rval σ q₀ ∈ Set.Icc (0 : ℝ) 1
  decidedTotal : ℚ → ℝ
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1
  rs1_equates : ∀ p ∈ PrimePools, (∑ σ ∈ Sigmas, Rval σ p) = decidedTotal p
  rsh_interp : ∀ σ ∈ Sigmas, ∀ p ∈ PrimePools, ∀ hdet : DetHyp T RB hK,
    ∃ hok : Rsh T M RB hdc hK hdet F WshP σ ∈ OKat p,
      ((evalAt p ⟨Rsh T M RB hdc hK hdet F WshP σ, hok⟩ : ℚ) : ℝ) = Rval σ p

/-- R23: the read-off bundle U-24b consumes — coordinate coverage as TYPED DATA.
EVERY e ∈ Icc 1 n, EVERY τA : Act (= every τ — the pools are all-active), EVERY σ',
every h_ent: total coordinate coverage, auditable from the type. -/
structure ReadOffBundle {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (S : Set ℚ) (hS : S ⊆ allActivePools M) (B : RS1Bundle T M RB hdc hK)
    (hdet : DetHyp T RB hK) where
  pkg : ∀ q₀, q₀ ∈ S → ∀ e (he : e ∈ Finset.Icc 1 n), PoolHyp T M RB e (hK e he) q₀
  read : ∀ q₀ (hq : q₀ ∈ S), ∀ e (he : e ∈ Finset.Icc 1 n),
    ∀ τA : (pkg q₀ hq e he).Act, ∀ σ' : Multiset T.VType, ∀ h_ent : ℕ,
    AVAgree (pkg q₀ hq e he) (blockSolve T RB hdc hK hdet e he (↑τA) σ')
      (bhatMeas (pkg q₀ hq e he) (fun e' he' => B.βmeas e' he' h_ent) σ') τA

end LeanUrat.MovesS

--- MovesS blueprint §W4-SYNC — THE SEAM CONTRACT (lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md, REV 13) ---
## §W4-SYNC — THE SEAM CONTRACT (REV 10; replaces §2.E as a build target)

**NOT LEAN UNITS. NOT BUILT AT E-PHASE.** The typed forms below (carried from
REV 9) are each entry's CURRENT PIN — the contract MovesT/MovesV re-key when
their vocabulary exists. Every Codex tie-demand across rounds 1–9 is recorded at
its entry; a seam entry is DONE only when re-keyed against the real corpora and
re-audited. The former file plan (`MovesS/Interfaces.lean`) is retired for these
declarations; the CORE keeps `RS1Bundle`/`RS4Chain`/`ReadOffBundle` (§2.D — typed,
tree-free) in `Interfaces.lean`, which at E-phase contains NOTHING from this
section.

**THE SEAM LIST (11 entries; tie-demand union + re-keying charge):**
- **S-1 `W1_RS1SH`** (+ **S-1e `W1e_equates`**, **S-1m `W1m_marked`**): current
  forms below. DEMANDS: premise all three on `RS1GivenPackage` (+ `Wsh17Package`
  at W1's CL-17(ii) leg) — Fable#7-GAP-1, FIXED at this contract: the S.2 GIVEN
  list premises ALL THREE RS.1 clauses; adjudication recorded — RS.1 is
  theorem-under-hypotheses in THIS note (not a consumed [5]-style item), so the
  pins carry the package. RE-KEY: package fields → the real MovesT statements.
- **S-2 `W2_xrb`**: DEMANDS (Codex#6-1): package fields must REFER to T/M/ledger/
  owner interfaces — re-key each Prop field to the real [2b]/[3t]/[2r] statement;
  until then the field-registry form stands as the contract shape ONLY.
- **S-3 `W3_recursion`**: DEMANDS (Codex#6-2): assume XRB's CONCLUSION (the
  invariance equality, or the thirteen premises + W2), not the bare implication;
  re-keyed form: `(hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …) → …`.
- **S-4 `W4_x3`**: consumed-item pin ([5]'s package displayed THERE); unchanged.
- **S-5 `W7_cutWD` + TreeIface**: DEMANDS (Codex#6-5): the no-reclassification
  fence must say "a deep split has a FIRST-ENTRANCE ANCESTOR" (placed strictly in
  an entered block subtree), not `¬isEntrance`; re-keyed clause:
  `∀ t ν, TI.isDeepSplit t ν → ∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν`.
- **S-6 `W8_bdy` + ReadLedger**: DEMANDS (Codex#6-6): tie ReadLedger to the tree
  — a per-entered-path assignment `RL : (t, first-entrance ν) → ReadLedger` with
  charges = the tree's read masses, Wcharge feeding WshVal, βcharge feeding βmeas.
- **S-7 `W10_convergence` + FiberIface**: DEMANDS (Codex#6-9): `Fib` must MAP to
  canonical-tree fibers (TREE-N's complete finite subtrees; disjointness; the
  ONE-F partition) — add `fibOf : Fib → TI.Tree`-style keying; βmeas = 0 must not
  trivialize (fiber nonemptiness where βmeas > 0).
- **S-8 `W17ii` + Wsh17Package**: DEMANDS (Codex#6-7/8): add the `xhd_s` face to
  the package; exclude the empty menu (`F.Sh.Nonempty`, or premise W7's tree_ne
  through S-5); package fields re-keyed to real interfaces. RE-KEYING REPLACES
  (R46): the gate's DEVICE fields `WshP`/`WshVal`/`shDom`/`shEvtH`/`visH`/
  `shEvt`/`shWeightH` (from the device batch n2_wshp_device/n2_sh_events/
  n2_sh_laws — R56) by the real production objects.
- **S-9 packages as registries** (Codex#6-1, global): every abstract Prop field
  in XRBPackage/RS1GivenPackage/Wsh17Package is a NAME AWAITING RE-KEYING — the
  contract's whole point; none is consumed by a core unit.
- **S-10 RS4Chain's tree-tied provenance**: `rs1_equates`/`rsh_interp`/
  `sh_realized`/`wshval_card` keep their field forms in core; their DISCHARGE
  provenance (TREE-EXP/CUT-WD/ONE-F) is seam. RE-KEYING REPLACES (R46): the
  device-satisfied instances of these laws at the gate by production-derived ones.
- **S-11 `n2_treeiface`** (ex-U-29d6): the gate's TreeIface instance + W7 check,
  built when TreeIface is re-keyed.

The REV-9 typed forms (the contract's current shapes):

```lean
-- minimal carriers for statements whose native vocabulary is MovesT's:
structure TreeIface (T : TableShape n) where       -- W-7's carrier — R41-COMPLETED
  Tree : Type
  tree_ne : Nonempty Tree                           -- no empty-carrier vacuity
                                                    --   (Codex#5-3)
  Node : Tree → Type
  finN : ∀ t, Fintype (Node t)
  node_ne : ∀ t, Nonempty (Node t)                  -- a tree has a root
  onPath : ∀ t, Node t → Node t → Prop              -- ν ≼ ν′: ν on ν′'s root-path
  path_refl : ∀ t ν, onPath t ν ν                   -- ROOT-PATH ORDER LAWS (R41):
  path_trans : ∀ t ν₁ ν₂ ν₃, onPath t ν₁ ν₂ → onPath t ν₂ ν₃ → onPath t ν₁ ν₃
  path_antisymm : ∀ t ν ν', onPath t ν ν' → onPath t ν' ν → ν = ν'
  path_total : ∀ t ν₁ ν₂ ν, onPath t ν₁ ν → onPath t ν₂ ν →   -- ancestors of a node
    onPath t ν₁ ν₂ ∨ onPath t ν₂ ν₁                            -- are comparable
  isEntrance : ∀ t, Node t → Prop                   -- the CL-13 entrance predicate
  decE : ∀ t, DecidablePred (isEntrance t)          --   (CTS-M(i)/(iii) supply)
  isDeepSplit : ∀ t, Node t → Prop                  -- b_e^split sites (R41: typed,
                                                    --   for the reclassification
                                                    --   fence — Fable#6-G3)
  blockOf : ∀ t (ν : Node t), isEntrance t ν → Σ e, T.State e   -- the entered block
  entδ : ∀ t (ν : Node t), isEntrance t ν → ℕ+      -- the entrance's δ-leg factor
  leafHalt : ∀ t, Node t → Option T.VType           -- shallow τ-halt leaves (σ₀ feed)
  shapeOf : Tree → Shape T                          -- CUT-3's choice-free assignment
structure FiberIface (T) (M : MeasuredSide T) where -- W-10's carrier
  Fib : ∀ e, T.State e → Multiset T.VType → Type    -- complete finite subtrees w/ leaf
  ctbl : ∀ e τ σ', Countable (Fib e τ σ')           --   multiset of type σ′ (TREE-N)
  fibMass : ∀ e τ σ', Fib e τ σ' → ℕ → ℚ → ℝ        -- per-fiber mass given h_ent
structure ReadLedger where                          -- W-8's carrier (one entered path)
  L fe : ℕ ; hfe : fe ≤ L
  charge : ℕ → ℝ                                    -- per-read mass attribution
  Wcharge βcharge : ℝ                               -- the W_Ŝ-side / β-side totals

-- the pinned deferrals (each cites its owner; NONE is a wave-2 unit):
def W1_RS1SH (Π' : RS1GivenPackage) (Πw : Wsh17Package) (Π : XRBPackage)
    (L : LedgerIV T M) (C : RS4Chain …) (hdet) : Prop :=   -- RS.1-SH, PREMISED on
  Π'.tree_exp_fin → Π'.tree_exp_ns → Π'.tree_n → Π'.one_f → Π'.sib →   -- the S.2
  Π'.tb_cap → Π'.vp → Π'.pci →                                          -- GIVEN
  Π'.rel2_a → Π'.rel2_b → Π'.rel2_c → Π'.rel2_d → Π'.rel2_e →           -- list +
  Πw.c15_volumes → Πw.cts_counts → Πw.sib_count →       -- CL-17(ii)'s leg + XRB
  W2_xrb Π (B₀-of C) →                                  -- (Fable#7-GAP-1, fixed at
  ∀ σ ∈ C.Sigmas, ∀ p ∈ C.PrimePools,                   --  the contract): the S.2
    ∃ hok : Rsh T M RB hdc hK hdet F C.WshP σ ∈ OKat p, --  GIVEN list premises ALL
      ((evalAt p ⟨Rsh T M RB hdc hK hdet F C.WshP σ, hok⟩ : ℚ) : ℝ) = C.Rval σ p
  -- THREE RS.1 clauses; the symbolic half is definitional (U-18 defines Rsh).
  -- ADJUDICATION (recorded): RS.1 is THIS note's theorem-under-hypotheses (S.2),
  -- not a consumed [5]-style item — so its pins CARRY the package (contrast W4).
def RS1Given.holds (Π' : RS1GivenPackage) : Prop :=  -- the premise row, named once
  Π'.tree_exp_fin ∧ Π'.tree_exp_ns ∧ Π'.tree_n ∧ Π'.one_f ∧ Π'.sib ∧
  Π'.tb_cap ∧ Π'.vp ∧ Π'.pci ∧
  Π'.rel2_a ∧ Π'.rel2_b ∧ Π'.rel2_c ∧ Π'.rel2_d ∧ Π'.rel2_e
def W1e_equates (Π' : RS1GivenPackage) (C : RS4Chain …) : Prop :=
  RS1Given.holds Π' →                                -- the S.2 GIVEN list (GAP-1)
  ∀ p ∈ C.PrimePools, (∑ σ ∈ C.Sigmas, C.Rval σ p) = C.decidedTotal p
def W1m_marked (Π' : RS1GivenPackage) (B : RS1Bundle …) (hdet) : Prop :=
  RS1Given.holds Π' →                               -- RS.1-MARKED, premised (GAP-1)
  ∀ e (he : e ∈ Finset.Icc 1 n) q₀ (h : q₀ ∈ M.Pools)   -- + GATED per pool:
    (hok : (markedPairing T M RB hdc hK hdet e he).val ∈ OKat q₀),
      ((evalAt q₀ ⟨_, hok⟩ : ℚ) : ℝ) = M.markedVal e q₀
    -- the OKat membership (no pole surviving cancellation — the (ii-c) PASS) is a
    -- HYPOTHESIS, agreement the conclusion: "the sealed check … must pass BEFORE it
    -- may be read off; a pole SURVIVING cancellation at a wild pool is (ii-c)'s
    -- FAIL" — the pin demands nothing at pools where the gate fails
/-- S.1's displayed hypothesis package as TYPED FIELDS (R37/R38, Codex#5-1): each
    an abstract owner-tagged Prop, instantiated by its owner's REAL statement at
    wave 4. Owners per the S.1 STATUS LINE. -/
structure XRBPackage where
  xhd_w : Prop ; xhd_u : Prop ; xhd_d : Prop ; xhd_s : Prop  -- [2b]; discharge
                                                              --   = [1v]-FULL
  jc_inv : Prop                                               -- [2b] (rev-2, NEW)
  sib : Prop ; jc_multi : Prop                                -- CL-10, [3t], OPEN
  tb_cap : Prop ; vp : Prop                                   -- [3t] §T.2 statuses
  rel2_a : Prop ; rel2_b : Prop ; rel2_d : Prop               -- CL-8, [2r], OPEN
  ns_null : Prop                                              -- [3t] §T.2, CLOSED

def W2_xrb (Π : XRBPackage) (B₀ : RS1Meas T M) : Prop :=      -- the obligation that
  Π.xhd_w → Π.xhd_u → Π.xhd_d → Π.xhd_s → Π.jc_inv →          -- CREATES
  Π.sib → Π.jc_multi → Π.tb_cap → Π.vp →                      -- RS1Bundle.xrb at
  Π.rel2_a → Π.rel2_b → Π.rel2_d → Π.ns_null →                -- wave 4: XRB GIVEN
  ∀ e he h h' τ σ' q₀, q₀ ∈ M.Pools →                          -- the package — the
    B₀.βmeas e he h τ σ' q₀ = B₀.βmeas e he h' τ σ' q₀         -- S.1 theorem-under-
  -- hypotheses SHAPE, typed (R38); pool-quantified (R40). No premise in comments.
/-- S.2's GIVEN-list as TYPED FIELDS (R37/R38, Codex#5-2). The nine-input ledger
    enters as the REAL `LedgerIV` (already typed); the XRB leg as W2's statement. -/
structure RS1GivenPackage where
  tree_exp_fin : Prop ; tree_exp_ns : Prop ; tree_n : Prop ; one_f : Prop  -- [3t]
  sib : Prop                                                   -- CL-10, [3t], OPEN
  tb_cap : Prop ; vp : Prop                                    -- [3t] §T.2
  pci : Prop                                                   -- [3t] (PCI =
                                                               --  REL.2(a)(b)(d) +
                                                               --  (iv)-REP + XRB)
  rel2_a : Prop ; rel2_b : Prop ; rel2_c : Prop ; rel2_d : Prop ; rel2_e : Prop
                                                               -- CL-8, [2r], OPEN

def W3_recursion (Π' : RS1GivenPackage) (Π : XRBPackage) (L : LedgerIV T M)
    (B₀ : RS1Meas T M) : Prop :=                    -- CREATES recursion_meas:
  Π'.tree_exp_fin → Π'.tree_exp_ns → Π'.tree_n → Π'.one_f → Π'.sib →
  Π'.tb_cap → Π'.vp → Π'.pci →
  Π'.rel2_a → Π'.rel2_b → Π'.rel2_c → Π'.rel2_d → Π'.rel2_e →
  W2_xrb Π B₀ →                                     -- "XRB (S.1, proved above)"
  ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools), M.activeState q₀ e τ →
    ∀ h_ent, B₀.βmeas e he h_ent τ σ' q₀
    = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => B₀.βmeas e' he' h_ent)
  -- the S.2 GIVEN-list ("the [3t] package (TREE-EXP fin/ns + TREE-N + ONE-F;
  -- (SIB), CL-10; TB-CAP/VP), the S.0 nine-input ledger (CL-5), XRB (S.1), and
  -- [2r]'s REL.2 obligations at every base-changed leg (CL-8)") — EVERY item a
  -- typed premise (L is the real ledger; the rest owner-tagged Props per R37);
  -- activity-guarded, identical quantifier to the field (R16(i)).
def W4_x3 (C : RS4Chain …) : Prop := ∀ p ∈ C.PrimePools, C.decidedTotal p = 1
def W7_cutWD (F : ShapeFam T) (TI : TreeIface T) : Prop :=   -- (CUT-WD), R41-complete
  -- (CUT-1) — with TreeIface's order laws, ancestors are comparable; the clause is
  -- LEAST-FIRST-ENTRANCE (not mere antisymmetry — Codex#5-3):
  (∀ t (ν : TI.Node t), (∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν) →
    ∃! ν₀, TI.isEntrance t ν₀ ∧ TI.onPath t ν₀ ν ∧
      ∀ ν', TI.isEntrance t ν' → TI.onPath t ν' ν → TI.onPath t ν₀ ν') ∧
  -- (CUT-2) exhaustive/nonoverlapping is the ∃!-dichotomy the above induces
  -- (shallow := no entrance ancestor; else the UNIQUE first entrance) — plus the
  -- TYPED NO-RECLASSIFICATION FENCE (Fable#6-G3, a clause not a comment):
  (∀ t (ν : TI.Node t), TI.isDeepSplit t ν → ¬ TI.isEntrance t ν) ∧
  -- shallow τ-halts feed σ₀(Ŝ):
  (∀ t, (TI.shapeOf t).σ0 =
    (Finset.univ.filter (fun ν : TI.Node t =>
      ¬ ∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν)).val.filterMap
      (TI.leafHalt t)) ∧
  -- (CUT-3) with the ENTRANCE-BOUNDARY-DATA clause (Fable#6-G2): the shape's
  -- entrance lists ARE the tree's first entrances, blocks and δ-legs matching —
  -- "entrance and halt boundary data retained":
  (∀ t, ∃ enum : Fin (TI.shapeOf t).k ≃
      {ν : TI.Node t // TI.isEntrance t ν ∧
        ∀ ν', TI.isEntrance t ν' → TI.onPath t ν' ν → ν' = ν},
    ∀ i, ∃ hE : TI.isEntrance t (enum i).1,
      TI.blockOf t (enum i).1 hE
        = ⟨(TI.shapeOf t).eOf i, (TI.shapeOf t).τOf i⟩ ∧
      TI.entδ t (enum i).1 hE = (TI.shapeOf t).δOf i) ∧
  (∀ t, TI.shapeOf t ∈ F.Sh)                        -- choice-free, listed
-- The (BDY) mass clause (node block-side as STATE INDEX = blockOf's type,
-- structural; the entering EDGE entrance-side) is the SEPARATE pin W8_bdy
-- (ReadLedger), cited per entered path. Non-vacuity: TreeIface.tree_ne/node_ne.
def W8_bdy (RL : ReadLedger) : Prop :=              -- (BDY) consumption: the entering
  RL.Wcharge = ∑ r ∈ Finset.Icc 0 RL.fe, RL.charge r ∧                -- read is W-side
  RL.βcharge = ∑ r ∈ Finset.Icc (RL.fe + 1) RL.L, RL.charge r         -- β charges none
def W10_convergence (B : RS1Bundle …) (FI : FiberIface T M) : Prop :=
  ∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools →              -- S.2 CONVERGENCE display:
    (∀ f : FI.Fib e τ σ' , 0 ≤ FI.fibMass e τ σ' f h_ent q₀) ∧    -- POSITIVE series
    HasSum (fun f : FI.Fib e τ σ' => FI.fibMass e τ σ' f h_ent q₀)  -- (Codex-6:
      (B.βmeas e he h_ent τ σ' q₀)                  -- summand nonneg + bounded by 1
                                                    -- via β_bdd = the note's
                                                    -- "positive series bounded by 1,
                                                    -- rearrangements licit (Tonelli)")

/-- CL-17(ii)'s production faces as TYPED owner-tagged Props (R37/R42). -/
structure Wsh17Package where
  c15_volumes : Prop                                -- §C C.1.5 node volumes
  cts_counts : Prop                                 -- CTS/[1] counts ([1v])
  sib_count : Prop                                  -- (SIB)'s COUNT face across
                                                    --   shallow splits ([3t]/CL-10)

def W17ii (Π : Wsh17Package) (C : RS4Chain …) : Prop :=   -- CL-17(ii), OPEN — now
  Π.c15_volumes → Π.cts_counts → Π.sib_count →            -- INSIDE the fence
  ∀ Ŝ ∈ F.Sh, ∀ q₀ (h : q₀ ∈ M.Pools),                    -- (Fable#6-G4) and
    (∃ hok : (C.WshP Ŝ).val ∈ OKat q₀,                    -- PREMISED on the typed
      ((evalAt q₀ ⟨(C.WshP Ŝ).val, hok⟩ : ℚ) : ℝ) = C.WshVal Ŝ q₀) ∧   -- production
    HasSum (fun hh : C.shDom Ŝ => C.shWeightH Ŝ hh q₀) (C.WshVal Ŝ q₀)  -- package
  -- "every W_Ŝ is PRODUCED by the stated rational machinery (C.1.5 node volumes ×
  -- CTS/[1] counts × XHD-s shallow height sums, with (SIB)'s COUNT face across
  -- shallow splits)": the height-sum face over the TYPED carriers shDom/shWeightH
  -- (card-pinned by shweight_card; nonempty by shDom_ne/sh_realized — no ∅/0
  -- model, R42); owners [1v]/[3t]; remains OPEN (CL-17).
```

W-5 (nsNull's discharge) is the field `RS4Chain.hns` — demanded, not deferred-loose.
W-6 (wild-pool read-off) is the Prop `AVAgree` (§2.C), cited per consumption site.
W-9 is RETIRED (subsumed by the R7 event carrier in LedgerIV). W-11 (instantiation of
every §2 structure by the REAL CTS objects) is a wave-4 PROCESS gate (§5), not a Prop.

---

## 3. The unit DAG — REV 12: THE CORE, 95 units (52 easy / 43 medium / 0 hard);

==================================================================
THE BLUEPRINT (full: lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md):
==================================================================

# MOVESV LEAN BLUEPRINT — REV 1 (wave 4)

*(2026-07-28, Fable blueprint writer. GROUND TRUTH: the frozen dual-accepted
§V-TABLES text, `lean/notes/MOVES_2026-07-24.md` lines 7829–9054 (rev 7 —
Codex passes 6+7 + Fable pass, all CLEAN on identical text; V-n3 gate PASSED
178/178). A Lean statement below is faithful iff it says what that text's
display says. Campaign doctrine per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`
§2/§3 + the wave-2 ledger doctrine: "a faithful interface must be FALSE for
instances the note would reject; obligations may be open, but their TYPES must
pin their content" — every hypothesis package below is TYPED FIELDS, never
comments, and every package carries a non-degeneracy law or an inhabitation
witness unit.)*

## §0 Charge, status, and the conditionality banner

**WHAT THIS CORPUS IS.** §V-TABLES = assembly note [1v]-COND: ONE fixed
p-independent state space of syntactic branch-cells (V.2), one polynomial table
family T counting per-cell fresh-assignment transitions (V.2), and ONE measured
theorem — CTS-M (V.1) — typing how counts (T), fixed-height weights (g),
resummed weights (G), entrance masses (ι), and marked masses (μ̂) compose,
EACH CLAUSE GIVEN EXACTLY its V.1-ledger hypothesis set. Every left-hand side
is a MARKED-BRANCH mass μ̂ (μ̂(E) := Σ_η μ({f : (f,η) ∈ E}) — a sum over marks
BY DEFINITION), never an f-event mass and never a density.

**THE CONDITIONALITY BANNER (binding on every unit and on the corpus record).**
- XHD (XHD-w/-d/-s) + (XHD-u) + (ENT-U): OPEN, owner [2b] §H-DOMAINS (its six
  H.6 fences block [1v]-FULL). In Lean they are the §2.B typed hypothesis
  structures; NO unit proves them; the discharge is the separate recorded
  event [1v]-FULL (V1-5's `IsFullDischarge` — bookkeeping, no mathematics).
- (v) HMC: OPEN KERNEL (probe specced-and-pinned at V.4, RUN status per the
  note: NOT run at freeze). Typed at §2.G; (HMC-AUG) a SEPARATE named Prop.
- ENT-COUNT, (ENT-U), INIT-RAT: named burdens of clause (iii) — statements
  typed, INIT-RAT a theorem-under-hypotheses unit (V3-9c).
- (J-RAT)/CL-18: owner [1v] (with [2b] on the height-sum face) — THE PLAN-SYNC
  deliverable this corpus records on the owner side: the per-cell tables
  J_{τ,o} ∈ ℚ(q) ENTRYWISE, beyond PART-1's total (layer V5, units V5-7*).
- (ii-c) ACTIVE-VALUE: a finite per-(n, q₀) check (MovesS's AVAgree shape),
  recorded, never a blanket det ≠ 0 claim.
- Inherited: §C (via MovesC/HC-2 — the C.1.5(1)/TYP(b) faces ride as the typed
  `C15Pack`, owner tag §C/HC-2), §D4-R (MovesD — PROVED core consumed),
  [2a] §M-SPECIES (MovesSp — PROVED, so the note's "[2a] pending" inheritance
  is DISCHARGED against the Lean corpus at n = 3; recorded as an upgrade,
  not a deviation: the note's conditionality only shrinks).
- ESCAPE(E0): [3]'s duty (MovesS.EscapeE0); cited only inside (vi)'s
  conditional solve sentence, never claimed here.
- [3t] fence: VP, TB-CAP, TREE-EXP/ONE-F, tree pruning are NOT in this corpus;
  terminal outcome labels are consumed as ABSORBING COLUMN LABELS only
  (`VLabel`, §2.C). Equating any μ̂ object of this corpus with an f-event mass
  is a TYPE ERROR except through [3t]'s displayed conversion (MovesT, wave 4).

**WHAT IS PROVED OUTRIGHT HERE (no hypothesis fields):** (U-A) as the note
proves it (V1-6, GIVEN only the typed §C-supply pack — the note's own GIVEN);
the clause-(i) meet lemma (V2-3); ENT-AGG's finite half (V3-7); (ii-a)/(ii-b)
given the count-semantics field (V4-1/2); PART-2's n = 3 surplus ≡ 0 (V4-8);
the naming-discipline iff (V4-12); the entire V.6 gate layer (V6-*: closed
forms, PART-1 count faces, DEG-CONS rosters, domain normal form, the gate-B
dyadic arithmetic and two-history discipline) — decide/ring/norm_num-native.

## §1 Consumption map (all PROVED corpora; owner tags for open vocabulary)

| consumed | what | where used |
|---|---|---|
| `MovesSp` (PROVED, dual-accepted rev 5) | `Species` (SP.1 datum, heights forgotten BY TYPE), `InCatalogue`/`SnRaw`, `Succ`/`Out` (SP-OUT syntactic menus, NO field evaluated), `Verdict` (bare labels), `EntranceShape` (the species-word entrance carrier with height SLOTS), SP2 finiteness (`SP2_finThm`), the 53-catalogue + SP6 menu roster (kernel-decided) | §2.C skeletons + (D1) menus; V2-1; the (iii) template layer V3-3/V3-4; V4-8's roster; clause (i)'s [2a] discharge |
| `MovesD` (PROVED core, rev 9 seam split) | `Shape n`/`ShapePrefix`/`ShapeRead` (L3 rev 9: retains per-read (h, u*) — fields `h`, `ustar`), `Presented`/`PrefIdx`/`Presented.fiber`/`mult`, `Box`, `D4R1_SUM` (D10), `mult_sum` (D11a), `D4R4_all`, `ShapePrefix.A`/`A'`/`W` | §2.E entrance shapes ε (P̂ concrete WITH heights); ι's counting-native def; A(ε) = A(P̂), W_ent(ε) = W(P̂); the marked-event census V5-1 |
| `MovesS` core (E-phase built) | `Qq`, `PolyGeom`, `OKat`/`evalAt`, `MuHat`, `TableShape`, `MeasuredSide`, `RatBurdens`, `LedgerIV`, `DegCons`, `KmatHyp`, `EscapeE0`, `AVAgree` | §4 SEAM-SUPPLY: layer V7 instantiates; §2 reuses the ℚ(q) plumbing verbatim (NO re-derivation) |
| `MovesC` (PROVED) — owner tag §C/HC-2 | Theorem C(b) engine; C.1.5(1)/TYP(b) have NO standalone Lean form yet | the `C15Pack` typed supply for (U-A) (§2.B); each field cites its §C display; discharge = HC-2 territory |
| owner [2b] §H-DOMAINS | XHD-w/-u/-d/-s, (ENT-U), (JC-INV) | typed hypothesis structures §2.B; NEVER proved here |
| owner [3t] → MovesT | VP/TB-CAP/TREE-EXP/ONE-F/(SIB) | absent; absorbing labels only (`VLabel`) |
| owner [3] MovesS | ESCAPE(E0), the solve | cited in (vi)'s solve sentence via `MovesS.EscapeE0`/`DetHyp` |

Ownership fence, restated binding: this corpus does NOT own and nowhere
re-derives VP, TB-CAP, TREE-EXP/ONE-F (the SOLE marked→per-f conversion), the
nine-input ledger's probabilistic reading (CL-5, [3] RS.PRE), or exhaustion
([5]). K_e's construction as a MATRIX is MovesS's (`Kmat`); this corpus
supplies its ENTRY tables and their laws.

DAG position: MovesV consumes MovesSp + MovesD + MovesS-core (+ MovesC via the
typed pack); it is consumed by MovesS's wave-4 seam (§W4-SYNC) and MovesT.
Import direction `MovesV → MovesS.Defs/Interfaces` is ACYCLIC: MovesS's core
never imports MovesV (its intended-instance comments become real here).

## §2 The Defs layer — `MovesV/Defs.lean` (+ `DefsGate.lean` for V.6 data)

Declaration order below is normative. Defs are sorry-free; every law with
content is a UNIT, not a Defs field, EXCEPT hypothesis-package fields (which
are obligations by design, per the doctrine). `open LeanUrat.MovesS (Qq
PolyGeom OKat evalAt MuHat)` — the ℚ(q) plumbing is reused, never rebuilt.

### 2.A The height apparatus (V.0's ambient objects, "defined here so the package is CLOSED and refutable")

```lean
namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq PolyGeom OKat evalAt MuHat)

/-- A height point in D ℕ-slots (V.0: "the tuple of its reads' ℕ-height
parameters (the parameters [2a] SP.1 forgets; d_i height slots at step i)"). -/
abbrev Hpt (D : ℕ) := Fin D → ℕ

/-- (XHD-w)'s exponent: "E affine in h with positive weights". The weights are
DATA with a typed positivity law — a weight-0 (h-degenerate) instance is
UNSATISFIABLE, per the wave-2 doctrine. -/
structure AffineE (D : ℕ) where
  const : ℕ
  coeff : Fin D → ℕ
  pos   : ∀ i, 1 ≤ coeff i

def AffineE.eval {D : ℕ} (E : AffineE D) (h : Hpt D) : ℕ :=
  E.const + ∑ i, E.coeff i * h i

/-- V.0: "a LINEAR SET in ℕ^D is L(h₀; P) := {h₀ + Σ_{v∈P} n_v·v : n_v ∈ ℕ}
with base h₀ ∈ ℕ^D and a FINITE period list P" — bases and periods EXPLICITLY
LISTED (the "congruence-class translates" gloss is struck). -/
structure LinSet (D : ℕ) where
  base    : Hpt D
  periods : List (Hpt D)

def LinSet.Mem {D : ℕ} (L : LinSet D) (h : Hpt D) : Prop :=
  ∃ c : Fin L.periods.length → ℕ,
    h = fun i => L.base i + ∑ j, c j * (L.periods.get j) i

/-- THE DISJOINT-COMPONENT CONVENTION (rev 3, pass-2 finding 1), AS A TYPE:
every semilinear domain this corpus consumes is a LISTED PARTITION — the
listed linear sets pairwise disjoint. Overlapping lists are UNSATISFIABLE. -/
structure SemilinPart (D : ℕ) where
  comps : List (LinSet D)
  disj  : comps.Pairwise (fun L L' => ∀ h, ¬(L.Mem h ∧ L'.Mem h))

def SemilinPart.Mem {D : ℕ} (S : SemilinPart D) (h : Hpt D) : Prop :=
  ∃ L ∈ S.comps, L.Mem h
```

### 2.B The XHD hypothesis packages (V.0, typed; owner [2b]; + the (U-A) supply pack, owner §C/HC-2)

XHD is stated over the STEP SYSTEM `StepSys` (§2.C below defines its intended
instance; the structures here are parameterized so [2b]'s eventual discharge
re-keys once). The RAW primitives are HISTORY-INDEXED — without that, (u-R)
and (U-A) would be contentless (the pass-1/2 lumpability findings).

```lean
/-- The index vocabulary + measured primitives XHD quantifies over (V.0:
"for every step datum (m, o) with source cell α and target cell β, and every
height point h"). `Hist α` = admissible histories/representatives reaching a
concrete state of α (x AND its history — (u-R)'s quantifier); `Assign` = the
fresh-assignment fiber realizing (m, o, β) at h from x; `massOf` = the
per-assignment C.1.5 conditional mass carrier; `cntraw` = T(h) from x. -/
structure StepSys (n : ℕ) where
  Cell  : Type                        -- 𝒞_n, symbolic, p-independent BY TYPE
  finC  : Fintype Cell
  Move  : Cell → Cell → Type          -- continuing step data (m, o) : α → β
  MoveT : Cell → VLabel n → Type      -- terminal-final step data (rev-4 exit
  finM  : ∀ α β, Fintype (Move α β)   --   objects; β_k := absorbing label)
  finMT : ∀ α v, Fintype (MoveT α v)
  dim   : ∀ {α β}, Move α β → ℕ       -- the step's height-slot count d_i
  dimT  : ∀ {α v}, MoveT α v → ℕ
  Pools : Set ℚ                       -- prime-power evaluation points
  pools_gt_one : ∀ q₀ ∈ Pools, (1 : ℚ) < q₀
  Hist  : Cell → Type
  hist_ne : ∀ α, Nonempty (Hist α)
  zc    : ∀ {α}, Hist α → Prop        -- (ZC)-satisfying realizable prefixes
  Assign : ∀ {α β} (m : Move α β), Hist α → Hpt (dim m) → Type
  finA   : ∀ {α β} (m : Move α β) x h, Fintype (Assign m x h)
  AssignT : ∀ {α v} (m : MoveT α v), Hist α → Hpt (dimT m) → Type
  finAT  : ∀ {α v} (m : MoveT α v) x h, Fintype (AssignT m x h)
  massOf : ∀ {α β} (m : Move α β) (x : Hist α) (h : Hpt (dim m)),
    Assign m x h → ℚ → ℝ              -- the C.1.5 fresh-volume ratio, per cell
  massOfT : ∀ {α v} (m : MoveT α v) (x : Hist α) (h : Hpt (dimT m)),
    AssignT m x h → ℚ → ℝ
  cntraw : ∀ {α β} (m : Move α β), Hist α → Hpt (dim m) → ℕ   -- T(h) from x
  inv    : ∀ {α β}, Move α β → Hpt 0 ⊕ Unit → Unit            -- PLACEHOLDER, see
  -- [DESIGN FREEDOM, audit round]: `inv` above is a stub slot for the NOMINAL
  -- DIGIT INVENTORY carrier consumed by C15Pack; the E-designer replaces it by
  -- `Inv : Type` + `invOf : ∀ {α β} (m : Move α β), Hist α → Hpt (dim m) → Inv`
  -- (C.1(ii): inventory = strip-pin count + alphabet sizes, a function of the
  -- read's shape data). Recorded here so the audit sees the slot, not prose.

/-- (U-A)'s §C supply, TYPED (V.0 "WHAT §C ACTUALLY SUPPLIES, displayed"):
C.1.5(1) gives per fresh assignment vol_nom(E_fresh) = q^{−#(strip pins)} ·
∏_slots (alphabet size)^{−1}, and BOTH factors are functions of the read's
NOMINAL DIGIT INVENTORY (C.1(ii)) — never of which values the cell pins.
Owner §C/HC-2; each field cites its display. -/
structure C15Pack (n : ℕ) (S : StepSys n) where
  Inv   : Type
  invOf : ∀ {α β} (m : S.Move α β), S.Hist α → Hpt (S.dim m) → Inv
  F     : Inv → ℚ → ℝ                 -- the common conditional-mass functional
  mass_factors : ∀ {α β} (m : S.Move α β) (x : S.Hist α) (h : Hpt (S.dim m))
    (a : S.Assign m x h) (q₀ : ℚ), q₀ ∈ S.Pools → S.zc x →
    S.massOf m x h a q₀ = F (invOf m x h) q₀
  -- [C.1.5(1) + TYP(b): the mass is q^{−pins(inv)}·∏ alph(inv)⁻¹; the
  -- factored NUMERIC form is a second field the E-designer adds if a unit
  -- needs it; `mass_factors` alone carries (U-A)'s derivation.]

/-- (XHD-w) WEIGHTS, typed: per step datum a monomial g = q^{−E(h)}, E affine
positive, EQUAL to the per-assignment C.1.5 ratio at h — "the conditional
mass, given the source cylinder at ANY representative of α under ANY
admissible history reaching it, of one fresh assignment realizing (m, o, β)
at h". Indexed by SOURCE AND TARGET cells (pass-6 concern 1). Owner [2b]. -/
structure XHDw (n : ℕ) (S : StepSys n) where
  E : ∀ {α β} (m : S.Move α β), AffineE (S.dim m)
  ET : ∀ {α v} (m : S.MoveT α v), AffineE (S.dimT m)
  w_eq : ∀ {α β} (m : S.Move α β) (x : S.Hist α) (h : Hpt (S.dim m))
    (a : S.Assign m x h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOf m x h a q₀ = (q₀ : ℝ) ^ (-((E m).eval h : ℤ))
  wT_eq : ∀ {α v} (m : S.MoveT α v) (x : S.Hist α) (h : Hpt (S.dimT m))
    (a : S.AssignT m x h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOfT m x h a q₀ = (q₀ : ℝ) ^ (-((ET m).eval h : ℤ))

/-- the derived one-step weight (a def, not a field): g^{α,β}_{m,o}(h)(q₀). -/
noncomputable def XHDw.g {n} {S : StepSys n} (X : XHDw n S) {α β}
    (m : S.Move α β) (h : Hpt (S.dim m)) (q₀ : ℚ) : ℝ :=
  (q₀ : ℝ) ^ (-((X.E m).eval h : ℤ))

/-- (XHD-u) UNIFORMITY (rev 2, findings 2–3), typed. (u-R): ratio and count
depend on x and its history ONLY through (α, β, m, o, h). (u-T): the count is
one h-independent value per step ON the one-step domain, with the counterpart
clause carried by XHD-d's no-stray. Owner [2b]; NOT §C-derivable (V.0's honest
split — the fence unit V1-7 exhibits a C15Pack model violating u_R). -/
structure XHDu (n : ℕ) (S : StepSys n) where
  u_R_mass : ∀ {α β} (m : S.Move α β) (x x' : S.Hist α) (h : Hpt (S.dim m))
    (a : S.Assign m x h) (a' : S.Assign m x' h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOf m x h a q₀ = S.massOf m x' h a' q₀
  u_R_cnt : ∀ {α β} (m : S.Move α β) (x x' : S.Hist α) (h : Hpt (S.dim m)),
    S.cntraw m x h = S.cntraw m x' h
  u_T : ∀ {α β} (m : S.Move α β) (x : S.Hist α) (h h' : Hpt (S.dim m)),
    -- height rectangularity on the exact one-step domain (dom₁ from XHDd):
    -- stated domain-conditionally at the XHD bundle (see `XHD.u_T_dom`);
    -- the RAW field here demands it where both heights are realized:
    0 < S.cntraw m x h → 0 < S.cntraw m x h' →
    S.cntraw m x h = S.cntraw m x h'
```

`Template`/`XHDd`/`XHDs` need the path vocabulary; they follow in §2.G after
the state space, keeping V.0's own order (the package is stated at V.0 but
quantifies over templates constructed at V.2). The XHD BUNDLE:

```lean
/-- THE XHD PACKAGE (V.0), one record: w + u + d + s (s parameterized by w, d
— see §2.G). [1v]-FULL is V1-5's `IsFullDischarge` (the recorded-discharge
event — bookkeeping, no new mathematics); until it is instantiated every
measured unit takes the package (or the exact sub-package its V.1 ledger line
names) as an explicit argument — the tag displayed at its site. -/
structure XHD (n : ℕ) (S : StepSys n) where
  w : XHDw n S
  u : XHDu n S
  d : XHDd n S
  s : XHDs n S w d
```

### 2.C The state space 𝒞_n (CTS-S) and the computed-partition deliverable (D1)–(D4)

```lean
/-- A SKELETON s (V.2 CTS-S): "the [2a] SP.1 stage/side/residual-shape fields
of the CURRENT node, values and heights forgotten" — EXACTLY MovesSp.Species
(which forgets heights BY TYPE), catalogue-membered. p-INDEPENDENCE BY TYPING:
no field mentions a prime. -/
structure Skeleton (n : ℕ) where
  sp  : MovesSp.Species
  mem : MovesSp.InCatalogue n sp

/-- Absorbing column labels: (e, f) with e·f ≤ n — verdict SEMANTICS is [3t]
VP's, "consumed here only as absorbing column labels"; this carrier is also
MovesS's R20 pin verbatim (TableShape.vEquiv will be `Equiv.refl`-keyed). -/
abbrev VLabel (n : ℕ) := {ef : ℕ+ × ℕ+ // (ef.1 : ℕ) * (ef.2 : ℕ) ≤ n}

/-- ONE (D2) GENERATOR over the per-prime concrete-state carrier: a UNIFORM
finite partition — one fixed label set, a total per-q₀ cell assignment. The
note's two generator classes ride the `kind` tag: (a) anchor-twisted VAL.1
cells (twist exponent DISPLAYED) or (b) a relational stratum (its polynomial
relation named by `relName`, its exceptional-characteristic convention as the
per-q₀ assignment itself — the convention IS the map). -/
structure GenSpec (Carrier : ℚ → Type) where
  idx    : Type
  finI   : Fintype idx
  part   : ∀ q₀, Carrier q₀ → idx       -- total ⟹ a partition, typed
  kind   : (twist : ℤ) ⊕ (relName : String)
  -- [audit note: `String` carries the (D2) display duty "each relation named
  -- WITH its polynomial and its exceptional-characteristic convention"; the
  -- polynomial itself lives in the E-designer's per-instance `relPoly` field
  -- where a unit consumes it — no unit in this corpus computes with it.]

/-- (D1)–(D4) for ONE skeleton — CL-13's COMPUTED-PARTITION DELIVERABLE, one
typed record (V.2: "the meet symbol is a construction RECIPE; the clause-(i)
deliverable is the DISPLAYED LIST"). The MEET CELLS are the fibers of the
product of generator maps — "explicit cell predicates as boolean combinations
of (D2)'s generators" is DEFINITIONAL here. -/
structure BlockData (n : ℕ) (s : Skeleton n) where
  Carrier : ℚ → Type                       -- concrete states over F_{q₀}
  finCar : ∀ q₀, Fintype (Carrier q₀)
  -- (D1) the menu: [2a] SP-OUT letters from s, membership TYPED:
  Letter : Type
  finL   : Fintype Letter
  letterSp : Letter → MovesSp.Species ⊕ MovesSp.Verdict
  letter_menu : ∀ m, letterSp m ∈ MovesSp.Out n s.sp
  -- (D2) the generator list:
  Gen  : Type
  finG : Fintype Gen
  gen  : Gen → GenSpec Carrier
  -- (D3) the meet list: labels = the product of generator labels; size
  -- polynomials with the SPLIT degree bound (W_state(s), never any W_loc):
  Wstate : ℕ
  sizeP  : (∀ g : Gen, (gen g).idx) → Polynomial ℚ
  size_deg : ∀ a, (sizeP a).natDegree ≤ Wstate
  size_count : ∀ (a) (q₀ : ℚ) (hq : IsPP q₀),   -- IsPP: prime-power predicate
    ((sizeP a).eval q₀ : ℚ)
      = (Finset.univ.filter (fun x : Carrier q₀ => ∀ g, (gen g).part q₀ x = a g)).card
  -- (D4) the target-cell map per CONTINUING letter, landing in the TARGET
  -- block's cells "under the SAME global definition" (typed by codomain):
  cont : Letter → Prop
  decCont : DecidablePred cont
  tgtSk : ∀ m, cont m → Skeleton n
  tgt_menu : ∀ m (h : cont m), (letterSp m).isLeft   -- continuing ⟹ species side
```

`BlockData.CellIdx := ∀ g, (gen g).idx` after zero-size deletion (V.2: "cells
with IDENTICALLY-zero size polynomial are deleted once, symbolically" — the
subtype `{a // sizeP a ≠ 0}`). THE TARGET-CELL MAP's cell-level component
(`tcell : ∀ m h, CellIdx → (B' (tgtSk m h)).CellIdx`) is a field of the
GLOBAL family record `CtsFamily` (below), since its codomain needs the target
skeleton's own BlockData — matrix indices type-check BY CONSTRUCTION, "no
species-relative cell ever appears as an index".

```lean
/-- THE TABLE FAMILY over one n: per-skeleton BlockData + the globally-typed
(D4) cell maps + the per-entry count tables (CTS-T). THIS is the record the
SEAM instantiates into MovesS.TableShape (unit V7-3). -/
structure CtsFamily (n : ℕ) where
  bd : ∀ s : Skeleton n, BlockData n s
  tcell : ∀ (s : Skeleton n) (m : (bd s).Letter) (h : (bd s).cont m),
    (bd s).CellIdx → (bd (( bd s).tgtSk m h)).CellIdx
  -- (CTS-T) the tables, with Theorem VAL(a)'s per-entry content as TYPE:
  -- one polynomial, degree ≤ W_loc(m), valued correctly at every prime power
  -- (the count semantics rides the measured side's `tbl_count`, §2.F):
  Wloc : ∀ (s : Skeleton n), (bd s).Letter → ℕ
  Outc : ∀ (s : Skeleton n), (bd s).Letter → Type   -- full outcome labels o
  finO : ∀ s m, Fintype (Outc s m)
  T : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : Outc s m)
    (α : (bd s).CellIdx) (β : TargetIx s m), Polynomial ℚ
  T_deg : ∀ s m o α β, (T s m o α β).natDegree ≤ Wloc s m
  -- TargetIx s m := continuing ⟹ target cells; terminal ⟹ VLabel n
  -- (the absorbing column — rev 4's terminal-final signature, typed once here)
```

[DESIGN NOTE for the audit: `TargetIx s m := if cont m then target cells else
VLabel n` is spelled as a two-constructor inductive in the E-phase file; the
blueprint displays the intent. The OUTCOME label o carries "next-node data +
all hinge-value cells + collision pattern, or a terminal label — the [2a]
L5-case letters"; its Lean carrier is the abstract `Outc` with the V.6 gate
instances pinning concrete rosters (V6 layer), and the FULL per-skeleton
roster is the TABLE-BUILD deliverable — [1v]-COND's CL-13 burden, which this
corpus types but does not globally compute (exactly the note's own perimeter:
"executed in this note ONLY for the three V.6 gate blocks").]

### 2.D Entrance shapes ε (V.1(iii), rev-4 unified typing)

```lean
/-- V.1(iii)'s ENTRANCE SHAPE — "the TRIPLE ε := (P̂, b, σ_sel) of a shallow
CONCRETE §D4-R shape-prefix P̂ — which RETAINS its per-node heights h_r and
its per-read side heights u*_r (§D4-R L3, rev 9) — a designated continuing
branch b entering the size-e block landing in cell β₀, and the
branch-selection record σ_sel (L11's encoding data, lifted into the label)".
P̂ IS MovesD.Shape n (its ShapeRead fields `h`, `ustar` are the retained
heights — the rev-4 F1 unification is BY TYPE: no independent height
parameter exists). Entrances are POST-SPLIT objects: siblings differ in
σ_sel, hence carry DISTINCT ε (V.3(iii)'s post-split typing). -/
structure EntShapeV (n : ℕ) where
  Phat   : MovesD.Shape n
  hne    : (Phat : MovesD.ShapePrefix).reads ≠ []
  gsel   : ℕ                       -- the designated branch's selection (g, μ)
  musel  : ℕ                       --   at the entry read (b's datum)
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  selRec : List ℕ                  -- σ_sel: s_r at every shallow branching
                                   --   cell passed (L11 encoding data)

/-- HEIGHT PROJECTION (rev 4): h_ent(ε) := the tuple of ε's RETAINED height
data — the (h_r, u*_r) pair vector over P̂'s reads. A FUNCTION of ε,
displayed; "one concrete ε FIXES its entrance heights". -/
def EntShapeV.hent {n : ℕ} (ε : EntShapeV n) : List (ℕ × ℚ) :=
  (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))

/-- ledger exponent A(ε) := §D4-R's A(P̂) — "a function of ε since u*_r ∈ P̂";
pool dimension W_ent(ε) := §D4-R's W(P̂) — "height-free, L3 rev 9". -/
noncomputable def EntShapeV.A (ε : EntShapeV n) : ℕ :=
  (ε.Phat : MovesD.ShapePrefix).A' n
def EntShapeV.Went (ε : EntShapeV n) : ℕ := (ε.Phat : MovesD.ShapePrefix).W

/-- The height-forgetting TEMPLATE ε̊ — "SP.1 applied to P̂, selection data
kept". Carrier: the MovesSp species word + the selection data, heights
CLEARED. `spWord` is the SP.1-per-read bridge (unit V3-3's def+law: the fold
of MovesSp.StageLaws along the reads). -/
structure EntTemplate (n : ℕ) where
  word   : List MovesSp.Species
  hne    : word ≠ []
  gsel musel : ℕ
  selRec : List ℕ

def EntShapeV.template {n : ℕ} (ε : EntShapeV n) : EntTemplate n :=
  { word := spWord n (ε.Phat : MovesD.ShapePrefix), hne := …,
    gsel := ε.gsel, musel := ε.musel, selRec := ε.selRec }
```

The template family's FINITENESS ("{ε̊} is FINITE — [2a]/M1 for the
P̂-templates; L5's finite eligible-continuation menus for the σ_sel's") is
unit V3-4, keyed to MovesSp's SP2 finiteness. The INSTANTIATION MAP
`h ↦ ε̊[h]` and its bijection onto {concrete ε with template ε̊} is unit V3-5
(theorem-under-hypotheses: GIVEN XHD-d on the shallow layer supplying H(ε̊)).

### 2.E The marked space and μ̂ (keying to MovesD; the [3t] fence)

```lean
/-- ι_{e,ε,β₀}'s counting-native carrier: the ε-REFINED ENTRANCE INDEX — the
sub-family of Pref(P̂) (MovesD.PrefIdx, D4R.1-SUM's index) cut by the
landing-cell condition on the designated continuing branch (cell data, §D4-R
L5). `lands` is a PARAMETER field with its (D4)-tie: the cut is a CELL
condition, never a height condition (heights ride IN ε). -/
structure EntranceCut (n : ℕ) (ε : EntShapeV n) (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (pol : MovesD.CanonPolicy p F) where
  lands : MovesD.PrefIdx n pol ε.Phat → Prop
  decL  : DecidablePred lands

/-- The MARKED entrance mass at level N, division-free (the MovesC/MovesD
counting idiom): ι·p^{nN} = Σ over the refined index of fiber cards. Each
member is one realized branch prefix η with its Theorem C(b) mass — "ι is
their SUM — a D4R.1-SUM sub-sum, hence a μ̂-object; an f entering twice
carries two marks". The ℝ-valued ι of the seam is `MeasuredSide.ιsh`'s field,
tied to THIS count by V7-4's instantiation. -/
noncomputable def iotaCount {n : ℕ} (ε : EntShapeV n) {p F pol}
    (cut : EntranceCut n ε p F pol) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) : ℕ :=
  ∑ᶠ i ∈ {i | cut.lands i}, Nat.card ↥(S.fiber i)
```

μ̂ FENCE (binding, from MovesS): every aggregate of `iotaCount`-type objects
that leaves this corpus is wrapped in `MovesS.MuHat` (no Add, no coercion) —
"the pairing ι_e^T β_e is the μ̂-typed MARKED-entrance total … NEVER a clause
of the density R_σ". No unit of this corpus states a per-f density.

### 2.F The measured carrier `CtsMeasured` (the intended `MeasuredSide` producer)

```lean
/-- The corpus's measured primitives OVER the level-N boxes: cells and their
events, per-height weights, table-count semantics, entrance events. This is
the FINER carrier from which unit V7-4 produces `MovesS.MeasuredSide` (whose
fields are a projection of these), and over which PART-1/REP/MEAS are stated.
Fields marked [law→unit] carry NO axioms here — their laws are units. -/
structure CtsMeasured (n : ℕ) (C : CtsFamily n) (S : StepSys n) where
  toStepCells : S.Cell ≃ Σ s : Skeleton n, (C.bd s).CellIdx
    -- 𝒞_n := {(s, α)} — the StepSys index IS the state space, typed once
  Pools : Set ℚ
  pools_sub : Pools ⊆ S.Pools
  Box  : ℚ → ℕ → Type                  -- level-N residue boxes (MovesD.Box keyed)
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  -- digit cells of a read from one representative (D4R.0/L5's partition index):
  DCell : ∀ {α β}, S.Move α β → Type
  finD  : ∀ {α β} (m : S.Move α β), Fintype (DCell m)
  DCellT : ∀ {α v}, S.MoveT α v → Type
  finDT : ∀ {α v} (m : S.MoveT α v), Fintype (DCellT m)
  -- fixed-height cell events + masses (counting-native):
  cellEvt : ∀ {α β} (m : S.Move α β), S.Hist α → DCell m → Hpt (S.dim m) →
    ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  μcell : ∀ {α β} (m : S.Move α β), S.Hist α → DCell m → ℚ → ℝ   -- resummed
  -- TABLE-COUNT SEMANTICS ((iv)-POLY's "valued correctly at every prime
  -- power"): the polynomial T's value IS the fresh-assignment count
  -- [law→unit V4-1 consumes it; the field is the TIE, per representative]:
  tbl_count : ∀ (s : Skeleton n) (m o α β) (x : _) (q₀ : ℚ), q₀ ∈ Pools →
    ((C.T s m o α β).eval q₀ : ℚ) = (S.cntraw (moveOf s m o α β) x (…) : ℚ)
  -- [DESIGN FREEDOM, audit round: `moveOf` is the CtsFamily→StepSys move
  -- embedding and the height argument is the h-independent (u-T)-cleared
  -- count; the E-designer states tbl_count at fixed h with the (u-T) field
  -- discharging independence — the blueprint pins the CONTENT: eval = count.]
  activeState : ℚ → S.Cell → Prop     -- |α|(q₀) > 0 (Act_{q₀}'s predicate)
  act_size : ∀ q₀ ∈ Pools, ∀ c : S.Cell, activeState q₀ c ↔
    ((C.bd (toStepCells c).1).sizeP (toStepCells c).2).eval q₀ ≠ 0
  -- entrance side (per concrete ε, β₀):
  entEvt : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)
  ιval : EntShapeV n → S.Cell → ℚ → ℝ
  entCount : EntShapeV n → S.Cell → ℚ → ℕ       -- I^ent_{ε,β₀}(q₀), marked
```

### 2.G Templates, XHD-d/-s, HMC, and the COMP typing (V.1(iv)–(vi), V.4)

```lean
/-- A finite path template γ in block e (V.1(vi)): β₀ →^{m₁,o₁} β₁ → … → β_k,
length ≥ 1, with the rev-4 TERMINAL-FINAL EXTENSION: the final step may carry
a terminal outcome — "there β_k := the absorbing column label [o_k] — an EXIT
OBJECT … the label consumed only as a column index", heights/weight/count
typed as for any read, NO target-cell map consumed. -/
inductive Template (n : ℕ) (S : StepSys n) : S.Cell → Type
  | last  {α β} (m : S.Move α β)  : Template n S α
  | lastT {α v} (m : S.MoveT α v) : Template n S α
  | cons  {α β} (m : S.Move α β) (γ : Template n S β) : Template n S α

def Template.D {n S} : ∀ {α}, Template n S α → ℕ    -- total height dimension
  | _, .last m => S.dim m | _, .lastT m => S.dimT m
  | _, .cons m γ => S.dim m + γ.D

/-- (XHD-d) DOMAINS, typed: per template an EXPLICITLY LISTED pairwise-
disjoint semilinear PARTITION of the EXACT realizable height domain, exact
two-sidedly against the chain count T_γ(x, h):
(no orphan) count > 0 at some representative ⟹ h ∈ H(γ);
(no stray)  h ∈ H(γ) ⟹ count > 0 at EVERY representative. Owner [2b]. -/
structure XHDd (n : ℕ) (S : StepSys n) where
  chain : ∀ {α} (γ : Template n S α), S.Hist α → Hpt γ.D → ℕ
    -- T_γ(x,h) := #{fresh-assignment chains from x realizing (γ, h)} — the
    -- V.0 REALIZABILITY primitive; its tie to per-step cntraw is VAL(b)'s
    -- (XHD-u)-conditional content (unit V2-5), NEVER assumed here
  dom : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  no_orphan : ∀ {α} (γ : Template n S α) (x : S.Hist α) (h : Hpt γ.D),
    0 < chain γ x h → (dom γ).Mem h
  no_stray : ∀ {α} (γ : Template n S α) (h : Hpt γ.D),
    (dom γ).Mem h → ∀ x : S.Hist α, 0 < chain γ x h

/-- (XHD-s) SUMS, typed: per LISTED linear set, the height sum of the weight
product is ONE ℚ(q) element in the note's geometric-denominator class
(MovesS.PolyGeom's `geom_denom_dvd` — denominators ∣ X^b·∏(1 − X^a)),
convergent at every pool evaluation. "By XHD-d's disjointness the finitely
many component sums ADD EXACTLY to the H(γ)-sum" is unit V0-3 + V5-4's
consumption, not a field. Owner [2b]. -/
structure XHDs (n : ℕ) (S : StepSys n) (W : XHDw n S) (D : XHDd n S) where
  Gc : ∀ {α} (γ : Template n S α), Fin (D.dom γ).comps.length → Qq
  Gc_denom : ∀ {α} (γ : Template n S α) (j), ∃ b (as : Finset ℕ+),
    (Gc γ j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))
  Gc_ok : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
    Gc γ j ∈ OKat q₀
  Gc_hasSum : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((D.dom γ).comps.get j).Mem h} =>
        gProd W γ h.1 q₀)                     -- ∏_i g_i(h_i), def below
      ((evalAt q₀ ⟨Gc γ j, Gc_ok γ j q₀ hq⟩ : ℚ) : ℝ)

/-- ∏ᵢ g_i(h_i): the fixed-height template weight (a def over XHDw). -/
noncomputable def gProd {n S} (W : XHDw n S) :
  ∀ {α} (γ : Template n S α), Hpt γ.D → ℚ → ℝ := …

/-- (v) HMC — THE OPEN KERNEL, typed exactly as displayed: "the whole-template
exact domain FACTORS stepwise, each factor depending ONLY on the retained
state β_{i−1} and the step data — never on earlier height choices". Stated as
membership-factorization over the flattening; templates INCLUDE terminal-final
ones (they are `Template` constructors — the rev-4 signature is BY TYPE).
NEVER proved in this corpus; consumed by (COMP-Σ)/V5-5 and V4-12. -/
def HMC {n : ℕ} (S : StepSys n) (D : XHDd n S) : Prop :=
  ∀ {α β} (m : S.Move α β) (γ : Template n S β) (h₁ : Hpt (S.dim m))
    (h₂ : Hpt γ.D),
    (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔
      (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂

/-- (HMC-AUG) — "a SEPARATE named redesign hypothesis, NOT a consequence of
HMC": one round of 𝒞_n refinement by finitely-valued boundary/gap data
restores factorization. Typed as an ∃-refinement Prop over StepSys; never
assumed anywhere in this corpus (ledgered V.5(2)). -/
def HMCAug {n : ℕ} (S : StepSys n) (D : XHDd n S) : Prop := …
```

### 2.H The J tables ((J-RAT)/CL-18's carrier — the PLAN-SYNC deliverable)

```lean
/-- The BRANCHING digit cells of outcome class o at state τ: the digit cells
carrying ≥ 2 eligible continuing marks' worth of continuation, i.e. the
(c ≥ 1, m ≥ 2) rows' cells (the classification is MovesS's; here the cell
SET is data with its roster tie). Each cell ONCE — PART-1's partition index,
NEVER the marked per-continuing-branch T·G (the rev-2/S.0 finding: "a T·G-sum
would multiply-count the cell"). -/
structure JCells (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  bcells : ∀ {α β} (m : S.Move α β), Finset (V.DCell m)
  -- + the roster tie fields (branching ⟺ ≥ 2 eligible (side,ψ) continuations,
  --   §D4-R L5) — typed against MovesD's L5 eligibility carrier at E-phase.

/-- J_{τ,o}(q₀) as a MEASURED value: Σ over the branching cells, EACH ONCE, of
the XHD-resummed conditional cell mass (V.3(iv)'s μcell, resummed). The ℚ(q)
membership — (J-RAT) — is unit V5-7b, GIVEN XHD-s + the cell-count
polynomials; its PolyGeom presentation supplies `MovesS.RatBurdens.jP`. -/
noncomputable def Jval {n C S} {V : CtsMeasured n C S} (J : JCells n C S V)
    {α β} (m : S.Move α β) (x : S.Hist α) (q₀ : ℚ) : ℝ :=
  ∑ c ∈ J.bcells m, V.μcell m x c q₀
```

### 2.I `DefsGate.lean` — the V.6 sealed data (concrete, decide-native)

Concrete data only (no laws): the root roster (five letters with their five
closed-form polynomials `TH3 = C(1/6)·X·(X−1)·(X−2)`, `TH12 = C(1/2)·X²·(X−1)`,
`TH3c = C(1/3)·(X³−X)`, `T21 = X·(X−1)`, `T3 = X`); the A2 entry
(`TA2 = (X−1)²`, domain data `A2dom := LinSet.mk ![4,1] [![3,1], ![2,0]]`,
weight `EA2 : AffineE 2` with eval (h₀,h₂) ↦ (3(h₀+h₂)−1)/2 in the (t,u)
chart = 6t+3u+1); the s_blk2 roster (`Tsplit = C(1/2)·(X−1)·(X−2)`,
`Tinert = C(1/2)·X·(X−1)`, `Tdbl = X−1`, `Tw2 = X−1`, `Tvv = (X−1)²`); the
gate-B constants (A(ε) = 3, W_ent = 3, `Ient = X·(X−1)`, ι = 1/4, T = 1,
g = 1/8, μ̂ = 1/32, shadow = 2, N₀ = 3); the census q-list
`censusQ := [2,3,4,5,7,8,9,11,13]` and its prime sublist
`censusP := [2,3,5,7,11,13]` (see V6-1c's honest scope split).

## §3 The unit DAG — 70 units (32 easy / 33 medium / 5 hard)

Format per campaign §2: id `MovesV.<name>` · file · statement (against §2
Defs) · moves_ref (V-TABLES display, ≤ 3 lines) · deps · sketch · difficulty ·
hypothesis_fields (which open kernels ride — NEVER silently strengthened or
dropped). Units are SHORT: one display, one lemma. Pre-approved splits are
marked ⌿.

### Layer V0 — height apparatus [4]

**V0-1 `affine_pos` · `V0_affine.lean` · easy.**
`theorem affine_strictMono {D} (E : AffineE D) (i : Fin D) : StrictMono (fun t => E.eval (Function.update h i t))`
+ `theorem affine_ge_const : E.const ≤ E.eval h`.
moves_ref: "E affine in h with positive weights" (XHD-w).
deps: Defs. sketch: sum manipulation; `Finset.sum_le_sum`. hyp_fields: none.

**V0-2 `linset_mem_iff` · `V0_linset.lean` · easy.**
Normal-form membership + base membership `L.Mem L.base` (c := 0) + closure
under adding one period. moves_ref: "L(h₀; P) := {h₀ + Σ n_v·v}".
deps: Defs. sketch: definitional; `Fin.sum` lemmas. hyp_fields: none.

**V0-3 `semilin_sum_exact` · `V0_partition.lean` · medium.**
For `S : SemilinPart D`, `f : Hpt D → ℝ` with `0 ≤ f`, and per-component
`HasSum (f ∘ incl_j) (v j)`: `HasSum (f ∘ incl_{S.Mem}) (Σ_j v j)`.
moves_ref: "the finitely many component sums ADD EXACTLY to the H(γ)-sum —
no overlap terms exist (rev 3)". deps: V0-2.
sketch: induction on comps; `HasSum` over a disjoint union of subtypes
(`hasSum_subtype_iff` + disjointness field); nonneg gives summability
transfer. hyp_fields: none (the disjointness is a TYPE field of SemilinPart).

**V0-4 `xhds_instance_A2` · `V0_xhds_witness.lean` · medium ⌿.**
THE NON-DEGENERACY WITNESS for the XHD-s format (doctrine: packages must be
non-degenerately instantiable): over `A2dom` with weight `EA2`,
`HasSum (fun h : {h // A2dom.Mem h} => (q₀:ℝ)^(-(EA2.eval h : ℤ)))
((evalAt q₀ ⟨GA2, _⟩ : ℚ) : ℝ)` for every q₀ > 1, where
`GA2 : Qq := X⁻¹·(X⁻⁶/(1−X⁻⁶))·(1/(1−X⁻³))`-cleared — denominators in the
PolyGeom class. moves_ref: "HEIGHT DOMAIN … the ONE linear set
L((4,1); {(3,1), (2,0)}) … E = (3(h₀+h₂)−1)/2 — affine, positive weights"
(V.6.2). deps: V0-2, V6-2a (the domain chart), V6-2b (E in the chart).
sketch: reparametrize by the (t,u)-chart bijection (V6-2a); E = 6t+3u+1;
product of two geometric series (`tsum_geometric_of_lt_one`, `HasSum.mul`);
match the cleared rational form at eval. ⌿ split: (a) the double geometric
sum; (b) the Qq clearing identity. hyp_fields: none — a PROVED instance.

### Layer V1 — the XHD packages + (U-A) [7]

**V1-1 `xhdw_range` · `V1_xhdw.lean` · easy.**
`theorem xhdw_pos (X : XHDw n S) … : 0 < X.g m h q₀` and `X.g m h q₀ ≤ 1`
at pools (q₀ > 1, E ≥ const… state `0 <` and `≤ q₀^(−E.const)`).
moves_ref: "a FIXED-HEIGHT weight monomial g = q^{−E(h)}".
deps: Defs, V0-1. sketch: `zpow` monotonicity. hyp_fields: consumes XHDw as
an ARGUMENT (owner [2b]); proves only its numeric range.

**V1-2 `xhdu_rect_sum` · `V1_xhdu.lean` · easy.**
GIVEN (u-T)'s constant count: `∑ h ∈ Hfin, (cnt h : ℝ) * g h = (T:ℝ) * ∑ h ∈ Hfin, g h`
when `∀ h ∈ Hfin, cnt h = T`. moves_ref: "Σ_h T(h)·g(h) = T·Σ_h g(h) is
EXACTLY (u-T), else false in general" ((iv) STEP).
deps: Defs. sketch: `Finset.sum_congr` + `mul_sum`. hyp_fields: none (the
premise is the (u-T) instance, explicit).

**V1-2w `xhdu_rect_false` · same file · easy.**
The "else false in general" witness: a concrete `cnt` non-constant on a
two-point H with `Σ cnt·g ≠ cnt(h₀)·Σ g`. moves_ref: same display.
deps: none. sketch: norm_num instance. hyp_fields: none. (Counted with V1-2
as ONE unit id V1-2; the file carries both lemmas.)

**V1-3 `xhdd_exact_supp` · `V1_xhdd.lean` · easy.**
GIVEN XHDd: `(D.dom γ).Mem h ↔ ∀ x, 0 < D.chain γ x h` at inhabited `Hist α`
(both directions from no_orphan/no_stray + `hist_ne`).
moves_ref: "(no orphan) … ⟹ h ∈ H(γ); (no stray) h ∈ H(γ) ⟹ … EVERY
representative". deps: Defs. sketch: unfold; `Nonempty.elim`.
hyp_fields: XHDd argument (owner [2b]).

**V1-4 `xhds_eval_nonneg` · `V1_xhds.lean` · easy.**
GIVEN XHDw/XHDd/XHDs: each `Gc γ j` evaluates ≥ 0 at pools (limit of a
nonneg-term sum via `Gc_hasSum` + V1-1). moves_ref: "convergent at every
prime power evaluation (positive weights)". deps: V1-1.
sketch: `HasSum.nonneg`. hyp_fields: XHDw/XHDd/XHDs arguments.

**V1-5 `xhd_discharge` · `V1_discharge.lean` · easy.**
`def XHD.discharged (X : XHD n S) : Prop := True → …` — NO. Instead:
`def IsFullDischarge (n S) : Prop := Nonempty (XHD n S)` + the RECORD lemma
`theorem cond_of_discharge : IsFullDischarge n S → ∀ {P : XHD n S → Prop}, (∀ X, P X) → ∃ X, P X` —
the [1v]-FULL bookkeeping shape: discharge = INHABITATION of the package,
"no new mathematics"; every measured unit keeps its explicit `XHD` argument.
moves_ref: "[1v]-FULL := the RECORDED DISCHARGE of the XHD hypotheses upon
[2b]'s acceptance — a bookkeeping event" (V.0).
deps: Defs. sketch: trivial. hyp_fields: none (typing unit). [Audit note:
deliberately NOT `True`-valued — inhabitation of the full package is exactly
the event; no unit may replace its XHD argument by this Prop.]

**V1-6 `UA_fixed_history` · `V1_UA.lean` · medium.**
(U-A) AS THE NOTE PROVES IT — this corpus's ONE §C-derivable clause:
`theorem UA (P : C15Pack n S) {α β} (m : S.Move α β) (x : S.Hist α)
(hzc : S.zc x) (h : Hpt (S.dim m)) (a a' : S.Assign m x h) (q₀ ∈ S.Pools) :
S.massOf m x h a q₀ = S.massOf m x h a' q₀`.
moves_ref: "Fix ONE realizable prefix satisfying (ZC) … BOTH factors are
functions of the read's NOMINAL DIGIT INVENTORY … Hence all fresh assignments
realizing (m, o, β) at h FROM THAT PREFIX carry one common conditional
mass. ∎" (V.0 (U-A)). deps: Defs (C15Pack).
sketch: two `mass_factors` rewrites; both sides = `F (invOf m x h) q₀`.
hyp_fields: `C15Pack` (owner §C/HC-2 — the typed C.1.5(1)+TYP(b) supply; the
PROOF is unconditional given the pack, exactly the note's GIVEN).

**V1-7 `ua_split_fence` · `V1_fence.lean` · medium.**
THE HONEST-SPLIT WITNESS: a concrete `StepSys` + `C15Pack` instance whose
(u-R) FAILS: `∃ S P, (C15Pack n S) ∧ ¬ (∀ (m x x' h a a' q₀ …), massOf m x h a q₀ = massOf m x' h a' q₀)`
(two histories, two inventories). moves_ref: "NOT §C-derivable, HYPOTHESIZED
in (XHD-u) (they are lumpability assertions about histories §C never
compares)" (V.0). deps: Defs. sketch: two-history toy model, F distinguishing
inventories; norm_num. hyp_fields: none — a machine-checked record that
(XHD-u) is not a consequence of the pack (the inverse-defect discipline).

### Layer V2 — state space + tables [10]

**V2-1 `skeleton_menu` · `V2_skeleton.lean` · easy.**
`theorem letter_menu_out (B : BlockData n s) (m) : B.letterSp m ∈ MovesSp.Out n s.sp`
(projection) + the n = 3 finiteness tie: skeletons at n = 3 inject into the
53-catalogue (`MovesSp` SP2/SP6 consumption; statement:
`Set.Finite {s : Skeleton 3 | True}` via `SnRaw` finiteness).
moves_ref: "Out(s) := the finite p-INDEPENDENT SYNTACTIC menu … ([2a] SP-OUT
+ M1 bookkeeping ALONE, evaluated over NO residue field)" (CTS-S).
deps: MovesSp.SP2_finThm, Defs. sketch: image of a finite set.
hyp_fields: none — the note's "[2a] pending" inheritance is DISCHARGED
against the PROVED MovesSp (recorded upgrade, §0).

**V2-2 `cellidx_delete` · `V2_cells.lean` · easy.**
`def BlockData.CellIdx (B) := {a : ∀ g, (B.gen g).idx // B.sizeP a ≠ 0}` +
`instance : Fintype B.CellIdx` + the deletion law: deleted cells have empty
fibers at every prime power (`size_count` + eval 0 ⟹ card 0).
moves_ref: "cells with IDENTICALLY-zero size polynomial are deleted from 𝒞_n
once, symbolically" (CTS-S). deps: Defs. sketch: subtype Fintype; card = 0
from ℚ-cast. hyp_fields: none.

**V2-3 `meet_finite_uniform` · `V2_meet.lean` · medium.**
Clause (i)'s proved core: the product-of-generators cell map
`x ↦ (fun g => (B.gen g).part q₀ x)` induces a finite partition of
`Carrier q₀` with p-independent label set `∀ g, idx g`; fibers are pairwise
disjoint and exhaustive; refines EVERY generator.
moves_ref: "the meet of finitely many finite uniform partitions is finite and
uniform, and labels are fixed by (D2)/(D3)'s conventions" (V.3(i)).
deps: V2-2. sketch: fibers of a total map partition the domain; `Fintype.pi`.
hyp_fields: none. [The note's conditionality of clause (i) on the UNCOMPUTED
skeletons is the `BlockData`-per-skeleton ARGUMENT — clause (i) at full depth
is `∀ s, BlockData n s → …`, never "proved by construction" bare.]

**V2-4 `val_a_burden` · `V2_valA.lean` · easy (statement-shape unit).**
`structure ValA (n) (C : CtsFamily n) (V : CtsMeasured n C S) : Prop` with
fields = Theorem VAL(a) verbatim: every entry T ONE polynomial, degree ≤
W_loc(m) (already TYPE via `T_deg`), valued correctly at every prime power
(`tbl_count`-keyed), every cell size ONE polynomial degree ≤ W_state(s)
(`size_deg`/`size_count`-keyed) — the residual FIELD content: the count tie
at every pool for tables and sizes. + `theorem valA_gate : ValA 3 gateFam gateMeas`
DEFERRED to V6 (the three blocks). moves_ref: "(a) LOCAL: every entry
T_{m,o}^{α,β} is ONE polynomial in ℚ[q] of degree ≤ W_loc(m), and every cell
size |α| ONE polynomial of degree ≤ W_state(s), each valued correctly at
every prime power q" (Thm VAL). deps: Defs. sketch: structure decl + gate
pointer. hyp_fields: the count ties are per-skeleton TABLE-BUILD burdens
(CL-13/V.5(4)) — open beyond the V.6 blocks, stated as the structure.

**V2-5 `val_b_chain` · `V2_valB.lean` · medium.**
Theorem VAL(b) GIVEN (XHD-u)'s count face:
`theorem valB (U : XHDu n S) (D : XHDd n S) {α} (γ : Template n S α)
(x : S.Hist α) (h : Hpt γ.D) (hmem : (D.dom γ).Mem h) :
D.chain γ x h = pathProd S γ` where `pathProd` := ∏ᵢ (the h-independent
per-step counts, well-defined by u_R_cnt/u_T). PLUS the unconditional degree
bound `chainCount ≤ q^{W(γ)}` as a separate lemma (per-step pools bound it).
moves_ref: "(b) CHAIN — GIVEN (XHD-u)'s COUNT FACE …: the PER-REPRESENTATIVE
linked count from one fixed source representative EQUALS the PATH PRODUCT
C_γ(q) = ∏ T" (Thm VAL). deps: Defs, V1-2.
sketch: induction on γ; each step's count is state-only by (u-R)+(u-T); the
chain recursion is the `chain`-vs-`cntraw` tie FIELD the E-designer adds to
XHDd (chain (cons m γ) = Σ over step-1 assignments of chain γ — recorded
DESIGN FREEDOM; the note's chain count is defined by exactly that recursion).
hyp_fields: XHDu + XHDd (owner [2b]); "never proved here" — the unit derives
the equality FROM them, matching "hypothesized in (XHD-u), never proved here
(alternative discharge: the table build proves representative-uniform count
rows per species)".

**V2-6 `exp_audit_pow` · `V2_audit.lean` · medium.**
The EXPONENT-MAP AUDIT's worked law: for a finite field F with `|Fˣ| = m`,
the image of `t ↦ t^a` on `Fˣ` has cardinality `m / gcd a m`.
moves_ref: "e.g. the image size of t ↦ t^a on F_{q^g}ˣ is
(q^g − 1)/gcd(a, q^g − 1)" (EXPONENT-MAP AUDIT).
deps: none (Mathlib: `IsCyclic`, `powMonoidHom`, index/range card).
sketch: cyclic Fˣ; image of power map = unique subgroup of order m/gcd.
hyp_fields: none. [The AUDIT as a duty — "each such factor either cancels
against a displayed cell-size factor or splits the cell" — is a FIELD of the
table-build structure `AuditedEntry` in this file: per entry, a proof term
`cancels ⊕ splits`, consumed by V2-4's gate instances.]

**V2-7 `val1_worked` · `V2_val1.lean` · medium.**
The VAL.1 worked instance, stated generically: F a field, `V : Fˣ × Fˣ → F × F`,
`V (A, B) = (A, B)` in the basis coordinates (the note's V(A,B) = Aα + B read
in the basis {α, 1}): the fiber count over t = (x, y) is 1 on
FG = {x ≠ 0 ∧ y ≠ 0}, 0 on FL = {y = 0}, 0 on FS = {x = 0} — c_V constant
per cell. moves_ref: "Worked instance (V(A,B) = Aα + B …): THREE cells — FG
…, c_V = 1; FL …, c_V = 0; FS …, c_V = 0" (VAL.1).
deps: none. sketch: coordinates are literal; fiber = {(x,y)} iff both
nonzero, else empty (A = 0/B = 0 prohibited by Fˣ). hyp_fields: none.

**V2-8 `anchor_twist_fence` · `V2_anchor.lean` · easy (typing unit).**
ANCHOR ALIGNMENT as a TYPE: the (a)-generator constructor of `GenSpec` at
twist `a_eff` partitions the TWISTED target — a def `twistedCells (a_eff)
(t) := cells (α^{−a_eff}·t)` + the fence lemma: at `a_eff = 0` twisted =
fixed-frame. moves_ref: "at anchor exponent a_eff ≠ 0 the cells apply to the
TWISTED target α^{−a_eff}·t, never to t in the fixed frame — fixed-frame cell
counts are PROVABLY char-dependent (the value probe …)" (VAL.1).
deps: Defs. sketch: definitional. hyp_fields: none. [The char-dependence
refutation itself is the Python probe's, cited as evidence — no Lean claim.]

**V2-9 `deg_cons_gate` · `V2_degcons.lean` · easy.**
DEG-CONS at the computed rosters: for the V.6 gate family's outcome rosters,
every m ≥ 2 outcome has per-member sizes e_j ≥ 1 with Σ e_j ≤ e — by
`decide` over the DefsGate lists; PLUS the shape lemma producing
`MovesS.DegCons gateTS` for V7-3. moves_ref: "DEG-CONS … m ≥ 2 children,
each child cluster size e_j ≥ 1, Σ_j e_j ≤ e — per member … The check runs
over the FULL roster of each computed table block" (V.2).
deps: DefsGate. sketch: decide. hyp_fields: none at the gate blocks; the
full-roster check at other skeletons is CL-11's burden (typed as the ValA-
style structure field, open).

**V2-10 `wloc_wstate_split` · `V2_bounds.lean` · easy.**
The SPLIT-bound fence: a lemma family showing the gate data satisfy
`(sizeP α).natDegree ≤ Wstate s` AND an explicit instance where
`Wstate s > Wloc m` is CONSISTENT (the note's "a source-cell size belongs to
(s, α), not to any outgoing m, and may exceed some W_loc(m)") — the s_blk2
data (Wstate = 1, some W_loc = 2, and the root: Wstate = 0 < Wloc = 3).
moves_ref: "(SPLIT bounds — a source-cell size belongs to (s, α), not to any
outgoing m)" ((iv)-POLY). deps: DefsGate. sketch: norm_num.
hyp_fields: none.

### Layer V3 — entrance shapes + clause (iii) [11]

**V3-1 `entshape_postsplit` · `V3_eps.lean` · easy.**
POST-SPLIT TYPING "proved by construction": two `EntShapeV` differing in
`selRec` are ≠ (injectivity of the label in the σ_sel coordinate); siblings
at a shallow split carry DISTINCT ε. moves_ref: "siblings at a shallow split
differ in s_r, hence carry DISTINCT ε — ι never aggregates a pre-split
f-event or a joint-sibling locus" (V.3(iii)). deps: Defs.
sketch: structure injectivity. hyp_fields: none.

**V3-2 `hent_proj` · `V3_hent.lean` · easy.**
h_ent is a PROJECTION: `hent` is a function of ε (definitional), determined
by `Phat` alone; + the non-degeneracy law: two ε with same template but
different read-heights have different `hent` (heights are RETAINED, not
quotiented). moves_ref: "h_ent(ε) := the tuple of ε's RETAINED height data —
… a FUNCTION of ε, displayed, no free height variable anywhere" (V.1(iii)).
deps: Defs. sketch: `List.map` congruence + a two-read discriminating
instance. hyp_fields: none.

**V3-3 `spword_bridge` · `V3_spword.lean` · medium.**
The SP.1-per-read bridge: `def spWord (n) (P : MovesD.ShapePrefix) :
List MovesSp.Species` (fold of the stage laws along `P.reads`) + its law:
consecutive outputs satisfy `MovesSp.StageLaws` when the reads satisfy
MovesD's `ShapeWF` stage clauses. moves_ref: "ε̊ := ε's height-forgetting
TEMPLATE (SP.1 applied to P̂, selection data kept)" (V.1(iii)).
deps: MovesD.Defs, MovesSp.Defs. sketch: structural recursion over reads;
match `ShapeRead` fields (e, g, μ, species tags) to `Species` stage fields
via the D.5/D.7/D.8 output laws both corpora carry. hyp_fields: the ShapeWF
certificate (MovesD's, PROVED apparatus) — no open kernel.

**V3-4 `template_finite` · `V3_tfin.lean` · medium.**
Per (e, β₀) and bounded shallow depth, the template family is FINITE:
`Set.Finite {ε̊ : EntTemplate n | WordBounded n ε̊}` — words in the catalogue
(V3-3's bridge lands in `SnRaw n`, finite by SP2), selections in L5's finite
menus (bounded lists over finite data). moves_ref: "the family {ε̊} is FINITE
([2a]/M1 for the P̂-templates; L5's finite eligible-continuation menus for
the σ_sel's)" (V.1(iii)). deps: V3-3, MovesSp.SP2_finThm.
sketch: finite words of bounded length over a finite alphabet.
hyp_fields: the depth bound is the SHALLOW-layer scope (entrance prefixes are
shallow BY the [3t] cut — carried as the `WordBounded` premise, owner [3t]'s
cut vocabulary, typed here as a bound argument).

**V3-5 `inst_bijection` · `V3_instbij.lean` · HARD.**
The rev-4 INSTANTIATION BIJECTION, GIVEN XHD-d on the shallow layer:
`theorem inst_bij (D : XHDdSh n) (ε̊ : EntTemplate n) :
∃ e : {h // (D.entDom ε̊).Mem h} ≃ {ε : EntShapeV n // ε.template = ε̊ ∧ Realizable ε},
∀ h, (e h).1.hent = writeHeights ε̊ h` — "write the heights h into the
template's retained slots" is a BIJECTION from H(ε̊) onto the concrete
realizable ε with that template. moves_ref: "the INSTANTIATION MAP h ↦ ε̊[h]
… is a BIJECTION from H(ε̊) onto {concrete ε with template ε̊} — D4R.1-SUM is
cited ONLY at concrete ε" (V.1(iii), pass-3 F1's two horns).
deps: V3-3, V3-4, Defs (XHDdSh := XHDd at the entrance-template layer).
sketch: injectivity = heights determine the reads' (h, u*) slots given the
template (V3-2); surjectivity = no-stray realizability + template-matching;
the `Realizable` predicate is XHD-d's chain-count positivity at the shallow
layer. ⌿ pre-approved split: (a) injectivity; (b) surjectivity; (c) the
hent-computation law. hyp_fields: XHD-d shallow (owner [2b]).

**V3-6 `iota_muhat` · `V3_iota.lean` · medium.**
ι's typing laws: `iotaCount` is a SUB-SUM of D4R.1-SUM's index — i.e.
`iotaCount ε cut S ≤ Σᶠ i, Nat.card (S.fiber i)` with equality iff `lands`
is total; and the D4R.1-SUM tie at stabilized levels: each summand's fiber
card × p^{A'} = p^{nN} (MovesD.thmC_top via D10's `key`).
moves_ref: "ι_{e,ε,β₀}(p) := the D4R.1-SUM MARKED mass μ̂ of the entrance
family refined by ε (each summand Theorem C(b); an f entering twice carries
two marks — a μ̂-object, never an f-event mass)" (V.1(iii)).
deps: MovesD.D10_sumLaw, Defs 2.E. sketch: `finsum` over a subset ≤ total;
per-summand D10.key. hyp_fields: `S.jet` (MovesD's presented-jet field, as in
D10); the `lands` cut (§D4-R L5 cell data — a parameter with its (D4)-tie).

**V3-7 `ent_agg_finite` · `V3_aggfin.lean` · medium.**
ENT-AGG's hypothesis-free half: for FINITELY many pairwise-distinct concrete
ε (distinct marked pairs), the refined counts ADD:
`iotaCount` over a disjoint union of cuts = Σ of `iotaCount`s
(μ̂-additivity over disjoint mark families).
moves_ref: "The primitives and every FINITE partial sum are hypothesis-free
(μ̂-additivity over disjoint mark families — distinct concrete ε give
distinct marked pairs)" (V.1(iii)). deps: V3-6, V3-1.
sketch: `finsum_mem_union` on disjoint index sets. hyp_fields: none.

**V3-8 `ent_agg_full` · `V3_aggfull.lean` · easy.**
The FULL aggregate GIVEN XHD-s (shallow): the ℝ-valued
`ιval e β₀ = Σ_{ε̊} Σ_{h ∈ H(ε̊)} ιsh (ε̊[h]) β₀` as a `HasSum` statement over
the instantiation index — entrance heights summed HERE and nowhere else, each
concrete ε hit EXACTLY ONCE (via V3-5's bijection).
moves_ref: "ι_{e,β₀} := Σ_{ε̊} Σ_{h ∈ H(ε̊)} ι_{e,ε̊[h],β₀} … CONVERGENCE of
the full aggregate … is GIVEN XHD-s on the shallow layer" (ENT-AGG).
deps: V3-5, V3-7, V0-3. sketch: reindex by the bijection; component sums by
XHD-s; finite outer sum (V3-4). hyp_fields: XHD-s shallow (owner [2b]);
(iv)-REP invoked NOWHERE (the note: "never for the sum's definition").

**V3-9a `ent_count_stmt` · `V3_entcount.lean` · easy (statement unit).**
ENT-COUNT as the NAMED BURDEN, typed: `def EntCount (V : CtsMeasured …) : Prop :=
∀ ε β₀, ∃ P : Polynomial ℚ, P.natDegree ≤ ε.Went ∧ ∀ q₀ ∈ V.Pools,
(P.eval q₀ : ℚ) = V.entCount ε β₀ q₀` + the displayed FENCE lemma:
`I^ent = |β₀|` is NOT assumed (no field ties them; the gate exhibits
I^ent = q·|β₀| ≠ |β₀| — V6-4a). moves_ref: "ENT-COUNT (named burden): each
I^ent_{ε,β₀} is one polynomial in q of degree ≤ W_ent(ε) … I^ent = |β₀| is
NOT general — a per-family theorem, displayed wherever used" (V.1(iii)).
deps: Defs. sketch: def + gate pointer. hyp_fields: ENT-COUNT itself (owner
[1v], open — THIS corpus's burden, V.5(3)).

**V3-9b `ent_u_stmt` · `V3_entu.lean` · easy (statement unit).**
(ENT-U), typed: over each listed component c of H(ε̊), the count polynomial
across instantiations is ONE polynomial CONSTANT in h on c:
`def EntU … : Prop := ∀ ε̊ (c ∈ comps), ∃ P, ∀ h ∈ c, IentP (ε̊[h]) = P`.
moves_ref: "(ENT-U) …: over each listed linear set c of H(ε̊) …, I^ent,
viewed across the instantiations ε̊[h] with h ∈ c, is ONE polynomial CONSTANT
in h on c — [2b] M4b's h_ent-constancy clause, never assumed here" (V.3(iii)).
deps: Defs, V3-5. sketch: def. hyp_fields: (ENT-U) (owner [2b] M4b).

**V3-9c `init_rat` · `V3_initrat.lean` · medium.**
INIT-RAT, theorem-under-hypotheses:
`theorem initRat (hXs : XHDsSh …) (hEU : EntU …) (hEC : EntCount …)
(hA : AffEnt …) : ∀ e (τ : …), ∃ P : PolyGeom, ∀ q₀ ∈ Pools,
((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ) = V.ιval e τ q₀` — the displayed assembly
ι = Σ_{ε̊} Σ_{c} I^ent_c(q)·Σ_{h∈c} q^{−A(ε̊[h])}, inner sums XHD-s
geometric, outer finite; A affine in h across instantiations (`AffEnt`, the
[2b] M4a face, typed). moves_ref: "INIT-RAT (BURDEN, GIVEN XHD on the shallow
layer + (ENT-U)): ι_{e,(s,α)} = Σ_{ε̊} Σ_{c ⊆ H(ε̊)} I^ent_c(q)·Σ_{h∈c}
p^{−A(ε̊[h])} … hence ∈ ℚ(q); CITED by RS.2" (V.3(iii)).
deps: V3-8, V3-9a, V3-9b, V0-3, V0-4 (the witness pattern).
sketch: per component: constant I^ent_c times a geometric Qq (XHD-s);
finitely many components and templates; PolyGeom closure under + and scalar
(the E-designer adds the closure mini-lemmas or lands the sum in `Qq` with
`OKat` membership — DESIGN FREEDOM recorded). hyp_fields: XHD-s shallow +
(ENT-U) + ENT-COUNT + M4a's affine-A face — EXACTLY the V.1 ledger line
"INIT-RAT GIVEN XHD (shallow) + (ENT-U)"; supplies `RatBurdens.ιP/ι_interp`.

### Layer V4 — clauses (ii), (iv), (v) [12]

**V4-1 `act_no_entry` · `V4_act.lean` · medium.**
(ii-a) NO-ENTRY, GIVEN (iv)-POLY's correct valuation (the `tbl_count` +
`size_count` fields): at q₀ with `(sizeP β).eval q₀ = 0`, every table entry
INTO β evaluates to 0 there, and ι is supported on Act:
`theorem no_entry … : ¬ V.activeState q₀ β → (C.T s m o α βc).eval q₀ = 0`
+ `theorem iota_supp : ¬ V.activeState q₀ β₀ → V.ιval ε β₀ q₀ = 0`.
moves_ref: "(ii-a) NO-ENTRY — for every source active at q₀, every
table/kernel entry INTO a target inactive at q₀ evaluates to 0 there (a
landing forces a concrete target state), and ι of (iii) is supported on
Act_{q₀}" (V.1(ii)). deps: Defs (tbl_count, act_size).
sketch: the count lands ON a concrete target state; card of an empty carrier
fiber is 0; cast. The E-designer adds the `lands_in` field to CtsMeasured
(assignments realizing (m,o,β) map into β's fiber — the "landing forces a
concrete target state" tie); recorded DESIGN FREEDOM.
hyp_fields: (iv)-POLY's count ties (table-build burden beyond the gate
blocks) — the unit is GIVEN them per the V.1 ledger "(ii-a/b) GIVEN
(iv)-POLY's correct valuation".

**V4-2 `act_triangular` · `V4_tri.lean` · medium.**
(ii-b): ordering states active-first, the evaluated kernel matrix at q₀ is
block-triangular `[[A, 0], [C, D]]` — every active-source → inactive-target
entry vanishes (V4-1): stated on `MovesS.Kmat` at evaluation, matching
`MovesS.PoolHyp.inactive_vanish`'s shape. NO stochastic-chain reading: rows
are marked offspring rows ("chain" struck at rev 2) — the lemma is about
matrix zeros only. moves_ref: "(ii-b) DELETION COMPATIBILITY — ordering
states active-first, K_e(q₀) is block-triangular [[A, 0],[C, D]]: the
realized system at q₀ IS the A-block" (V.1(ii)). deps: V4-1, MovesS.Defs.
sketch: entry-wise from V4-1 through Kmat's dite sum. hyp_fields: same as
V4-1.

**V4-3 `act_agreement_stmt` · `V4_agree.lean` · easy (statement unit).**
(ii-c) ACTIVE-VALUE as the typed per-(n, q₀) check — the Prop this corpus
RECORDS, never proves: `def ActiveValueAgree … : Prop := ∀ q₀ ∈ finitely
many empty-cell pools, AVAgree-shaped agreement after cancellation` — stated
via `MovesS.AVAgree` at the instantiated PoolHyp; removability of
det(I − D)(q₀) = 0 carried as the OKat membership hypothesis (MovesS's
"(ii-c) PASS" gate shape, verbatim consumption). moves_ref: "(ii-c)
ACTIVE-VALUE — … the burden is AGREEMENT: at the finitely many q₀ with empty
cells, the symbolic ℚ(q)-solution's value component, after cancellation,
EVALUATES to the active-subsystem value" (V.1(ii)).
deps: MovesS.Interfaces, V7-4. sketch: def only. hyp_fields: (ii-c) itself —
"a finite per-(n, q₀) verification duty … exercised by RESUM-n3's wild-p
layer ([3]'s gate), recorded here as the clause's standing check, never a
blanket det ≠ 0 claim" (V.3(ii), finding 8: NO general theorem claimed).

**V4-4 `kernel_row_hfree` · `V4_krow.lean` · easy.**
K_e's entrance-height-freeness BY TYPE + the no-division fence: the entry def
`Σ_{m,o} T·G` consumes no `hent` argument (a definitional lemma: the entry
function factors through (α, β) only) and no source-mass denominator (its Qq
numerator is a product, never a quotient by |α| — checked on the def's
shape). moves_ref: "K_e(q)_{(s,α),(s′,β)} := Σ_{m: s→s′} Σ_o T·G — NO
source-mass division … K_e is entrance-height-FREE: entrance heights ride in
ε (retained data, rev 4), hence in ι alone" (V.1(iv)).
deps: Defs, MovesS.Kmat. sketch: definitional. hyp_fields: none.

**V4-5 `step_row_eq` · `V4_step.lean` · medium.**
The (iv) STEP display, GIVEN (U-A) + (XHD-u):
`theorem step_row (P : C15Pack) (U : XHDu) (D : XHDd) (Xs : XHDs) … :
HasSum (fun h : dom₁ => (S.cntraw m x h : ℝ) * X.g m h q₀)
((T : ℝ) * G)` — the height-resolved row Σ T(h)·g(h) equals T·G: (U-A) makes
g one constant per (m,o,β,h) at the fixed history, (u-R) makes constant and
count state-only, (u-T) makes T(h) = T; each g-summand ALREADY conditional
(no re-division — the statement has no |α| factor).
moves_ref: "UNIFORMITY CONSUMPTION, displayed at the product (rev 2 —
findings 2–3: T·G is NOT licit from XHD-w/d alone): the height-resolved row
is Σ_{h} T(h)·g(h) … = T·Σ_h g(h) is EXACTLY (u-T)" (V.1(iv)).
deps: V1-6, V1-2, V1-1, Defs. sketch: pointwise congr to constant count;
`HasSum.mul_left`; G := the length-1 XHD-s value. hyp_fields: (U-A)'s pack +
XHD-u + XHD-d/s — VERBATIM the ledger "(iv) measured faces GIVEN XHD-w +
(U-A) + (XHD-u); resummed forms also GIVEN XHD-d/s".

**V4-6 `part1_route` · `V4_part1.lean` · HARD.**
PART-1 by the rev-3 countable route, theorem-under-hypotheses with the FOUR
displayed legs as typed premises:
`theorem part1 (leg_a : Totality …) (leg_b : CtblAdd …) (leg_c : NullRem …)
(leg_d : FixedHeightExact …) : ∀ e τ x q₀ ∈ Pools, activeState q₀ τ →
HasSum (fun ch : Σ c : DCellAll τ, {h // h ∈ HDom c} => μcellH … ) 1`
— legs: (a) TOTALITY: outside the no-finite-height locus every source point
lies in exactly ONE digit cell (D4R.0 — keyed to MovesD's d4r0 apparatus);
(b) COUNTABLE ADDITIVITY of the conditional measure over this countable
partition; (c) NULL REMAINDER: the no-finite-height locus lies in the
decreasing intersection of height-≥-H strip cylinders with conditional
masses → 0 (typed: `Tendsto (stripMass H) atTop (nhds 0)`); (d) each
fixed-height block sums by C.1.5(1)'s conditional exactness.
moves_ref: "PART-1's route, displayed: (a) TOTALITY … (b) COUNTABLE
ADDITIVITY … (c) NULL REMAINDER … (d) each fixed-height block sums by
C.1.5(1)'s conditional exactness — together, the per-cell ratios over the
whole partition sum to 1" (V.3(iv), pass-2 finding 4: "mass 1 is NOT a
finite-pool identity"). deps: Defs, V0-3.
sketch: (d) gives per-(c,h) masses; (a)+(b) give the countable HasSum to the
total minus remainder; (c) kills the remainder; assemble by
`HasSum.of_nat_of_sum_le`-style monotone limits on nonneg terms. ⌿
pre-approved split: (i) the countable-partition HasSum from legs a/b/d;
(ii) the remainder-null limit from leg c; (iii) assembly.
hyp_fields: the four legs VERBATIM (the ledger: "PART-1 additionally GIVEN
D4R.0 totality + countable additivity + the null no-finite-height remainder"
+ XHD-w's (U-A) face at fixed history + XHD-d/s); leg (a)'s D4R.0 cite keys
to MovesD (PROVED core) at the shape layer but stays a premise HERE because
the CTS digit-cell carrier is abstract until V7-4.

**V4-7 `part2_row` · `V4_part2.lean` · medium.**
PART-2, the marked offspring row: GIVEN PART-1's conclusion + the mark-count
data (each cell's eligible continuing marks, `emult : DCell → ℕ`):
`Σ_{m,o,β} T·G + terminal = 1 + surplus` with
`surplus := Σ_cells (emult c − 1)⁺·mass c ≥ 0` — the marked row counts each
branching cell once PER eligible continuing mark; NO substochasticity of THIS
row is stated anywhere (the lemma's conclusion is the equality, and a
separate lemma `part2_ge`: row sum ≥ 1 − terminal).
moves_ref: "(PART-2, the marked offspring row) the kernel row Σ T·G counts
each branching cell once PER eligible continuing mark, so Σ T·G + (terminal)
= 1 + (branch surplus) … possibly > 1: NO substochasticity is claimed"
(V.1(iv)). deps: V4-6, Defs. sketch: regroup the marked sum by cells;
emult-weighted count vs once-per-cell count. hyp_fields: PART-1's set +
the emult roster tie (§D4-R L5's multi-eligible cells — MovesD-keyed field).

**V4-8 `part2_n3_zero` · `V4_n3surplus.lean` · easy.**
At n = 3 the surplus vanishes IDENTICALLY: no digit cell carries two
continuing marks — two continuing clusters need sizes ≥ 2 + 2 > 3. Stated
over the gate rosters: `∀ cells in the V.6 rosters, emult ≤ 1` by `decide`;
+ the degree argument as an omega lemma over DEG-CONS data (2 + 2 > 3).
moves_ref: "(At n = 3 the surplus vanishes identically — two continuing
clusters need sizes ≥ 2 + 2 > 3 … first possible surplus at n = 4. Verified
over the V.6 rosters.)" (V.1(iv)). deps: V2-9, DefsGate.
sketch: decide + omega. hyp_fields: none.

**V4-9 `rep_indep` · `V4_rep.lean` · medium.**
(iv)-REP GIVEN (U-A) + (u-R), as the checkable row-level clause:
`theorem rep_row (P : C15Pack) (U : XHDu) (hobs : ObsCheck s m) :
∀ (x x' : reps of α) …, measuredRow x = measuredRow x'` — the WEIGHTED
(T·G)-row, not the cardinality row; `ObsCheck` = the PER-SPECIES proviso
("the species' evaluation maps mention no observable outside the (a)/(b)
generator list"), a typed per-species field executed at the gate blocks
(V6-3a's (D2)-EMPTY check) and OPEN elsewhere.
moves_ref: "(iv)-REP … the measured row from x ∈ α is a function of (a) x's
twisted VAL.1 cell data and (b) x's relational strata … the row is
cell-constant PROVIDED the species' evaluation maps mention no observable
outside the (a)/(b) generator list. That proviso is a PER-SPECIES CHECK"
(V.3(iv)). deps: V4-5, V1-6. sketch: row entries via u_R_mass/u_R_cnt +
ObsCheck's factoring. hyp_fields: (U-A) pack + (XHD-u)(u-R) + ObsCheck (the
table-build per-species check; refuter JOINT-probe is Python evidence,
cited not claimed).

**V4-10 `meas_marked` · `V4_meas.lean` · medium.**
(iv)-MEAS in the RETYPED (rev 3) marked-space form: each (m, o, β,
height-class) summand is a finite-level digit-cell union WITH the
continuation mark ADJOINED — a fiber of a finite-level map ON the marked
space; summands pairwise disjoint IN THE MARKED SPACE; as f-events only the
DIGIT CELLS are disjoint (and two summands' f-projections CAN be equal —
stated as: disjointness is claimed on Σ-marked carriers only, plus an
explicit two-continuation instance where f-projections coincide, keyed to
D4-R L5). moves_ref: "the summands are pairwise disjoint IN THE MARKED
SPACE; as f-events only the DIGIT CELLS are disjoint. No ordinary-source
disjointness is claimed anywhere" (V.1(iv), pass-2 finding 2).
deps: Defs 2.E/2.F, MovesD (L12/D4R.4 finite-level realization).
sketch: the marked event's carrier is `Σ (cell × mark)`; disjointness from
the mark coordinate; the equal-projection witness from L5's two eligible
(side, ψ) continuations. hyp_fields: XHD-d (height classes listed); the L5
eligibility roster (MovesD-keyed field).

**V4-11 `hmc_typing` · `V4_hmc.lean` · easy (typing unit).**
The HMC/HMCAug Prop shapes compile against a NON-degenerate instance: a toy
StepSys with a 2-step template where `HMC` is FALSE (a coupled domain) and a
refined one where it holds — the kernel is a real hypothesis, not a
tautology; + the terminal-final signature check: `Template.lastT` instances
type against `HMC`'s quantifier (the probe's step 2 is a literal instance BY
TYPE). moves_ref: "(v) HMC — … OPEN KERNEL, displayed hypothesis … TERMINAL-
FINAL EXTENSION (rev 4 …): templates INCLUDE those whose FINAL step carries a
terminal outcome" (V.1(v)). deps: Defs 2.G. sketch: two decide-scale toy
models. hyp_fields: none proved ABOUT the CTS instance; HMC itself OPEN
(V.5(2)) — "until HMC closes, K_e(p)^k is NOT a theorem about the process".

**V4-12 `comp_naming_iff` · `V4_naming.lean` · medium.**
The naming-discipline IFF (finding 11): for nonneg weights with per-step
XHD-s sums, `(Σ_{h∈H(γ)} ∏ g_i(h_i)) = ∏ G_i` for ALL fixed weight systems
of XHD-w's monomial form IFF the membership factorization `HMC` holds at γ
(⟸ Fubini/`HasSum.mul_eq`; ⟹ contrapositive: a missing/extra height tuple
changes a strictly-positive sum — positivity from V1-1).
moves_ref: "The right side factors into ∏(T·G), i.e. (COMP-hΣ) upgrades to
(COMP-Σ), IF AND ONLY IF the whole-template domain factors stepwise with
state-only dependence — exactly (v) HMC" (V.4).
deps: V0-3, V1-1, Defs 2.G. sketch: product of HasSums over a product set vs
the actual domain; strict positivity separates. hyp_fields: XHD-w/-d/-s (the
weights and sums quantified over — hypotheses of the iff, owner [2b]).

### Layer V5 — COMP + the J tables [9]

**V5-1 `marked_event_census` · `V5_event.lean` · medium.**
The (vi) marked event, typed over 2.E/2.F: its MARK-INDEX family is FINITE
per level and its level-N residue census is finite (keyed to MovesD.D4R4_all
at the entrance layer + the finite step data); the f-fibers are boxes,
GENERALLY INFINITE — typed by the carrier: the event is a Finset of
(box-point, mark) pairs at each level, NEVER a Finset of f's; + the census
lemma: card = Σ over marks of fiber cards.
moves_ref: "its MARK-INDEX family (the realized histories η) is FINITE per
level and its level-N residue census is finite (D4R.4); the f-fibers are
p-adic boxes, generally INFINITE (rev 2, finding 13 — never 'finitely many
f')" (V.1(vi)). deps: Defs 2.E/2.F, MovesD.D4R4all_wrapper, V3-6.
sketch: Fintype instances + double counting (MovesD.mult_sum's idiom).
hyp_fields: none beyond MovesD's proved apparatus.

**V5-2 `comp_h` · `V5_comph.lean` · HARD.**
(COMP-h), GIVEN (U-A)'s pack + (XHD-u), ε concrete and h FIXED:
`theorem comp_h … : μ̂N (markedEvent ε γ h) q₀ N
= ιN ε β₀ q₀ N * ∏ i, (T_i * g_i(h_i)) — in the counting-native form:
(markedEvent …).card * (normalization) = iotaCount … * ∏ (cnt · q₀^{−E})`
(exact at stabilized levels, the MovesC idiom).
moves_ref: "(COMP-h) at every concrete ε and fixed h ∈ H(γ): μ̂(marked event
of (ε, γ, h) at p) = ι_{e,ε,β₀}(p) · ∏_{i=1}^k [T·g](p)" + the V.4 route
"Group the marked event by its entrance prefix … Per entrance mark, the
continuation mass along γ at h is the C.1.5 conditional chain".
deps: V5-1, V1-6, V4-5, V3-6. sketch: group by entrance mark (V5-1's census);
per mark, induct along γ: each step contributes cnt·g by (U-A) at the fixed
history + (u-R) across the histories reaching βᵢ; multiply out. ⌿
pre-approved split: (a) the one-step case; (b) the induction step; (c) the
grouping identity. hyp_fields: (U-A) pack (§C/HC-2) + (XHD-u) (owner [2b]) —
VERBATIM V.4's GIVEN; "at a FIXED path height point AND one fixed entrance
history, the identity consumes only (U-A)'s §C-derivable content" is the
V6-4 gate's per-history face.

**V5-3 `comp_h_count` · `V5_shadow.lean` · medium.**
The COUNT SHADOW: `Ĉ_{ε,γ}(q) = I^ent_{ε,β₀}(q)·C_γ(q)` at the same concrete
ε — the same grouping at the count layer, GIVEN VAL(b)'s (XHD-u) count face +
ENT-COUNT; degree ≤ W̄(ε,γ) = W_ent(ε) + W(γ); + the FENCES as typed
non-lemmas: never |β₀| without the displayed per-family theorem, never summed
raw across ε with different A(ε) (the aggregation lemma V5-6 takes masses
ONLY). moves_ref: "the FULL realization count is PER (concrete) ENTRANCE
SHAPE: Ĉ_{ε,γ}(q) = I^ent_{ε,β₀}(q)·C_γ(q) (same (XHD-u) tag, plus
ENT-COUNT), degree ≤ W̄(ε,γ) = W_ent(ε) + W(γ) — the entrance factor never
omitted" (Thm VAL(b)). deps: V2-5, V3-9a, V5-2's grouping.
sketch: count-layer replay of V5-2. hyp_fields: (XHD-u) + ENT-COUNT.

**V5-4 `comp_hsum` · `V5_comphs.lean` · medium.**
(COMP-hΣ), GIVEN XHD-d/s, NO HMC: `HasSum (fun h : {h // (dom γ).Mem h} =>
μ̂(ε, γ, h) q₀) (ι_{e,ε,β₀} q₀ * Σ_{h∈H(γ)} ∏ (T·g(h_i)))` — the unfactored
per-template series, well-defined via V0-3 over the listed disjoint
components. moves_ref: "(COMP-hΣ) GIVEN XHD-d/s, NO HMC (rev 2, finding 11
— the unfactored height sum carries its OWN name)" (V.1(vi)).
deps: V5-2, V0-3, V1-4. sketch: sum V5-2 over h; `HasSum.mul_left`.
hyp_fields: XHD-d/s + V5-2's set.

**V5-5 `comp_sigma` · `V5_compsig.lean` · easy.**
(COMP-Σ), GIVEN additionally HMC: the V5-4 value factors to
`ι · ∏ (T·G)_i` — by V4-12's ⟸ direction. moves_ref: "(COMP-Σ) GIVEN
additionally (v) HMC — the factored form" (V.1(vi)).
deps: V5-4, V4-12. sketch: rewrite. hyp_fields: + HMC (OPEN kernel; the tag
rides — every consumer of this unit carries `hHMC`).

**V5-6 `comp_agg` · `V5_compagg.lean` · medium.**
(COMP-AGG), GIVEN (COMP-Σ) + (iii) + (iv)-REP: summing over instantiations
ε̊[h] (the V3-5 bijection) then templates (V3-4 finite):
`Σ_{ε̊} Σ_{h∈H(ε̊)} (COMP-Σ at ε̊[h]) = ι_{e,β₀} · ∏ (T·G)` — entrance
heights EXACTLY ONCE; the common continuation factor pulled out by (iv)-REP
(the ONLY site invoking it, per ENT-AGG's fence); counts do NOT aggregate
(no count analogue stated — distinct A(ε)).
moves_ref: "(COMP-AGG) summing (COMP-Σ) over entrance heights (via the
instantiation bijection) then over templates ε̊ via ENT-AGG (licit by
(iv)-REP): … = ι_{e,β₀} · ∏ (T·G) — masses aggregate, counts do NOT"
(V.1(vi)). deps: V5-5, V3-8, V4-9, V3-5.
sketch: factor the constant continuation out of the double sum; ENT-AGG.
hyp_fields: HMC + XHD set + (iv)-REP's set (union of the deps' ledgers —
displayed in the theorem's signature, nothing implicit).

**V5-7a `jcells_once` · `V5_jdef.lean` · easy.**
J's defining laws: `Jval` sums EACH CELL ONCE (a `Finset.sum` over `bcells`,
no mark index — definitional lemma: `Jval` factors through the cell SET);
+ the branching-roster tie at the gate blocks: `bcells` at n = 3 rosters =
the (c ≥ 1, m ≥ 2) outcome cells by `decide`.
moves_ref: "J_{τ,o}(q) := the CELL-LEVEL resummed branching mass — the sum,
over the branching digit CELLS of outcome class o at state τ, of the
XHD-resummed conditional cell mass …, EACH CELL ONCE" (§S-RESUM S.0, the
CL-18 display; owner-side record per the PLAN-SYNC flag).
deps: Defs 2.H, DefsGate. sketch: definitional + decide.
hyp_fields: none (def-layer).

**V5-7b `j_rat` · `V5_jrat.lean` · medium.**
(J-RAT) = CL-18, the deliverable: GIVEN XHD-s + the per-cell count
polynomials (the (iv)-POLY pattern at cell level):
`theorem jRat (hXs : XHDs …) (hcell : CellPolyPack …) : ∀ (m : S.Move α β)
(o …), ∃ P : MovesS.PolyGeom, P.degBoundT = Wloc ∧ P.degBoundS = Wstate ∧
∀ q₀ ∈ Pools (x), ((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ) = Jval J m x q₀`
— J_{τ,o} ∈ ℚ(q) ENTRYWISE, "a deliverable BEYOND PART-1's TOTAL
cell-partition mass". moves_ref: "its ℚ(q)-membership is the NEW NAMED
burden (J-RAT) (owner [1v]/[2b]: cell-level counts polynomial per the
(iv)-POLY pattern, XHD-s height sums)" (S.0/CL-18).
deps: V5-7a, V0-3, V1-4. sketch: per cell: count polynomial × XHD-s
geometric value; finite cell sum; PolyGeom assembly (V3-9c's closure
pattern). hyp_fields: XHD-s ([2b]'s height-sum face) + `CellPolyPack` (the
per-cell count polynomials — [1v]'s own OPEN face beyond the gate blocks;
at the gate blocks discharged by V6 data). SUPPLIES `MovesS.RatBurdens.jP/
j_ok/j_interp/j_degT/j_degS` (seam row S-J, §4).

**V5-7c `j_not_marked_tg` · `V5_jfence.lean` · easy.**
THE J-FENCE, machine-checked: on any roster with a multi-eligible cell
(emult c = 2), the marked row Σ T·G DIFFERS from the once-per-cell J-sum
(J + surplus = marked row, surplus > 0 there); at the n = 3 gate rosters they
coincide (surplus ≡ 0, V4-8) — BOTH directions stated, so no consumer can
conflate the objects. moves_ref: "This is NOT the marked per-continuing-
branch T·G (rev 2, pass-1 finding 1: … a T·G-sum would multiply-count the
cell)" (S.0). deps: V5-7a, V4-7, V4-8. sketch: toy 2-mark cell instance +
the n = 3 decide. hyp_fields: none.

### Layer V6 — gate V-n3, decide-native (the seal's displays re-derived) [10]

**V6-1a `rootTable_identities` · `V6_a1poly.lean` · easy.**
The five root closed forms + PART-1 count face AS POLYNOMIALS:
`TH3 + TH12 + TH3c + T21 + T3 = X^3` in ℚ[X] (`ring`), + each degree ≤ 3.
moves_ref: "PART-1 count face, displayed: (q³−3q²+2q)/6 + (3q³−3q²)/6 +
(2q³−2q)/6 + (6q²−6q)/6 + 6q/6 = q³ = pool. ✓" (V.6.1).
deps: DefsGate. sketch: ring/decide on coefficients. hyp_fields: none.

**V6-1b `rootTable_evals` · `V6_a1eval.lean` · easy.**
The PREDICTED EVALUATIONS table at the nine census q — all 45 entries + the
Σ = q³ row, `norm_num`/`decide` (values from V.6.1's table: m_H3 row
0,1,4,10,35,56,84,165,286; …; m_3 row = q). Includes the m_H3 = 0 at q = 2
falsifier as its own named lemma. moves_ref: the V.6.1 evaluation table +
"the m_H3 zero at q = 2 (a genuine falsifier)" (V.6.5).
deps: V6-1a. sketch: norm_num. hyp_fields: none.

**V6-1c `rootTable_census` · `V6_a1census.lean` · medium.**
THE COUNT SEMANTICS at prime census points: over `ZMod p` for
p ∈ {2,3,5,7,11,13}, classifying monic cubics z³+az²+bz+c by
(root count, max multiplicity via f/f′/f″ evaluations): the five class
counts equal the closed forms' values — `decide` per p.
HONEST SCOPE (recorded DEVIATION-FREE): the note's census includes prime
powers 4, 8, 9 (Python, sealed); the Lean census covers the six PRIME points
— which already OVER-determine each degree-≤3 polynomial (4 points suffice
per (†)), so the Lean layer re-derives the polynomial identification;
the prime-power points remain the Python seal's record, cited not re-proved.
moves_ref: "(A-side …) exhaustive enumeration over F_q at the nine census q
of all fresh assignments … CHECKED EXACTLY, zero tolerance" (V.6.5) + (†).
deps: DefsGate. sketch: decide over Fin p³ with multiplicity predicates
f(x) = 0 ∧ f′(x) = 0 (∧ f″ for triple). hyp_fields: none.

**V6-2a `a2_domain_chart` · `V6_a2dom.lean` · medium.**
The A2 height-domain normal form: `{(h₀,h₂) : 1 ≤ h₂ ∧ 3·h₂ < h₀ ∧
Odd (h₀ − h₂)} = LinSet.Mem A2dom`-image under the (t,u)-chart
(h₂ = t ≥ 1, h₀ = 3t + 2u + 1), i.e. the ONE listed linear set
L((4,1); {(3,1),(2,0)}); one-component ⟹ the disjointness convention holds
VACUOUSLY (a `Pairwise` on a singleton list — stated).
moves_ref: "realizability = {h₂ ≥ 1 (vertex), h₀ > 3h₂ (hull strictness),
h₀ − h₂ odd}; with h₂ = t ≥ 1, h₀ = 3t + 2u + 1 (u ≥ 0) this is the ONE
linear set L((4,1); {(3,1), (2,0)})" (V.6.2). deps: Defs 2.A.
sketch: omega both directions (parity via 2u+1). hyp_fields: none — the gate
"FIXES its heights and consumes no domain hypothesis" (an ILLUSTRATION of
XHD-d's format, exactly as displayed).

**V6-2b `a2_weight_table` · `V6_a2wt.lean` · easy.**
E affine in the chart: `EA2.eval (chart t u) = 6t + 3u + 1` (omega/ring),
sealed point (4,1) ↦ E = 7; `TA2 = (X−1)²` with the nine evaluations
1,4,9,16,36,49,64,100,144 and PART-1 `(q−1)² = pool` (one letter).
moves_ref: "g(h₀,h₂) = q^{−E}, E = (3(h₀+h₂)−1)/2 — affine, positive
weights. Sealed census height point: (4, 1): E = 7" + the T = (q−1)² table
(V.6.2). deps: DefsGate, V6-2a. sketch: norm_num. hyp_fields: none.

**V6-3a `blk2_table` · `V6_bpoly.lean` · easy.**
s_blk2 closed forms + PART-1: `Tsplit + Tinert + Tdbl = X·(X−1)` (ring);
char-2 recount equalities as polynomial identities ((q−1)(q/2 − 1) form =
Tsplit, (q−1)·q/2 = Tinert — the displayed convention: "the closed forms
below are the SAME polynomials under both"); degrees ≤ 2; Tw2 = X−1,
Tvv = (X−1)². moves_ref: "PART-1 count face: (q−1)(q−2)/2 + q(q−1)/2 +
(q−1) = q(q−1) ✓" + "(D2) … DISPLAYED exceptional-char convention; the
closed forms below are the SAME polynomials under both" (V.6.3).
deps: DefsGate. sketch: ring. hyp_fields: none.

**V6-3b `blk2_census` · `V6_bcensus.lean` · medium.**
The m₂ outcome census at the six prime census points: over ZMod p, quadratics
y² + wy + u with (u, w) ∈ pˣ × p classified split/inert/double by root count
+ multiplicity: counts = (q−1)(q−2)/2, q(q−1)/2, q−1 — decide per p; + the
(iv)-REP count face: the classification is independent of the source state
t ∈ F_qˣ BY CONSTRUCTION in the Lean carrier (the count sets don't mention
t — the (D2)-EMPTY executed check, stated as a definitional lemma), with the
two-representative census duty recorded as discharged-by-typing.
moves_ref: "the s_blk2 rows identical at both representatives ((iv)-REP)"
(gate record) + "(D2) source generators: EMPTY — none of the three letters'
displayed evaluation maps reads t" (V.6.3). deps: DefsGate.
sketch: decide + rfl-lemma. hyp_fields: none.

**V6-4a `gateB_numbers` · `V6_gateB.lean` · easy.**
Gate B's dyadic arithmetic, every number displayed: ι = 2·2⁻³ = 1/4;
T_{o_double}(2) = 1; g = 2⁻³; μ̂ = ι·T·g = 2⁻⁵ = 1/32; count shadow
I^ent(2)·T(2) = 2·1 = 2; marked pairs 2^{3N−5}: N = 3 ↦ 16, N = 4 ↦ 128;
A(ε) = 3, W_ent(ε) = 3, I^ent = q(q−1) = q·|β₀| ≠ |β₀| (the displayed
NOT-general instance, q ≥ 2). moves_ref: "SEALED EXACT PREDICTIONS:
μ̂(marked event) = ι·T·g = (1/4)·1·(1/8) = 2⁻⁵ = 1/32 …; count shadow =
2·1 = 2" + "note I^ent = q·|β₀| ≠ |β₀|" (V.6.4).
deps: DefsGate. sketch: norm_num. hyp_fields: none.

**V6-4b `gateB_two_histories` · `V6_gate2h.lean` · medium.**
The TWO-HISTORY DISCIPLINE, concrete at p = 2: the two marked entrance
histories (f̄ = z²(z+1) and f̄ = (z+1)²z over ZMod 2) BOTH land at the
same β₀ state (t = β̄ − ᾱ: 1 and −1 = 1 in ZMod 2), and their step reads
carry the SAME nominal inventory (E = 3λ as a function of the window shape
alone — stated as: the inventory function of DefsGate does not read the
recentering shift; evaluated equal for both histories) — hence T = 1 and
g = 2⁻³ per history BY DISPLAY, aggregate 2·2⁻³·(step factor); NO (XHD-u)
content consumed (the theorem's hypotheses list contains only the C15-shape
inventory data — auditable from the signature).
moves_ref: "(U-A) is applied PER HISTORY, separately … Both land at the SAME
β₀ state (t = 1 for z²(z+1); t = −1 = 1 at p = 2 …) and in EACH history's
branch frame the step read carries the SAME nominal digit inventory …
the commonality is DERIVED, not assumed" (V.6.4). deps: DefsGate, V1-6.
sketch: ZMod 2 arithmetic + inventory-function evaluation; decide/norm_num.
hyp_fields: the concrete inventory data (DefsGate) — no open kernel.

**V6-4c `gateB_threshold` · `V6_gateN.lean` · medium.**
THRESHOLD N = 3, the derivation typed: GIVEN the coprime-factorization lift
(typed premise `hensel : CoprimeLiftPack` keyed to Mathlib's Hensel/coprime
factorization — a PUBLISHED-statement face, preferred from the library per
the campaign axiom policy §4), level-3 data determine every event datum:
h₀ ≡ 4 mod 8 (v(h₀) = 2 + unit digit at level 3) and h₁ ≡ 0 mod 4
(v(h₁) ≥ 2) are level-3 predicates; box-precision 2^{3N−5} follows for all
N ≥ 3 with ZERO event-word changes (the multiplier lemma: each level adds
exactly 2³ free digits). moves_ref: "THRESHOLD N := 3, with the derivation
displayed: … the coprime (Hensel) factorization f = u·h lifts uniquely with
h mod 2^k determined by f mod 2^k for EVERY k … So level 3 determines every
event datum" (V.6.4). deps: DefsGate, V6-4a.
sketch: mod-arithmetic on box coordinates; the lift pack supplies
determinacy; counting the free digits. hyp_fields: `CoprimeLiftPack`
(Mathlib-backed; if the exact form is missing, it becomes a declared
published-axiom candidate per campaign §4 — flag at E-phase, do NOT
silently strengthen).

### Layer V7 — CTS-M assembly + the seam instances [7]

**V7-1 `ctsm_ledger` · `V7_ledger.lean` · easy (typing unit).**
THE PER-CLAUSE HYPOTHESIS LEDGER as ONE record (V.1's rev-2 finding-7 list,
verbatim — "each clause is asserted GIVEN exactly its listed set, nothing
less"): `structure CtsmLedger …` with one field per clause line: (i) the
BlockData family + computed lists at consumed skeletons; (ii) (ii-a/b) ←
(iv)-POLY ties, (ii-c) ← ActiveValueAgree; (iii) primitives free; ENT-AGG ←
XHD-s shallow; ENT-COUNT named; INIT-RAT ← XHD shallow + (ENT-U); (iv) ←
computed tables / + (XHD-u) / + PART-1's four legs / measured ← XHD-w +
(U-A) + (XHD-u) / resummed ← XHD-d/s; (v) OPEN + (HMC-AUG) separate; (vi) ←
per-identity sets + the solve sentence's ESCAPE(E0)/(ii-c)/ENT-COUNT/
INIT-RAT. Every field TYPED to the §3 unit statements (no Prop-placeholder
fields for in-corpus content; owner-tagged packages for [2b]/[3t]).
moves_ref: "PER-CLAUSE HYPOTHESIS LEDGER (rev 2 — finding 7 …)" (V.1).
deps: all statement layers. sketch: record decl. hyp_fields: the ledger IS
the hypothesis inventory — nothing new.

**V7-2 `ctsm_given` · `V7_ctsm.lean` · medium.**
THEOREM CTS-M assembled: `theorem ctsM (L : CtsmLedger …) : CtsmConclusions`
— the conjunction of the clause conclusions (i) syntax partition (V2-3 at
every listed skeleton), (ii-a/b) (V4-1/2), (iii)'s typing + ENT-AGG (V3-7/8),
(iv) STEP/PART/REP/MEAS (V4-5/6/7/9/10), (vi) COMP-h/hΣ/Σ/AGG
(V5-2/4/5/6) — each conclusion carrying EXACTLY its ledger field, (v) never
concluded (it remains a FIELD — open kernel). The [1v]-COND capstone of this
corpus. moves_ref: "This note proves CTS-M's clauses EACH GIVEN EXACTLY the
hypothesis set displayed in V.1's per-clause ledger" (header).
deps: V7-1 + cited units. sketch: apply each unit; assemble.
hyp_fields: = V7-1's ledger, displayed in the signature.

**V7-3 `tableShape_inst` · `V7_ts.lean` · medium.**
The `MovesS.TableShape n` instance from `CtsFamily`:
State e := block-e cells (via `toStepCells` and the block-size datum);
VType := `VLabel n` with `vEquiv := Equiv.refl`-keyed and `vdeg_spec` by rfl;
Out/odata from the letter+outcome rosters with member data from DEG-CONS's
tuples; Wloc/Wstate transported. + `MovesS.DegCons` for it (V2-9 at the gate
family; the general instance GIVEN the CL-11 burden field).
moves_ref: "Downstream discipline (plan REV 6): M2's τ, RS.0, RS.PRE, SQ.2
condition on CTS cells and on NOTHING finer or coarser" (V.0) — the seam's
one carrier. deps: V2-*, V7-1. sketch: structure wiring; Fintype instances.
hyp_fields: the roster-coverage burden (CL-13) rides as the BlockData-family
argument.

**V7-4 `measuredSide_inst` · `V7_ms.lean` · HARD.**
The `MovesS.MeasuredSide (tableShape_inst …)` instance from `CtsMeasured` +
MovesD boxes: Pools (prime powers, closure fields), Box := MovesD.Box-keyed,
Cell := digit cells, Rep := Hist, cellEvt/μcell/rowVal/kstep from 2.F,
activeState (act_size), EntShape := the (template-bounded) EntShapeV subtype
with hent/Went/ιsh/ιval/entCount/entLvl/entInst from 2.E, markedVal := the
μ̂ totals. ⌿ pre-approved split: (a) pools+boxes+cells; (b) entrance side;
(c) the kstep/rowVal wiring. moves_ref: MovesS.Defs §2.B's own intended-
instance note: "the CTS cell space over the level-N residue boxes of the O_δ
theory (the MovesC counting idiom), wave 4". deps: V7-3, Defs 2.E/2.F,
MovesD. sketch: field-by-field; the content lemmas are elsewhere — this unit
is wiring + the finiteness/nonemptiness instances.
hyp_fields: none NEW (an instantiation; open faces stay in LedgerIV).

**V7-5 `ratBurdens_inst` · `V7_rb.lean` · HARD.**
`MovesS.RatBurdens T M`, theorem-under-hypotheses — GIVEN the open faces,
the burdens structure is inhabited:
`theorem ratBurdens_exists (hVA : ValA …) (hJ : (V5-7b's premises))
(hIR : (V3-9c's premises)) (hACT : CofinAct …) :
Nonempty (MovesS.RatBurdens T M)` — tgP from ValA's tables ((iv)-POLY/CL-6),
jP from V5-7b ((J-RAT)/CL-18), ιP from V3-9c (INIT-RAT), cellP from
BlockData.sizeP (+ `act_iff` from act_size; `cellP_nonzero` from the zero-
deletion V2-2), degree fields from the split bounds (V2-10). ⌿ split: (a)
tgP/j̲P legs; (b) ιP leg; (c) cellP + act_iff. moves_ref: the V.0 downstream
line "[3] RESUM consumes K_e and ι_e from this note's clauses only" + CL-6/
CL-18/INIT-RAT ownership rows. deps: V2-4, V5-7b, V3-9c, V2-2, V2-10, V7-4.
sketch: assemble PolyGeoms; interp fields from the units' eval conclusions.
hyp_fields: (iv)-POLY beyond gate blocks (CL-13/CL-6) + (J-RAT)'s cell pack +
INIT-RAT's set — the STATED premises; nothing discharged silently.

**V7-6 `ledgerIV_inst` · `V7_liv.lean` · medium.**
`MovesS.LedgerIV T M`, theorem-under-hypotheses: GIVEN the XHD bundle + HMC
+ the PART-1 legs + ENT-COUNT: every LedgerIV field supplied from its §3
unit — xhd_sum/no_stray/no_orphan ← XHDd/XHDs (via V0-3 restriction to
cells); d4r0 ← V4-10's marked-space disjointness projected to fixed-height
cell events (the f-side disjointness of DIGIT CELLS — exactly what d4r0
demands); part1 ← V4-6; rep_indep ← V4-9; meas_card ← the counting-native
tie (V7-4's cellEvt semantics); kstep_one (def tie) + hmc ← the HMC field
(NOTE: MovesS's `hmc` field is the k-step FACTORIZATION law — supplied
CONDITIONALLY on the open kernel, so `ledgerIV_inst` carries `hHMC`
explicitly; no unconditional instance exists until (v) closes);
act_target ← V4-1; init_agg ← V3-8; init_count/ent_count_card ← V3-9a +
V7-4's entInst; comp_once ← V5-4 at length-0 continuation (the ι height
sum). moves_ref: the CL-5 nine-input ledger's [1v] faces (S.0, cited; each
face's home display quoted at its field). deps: V4-*, V3-*, V5-4, V7-4.
sketch: field-by-field application. hyp_fields: XHD + HMC + PART-1 legs +
ENT-COUNT — the ledger's own tags, verbatim.

**V7-7 `seam_rekey_stmts` · `V7_seam.lean` · easy (statement units).**
The §W4-SYNC re-keyed statements this corpus OWNS, as named defs consumable
by MovesS's contract: `def xhd_w_stmt/xhd_u_stmt/xhd_d_stmt/xhd_s_stmt :
Prop := Nonempty (XHDw …)/(XHDu …)/(XHDd …)/(XHDs …)` at the V7-4 instance
(re-keying XRBPackage's four xhd fields — S-2/S-9's "NAME AWAITING
RE-KEYING"); `def cts_counts_stmt : Prop := ValA … ∧ EntCount …` (re-keying
Wsh17Package.cts_counts — S-8's [1v] leg). moves_ref: MovesS §W4-SYNC S-2/
S-8/S-9 + this note's V.0 package. deps: V7-4, V2-4, V3-9a.
sketch: defs. hyp_fields: none (names for open obligations — their TYPES pin
their content, per doctrine; inhabitation stays with the owners).

## §4 SEAM-SUPPLY — every MovesS interface field, mapped to its supplying unit

This section is the wave-4 answer to MovesS's §W4-SYNC contract and to the
intended-instance notes in `MovesS/Defs.lean`. Legend: **[MovesV: unit]** =
supplied by this corpus; **[owner]** = NOT this corpus's (named owner; MovesV
neither states nor strengthens it).

### 4.1 `MovesS/Defs.lean` instantiation targets (the W-11 process gate)

| MovesS object | supplier |
|---|---|
| `TableShape n` (State/VType/vEquiv/Out/odata/Wloc/Wstate) | [MovesV: V7-3 from `CtsFamily` (§2.C); vEquiv via `VLabel` = the R20 pin verbatim] |
| `DegCons T` | [MovesV: V2-9 (gate rosters, decide) + the CL-11 full-roster burden field for uncomputed skeletons — carried, not discharged] |
| `KmatHyp T e` (kcol members size e) | [MovesV: V7-3's roster wiring supplies the member DATA; the (SCS) stage-law derivation is MovesS's own (K-SUB section) — no re-derivation here] |
| `MeasuredSide T` (all fields) | [MovesV: V7-4 from `CtsMeasured` (§2.F) + MovesD boxes; `Hgt` carrier = the corpus height points (MovesS blueprint line "MovesV instantiates the carrier at wave 4" — DONE here)] |
| `RatBurdens T M`: `tgP/tg_ok/tg_interp/tg_degT/tg_degS` | [MovesV: V7-5 leg (a) from ValA (V2-4) — CL-6 (iv)-POLY, GIVEN the table-build coverage] |
| `RatBurdens.jP/j_ok/j_interp/j_degT/j_degS` | [MovesV: V7-5 from V5-7b — **(J-RAT)/CL-18, THE PLAN-SYNC DELIVERABLE recorded owner-side**; height-sum face tagged [2b]] |
| `RatBurdens.ιP/ι_ok/ι_interp/ι_countS_one/ι_count/ι_degT/ι_degS` | [MovesV: V7-5 leg (b) from V3-9c (INIT-RAT) + V3-9a (ENT-COUNT); GIVEN XHD-shallow + (ENT-U)] |
| `RatBurdens.cellP/cellP_deg/cellP_nonzero/cellP_count/act_iff` | [MovesV: V7-5 leg (c) from `BlockData.sizeP` + V2-2's zero-deletion + `act_size`] |
| `LedgerIV T M` (all nine inputs) | [MovesV: V7-6, CONDITIONALLY — xhd_* ← XHD package fields ([2b]); d4r0 ← V4-10 projection; part1 ← V4-6 (its four legs displayed); rep_indep ← V4-9; meas_card ← V7-4 semantics; kstep_one def-tie; hmc ← the OPEN kernel field (hHMC explicit — no unconditional instance until (v) closes); act_target ← V4-1; init_agg ← V3-8; init_count/ent_count_card ← V3-9a/V7-4; comp_once ← V5-4] |
| `EscapeE0`, `PoolHyp`, `DetHyp`, `RegP` | [owner [3] MovesS — CL-1; MovesV only supplies the entries' OKat memberships through RatBurdens] |

### 4.2 `MovesS/Interfaces.lean` fields

| field | supplier |
|---|---|
| `RS1Meas.βmeas/β_bdd/βfull` | [owner [3t] → MovesT: measured subtree values; MovesV supplies NO per-f or subtree object — the [3t] fence] |
| `RS1Bundle.xrb` (W-2) | [owner [3]: the S.1 theorem; its `XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` premise fields RE-KEYED to MovesV's typed statements — V7-7] |
| `RS1Bundle.recursion_meas` (W-3) | [owner [3t]/[3]: the RS1GivenPackage route; MovesV contributes the PCI leg's (iv)-REP statement (V4-9) as the re-key target for `pci`'s REP conjunct] |
| `RS1Bundle.nsNull/rexact` | [owner [3t] §T.2 — CLOSED there; tag displayed] |
| `RS4Chain.L` | [MovesV: V7-6 (conditional instance)] |
| `RS4Chain.B/hns/PrimePools/prime_*/Sigmas/sig_exact` | [owner: wave-4 assembly (MovesT + MovesS gate)] |
| `RS4Chain.pools_e0/legs_reg` | [owner [3] — CL-1 E0; consumes MovesV's RatBurdens entries] |
| `RS4Chain.WshP/wsh_ok/WshVal/wsh_interp/wshval_bdd` | [owner [3t]/[3] — CL-17(ii) production; MovesV supplies the `cts_counts` leg: V7-7's `cts_counts_stmt` (ValA ∧ EntCount) re-keys `Wsh17Package.cts_counts` (seam S-8)] |
| `RS4Chain.wsh17_pin` | [owner [3]: instantiated with W17ii's statement at wave 4; the [1v] ingredient = V7-7] |
| `RS4Chain.shDom/shEvtH/visH/shEvt/shWeightH/shevt_grouping/shDom_ne/sh_realized/shweight_card/wshval_card` | [SPLIT: the per-ε shallow ingredients (entrance domains H(ε̊), entrance events, ιshH weights) are MovesV's — V7-4's entrance side (2.E/2.F); the per-SHAPE Ŝ assembly over trees is MovesT's (shapes are [3t] vocabulary). The re-keying REPLACES MovesS's device fields by production objects only when BOTH halves exist — per S-8/S-10's re-keying charge] |
| `RS4Chain.Rval/r_bdd/decidedTotal/x3_total/rs1_equates/rsh_interp` | [owners [3t]/[5]/[3] — W-1/W-4 pins; μ̂/density fence: nothing here is MovesV's to state] |
| `ReadOffBundle.pkg` | [owner [3] — E0 packages] |
| `ReadOffBundle.read` (AVAgree) | [MovesV: V4-3 states the (ii-c) duty in MovesS's own AVAgree shape; the CHECK is RESUM-n3's ([3]'s gate) — recorded, never a blanket claim] |

### 4.3 The seam entries RE-KEYED by this blueprint (count: 6)

1. **S-2 (`W2_xrb` package fields)** — the four `xhd_*` Prop placeholders in
   `XRBPackage` re-keyed to `Nonempty (XHDw/XHDu/XHDd/XHDs …)` at the V7-4
   instance (V7-7). `jc_inv`/`sib`/`tb_cap`/`vp`/`rel2_*` stay with their
   owners ([2b]/[3t]/[2r]).
2. **S-8 (`W17ii` + `Wsh17Package`)** — the `cts_counts` field re-keyed to
   `cts_counts_stmt := ValA ∧ EntCount` (V7-7); the demanded `xhd_s` face is
   the typed `XHDs` structure (§2.G). `c15_volumes` stays §C/HC-2's;
   `sib_count` stays [3t]'s.
3. **S-9 (packages as registries)** — the [1v]/[2b]-XHD names in the
   registries now point at typed structures with content-pinning fields
   (doctrine satisfied: degenerate instances violate typed laws).
4. **W-6 (wild-pool read-off, AVAgree)** — cited per consumption site: V4-3
   is the [1v]-side citation form.
5. **W-11 (instantiation of every §2 structure by the REAL CTS objects)** —
   the process gate is now the concrete unit list V7-3/V7-4/V7-5/V7-6 (+
   V2-9); DONE when those build.
6. **CL-18 (J-RAT) owner-side record** — the PLAN-SYNC flag's demand ("the
   owner notes' NEXT revision rounds must record these deliverables on their
   side") is discharged FOR THE LEAN CORPUS by §2.H + V5-7a/b/c: the
   per-cell tables are typed, their ℚ(q)-membership stated in the (iv)-POLY
   pattern, the not-the-marked-T·G fence machine-checked. (The NOTE text
   itself is accepted and unedited — this is the Lean-side record, exactly
   as the flag prescribes cross-note binding through the ledger.)

NOT re-keyed here (recorded): MovesS seam entries S-1/S-1e/S-1m, S-3, S-4,
S-5, S-6, S-7, S-10, S-11 (MovesT's vocabulary — trees, fibers, read
ledgers, RS.1); MovesD's §2.5 entries W4-1..W4-4 (TreeModel semantics,
VerdictModel, D4R_CYL consumer, NP-ID — MovesT/HC-2's). (JC-INV)/CL-19 is
[2b]'s and appears in NO MovesV statement.

## §5 Build order, process, and the census

**Build order (E-phase):** Defs → DefsGate → V0 → V1 → {V2, V6} (parallel;
V6 depends only on DefsGate + 2.A) → V3 → V4 → V5 → V7. The gate layer V6
is deliberately early-buildable: it is the corpus's non-vacuity anchor (the
sealed numbers re-derived in-kernel before any measured clause elaborates).

**Difficulty census: 70 units = 32 easy / 33 medium / 5 hard.**
HARD (escalation-risk set, pre-declared): V3-5 (instantiation bijection;
split (a)/(b)/(c) pre-approved), V4-6 (PART-1's countable route; split
(i)/(ii)/(iii)), V5-2 (COMP-h grouping induction; split (a)/(b)/(c)),
V7-4 (MeasuredSide wiring; split (a)/(b)/(c)), V7-5 (RatBurdens assembly;
split (a)/(b)/(c)). WATCH (medium with known teeth): V0-4 (double geometric
sum in Qq), V2-6 (cyclic power-image cardinality), V6-4c (the
CoprimeLiftPack — Mathlib Hensel archaeology; published-axiom fallback per
campaign §4, flag before declaring).

**Statement-fence inventory (changes needing sign-off):** none — every
structure above is new (additive); MovesS/MovesSp/MovesD are imported, never
edited. The two DESIGN-FREEDOM slots (StepSys.inv → C15Pack's carrier;
XHDd.chain's recursion tie in V2-5) are flagged inline for the audit round
— the Defs designer resolves them WITH the auditor, per campaign §3(ii).

**Non-vacuity anchors (the wave-2 doctrine, per package):** XHD-w: positive
weights are typed data (V0-1) + range lemma V1-1; XHD-u: the rectangularity
FALSITY witness (V1-2's second lemma) + the (U-A)-does-not-imply-(u-R) fence
V1-7; XHD-d: two-sided exactness against a count primitive (V1-3), listed
partition BY TYPE (2.A); XHD-s: the PROVED A2-format witness V0-4; HMC: the
false-instance/true-instance pair V4-11; templates: terminal-final BY
CONSTRUCTOR; J: the not-marked-T·G fence V5-7c; ε: post-split distinctness
V3-1, heights-retained discrimination V3-2; gate: 100+ sealed numbers
re-derived (V6-1a..V6-4a) including the m_H3 = 0 falsifier.

**Honest-perimeter recap (what a corpus record may claim when all 70 build):**
CTS-M's clauses machine-checked EACH GIVEN EXACTLY its V.1-ledger set (V7-2);
(U-A) proved given the typed §C pack; the V-n3 displays re-derived in-kernel
(prime census points; prime-power points remain the Python seal's); the
MovesS seam supplied per §4 — with XHD/(XHD-u)/(ENT-U)/HMC/ENT-COUNT/
INIT-RAT-premises/(J-RAT)-cell-pack/(ii-c)/CL-13-coverage all OPEN, riding
as typed arguments. NOTHING here is "the density R_σ": every mass is μ̂-typed
or counting-native; the marked→per-f conversion stays [3t]'s.

*(End of MOVESV blueprint REV 1. Next per campaign §3: Codex/Fable semantic
audit of this blueprint + Defs; REJECT loops until ACCEPT; then E-phase.)*

warning: Codex could not find bubblewrap on PATH. Install bubblewrap with your OS package manager. See the sandbox prerequisites: https://developers.openai.com/codex/concepts/sandboxing#prerequisites. Codex will use the bundled bubblewrap in the meantime.
codex
I’m auditing the unit statements and the seam table against the displays, with special attention to whether the proposed Defs can actually produce every `MovesS` field. I’ll report only offending specs, quoted and classified; clean units won’t be repeated.
codex
1. **CRITICAL — XHD packages remain vacuously inhabitable.**

   Offending spec:

   > `structure StepSys (n : ℕ) where Cell : Type ... hist_ne : ∀ α, Nonempty (Hist α)`

   Neither `Cell` nor any `Move α β`, `MoveT α v`, or realizable height domain must be inhabited. Thus all fields of `XHDw`, `XHDu`, `XHDd`, and `XHDs` can hold vacuously on an empty transition system. The later A2 witness shows that one nondegenerate instance exists; it does not prevent degenerate instances from satisfying the same hypothesis structures. This violates the requested per-structure non-vacuity doctrine.

2. **CRITICAL — the realization/count primitives are not tied together.**

   Offending specs:

   > `Assign ...`, `cntraw ...`, `XHDd.chain ...`

   and:

   > `the chain recursion is the chain-vs-cntraw tie FIELD the E-designer adds to XHDd`

   `cntraw` is not required to be the cardinality of `Assign`; `XHDd.chain` is not required to count assignment chains; neither is tied to `CtsMeasured.cellEvt`. Consequently XHD-d can certify an arbitrary synthetic support unrelated to realizable fresh assignments. The note defines \(T_\gamma(x,h)\) as the actual finite assignment-chain count, not an unconstrained function.

3. **CRITICAL — the A2 exponent cannot inhabit the proposed `AffineE`.**

   Offending specs:

   > `structure AffineE ... coeff : Fin D → ℕ`

   > `EA2 : AffineE 2` with `E(h₀,h₂) = (3(h₀+h₂)−1)/2`

   On the actual coordinates \((h₀,h₂)\), this has half-integral coefficients and cannot be represented by natural coefficients. Reparameterizing by \((t,u)\) gives \(6t+3u+1\), but `A2dom` is still declared in \((h₀,h₂)\)-coordinates. Indeed no natural-coefficient affine function on \((h₀,h₂)\) restricts to the displayed value: the \(u\)-coefficient would force \(2a=3\). This makes V0-4 and V6-2b incompatible with their own Defs.

4. **GAP — declaration order and several displayed types are not Lean-plausible as written.**

   Offending specs include:

   > `StepSys ... MoveT : Cell → VLabel n → Type`

   before `VLabel` is declared;

   > `structure XHD ... d : XHDd ... s : XHDs ...`

   before `XHDd`/`XHDs` are declared; and

   > `kind : (twist : ℤ) ⊕ (relName : String)`

   which is not a valid sum type. The “normative declaration order” therefore cannot elaborate verbatim.

5. **CRITICAL — (D2) is weakened to a name string and an unconstrained partition.**

   Offending spec:

   > `kind : (twist : ℤ) ⊕ (relName : String)`

   > “the polynomial itself lives in the E-designer's per-instance `relPoly` field where a unit consumes it”

   No such field is present. Nor does the type require an anchor generator’s `part` to apply the displayed twist. The note requires each relation with its polynomial and exceptional-characteristic convention, and requires twisted rather than fixed-frame cells. A `String` plus arbitrary `part` can silently encode any partition.

6. **CRITICAL — `EntShapeV` does not type the note’s entrance triple.**

   Offending spec:

   > `gsel : ℕ; musel : ℕ; selRec : List ℕ`

   These fields are not tied to an actual designated continuing branch, an L5-eligible selection, the entry read, the landing block/cell, or one selection record entry per shallow branching cell. V3-1 proves only that records already differing in `selRec` are unequal; it does not prove that siblings must receive different records. Degenerate or fictitious “entrances” rejected by the note therefore inhabit the type.

7. **CRITICAL — V7-4 cannot produce `MovesS.MeasuredSide`.**

   Offending unit:

   > “The `MovesS.MeasuredSide ...` instance from `CtsMeasured` ... field-by-field”

   Required fields have no supplier of the right type. Examples:

   - `MeasuredSide.hent : EntShape → ℕ`, while `EntShapeV.hent : List (ℕ × ℚ)`;
   - `rowVal` and `kstep` are absent from `CtsMeasured`;
   - `cellLvl`, `cellInst`, `gwt`, `entEvtH`, `ιDom`, `ιshH`, `entLvl`, and `entInst` are absent;
   - pool closure and infinitude are absent;
   - finiteness of the proposed bounded entrance subtype is not supplied;
   - `MeasuredSide.Cell e τ` is an outcome-cell fiber at a state, whereas `CtsMeasured.DCell` is indexed by a particular move between two `StepSys` cells.

   Thus the claimed all-fields seam supplier is not type-correct.

8. **CRITICAL — V5-7a/b/c do not carry the required per-\((\tau,o)\) J table.**

   Offending specs:

   > `bcells : ∀ {α β} (m : S.Move α β), Finset (V.DCell m)`

   > `Jval ... {α β} (m : S.Move α β) ...`

   There is no outcome parameter `o`, and only continuing `Move` data are covered. But `RatBurdens.jP` requires:

   > `∀ e (τ : T.State e), T.Out e τ → PolyGeom`

   Therefore V5-7b cannot produce `jP/j_interp` for every branching outcome. This fails the binding J-RAT/CL-18 obligation: entrywise \(J_{\tau,o}\in\mathbb Q(q)\), not a move-level or marked \(T\!\cdot G\) aggregate.

9. **CRITICAL — V2-5 is false under its stated hypotheses.**

   Offending unit:

   > `theorem valB (U : XHDu ...) (D : XHDd ...) ... : D.chain γ x h = pathProd S γ`

   `XHDu` constrains `cntraw`; `XHDd.chain` is independent arbitrary data. The admitted future “chain recursion tie FIELD” is essential and missing. The additional “unconditional degree bound” also has no box/pool-size or per-step cardinality hypothesis from which it could follow.

10. **CRITICAL — V2-8 proves only the zero-twist special case, not the anchor-alignment fence.**

    Offending unit:

    > “the fence lemma: at `a_eff = 0` twisted = fixed-frame”

    The note’s binding statement is that when \(a_{\mathrm{eff}}\ne0\), cells apply to the twisted target and never directly to the fixed-frame target. Equality at zero does not enforce that requirement, and `GenSpec.part` remains unconstrained.

11. **CRITICAL — V2-10’s advertised strict-bound witness contradicts its examples.**

    Offending unit:

    > “an explicit instance where `Wstate s > Wloc m` is CONSISTENT (the s_blk2 data (`Wstate = 1`, some `Wloc = 2`, and the root: `Wstate = 0 < Wloc = 3`)”

    Both cited examples satisfy `Wstate < Wloc`; neither witnesses `Wstate > Wloc`. The unit’s promised statement and sketch do not match.

12. **CRITICAL — V3-4 weakens the note’s finite-template claim.**

    Offending unit:

    > “Per `(e, β₀)` and bounded shallow depth, the template family is FINITE”

    The note asserts finiteness of the entrance-template family from [2a]/M1 and L5. The blueprint adds an external `WordBounded` premise attributed to a [3t] cut. That changes the quantification and silently moves part of this note’s entrance-finiteness obligation to another owner.

13. **CRITICAL — V3-6 contains a false equality characterization.**

    Offending unit:

    > `iotaCount ... ≤ total; with equality iff lands is total`

    Equality need not imply `lands` is total: excluded indices may have empty fibers and contribute zero. The frozen note asserts a refined D4R.1 subsum, not this stronger iff.

14. **CRITICAL — V3-8 cannot establish ENT-AGG from the displayed structures.**

    Offending unit:

    > “component sums by XHD-s”

    `XHDs` sums `gProd` for path templates. No field identifies the concrete entrance mass `ιsh (ε̊[h])` or `iotaCount` with an entrance count times the corresponding shallow `gProd`. Hence shallow XHD-s cannot yield the claimed `HasSum` without an additional entrance-mass/count tie.

15. **CRITICAL — V4-1 silently drops the active-source guard.**

    Offending statement:

    > `¬ V.activeState q₀ β → (C.T ... α βc).eval q₀ = 0`

    The note states NO-ENTRY only “for every source active at \(q₀\).” The proposed theorem demands zero entries even from inactive source rows, which the note explicitly treats as formal junk and never constrains. It is strictly stronger.

16. **CRITICAL — V4-5 omits the XHD-w hypothesis that supplies `g`.**

    Offending statement:

    > `theorem step_row (P : C15Pack) (U : XHDu) (D : XHDd) (Xs : XHDs) ... X.g ...`

    No `X : XHDw` argument appears, although the conclusion uses `X.g`. More substantively, (U-A) gives equality among assignment masses at one history; it does not identify that mass with \(q^{-E(h)}\). The note explicitly requires XHD-w plus (U-A), XHD-u, and XHD-d/s.

17. **GAP — V4-6’s actual hypothesis fields are not displayed.**

    Offending unit:

    > `theorem part1 (leg_a ...) (leg_b ...) (leg_c ...) (leg_d ...)`

    The prose later says the unit also carries XHD-w’s (U-A) face and XHD-d/s, but these do not occur in the quoted statement. It is unclear whether they are genuinely explicit fields or have been folded into the four abstract leg predicates.

18. **CRITICAL — V4-8 proves only a gate fragment of the universal \(n=3\) assertion.**

    Offending unit:

    > “Stated over the gate rosters: `∀ cells in the V.6 rosters, emult ≤ 1`”

    The note states that at \(n=3\) the surplus vanishes identically. The proposed general fallback uses only `DegCons`, whose `size_pos` gives member size at least 1, not the required fact that each continuing cluster has size at least 2. Thus neither the gate-only census nor the stated abstract hypotheses prove the displayed universal claim.

19. **CRITICAL — V4-12’s numerical iff is not valid.**

    Offending unit:

    > “height-sum factorization ... for ALL fixed weight systems of XHD-w’s monomial form IFF ... `HMC`”

    Strict positivity alone does not reconstruct set equality from equality of weighted sums: distinct tuples can have equal monomial weights, allowing a missing tuple and an extra tuple to cancel numerically. The note uses HMC as the structural condition licensing factorization; it does not prove this stronger extensional characterization from the restricted monomial family.

20. **CRITICAL — V6-1c and V6-3b weaken the sealed census display.**

    Offending units:

    > “the Lean census covers the six PRIME points”

    versus their quoted `moves_ref`:

    > “exhaustive enumeration over \(F_q\) at the nine census \(q\)”

    Prime powers \(4,8,9\) are omitted. Polynomial overdetermination at six primes does not faithfully state the note’s nine-point, prime-power census, especially since exceptional-characteristic and finite-field behavior—not merely polynomial interpolation—is part of the gate.

21. **GAP — the fenced Hensel proposal has no auditable type.**

    Offending unit:

    > `hensel : CoprimeLiftPack`

    > “if the exact form is missing, it becomes a declared published-axiom candidate”

    This remains a premise and is explicitly flagged, so it has not yet violated the no-unconditional-axiom rule. But `CoprimeLiftPack` is nowhere defined field-by-field, so one cannot verify that it states exactly unique coprime lifting and coefficient determinacy rather than a stronger conclusion. It must remain a typed fenced proposal; “declared” must not become an unconditional Lean axiom.

22. **GAP — V7-2’s capstone conclusion is underspecified.**

    Offending unit:

    > `theorem ctsM (L : CtsmLedger …) : CtsmConclusions`

    `CtsmConclusions` is not displayed. The prose list omits or leaves unclear several ledgered deliverables, including VAL(b), INIT-RAT, ENT-COUNT’s status, ACTIVE-VALUE, the count shadow, and the conditional solve sentence. Exact per-clause hypothesis fidelity cannot be audited from this opaque target.

23. **CRITICAL — V7-5 cannot construct the advertised `RatBurdens`.**

    Offending unit:

    > “`tgP` from ValA’s tables”

    and:

    > “`ιP` from V3-9c”

    `tgP` must interpolate the measured resummed row `rowVal`, requiring the \(G\)-bearing XHD-s face; ValA supplies only count polynomials. Conversely V3-9c states a rational presentation for aggregate `V.ιval e τ`, whereas `RatBurdens.ιP/ι_interp` are per entrance shape and interpolate `M.ιsh e τ ε`. These are different types and different note displays.

24. **CRITICAL — V7-6 does not actually produce several `LedgerIV` fields.**

    Offending unit:

    > “`LedgerIV T M`, theorem-under-hypotheses ... field-by-field application”

    Specific mismatches include:

    - no tie from `XHDs.Gc_hasSum` to `M.μcell`, so `xhd_sum` is unavailable;
    - no counting law tying `gwt` to `cellEvt`, so `meas_card` is unavailable;
    - no supplied `kstep`, so `kstep_one` and the recursive `hmc` field are unavailable;
    - V3-9a is an aggregate entrance polynomial statement, not `init_count`’s fixed-height cardinality law;
    - V5-4 sums path heights, whereas `comp_once` sums entrance heights in `ιDom`.

    The claimed supplier units do not produce the target field types.

25. **CRITICAL — the SEAM-SUPPLY table drops `SCSData` and misattributes `KmatHyp`.**

    Offending seam row:

    > “`KmatHyp T e` ... V7-3’s roster wiring supplies the member DATA; the (SCS) stage-law derivation is MovesS’s own”

    `MovesS.Defs` contains the full `SCSData` structure with data and laws (`W`, `D`, `ℓ`, `g`, `μsel`, `memberOf`, `stage_D`, `cluster_child`, etc.). §4 maps none of those fields to a MovesV supplier or an explicit external owner. Moreover `KmatHyp` is a proposition, not member data, and no theorem in pasted MovesS derives it automatically. This directly violates the binding field-by-field seam audit.

26. **CRITICAL — the S-8 seam remains vacuous and drops the demanded XHD-s field.**

    Offending seam claim:

    > “the demanded `xhd_s` face is the typed `XHDs` structure”

    No `xhd_s` field is added to `Wsh17Package` or to V7-7’s `cts_counts_stmt`; nor is `F.Sh.Nonempty` supplied. Therefore `W17ii` remains trivially true when `F.Sh = ∅`, precisely the empty-menu trap called out by §W4-SYNC S-8.

27. **CRITICAL — V7-7 re-keys XHD as unrelated existential fragments.**

    Offending unit:

    > `xhd_w_stmt/xhd_u_stmt/xhd_d_stmt/xhd_s_stmt := Nonempty (XHDw …)/(XHDu …)/(XHDd …)/(XHDs …)`

    The note consumes one coherent XHD package: the same weights, uniformity data, exact domains, and sums. Independent `Nonempty` propositions can be witnessed by incompatible structures. `XHDs` also depends on particular `XHDw` and `XHDd` values, which the proposed standalone existential does not visibly bind to the other seam fields. The correct obligation is not four unrelated satisfiability claims.

28. **GAP — several units conceal multiple independent declarations or lemmas.**

    Offending examples:

    > V0-2: “membership + base membership + closure”

    > V2-1: projection theorem + finiteness theorem

    > V2-2: definition + instance + deletion theorem

    > V6-4a: arithmetic, count shadow, two census levels, degree facts, and the \(I^{ent}\ne|\beta_0|\) fence

    These exceed the promised “one display, one lemma” decomposition and make the stated sketches too small for the advertised conclusions.

29. **GAP — essential Defs remain explicit design placeholders rather than auditable dependencies.**

    Offending specs include:

    > `inv ... -- PLACEHOLDER`

    > `TargetIx ... is spelled ... in the E-phase file`

    > `HMCAug ... := …`

    > `XHDdSh`, `AffEnt`, `CellPolyPack`, `ObsCheck`, `CofinAct`, `moveOf`, `Realizable`, and `CtsmConclusions`

    Their fields determine whether open kernels are explicit, whether counts are genuine, and whether target indices type-check. Leaving them to E-phase design prevents a complete faithfulness and hypothesis-field audit.

Counts: **23 CRITICAL / 6 GAP**

**REJECT (23 crit / 6 gap)**
tokens used
91,541
1. **CRITICAL — XHD packages remain vacuously inhabitable.**

   Offending spec:

   > `structure StepSys (n : ℕ) where Cell : Type ... hist_ne : ∀ α, Nonempty (Hist α)`

   Neither `Cell` nor any `Move α β`, `MoveT α v`, or realizable height domain must be inhabited. Thus all fields of `XHDw`, `XHDu`, `XHDd`, and `XHDs` can hold vacuously on an empty transition system. The later A2 witness shows that one nondegenerate instance exists; it does not prevent degenerate instances from satisfying the same hypothesis structures. This violates the requested per-structure non-vacuity doctrine.

2. **CRITICAL — the realization/count primitives are not tied together.**

   Offending specs:

   > `Assign ...`, `cntraw ...`, `XHDd.chain ...`

   and:

   > `the chain recursion is the chain-vs-cntraw tie FIELD the E-designer adds to XHDd`

   `cntraw` is not required to be the cardinality of `Assign`; `XHDd.chain` is not required to count assignment chains; neither is tied to `CtsMeasured.cellEvt`. Consequently XHD-d can certify an arbitrary synthetic support unrelated to realizable fresh assignments. The note defines \(T_\gamma(x,h)\) as the actual finite assignment-chain count, not an unconstrained function.

3. **CRITICAL — the A2 exponent cannot inhabit the proposed `AffineE`.**

   Offending specs:

   > `structure AffineE ... coeff : Fin D → ℕ`

   > `EA2 : AffineE 2` with `E(h₀,h₂) = (3(h₀+h₂)−1)/2`

   On the actual coordinates \((h₀,h₂)\), this has half-integral coefficients and cannot be represented by natural coefficients. Reparameterizing by \((t,u)\) gives \(6t+3u+1\), but `A2dom` is still declared in \((h₀,h₂)\)-coordinates. Indeed no natural-coefficient affine function on \((h₀,h₂)\) restricts to the displayed value: the \(u\)-coefficient would force \(2a=3\). This makes V0-4 and V6-2b incompatible with their own Defs.

4. **GAP — declaration order and several displayed types are not Lean-plausible as written.**

   Offending specs include:

   > `StepSys ... MoveT : Cell → VLabel n → Type`

   before `VLabel` is declared;

   > `structure XHD ... d : XHDd ... s : XHDs ...`

   before `XHDd`/`XHDs` are declared; and

   > `kind : (twist : ℤ) ⊕ (relName : String)`

   which is not a valid sum type. The “normative declaration order” therefore cannot elaborate verbatim.

5. **CRITICAL — (D2) is weakened to a name string and an unconstrained partition.**

   Offending spec:

   > `kind : (twist : ℤ) ⊕ (relName : String)`

   > “the polynomial itself lives in the E-designer's per-instance `relPoly` field where a unit consumes it”

   No such field is present. Nor does the type require an anchor generator’s `part` to apply the displayed twist. The note requires each relation with its polynomial and exceptional-characteristic convention, and requires twisted rather than fixed-frame cells. A `String` plus arbitrary `part` can silently encode any partition.

6. **CRITICAL — `EntShapeV` does not type the note’s entrance triple.**

   Offending spec:

   > `gsel : ℕ; musel : ℕ; selRec : List ℕ`

   These fields are not tied to an actual designated continuing branch, an L5-eligible selection, the entry read, the landing block/cell, or one selection record entry per shallow branching cell. V3-1 proves only that records already differing in `selRec` are unequal; it does not prove that siblings must receive different records. Degenerate or fictitious “entrances” rejected by the note therefore inhabit the type.

7. **CRITICAL — V7-4 cannot produce `MovesS.MeasuredSide`.**

   Offending unit:

   > “The `MovesS.MeasuredSide ...` instance from `CtsMeasured` ... field-by-field”

   Required fields have no supplier of the right type. Examples:

   - `MeasuredSide.hent : EntShape → ℕ`, while `EntShapeV.hent : List (ℕ × ℚ)`;
   - `rowVal` and `kstep` are absent from `CtsMeasured`;
   - `cellLvl`, `cellInst`, `gwt`, `entEvtH`, `ιDom`, `ιshH`, `entLvl`, and `entInst` are absent;
   - pool closure and infinitude are absent;
   - finiteness of the proposed bounded entrance subtype is not supplied;
   - `MeasuredSide.Cell e τ` is an outcome-cell fiber at a state, whereas `CtsMeasured.DCell` is indexed by a particular move between two `StepSys` cells.

   Thus the claimed all-fields seam supplier is not type-correct.

8. **CRITICAL — V5-7a/b/c do not carry the required per-\((\tau,o)\) J table.**

   Offending specs:

   > `bcells : ∀ {α β} (m : S.Move α β), Finset (V.DCell m)`

   > `Jval ... {α β} (m : S.Move α β) ...`

   There is no outcome parameter `o`, and only continuing `Move` data are covered. But `RatBurdens.jP` requires:

   > `∀ e (τ : T.State e), T.Out e τ → PolyGeom`

   Therefore V5-7b cannot produce `jP/j_interp` for every branching outcome. This fails the binding J-RAT/CL-18 obligation: entrywise \(J_{\tau,o}\in\mathbb Q(q)\), not a move-level or marked \(T\!\cdot G\) aggregate.

9. **CRITICAL — V2-5 is false under its stated hypotheses.**

   Offending unit:

   > `theorem valB (U : XHDu ...) (D : XHDd ...) ... : D.chain γ x h = pathProd S γ`

   `XHDu` constrains `cntraw`; `XHDd.chain` is independent arbitrary data. The admitted future “chain recursion tie FIELD” is essential and missing. The additional “unconditional degree bound” also has no box/pool-size or per-step cardinality hypothesis from which it could follow.

10. **CRITICAL — V2-8 proves only the zero-twist special case, not the anchor-alignment fence.**

    Offending unit:

    > “the fence lemma: at `a_eff = 0` twisted = fixed-frame”

    The note’s binding statement is that when \(a_{\mathrm{eff}}\ne0\), cells apply to the twisted target and never directly to the fixed-frame target. Equality at zero does not enforce that requirement, and `GenSpec.part` remains unconstrained.

11. **CRITICAL — V2-10’s advertised strict-bound witness contradicts its examples.**

    Offending unit:

    > “an explicit instance where `Wstate s > Wloc m` is CONSISTENT (the s_blk2 data (`Wstate = 1`, some `Wloc = 2`, and the root: `Wstate = 0 < Wloc = 3`)”

    Both cited examples satisfy `Wstate < Wloc`; neither witnesses `Wstate > Wloc`. The unit’s promised statement and sketch do not match.

12. **CRITICAL — V3-4 weakens the note’s finite-template claim.**

    Offending unit:

    > “Per `(e, β₀)` and bounded shallow depth, the template family is FINITE”

    The note asserts finiteness of the entrance-template family from [2a]/M1 and L5. The blueprint adds an external `WordBounded` premise attributed to a [3t] cut. That changes the quantification and silently moves part of this note’s entrance-finiteness obligation to another owner.

13. **CRITICAL — V3-6 contains a false equality characterization.**

    Offending unit:

    > `iotaCount ... ≤ total; with equality iff lands is total`

    Equality need not imply `lands` is total: excluded indices may have empty fibers and contribute zero. The frozen note asserts a refined D4R.1 subsum, not this stronger iff.

14. **CRITICAL — V3-8 cannot establish ENT-AGG from the displayed structures.**

    Offending unit:

    > “component sums by XHD-s”

    `XHDs` sums `gProd` for path templates. No field identifies the concrete entrance mass `ιsh (ε̊[h])` or `iotaCount` with an entrance count times the corresponding shallow `gProd`. Hence shallow XHD-s cannot yield the claimed `HasSum` without an additional entrance-mass/count tie.

15. **CRITICAL — V4-1 silently drops the active-source guard.**

    Offending statement:

    > `¬ V.activeState q₀ β → (C.T ... α βc).eval q₀ = 0`

    The note states NO-ENTRY only “for every source active at \(q₀\).” The proposed theorem demands zero entries even from inactive source rows, which the note explicitly treats as formal junk and never constrains. It is strictly stronger.

16. **CRITICAL — V4-5 omits the XHD-w hypothesis that supplies `g`.**

    Offending statement:

    > `theorem step_row (P : C15Pack) (U : XHDu) (D : XHDd) (Xs : XHDs) ... X.g ...`

    No `X : XHDw` argument appears, although the conclusion uses `X.g`. More substantively, (U-A) gives equality among assignment masses at one history; it does not identify that mass with \(q^{-E(h)}\). The note explicitly requires XHD-w plus (U-A), XHD-u, and XHD-d/s.

17. **GAP — V4-6’s actual hypothesis fields are not displayed.**

    Offending unit:

    > `theorem part1 (leg_a ...) (leg_b ...) (leg_c ...) (leg_d ...)`

    The prose later says the unit also carries XHD-w’s (U-A) face and XHD-d/s, but these do not occur in the quoted statement. It is unclear whether they are genuinely explicit fields or have been folded into the four abstract leg predicates.

18. **CRITICAL — V4-8 proves only a gate fragment of the universal \(n=3\) assertion.**

    Offending unit:

    > “Stated over the gate rosters: `∀ cells in the V.6 rosters, emult ≤ 1`”

    The note states that at \(n=3\) the surplus vanishes identically. The proposed general fallback uses only `DegCons`, whose `size_pos` gives member size at least 1, not the required fact that each continuing cluster has size at least 2. Thus neither the gate-only census nor the stated abstract hypotheses prove the displayed universal claim.

19. **CRITICAL — V4-12’s numerical iff is not valid.**

    Offending unit:

    > “height-sum factorization ... for ALL fixed weight systems of XHD-w’s monomial form IFF ... `HMC`”

    Strict positivity alone does not reconstruct set equality from equality of weighted sums: distinct tuples can have equal monomial weights, allowing a missing tuple and an extra tuple to cancel numerically. The note uses HMC as the structural condition licensing factorization; it does not prove this stronger extensional characterization from the restricted monomial family.

20. **CRITICAL — V6-1c and V6-3b weaken the sealed census display.**

    Offending units:

    > “the Lean census covers the six PRIME points”

    versus their quoted `moves_ref`:

    > “exhaustive enumeration over \(F_q\) at the nine census \(q\)”

    Prime powers \(4,8,9\) are omitted. Polynomial overdetermination at six primes does not faithfully state the note’s nine-point, prime-power census, especially since exceptional-characteristic and finite-field behavior—not merely polynomial interpolation—is part of the gate.

21. **GAP — the fenced Hensel proposal has no auditable type.**

    Offending unit:

    > `hensel : CoprimeLiftPack`

    > “if the exact form is missing, it becomes a declared published-axiom candidate”

    This remains a premise and is explicitly flagged, so it has not yet violated the no-unconditional-axiom rule. But `CoprimeLiftPack` is nowhere defined field-by-field, so one cannot verify that it states exactly unique coprime lifting and coefficient determinacy rather than a stronger conclusion. It must remain a typed fenced proposal; “declared” must not become an unconditional Lean axiom.

22. **GAP — V7-2’s capstone conclusion is underspecified.**

    Offending unit:

    > `theorem ctsM (L : CtsmLedger …) : CtsmConclusions`

    `CtsmConclusions` is not displayed. The prose list omits or leaves unclear several ledgered deliverables, including VAL(b), INIT-RAT, ENT-COUNT’s status, ACTIVE-VALUE, the count shadow, and the conditional solve sentence. Exact per-clause hypothesis fidelity cannot be audited from this opaque target.

23. **CRITICAL — V7-5 cannot construct the advertised `RatBurdens`.**

    Offending unit:

    > “`tgP` from ValA’s tables”

    and:

    > “`ιP` from V3-9c”

    `tgP` must interpolate the measured resummed row `rowVal`, requiring the \(G\)-bearing XHD-s face; ValA supplies only count polynomials. Conversely V3-9c states a rational presentation for aggregate `V.ιval e τ`, whereas `RatBurdens.ιP/ι_interp` are per entrance shape and interpolate `M.ιsh e τ ε`. These are different types and different note displays.

24. **CRITICAL — V7-6 does not actually produce several `LedgerIV` fields.**

    Offending unit:

    > “`LedgerIV T M`, theorem-under-hypotheses ... field-by-field application”

    Specific mismatches include:

    - no tie from `XHDs.Gc_hasSum` to `M.μcell`, so `xhd_sum` is unavailable;
    - no counting law tying `gwt` to `cellEvt`, so `meas_card` is unavailable;
    - no supplied `kstep`, so `kstep_one` and the recursive `hmc` field are unavailable;
    - V3-9a is an aggregate entrance polynomial statement, not `init_count`’s fixed-height cardinality law;
    - V5-4 sums path heights, whereas `comp_once` sums entrance heights in `ιDom`.

    The claimed supplier units do not produce the target field types.

25. **CRITICAL — the SEAM-SUPPLY table drops `SCSData` and misattributes `KmatHyp`.**

    Offending seam row:

    > “`KmatHyp T e` ... V7-3’s roster wiring supplies the member DATA; the (SCS) stage-law derivation is MovesS’s own”

    `MovesS.Defs` contains the full `SCSData` structure with data and laws (`W`, `D`, `ℓ`, `g`, `μsel`, `memberOf`, `stage_D`, `cluster_child`, etc.). §4 maps none of those fields to a MovesV supplier or an explicit external owner. Moreover `KmatHyp` is a proposition, not member data, and no theorem in pasted MovesS derives it automatically. This directly violates the binding field-by-field seam audit.

26. **CRITICAL — the S-8 seam remains vacuous and drops the demanded XHD-s field.**

    Offending seam claim:

    > “the demanded `xhd_s` face is the typed `XHDs` structure”

    No `xhd_s` field is added to `Wsh17Package` or to V7-7’s `cts_counts_stmt`; nor is `F.Sh.Nonempty` supplied. Therefore `W17ii` remains trivially true when `F.Sh = ∅`, precisely the empty-menu trap called out by §W4-SYNC S-8.

27. **CRITICAL — V7-7 re-keys XHD as unrelated existential fragments.**

    Offending unit:

    > `xhd_w_stmt/xhd_u_stmt/xhd_d_stmt/xhd_s_stmt := Nonempty (XHDw …)/(XHDu …)/(XHDd …)/(XHDs …)`

    The note consumes one coherent XHD package: the same weights, uniformity data, exact domains, and sums. Independent `Nonempty` propositions can be witnessed by incompatible structures. `XHDs` also depends on particular `XHDw` and `XHDd` values, which the proposed standalone existential does not visibly bind to the other seam fields. The correct obligation is not four unrelated satisfiability claims.

28. **GAP — several units conceal multiple independent declarations or lemmas.**

    Offending examples:

    > V0-2: “membership + base membership + closure”

    > V2-1: projection theorem + finiteness theorem

    > V2-2: definition + instance + deletion theorem

    > V6-4a: arithmetic, count shadow, two census levels, degree facts, and the \(I^{ent}\ne|\beta_0|\) fence

    These exceed the promised “one display, one lemma” decomposition and make the stated sketches too small for the advertised conclusions.

29. **GAP — essential Defs remain explicit design placeholders rather than auditable dependencies.**

    Offending specs include:

    > `inv ... -- PLACEHOLDER`

    > `TargetIx ... is spelled ... in the E-phase file`

    > `HMCAug ... := …`

    > `XHDdSh`, `AffEnt`, `CellPolyPack`, `ObsCheck`, `CofinAct`, `moveOf`, `Realizable`, and `CtsmConclusions`

    Their fields determine whether open kernels are explicit, whether counts are genuine, and whether target indices type-check. Leaving them to E-phase design prevents a complete faithfulness and hypothesis-field audit.

Counts: **23 CRITICAL / 6 GAP**

**REJECT (23 crit / 6 gap)**
