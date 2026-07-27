# MovesS Lean blueprint — Codex final confirmation pass 4, on REV 7 (2026-07-27)
Verdict: REJECT (6 crit / 4 gap). Raw transcript below (codex CLI echoes the final answer twice; content identical).

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa448-edba-7101-9775-f8b8d70d9b1d
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

FOURTH final pass, on REV 7 — the CLOSING rev. History: your rev-6 verdict (1/7) affirmed all structural repairs; the critical was the jointly-uninhabitable n=2 instance. Rev 7 rebuilt it from the note's own data: one state, three outcomes (kcol q₀⁻³; termFin (1,1)² at 1−q₀⁻¹; termFin (1,2) at q₀⁻¹−q₀⁻³), part1 sums to 1, det(1−K) = (q³−1)/q³, and the reduced solve gives β₍₁,₂₎ = (q+1)/(q²+q+1), β₍₁,₁₁₎ = q²/(q²+q+1) — the note's displayed denominator, sum 1. CHECK THIS ARITHMETIC YOURSELF against the note's n=2/cubic-shadow displays. Your seven gaps: W-bounds pinned before the burdens (tg_deg/j_deg/ι_deg); W_Ŝ tethered with pinned owners; b1→7/b2→4/d1→3/d3→3 one-display splits; ONE Interfaces.lean. Also the independent auditor's two mechanical gaps: the [DecidableEq ι] batch and the ReadOffBundle n=2 inhabitation (new U-29d5). VERIFY each and sweep end to end. A clean pass = ACCEPTED for formalization.

THE FROZEN NOTE:

## §S-RESUM — the depth resummation into rational functions (assembly note 8, = plan [3]-COND)

*(2026-07-27. Assembly note 8 per ASSEMBLY_PLAN_2026-07-26.md §4, drafted
under the REV 15 DRAFTING RULING in the CONDITIONAL form [3]-COND: every
input enters as a DISPLAYED hypothesis with a named owner; this note's own
derivations are marked DERIVED and kept separate from what is consumed.
Consumes: the dual-accepted §V-TABLES (= [1v]-COND — Theorem CTS-M GIVEN
XHD; K_e, ι_e, the T/C_γ/Ĉ/I^ent count tables, (COMP-h)/(COMP-hΣ)/
(COMP-Σ)/(COMP-AGG), and the V.4 [3t]/[3] interface: K_e and ι_e handed
over with no source-mass division, ι paired once on the left, b_e THIS
note's object with its T·G entries supplied by (iv)-PART's absorbing
columns); the dual-accepted §T-ASSEMBLY (= [3t] — TREE-EXP fin/ns, TREE-N,
ONE-F, (SIB) as CL-10's open kernel in its (SIB-STEP) joint-vector form,
TB-CAP, VP, (NS-ROUTE), SIBLING INDEXING, and PCI with the XRB hypothesis
package THIS note discharges); the dual-accepted §R-LEDGER (= [2r] — the
FIVE REL.2 obligations (a)–(e), ALL OPEN, cited by name at every
base-changed leg); the dual-accepted §M-SPECIES (= [2a] — finiteness of
every shape/species quantifier, M1/M5); §H-DOMAINS (= [2b], in spiral —
the XHD/(ENT-U) owner; nothing here consumes a [2b] THEOREM, only the
NAMED hypotheses CTS-M already displays); §X-EXHAUST (= [5] — X.3 in its
CL-4 conditional form, consumed by E0's route and RS.4 ONLY). ACCEPTANCE:
blocked on STATE-probe-2 (plan §4 — M2(ii)'s vtx-varying regime),
[1v]-FULL (the recorded XHD discharge), and the gate RESUM-n3
(S.7; SPECIFIED, seal artifact owed) — none of which this draft
claims; see S.6. OPEN KERNELS owned
here: ESCAPE(E0) (CL-1) and CL-17's duty (ii) (the W_Ŝ machinery).
PROVED here under displayed hypotheses: XRB = RS.0(β) (CL-9) — and the
INTERNAL PROOF ORDER is BINDING (plan REV 14, pass-13 concern 1) in its
CONSUMPTION form (rev 3, pass-2 finding 9): the binding object is the
CONSUMPTION DAG, not textual position — S.1's proof of RS.0(β) consumes
NEITHER PCI β-substitution site, both sites (b_e^split at S.0, RS.1-SH
at S.2) consume XRB by citation, and the DAG is acyclic; S.0's site is
DEFINITIONAL presentation that FORWARD-REFERENCES S.1's proof —
textually earlier, logically downstream.)*

**What this note is.** The depth direction of the classifier tree,
resummed: the same-size block recursion (R_e) whose unknowns are the
entrance-free conditional subtree values β_{e,τ}; the marked-side solve
ι_e^T(I−K_e)^{−1}b_e; the three-clause aggregation identity RS.1 tying
the solve to the density components R_σ; rationality with fixed
coefficients (RS.2); solvability (RS.3, on the open kernel ESCAPE(E0));
and the checksum (RS.4). Everything measured is consumed from §V-TABLES's
CTS-M in its XHD-conditional form — no source-mass division anywhere,
heights summed EXACTLY ONCE (the (COMP-h)→(COMP-hΣ)→(COMP-Σ) passage),
and no μ̂-typed object is ever a density (V.4's fence, RS.1-MARKED). The
one piece of new mathematics the plan assigns to THIS note and delivered
here is S.1: XRB = RS.0(β), the height-elimination theorem-under-
hypotheses (CL-9), discharged at the acceptance-only edge [3]→[3t]-FULL.

### S.0 RS.PRE — the block system, its kernel, and the nine-input ledger

**The solve, displayed (plan §4 REV 6/10/13 form).** Fix n and a block
size e ≤ n. Unknowns β_{e,τ}(σ′), τ = (s, α) ranging over the block-e
states of 𝒞_n (the [1v] CTS-S cells at cluster size e; the typed list
𝒯_n is [2b]-owed), σ′ a verdict-type multiset. TYPING (REV 10/13,
verbatim duty): β_{e,τ}(σ′) is the CONDITIONAL PER-f value — the
probability, given ONE branch entering state τ, that its T_can^τ-subtree
completes with an ALL-(τ-irr)/(τ-hen) leaf multiset of type σ′. It is
ENTRANCE-FREE ((R_e) carries NO ι; entrance masses live in the outer
marked pairing alone) and HEIGHT-FREE (no h_ent index — exactly XRB,
proved at S.1).
  (BDY) BOUNDARY CONVENTION (rev 2, pass-1 finding 5 — pinned ONCE,
  EDGE-BASED, consumed by β's conditioning HERE and by (CUT-WD)'s
  trichotomy at S.2; it matches [1v]'s pin): the ENTERING READ of a
  block entrance belongs to the ENTRANCE SIDE — to ι_{e,ε,β₀} in the
  marked clause ([1v] (COMP-h): ι owns the ε-shaped entrance prefix
  LANDING in β₀, with its retained h_ent(ε); γ = the in-block reads
  only), and to W_Ŝ in the density clause (the shallow cascade runs
  to every block entrance INCLUSIVE of the entering read). β_{e,τ}
  is CONDITIONED on that entrance event and charges NO mass or
  height for the entering read: its inventory starts with the first
  in-block read from β₀. Node shadow: the first entrance node ν is
  BLOCK-side as a STATE INDEX (it carries the landed τ), while the
  edge INTO ν is entrance-side MASS — no read omitted, none
  double-charged.
The recursion, in its two displayed forms (one line
each, tagged — RS.PRE's (ns) TYPING, a named (NS-ROUTE) cite site):

  (R_e-lump)   β_e = K_e β_e + b_e^{term,fin} + b_e^split
    [UNCONDITIONAL — the lump form: the unknown is the 𝒯^fin-completion
    value; ns-bound paths ride K_e's continuing (vanishing-digit)
    columns and exit through NO column, contributing 0 to the Neumann
    sum];
  (R_e-exact)  β_e^full = β_e
    [GIVEN (ns-null) — CLOSED at [3t] §T.2 (REV 15; the single-state
    admissible-Z argument, four independent verifications); the
    discharged tag stays displayed: the same solve equals the FULL
    conditional subtree density].

Plan notation: (R_e) β_{e,·} = q^{−e(e−1)/2}M_e(q)β_{e,·} + b_{e,·} with
q^{−e(e−1)/2}M_e(q) := K_e(q) — the exterior factor is notation, never an
extra cost. The n = 2 instance is the 1×1 case (W6's geometric series,
denominator q² + q + 1; `msW_eighth_le` its p = 2 inequality shadow).
Engine form: `verification/om_density_engine.py`; BB3_infinity §4.1's
scalar FULLMONIC is hereby a CONJECTURED degenerate case (|𝒯| = 1), not
an input.

**The pieces, each consumed from its owner:**
- **K_e(q)** := the CTS-M(iv) kernel, entrywise K_e(q)_{(s,α),(s′,β)} =
  Σ_{m: s→s′} Σ_{o continuing} T_{m,o}^{α,β}(q)·G^{α,β}_{m,o}(q)
  (o continuing = the (c = 1, m = 1) row of (K-SUB)'s (m, c)
  CLASSIFICATION — agreement check (ii) there) — NO
  source-mass division (each g-summand is ALREADY conditional on the
  source cylinder; dividing again inflates the conditional — the pass-5
  critical). G := the XHD one-step resummed height mass (XHD-w monomials
  g over the XHD-d exact length-1 domain, per listed pairwise-disjoint
  component; XHD-s rationality; no HMC at k = 1). T·G is licit from
  (U-A) + (XHD-u)(u-R)/(u-T) — [1v] (iv)'s displayed consumption, cited
  not re-derived. K_e is entrance-height-FREE by [1v]'s display
  (entrance heights ride in ε, hence in ι alone). ANCHOR-EXPONENT DUTY
  (the plan's kernel-2 display duty, carried forward): entries at a > 0
  strata carry the Case-J anchor-monomial exponents inline (§B2-DEF's
  (z+c)^a transport factor) — a wrong anchor exponent silently corrupts
  every deep coefficient; the [1v] computed blocks are the checked
  instances.
- **ι_e** := the CTS-M(iii) initial vector: the ENT-AGG aggregate of the
  per-entrance-shape marked masses ι_{e,ε,β₀} (concrete ε carries its
  h_ent(ε); the instantiation bijection sums entrance heights HERE and
  nowhere else; POST-SPLIT, branch-weighted, per CTS-M(iii)). Components
  in ℚ(q) by INIT-RAT — a NAMED [1v] burden, cited by RS.2, not proved.
- **b_e** := b_e^{term,fin} + b_e^split, the named EXIT VECTOR — NO ns
  column (REV 13; the (NS-ROUTE) typing below). Per state τ, type
  argument σ′:
    b_e^{term,fin}(τ)(σ′) := Σ_{o terminal fin, v(o) = σ′} T·G
      (o terminal fin := the (c = 0, any m) row of (K-SUB)'s (m, c)
      CLASSIFICATION — ALL m members (τ-irr)/(τ-hen) one-step τ-halt,
      and v(o) := the FULL verdict multiset of ALL m members.
      Multi-member verdict values are LICIT: σ′ is typed a verdict-type
      MULTISET above, the display carries NO m = 1 restriction, and
      V.6.1's absorbing labels are the displayed multi-member
      instances — m_H3's three Hensel tracks ((1,1)³) and m_H12's
      "[1,1]+[1,2]". (iv)-PART's absorbing columns;
      verdict semantics [3t]'s VP, the labels consumed as column indices
      only);
    b_e^split(τ)(σ′) := Σ_{o branching} J_{τ,o}(q) ·
      Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m β_{e_j,τ_j(o)}(σ_j)(q^{δ_j})
      [o branching := the (c ≥ 1, m ≥ 2) row of (K-SUB)'s (m, c)
      CLASSIFICATION; rev 4, Fable F2: the product ranges over ALL
      branch members —
      τ-halted members contribute FACTOR 1 with σ_j their verdict value,
      per §T.4's leaf convention ('a τ-hen track is a leaf, factor 1'),
      cited here; β is evaluated only at block-state members]
      where J_{τ,o}(q) := the CELL-LEVEL resummed branching mass — the
      sum, over the branching digit CELLS of outcome class o at state
      τ, of the XHD-resummed conditional cell mass ([3t] TREE-EXP's
      jvol(c│Σ) summed over the cell's XHD height classes), EACH CELL
      ONCE. This is NOT the marked per-continuing-branch T·G (rev 2,
      pass-1 finding 1: §V types T·G per eligible continuation — a
      branching cell carries one T·G per continuing branch, PART-2's
      surplus — so a T·G-sum would multiply-count the cell); J's
      supply is (iv)-PART-1's digit-cell partition + XHD resummation,
      and its ℚ(q)-membership is the NEW NAMED burden (J-RAT) (owner
      [1v]/[2b]: cell-level counts polynomial per the (iv)-POLY
      pattern, XHD-s height sums), OPEN, cited by RS.2 and riding
      RS.4's tag — the MULTISET CONVOLUTION over children's types; the
      child index
      j runs over the branch set's INDIVIDUATED members ([3t] SIBLING
      INDEXING — member-indexed tuples, no order, no symmetry factor);
      the sibling product licensed by (SIB) conditionally on the
      branching cell (CL-10, open); each leg base-changed with δ_j
      ABSOLUTE ([2r] BASE-INDEX CONVENTION + (e2)); and the substitution
      of β_{e_j,τ_j(o)} for the subtree mass μ(S_j │ Σ_c) CITES the
      named interface PCI = REL.2(a)/(b)/(d) + CTS-M(iv)-REP + XRB —
      with XRB proved at S.1 (a FORWARD reference, rev 3: this display
      is DEFINITIONAL presentation, textually before S.1 but logically
      DOWNSTREAM of it in the consumption DAG — S.1's status line),
      and the [2r] legs cited as OPEN obligations (e1)–(e5)/CL-8.
- **ORIENTATION (REV 7/8, one convention).** The block solve is the
  COLUMN solve β_e = K_e β_e + b_e; ι_e is the entrance COLUMN vector
  acting ONCE on the left via its transpose; the scalar output
      ι_e^T (I − K_e)^{−1} b_e
  is the μ̂-typed MARKED-entrance total over post-split marks — consumed
  by (COMP-AGG) and the gates, NEVER the density (RS.1-SH assembles
  R_σ). ι is never inserted into the matrix or into b_e.
- **(ns) TYPING ((NS-ROUTE) cite site; REV 13).** The eventual-ns object
  b_e^{ns}(τ)(σ′) := lim_N μ̂(the reachable ns classes with verdict σ′,
  LUMPED at N via L_{M(N)} │ entering τ) is the (NS-ROUTE)(NS-b)
  lumped-limit RESIDUAL — it sits OUTSIDE the recursion and is NEVER a
  summand of b_e: every finite ns shadow stays inside K_e's CONTINUING
  vanishing-digit columns (no finite read detects ns), so an additive
  b_e^{ns} column would double-count through BOTH K_e β_e AND the exit.
  There is NO licensed additive root-level b_e^{ns} formula (REV 14),
  and none is written here; with (ns-null) closed the residual is 0 and
  (R_e-exact) reads as displayed.

**(K-TRI) Well-foundedness (DERIVED GIVEN DEG-CONS/CL-11).** DEG-CONS
(the per-outcome degree-conservation law, derivable from M1's degree
identity; its per-outcome check against the FULL outcome roster is a
[1v] display duty, CL-11 — V.4 interface item (4) hands the computed-
block instances over): the degree law reads PER MEMBER over the FULL
roster — EVERY m ≥ 2 outcome, halted members included (its display:
"per member, from M1's degree identity"; "the check runs over the FULL
roster"; V.6.1 executes it on the ALL-HALTED rows m_H3/m_H12) — each
member e_j ≥ 1, Σ_j e_j ≤ e; hence at m ≥ 2 EVERY e_j < e (two
same-size children would
need 2e > e; a same-size child with any sibling needs e + 1 > e). So
b_e^split is multilinear in STRICTLY-SMALLER-block solutions only, (R_e)
stays LINEAR within block e (the same-size direction is single-child),
and the induction on e is triangular: blocks solve bottom-up, each
b_e^split leg already solved.

**(K-SUB) The kernel-row reconciliation (DERIVED here from (iv)-PART in
its dual-accepted retyped form + DEG-CONS; a PLAN-SYNC note).** The
plan's §4 gloss "Σ T·G + terminal mass = 1" must be read against
§V-TABLES's retyping (its rev-2 finding 5): the ALL-OFFSPRING marked row
sums to 1 + surplus (PART-2), and NO substochasticity is claimed of THAT
row. But K_e's columns are the SAME-SIZE continuing outcomes only, and
by (K-TRI) the same-size direction is single-child: no digit cell
carries two same-size-e continuing marks, and a same-size mark excludes
siblings. So within the row of K_e each digit cell is counted AT MOST
ONCE, and PART-1 (the digit-cell partition identity, per representative,
countable across heights — [1v] V.3(iv)'s route) gives
  (K-SUB)  Σ_β K_e(τ,β) + Σ_{σ′} b_e^{term,fin}(τ)(σ′)
             + (branching-cell one-step mass, per cell once) = 1,
the third summand being exactly Σ_o J_{τ,o} — the (J-RAT) cell-level
object supplied by PART-1, never the marked offspring row —
every summand ≥ 0 (the ns-bound tail rides INSIDE the K_e term — its
cells are continuing columns). K_e's rows are genuine sub-distributions
with exits typed terminal/split; PART-2's surplus lives ONLY in the
across-sizes marked offspring row, which (R_e) never consumes
(b_e^split consumes each branching CELL once — J_{τ,o} per cell, the
(J-RAT) object, NEVER the marked T·G; the convolution inside the
factor). At n = 3 the surplus vanishes
identically anyway (V.6 rosters). CONDITIONALITY: (K-SUB) is GIVEN the
(iv) ledger below + DEG-CONS (CL-11) + the (m, c) CLASSIFICATION with
its (SCS) clause — REV 6 [pass-6 critical: rev 5's member-count
TRICHOTOMY ("terminal / continuing / branching = m = 1 halted /
m = 1 continuing / m ≥ 2") is REFUTED by the roster — terminal
outcomes can be MULTI-member all-halted (V.6.1's "m_H3: 3 children
(1,1,1)" and "m_H12: (1,2)"), which the trichotomy misrouted to
b_e^split; and DEG-CONS proves only branching ⟹ m ≥ 2, never a
converse. The classification below replaces it; pass 6 verified the
(SCS) arithmetic and the fence SOUND given the m = 1 premise the
classification now supplies definitionally]:

**(m, c) CLASSIFICATION (a DISPLAYED DEFINITION THIS NOTE ADOPTS —
the routing is NOT the roster's own label axis; the roster supplies
the per-outcome DATA on both axes).** Per outcome o at a block-e
state: m := its count of INDIVIDUATED members, τ-halted tracks
INCLUDED ([3t] SIBLING INDEXING); c := its count of CONTINUING
members. Every outcome has m ≥ 1 and 0 ≤ c ≤ m. ROUTING:
  (c = 0, any m)  → b_e^{term,fin}  [ALL members halted; σ′ = v(o)
                    the FULL verdict multiset of all m members];
  (c ≥ 1, m ≥ 2)  → b_e^split      [the cell's J once; halted
                    siblings factor 1 per §T.4's leaf convention,
                    displayed at S.0's b_e^split];
  (c = 1, m = 1)  → a K_e column   [same block: e₁ = e by (SCS)].
EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION: the three predicates
partition {(m, c) : m ≥ 1, 0 ≤ c ≤ m} (c ≥ 1 with m = 1 forces
c = 1). SOURCE DATA, roster-displayed on both axes: the c-axis is
the TERMINAL/CONTINUING labels ("m_H3 ... TERMINAL (3 Hensel
tracks)" vs "m_2+1 ... CONTINUING", V.6.1 (D1)) — a letter label
marks the DESIGNATED branch's continuation, never the routing
(m_2+1 is (m, c) = (2, 1), a split, per its check "m_2+1: (2,1) ✓");
the m-axis is DEG-CONS's executed full-roster member tuples
("m_H3: 3 children (1,1,1)"; "m_H⟨3⟩, m_3: single-child (m = 1, no
branching check applies)" (V.6.1); "m_vv (1,1) ✓; o_double single
child size 2" (V.6.3)) — flank-side clusters and halted tracks are
members.
VERIFIED AGAINST THE DISPLAYED SEMANTICS (two agreement checks):
 (i) TERMINAL COLUMNS TAKE MULTI-MEMBER VERDICT VALUES: σ′ ranges
   over verdict-type MULTISETS (S.0's typing line), b_e^{term,fin}
   sums over v(o) = σ′ with NO displayed m = 1 restriction, and
   V.6.1's absorbing labels are the multi-member instances — m_H12's
   "[1,1]+[1,2]" (two members) and m_H3's three Hensel tracks
   ((1,1)³). The (c = 0) row lands exactly on the displayed columns.
 (ii) K-COLUMN AGREEMENT (the (c = 1, m = 1) bucket vs [1v]'s
   columns): K_e is typed block-e → block-e ([1v] (iv): entry
   K_{(s,α),(s′,β)} with target β a block-e state via (D4)); the
   degree law in its executed FULL-ROSTER per-member form ((K-TRI):
   every m ≥ 2 outcome, halted members included) gives m ≥ 2 ⟹
   every e_j ≤ e − 1 < e ⟹ no member is a block-e state ⟹ o is NO
   K_e column. So [1v]'s columns sit inside the (c = 1, m = 1)
   bucket — "a K-column outcome has exactly one total member"
   (pass 6's missing premise) is DEFINITIONAL under this routing and
   CONSISTENT with [1v]'s column typing by the degree law — and no
   digit cell is counted both in K_e and in the split summand.
Then (SCS), whose premise m = 1 is DEFINITIONAL for the K-bucket:
  (SCS)  a (c = 1, m = 1) outcome's single child inherits the block
         size: e₁ = e — a size-dropping child never comes alone.
DERIVATION (steps unchanged from rev 5 — pass 6 verified them SOUND
given the m = 1 premise; cites verbatim; owners [2a]/[1v], both
dual-accepted).
(1) m = 1 LEAVES NO ROOM TO SHRINK. [2a] SP.1's letter fields: the
flank field types "the horizontal compositions of the window span
outside the read side (the other sides' raw widths, left and right of
the read side)", each side carrying ≥ 1 residual factor
("Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ", ℓ ≥ 1) = ≥ 1 member; and a non-selected factor
of the read side is likewise a member ("the non-selected part of λ is
the residual co-factor"). So m = 1 forces NO flank side (the read side
spans the window: e·ℓ = W) and a SINGLETON residual shape
λ = {(g, μ)}, i.e. g·μ = ℓ.
(2) THE STAGE LAW. [2a] SP.2 (B1)/(B3), citing §B2-DEF: D′ = e·g·D
(D.5: "deg Φ̂ = e·g·deg Φ"; "a recentering is the e = g = 1 case,
D.10") and W′ = μ ("the child window is [0, μ]" — D.8 (BOX)/(VERTEX),
D.10 RS-landing). Hence the child's cluster degree
  W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D
equals the parent's — and cluster size IS the stage product W·D (the
[1v] CTS-S datum S.0's "cells at cluster size e" reads; every V.6
instance displays it: the size-2 block's "distinguished quadratic" at
window (0, v(h₀)), (1, v(h₁)), (2, 0) with D = 1; the root entrance
typings "μ = 2 cluster into the size-2 block", "μ = 3 cluster into the
size-3 block" = μ·e·g·D). So the m = 1 continuing child sits in block
e — (SCS); V.6.3's roster line "o_double single child size 2" is its
displayed instance. ∎
(FENCE: the [2a] SP-DAG rank case "e = g = 1, μ < W(s)" — the window-
shrinking successor edge — is a SPECIES edge, the walked branch's
descent through a (c ≥ 1, m ≥ 2) outcome's selected member; by (1) it
never occurs at m = 1, so no K_e column rides it.) Without (SCS) the
(c = 1, m = 1) row would name a same-block column that need not
exist — a size-dropping single child escaping every summand; WITH it
the summands are EXHAUSTIVE over PART-1's cells by the (m, c)
classification: (c = 0, any m) → b^{term,fin} (σ′ the full verdict
multiset) / (c = 1, m = 1) → the same-block K_e column ((SCS)) /
(c ≥ 1, m ≥ 2) → b^split (the cell's J once). Every probabilistic reading in
S.4 routes through (K-SUB), never through PART-2's marked row.
[PLAN-SYNC FLAG: the plan §4 parenthetical "(Σ T·G + terminal mass =
1)" should cite (K-SUB)'s typed form; owed at the next plan rev.]

**The NINE-input conditionality ledger (= CL-5 of the CAPSTONE LEDGER;
quoted verbatim from plan §4 REV 7; K_e carries all nine tags until each
closes).** K_e's probabilistic reading is conditional on NINE named
inputs — (1) XHD = M4a-X exact height domains, weights, and sums (else
resummed rows sum masses of non-events); (2) D4R.0 disjointness after
height grouping; (3) CTS-M(iv)-PART (else rows are not sub-distributions
— consumed here in the dual-accepted PART-1/PART-2 retyped form, via
(K-SUB)); (4) CTS-M(iv)-REP weighted representative independence =
M2(ii) (else the quotient by τ is ill-defined); (5) CTS-M(iv)-MEAS (else
summands are not masses of disjoint measurable events); (6) CTS-M(v)
HMC (else K_e^k does not factor the whole-template height domains —
OPEN kernel); (7) CTS-M(ii) ACT (else empty cells at wild p corrupt
rows, denominators, determinants); (8) CTS-M(iii) INIT + ENT-COUNT
(else no product is tied to a cylinder mass or a full count — the
per-entrance-shape form: ι_{e,ε,β₀} and I^ent_{ε,β₀} with ENT-AGG and
INIT-RAT); (9) the CTS-M(vi) COMP-TYPING duty — heights summed exactly
once, through the (COMP-h)→(COMP-Σ) passage (else the height coordinate
is double-counted). Every probabilistic claim in S.4/SQ.2 is about K_e
restricted per CTS-M(ii) to the ACTIVE block.

### S.1 XRB = RS.0(β) — the height-elimination theorem (CL-9; this note's owned derivation, UPSTREAM of both PCI substitution sites in the consumption DAG)

**The hypothesis being discharged ([3t]'s display, verbatim charge).**
(XRB): for every block (e, τ), the entrance-free conditional
continuation law from a concrete state of type τ at entrance height
h_ent is h_ent-INVARIANT (the height-shift conjugacy), so β_{e,τ}
carries no height index. [3t]-COND consumes XRB HYPOTHETICALLY (a
displayed item on its acceptance record); THIS section proves it under
the displayed hypothesis set below; [3t]-FULL records the discharge at
the acceptance-only edge [3] → [3t]-FULL (no [3t]-time consumption of an
unaccepted [3] theorem — the DAG stays acyclic).

**RS.0(α) LUMPABILITY — CONSUMED, not proved.** = CTS-M(iv)-REP =
M2(ii): the MEASURED row (T·G) is identical from every representative
of the cell (weighted form; cardinality equality is insufficient).
[1v]'s clause, XHD-conditional there; its blocking probe is
STATE-probe-2 (a same-type failure surviving adjudication and one
𝒯-refinement is R2's wall).

**RS.0(β), proved in two steps.**

**(β-1) MARGINAL INVARIANCE — DERIVED, GIVEN XHD-w + (XHD-u) + XHD-d
(owner [2b]).** CLAIM: for every finite single-branch template γ from
cell (s, α) and every height point h, the conditional mass — given the
entrance cylinder of ANY concrete state x of type τ = (s, α), under ANY
entrance shape ε (any h_ent(ε)) and ANY admissible history — of one
continuation realizing (γ, h) is
    m_γ(h) := ∏_i T_{m_i,o_i}^{β_{i−1},β_i} · g^{β_{i−1},β_i}_{m_i,o_i}(h_i)
              for h ∈ H(γ), and 0 otherwise
— ONE function of (γ, h), free of x, of h_ent, and of the history.
DERIVATION, each move a cited [1v]/§C display: (i) the per-assignment
step mass is XHD-w's g, which is BY ITS DISPLAY the C.1.5 fresh-volume
ratio "at ANY representative of α under ANY admissible history reaching
it" — the h_ent-quantifier is built into the hypothesis; (ii) counts
and constants factor through retained data only — (XHD-u)(u-R): the
ratio and the count T_γ(x, h) depend on x and its history only through
(α, β⃗, m⃗, o⃗, h); (iii) (XHD-u)(u-T) height rectangularity makes the
per-h count the h-independent ∏_i T; (iv) the DOMAIN is representative-
free — XHD-d's TWO-SIDED exactness is quantified over EVERY
representative ((no stray): h ∈ H(γ) ⟹ T_γ(x, h) > 0 for every x of α;
(no orphan): realizability from some x ⟹ h ∈ H(γ)) — so WHICH h are
realizable from x does not depend on x, hence not on h_ent; (v) the
chain multiplies per-step conditional masses along γ by §C C.1.5's
conditional chain (accepted; NO independence assumption). ∎
This IS the height-shift conjugacy in the plan's bisimulation reading:
a state entered at h_ent + 1 differs from one entered at h_ent by one
admissible-history layer, and (i)–(iv) say the retained cell is a
sufficient statistic for every finite single-branch marginal.
HYPOTHESES: XHD (w, u, d) — nothing else; note (u-R)/(u-T) are exactly
the clauses [1v] flags as NOT §C-derivable (lumpability assertions about
histories §C never compares) — the [2b] fence is load-bearing here.

**(β-2) THE LIFT — fixed-height to resummed, then marginals to the
subtree value.** Two parts, conditionality strictly increasing.
(β-2a) RESUMMED ENTRIES (DERIVED, GIVEN additionally XHD-s): summing
(β-1) over h ∈ H(γ¹) per listed pairwise-disjoint component gives the
kernel and terminal-column entries T·G, G := Σ_h g(h) ∈ ℚ(q) — each
fixed-height summand is h_ent-free by (β-1) and the domain is template-
attached (XHD-d), so the RESUMMED entries are h_ent-free. No HMC at
k = 1. Multi-step: the unfactored whole-template sum (COMP-hΣ)
Σ_{h ∈ H(γ)} ∏_i T·g(h_i) is h_ent-free by the same two moves — the
INVARIANCE does not wait on HMC; only the FACTORIZATION of that sum
into ∏_i (T·G) is HMC's open duty (CL-5 item 6), and its tag rides
every K_e-power claim as before. This is the fixed-height → resummed
passage on the K_e entries the plan assigns to this note, closed GIVEN
XHD alone.
(β-2b) THE SUBTREE VALUE (DERIVED, GIVEN additionally (JC-INV) (NEW,
displayed below — the joint-lumpability face) + the [3t] package
— (SIB) (CL-10, open), (JC-multi) at multi-side sites, TB-CAP/VP per
their [3t] statuses — and [2r] REL.2(a)/(b)/(d) at base-changed legs
(CL-8, open); (ns) scope per (NS-ROUTE)): the defining event of
β_{e,τ}(σ′) on the (R_e-lump) typing is the 𝒯^fin completion event — a
COUNTABLE disjoint union, over complete finite subtrees T with leaf
multiset of type σ′, of tree fibers (disjoint because T_can^τ is a
choice-free function of f), each fiber a finite intersection of finite-
level digit-cell conditions (TREE-N's structure clause). Conditional on
the entrance, TREE-EXP expands each fiber mass into per-site factors,
and EVERY factor is h_ent-free: unbranched-segment and terminal-site
factors are (β-1) instances; joint-cell factors jvol(c_s │ Σ) —
INCLUDING the selection law of the branching cell itself — are
h_ent-free GIVEN the NEW displayed hypothesis (rev 2, pass-1 finding
2, the formerly unlicensed joint-lumpability step):
    (JC-INV)  per read, the JOINT digit-cell conditional law given
    the entrance (all cells of the read jointly, branching cells
    included) is ONE function of the retained state — invariant
    across representatives and admissible histories, h_ent included.
(u-R) does NOT supply this (it is single-branch/per-assignment: equal
marginals can coexist with different correlations or different
branching-cell probabilities), and (SIB) starts only AFTER
conditioning on the branching cell, so it supplies no selection law.
(JC-INV)'s owner is [2b], alongside XHD-u's lumpability clauses; a
surviving (JC-INV) failure adjudicates as R2's lumpability channel
(one 𝒯-refinement round, then wall); branching-
site sibling products are (SIB)'s, whose per-child factors are, after
REL.2(a)/(b)/(d)'s identification, O_{δ_j}-masses of the base-changed
theory — objects carrying NO ambient h_ent by construction (the
transported data is Θ_j's, [2r] R.1). A countable positive sum of
h_ent-free terms, bounded by 1: countable additivity transfers the
invariance to the total. Hence β_{e,τ} carries no height index on the
lump typing; the (R_e-exact) reading inherits it GIVEN (ns-null)
(closed, tag displayed). ∎

**(XRB) STATUS LINE.** PROVED-UNDER-HYPOTHESES, with the set displayed:
XHD (w/u/d/s — owner [2b]; discharge = [1v]-FULL) + (JC-INV) (NEW at
rev 2 — the joint-lumpability face, owner [2b]) + (SIB)/(JC-multi)
(CL-10, open) + TB-CAP/VP ([3t] §T.2 per-clause statuses) +
REL.2(a)/(b)/(d) (CL-8, open) + (ns-null) (CLOSED). PCI is consumed
NOWHERE above (TREE-EXP performs no β-substitution — [3t] REV 13
scope), so no cycle: the INTERNAL PROOF ORDER is satisfied in its
binding CONSUMPTION form (rev 3, pass-2 finding 9) — in the
consumption DAG RS.0(β) sits UPSTREAM of both PCI β-substitution sites
(b_e^split at S.0 — a licit textual forward reference from a
definition — and RS.1-SH at S.2), both sites cite (XRB, S.1), and this
proof consumes neither site; textual position is presentation, not
order. ADJUDICATION: a surviving h_ent-dependence at any
probe is R2's lumpability channel (one 𝒯-refinement round, then wall),
never a (SIB) failure.

### S.2 RS.1 — the three-clause aggregation identity (theorem-under-hypotheses; the CL-17 duties displayed, duty (i) derived)

**Statement (REV 10/13 form).** GIVEN the [3t] package (TREE-EXP fin/ns
+ TREE-N + ONE-F; (SIB), CL-10; TB-CAP/VP), the S.0 nine-input ledger
(CL-5), XRB (S.1, proved above), and [2r]'s REL.2 obligations at every
base-changed leg (CL-8, open):

  (RS.1-DEEP)   per block (e, τ):
      β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)
    — the ENTRANCE-FREE conditional subtree value (S.0 typing), with
    b_e = b_e^{term,fin} + b_e^split consuming every DEEP (in-block)
    split multilinearly; solvability of the inverse is RS.3's (S.4).
  (RS.1-SH)     THE SHALLOW CONVOLUTION (the base clause):
      R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ … ⊎ σ_{k(Ŝ)}}
              ∏_{i=1}^{k(Ŝ)} β_{e_i(Ŝ),τ_i(Ŝ)}(σ_i)(q^{δ_i})
    — Ŝ over the finite-up-to-heights family of SHALLOW TREE SHAPES
    (the [1] root cascade from the empty prefix to every block entrance
    — entering reads INCLUSIVE, per (BDY) — and every shallow τ-halt,
    splits included; finiteness from [2a]);
    W_Ŝ ∈ ℚ(q) the resummed shallow tree mass (C.1.5 node volumes ×
    CTS/[1] counts × XHD-s shallow height sums, (SIB)'s COUNT face
    across shallow splits); σ₀(Ŝ) the verdict multiset of Ŝ's shallow
    τ-halted leaves ((NS-ROUTE): shallow leaves entering W_Ŝ's finite-
    level machinery are (τ-irr)/(τ-hen); an ns-leaf shallow shape has
    no finite-level mass and contributes 0 GIVEN (ns-null) — the drop
    displayed once at (TGT)); the product over Ŝ's k(Ŝ) block entrances
    licensed by (SIB) at every shallow branching cell, with PCI
    substituting β_{e_i,τ_i} for each subtree mass — XRB's leg
    discharged by S.1, [2r]'s type dictionary at δ_i > 1. The ROOT
    read's own factorization (the L3 Gauss/necklace layer) is
    RS.1-SH's outermost instance, its sibling law (SIB) at η = ∅ —
    authority the MONTES-L1 cite (D4R0K O4); the accepted JOINT-D1 is
    single-cluster EVIDENCE for it, never the theorem.
  (RS.1-MARKED) the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed
    MARKED-entrance total (post-split marks, CTS-M(iii) POST-SPLIT) —
    the object (COMP-AGG) and the gates consume; NEVER summed into R_σ.

CONVERGENCE (unconditional): the outer sum is over complete finite
realizable canonical TREES with disjoint fibers (T_can^τ choice-free),
a positive series bounded by 1 — unconditionally convergent, all
rearrangements licit (Tonelli). The X.1b envelope is needed only for
RATES ([4]'s X.2/SQUEEZE), never for convergence here.

**ROUTING (prove-on-display; ledgered at CL-17).** Every split of
T_can^τ(f) is consumed at EXACTLY ONE multilinear site — DEEP splits at
b_e^split (RS.1-DEEP), ROOT/SHALLOW splits at RS.1-SH's convolution —
and BOTH sites act BEFORE any linear marked aggregation (ENT-AGG/the
ι-pairing applies only to post-split marks). No split is ever a sum of
separately-inserted child entrances: the failure mode ι_{e₁}^Tβ_{e₁} +
ι_{e₂}^Tβ_{e₂} is excluded by construction, not by cancellation.

**(CUT-WD) The shallow-cut decomposition — CL-17 duty (i), DERIVED here
GIVEN its predicate supply.** SUPPLY (fenced): the ENTRANCE PREDICATE —
"ν is a BLOCK-ENTRANCE node" — is CELL data: ν's entering step is the
designated continuing branch of an entrance shape ε into some (e, β₀)
(CTS-M(iii)'s object, whose P̂-component is SHALLOW by its definition);
the predicate's computability per node rests on CTS-M(i)'s computed
partition (CL-13) and the (iii) entrance-shape family — [1v]/[2b]
territory, cited not proved. GIVEN the predicate:
 (CUT-1) per branch: on any root-to-leaf path of a complete tree T the
   entrance nodes are linearly ordered; the FIRST one (if any) is
   unique. A branch with no entrance node τ-halts in the shallow layer
   (its leaf feeds σ₀(Ŝ)).
 (CUT-2) node trichotomy: a node ν is SHALLOW iff its root-path
   contains no entrance node at-or-before ν; otherwise ν lies at-or-
   below the UNIQUE first entrance on its root-path — READ/MASS
   ownership at the boundary is (BDY)'s (S.0): the first entrance
   node is block-side as a state index, its ENTERING read is
   entrance-side mass (W_Ŝ here), so the node rule and the edge rule
   agree with no omitted or double-charged read — (unique by (CUT-1);
   common to every branch through ν, since it sits on ν's root-path).
   So every node of T lands in EXACTLY one of: the shallow layer, or
   exactly one entered block subtree — EXHAUSTIVE and NONOVERLAPPING,
   no node orphaned, none double-charged. Deep-recursion splits are
   never re-classified as shallow: b_e^split consumes them in-block by
   the ROUTING law (their children are convolution legs, not new
   entrances of RS.1-SH).
 (CUT-3) the assignment T ↦ Ŝ(T): Ŝ := T's shallow layer with values
   and heights forgotten, entrance and halt boundary data retained — a
   CHOICE-FREE function of T, so every complete tree carries exactly
   ONE shallow shape. ∎
CL-17 duty (ii) — that every W_Ŝ is PRODUCED by the stated rational
machinery (C.1.5 node volumes × CTS/[1] counts × XHD-s shallow height
sums, with (SIB)'s COUNT face across shallow splits) — remains OPEN
here: the machinery is displayed, ENT-COUNT/INIT-RAT are its [1v]-side
burdens, and the capstone may not be accepted while it is open (CL-17).

**Proof route (the plan's `unroll`-then-`resum` sketch, restated as this
note's program — scope per REV 10).** Theorem C gives per-branch masses;
tree fibers partition the decided set (ONE-F); TREE-EXP (GIVEN (SIB))
expands fibers into per-node products — C.1.5 chains along unbranched
segments, sibling products at branching cells, REL.2 base-changed legs.
The MARKED clause: group branches by (entrance shape ε, template γ,
height point h); at each height point the FIXED-HEIGHT identity is
(COMP-h) (the step factor is the monomial g, never G; the initial
factor ι_{e,ε,β₀} never omitted); then the ONE height sum over XHD-d's
exact classes ((COMP-hΣ)); the factorization into ∏(T·G) ONLY through
HMC ((COMP-Σ) — after which NO further height sum occurs anywhere);
then the entrance sum via ENT-AGG/(COMP-AGG) against the entrance-
independent continuation ((iv)-REP) — the ONE place ι_e is formed and
h_ent is summed; the depth direction is the regular path language of
the finite CTS automaton — a depth-k chain is the k-fold matrix product
(RS.0), and the Neumann fixpoint (I − K_e)^{−1} is the block solve, not
a new sum; positivity licenses every regrouping. SKETCH SCOPE: this
establishes RS.1-MARKED. The DENSITY clauses RS.1-DEEP/RS.1-SH regroup
the SAME per-node TREE-EXP expansions PER SHALLOW SHAPE Ŝ — the tree
product cut at the block boundary per (CUT-WD) — never through ι.
D4R.1-SUM/D4R.4-SUM quantities are consumed as MARKED sums, never as
f-event masses (mult ≡ 1 instances displayed where claimed).

### S.3 RS.2 — rationality with fixed coefficients (Cramer/adjugate over ℚ(q))

DERIVED, GIVEN the cited rationality burdens (each named): every
coefficient of (R_e) is ONE FIXED element of ℚ(q), the same at every
prime. Inventory:
- K_e/b_e^{term,fin} entries: T is one polynomial of degree ≤ W_loc(m)
  and each cell size one polynomial of degree ≤ W_state(s), valued
  correctly at every prime power — CTS-M(iv)-POLY (CL-6, with V.2's
  EXPONENT-MAP AUDIT); G ∈ ℚ(q) with geometric denominators
  (1 − q^{−a}) — XHD-s over the listed pairwise-disjoint components.
- ι_e entries: INIT-RAT — CITED as [1v]'s displayed burden (finite
  entrance-shape family, per-shape ENT-COUNT polynomials of degree
  ≤ W_ent(ε), XHD-s shallow sums, (ENT-U)); NOT proved here or there
  yet.
- b_e^split legs: strictly-smaller-block β's at argument q^{δ_j} —
  ℚ(q)-membership by the triangular induction on e ((K-TRI)): each leg
  is an already-solved block's entry composed with q ↦ q^{δ_j} (which
  maps ℚ(q) → ℚ(q)); the ARGUMENT convention is [2r] (e2) (δ absolute);
  NUMERIC evaluation of a leg at a pool q₀ = p^{δ_j} is guarded by
  S.4's PER-POOL E0/ACT (rev 3), never by this symbolic clause;
  and the cell-level coefficients J_{τ,o} ∈ ℚ(q) by (J-RAT) (S.0's NEW
  named burden, owner [1v]/[2b] — CITED, not proved; finding-1 ripple).
THE SOLVE: GIVEN det(I − K_e) ≠ 0 in ℚ(q) (S.4), Cramer/adjugate gives
  β_e = adj(I − K_e) b_e / det(I − K_e)
entrywise — finitely many +/×/÷ over ℚ(q): every β_{e,τ}(σ′) is one
fixed rational function. W_Ŝ ∈ ℚ(q) per CL-17(ii) (open); RS.1-SH's
outer sum is over finitely many height-forgotten shapes ([2a]) — so
R_σ ∈ ℚ(q), one per σ. p-INDEPENDENCE: no coefficient mentions p; p
enters ONLY at evaluation q = p. Per-shape emptiness at wild p is
polynomial vanishing (CTS-M(ii); W1's pool-size effect), handled by the
ACT semantics, never by changing a coefficient. HONESTY (REV 2,
standing): all of this rests on [1v] Theorem VAL in its CTS-M form — it
does NOT follow from Theorem C + Claim 4.3; the torus-lemma bridge is
dead. If VAL.3 is ever entered, RS.2 and the whole block system are
re-derived in [3′] (plan §2v/R8). INIT-RAT's citation is this clause's
one deliberate forward dependence — displayed, owner [1v]/[2b].

### S.4 RS.3 — solvability; ESCAPE(E0), the displayed open kernel

> **ESCAPE(E0) (OPEN KERNEL — owner THIS note; CL-1; per-fixed-POOL,
> on the ACTIVE block; widened at rev 3, pass-2 finding 8).** For each
> RELEVANT POOL q₀ = p^δ — δ ranging over 1 AND every base-change
> index a β_{e_j,τ_j}(q^{δ_j}) leg of b_e^split or RS.1-SH consumes
> ([2r] BASE-INDEX CONVENTION + (e2), δ ABSOLUTE; δ = 1 the base
> instance) — and each e ≤ n, with A(q₀) := the CTS-M(ii) active
> submatrix of K_e(q₀): A(q₀)^k 𝟙 → 0 as k → ∞ — the k-step
> still-in-block mass from every REALIZED state of the O_δ theory
> tends to 0 — hence, A(q₀) being a FINITE nonnegative matrix,
> ρ(A(q₀)) < 1, the Neumann series converges, and (I − A(q₀))^{−1} ≥ 0.
> Scope: realized states only; formal rows of cells empty at q₀ are
> OUTSIDE E0 and guarded by CTS-M(ii-c) — whose removable-pole/
> ACTIVE-VALUE AGREEMENT burden holds likewise PER POOL q₀ (never only
> at q₀ = p): symbolic nonvanishing of det(I − K_e) does not prevent a
> zero or an uncancelled pole at an individual p^δ.

ROUTE E0 (displayed; NO derivation claimed — this is the kernel):
X.3 (CL-4 — [5]'s a.e. termination, itself conditional per §X-EXHAUST's
CL-4 record line) + the EXACT finite kernel identification (the nine
CL-5 inputs) + (K-SUB)'s sub-distribution typing give: A^k 𝟙 = the
still-in-block-after-k masses (a PROBABILITY per (K-SUB) — its (m, c)
classification types every K-column as (c = 1, m = 1), the same-size
single-child direction, so the k-step in-block object is a
branch probability, never a marked-offspring expectation) ↓ μ(never
exits the block) = 0 by monotone convergence. At δ > 1 the SAME route
reads verbatim over the base-changed theory O_δ (its X.3, its (K-SUB)),
ingredients transported per [2r] — per-pool legs; no uniformity in q₀
is needed anywhere downstream. (e3)-FENCE (rev 3, displayed): REL.2(e3)
is an IDENTIFICATION of the evaluated β with an O_δ-mass — it
PRESUPPOSES that the evaluated entry β_{e_j,τ_j}(q^{δ_j}) is
well-defined (per-pool E0/ACT, THIS kernel) and cannot SUPPLY that
well-definedness. ESCAPE-UNIF (the uniform
(B, c) strengthening) stays OPEN in the plan and is CONSUMED BY
NOTHING; no consumer may cite it silently.

(ii) det(I − K_e) ≠ 0 in ℚ(q), DERIVED GIVEN E0 + (iv)-POLY: at
all-active primes (cofinitely many — only finitely many primes are
roots of some not-identically-zero cell-size polynomial) K_e(p) = A and
ρ(A) < 1 gives det(I − A) ≠ 0; a rational function vanishing at
infinitely many prime evaluations is 0, so det(I − K_e) ≠ 0 in ℚ(q) —
the SYMBOLIC block solve is licit. EVALUATION IS PER POOL (rev 3):
symbolic det ≠ 0 prevents no zero or uncancelled pole at an individual
q₀ = p^δ. At every NON-all-active pool q₀ (the wild pools; finitely
many per e) the symbolic solve is read on the ACTIVE subsystem:
CTS-M(ii-c)'s ACTIVE-VALUE AGREEMENT burden (weakened form, REV 7),
PER POOL — the junk-block determinants det(I − D_{q₀}) are RECORDED
(a zero is a FINDING, not by itself a FAIL; a blanket det(I − D_{q₀})
≠ 0 is NOT required), and the sealed check that the evaluated object's
q₀-value (R_σ(p) at δ = 1; a β_{e_j,τ_j}(p^{δ_j}) leg at δ > 1 — after
cancellation where needed) equals the active-subsystem solve there
must pass BEFORE it may be read off; a pole SURVIVING cancellation at
a wild pool is (ii-c)'s FAIL. RS.3 and SQ.2 consume E0
ONLY (each at a fixed pool); both are CONDITIONAL-ON-E0 until the
kernel closes, and E0 is itself conditional on X.3 + the nine inputs.
RS.3 cites X.1b NOWHERE.

PROBE ROSTER (E0's refuters, front-loaded):
 (a) ESCAPE-probe layer 1 — the SYMBOLIC CLOSED-CLASS REFUTER (the
   genuine falsifier): from the sealed active kernel at q = p, compute
   A's directed transition graph and its strongly-connected components;
   any CLOSED class — TOTAL ROW MASS INSIDE THE CLASS = 1 on every
   member, i.e. zero one-step terminal mass AND zero branching/split
   exit mass AND no A-edges leaving (rev 2, pass-1 finding 7: split
   mass is an exit that appears as a ROW DEFICIT, not as an A-column
   or terminal column, so "no out-edges + no terminal mass" alone
   does not make the class stochastic) — refutes E0 at that p
   OUTRIGHT (genuinely stochastic on the class, hence ρ = 1),
   finitely and conclusively.
 (b) ESCAPE-probe layer 2 — the k = 1…8 per-type still-in-block decay
   census: CONSISTENCY-CLASS ONLY — it refutes sealed finite-depth
   predictions, never the asymptotic E0 (arbitrarily delayed escape is
   E0-compatible); a row stabilizing above 0 is a FINDING to
   adjudicate.
 (c) RESUM-n3's ACT layer (S.7): sealed Act_2/Act_3 lists, verified
   entry vanishing into inactive cells, det(I − D_{q₀}) recorded, the
   active-value agreement check — PER POOL. SCOPE (rev 3, pass-2
   finding 8): the gate TESTS the base pools q₀ = 2, 3 and, AS
   FEASIBLE, the first base-changed pool q₀ = 4 = 2² (the δ = 2 legs
   n = 3's shallow convolution consumes); the seal artifact RECORDS
   the tested-pool list; every other relevant pool is UNTESTED there
   and rides the per-pool kernel above — the probe roster narrows no
   quantifier of E0.

### S.5 RS.4 — the checksum ((ns-null)-closed, X.3-conditional form)

  (RS.4)  Σ_σ R_σ = 1  identically in q.

ROUTE (DERIVED, GIVEN its inherited set): at each prime p the decided-
mass series totals 1 — X.3's density form (CL-4; the (ns) residual
contributes 0: (ns-null) CLOSED, tag displayed; countability via
(NS-c)'s symbolic indexing); RS.1 equates that series with Σ_σ R_σ(p);
a rational function equal to 1 at infinitely many prime powers is
identically 1. STANDING TAG (inline, per the plan's REV 4 rule): RS.4
inherits EVERY condition of the block solve — ESCAPE(E0) (CL-1), the
nine RS.PRE inputs (CL-5), RS.1's hypothesis set (CL-10/CL-17/CL-8 +
XRB's displayed set), and X.3 (CL-4; the total-mass identity needs X.3,
NOT the quantitative envelope — X.1b is tagged only where env constants
are consumed, i.e. nowhere in this note) — AND the full RS.2
RATIONALITY chain (rev 2, pass-1 finding 6): CTS-M(iv)-POLY (CL-6),
XHD-s, INIT-RAT, CL-17(ii)'s rational W_Ŝ, and (J-RAT). Reason: RS.1 +
the nine inputs give only the PRIMEWISE mass equality; that Σ_σ R_σ IS
one fixed rational function — the object the infinitely-many-values
argument applies to — is RS.2's conclusion, so the checksum consumes
RS.2 wholesale, hypotheses attached. Its acceptance record, like
this note's, may NOT be marked unconditional before those close. It is
the cheapest layer invariant of every gate below.

### S.6 Honest perimeter (derived vs fenced vs hypothesized; acceptance)

DERIVED here, each under its displayed hypothesis set (site in
brackets): XRB = RS.0(β) [S.1 — GIVEN XHD + (JC-INV) +
(SIB)/(JC-multi)/CL-10 + TB-CAP/VP + REL.2(a)/(b)/(d)/CL-8 +
(ns-null) closed]; the fixed-height
→ resummed passage on the K_e entries [S.1 (β-2a) — GIVEN XHD alone];
(K-TRI) and (K-SUB) [S.0 — GIVEN the (iv) ledger + DEG-CONS/CL-11 (its full-roster per-member degree law) + the (m, c) CLASSIFICATION (rev 6: a displayed definition THIS NOTE adopts, exhaustive by construction; the roster supplies the two axes; K-columns = the (c = 1, m = 1) row, agreement with [1v]'s column typing derived) + its (SCS) clause (premise m = 1 definitional; the flank/stage derivation pass-6-verified; the window-shrinking edge fenced as a species edge through a (c ≥ 1, m ≥ 2) outcome)];
(CUT-WD) = CL-17 duty (i) [S.2 — GIVEN the CTS-M(i)/(iii) entrance-
predicate supply, CL-13]; RS.2's fixed-coefficient rationality [S.3 —
GIVEN (iv)-POLY/CL-6 + XHD-s, INIT-RAT + (J-RAT) cited, S.4's det]; RS.3(ii)'s
det ≠ 0 [S.4 — GIVEN E0]; RS.4's rational-identity step [S.5 — GIVEN
its inherited set].
OPEN KERNELS owned by this note: ESCAPE(E0) (CL-1; PER-POOL q₀ = p^δ
form at rev 3 — the quantifier the β(q^{δ_j}) legs consume; probes
specced, none run); CL-17 duty (ii) (the per-shape W_Ŝ production).
CONSUMED OPEN ITEMS, owner elsewhere (cited, never proved here): the
NINE CL-5 inputs (XHD/(ENT-U) — [2b]; HMC — [1v]'s open kernel, probe
pinned there; INIT-RAT/ENT-COUNT — [1v] burdens); (JC-INV) ([2b] —
the S.1 joint-lumpability face, NEW at rev 2); (J-RAT) ([1v]/[2b] —
the S.0 cell-level branching-mass burden, NEW at rev 2);
(SIB)/(SIB-STEP) + (JC-multi) (CL-10, [3t]); REL.2(a)–(e) (CL-8, [2r] — every β(q^δ) leg
cites (e1)–(e5)); DEG-CONS's full-roster check (CL-11, [1v]); X.3
(CL-4, [5]); CTS-M(iv)-POLY (CL-6, [1v]); M2(ii)'s probe =
STATE-probe-2 (blocking, plan §4).
[PLAN-SYNC FLAG (rev 3, pass-2 finding 10) — the owner-side interface
for the two rev-2 hypotheses. The plan's CAPSTONE LEDGER is OWED TWO
NEW CL-ROSTER ENTRIES: (J-RAT) — owner [1v], deliverable the PER-CELL
rational tables (per branching digit cell of each outcome class o at
each state τ: the cell-count polynomial per the (iv)-POLY pattern +
its XHD-s height sum, i.e. J_{τ,o} ∈ ℚ(q) entrywise) — a deliverable
BEYOND PART-1's TOTAL cell-partition mass, which is all [1v] currently
displays; and (JC-INV) — owner [2b] (the joint-lumpability face,
alongside XHD-u's lumpability clauses). The owner notes' NEXT REVISION
ROUNDS must record these deliverables on their side; §V-TABLES and
§H-DOMAINS are ACCEPTED texts and are NOT edited from here — the
plan's ledger is the cross-note authority through which the
obligations bind.]
TYPE FENCES, binding on every consumer: ι_e^T(I − K_e)^{−1}b_e is
μ̂-typed (NEVER a density; R_σ is RS.1-SH's object); no finite ns
column exists anywhere ((NS-ROUTE)); heights sum EXACTLY ONCE (CL-5
item 9); no source-mass division; equating any μ̂ object with an
f-event mass outside [3t]'s displayed conversion is a TYPE ERROR.
ACCEPTANCE (the plan's REV 15 ruling, restated so no record can
inflate it): this note may NOT be accepted before (1) STATE-probe-2
PASSES (the vtx-varying M2(ii) regime, plan §4 spec — it directly
tests RS.0(α)'s supply), (2) [1v]-FULL is RECORDED (the XHD discharge
upon [2b]'s acceptance), and (3) RESUM-n3 PASSES (S.7). This draft
asserts NO acceptance-level claim; XRB's discharge at [3t]-FULL is an
acceptance-only edge, recorded only when [3] itself is accepted.
CONSUMER MAP: RS.0(β) → CL-9 (+ [3t]-FULL's second discharge); the
K_e ledger → CL-5's cite sites; RS.2 → CL-6's consumer; E0 → CL-1
(RS.3 here, SQ.2 at [4]); RS.1 → CL-17; RS.4 → the capstone's checksum
layer; b_e^split/RS.1-SH's PCI citations → CL-10/CL-8/CL-9.

### S.7 Gate RESUM-n3 (SPECIFIED — seal artifact owed, nothing run) and the blocking probes

The headline gate (plan §4, REV 2 form + the REV 6/7 ACT layer). Solve
(R_e) for n = 3 symbolically. SEAL BEFORE ANY CENSUS:
 (i)   the FIVE rational functions R_σ, σ ∈ {(1,1)³, (1,1)+(1,2),
   (1,3), (1,1)+(2,1), (3,1)};
 (ii)  their values at p = 2, 3 (wild) and 5, 7 (tame), and the
   checksum Σ_σ R_σ = 1;
 (iii) the exact finite-level partial sums by depth;
 (iv)  THE ACT LAYER: the sealed active-state lists Act_2/Act_3; the
   verified vanishing at p = 2, 3 of every entry into an inactive
   cell; the junk-block determinants det(I − D_{q₀}) RECORDED at each
   tested pool (a zero is a FINDING, not by itself a FAIL); and the
   sealed check that each R_σ's wild-p value — after cancellation
   where needed — equals the ACTIVE-subsystem solve there (a pole
   SURVIVING cancellation = CTS-M(ii-c)'s FAIL, adjudicated before any
   density comparison). POOL SCOPE (rev 3, pass-2 finding 8): this
   layer runs at the base pools q₀ = 2, 3 and, AS FEASIBLE, at
   q₀ = 4 = 2² (the δ = 2 legs n = 3's shallow convolution consumes);
   the seal artifact RECORDS the tested-pool list; untested relevant
   pools ride S.4's per-pool kernel — the gate narrows no quantifier;
 (v)   ONE END-TO-END SOLVE vs A CENSUSED DEPTH SERIES (the task's
   added layer, typed CONSISTENCY): the theory-side depth-k partial
   sums of the block solve (K_e-powers at q = p, k through 8 at p = 2
   and through 5 at p = 3) sealed against the censused per-depth
   decided masses — depth attribution uses the extractor under test,
   so this layer is exact but NOT discriminating (REV 3
   reclassification).
SEAL SEMANTICS (rev 2, pass-1 finding 3 — the pass-1 status
"SEALED-NEW" overclaimed: a protocol is not a seal): the list
(i)–(v) is the seal PROTOCOL. A seal EXISTS only when a
referee-readable artifact (house pattern:
RESUM_N3_SEALED_PREDICTIONS.md) records the CONCRETE contents — the
five rational functions, their four-prime values + the checksum, the
integer/rational depth partial sums, the Act_2/Act_3 lists, the
junk-block determinants — derived from THIS note's displayed
(R_e)/RS.1-SH machinery WITHOUT consulting the census implementation
under test, committed BEFORE any census runs. Until that artifact
exists the gate status is SPECIFIED, not SEALED: a referee must be
able to reconstruct the comparison target from note + seal alone.
DISCRIMINATING layer (exact — the gate-design rule): decided_σ(N) by
EXHAUSTIVE enumeration (p = 2: N ≤ 8, 2²⁴; p = 3: N ≤ 5, 3¹⁵), types
from the PARI `factorpadic` oracle (`verification/quartic_oracle.py`
pattern) — EXACT integer equality per (σ, N) against the sealed theory
totals; oracle types are extractor-independent. CYLINDER DECISIVENESS
(rev 2, pass-1 finding 4 — enumeration mod p^N counts residue BOXES;
one representative's factorization does not by itself type its box):
 (ORC-1) a box is COUNTED into decided_σ(N) only with a CERTIFIED
   determination radius: a displayed classifier-independent criterion
   (route: the Krasner/discriminant bound comparing v_p(disc f_rep)
   against N; the exact inequality + its citation is a SEAL-TIME
   DISPLAY DUTY, owed before the gate may run) certifying the type
   constant on the WHOLE cylinder;
 (ORC-2) every box failing (ORC-1) — including v_p(disc f_rep) at or
   above threshold, disc = 0 at working precision, or any factorpadic
   precision failure — goes to an explicit UNRESOLVED bin, sealed as
   its own count, NEVER counted into decided_σ(N);
 (ORC-3) the PARI-output → σ map is displayed at seal time: σ := the
   multiset of (e_i, f_i) of the certified factorization;
 (ORC-4) the equality target is TYPED: certified-oracle-decided boxes
   vs the sealed theory totals for the CLASSIFIER-decided set at
   level N; both symmetric-difference counts (oracle-certified but
   not classifier-decided, and conversely) are sealed, and their
   non-emptiness is an adjudication FINDING before any density
   comparison.
Any exact mismatch surviving adjudication is STRUCTURAL (plan §8
R1/R2).
CONSISTENCY layers (labeled non-discriminating): the depth rows ((v));
10⁶–10⁷ sampled cubics at all four primes within EXHAUST-tail +
σ-bands; `om_density_engine.alpha_full(3)` and `reconcile_om_bcfg.py`
(RS.5's engine agreement — the engine shares the value-count formulas,
so this is CONSISTENCY, never independent evidence). CAVEAT ON n = 3's
degeneracies, displayed: at n = 3 the PART-2 surplus vanishes
identically and the deep convolution is thin (two continuing clusters
need degree ≥ 4); the n = 2 instance is the 1×1 geometric series
(denominator q² + q + 1). RESUM-n3 therefore exercises the SOLVE, the
ACT semantics, and the checksum — the value-kernel and μ ≥ 2 machinery
are gated at n = 5 elsewhere ([1v] V-n5 duties; plan §0's gate-design
rule).
BLOCKING PROBES (not layers of this gate, but acceptance-blocking):
STATE-probe-2 (plan §4 spec: p = 2 monic sextics, R₀ = ψ²·χ, the
vtx-varying twisted cells; REQUIRED PASS before [2b] STATE-GEOM or
THIS note may be ACCEPTED; seal = the per-τ conditional rows in their
[1v]-COND definable form); the ESCAPE-probe layers (a)/(b) of S.4
(exploration-class, front-loaded — layer (a) is E0's genuine
falsifier).

STATUS: drafted 2026-07-27 per the REV 15 drafting ruling, in the
[3]-COND form (every input a displayed hypothesis with a named owner).
PROVED-under-hypotheses here: XRB = RS.0(β) (CL-9; hypothesis set at
S.1's status line). DERIVED: (β-2a)'s fixed-height → resummed passage
(GIVEN XHD alone); (K-TRI); (K-SUB) (+ plan-sync flag); (CUT-WD) =
CL-17(i) (given its predicate supply); RS.2; RS.3(ii) given E0; RS.4's
rational-identity step. OPEN KERNELS owned: ESCAPE(E0) (CL-1),
CL-17(ii). HYPOTHESIZED throughout, owners named: the nine CL-5 inputs,
(JC-INV) ([2b], rev 2), (J-RAT) ([1v]/[2b], rev 2), CL-10's
(SIB)/(JC-multi), CL-8's REL.2(a)–(e), CL-11's roster check,
CL-4's X.3. Gate RESUM-n3 SPECIFIED (protocol displayed; NO seal
artifact yet, nothing run — S.7 SEAL SEMANTICS); acceptance blocked on
STATE-probe-2 + [1v]-FULL + RESUM-n3. Rev 2 (2026-07-27) repaired
pass 1's 4 criticals + 3 gaps in place. Rev 3 (2026-07-27, pass 2's
1 critical + 2 gaps): E0/ACT widened to PER-POOL q₀ = p^δ (S.4's
kernel/(ii)/(e3)-FENCE + the ACT-layer pool scope); the binding proof
order retyped to the CONSUMPTION DAG (header, S.0's site, S.1); the
(J-RAT)/(JC-INV) owner-side interface routed through the plan ledger
(S.6 PLAN-SYNC FLAG). Awaits pass 3.


THE BLUEPRINT (REV 7):

# MOVES §S-RESUM — Lean formalization blueprint (corpus MovesS) — REV 7

## H0000. REV-7 rulings (the closing residue; on top of R1–R25)

**R26 — the n = 2 gate is the NOTE's instance, jointly inhabitable (Codex#3-1).**
The note's n = 2 data (S.0: "The n = 2 instance is the 1×1 case (W6's geometric
series, denominator q² + q + 1; `msW_eighth_le` its p = 2 inequality shadow)"): ONE
block-2 state, a THREE-outcome roster — one kcol outcome of mass q⁻³ (the ratio-1/8
face at q = 2 = `msW_eighth_le`'s shadow, `OM/SeriesAssembly.lean`) and TWO all-halted
terminal outcomes, verdicts (1,1)² (m = 2) and (1,2) (m = 1), masses 1 − q⁻¹ and
q⁻¹ − q⁻³; NO split outcomes ("the deep convolution is thin", S.7). JOINT
INHABITABILITY, row masses explicit: q⁻³ + (1 − q⁻¹) + (q⁻¹ − q⁻³) = 1 (part1 ✓);
kernel entry q⁻³ < 1 at every q₀ ≥ 2 (E0 ✓); det(1 − K) = 1 − q⁻³ = (q−1)(q²+q+1)/q³
≠ 0; the solve REDUCED: β_{(1,2)} = (q⁻¹−q⁻³)/(1−q⁻³) = (q+1)/(q²+q+1) and
β_{(1,1)²} = (1−q⁻¹)/(1−q⁻³) = q²/(q²+q+1) — the note's displayed denominator
EXACTLY, and β_{(1,2)} + β_{(1,1)²} = 1 (the checksum shadow). U-29b3 rebuilt on
this roster; the one-outcome impossibility is gone.

**R27 — degree bounds and CL-17(ii) tethered (Codex#3-2/3).** `TableShape` gains
`Wloc : ∀ e τ, Out e τ → ℕ` + `Wstate : ∀ e, State e → ℕ`; `MeasuredSide` gains
`Went : ∀ e τ, EntShape e τ → ℕ` — the note's bound functions, FIXED BEFORE the
burdens ("T is one polynomial of degree ≤ W_loc(m) and each cell size one polynomial
of degree ≤ W_state(s)"; "per-shape ENT-COUNT polynomials of degree ≤ W_ent(ε)",
S.3). `RatBurdens` gains `tg_deg`/`j_deg`/`ι_deg` pinning each `PolyGeom.degBound`
to them — degBound can no longer be chosen after the polynomial. `RS4Chain`'s W_Ŝ
is TETHERED: `shEvt` (shallow-shape events) + `wshval_card` (eventually-exact card
ratio — the C.1.5-node-volume/CTS-count face, counting-native per R7) +
`wshval_bdd` (mass in [0,1]); the residual production law (XHD-s shallow sums ×
(SIB)'s COUNT face) is the pinned `W17ii` (§2.E) with owners [1v]/[3t] — CL-17(ii)
stays the note's OPEN kernel, never free interpolation.

**R28 — one-display S5 (Codex#3-4/5/6/7) + the ReadOffBundle gate (Fable#4-F2).**
U-29b1 → seven one-FIELD units (xhd_sum/no_stray/no_orphan/d4r0/part1/rep_indep/
meas_card); U-29b2 → four one-DISPLAY units (kstep+hmc / act / init+entcount /
comp); U-29d1 → three (β-def / recursion / xrb+rexact); U-29d3 → three (sigmas /
x3+rs1 / rsh-interp); NEW U-29d5 `n2_readoff` inhabits `ReadOffBundle` (S := the
all-active pools; hok from the explicit q²+q+1 denominators; no split legs).

**R29 — mechanical batch (Codex#3-8 + Fable#4-F1 + O-a/b/c).** ONE canonical
location: `MovesS/Interfaces.lean` — §2.E's heading and every "SyncDefs" reference
updated (the file `SyncDefs.lean` does not exist). `[DecidableEq ι]` added at every
generic-index matrix `1`/`^` site (U-13, EscapeE0, U-21a/b, U-23a–d). U-24a1's
stale "(over ℚ)" dep line fixed. Clarifiers: Defs' `consumedDeltas` body is filled
at phase E, U-16a3 proves `nested_delta_mem`; `markedPairing` takes no `hdet`
(Mathlib `⁻¹` total) — W1m's `hdet` binder is arity slack to align at phase E.

*REV 6, 2026-07-27. Repairs the two parallel rev-5 verdicts — Codex#2
(`MOVESS_AUDIT_CODEX_FINAL2_2026-07-28.md`, 2 crit / 4 gap) and Fable#3
(`MOVESS_AUDIT_FABLE3_2026-07-28.md`, 0 crit / 2 gap; DELTA-ABS, the guards, U-24a1's
closure, U-24b's locus, and Aℝ all DIRECTLY VERIFIED there). Audit trail: REV 2 ←
Codex(19/3) · REV 3 ← Codex(13/7) · REV 4 ← Fable(2/4) · REV 5 ← Codex(6/2)+Fable(1/4)
· REV 6 ← Codex(2/4)+Fable(0/2); cumulative table §6. Ground truth: DUAL-ACCEPTED
**§S-RESUM rev 6**, `MOVES_2026-07-24.md` ~11557–12430 — cite the ACCEPTANCE RECORD
(line ~12854), NEVER the in-body STATUS trailer (~12412: stale rev-3 narration;
Fable#3 O-4). Protocol-L; no new axioms; statement-fence; declaration order = spec.*

## H000. REV-6 rulings (on top of R1–R19)

**R20 — the verdict vocabulary is PINNED STRUCTURALLY (Codex#2-1).** `TableShape`
gains `vEquiv : VType ≃ {ef : ℕ+ × ℕ+ // (ef.1 : ℕ) * ef.2 ≤ n}` and `vdeg_spec :
(vdeg v : ℕ) = (vEquiv v).1.1 * (vEquiv v).1.2` — verdict types ARE the (e, f) pairs
of degree ≤ n, one label each (no extra, no missing), degree = e·f. With `sig_exact`
this forces Sigmas = the note's roster AT EVERY instance (n = 3: exactly the
displayed five — "σ ∈ {(1,1)³, (1,1)+(1,2), (1,3), (1,1)+(2,1), (3,1)}", S.7(i)).

**R21 — PrimePools = ALL base primes, both directions (Codex#2-2).** `prime_base`
becomes an iff; `prime_infinite` demoted to a derivable lemma
(`Nat.exists_infinite_primes`); x3_total/rs1_equates/rsh_interp/legs_reg now
quantify over every base prime — the note's "at each prime p" / CL-1's "δ = 1 the
base instance", with `prime_sub` forcing every base prime into `Pools`.

**R22 — carrier genericization (Codex#2-3 + Fable#3-G2, one fix family).** U-13/U-14
are stated over a generic carrier (`[CommRing R]` / `[Field F]`), so their ℝ
instances exist at U-24a1's seam; U-10's conclusion is stated over `Aℝ P` per D11;
D11's prose corrected (Fable#3 O-3).

**R23 — `hread` is TYPED DATA (Codex#2-4): `ReadOffBundle`** — packages at every
q₀ ∈ S and every e ∈ Icc 1 n, with AVAgree read-offs at EVERY (e, τA : Act, σ' :
Multiset VType); U-24b consumes it; coordinate coverage is auditable from the type.

**R24 — gate splits (Codex#2-5/6):** U-29b → U-29b1/b2/b3; U-29d → U-29d1/d2/d3.

**R25 — elaboration order made real (Fable#3-G1).** FILE PLACEMENT: §2.D's
RS1Bundle/RS4Chain + §2.E's SyncDefs live in `MovesS/Interfaces.lean`, elaborated
AFTER the S2/S4 definition units (imports BSplitDef, EvalReDef, ConsumedDeltas,
BlockSolve, BlockSolveTot, RshDef, MarkedDef) — cross-file declaration order = the
import DAG. `legs_reg` reordered after `PrimePools`; `splitOuts` declared in §2.C;
`bhatMeas` declared in U-16a2 (EvalReDef); `rsh_interp`'s `hdet` binder typed;
U-12c added to §3b's edges (O-2).

## H00. REV-5 rulings (on top of R1–R15)

**R16 — the active-block boundary, BOTH directions (Fable2-C1 + Codex-4).**
(i) `recursion_meas` and the pinned `W3_recursion` gain the `M.activeState q₀ e τ`
guard — the measured fixpoint is "restricted per CTS-M(ii) to the ACTIVE block"
exactly like every other measured claim; at wild pools the junk-block rows make NO
demand (det(I − D_{q₀}) = 0 stays a tolerated FINDING). U-24a1 unaffected: it fires
at τA ∈ P.Act where `act_spec` supplies the guard. (ii) U-24b's identification locus
is `S ⊆ allActivePools M` — at an all-active pool EVERY (e, τ) coordinate is active,
so coordinatewise coverage is total; this is the note's own locus: "at all-active
primes (cofinitely many — only finitely many primes are roots of some
not-identically-zero cell-size polynomial)" (S.4(ii)). No uniqueness is claimed for a
coordinate outside its activity locus.

**R17 — ONE δ-convention, multiplicative closure (Codex-5, architectural).**
CONVENTION (DELTA-ABS): the SEMANTIC base-change index of any consumed leg is its
index relative to the BASE PRIME p ([2r] (e2), "δ ABSOLUTE"); the STORED
`Member.δ`/`Shape.δOf` is the FACTOR contributed at its nesting step, and nested
substitution COMPOSES MULTIPLICATIVELY: `powSubst δ₁ ∘ powSubst δ₂ = powSubst
(δ₁·δ₂)`, `(p^δ₁)^δ₂ = p^(δ₁·δ₂)`. Consequences, all restated: `consumedDeltas` :=
ALL products of ≤ n stored factors (finite — (K-TRI) bounds nesting depth by n);
`pools_closed` (∀ δ : ℕ+) covers the closure; `RegP`/`legs_reg` therefore carry E0
over EVERY effective pool. The REV-4 remnant "leg-within-leg pools stay inside the
roster" is PURGED (it asserted the incompatible flat reading); a `powSubst_mul`
composition lemma is added (U-12c).

**R18 — exactness and domain pins (Codex-1/2/3).** `TableShape` gains the MovesSp
verdict vocabulary `vdeg : VType → ℕ+` (+ `finV : Fintype VType`); `RS4Chain.Sigmas`
gains `sig_exact : σ ∈ Sigmas ↔ (σ.map vdeg).sum = n` — Sigmas IS the note's full
degree-n splitting-type roster (n = 3 instance: the displayed five), never a menu;
W-1 inherits the exact roster through Sigmas. `PrimePools` gains `prime_base :
∀ q₀ ∈ PrimePools, ∃ p : ℕ, p.Prime ∧ q₀ = (p:ℚ)` — base primes (δ = 1) exactly as
the note's per-prime density route uses; x3_total/rs1_equates/rsh_interp now
quantify over that pinned domain.

**R19 — carriers and the rest (Codex-6/7/8 + Fable2-G1/G2/G3/G4).** D11 (below):
ℚ-matrices, ℝ-measured values, ONE coercion point `Aℝ P := P.A.map (algebraMap ℚ ℝ)`
declared in Defs and used by U-24a1/AVAgree/U-24a2 consistently. W-10 gains summand
NONNEGATIVITY (the note's "positive series"). `W1m_marked` is GATED per pool: the
OKat membership (no surviving pole — the (ii-c) pass) is a HYPOTHESIS, agreement the
conclusion. U-10 gains `he : e ∈ Finset.Icc 1 n`. U-29 splits into U-29a–e
(construction / ledger laws / pool+E0 / bundles / the W6 denominator check). Layer
headcounts corrected.

## H0. REV-4 rulings (on top of R1–R12)

**R13 — the ACT scope is a GUARD, never a zero-row law (Fable C2).** The invented
`act_row` is DELETED (the note displays only entry-INTO-inactive vanishing =
`act_target`, S.7(iv)). `part1`/`rep_indep`/`xhd_sum`/`xhd_no_stray`/`meas_card` are
GUARDED by `activeState q₀ e τ` — the note's own scope: "Scope: realized states only"
(S.4); "Every probabilistic claim … is about K_e restricted per CTS-M(ii) to the
ACTIVE block" (S.0). Wild pools are now instantiable; the ACT apparatus (act_spec,
inactive_vanish, AVAgree, U-21c's empty case) is live code. Ripple: U-9a/U-9b/U-10
carry the activity guard.

**R14 — the per-pool guards are CONSUMED (Fable C1).** U-24a is replaced by the pair
U-24a1 (the measured value IS the active-subsystem solve — derived per pool from
`recursion_meas` + subsystem closure (`inactive_vanish`/`act_target`) + E0/U-21c;
the split legs enter the exit vector as MEASURED values at q₀^δ, pools_closed-typed,
so NO induction and NO leg evaluation is needed) and U-24a2 (the symbolic read-off:
`evalAt q₀ (blockSolve …) = βmeas …` GIVEN `AVAgree` at that entry — the note's
sealed (ii-c) check as an explicit hypothesis; uncancelled wild poles are EXCLUDED by
the guard, not claimed). `RegP` and `AVAgree` are now consumed (U-24a1/2, U-24b,
RS4Chain.legs_reg). U-24b's global identification is CONDITIONAL on an infinite
read-off-valid pool family — the (ii-c) burden stays open and per-pool, as displayed.
VERDICT: U-24a CLOSES under the wired guards (no STUCK report); the former "hard"
strong induction DISSOLVES — the hardness was exactly the unhypothesized burden.

**R15 — gap closures (Fable G1–G4).** `kstep_one`'s target predicate is pinned in its
hK-free existential-cast form; W-1's rfl-conjunct is struck (the symbolic half is
definitional — RS.1-SH's content is the measured clause), binders unshadowed; U-16a
splits into U-16a1/2/3 with the halted-member FACTOR-1/verdict-singleton clause
displayed as bSplit's def-equation; `entCount` gets its event-card tie at the shape's
own level (`entLvl`/`entInst`/`ent_count_card`). New easy lemma U-12b
`powSubst_OKat_evalAt` (OK-membership and evaluation transport along q₀ ↦ q₀^δ).

## H. HEADER — REV-3 design rulings (kept; R7–R12)

**R7 — the counting-native event carrier (ORCHESTRATOR RULING, finding R2-4).** MovesS
gains a MINIMAL event layer in the corpus house style (MovesC's DigitSystem/Nat.card
pattern): per pool q₀ and level N a finite `Box q₀ N`; EVENTS are `Finset (Box q₀ N)`;
disjointness is `Disjoint` of Finsets; masses are EVENTUALLY-EXACT CARD RATIOS
(`mass * card Box = card event` for N ≥ N₀ — the MovesC level-independence idiom).
XHD / D4R.0 / (iv)-MEAS restate the note's disjoint-EVENT conditions over this carrier
— not height-label arithmetic. MovesV instantiates the carrier at wave 4; MovesS does
not wait.

**R8 — RS.2 de-circularized (finding R2-9).** `RS1Bundle` carries NO symbolic β input.
Its measured inputs are `βmeas` (height-indexed, per-pool) + the measured fixpoint
`recursion_meas` + `xrb`. The interpolant is DERIVED: U-24a proves the per-pool
evaluated identity `evalAt q₀ (blockSolve …) = βmeas …` at all-active pools (per-pool
E0/ACT guarding evaluation, exactly S.4's discipline); U-24b proves the interpolant
UNIQUE and FIXED (U-27 infinitude) — that is RS.2's "one fixed rational function" and
RS.1-DEEP's symbolic reading, derived from the note's actual GIVENs.

**R9 — no free index sets** (findings R2-7, R2-8, R2-10, R2-11). `Pools` is pinned to
prime powers and CLOSED under q₀ ↦ q₀^δ (the [2r] (e2) legs); `allActive` is a DEFINED
locus (the all-active states classification), with only its INFINITUDE a burden
((iv)-POLY's cofiniteness face); `PoolHyp.Act` is DETERMINED by the CTS-M(ii)
classification field (`act_spec`, an iff) — never chosen; `SigSet`/`sig_covers` are
DELETED — every σ′ quantifier runs over ALL of `Multiset VType` as the note displays,
finite sums use the roster's verdict-image Finset; RS.4's σ-index is
`Multiset VType` with a Finset `Sigmas` of splitting types (W-1 typechecks).

**R10 — every wave-4 deferral is a PINNED Prop** (finding R2-18): the pin file
[CANONICAL at REV 7: `MovesS/Interfaces.lean`, R29]
declares W-1/W-1e/W-1m/W-2/W-3/W-4/W-7/W-8/W-10 as Lean `def … : Prop` signatures over
minimal carriers (`TreeIface`, `ReadLedger`, `FiberIface`); no prose deferrals. W-9 is
RETIRED — subsumed by R7's event carrier. Convergence (S.2's unconditional display) is
pinned as W-10.

**R11 — the non-vacuity gate is renamed to its honest claim** (finding R2-20):
U-29 `consistency_n2` inhabits EVERY §2 structure simultaneously with a nontrivial
instance reproducing W6's displayed 1×1 solve (denominator q² + q + 1) — a SCHEMA
CONSISTENCY gate. Inhabitation by the intended CTS instance is MovesV/MovesT's wave-4
instantiation duty (§5 process obligation), and is NOT claimed by any unit.

**R12 — mechanical fatalities** (findings R2-1, R2-2, R2-3, R2-12, R2-13, R2-15,
R2-16, R2-17): the `∨ True` disjunct is DELETED (`memberOf_ne_sel` states the real
inequality); `flank_zero : flankCount = 0 → flankWidth = 0` added (U-4's missing leg);
declaration order fixed everywhere (fields precede uses); U-10's TG/J nonnegativity is
ROUTED (TG on non-split, J on split) and now DERIVED from the ledger, not assumed;
U-22's `e` binder is inside the per-block quantifier; U-21b takes `[Nonempty ι]` (U-21c
handles the empty case via `Matrix.det_isEmpty`); U-7 splits into U-7a/b/c; `bTot`/
`blockSolveTot` define U-25's aggregate; the measured marked total `markedVal` is a
carrier field.

Downstream statement: MovesV/MovesT enter ONLY through §2's hypothesis structures;
owners at every field; instantiable at wave 4.

---

## 0. What §S-RESUM is (one paragraph)

The depth direction of the classifier tree, resummed: per block 1 ≤ e ≤ n the system
> (R_e-lump)  β_e = K_e β_e + b_e^{term,fin} + b_e^split
over ℚ(q); the (m, c) CLASSIFICATION routes every outcome to exactly one of {K_e
column, terminal exit, split exit}; (K-TRI) triangularizes the block family; (K-SUB)
gives sub-stochastic rows from PART-1; the solve is adj(I−K_e)b_e/det(I−K_e) (RS.2);
solvability rides ESCAPE(E0) per pool (RS.3, OPEN CL-1); RS.1 ties the solve to R_σ
(DEEP/SH/MARKED); RS.4: Σ_σ R_σ = 1 by the infinitely-many-evaluations argument.

## 1. Mathlib design (all names verified in the pinned cache; = REV 2's D1–D9 plus)

D1 `Qq := RatFunc ℚ` (`RatFunc.instField`) · D2 one matrix per e, vectors per (e, σ′) ·
D3 `Matrix.isUnit_iff_isUnit_det`, `mul_nonsing_inv`/`nonsing_inv_mul`, `inv_def`,
`cramer_eq_adjugate_mulVec`, `mul_adjugate`/`adjugate_mul`,
`det_smul_inv_mulVec_eq_cramer` · D4 partial evaluation `evalAt q₀ : OKat q₀ →+* ℚ`
(`RatFunc.eval_add`/`eval_mul` hypothesis-carrying) · D5
`Polynomial.eq_zero_of_infinite_isRoot` via `ratfunc_eval_infinite` · D6
`powSubst (δ : ℕ+)` via `IsFractionRing.lift` (δ = 0 unrepresentable) · D7 σ′ =
`Multiset VType`, finite sums over roster-image Finsets (SigSet DELETED, R9) · D8
`MuHat` fence · D9 measured values in ℝ, symbolic in Qq, meeting only through
interpolation laws · D10 events = `Finset (Box q₀ N)`, masses = eventually-exact card
ratios (R7); `Matrix.det_isEmpty` for empty active blocks · **D11 (REV 5, the ℚ/ℝ
architecture — Codex-7 = Fable2-G1)**: matrices/vectors of evaluated table data live
in ℚ; measured values live in ℝ; the identification passes through ONE coercion point
declared in Defs — `def Aℝ (P : PoolHyp …) : Matrix P.Act P.Act ℝ :=
P.A.map (algebraMap ℚ ℝ)` — with det transported by `RingHom.map_det` +
`Rat.cast_injective` (so `(1 - Aℝ P).det ≠ 0 ↔ (1 - P.A).det ≠ 0`); every mixed
statement (U-24a1, AVAgree, U-24a2, and — REV 6, R22 — U-10's conclusion) is stated
over ℝ via `Aℝ`/`(algebraMap ℚ ℝ)` and NOWHERE else coerces; the generic-carrier
U-13/U-14 (R22) supply the ℝ instances at U-24a1's seam.

---

## 2. Defs skeleton — `MovesS/Defs.lean` (declaration order = spec; findings R2-3)

### 2.A Combinatorial layer (owner MovesV/MovesSp rosters)

```lean
import Mathlib
namespace LeanUrat.MovesS
open Matrix Polynomial

abbrev Qq := RatFunc ℚ

structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+   -- the base-change FACTOR contributed at this nesting step; the
                -- SEMANTIC index rel. the base prime is the product along the chain
                -- (CONVENTION DELTA-ABS, R17; [2r] (e2)); no δ = 0
  status : V ⊕ State size
def Member.continuing (μ : Member V State) : Prop := μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []
def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ := (o.mem.filter (·.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  (o.mem.filterMap (fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split deriving DecidableEq
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

/-- Block states + rosters. NO SigSet (R9): σ′ ranges over all of `Multiset VType`;
    finite σ′-sums use `verdictImage` below. -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  finV   : Fintype VType            -- the MovesSp verdict catalogue is finite (R18)
  vdeg   : VType → ℕ+               -- the verdict type's degree
  vEquiv : VType ≃ {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ n}
    -- STRUCTURAL PIN (R20, Codex#2-1): verdict types ARE the (e, f) pairs of degree
    -- e·f ≤ n — exactly one label per pair, none extra, none missing (the note's
    -- vocabulary: σ′ multisets of (e_i, f_i); roster display S.7(i))
  vdeg_spec : ∀ v, (vdeg v : ℕ) = ((vEquiv v).1.1 : ℕ) * ((vEquiv v).1.2 : ℕ)
    -- degree THROUGH the pin — vdeg cannot be gamed; with sig_exact this forces
    -- Sigmas = the note's full roster at every n (n = 3: exactly the five)
  Out    : ∀ e, State e → Type
  finO   : ∀ e τ, Fintype (Out e τ)
  odata  : ∀ e τ, Out e τ → Outcome VType State
  Wloc   : ∀ e τ, Out e τ → ℕ      -- the note's W_loc(m) bound datum (R27, Codex#3-2;
  Wstate : ∀ e, State e → ℕ        --   W_state(s)) — FIXED HERE, before any burden
attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finV
  TableShape.finO

/-- The finitely many verdict multisets the (e, τ) roster's terminal outcomes emit —
    the index Finset of (K-SUB)'s Σ_{σ′} b^{term,fin} (replaces REV 2's SigSet). -/
def verdictImage (T : TableShape n) (e : ℕ) (τ : T.State e) : Finset (Multiset T.VType) :=
  Finset.image (fun o => (T.odata e τ o).verdicts)
    {o : T.Out e τ | routeOf (T.odata e τ o) = .termFin}.toFinset
```

**(SCS) supply — declaration order fixed (R2-3), the `∨ True` artifact deleted (R2-1),
the flank-zero law added (R2-2).** Owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via SP.2.

```lean
structure SCSData (T : TableShape n) where
  -- data first (R2-3): every field below is declared before first use
  W D ℓ g μsel W' D' : ∀ e τ (o : T.Out e τ), ℕ
  flankCount  : ∀ e τ (o : T.Out e τ), ℕ
  flankWidth  : ∀ e τ (o : T.Out e τ), ℕ
  resFactors  : ∀ e τ (o : T.Out e τ), Finset (ℕ × ℕ)
  selIdx      : ∀ e τ (o : T.Out e τ), Fin (T.odata e τ o).mem.length
  memberOf    : ∀ e τ o, Fin (flankCount e τ o) ⊕
    {x // x ∈ resFactors e τ o ∧ x ≠ (g e τ o, μsel e τ o)} →
    Fin (T.odata e τ o).mem.length
  -- laws
  ℓpos : ∀ e τ o, 1 ≤ ℓ e τ o
  window_comp : ∀ e τ o, W e τ o = e * ℓ e τ o + flankWidth e τ o
    -- SP.1: flank sides = "the horizontal compositions of the window span outside
    -- the read side"
  flank_zero : ∀ e τ o, flankCount e τ o = 0 → flankWidth e τ o = 0   -- (R2-2): no
    -- sides ⟹ no width (the width is the sides' total raw width)
  sel_mem : ∀ e τ o, (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e τ o, ∑ x ∈ resFactors e τ o, x.1 * x.2 = ℓ e τ o     -- "Σ g⁽ⁱ⁾μ⁽ⁱ⁾ = ℓ"
  memberOf_inj : ∀ e τ o, Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e τ o i, memberOf e τ o i ≠ selIdx e τ o        -- (R2-1): the
    -- REAL inequality — every flank side / non-selected residual factor is a member
    -- DISTINCT from the designated one; no disjunct, no vacuous premise
  sel_continuing : ∀ e τ o, routeOf (T.odata e τ o) = .kcol →
    ((T.odata e τ o).mem.get (selIdx e τ o)).continuing
  stage_D : ∀ e τ o, D' e τ o = e * g e τ o * D e τ o                 -- (B1)
  stage_W : ∀ e τ o, W' e τ o = μsel e τ o                            -- (B3)
  cluster_parent : ∀ e τ o, W e τ o * D e τ o = e
  cluster_child : ∀ e τ o (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o

/-- DEG-CONS (CL-11, [1v]): full-roster per-member degree law. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e τ (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ τ (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e
```

### 2.B The measured side (R7 event carrier) + the NINE-input ledger (R2-4/5/6 repaired)

Owner [1v] CTS-M / [2b] XHD / [5]. Intended instance: the CTS cell space over the
level-N residue boxes of the O_δ theory (the MovesC counting idiom), wave 4.

```lean
structure MeasuredSide (T : TableShape n) where
  -- pools: prime powers, closed under the base-change legs (R2-7, R2-14)
  Pools : Set ℚ
  pools_prime_pow : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p:ℚ)^(δ:ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀^(δ:ℕ) ∈ Pools
  pools_infinite : Pools.Infinite
  -- the counting carrier (R7): level-N boxes, events as Finsets
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  -- cells, representatives, heights
  Cell : ∀ e, T.State e → Type
  finC : ∀ e τ, Fintype (Cell e τ)
  cellOut : ∀ e τ, Cell e τ → T.Out e τ
  Rep : ∀ e, T.State e → Type          -- concrete states WITH their admissible
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ, Nonempty (Rep e τ)   -- histories (design note:
                                        -- the ∀-x quantifiers below quantify histories)
  Hgt : Type
  HDom : ∀ e τ, Cell e τ → Set Hgt     -- the EXACT height domain (XHD-d)
  gwt : ∀ e τ (c : Cell e τ), Hgt → ℚ → ℝ        -- XHD-w fixed-height weight
  cellEvt : ∀ e τ, Rep e τ → Cell e τ → Hgt → ∀ q₀ N, Finset (Box q₀ N)
    -- the (cell, height) one-step EVENT at level N given the entrance representative
  μcell : ∀ e τ, Rep e τ → Cell e τ → ℚ → ℝ      -- XHD-resummed conditional cell mass
  rowVal : ∀ e τ, T.Out e τ → ℚ → ℝ    -- the MEASURED per-outcome resummed row (the
                                        -- T·G row for non-split, the J cell-sum for
                                        -- split) — RS.0(α)'s object (R2-5)
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ -- measured k-step in-block mass
  activeState : ℚ → ∀ e, T.State e → Prop        -- CTS-M(ii)'s classification (R2-6/8)
  decA : ∀ q₀ e, DecidablePred (activeState q₀ e)
  -- entrance side
  EntShape : ∀ e, T.State e → Type
  finE : ∀ e τ, Fintype (EntShape e τ)
  hent : ∀ e τ, EntShape e τ → ℕ                 -- retained h_ent(ε)
  Went : ∀ e τ, EntShape e τ → ℕ                 -- W_ent(ε), the INIT-RAT degree
                                                  --   bound datum (R27), fixed here
  entEvtH : ∀ e τ, EntShape e τ → Hgt → ∀ q₀ N, Finset (Box q₀ N)  -- fixed-height
  ιDom : ∀ e τ, EntShape e τ → Set Hgt           --   entrance events + exact classes
  ιshH : ∀ e τ, EntShape e τ → Hgt → ℚ → ℝ       -- fixed-height marked mass ((COMP-h))
  ιsh : ∀ e τ, EntShape e τ → ℚ → ℝ              -- resummed per-shape marked mass
  ιval : ∀ e, T.State e → ℚ → ℝ                  -- the ENT-AGG aggregate
  entCount : ∀ e τ, EntShape e τ → ℚ → ℕ         -- the full count I^ent_{ε,β₀}
  entLvl : ∀ e τ, EntShape e τ → ℕ               -- ε's own defining level (a finite
                                                  --   prefix shape) — G4's tie level
  entInst : ∀ e τ, EntShape e τ → ∀ q₀ N, Finset (Box q₀ N)  -- ε-instance events
  markedVal : ∀ e, ℚ → ℝ                          -- the measured μ̂ marked-entrance
                                                  -- total (W-1m's carrier, R2-17)

def allActivePools (M : MeasuredSide T) : Set ℚ :=       -- DEFINED locus (R2-7/R9)
  {q₀ ∈ M.Pools | ∀ e ∈ Finset.Icc 1 n, ∀ τ, M.activeState q₀ e τ}

/-- CL-5, all nine inputs as contentful Props (R2-4/5/6). Notation: `cells o` :=
    `{c | M.cellOut e τ c = o}.toFinset`; `evR x` := eventually-exact card ratio. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  -- ACTIVITY GUARDS THROUGHOUT (R13, Fable C2): every per-(e,τ,q₀) mass claim below
  -- carries `M.activeState q₀ e τ` — the note's "realized states only" scope. NO
  -- zero-row law for inactive sources exists (act_row DELETED — undisplayed).
  -- (1) XHD [2b], guarded; two-sided exactness representative-quantified (R2-4):
  xhd_sum : ∀ e τ x c q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
  xhd_no_stray : ∀ e τ x c (h : M.Hgt), h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀, (M.cellEvt e τ x c h q₀ N).Nonempty
  xhd_no_orphan : ∀ e τ x c (h : M.Hgt), h ∉ M.HDom e τ c →
    ∀ q₀ N, M.cellEvt e τ x c h q₀ N = ∅
  -- (2) D4R.0 (event disjointness needs no realization; unguarded is harmless —
  -- empty events are disjoint):
  d4r0 : ∀ e τ x q₀ N c c' (h h' : M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (M.cellEvt e τ x c h q₀ N) (M.cellEvt e τ x c' h' q₀ N)
  -- (3) (iv)-PART-1 [1v], GUARDED (C2's 0 = 1 collapse is gone — at a wild pool the
  -- inactive rows make NO partition claim):
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ τ x q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
  -- (4) (iv)-REP = RS.0(α) verbatim (weighted grouping), GUARDED:
  rep_indep : ∀ e τ (o : T.Out e τ) (x : M.Rep e τ) q₀, q₀ ∈ M.Pools →
    M.activeState q₀ e τ → M.rowVal e τ o q₀ = ∑ c ∈ cells o, M.μcell e τ x c q₀
  -- (5) (iv)-MEAS counting-native (R7), GUARDED:
  meas_card : ∀ e τ x c (h : M.Hgt), h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.gwt e τ c h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.cellEvt e τ x c h q₀ N).card : ℝ)
  -- (6) CTS-M(v) HMC (OPEN) + the base tie, target predicate PINNED hK-FREE (G1):
  kstep_one : ∀ e τ β q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ → M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o | routeOf (T.odata e τ o) = .kcol ∧
      ∃ μ ∈ (T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, M.rowVal e τ o q₀
  hmc : ∀ k e τ β q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep (k+1) e τ β q₀ = ∑ γ, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
  -- (7) CTS-M(ii) ACT — ONLY the displayed law (S.7(iv): "the verified vanishing …
  -- of every entry into an inactive cell"); the source-side scope is the guards:
  act_target : ∀ e τ β q₀, q₀ ∈ M.Pools → ¬ M.activeState q₀ e β →
    M.kstep 1 e τ β q₀ = 0
  -- (8) CTS-M(iii) INIT + ENT-COUNT, guarded; the I^ent tie at ε's OWN level (G4):
  init_agg : ∀ e τ q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.ιval e τ q₀ = ∑ ε, M.ιsh e τ ε q₀
  init_count : ∀ e τ ε (h : M.Hgt), h ∈ M.ιDom e τ ε → ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.ιshH e τ ε h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.entEvtH e τ ε h q₀ N).card : ℝ)
  ent_count_card : ∀ e τ ε q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ((M.entInst e τ ε q₀ (M.entLvl e τ ε)).card : ℚ) = M.entCount e τ ε q₀
    -- "a full count": I^ent_{ε,β₀} IS the card of the ε-instance event at the
    -- shape's own defining level — the counting tie ι_count's polynomial now means
  -- (9) COMP-TYPING, heights once: (COMP-h) = init_count's fixed-height objects;
  -- (COMP-hΣ) = THE one height sum; (COMP-Σ)'s factorization is hmc's duty:
  comp_once : ∀ e τ ε q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)
```

*(Design note: the ONLY height summations in the corpus are xhd_sum and comp_once —
(COMP-Σ)'s "no further height sum" is structural. kstep_one's target predicate is the
PINNED hK-free existential-cast form above (Fable G1) — no SCSData/DegCons/hK is in
LedgerIV's scope, and none is needed.)*

### 2.C Evaluation, rationality burdens (POLY bounds restored), kernel, pools

```lean
def OKat (q₀ : ℚ) : Subring Qq := sorry             -- {f // f.denom.eval q₀ ≠ 0}; U-19
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ := sorry                       -- U-19

/-- The (iv)-POLY/XHD-s presentation pattern (R2-7): a count POLYNOMIAL with its
    displayed degree bound × a height part with GEOMETRIC denominators. -/
structure PolyGeom where
  count : Polynomial ℚ
  degBound : ℕ
  deg_le : count.natDegree ≤ degBound          -- "degree ≤ W_loc(m)" / "≤ W_state(s)"
  geom : Qq                                     -- the XHD-s height sum G
  geomDenoms : Finset ℕ+
  geom_denom_dvd : geom.denom ∣ ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a:ℕ))
    -- "G ∈ ℚ(q) with geometric denominators (1 − q^{−a})" (cleared form)
def PolyGeom.val (P : PolyGeom) : Qq := algebraMap (Polynomial ℚ) Qq P.count * P.geom

/-- The rationality burdens: ℚ(q) data in (iv)-POLY form + interpolation to the
    measured rows. Owners: CL-6 (iv)-POLY [1v] (tgP + tg_interp); (J-RAT) [1v]/[2b]
    (jP + j_interp); INIT-RAT [1v] (ιP + ι_interp); + the cofinite-activity face. -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  tgP : ∀ e τ (o : T.Out e τ), PolyGeom
  jP  : ∀ e τ (o : T.Out e τ), PolyGeom
  ιP  : ∀ e τ (ε : M.EntShape e τ), PolyGeom      -- per-shape ENT-COUNT polynomials,
                                                   -- "degree ≤ W_ent(ε)", XHD-s sums
  tg_ok : ∀ e τ o q₀, q₀ ∈ M.Pools → (tgP e τ o).val ∈ OKat q₀
  j_ok  : ∀ e τ o q₀, q₀ ∈ M.Pools → (jP e τ o).val ∈ OKat q₀
  ι_ok  : ∀ e τ ε q₀, q₀ ∈ M.Pools → (ιP e τ ε).val ∈ OKat q₀
  tg_interp : ∀ e τ o q₀ (h : q₀ ∈ M.Pools), routeOf (T.odata e τ o) ≠ .split →
    (evalAt q₀ ⟨(tgP e τ o).val, tg_ok e τ o q₀ h⟩ : ℝ) = M.rowVal e τ o q₀
    -- "valued correctly at every prime power" — against the MEASURED row (R2-5's
    -- rowVal), for the kernel/terminal columns
  j_interp : ∀ e τ o q₀ (h : q₀ ∈ M.Pools), routeOf (T.odata e τ o) = .split →
    (evalAt q₀ ⟨(jP e τ o).val, j_ok e τ o q₀ h⟩ : ℝ) = M.rowVal e τ o q₀
    -- J = the branching-cell mass, EACH CELL ONCE — never the marked T·G
  ι_interp : ∀ e τ ε q₀ (h : q₀ ∈ M.Pools),
    (evalAt q₀ ⟨(ιP e τ ε).val, ι_ok e τ ε q₀ h⟩ : ℝ) = M.ιsh e τ ε q₀
  ι_count : ∀ e τ ε q₀, q₀ ∈ M.Pools →                    -- ENT-COUNT's polynomial IS
    ((ιP e τ ε).count.eval q₀ : ℚ) = M.entCount e τ ε q₀  -- the full count at pools
  tg_deg : ∀ e τ o, (tgP e τ o).degBound = T.Wloc e τ o + T.Wstate e τ
  j_deg  : ∀ e τ o, (jP e τ o).degBound = T.Wloc e τ o + T.Wstate e τ
  ι_deg  : ∀ e τ ε, (ιP e τ ε).degBound = M.Went e τ ε
    -- DEGREE PINS (R27, Codex#3-2): each degBound IS the note's named bound —
    -- "degree ≤ W_loc(m)" × "≤ W_state(s)" (the combined count ≤ the sum) and
    -- "ENT-COUNT polynomials of degree ≤ W_ent(ε)"; the W-data live on
    -- TableShape/MeasuredSide, fixed BEFORE the burdens — never chosen per entry
  allActive_infinite : (allActivePools M).Infinite
    -- (iv)-POLY's cofiniteness face: "only finitely many primes are roots of some
    -- not-identically-zero cell-size polynomial" ⟹ the DEFINED locus is infinite
abbrev RatBurdens.TG (RB) e τ o : Qq := (RB.tgP e τ o).val
abbrev RatBurdens.J  (RB) e τ o : Qq := (RB.jP e τ o).val
noncomputable def RatBurdens.ι (RB) e : T.State e → Qq := fun τ => ∑ ε, (RB.ιP e τ ε).val

def splitOuts (T : TableShape n) (e : ℕ) (τ : T.State e) : Finset (T.Out e τ) :=
  {o | routeOf (T.odata e τ o) = .split}.toFinset      -- (Fable#3-G1(iii): declared)
def kTarget (T) e τ (o : T.Out e τ) (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e := sorry   -- U-16a region
def Kmat (T) (RB : RatBurdens T M) (e : ℕ)
    (hK : ∀ τ o hk, ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) :
    Matrix (T.State e) (T.State e) Qq := sorry    -- Σ_{kcol o → β} RB.TG e τ o
def bTerm (T) (RB) (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq := sorry
    -- Σ_{termFin o, v(o) = σ'} RB.TG e τ o  (any σ'; supported on verdictImage)

structure EscapeE0 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) :
    Prop where   -- [DecidableEq ι]: Matrix `1`/`^` need it (Fable#4-F1 batch, R29)
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1:ℚ))) Filter.atTop (nhds 0)

/-- Per-pool package (S.4). `Act` is DETERMINED by CTS-M(ii)'s classification
    (R2-8: act_spec is an iff — an empty Act needs the NOTE's own no-realized-state
    situation, never a modeling choice). -/
structure PoolHyp (T) (M) (RB : RatBurdens T M) (e : ℕ) (hK) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  act_spec : ∀ τ, τ ∈ Act ↔ M.activeState q₀ e τ            -- (R2-8)
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok _ _ τ.2 β.2⟩
  inactive_vanish : ∀ τ β (hok : Kmat T RB e hK τ β ∈ OKat q₀), τ ∈ Act → β ∉ Act →
    evalAt q₀ ⟨_, hok⟩ = 0
  e0 : EscapeE0 A                                            -- ESCAPE(E0), CL-1, OPEN

/-- D11's ONE coercion point (R19, Codex-7 = Fable2-G1): the active matrix over ℝ. -/
noncomputable def Aℝ (P : PoolHyp T M RB e hK q₀) : Matrix P.Act P.Act ℝ :=
  P.A.map (algebraMap ℚ ℝ)
  -- det transported: `RingHom.map_det` + `Rat.cast_injective` give the E-phase simp
  -- lemma `Aℝ_det_iff : (1 - Aℝ P).det ≠ 0 ↔ (1 - P.A).det ≠ 0`.

/-- CTS-M(ii-c)'s per-pool read-off gate, ℝ-typed via Aℝ (R19): "the evaluated
    object's q₀-value (after cancellation — OKat membership is post-cancellation by
    RatFunc's reduced num/denom) equals the active-subsystem solve there". Junk-block
    determinants stay census-side: recorded, never required nonzero. -/
def AVAgree (P : PoolHyp T M RB e hK q₀) (v : Qq) (bA : P.Act → ℝ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, ((evalAt q₀ ⟨v, hok⟩ : ℚ) : ℝ) = ((1 - Aℝ P)⁻¹ *ᵥ bA) τ

```

*(`consumedDeltas`/`RegP` are declared in §2.D AFTER `ShapeFam` — declaration order.)*

### 2.D (BDY), shapes, RS.1/RS.4 interfaces (R2-9/10/11/17/19 repaired)

**FILE PLACEMENT (R25, Fable#3-G1):** `MuHat`/`ReadOwner`/`Shape`/`ShapeFam`/
`consumedDeltas`/`RegP` below live in `Defs.lean`; **`RS1Bundle`, `RS4Chain`,
`ReadOffBundle`, and all of §2.E live in `MovesS/Interfaces.lean`**, which imports
the S2/S4 definition units (BSplitDef, EvalReDef — incl. `bhatMeas` —
ConsumedDeltas, BlockSolve, BlockSolveTot, RshDef, MarkedDef), so `evalRe`/`Rsh`/
`markedPairing`/`bhatMeas` are in scope where the interface fields cite them.
Cross-file declaration order = the import DAG; phase E elaborates as written.

```lean
structure MuHat where val : Qq                    -- the μ̂ fence (no Add, no coercion)

inductive ReadOwner | entrance | block deriving DecidableEq
def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance

structure Shape (T : TableShape n) where           -- length-matched record (REV 2)
  k    : ℕ
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)
  δOf  : Fin k → ℕ+   -- the shape leg's base-change FACTOR (CONVENTION DELTA-ABS,
                      --   R17: semantic index rel. base prime = chain product)
  σ0   : Multiset T.VType
structure ShapeFam (T : TableShape n) where
  Sh : Finset (Shape T)                            -- [2a] finiteness; CUT-3's image
                                                   -- is the intended instance (W-7)
def consumedDeltas (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ := sorry -- U-16a3:
  -- MULTIPLICATIVE CLOSURE (R17, Codex-5): all products of AT MOST n factors drawn
  -- from {split-leg δ's over the full roster} ∪ ⋃_{Ŝ ∈ F.Sh} image Ŝ.δOf, including
  -- the empty product 1. FINITE: the factor set is finite and (K-TRI) bounds nesting
  -- depth by n (each split leg strictly decreases e; a shape leg adds one factor).
  -- Covers every EFFECTIVE index (p^δ₁)^δ₂ = p^(δ₁·δ₂) a nested leg reaches — the
  -- closure lemma `nested_delta_mem` is U-16a3's spec obligation.
def RegP (T M) (RB : RatBurdens T M) (p : ℕ) (hK) (F : ShapeFam T) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ δ ∈ consumedDeltas T F,
    Nonempty (PoolHyp T M RB e (hK e) ((p:ℚ)^(δ:ℕ)))

/-- RS.1's interface — NO symbolic β input (R8/R2-9): measured objects only. -/
structure RS1Bundle (T) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK) where
  βmeas : ∀ e ∈ Finset.Icc 1 n, ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
    -- (h_ent-INDEXED measured conditional subtree value; owner [3t])
  β_bdd : ∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools →
    βmeas e he h_ent τ σ' q₀ ∈ Set.Icc (0:ℝ) 1     -- "a positive series bounded by 1"
  xrb : ∀ e he h h' τ σ', βmeas e he h τ σ' = βmeas e he h' τ σ'   -- (XRB) CL-9, OPEN
    -- (discharge = the pinned W-2, S.1's proof under XHD+(JC-INV)+(SIB)/(JC-multi)
    -- +TB-CAP/VP+REL.2(a)(b)(d)+(ns-null) — measure-side, wave 4)
  recursion_meas : ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools), M.activeState q₀ e τ →
    ∀ h_ent, βmeas e he h_ent τ σ' q₀
      = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
    -- ACTIVITY-GUARDED (R16(i), Fable2-C1): the measured fixpoint is "restricted per
    -- CTS-M(ii) to the ACTIVE block" — junk-block rows at wild pools make NO demand
    -- (det(I − D_{q₀}) = 0 stays a tolerated FINDING). EVERY σ' (R2-10); legs at
    -- q₀^δ well-formed by pools_closed. Discharge = pinned W-3 (TREE-EXP+ONE-F+
    -- (SIB)+PCI). U-24a1 fires it at τA ∈ P.Act (act_spec supplies the guard).
  βfull : ∀ e ∈ Finset.Icc 1 n, ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
  nsNull : Prop                                    -- the (ns-null) tag; [3t]-closed
  rexact : nsNull → ∀ e he h_ent τ σ' q₀,          -- (R_e-exact) GIVEN (ns-null)
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀

/-- RS.4's chain — the FULL displayed inherited set as explicit components (R2-19),
    with the σ-index = verdict multisets (R2-11) so W-1 typechecks. -/
structure RS4Chain (T) (M) (RB : RatBurdens T M) (hdc : DegCons T) (hK)
    (F : ShapeFam T) where
  L : LedgerIV T M                                 -- the nine CL-5 inputs
  B : RS1Bundle T M RB hdc hK                      -- RS.1's set (xrb, recursion, …)
  hns : B.nsNull                                   -- (ns-null)'s proof demanded HERE
  pools_e0 : ∀ e ∈ Finset.Icc 1 n, ∀ q₀ ∈ allActivePools M,
    Nonempty (PoolHyp T M RB e (hK e) q₀)          -- the all-active face (feeds U-22)
  PrimePools : Set ℚ                               -- (declared BEFORE legs_reg — R25)
  prime_sub : PrimePools ⊆ M.Pools
  prime_base : ∀ q₀, q₀ ∈ PrimePools ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)
    -- DOMAIN PIN, BOTH DIRECTIONS (R21, Codex#2-2): PrimePools = ALL base primes,
    -- not an infinite selection — X.3/RS.1/E0's base instance fire at EVERY prime
    -- ("at each prime p the decided-mass series totals 1"); with prime_sub this
    -- also forces every base prime into Pools. Infinitude now DERIVABLE
    -- (`Nat.exists_infinite_primes`) — prime_infinite demoted to a lemma.
  legs_reg : ∀ p, (p:ℚ) ∈ PrimePools → RegP T M RB p hK F
    -- CL-1's FULL per-pool quantifier at EVERY base prime (R21): E0/ACT packages at
    -- δ = 1 AND every consumed base-change leg pool p^δ — wild pools included;
    -- their READ-OFF stays gated per object by AVAgree (W-6)
  Sigmas : Finset (Multiset T.VType)               -- the splitting types of degree n
  sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n
    -- EXACTNESS PIN (R18, Codex-1/2): Sigmas IS the full degree-n verdict-type
    -- roster — every multiset of verdict types of total degree n, no menu freedom
    -- (n = 3 instance: exactly the note's displayed five). Nonemptiness is derivable
    -- for n ≥ 1 from any degree-n verdict; kept as a lemma, not a field.
  WshP : Shape T → PolyGeom                        -- CL-17(ii): W_Ŝ in rational form —
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, (WshP Ŝ).val ∈ OKat q₀   -- the OPEN production
                                                   -- duty rides this presentation
  WshVal : Shape T → ℚ → ℝ                         -- measured shallow-shape masses
  wsh_interp : ∀ Ŝ ∈ F.Sh, ∀ q₀ (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(WshP Ŝ).val, wsh_ok Ŝ ‹_› q₀ h⟩ : ℚ) : ℝ) = WshVal Ŝ q₀
  -- W_Ŝ TETHER (R27, Codex#3-3 — never free interpolation):
  wshval_bdd : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, WshVal Ŝ q₀ ∈ Set.Icc (0:ℝ) 1
    -- a MASS ("the resummed shallow tree mass")
  shEvt : Shape T → ∀ q₀ N, Finset (M.Box q₀ N)    -- the shape's shallow-layer event
  wshval_card : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, ∃ N₀, ∀ N ≥ N₀,
    WshVal Ŝ q₀ * (Fintype.card (M.Box q₀ N) : ℝ) = ((shEvt Ŝ q₀ N).card : ℝ)
    -- the C.1.5-node-volume × CTS/[1]-count face, counting-native (R7); the
    -- residual production law — XHD-s shallow height sums × (SIB)'s COUNT face
    -- across shallow splits — is the PINNED W17ii (§2.E; owners [1v]/[3t];
    -- CL-17(ii) stays the note's OPEN kernel: "the capstone may not be accepted
    -- while it is open")
  Rval : Multiset T.VType → ℚ → ℝ                  -- measured densities (owner [3t])
  r_bdd : ∀ σ q₀, q₀ ∈ M.Pools → Rval σ q₀ ∈ Set.Icc (0:ℝ) 1
  -- (PrimePools/prime_sub/prime_base are declared ABOVE, before legs_reg — R25;
  --  the REV-5 duplicate block here is REMOVED, prime_infinite now a lemma — R21)
  decidedTotal : ℚ → ℝ                             -- the decided-mass series total
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1  -- X.3's density form — CL-4, OPEN,
                                                   -- owner [5]; pinned as W-4
  rs1_equates : ∀ p ∈ PrimePools, (∑ σ ∈ Sigmas, Rval σ p) = decidedTotal p
    -- "RS.1 equates that series with Σ_σ R_σ(p)" — provenance the PINNED W-1e
    -- (RS.1-SH + ONE-F + W-10 convergence), a deferral, never proved here
  rsh_interp : ∀ σ ∈ Sigmas, ∀ p ∈ PrimePools,
    ∀ hdet : (∀ e (he : e ∈ Finset.Icc 1 n), (1 - Kmat T RB e (hK e he)).det ≠ 0),
    ∃ hok : Rsh T M RB hdc hK hdet F WshP σ ∈ OKat p,
      ((evalAt p ⟨_, hok⟩ : ℚ) : ℝ) = Rval σ p
    -- (hdet binder TYPED — Fable#3-G1(iii)) the measured densities are the
    -- evaluations of THE symbolic Rsh (U-18's one fixed rational function) — the
    -- evaluated shadow of the PINNED W-1; U-28's target is Σ_σ Rsh, never a free R

/-- R23 (Codex#2-4): the read-off bundle U-24b consumes — coordinate coverage as
    TYPED DATA. Lives in `Interfaces.lean` (R25; blockSolve/bhatMeas in scope). -/
structure ReadOffBundle (S : Set ℚ) (hS : S ⊆ allActivePools M)
    (B : RS1Bundle T M RB hdc hK) (hdet) where
  pkg : ∀ q₀ ∈ S, ∀ e ∈ Finset.Icc 1 n, PoolHyp T M RB e (hK e ‹_›) q₀
  read : ∀ q₀ (hq : q₀ ∈ S), ∀ e (he : e ∈ Finset.Icc 1 n),
    ∀ τA : (pkg q₀ hq e he).Act, ∀ σ' : Multiset T.VType, ∀ h_ent,
    AVAgree (pkg q₀ hq e he) (blockSolve T RB hdc hK hdet e he τA σ')
      (bhatMeas (pkg q₀ hq e he) B σ' h_ent) τA
  -- EVERY e ∈ Icc 1 n, EVERY τA : Act (= every τ — the pools are all-active),
  -- EVERY σ', every h_ent: total coordinate coverage, auditable from the type.
```

*(R : the symbolic R_σ is NOT a field — RS.2 for R_σ is DERIVED: `Rsh` (U-18) is the
one fixed rational function, and U-28 consumes Rval through `rs1_equates` + the W-1
interpolation `wsh_interp`/blockSolve chain. No conclusion is a field beyond the
note's displayed GIVENs, each tagged CL-4/CL-8/CL-10/CL-17/CL-5/CL-1/CL-9 above.)*

### 2.E `MovesS/Interfaces.lean` (CANONICAL — R29, Codex#3-8; no `SyncDefs.lean`
exists) — the PINNED wave-4 Props (R10; no prose deferrals)

```lean
-- minimal carriers for statements whose native vocabulary is MovesT's:
structure TreeIface (T : TableShape n) where       -- W-7's carrier
  Tree : Type                                       -- complete finite canonical trees
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
def W1_RS1SH (C : RS4Chain …) (hdet) : Prop :=      -- RS.1-SH's CONTENT (Fable G2):
  ∀ σ ∈ C.Sigmas, ∀ p ∈ C.PrimePools,               -- the MEASURED density identity.
    ∃ hok : Rsh T M RB hdc hK hdet F C.WshP σ ∈ OKat p,
      (evalAt p ⟨Rsh T M RB hdc hK hdet F C.WshP σ, hok⟩ : ℝ) = C.Rval σ p
  -- The SYMBOLIC half of S.2's display ("R_σ = Σ_Ŝ W_Ŝ · Σ ∏ β…") is DEFINITIONAL
  -- here: U-18 DEFINES Rsh as that right side, so the note's identity reduces to
  -- "the measured density Rval IS Rsh's evaluation" — this Prop. No rfl-conjunct.
  -- (Owners MovesT: TREE-EXP, (CUT-WD), (SIB)/CL-10, PCI/CL-8, XRB/CL-9, CL-17(ii).)
def W1e_equates (C : RS4Chain …) : Prop :=          -- ONE-F + convergence regrouping
  ∀ p ∈ C.PrimePools, (∑ σ ∈ C.Sigmas, C.Rval σ p) = C.decidedTotal p
def W1m_marked (B : RS1Bundle …) (hdet) : Prop :=   -- RS.1-MARKED's identification,
  ∀ e (he : e ∈ Finset.Icc 1 n) q₀ (h : q₀ ∈ M.Pools)   -- GATED per pool (Fable2-G2):
    (hok : (markedPairing T M RB hdc hK hdet e he).val ∈ OKat q₀),
      ((evalAt q₀ ⟨_, hok⟩ : ℚ) : ℝ) = M.markedVal e q₀
    -- the OKat membership (no pole surviving cancellation — the (ii-c) PASS) is a
    -- HYPOTHESIS, agreement the conclusion: "the sealed check … must pass BEFORE it
    -- may be read off; a pole SURVIVING cancellation at a wild pool is (ii-c)'s
    -- FAIL" — the pin demands nothing at pools where the gate fails
def W2_xrb (B : RS1Bundle …) : Prop :=              -- XRB's discharge target = the
  ∀ e he h h' τ σ', B.βmeas e he h τ σ' = B.βmeas e he h' τ σ'   -- field's statement
def W3_recursion (B : RS1Bundle …) : Prop :=        -- the measured fixpoint's
  ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools), M.activeState q₀ e τ →     -- discharge target;
    ∀ h_ent, B.βmeas e he h_ent τ σ' q₀                          -- ACTIVITY-GUARDED
    = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => B.βmeas e' he' h_ent)
    -- (R16(i): identical quantifier to the field it discharges — Fable2-C1)
def W4_x3 (C : RS4Chain …) : Prop := ∀ p ∈ C.PrimePools, C.decidedTotal p = 1
def W7_shapeFam (F : ShapeFam T) (TI : TreeIface T) : Prop :=
  ∀ t : TI.Tree, TI.shapeOf t ∈ F.Sh                -- CUT-3: every complete tree
                                                    -- carries exactly ONE listed shape
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
```

def W17ii (C : RS4Chain …) : Prop :=                -- CL-17(ii), the OPEN production
  ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, ∃ hok : (C.WshP Ŝ).val ∈ OKat q₀,
    ((evalAt q₀ ⟨_, hok⟩ : ℚ) : ℝ) = C.WshVal Ŝ q₀ ∧
    HasSum (fun h : M.ιDom' Ŝ => shWeight Ŝ h q₀) (C.WshVal Ŝ q₀)
  -- "every W_Ŝ is PRODUCED by the stated rational machinery (C.1.5 node volumes ×
  -- CTS/[1] counts × XHD-s shallow height sums, with (SIB)'s COUNT face across
  -- shallow splits)" — the height-sum face over shape-level carriers
  -- (ιDom'/shWeight: the Ŝ-level analogues of ιDom/ιshH, added to MeasuredSide at
  -- phase E with the same pattern); owners [1v]/[3t]; remains OPEN (CL-17).

W-5 (nsNull's discharge) is the field `RS4Chain.hns` — demanded, not deferred-loose.
W-6 (wild-pool read-off) is the Prop `AVAgree` (§2.C), cited per consumption site.
W-9 is RETIRED (subsumed by the R7 event carrier in LedgerIV). W-11 (instantiation of
every §2 structure by the REAL CTS objects) is a wave-4 PROCESS gate (§5), not a Prop.

---

## 3. The unit DAG — REV 7: 68 units (32 easy / 36 medium / 0 hard)

### Layer S0 — dispatch, (SCS), (BDY) [9]

**U-1 `dispatch_spec` · easy — unchanged from REV 2** (route iff-triple; omega).
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION … (c ≥ 1 with m = 1 forces c = 1)".

**U-2 `ktri` · easy — unchanged** (DegCons + m ≥ 2 ⟹ every member size < e).
moves_ref: "at m ≥ 2 EVERY e_j < e". **U-3 `kcol_agree` · easy — unchanged.**

**U-4 `scs_flank` · medium — hypotheses now SUFFICIENT (R2-1, R2-2).**
`statement`: as REV 2 (flankCount = 0 ∧ resFactors singleton ∧ W = e·ℓ ∧ g·μ = ℓ at
m = 1). moves_ref: "m = 1 forces NO flank side (the read side spans the window:
e·ℓ = W) and a SINGLETON residual shape λ = {(g, μ)}". deps: Defs · hyp: SCSData ·
sketch: m = 1 ⟹ member positions = Fin 1 ⟹ `selIdx` is the only position; `memberOf`
avoids it (`memberOf_ne_sel`, now unconditional) yet is injective into it ⟹ its domain
is EMPTY ⟹ flankCount = 0 AND no non-selected residual factor (so `sel_mem` makes
resFactors the singleton); `flank_zero` gives flankWidth = 0; `window_comp` gives
W = e·ℓ; `res_sum` on the singleton gives g·μ = ℓ. Every step now has its field.

**U-5 `scs_stage` · easy — unchanged** (W′D′ = WD via stage_D/stage_W + U-4).
**U-6 `scs` · medium — unchanged** (kcol ⟹ all member sizes = e; uses
`sel_continuing` + cluster_child/cluster_parent + U-4/U-5; PRODUCES the `hK`
argument of every Kmat consumer).

**U-7a `bdy_edge` · Bdy.lean · easy — split (R2-15).**
`theorem bdy_edge : ∀ fe r, (bdyEdgeOwner fe r = .entrance ↔ r ≤ fe) ∧`
`(bdyEdgeOwner fe r = .block ↔ fe < r)`. moves_ref: "the ENTERING READ of a block
entrance belongs to the ENTRANCE SIDE".

**U-7b `bdy_node_shadow` · BdyNode.lean · easy — split.**
`theorem bdy_node_shadow : ∀ fe, bdyNodeOwner fe fe = .block ∧`
`bdyEdgeOwner fe fe = .entrance ∧ ∀ r ≠ fe, bdyNodeOwner fe r = bdyEdgeOwner fe r`.
moves_ref: "the first entrance node ν is BLOCK-side as a STATE INDEX …, while the
edge INTO ν is entrance-side MASS".

**U-7c `bdy_mass_split` · BdyMass.lean · easy — split.**
`theorem bdy_mass_split (μm : ℕ → ℝ) (L fe) (h : fe ≤ L) :`
`∑ r ∈ Finset.range (L+1), μm r = (∑ r ∈ Finset.Icc 0 fe, μm r) +`
`(∑ r ∈ Finset.Icc (fe+1) L, μm r)`. moves_ref: "no read omitted, none double-charged".

### Layer S1 — (K-SUB) [4]

**U-8 `ksub_regroup` · medium — SigSet replaced by verdictImage (R9, R2-10).**
`statement` (per e ∈ Icc 1 n, τ, hK from U-6):
`(∑ β, Kmat T RB e hK τ β) + (∑ σ' ∈ verdictImage T e τ, bTerm T RB e σ' τ) +`
`(∑ o ∈ splitOuts T e τ, RB.J e τ o) = ∑ o : T.Out e τ, routedMass RB e τ o`
(routedMass := J on split, TG otherwise). moves_ref: "(K-SUB) Σ_β K_e(τ,β) +
Σ_{σ′} b_e^{term,fin}(τ)(σ′) + (branching-cell one-step mass, per cell once) = 1".
deps: U-1, U-6 · hyp: none beyond structures (verdictImage is exhaustive for the
terminal columns BY CONSTRUCTION — the R2-10 covering defect is gone) · sketch:
partition by routeOf; fiberwise regrouping by kTarget / by verdicts.

**U-9a `ksub_eval` · medium — ACTIVITY-GUARDED (R13).** Per pool, per representative,
AT ACTIVE STATES: `∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → evalAt q₀ (routedMass-sum)
= 1`. deps: U-8, U-19 · hyp: LedgerIV.part1 + rep_indep (both now guarded) +
RB.tg_interp/j_interp — the note's bracket "GIVEN the (iv) ledger + DEG-CONS + the
(m, c) CLASSIFICATION with its (SCS) clause", scoped "restricted per CTS-M(ii) to the
ACTIVE block" · sketch: interp → rowVal; rep_indep → x-grouped cell sum;
`Finset.sum_fiberwise` over cellOut; part1 → 1.

**U-9b `ksub` · medium — locus updated.** The SYMBOLIC (K-SUB) `= 1` in Qq, via U-9a
at every ALL-ACTIVE pool (activity supplied by the locus) + U-27 infinitude on
`RB.allActive_infinite`. deps: U-8, U-9a, U-27.

**U-10 `ksub_pool` · medium — nonnegativity DERIVED and ROUTED (R2-12); `he` binder
added (Fable2-G3).**
`statement`: `theorem ksub_pool (he : e ∈ Finset.Icc 1 n) (L : LedgerIV T M)`
`(P : PoolHyp T M RB e hK q₀) (τA : P.Act) :`
`(∀ βA : P.Act, 0 ≤ Aℝ P τA βA) ∧ (∑ βA : P.Act, Aℝ P τA βA) ≤ 1`
— stated over `Aℝ` per D11 (R22, Codex#2-3): the proof's chain (rowVal/μcell/interp)
is ℝ-native; the ℚ facts transfer through the one coercion point, nowhere else.
moves_ref: "K_e's rows are genuine sub-distributions … every summand ≥ 0 (the
ns-bound tail rides INSIDE the K_e term)". deps: U-9a, U-19 · hyp: LedgerIV +
RatBurdens ONLY — the routed nonnegativity is DERIVED: for non-split o,
eval TG = rowVal = Σ μcell ≥ 0 (tg_interp + rep_indep + a μcell-nonneg lemma from
meas_card's card ratios at heights in the domain + xhd_sum); for split o likewise via
j_interp. NO hypothesis about TG on split outcomes or J on non-split outcomes exists
anywhere (the R2-12 swap is structurally impossible now) · sketch: evaluate U-9a,
drop the nonneg exit sums, restrict along act_spec/inactive_vanish (τA ∈ Act supplies the
activity guard via act_spec — U-9a fires at exactly the note's scope).

### Layer S2 — the ℚ(q) system and its solve [16]  *(headcount fixed — Fable2-G4)*

**U-11 `decompFintype` · medium — unchanged** (Fintype on multiset decompositions).
**U-12 `powSubst` · medium — unchanged** (δ : ℕ+; `IsFractionRing.lift`).

**U-12b `powSubst_OKat_evalAt` · PowSubstOK.lean · easy — NEW (serves R14).**
`theorem powSubst_OKat (δ : ℕ+) (q₀ : ℚ) (f : Qq) (h : f ∈ OKat (q₀ ^ (δ:ℕ))) :`
`powSubst δ f ∈ OKat q₀` and `evalAt q₀ ⟨powSubst δ f, _⟩ = evalAt (q₀^(δ:ℕ)) ⟨f, h⟩`
— OK-membership and evaluation transport along a base-change leg: the denominator of
`powSubst δ f` divides `f.denom.comp (X^δ)`, and `(f.denom.comp (X^δ)).eval q₀ =
f.denom.eval (q₀^δ) ≠ 0`. deps: U-12, U-19 · sketch: `Polynomial.eval_comp` +
divisibility of denominators under ring homs.
**U-13 `solve_iff` · easy — unchanged.** **U-14 `solve_exists_unique` · medium —
unchanged.** **U-15 `solve_cramer` · medium — unchanged** (adjugate/Cramer; RS.2's
conditionality = RatBurdens by construction, now in (iv)-POLY form with degree bounds).

**U-16a1 `bSplit_def` · BSplitDef.lean · medium — SPLIT + the halted-member clause
DISPLAYED (Fable G3).** Defines `kTarget` and `bSplit` (DegCons argument licensing
smaller-block legs via U-2), with the summand's def-equation PINNED:
`bSplit T RB hdc e he βlt σ' τ = ∑ o ∈ splitOuts T e τ, RB.J e τ o *`
`∑ g : {g : Fin (T.odata e τ o).m → Multiset T.VType // σ' = ∑ j, g j},`
`∏ j, legFactor o g j` where, for member μ_j := (T.odata e τ o).mem.get j,
`legFactor = if v : verdict-halted μ_j v then (if g j = {v} then 1 else 0)`
`            else powSubst μ_j.δ (βlt μ_j.size (ktri-bound) (state of μ_j) (g j))`
— "τ-halted members contribute FACTOR 1 with σ_j their verdict value, per §T.4's
leaf convention" (S.0): a halted leg forces its σ_j to the verdict SINGLETON
(indicator), continuing legs are β at q^δ. moves_ref: "b_e^split(τ)(σ′) :=
Σ_{o branching} J_{τ,o}(q) · Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m β_{e_j,τ_j(o)}(σ_j)(q^{δ_j})
[… the product ranges over ALL branch members]". deps: U-1, U-2, U-11, U-12.

**U-16a2 `evalRe_def` · EvalReDef.lean · medium — split (G3); also declares
`bhatMeas` (R25).** Defines `evalRe`, the per-pool EVALUATED right side of
(R_e-lump) that `recursion_meas` cites: eval-K-row · β̂ + eval-bTerm + the evaluated
split summand with MEASURED legs β̂ at q₀^(δ:ℕ) (well-typed by `pools_closed`;
halted legs the same indicator as U-16a1) — AND `bhatMeas P B σ' h_ent : P.Act → ℝ`,
its Act-restricted exit-vector face (consumed by U-24a1/a2 and `ReadOffBundle`).
deps: U-16a1, U-19.

**U-16a3 `consumedDeltas_def` · ConsumedDeltas.lean · medium — REWRITTEN (R17,
Codex-5; the REV-4 "stays inside the roster" claim is PURGED).** Defines
`consumedDeltas T F` as the MULTIPLICATIVE CLOSURE (products of ≤ n stored factors,
empty product 1 included — finite by (K-TRI)'s depth bound) and proves its spec
lemma `nested_delta_mem`: for any nesting chain of split/shape legs (length ≤ n by
U-2), the chain's PRODUCT — the semantic index rel. the base prime, DELTA-ABS — lies
in `consumedDeltas`; hence `RegP`/`legs_reg` carry E0 over every EFFECTIVE pool
p^(δ₁·…·δ_k), and `pools_closed` (∀ δ : ℕ+) keeps each in `Pools`.
moves_ref: "δ ranging over 1 AND every base-change index a β_{e_j,τ_j}(q^{δ_j}) leg
of b_e^split or RS.1-SH consumes ([2r] BASE-INDEX CONVENTION + (e2), δ ABSOLUTE)".
deps: U-2, U-12c.

**U-12c `powSubst_mul` · PowSubstMul.lean · easy — NEW (R17).**
`theorem powSubst_mul (δ₁ δ₂ : ℕ+) : (powSubst δ₁).comp (powSubst δ₂) =`
`powSubst (δ₁ * δ₂)` and `theorem pow_pool (q₀ : ℚ) : (q₀ ^ (δ₁:ℕ)) ^ (δ₂:ℕ) =`
`q₀ ^ ((δ₁ * δ₂ : ℕ+) : ℕ)` — nested substitution composes multiplicatively; the
algebraic face of DELTA-ABS. deps: U-12 · sketch: both ring homs agree on X and
constants (`IsFractionRing.lift` uniqueness / `RingHom.ext`); `pow_mul`.

**U-16b `blockSolve` · medium — unchanged** (strong recursion on e ∈ Icc 1 n; σ′
UNRESTRICTED per R2-10: the solve is a function of every σ' : Multiset VType).

**U-16c `blockSolveTot` · BlockSolveTot.lean · medium — NEW (R2-17).** The σ′-FREE
totalized triangular solve: `bTot(τ) := Σ_{term o} TG + Σ_{split o} J · ∏_j legTot`
(halted legs 1, continuing legs `powSubst δ (blockSolveTot …)`), and
`blockSolveTot e := (1 - Kmat)⁻¹ *ᵥ bTot` — the exit-total vector the MARKED pairing
consumes. moves_ref: "the scalar output ι_e^T (I − K_e)^{−1} b_e" (ORIENTATION).
deps: U-14, U-16a pattern · sketch: same WF recursion as U-16b, scalar per state.

**U-17a `blockSolve_spec` · medium** — (R_e-lump) defining equation, EVERY σ′
(R2-10: no SigSet). **U-17b `rexact_solve` · medium — unchanged** ((R_e-exact) from
`rexact` + `nsNull`). **U-18 `rsh_def` · medium — unchanged** (shConv/Rsh from the
Shape record + blockSolve; now takes `WshP ·` as the W_Ŝ presentation). **U-18b
`interp_unique` · easy — unchanged** (interpolant uniqueness on infinite OK sets).

### Layer S3 — pools, evaluation, E0 consequences [10]

**U-19 `evalAt` · medium — unchanged.** **U-20 `eval_det` · easy — unchanged**
(INFRA; moves_ref the S.4(ii) "K_e(p) = A" reading). **U-21a `pow_fixed_vector` ·
easy — unchanged.**

**U-21b `mulVec_abs_bound` · medium — [Nonempty ι] added (R2-16).**
`theorem mulVec_abs_bound [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℚ}`
`(hA : ∀ i j, 0 ≤ A i j) (v : ι → ℚ) (k i) : |((A ^ k) *ᵥ v) i| ≤`
`(Finset.univ.sup' Finset.univ_nonempty fun j => |v j|) * ((A ^ k) *ᵥ 1) i`.
deps: U-23b.

**U-21c `e0_det_ne_zero` · medium** — `EscapeE0 A → (1 - A).det ≠ 0`; the EMPTY case
is `Matrix.det_isEmpty` (det = 1 ≠ 0 — an empty active block is vacuously
nonsingular, matching the note's "realized states only" scope); the nonempty case
uses U-21a/b. deps: U-21a, U-21b.

**U-22 `rs3_det_symbolic` · medium — quantifiers FIXED (R2-13).**
`statement`: `theorem rs3_det_symbolic (T M RB hdc) (hK : ∀ e ∈ Finset.Icc 1 n, …)`
`(hact : ∀ e ∈ Finset.Icc 1 n, ∀ q₀ ∈ allActivePools M,`
`Nonempty (PoolHyp T M RB e (hK e ‹_›) q₀)) :`
`∀ e ∈ Finset.Icc 1 n, (1 - Kmat T RB e (hK e ‹_›)).det ≠ 0`
— per-block hypotheses for the per-block conclusion, `e` bound INSIDE both.
moves_ref: "at all-active primes (cofinitely many …) K_e(p) = A and ρ(A) < 1 gives
det(I − A) ≠ 0; a rational function vanishing at infinitely many prime evaluations
is 0". deps: U-19, U-20, U-21c, U-27 · hyp: RB.allActive_infinite (the (iv)-POLY
cofiniteness face, now over the DEFINED locus) + per-pool packages at that locus ·
sketch: at an all-active pool Act = univ (act_spec + the locus definition); if
det = 0 in Qq its evaluation vanishes there (U-20), contradicting U-21c.

**U-23a `neumann_partial` / U-23b `pow_entry_nonneg` / U-23c `pow_entry_tendsto` ·
easy ×3 — unchanged.** **U-23d `e0_inv_nonneg` · medium — unchanged** (consumer
[4]/SQ.2 only).

### Layer S4 — RS.1-DEEP/RS.2 derivation, the marked pairing, RS.4 [6]
*(headcount fixed, Fable2-G4; the gate is now Layer S5)*

**U-24a1 `active_solve_meas` · ActiveSolve.lean · medium — REDESIGNED (Fable C1;
R14): the measured value IS the active-subsystem solve, PER POOL, guards consumed.**
`statement`: for B : RS1Bundle, L : LedgerIV, e ∈ Icc 1 n, σ', h_ent, ANY relevant
pool q₀ with package `P : PoolHyp T M RB e (hK e) q₀` (RegP-supplied — wild pools
INCLUDED), and any τA : P.Act:
`B.βmeas e he h_ent τA σ' q₀ = ((1 - Aℝ P)⁻¹ *ᵥ bhatMeas P B σ' h_ent) τA`
where `bhatMeas : P.Act → ℝ` := the evaluated exit vector with MEASURED legs:
(algebraMap ℚ ℝ)(eval-bTerm) + the split summand with legs `B.βmeas … (q₀^(δ:ℕ))`
(pools_closed-typed) — the D11 architecture: ℚ-matrix mapped ONCE through `Aℝ`,
everything else ℝ (Codex-7 = Fable2-G1; `Aℝ_det_iff` transports U-21c's det).
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)" +
"Every probabilistic claim in S.4/SQ.2 is about K_e restricted per CTS-M(ii) to the
ACTIVE block". deps: U-13, U-14 (their ℝ instances via `Aℝ` — R22; stale "(over ℚ)"
fixed, Fable#4 O-b), U-16a2, U-19, U-21c · hyp: B.recursion_meas
(W-3) + B.xrb + P (E0 inside) + L (act_target + inactive_vanish give SUBSYSTEM
CLOSURE: entries out of Act vanish, so the active restriction of the measured system
is itself linear) · sketch: β̂ := (βmeas ·)_Act satisfies β̂ = Â β̂ + b̂ by
recursion_meas restricted along the closure; (1 − Â) invertible by U-21c on P.e0
(empty Act: both sides live on an empty type — trivial); uniqueness of the evaluated
solution. NO induction, NO leg evaluation, NO hok claim — the legs enter b̂ as
measured values. **CLOSES from the note's own display; the REV-3 hardness was the
unhypothesized (ii-c) burden, now U-24a2's explicit guard.**

**U-24a2 `interp_read_off` · ReadOff.lean · easy — the (ii-c) gate consumed (C1).**
`statement`: additionally GIVEN `hAV : AVAgree P (blockSolve T RB hdc hK hdet e he τA
σ') (bhatMeas P B σ' h_ent) τA` (the note's sealed per-pool read-off check, per
OBJECT): `∃ hok, (evalAt q₀ ⟨blockSolve … e he τA σ', hok⟩ : ℝ) = B.βmeas e he h_ent
τA σ' q₀`. moves_ref: "the sealed check that the evaluated object's q₀-value … equals
the active-subsystem solve there must pass BEFORE it may be read off; a pole
SURVIVING cancellation at a wild pool is (ii-c)'s FAIL" + the (e3)-FENCE. deps:
U-24a1 · sketch: AVAgree supplies hok + the active-solve value; rewrite with U-24a1.
Uncancelled wild poles are EXCLUDED BY HYPOTHESIS — never claimed absent.

**U-24b `rs2_unique_interp` · Rs2Unique.lean · medium — locus = the ALL-ACTIVE
primes (R16(ii), Codex-4).** `statement`: GIVEN an INFINITE pool set
`S ⊆ allActivePools M` with, at every q₀ ∈ S, a package P and the AVAgree read-off
for every (e, τA, σ') consumed (the explicit `hread` bundle): any family f that is
OK on S and interpolates βmeas there equals `blockSolve …` — "every β_{e,τ}(σ′) is
ONE FIXED rational function" (RS.2's fixedness). The bundle is TYPED DATA (R23,
Codex#2-4): `hread : ReadOffBundle S hS B hdet` (§2.D) — packages at every q₀ ∈ S
and e ∈ Icc 1 n, AVAgree at every (e, τA : Act, σ', h_ent). COORDINATE COVERAGE: at
an all-active pool EVERY (e, τ) is active (`allActivePools` quantifies ∀ e ∀ τ), so
each coordinate's identification set is ALL of S — no coordinate is identified
outside its activity locus, and none is skipped; coverage is auditable from
`ReadOffBundle`'s type. This is the note's own
locus, quoted: "at all-active primes (cofinitely many — only finitely many primes
are roots of some not-identically-zero cell-size polynomial)" (S.4(ii)); RS.2's
assertion "every β_{e,τ}(σ′) is one fixed rational function" is claimed exactly
there. moves_ref: as quoted. deps: U-24a1, U-24a2, U-18b, U-27 · hyp: hread (the
per-pool (ii-c) burden, OPEN — provenance W-6; `allActive_infinite` supplies the
CANDIDATE locus, activity alone does not discharge AVAgree) · sketch: U-24a2 across
S; U-18b uniqueness per coordinate over S. Cramer form via U-15.

**U-25 `marked_def` · easy — aggregate now DEFINED (R2-17).**
`noncomputable def markedPairing … : MuHat := ⟨RB.ι e ⬝ᵥ ((1 - Kmat T RB e (hK e))⁻¹`
`*ᵥ bTot T RB hdc e he)⟩` (bTot from U-16c) + the no-Add/no-coercion fence check.
moves_ref: "(RS.1-MARKED) the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed
MARKED-entrance total … NEVER summed into R_σ." Identification with `M.markedVal` =
the PINNED W1m (never claimed here).

**U-27 `ratfunc_eval_infinite` · medium — unchanged** (the shared infinitude engine).

**U-28 `rs4_rational_step` · Rs4.lean · medium — full inherited set (R2-19).**
`statement`: `theorem rs4_rational_step (C : RS4Chain T M RB hdc hK F)`
`(hdet : ∀ e ∈ Finset.Icc 1 n, (1 - Kmat T RB e (hK e ‹_›)).det ≠ 0) :`
`(∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) = 1`
moves_ref: "(RS.4) Σ_σ R_σ = 1 identically in q … RS.4 inherits EVERY condition of
the block solve". deps: U-18, U-27 · hyp: THE DISPLAYED INHERITED SET, all explicit
in RS4Chain (R2-19): C.L (nine CL-5 inputs) · C.B (RS.1's set: xrb/CL-9,
recursion_meas/CL-10+CL-8 provenance) · C.hns ((ns-null) proof) · C.pools_e0 +
C.legs_reg (ESCAPE(E0)/CL-1 in its FULL per-pool quantifier — REV 4, Fable C1) ·
C.WshP/wsh_ok (CL-17(ii)) · RB in (iv)-POLY form (CL-6)
+ XHD-s geoms + INIT-RAT ιP + (J-RAT) jP · C.x3_total (X.3/CL-4, pinned W-4) ·
C.rs1_equates (pinned W-1e) · C.rsh_interp (pinned W-1's shadow) · sketch:
eval(Σ Rsh − 1) at p ∈ PrimePools = Σ Rval − decidedTotal = 0 (rsh_interp,
rs1_equates, x3_total); prime_infinite + U-27. The docstring lists every tag: the
acceptance fence "may NOT be marked unconditional before those close" verbatim.

### Layer S5 — the schema-consistency gate, REBUILT on the NOTE's n = 2 instance
### (R26, Codex#3-1) and one-display-split (R28) [23]

THE INSTANCE (R26; moves_ref for the layer: "The n = 2 instance is the 1×1 case
(W6's geometric series, denominator q² + q + 1; `msW_eighth_le` its p = 2
inequality shadow)"): ONE block-2 state τ★; THREE outcomes —
  o_K   (c=1, m=1, member size 2)          rowVal = q₀⁻³   (kcol; 1/8 at q₀ = 2)
  o_spl (c=0, m=2, verdicts (1,1)+(1,1))   rowVal = 1 − q₀⁻¹     (termFin)
  o_in  (c=0, m=1, verdict (1,2))          rowVal = q₀⁻¹ − q₀⁻³  (termFin)
part1: q₀⁻³ + (1−q₀⁻¹) + (q₀⁻¹−q₀⁻³) = 1 ✓ (every row mass ≥ 0 at q₀ ≥ 2 ✓);
E0: A = [q₀⁻³] < 1 ✓; det(1 − K) = 1 − q⁻³ = (q−1)(q²+q+1)/q³ ≠ 0 ✓; the REDUCED
solve: β_{(1,2)} = (q+1)/(q²+q+1), β_{(1,1)²} = q²/(q²+q+1) — the note's displayed
denominator EXACTLY, and their sum = 1 (the checksum shadow). No split outcomes
(S.7: "the deep convolution is thin"), so bSplit = 0 and consumedDeltas ⊇ {1} only.
CLAIM (R11 unchanged): schema consistency with the note's instance; the W-11
process gate still owns intended-CTS instantiation.

**U-29a `n2_data` · N2Data.lean · medium** — the CONSTRUCTION (defs only): the
three-outcome TableShape (vEquiv on the degree-≤2 pairs; Wloc/Wstate), MeasuredSide
(level-N boxes; cell events realizing the three row masses as card ratios; pools =
all prime powers), RatBurdens data (q⁻³, 1−q⁻¹, q⁻¹−q⁻³ in PolyGeom form with the
pinned degree data), SCSData/ShapeFam data. deps: Defs.

**U-29b-i…vii — LedgerIV items (1)–(5), ONE FIELD EACH (R28, Codex#3-4):**
`n2_xhd_sum` (easy) · `n2_xhd_stray` (easy) · `n2_xhd_orphan` (easy) · `n2_d4r0`
(easy) · `n2_part1` (easy — the display: q₀⁻³ + (1−q₀⁻¹) + (q₀⁻¹−q₀⁻³) = 1,
`field_simp`) · `n2_rep_indep` (easy) · `n2_meas_card` (medium — the card-ratio
identities at level N). Each: one LedgerIV field at the instance. deps: U-29a.

**U-29b-viii…xi — LedgerIV items (6)–(9), ONE DISPLAY EACH (Codex#3-5):**
`n2_kstep_hmc` (medium — kstep_one + hmc, 1×1 scalar powers: kstep k = q₀⁻³ᵏ) ·
`n2_act` (easy — act_target; all-active at q₀ ≥ 2, vacuous inactive case) ·
`n2_init` (medium — init_agg/init_count/ent_count_card on the one entrance shape) ·
`n2_comp` (easy — comp_once, a one-term height sum). deps: U-29a.

**U-29b3 `n2_degcons_scs` · N2DegScs.lean · easy — REBUILT (R26, Codex#3-1).**
DegCons + SCSData on the THREE-outcome roster: sizes (2), (1,1), (2) with sums
≤ 2 ✓; (m,c) routing (1,1)/(2,0)/(1,0) ✓; SCS at o_K: the single member has size
2 = e ✓ (window data W=2, D=1, ℓ=2, g=1, μ=2). deps: U-29a.

**U-29c `n2_pool` · N2Pool.lean · easy** — PoolHyp at q₀ = 2, EscapeE0 for
A = [1/8]: geometric decay (`tendsto_pow_atTop_nhds_zero_of_lt_one`). deps: U-29a.

**U-29d-i…iii — RS1Bundle, ONE DISPLAY EACH (Codex#3-6):**
`n2_beta` (medium — βmeas := the evaluated solve values, β_bdd from the explicit
[0,1] bounds) · `n2_recursion` (medium — the 1×1 measured fixpoint:
β̂ = q₀⁻³·β̂ + (exit masses), checked by field arithmetic) · `n2_xrb_rexact` (easy —
h_ent-independence and βfull = βmeas by construction). deps: U-29a/b/c.

**U-29d2 `n2_pools_all` · N2Pools.lean · medium** — legs_reg/pools_e0 at EVERY base
prime: 1×1 packages, entry q₀⁻³ < 1 uniformly at q₀ ≥ 2. deps: U-29a, U-29c.

**U-29d-iv…vi — RS4Chain, ONE DISPLAY EACH (Codex#3-7):**
`n2_sigmas` (easy — sig_exact forces Sigmas = {(1,1)², (1,2), (2,1)}, the three
degree-2 multisets) · `n2_x3_rs1` (easy — decidedTotal := Σ Rval; x3_total/
rs1_equates by construction) · `n2_rsh` (medium — rsh_interp at the explicit
values: eval β_{(1,2)} = (q₀+1)/(q₀²+q₀+1) etc.). deps: U-29d-i…iii, U-29d2.

**U-29d5 `n2_readoff` · N2ReadOff.lean · medium — NEW (Fable#4-F2).** Inhabits
`ReadOffBundle`: S := the all-active pools of the instance (all q₀ ≥ 2); AVAgree
from the explicit reduced denominators (q²+q+1 ≠ 0 at every q₀ ≥ 2 supplies hok;
the active solve = the explicit values; no split legs). deps: U-29c, U-29d2, U-24a2.

**U-29e `n2_denominator` · N2Denom.lean · easy — the W6 CHECK (explicit).**
`(1 - Kmat).det = (q³−1)/q³ ≠ 0`, and the reduced solve entries are
`β_{(1,2)} = (q+1)/(q²+q+1)`, `β_{(1,1)²} = q²/(q²+q+1)` — denominator q² + q + 1
exactly, sum = 1 (`field_simp`/`ring` over `RatFunc ℚ`). deps: U-29a, U-16b.

---

## 3c. Full specs for units carried forward (self-contained: REV 2 is retired)

**U-1** `theorem dispatch_spec (o : Outcome V State) (h1 : 1 ≤ o.m) (hc : o.c ≤ o.m) :
(routeOf o = .termFin ↔ o.c = 0) ∧ (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧
(routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m)` · sketch: unfold, split_ifs, omega.

**U-2** `theorem ktri (hdc : DegCons T) (he : e ∈ Finset.Icc 1 n) {τ o}
(hm : 2 ≤ (T.odata e τ o).m) : ∀ μ ∈ (T.odata e τ o).mem, μ.size < e` · sketch:
μ.size + (m−1) ≤ Σ sizes ≤ e via size_pos on the other members; omega.

**U-3** `theorem kcol_agree (hdc) (he) (hmem : ∃ μ ∈ mem, μ.continuing ∧ μ.size = e) :
(T.odata e τ o).m = 1` · sketch: contrapose with U-2.

**U-5** `theorem scs_stage (S : SCSData T) (hm : (T.odata e τ o).m = 1) :
S.W' e τ o * S.D' e τ o = S.W e τ o * S.D e τ o` · moves_ref: "W′·D′ = μ·e·g·D =
(g·μ)·e·D = ℓ·e·D = W·D" · sketch: stage_W/stage_D rewrite; U-4's g·μ = ℓ, W = e·ℓ; ring.

**U-6** `theorem scs (S : SCSData T) (hdc : DegCons T) (he) (hk : routeOf (T.odata e τ o)
= .kcol) : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e` · moves_ref: "(SCS) a (c = 1, m = 1)
outcome's single child inherits the block size: e₁ = e" · sketch: hk + U-1 ⟹ m = 1;
the only member is selIdx, continuing (sel_continuing); cluster_child + U-5 +
cluster_parent: size = W′D′ = WD = e.

**U-11** `instance decompFintype [DecidableEq V] (m σ') :
Fintype {g : Fin m → Multiset V // ∑ j, g j = σ'}` · sketch: induct on m; each g 0 ≤ σ'
ranges over finitely many sub-multisets.

**U-12** `noncomputable def powSubst (δ : ℕ+) : Qq →+* Qq` + `powSubst_X/`_C lemmas ·
moves_ref: "composed with q ↦ q^{δ_j} … ([2r] (e2), δ absolute)" · sketch:
`IsFractionRing.lift` over `aeval (X^(δ:ℕ))`; δ ≥ 1 ⟹ nonzero ↦ nonzero.

**U-13** — GENERIC CARRIER (R22) + `[DecidableEq ι]` (Fable#4-F1): `theorem solve_iff
[Fintype ι] [DecidableEq ι] [CommRing R] (K : Matrix ι ι R) (b β : ι → R) :
β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b` · sketch: sub_mulVec/one_mulVec; sub_eq_iff.
Instances at Qq (U-14/16b) AND at ℝ via `Aℝ` (U-24a1). BATCH NOTE (R29, Fable#4-F1):
`[DecidableEq ι]` is likewise added at EVERY generic-index matrix `1`/`^` site —
`EscapeE0` (§2.C, done), U-21a, U-21b, U-23a, U-23b, U-23c, U-23d — Mathlib's
`Matrix.one`/`Monoid.npow` require it; semantically inert (`Classical.decEq`).

**U-14** — GENERIC CARRIER (R22): `theorem solve_exists_unique [Fintype ι]
[DecidableEq ι] [Field F] (K : Matrix ι ι F) (b : ι → F) (hdet :
(1 - K).det ≠ 0) : ∃! β, β = K *ᵥ β + b` (witness `(1-K)⁻¹ *ᵥ b`) · Mathlib:
`isUnit_iff_ne_zero` + `Matrix.isUnit_iff_isUnit_det` + `mul_nonsing_inv`/
`nonsing_inv_mul` + `mulVec_mulVec`. F := Qq at the solve; F := ℝ at U-24a1
(det transported by `Aℝ_det_iff`).

**U-15** `theorem solve_cramer (hdet) : (1 - K)⁻¹ *ᵥ b = fun τ => ((1 - K).det)⁻¹ *
((1 - K).adjugate *ᵥ b) τ` · moves_ref: "β_e = adj(I − K_e) b_e / det(I − K_e)
entrywise" · Mathlib: `Matrix.inv_def`/`cramer_eq_adjugate_mulVec`/
`det_smul_inv_mulVec_eq_cramer`.

**U-16b** `noncomputable def blockSolve (T RB hdc hK hdet) : ∀ e ∈ Finset.Icc 1 n,
T.State e → Multiset T.VType → Qq` — strong recursion on e; body
`(1 - Kmat T RB e (hK e))⁻¹ *ᵥ (bTerm T RB e σ' + bSplit T RB hdc e he βlt σ')` ·
moves_ref: "blocks solve bottom-up, each b_e^split leg already solved".

**U-17a** `theorem blockSolve_spec (e ∈ Icc 1 n) (σ' : Multiset T.VType) :
blockSolve … e he · σ' = Kmat … *ᵥ (blockSolve … e he · σ') + bTerm … σ' +
bSplit … (blockSolve-restriction) σ'` · moves_ref: "(R_e-lump) β_e = K_e β_e +
b_e^{term,fin} + b_e^split [UNCONDITIONAL]".

**U-17b** `theorem rexact_solve (B) (hns : B.nsNull) : ∀ e he h_ent τ σ' q₀,
B.βfull e he h_ent τ σ' q₀ = B.βmeas e he h_ent τ σ' q₀` · moves_ref: "(R_e-exact)
β_e^full = β_e [GIVEN (ns-null) — CLOSED at [3t] §T.2]" · sketch: fire `rexact`.

**U-18** `noncomputable def shConv (…) (Ŝ : Shape T) (σ) : Qq := ∑ g : {g : Fin Ŝ.k →
Multiset T.VType // σ = Ŝ.σ0 + ∑ i, g i}, ∏ i, powSubst (Ŝ.δOf i)
(blockSolve … (Ŝ.eOf i) (Ŝ.eIcc i) (Ŝ.τOf i) (g i))` and `Rsh … (WshP) (σ) :=
∑ Ŝ ∈ F.Sh, (WshP Ŝ).val * shConv … Ŝ σ` · moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) ·
Σ_{σ = σ₀(Ŝ) ⊎ …} ∏ β_{e_i,τ_i}(σ_i)(q^{δ_i})".

**U-18b** `theorem interp_unique (S : Set ℚ) (hS : S.Infinite) (f g : Qq)
(hf hg : ∀ x ∈ S, · ∈ OKat x) (h : ∀ x ∈ S, evalAt x f = evalAt x g) : f = g` ·
sketch: U-27 on f − g.

**U-19** `def OKat (q₀) : Subring Qq` ({f | f.denom.eval q₀ ≠ 0}) +
`noncomputable def evalAt (q₀) : OKat q₀ →+* ℚ` + `evalAt_coe` · sketch: denom
divisibility closure; `RatFunc.eval_add`/`eval_mul` under the membership hypotheses.

**U-20** `theorem eval_det [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (OKat q₀)) :
evalAt q₀ M.det = (M.map (evalAt q₀)).det` · via `RingHom.map_det`.

**U-21a** `theorem pow_fixed_vector (h : A *ᵥ v = v) : ∀ k, (A ^ k) *ᵥ v = v`.

**U-23a** `(1 - A) * (∑ m ∈ Finset.range k, A ^ m) = 1 - A ^ k` (telescope).
**U-23b** `(∀ i j, 0 ≤ A i j) → ∀ k i j, 0 ≤ (A ^ k) i j` (induction).
**U-23c** `EscapeE0 A → ∀ i j, Tendsto (fun k => (A ^ k) i j) atTop (nhds 0)`
(squeeze between 0 and `((A^k) *ᵥ 1) i`).
**U-23d** `EscapeE0 A → ∀ i j, 0 ≤ (1 - A)⁻¹ i j` · moves_ref: "the Neumann series
converges, and (I − A(q₀))^{−1} ≥ 0" · sketch: `(1-A)⁻¹ = Σ_{m<k} A^m + (1-A)⁻¹ A^k`
(U-23a); nonneg partial sums (U-23b); remainder → 0 (U-23c); closed limit.

**U-27** `theorem ratfunc_eval_infinite (f : Qq) (S : Set ℚ) (hS : S.Infinite)
(hden : ∀ x ∈ S, f.denom.eval x ≠ 0) (hval : ∀ x ∈ S, RatFunc.eval (RingHom.id ℚ) x f
= 0) : f = 0` · moves_ref: "a rational function equal to 1 at infinitely many prime
powers is identically 1" (consumers apply to f − 1) · sketch: num vanishes on S;
`Polynomial.eq_zero_of_infinite_isRoot`; `RatFunc.num_eq_zero_iff`-style closure.

---

## 3b. Load-bearing DAG edges (acyclic)

U-1 → {U-3, U-6, U-8, U-16a1} · U-2 → {U-3, U-16a1} · U-4 → U-5 → U-6 · U-6 ⟹ `hK`
for {U-8, U-16b/c, U-22, U-24a1/a2/b, U-25, U-29} · U-8 → U-9a → {U-9b, U-10} ·
U-11, U-12 → {U-16a1, U-18} · U-12, U-19 → U-12b → {U-24a2 plumbing, W-1 hok} ·
U-12 → U-12c → U-16a3 (the DELTA-ABS composition — Fable#3 O-2) ·
U-13 → U-14 → {U-15, U-16b/c, U-24a1} · U-16a1 → U-16a2 → U-24a1; U-16a1 → U-16b →
{U-17a, U-18, U-29}; U-16a3 → RegP · U-16c → U-25 · U-19 → {U-9a, U-10, U-20, U-22,
U-16a2} · U-23b → U-21b; U-21a, U-21b → U-21c → {U-22, U-23d, U-24a1} · U-23a/b/c →
U-23d · U-27 → {U-9b, U-18b, U-22, U-24b, U-28} · U-24a1 → U-24a2 → U-24b · U-22 →
hdet of {U-16b/c, U-24a2/b, U-25, U-28} · RegP/AVAgree → {U-24a1, U-24a2, U-24b,
RS4Chain.legs_reg} (the guards are CONSUMED — Fable C1's symptom is gone).
CONSUMPTION-DAG discipline: U-24a1/a2/b consume `xrb`/`recursion_meas`; nothing
proves toward `xrb`; no PCI site is consumed by S.1-shaped content.

## 4. Trust surface & audit flags (REV 3)

1. NO `True` fields; NO vacuous disjuncts (R2-1 struck); grep duties at phase E:
   `': True'` and `'∨ True'` both empty on Defs.lean/Interfaces.lean.
2. `xrb` is the honest XRB interface (open; pinned W-2). `recursion_meas` (pinned
   W-3), `x3_total` (W-4), `rs1_equates` (W-1e), `rsh_interp` (W-1 shadow),
   `wsh_interp`, and `W1m` are the measured GIVENs — each maps to a note tag, none
   is a wave-2 conclusion.
3. The event carrier (R7) is the (iv)-MEAS/D4R.0/XHD trust boundary: masses =
   eventually-exact card ratios; auditor checks the ledger's nine fields against
   S.0's displayed ledger 1:1.
4. `rowVal` is RS.0(α)'s object; `rep_indep` is its weighted-grouping form VERBATIM
   (R2-5) — no cellwise strengthening exists.
5. PART-2's marked surplus row has NO carrier (unconsumable). ESCAPE-UNIF does not
   exist. `Act` is determined by `act_spec` (R2-8). `allActivePools` is a defined
   locus; only its infinitude is a burden.
6. `PolyGeom` restores the (iv)-POLY degree bounds + XHD-s geometric denominators
   (R2-7); `Pools` is pinned to prime powers with the δ-closure law (R2-7/14).
7. U-29's claim is SCHEMA CONSISTENCY (R11) — flag any reading of it as intended-
   instance inhabitation; that is the §5 wave-4 process gate.
8. S.7 / probe roster / (CUT-WD)'s proof / junk determinants: census-side; (BDY) in
   scope as U-7a/b/c + pinned W-8.
9. (REV 4) The ACT scope is GUARDS, not zero rows: `act_row` DELETED (undisplayed);
   part1/rep_indep/xhd_sum/no_stray/meas_card/kstep laws guarded by `activeState` —
   wild pools instantiable; auditor checks no ledger field asserts a mass claim at an
   unrealized source.
10. (REV 4) `RegP` and `AVAgree` are CONSUMED: U-24a1 (packages at every relevant
   pool incl. wild legs), U-24a2 (the per-object (ii-c) read-off hypothesis), U-24b
   (`hread` over an infinite read-off-valid family), `RS4Chain.legs_reg`. Flag any
   future unit that reads a numeric β/R value without citing a package + AVAgree.

## 5. Conventions (phase E / prover fleet) + census

Build per file `lake env lean LeanUrat/MovesS/<file>.lean`; `#print axioms` per unit
(Lean-core only; `sorryAx` flagged). Skeleton `sorry`s (`OKat`/`evalAt` bodies,
`kTarget`, `Kmat`, `bTerm`, `consumedDeltas`) elaborate at phase E BEFORE fan-out;
`bSplit`/`evalRe`/`bTot` live in U-16a/c. Statement changes to §2/§2.E = statement-
fence events. WAVE-4 PROCESS GATE (W-11): before MovesS results are cited by MovesU
with real semantics, MovesV/MovesT must exhibit instances of every §2 structure over
the real CTS objects and discharge W-1/W-1e/W-1m/W-2/W-3/W-4/W-7/W-8/W-10; the
campaign ledger tracks this per structure.

**Census (REV 7): 68 units = 32 easy / 36 medium / 0 hard** (S0:9 · S1:4 · S2:16 ·
S3:10 · S4:6 · S5:23). Easy: {U-1, U-2, U-3, U-5, U-7a/b/c, U-12b, U-12c, U-13,
U-18b, U-20, U-21a, U-23a/b/c, U-24a2, U-25} (18, wave-2 core) + S5's
{b-i…vi, b-ix, b-xi, b3, c, d-iii, d-iv, d-v, e} (14); medium the remaining 36
(S5's {29a, b-vii, b-viii, b-x, d-i, d-ii, d2, d-vi, d5} = 9 + 27 core). NO hard
units (the REV-3 hard dissolved under R14; unchanged).

---

## 6. Findings → repairs (cumulative; REV-2 audit rows kept, REV-3 rows appended)

**Round 1 audit (19c/3g) → REV 2:** all 22 repaired as recorded in the REV-2 table
(True-tags → contentful fields; XRB de-defined; RatBurdens; hK argument; SP.1
carriers; (BDY) halves; sig_covers; PART-1 chain; δ:ℕ+; DegCons in bSplit; Icc 1 n;
U-17b; Shape record; U-22 package; recursion de-malformed; RS.1-SH/MARKED deferred;
RS.4 two inputs; inhabitation batch; U-10 typing; U-20 ref; 3 hards split). REV-2
residuals found by the re-audit are below.

| R2-# | class | REV-3 repair | where |
|---|---|---|---|
| 1 | crit | `∨ True` disjunct DELETED; `memberOf_ne_sel` states the plain inequality | §2.A |
| 2 | crit | `flank_zero : flankCount = 0 → flankWidth = 0` added; U-4's chain complete | §2.A, U-4 |
| 3 | gap | declaration order fixed (data before laws; SplitTy eliminated; consumedDeltas moved after ShapeFam); order = spec | §2 |
| 4 | crit | ORCHESTRATOR RULING: counting-native event carrier (Box/cellEvt/card-ratio masses); XHD two-sided exactness (no_stray/no_orphan), D4R.0 as event disjointness, (iv)-MEAS as meas_card | R7, §2.B |
| 5 | crit | `rowVal` carrier + `rep_indep` = RS.0(α)'s weighted-grouping equality VERBATIM (row-level, not cellwise) | §2.B |
| 6 | crit | `kstep_one` ties kstep to the measured kernel row (kstep ≢ 0 now violates part1); `activeState` classification + act_row/act_target; `entCount`/`init_count` (ENT-COUNT); `ιshH`/comp_once + init_count = the (COMP-h)→(COMP-hΣ) chain, (COMP-Σ) = hmc | §2.B |
| 7 | crit | Pools pinned to prime powers + δ-closure; `allActivePools` a DEFINED locus (infinitude the only burden); `PolyGeom` restores (iv)-POLY degree bounds + XHD-s geometric denominators; ι in ENT-COUNT polynomial form | §2.B/C |
| 8 | crit | `act_spec` (iff) determines Act from CTS-M(ii)'s classification; empty Act only when the note itself has no realized states (U-21c covers it via det_isEmpty) | §2.C, U-21c |
| 9 | crit | βfam/β_ok/β_interp DELETED from RS1Bundle; the interpolant is DERIVED (U-24a per-pool identification, U-24b uniqueness/fixedness) — RS.2 no longer assumed | R8, §2.D, U-24a/b |
| 10 | crit | SigSet/sig_covers DELETED; σ′ unrestricted everywhere (recursion, solve, spec); finite sums via `verdictImage`; U-24b's functional equality now follows on the full domain | R9, §2.A, U-8/17a/24b |
| 11 | crit | RS.4's σ-index := `Multiset VType` + `Sigmas` Finset; W-1 typechecks | §2.D, §2.E |
| 12 | crit | U-10's nonnegativity ROUTED (TG↔non-split, J↔split) and DERIVED from the ledger — no swapped hypotheses exist | U-10 |
| 13 | crit | U-22: `e` bound inside both hypothesis and conclusion (∀ e ∈ Icc 1 n) | U-22 |
| 14 | gap | `pools_closed` (q₀ ↦ q₀^δ) added; U-24a's base-changed legs well-formed | §2.B, U-24a |
| 15 | gap | U-7 split into U-7a/7b/7c, one display each | §3 S0 |
| 16 | gap | U-21b takes `[Nonempty ι]`; empty case isolated in U-21c (`Matrix.det_isEmpty`) | U-21b/c |
| 17 | gap | `bTot`/`blockSolveTot` (U-16c) define U-25's aggregate; `markedVal` carrier added; W-1m pinned and typeable | U-16c, §2.B, §2.E |
| 18 | gap | ALL deferrals pinned as Props over minimal carriers (TreeIface/ReadLedger/FiberIface); convergence pinned as W-10; W-9 retired (subsumed by R7) | §2.E |
| 19 | gap | RS4Chain carries the full inherited set (LedgerIV, RS1Bundle, hns, pools_e0, CL-17(ii) presentation, POLY-form burdens) + the two pinned primewise inputs; U-28's docstring lists every tag | §2.D, U-28 |
| 20 | crit | U-29 → `consistency_n2`: covers ALL §2 structures; claim renamed to schema consistency; intended-instance inhabitation = the W-11 process gate | R11, U-29, §5 |

**Fresh-Fable audit (2 crit / 4 gap) → REV 4:**

| F-# | class | REV-4 repair | where |
|---|---|---|---|
| C1 | crit | U-24a → U-24a1 (measured value = active-subsystem solve, per pool, from recursion_meas + subsystem closure + E0 — no induction, no leg evaluation, no hok claim) + U-24a2 (symbolic read-off GIVEN AVAgree — the (ii-c)/(e3)-FENCE burden as explicit hypothesis); U-24b conditional on an infinite read-off-valid family (`hread`); RegP/AVAgree now CONSUMED; RS4Chain gains `legs_reg` (CL-1's full quantifier); new U-12b transports OK/eval along q₀ ↦ q₀^δ. U-24a CLOSES — no STUCK | R14, U-24a1/a2/b, §2.D |
| C2 | crit | `act_row` DELETED (undisplayed); part1/rep_indep/xhd_sum/xhd_no_stray/meas_card/kstep_one/hmc/init_*/comp_once GUARDED by `activeState` (the note's "realized states only"/"restricted to the ACTIVE block" scope); `act_target` kept (the displayed entry-INTO-inactive vanishing); wild pools instantiable; U-9a/9b/10 carry the guard | R13, §2.B, U-9a/9b/10 |
| G1 | gap | `kstep_one`'s target predicate pinned hK-free: `∃ μ ∈ mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β` | §2.B |
| G2 | gap | W-1's rfl-conjunct STRUCK; W1_RS1SH = the measured density clause only, symbolic half noted definitional; binders unshadowed; `∃ hok` type-ascribed | §2.E |
| G3 | gap | U-16a split → U-16a1 (bSplit with the PINNED def-equation incl. the halted-member factor-1/verdict-singleton indicator, §T.4 cited) / U-16a2 (evalRe) / U-16a3 (consumedDeltas + the δ-ABSOLUTE fence) | §3 S2 |
| G4 | gap | `entLvl`/`entInst` carriers + `ent_count_card`: I^ent = the card of the ε-instance event at the shape's own defining level | §2.B |

**Parallel rev-4 verdicts — Codex FINAL (6 crit / 2 gap) + Fable#2 (1 crit / 4 gap),
11 distinct findings → REV 5:**

| finding | class | REV-5 repair | where |
|---|---|---|---|
| Codex-1 | crit | `sig_exact`: Sigmas ↔ the full degree-n verdict-type roster via the new `TableShape.vdeg`/`finV` (MovesSp vocabulary); no menu freedom; `sig_ne` demoted to a derivable lemma | R18, §2.A, §2.D |
| Codex-2 | crit | W-1 inherits the exact roster through the pinned Sigmas — quantifies the note's full σ-range | §2.E |
| Codex-3 | crit | `prime_base`: PrimePools = base primes (δ = 1); x3_total/rs1_equates/rsh_interp re-domained | R18, §2.D |
| Codex-4 | crit | U-24b's locus := infinite `S ⊆ allActivePools M` — every coordinate active at every point of S (the note's own cofinite all-active locus, quoted in-unit); no uniqueness outside a coordinate's activity locus | R16(ii), U-24b |
| Codex-5 | crit | CONVENTION DELTA-ABS declared ONCE: stored δ = per-step factor, semantic index = chain product; `powSubst_mul` (U-12c); `consumedDeltas` = multiplicative closure (≤ n factors, finite by (K-TRI)) with spec lemma `nested_delta_mem`; RegP/legs_reg coverage re-derived; the "stays inside the roster" remnant PURGED | R17, §2.A/D, U-12c, U-16a3 |
| Codex-6 | crit | W-10 gains summand nonnegativity — the note's "positive series", Tonelli-licensed | §2.E |
| Codex-7 = Fable2-G1 | gap+gap | D11 coercion architecture: `Aℝ P := P.A.map (algebraMap ℚ ℝ)` declared once in Defs; U-24a1/AVAgree/U-24a2 stated over ℝ through it; `Aℝ_det_iff` transports U-21c | D11, §2.C, U-24a1/a2 |
| Codex-8 | gap | U-29 → U-29a (construction) / 29b (ledger laws) / 29c (pool+E0) / 29d (bundles) / 29e (the W6 denominator display) — Layer S5 | §3 S5 |
| Fable2-C1 | crit | `recursion_meas` + pinned `W3_recursion` gain the `activeState` guard (identical quantifiers); junk-block rows demand nothing at wild pools; U-24a1 unaffected (act_spec at τA ∈ Act) | R16(i), §2.D, §2.E |
| Fable2-G2 | gap | `W1m_marked` GATED per pool: OKat membership (the (ii-c) pass) is a hypothesis, agreement the conclusion — nothing demanded where the gate fails | §2.E |
| Fable2-G3 | gap | U-10 gains `he : e ∈ Finset.Icc 1 n` | U-10 |
| Fable2-G4 | gap | layer headcounts corrected (S2 [16], S4 [6], new S5 [5]); census re-enumerated | §3 |

**Parallel rev-5 verdicts — Codex#2 (2 crit / 4 gap) + Fable#3 (0 crit / 2 gap;
DELTA-ABS/guards/U-24a1/U-24b/Aℝ directly verified) → REV 6:**

| finding | class | REV-6 repair | where |
|---|---|---|---|
| Codex#2-1 | crit | `vEquiv : VType ≃ {(e,f) // e·f ≤ n}` + `vdeg_spec` — the verdict vocabulary pinned STRUCTURALLY (one label per pair, none extra/missing); with sig_exact, Sigmas = the note's roster at every instance | R20, §2.A |
| Codex#2-2 | crit | `prime_base` an IFF: PrimePools = ALL base primes; `prime_infinite` demoted to a lemma (`Nat.exists_infinite_primes`); x3_total/rs1_equates/rsh_interp/legs_reg re-domained to every prime | R21, §2.D |
| Codex#2-3 (+Fable#3-G2) | gap+gap | U-13 over `[CommRing R]`, U-14 over `[Field F]` (ℝ instances exist at U-24a1's seam); U-10's conclusion over `Aℝ P`; D11 prose corrected (O-3) | R22, §3c, U-10 |
| Codex#2-4 | gap | `ReadOffBundle` — hread as TYPED DATA: packages ∀ q₀ ∈ S, ∀ e ∈ Icc 1 n; AVAgree ∀ (e, τA, σ', h_ent); U-24b consumes it | R23, §2.D, U-24b |
| Codex#2-5 | gap | U-29b → U-29b1 (ledger counting laws) / b2 (flow laws) / b3 (DegCons+SCS) | R24, §3 S5 |
| Codex#2-6 | gap | U-29d → U-29d1 (RS1Bundle) / d2 (all-prime pool obligations) / d3 (RS4Chain assembly) | R24, §3 S5 |
| Fable#3-G1 | gap | elaboration order made real: `Interfaces.lean` placement (import DAG = declaration order); legs_reg after PrimePools; `splitOuts` declared; `bhatMeas` in U-16a2; `rsh_interp`'s hdet typed | R25, §2.C/D |
| Fable#3 O-2/O-3/O-4 | obs | U-12c edge added to §3b; D11 prose fixed; header now directs citation to the acceptance record, never the note's stale in-body trailer | §3b, D11, header |

**Parallel rev-6 verdicts — Codex#3 (1 crit / 7 gap; roster pin, all-prime iff,
carriers, ReadOffBundle ALL AFFIRMED) + Fable#4 (0 crit / 2 mechanical gaps; all six
directed checks PASS) → REV 7:**

| finding | class | REV-7 repair | where |
|---|---|---|---|
| Codex#3-1 | crit | the n = 2 gate rebuilt on the NOTE's instance: one state, THREE outcomes (kcol q⁻³ = the msW_eighth_le 1/8 shadow; termFin (1,1)² and (1,2)); joint inhabitability EXHIBITED — part1 sums to 1, E0 entry < 1, det = (q³−1)/q³, reduced solve β_{(1,2)} = (q+1)/(q²+q+1), β_{(1,1)²} = q²/(q²+q+1), sum 1 | R26, §3 S5 |
| Codex#3-2 | gap | Wloc/Wstate (TableShape) + Went (MeasuredSide) fixed BEFORE the burdens; tg_deg/j_deg/ι_deg pin every degBound to them (the note's W_loc/W_state/W_ent, quoted) | R27, §2.A/B/C |
| Codex#3-3 | gap | W_Ŝ tethered: wshval_bdd (mass) + shEvt/wshval_card (counting face) + the pinned W17ii (XHD-s × (SIB)-COUNT production, owners [1v]/[3t], stays OPEN) | R27, §2.D/E |
| Codex#3-4/5/6/7 | gap×4 | S5 one-display splits: b1 → 7 one-field units; b2 → 4; d1 → 3; d3 → 3 | R28, §3 S5 |
| Codex#3-8 | gap | ONE canonical location `MovesS/Interfaces.lean`; §2.E heading, R10, and the §4 grep duty updated; no SyncDefs.lean | R29 |
| Fable#4-F1 | gap | `[DecidableEq ι]` batch: U-13 (displayed), EscapeE0 (§2.C), U-21a/b, U-23a–d (batch note at U-13) | R29 |
| Fable#4-F2 | gap | NEW U-29d5 `n2_readoff`: ReadOffBundle inhabited at the n = 2 instance (explicit hok from q²+q+1 ≠ 0) | R28, §3 S5 |
| Fable#4 O-a/b/c | obs | SyncDefs labels canonicalized; U-24a1's "(over ℚ)" dep fixed; consumedDeltas/markedPairing phase-E clarifiers in R29 | R29 |

STATUS: REV 7 complete, 2026-07-27. Cumulative: R1 22/22 → R2 20/20 → R3 6/6 →
R4 11/11 → R5 8/8 → R6 10/10 repaired (1 crit / 9 gap + 3 obs); nothing pushed
back, no STUCK. 68 units = 32 easy / 36 medium / 0 hard. The structural core is
affirmed by BOTH verifiers (Codex#3: roster/domain/carrier/read-off repairs sound;
Fable#4: all directed checks pass). Awaits the closing dual confirmation on REV 7.

codex
I’m checking the REV 7 repairs against the displays themselves, including the cubic-shadow arithmetic and the claimed one-display/mechanical closures.
codex
1. **CRITICAL — the REV-7 \(n=2\) instance remains uninhabitable under `PolyGeom`.**

   Offending specs:

   > `geom_denom_dvd : geom.denom ∣ ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a:ℕ))`

   and

   > **U-29a `n2_data`** … RatBurdens data `(q⁻³, 1−q⁻¹, q⁻¹−q⁻³ in PolyGeom form …)`

   In reduced `RatFunc ℚ` form, \(q^{-3}\) has denominator \(X^3\), while \(1-q^{-1}\) and \(q^{-1}-q^{-3}\) also have a positive power of \(X\) in their denominators. No positive power of \(X\) divides a product of \(1-X^a\), whose constant term is \(1\). Thus none of the three required masses can inhabit the stipulated `PolyGeom` presentation. Consequently U-29a, and hence U-29b–e and U-29d5, cannot be jointly constructed.

   The advertised arithmetic itself is correct:
   \[
   q^{-3}+(1-q^{-1})+(q^{-1}-q^{-3})=1,
   \]
   \[
   1-q^{-3}=\frac{q^3-1}{q^3},
   \quad
   \beta_{(1,2)}=\frac{q+1}{q^2+q+1},
   \quad
   \beta_{(1,1)^2}=\frac{q^2}{q^2+q+1},
   \]
   and the two \(\beta\)'s sum to \(1\). The failure is representational, not arithmetic.

2. **CRITICAL — the `(iv)-POLY` hypotheses are weakened by merging two independently bounded polynomials.**

   Offending specs:

   > `structure PolyGeom where count : Polynomial ℚ …`

   > `tg_deg : ∀ e τ o, (tgP e τ o).degBound = T.Wloc e τ o + T.Wstate e τ`

   The note separately requires:

   > “T is one polynomial of degree ≤ W_loc(m) and each cell size one polynomial of degree ≤ W_state(s)”

   A single arbitrary polynomial of degree at most `Wloc + Wstate` need not factor into those two polynomials and does not establish either individual bound. The proposed hypothesis is strictly weaker than the displayed `(iv)-POLY` burden. `j_deg` has the same issue insofar as it claims conformance to the same per-cell `(iv)-POLY` pattern.

3. **CRITICAL — XRB is assumed as a field and its purported discharge is circular.**

   Offending specs:

   > `xrb : ∀ e he h h' τ σ', βmeas e he h τ σ' = βmeas e he h' τ σ'`

   > `def W2_xrb (B : RS1Bundle …) : Prop := ∀ e he h h' τ σ', B.βmeas … = B.βmeas …`

   `W2_xrb` is definitionally the already-assumed `B.xrb` field. It therefore proves none of S.1’s displayed derivation and can be discharged by projection. The required hypotheses—XHD-u, JC-INV, SIB/JC-multi, TB-CAP/VP, REL.2(a)/(b)/(d), and `(ns-null)`—do not occur in its hypothesis fields. This smuggles the note’s derived XRB theorem into an assumption.

4. **CRITICAL — RS.1-DEEP is likewise installed as its own hypothesis instead of derived from the displayed package.**

   Offending specs:

   > `recursion_meas : … βmeas … = evalRe …`

   > `def W3_recursion (B : RS1Bundle …) : Prop := … B.βmeas … = evalRe …`

   Again, the pinned discharge target merely repeats a structure field. TREE-EXP fin/ns, TREE-N, ONE-F, SIB, TB-CAP/VP, PCI, and REL.2 are represented only by provenance comments, not by hypothesis fields. The structure can therefore assume the measured recursion directly without supplying the note’s attached open kernels.

5. **CRITICAL — the derived shallow-cut theorem `(CUT-WD)` has no faithful unit.**

   Offending substitute:

   > `def W7_shapeFam (F : ShapeFam T) (TI : TreeIface T) : Prop := ∀ t : TI.Tree, TI.shapeOf t ∈ F.Sh`

   This states only that `shapeOf` lands in a finite menu. It says nothing about first-entrance uniqueness, exhaustive/nonoverlapping assignment of nodes, the `(BDY)` edge/node convention, shallow τ-halts, or the prohibition on reclassifying deep splits. Those are the content of `(CUT-WD)`, which the note derives. Assuming `rsh_interp` does not formalize that display.

6. **CRITICAL — `W17ii` remains vacuously satisfiable and does not tether \(W_{\widehat S}\) to the named production machinery.**

   Offending spec:

   > `HasSum (fun h : M.ιDom' Ŝ => shWeight Ŝ h q₀) (C.WshVal Ŝ q₀)`

   `ιDom'` and `shWeight` are unconstrained carriers that may be chosen specifically to sum to any desired `WshVal`. No field connects them to C.1.5 node volumes, CTS/[1] counts, XHD-s, shallow cells, or SIB’s COUNT face. Likewise, `shEvt` is not tied to `shapeOf` or shallow-tree fibers. Thus the displayed CL-17(ii) open kernel can be satisfied by an artificial singleton weight/event.

7. **GAP — `W17ii` is not a plausible elaborating Lean specification as written.**

   Offending text:

   > `(ιDom'/shWeight: … added to MeasuredSide at phase E …)`

   Neither `MeasuredSide.ιDom'` nor `shWeight` is declared in the Defs skeleton, and `W17ii` appears outside the preceding Lean code block. Its dependency and typing are deferred rather than specified.

8. **GAP — U-24b lacks a complete Lean statement.**

   Offending unit:

   > **U-24b `rs2_unique_interp`** … “any family f that is OK on S and interpolates βmeas there equals `blockSolve …`”

   The actual binders, family type, coordinate quantifiers, OK predicates, interpolation equation, and equality conclusion are not supplied. The prose is insufficient to audit quantifier order or verify that `ReadOffBundle` covers exactly the family used in the conclusion.

9. **GAP — U-29a is still a hidden multi-unit construction.**

   Offending unit:

   > **U-29a `n2_data`** … “the three-outcome TableShape … MeasuredSide … RatBurdens … SCSData/ShapeFam data.”

   This single unit defines at least five substantial structures, a finite event model, rational presentations, pools, representatives, heights, entrance data, and shape data. It cannot reasonably be a short one-display unit, and its sketch omits the block-\(1\) and entrance/shallow components required to inhabit the total structures.

10. **GAP — U-29d5’s claimed source of packages does not cover its stated set without an additional construction.**

   Offending unit:

   > `S := the all-active pools of the instance`

   > deps: `U-29c, U-29d2, U-24a2`

   U-29c constructs only the \(q_0=2\) package. U-29d2 supplies `RegP` at effective deltas in `consumedDeltas`, described here as only \(\{1\}\), whereas `allActivePools` contains every prime-power pool. U-29d5 therefore needs a fresh uniform `PoolHyp` construction at every prime power; that obligation is absent from its statement/sketch.

Counts: **6 CRITICAL / 4 GAP**

**REJECT (6 crit / 4 gap)**
tokens used
63,790
1. **CRITICAL — the REV-7 \(n=2\) instance remains uninhabitable under `PolyGeom`.**

   Offending specs:

   > `geom_denom_dvd : geom.denom ∣ ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a:ℕ))`

   and

   > **U-29a `n2_data`** … RatBurdens data `(q⁻³, 1−q⁻¹, q⁻¹−q⁻³ in PolyGeom form …)`

   In reduced `RatFunc ℚ` form, \(q^{-3}\) has denominator \(X^3\), while \(1-q^{-1}\) and \(q^{-1}-q^{-3}\) also have a positive power of \(X\) in their denominators. No positive power of \(X\) divides a product of \(1-X^a\), whose constant term is \(1\). Thus none of the three required masses can inhabit the stipulated `PolyGeom` presentation. Consequently U-29a, and hence U-29b–e and U-29d5, cannot be jointly constructed.

   The advertised arithmetic itself is correct:
   \[
   q^{-3}+(1-q^{-1})+(q^{-1}-q^{-3})=1,
   \]
   \[
   1-q^{-3}=\frac{q^3-1}{q^3},
   \quad
   \beta_{(1,2)}=\frac{q+1}{q^2+q+1},
   \quad
   \beta_{(1,1)^2}=\frac{q^2}{q^2+q+1},
   \]
   and the two \(\beta\)'s sum to \(1\). The failure is representational, not arithmetic.

2. **CRITICAL — the `(iv)-POLY` hypotheses are weakened by merging two independently bounded polynomials.**

   Offending specs:

   > `structure PolyGeom where count : Polynomial ℚ …`

   > `tg_deg : ∀ e τ o, (tgP e τ o).degBound = T.Wloc e τ o + T.Wstate e τ`

   The note separately requires:

   > “T is one polynomial of degree ≤ W_loc(m) and each cell size one polynomial of degree ≤ W_state(s)”

   A single arbitrary polynomial of degree at most `Wloc + Wstate` need not factor into those two polynomials and does not establish either individual bound. The proposed hypothesis is strictly weaker than the displayed `(iv)-POLY` burden. `j_deg` has the same issue insofar as it claims conformance to the same per-cell `(iv)-POLY` pattern.

3. **CRITICAL — XRB is assumed as a field and its purported discharge is circular.**

   Offending specs:

   > `xrb : ∀ e he h h' τ σ', βmeas e he h τ σ' = βmeas e he h' τ σ'`

   > `def W2_xrb (B : RS1Bundle …) : Prop := ∀ e he h h' τ σ', B.βmeas … = B.βmeas …`

   `W2_xrb` is definitionally the already-assumed `B.xrb` field. It therefore proves none of S.1’s displayed derivation and can be discharged by projection. The required hypotheses—XHD-u, JC-INV, SIB/JC-multi, TB-CAP/VP, REL.2(a)/(b)/(d), and `(ns-null)`—do not occur in its hypothesis fields. This smuggles the note’s derived XRB theorem into an assumption.

4. **CRITICAL — RS.1-DEEP is likewise installed as its own hypothesis instead of derived from the displayed package.**

   Offending specs:

   > `recursion_meas : … βmeas … = evalRe …`

   > `def W3_recursion (B : RS1Bundle …) : Prop := … B.βmeas … = evalRe …`

   Again, the pinned discharge target merely repeats a structure field. TREE-EXP fin/ns, TREE-N, ONE-F, SIB, TB-CAP/VP, PCI, and REL.2 are represented only by provenance comments, not by hypothesis fields. The structure can therefore assume the measured recursion directly without supplying the note’s attached open kernels.

5. **CRITICAL — the derived shallow-cut theorem `(CUT-WD)` has no faithful unit.**

   Offending substitute:

   > `def W7_shapeFam (F : ShapeFam T) (TI : TreeIface T) : Prop := ∀ t : TI.Tree, TI.shapeOf t ∈ F.Sh`

   This states only that `shapeOf` lands in a finite menu. It says nothing about first-entrance uniqueness, exhaustive/nonoverlapping assignment of nodes, the `(BDY)` edge/node convention, shallow τ-halts, or the prohibition on reclassifying deep splits. Those are the content of `(CUT-WD)`, which the note derives. Assuming `rsh_interp` does not formalize that display.

6. **CRITICAL — `W17ii` remains vacuously satisfiable and does not tether \(W_{\widehat S}\) to the named production machinery.**

   Offending spec:

   > `HasSum (fun h : M.ιDom' Ŝ => shWeight Ŝ h q₀) (C.WshVal Ŝ q₀)`

   `ιDom'` and `shWeight` are unconstrained carriers that may be chosen specifically to sum to any desired `WshVal`. No field connects them to C.1.5 node volumes, CTS/[1] counts, XHD-s, shallow cells, or SIB’s COUNT face. Likewise, `shEvt` is not tied to `shapeOf` or shallow-tree fibers. Thus the displayed CL-17(ii) open kernel can be satisfied by an artificial singleton weight/event.

7. **GAP — `W17ii` is not a plausible elaborating Lean specification as written.**

   Offending text:

   > `(ιDom'/shWeight: … added to MeasuredSide at phase E …)`

   Neither `MeasuredSide.ιDom'` nor `shWeight` is declared in the Defs skeleton, and `W17ii` appears outside the preceding Lean code block. Its dependency and typing are deferred rather than specified.

8. **GAP — U-24b lacks a complete Lean statement.**

   Offending unit:

   > **U-24b `rs2_unique_interp`** … “any family f that is OK on S and interpolates βmeas there equals `blockSolve …`”

   The actual binders, family type, coordinate quantifiers, OK predicates, interpolation equation, and equality conclusion are not supplied. The prose is insufficient to audit quantifier order or verify that `ReadOffBundle` covers exactly the family used in the conclusion.

9. **GAP — U-29a is still a hidden multi-unit construction.**

   Offending unit:

   > **U-29a `n2_data`** … “the three-outcome TableShape … MeasuredSide … RatBurdens … SCSData/ShapeFam data.”

   This single unit defines at least five substantial structures, a finite event model, rational presentations, pools, representatives, heights, entrance data, and shape data. It cannot reasonably be a short one-display unit, and its sketch omits the block-\(1\) and entrance/shallow components required to inhabit the total structures.

10. **GAP — U-29d5’s claimed source of packages does not cover its stated set without an additional construction.**

   Offending unit:

   > `S := the all-active pools of the instance`

   > deps: `U-29c, U-29d2, U-24a2`

   U-29c constructs only the \(q_0=2\) package. U-29d2 supplies `RegP` at effective deltas in `consumedDeltas`, described here as only \(\{1\}\), whereas `allActivePools` contains every prime-power pool. U-29d5 therefore needs a fresh uniform `PoolHyp` construction at every prime power; that obligation is absent from its statement/sketch.

Counts: **6 CRITICAL / 4 GAP**

**REJECT (6 crit / 4 gap)**
