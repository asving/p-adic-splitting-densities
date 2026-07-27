# MovesS blueprint audit (Codex) — 2026-07-28

Date run: 2026-07-27. Prompt = CAMPAIGN_AUDIT_CHARGE_2026-07-28.md (charge body, <CORPUS>→MovesS, <NOTE>→§S-RESUM) + MOVES_2026-07-24.md lines 11557–12577 (frozen §S-RESUM note, rev 6) + MOVESS_LEAN_BLUEPRINT_2026-07-28.md (full, 707 lines).

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa3c3-bd35-7831-a4a1-d1fa1da00217
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

THE FROZEN NOTE (ground truth — rev 6, repairs in place):

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

## §H-DOMAINS PASS RECORD (pass 3: 1 crit, 1 gap) and the rev-4 repairs

Pass 3 (`HDOM_PASS3_2026-07-27.md`): repairs 2 GENUINE / 1 PARTIAL /
0 NOT FIXED; 1 critical + 1 gap; NOT ACCEPTED. Rev 4, in place:
- CRIT (H-LIST only PARTIALLY fixed: (TRI) as stated admitted systems
  where the ambient floor h ∈ ℕ dominates the affine bound — least
  value max(0, x−2) on y ≥ x−2, not affine — and negative slopes
  whose periods leave ℕ^D, y ≥ 1−x) — repaired TWO ways: (a) the
  DOMINATION SPLIT, new step (0): per coordinate in triangular order,
  split by the half-space φ_j + 1 ≥ f_j; nonneg slopes make the
  floor-dominated side finite in the cited coordinates (enumerate/
  fix) and the φ-dominated complement a slab decomposition adding
  only CONSTANT bounds; recursion strictly down the triangular order,
  terminating; on each terminal piece ONE bound dominates everywhere
  and steps (1)-(4) run verbatim (floor case: constant, affine
  trivially); (b) class (TRI) RESTRICTED to nonneg slopes, ambient
  floors made explicit clause (c) — campaign-justified: (I-aug) is
  the only cross-coordinate bound of an adjacent-only census and its
  coefficients are POSITIVE (H.2.1); negative slopes join H-LIST-GEN
  (iii). Both pass-3 instances displayed with split cells + affine
  least-value maps ((E1) in-class 3 pieces; (E2) fenced, split still
  resolves it — the genuine obstruction is mixed-sign multi-
  coordinate bounds). GATE FAMILY: split TRIVIAL (φ + 1 = 2h₀ + 1 ≥
  3 > 1 = f₁), same two components, every sealed number stands.
- GAP (stale label) — H.5.2's column header now reads THIS NOTE, REV 4.
STATUS: rev 4 awaits pass 4. No new kernels; H-LIST-GEN widened by (iii).

## §H-DOMAINS PASS RECORD (pass 4: 1 crit, 0 gaps) and the rev-5 repair

Pass 4 (`HDOM_PASS4_2026-07-27.md`): pass-3 repair judged PARTIAL (the
nonneg-slope fence and domination strategy genuine, but not the stated
rational-slope class); 1 critical, 0 gaps; NOT ACCEPTED. Rev 5, in place:
- CRIT (the split's complement "φ_j ≤ f_j − 2" assumes φ_j INTEGER-
  VALUED; class (TRI) allows rational slopes — verifier's y ≥ x/2 − 1/2
  (φ = x/2 − 3/2, f = 0): affine side x ≥ 1, asserted floor side
  x ≤ −1 EMPTY, so x = 0 in NEITHER piece) — repaired by the CEILING-
  AWARE REORDER: H.2.2 now runs REFINE → SPLIT → CONSTRUCT. Strides/
  cells first (steps (1)–(2); order-sound: strides read only moduli +
  slopes); per refined cell ⌈φ_j⌉ is affine with INTEGER values (new
  step (3)), and the split compares INTEGERS — ⌈φ_j⌉ + 1 ≥ f_j vs
  ⌈φ_j⌉ ≤ f_j − 2, the EXACT complement over ℤ (step (4)); rev 4's
  enumeration/slab recursion and the construction (steps (5)–(6)) run
  verbatim per cell. Verified on pass-4's instance ((E3) display: cells
  x mod 2, integerized bounds x/2 and (x−1)/2, y_min = 0,0,1,1,2,2 —
  floor/meet/affine regimes exact); (E1)/(E2) re-checked (integer
  slopes ⟹ reorder vacuous, displays stand); GATE FAMILY: reorder
  VACUOUS (integer slope 2), same two components, every sealed H-n3
  number stands. H.5.2 column header bumped to REV 5.
STATUS: rev 5 awaits pass 5. No new kernels; none closed.

## §X-EXHAUST PASS RECORD (pass 1: 8 crit, 6 gaps) and the rev-2 repairs

*(2026-07-27. Verdict: lean/notes/XEXH_PASS1_2026-07-27.md — NOT ACCEPTED;
all findings repaired IN PLACE in §X-EXHAUST above. Disposition:)*

1 (CRIT, "ZERO" ≠ actual GMN gain) — verdict semantics rewritten: T3/T4
  are NOT-CERT ("no positive per-side bound", never "actual ind_r = 0");
  the semantic d_gen^sem defined and used NOWHERE; raw column = side bounds.
2 (CRIT, ALIGN fallback vs definitions; "T4-only" false) — CERTIFIED DEPTH
  (CD) pinned ONCE in X.0: d_cert = table-positive rows (T1/T2) whose
  ALIGN sub-clause is discharged; d_unc = the rest; used in EVERY display.
  WEIGHT-CHARGE restated over the FULL recentering population.
3 (CRIT, T3 not absorbable) — reduction rewritten with the ADDITIVE
  ⌊log₂ n⌋ term: v_p(disc f) ≥ (d_total − ⌊log₂ n⌋)/(s(n)+1/2); the deep
  leg's coercion updated to match.
4 (GAP, T2 witness) — explicit witness (s+1, u+1) displayed with the three
  strictness checks and the gcd-excluded (2,2) case.
5 (GAP, T0 typing) — T0 retyped: level-0 reduction-cluster OPENING, not a
  §M-SPECIES letter; ROOT-tag LETTERS are reads, classified into T1–T5.
6 (CRIT, false counting inequality) — (X2-HYP) fixed: Σ h_r ≤
  (d_total+1)·max h (the terminal read counted); dichotomy restated with
  d_total + 1; the d_total = 0 counterexample dissolved.
7 (GAP, (X2-AFF) overclaimed) — DEMOTED to a NAMED OPEN display duty of
  PROGRESS: neither c₀(n) nor its existence derived; Thm 2.1 gives only
  per-stratum finiteness.
8 (CRIT, envelope event inclusion unproved) — (X2-BRIDGE) named, displayed
  OPEN: the four-way Undec(N) decomposition, the existential conversion +
  the uniform cap c_cap(n) listed as its duties; envelope now GIVEN
  (X2-BRIDGE) at N′ = N − c_cap; qualitative X.3 never consumes it.
9, 10 (CORRECT) — kept; formulas re-based on the rev-2 reduction/counting.
11 (CRIT, X.3 disjunction wrong) — tag rewritten at every site:
  (X1a-ALIGN) ∨ ((ALIGN-inc) ∧ X.1b); "X.1b alone" struck (it bounds no
  increments); X.1b's consumer line now cites the conjunction.
12 (GAP, branch-finite vs tree-finite) — König bridge displayed in X.3(a):
  finite child menus ⟹ finitely branching; König upgrades to tree-finite.
13 (GAP, VP vs VP-SOUND) — X.3's perimeter + X.4 now cite VP-SOUND =
  (HEN-LIFT)/(OM-SAT), §T-ASSEMBLY's retained citation obligations.
14, 15, 17 (CORRECT) — kept (elementary tail; (NS-ROUTE) typing, now
  bridged through 8's repair; STALL-probe scope); probe vocabulary renamed
  to recentering runs and pointed at the sealed s(3).
16 (CRIT, gate not sealed) — X.5 REBUILT: censused quantity = the
  prefix-cumulative sweep v_p(disc f) ≥ 2·CUM(j), per-node table values
  displayed; sealed NUMBERS s(3) = 2, c₀(3) = 4, c_d = c_h = 1/2 (offsets
  1), C_T = 53, c_T = 1, each with a derivation line and Case-K status;
  (3b) legs numeric; assembled env*(N) computed and declared TOOTHLESS at
  N ≤ 8 (shape only) — falsifiability carried by the sweep, the s(3)
  ratio, the per-letter tails, and the (3b) legs.

Rev 2: kernels OPEN (X1a-ALIGN), WEIGHT-CHARGE (full recentering burden),
PROGRESS (owning (X2-AFF), (X2-BRIDGE)); gate sealed; awaits pass 2.

## §H-DOMAINS: ACCEPTED AT THE CODEX BAR (2026-07-27, passes 5 + 6 consecutive CLEAN on identical rev-5 text)

Spiral: pass 1 (9c/2g) → the species-correct inventory + the positivity split + the
(TRI) narrowing → pass 2 (1c/2g) → the refined strides → pass 3 (1c/1g) → the
domination split → pass 4 (1c/0g) → REFINE → INTEGERIZE → SPLIT → CONSTRUCT (the
rational leak closed) → passes 5+6 CLEAN (`HDOM_PASS5/6_2026-07-27.md`). What is
DERIVED: XHD-w (with AUD-E's additive exclusion), H-LIST on the nonneg-slope (TRI)
class via the four-stage construction, XHD-s conditional on its displayed inputs,
(u-R)'s mass face, (ENT-U) GIVEN M4b-T. FENCED (the [1v]-FULL blockers): XHD-d-EX(∂),
U-R-COUNT, XHD-u-X (first-tested by the re-attributed L4 leg), M4b-T-AUD, H-LIST-GEN,
E-POS. The demand/delivery table states plainly that [1v]-FULL cannot be recorded yet.
REMAINING: the H-n3 census (the seal is real, unrun), the Fable dual half (launched),
and the fences.

## §X-EXHAUST PASS RECORD (pass 2: 2 crit, 0 gaps) and the rev-3 repairs

*(2026-07-27. Verdict: lean/notes/XEXH_PASS2_2026-07-27.md — NOT ACCEPTED;
all 14 pass-1 repairs adjudicated GENUINE/CORRECT (finding 8 PARTIAL,
finding 11 with a residual defect — the two criticals below); TOOTHLESS
gate declaration judged honest and the gate meaningful at layers
(i)/(ii). Both criticals repaired IN PLACE in §X-EXHAUST above:)*

CRIT 1 ((X2-BRIDGE) uniform cap vs TB-CAP) — the rev-2 duty
  "cap(H) ≤ c_cap(n)" CONTRADICTED the TB-CAP record ("No cap uniform
  over ALL cells of a verdict value exists or is claimed — heights grow
  along deeper shapes") and is STRUCK. Rev 3: cap(H) := the max TB-CAP
  cap of H's OWN leaf-detection cells (H-dependent, level-indexed — what
  TB-CAP actually supplies); bridge statement now level-relative
  (threshold(H) + cap(H) > N); the four-way decomposition and the
  existential conversion KEPT (pass 2: well-posed); the quantitative
  conversion routed through the NEW open kernel (X2-CAP):
  cap(H) ≤ c_cap(n)·(1 + Σ h_r) — contradiction-free (rate, not level).
  (X.2)'s hypothesis and (X2-HYP)'s chain rebased (c₀⁺ := c₀ + c_cap);
  the N′ = N − c_cap shift struck; all tag lists + X.4 carry (X2-CAP);
  X.5's sealed √N numbers kept as the c_cap = 0 face, observation only.
CRIT 2 (X.3(a1) ALIGN-only termination) — STRUCK: (X1a-ALIGN) bounds
  only the certified T1/T2 accounting and supplies NO bound on T4
  recenterings (WEIGHT-CHARGE's population). Rev 3 tag:
  [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)] — the
  four-population decomposition displayed in (a1); X.1b's T4 leg is
  consumed by EVERY route (X.1b consumer line + X.4 map updated).

Rev 3: kernels OPEN (X1a-ALIGN), WEIGHT-CHARGE + s(n), PROGRESS (owning
(X2-AFF), (X2-BRIDGE), (X2-CAP)); gate unchanged; awaits pass 3.


THE BLUEPRINT UNDER AUDIT:

# MOVES §S-RESUM — Lean formalization blueprint (corpus MovesS, 2026-07-28)

*Blueprint-architect deliverable for the campaign (`LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`,
wave 1). Source of truth: the DUAL-ACCEPTED **§S-RESUM rev 6** of `lean/notes/MOVES_2026-07-24.md`
(lines ~11557–12430; acceptance record "§S-RESUM: DUAL-ACCEPTED (2026-07-27 — Codex pass 7 + the
Fable confirm, both CLEAN on identical rev-6 text)"). Written Protocol-L (agent-facing): verbatim
names, statements re-bound at use, explicit claim DAG. Discipline (parent CLAUDE.md): NO new
axioms; statement-fence holds; every interface structure is a trust boundary flagged for the
semantic audit (§4).*

## H. HEADER — the hypothesis-structure design (read first)

§S-RESUM CONSUMES the wave-4 corpora MovesV (§V-TABLES: the CTS cell space, the count tables
T/G, ι_e, the (iv) ledger) and MovesT (§T-ASSEMBLY: TREE-EXP, TREE-N, ONE-F, (SIB), VP, TB-CAP).
Those corpora do not exist yet. **Design ruling: every consumed MovesV/MovesT object enters
MovesS as a HYPOTHESIS STRUCTURE** — a section-variable bundle with named Prop/data fields —
so MovesS is self-contained NOW and instantiable at wave 4 by substituting the real objects:

- **`TableFamily`** — the table family T over ℚ(q): block states, the per-state outcome roster
  with individuated members ([3t] SIBLING INDEXING), the resummed masses T·G ∈ ℚ(q) ((iv)'s
  licit product), the cell-level branching masses J_{τ,o} ∈ ℚ(q) ((J-RAT)'s object), the
  entrance vectors ι_e (CTS-M(iii)/ENT-AGG/INIT-RAT). Owner: MovesV.
- **`LedgerIV`** — the NINE-input CL-5 conditionality ledger + PART-1's routed partition
  identity, as named Prop fields (opaque at wave 2). Owners: [1v]/[2b].
- **`RS1Bundle` / `RS4TagChain`** — the tree-assembly interface: the measured fixpoint
  (R_e-lump), the shallow expansion per (CUT-WD), the marked pairing, X.3's primewise total.
  Owners: MovesT/[5]/[2r]. Discharged at wave 4; NEVER proved here.

**XRB is baked in BY TYPE** (honesty flag, audit §4): the unknowns β_{e,τ}(σ′) are modeled with
NO h_ent index — exactly the S.0 typing ("HEIGHT-FREE (no h_ent index — exactly XRB, proved at
S.1)"). S.1's proof ((β-1)/(β-2)) is measure-side mathematics over [2b]/[3t] objects and is NOT
a MovesS unit; its conclusion is the model's type discipline, and its hypothesis set rides the
`RS1Bundle` fields. The same for S.2's (CUT-WD) and the S.7 gate (census-side, not Lean).

What IS proved in MovesS (the note's own DERIVED layer): the (m,c) dispatch and its routing
lemma; (K-TRI); the (SCS) derivation chain; (K-SUB)'s regrouping; the block-indexed linear
system over ℚ(q) and its adjugate/Cramer solve (RS.2's engine); the E0 ⟹ det ≠ 0 and Neumann
consequences (E0 itself a named hypothesis — the note's OPEN KERNEL CL-1); the evaluation
machinery and the infinitely-many-evaluations lemma; RS.1's assembly and RS.4's checksum as
CONDITIONAL theorems over the bundles.

---

## 0. What §S-RESUM is (one paragraph)

The depth direction of the classifier tree, resummed: per block size e ≤ n, the linear system
> (R_e-lump)  β_e = K_e β_e + b_e^{term,fin} + b_e^split
over ℚ(q), unknowns the entrance-free conditional subtree values β_{e,τ}(σ′); the (m,c)
CLASSIFICATION routes every roster outcome to exactly one of {K_e column, terminal exit,
split exit}; (K-TRI) makes the block family triangular in e (b_e^split consumes strictly
smaller blocks only), (K-SUB) makes K_e's rows sub-stochastic given the (iv) ledger; the solve
is β_e = adj(I−K_e)b_e/det(I−K_e) (RS.2, fixed coefficients in ℚ(q)); solvability rides the
open kernel ESCAPE(E0) per pool q₀ = p^δ (RS.3); RS.1 ties the solve to the density components
R_σ in three clauses (DEEP/SH/MARKED); RS.4 is the checksum Σ_σ R_σ = 1, via "a rational
function equal to 1 at infinitely many prime evaluations is identically 1".

---

## 1. Design decisions (the concrete Mathlib model), with justification

**D1 — ℚ(q) := `RatFunc ℚ`** (`abbrev Qq := RatFunc ℚ`). Field structure: `RatFunc.instField`
(pinned mathlib, `Mathlib/FieldTheory/RatFunc/Basic.lean:480`). So `Matrix τ τ Qq` lives over a
field and the whole `Matrix.det` / `Matrix.adjugate` / nonsingular-inverse API applies verbatim.

**D2 — the block system is ONE matrix per (e), ONE vector per (e, σ′).** K_e's entries do not
depend on σ′ (S.0: K_e is state-to-state; σ′ rides only the exit vectors), so the unknown for
fixed σ′ is `β : State e → Qq` and the system is `β = K.mulVec β + b σ′`. This puts the solve
directly on Mathlib's `Matrix.mulVec` / `Matrix.cramer` API with zero re-plumbing.

**D3 — the solve API (all names verified in the pinned mathlib).**
`Matrix.isUnit_iff_isUnit_det` (NonsingularInverse.lean:127) converts `det(1−K) ≠ 0` (a field,
so `IsUnit ↔ ≠ 0` via `isUnit_iff_ne_zero`) to invertibility; `Matrix.mul_nonsing_inv` (:211) /
`Matrix.nonsing_inv_mul` (:217) give the two-sided inverse; `Matrix.inv_def` (:172) is
`A⁻¹ = A.det⁻¹ʳ • A.adjugate`; `Matrix.cramer_eq_adjugate_mulVec` (Adjugate.lean:245),
`Matrix.mul_adjugate` (:264), `Matrix.adjugate_mul` (:269), and
`Matrix.det_smul_inv_mulVec_eq_cramer` (NonsingularInverse.lean:656) give RS.2's displayed
entrywise form `β = adj(I−K_e) b_e / det(I−K_e)` with no bespoke linear algebra.

**D4 — evaluation at a pool q₀ is PARTIAL, exactly as the note demands.** `RatFunc.eval`
(AsPolynomial.lean:146) is `eval₂ f a num / eval₂ f a denom` and is additive/multiplicative
ONLY where denominators do not vanish (`RatFunc.eval_add`/`eval_mul` carry those hypotheses) —
which is precisely S.4's per-pool discipline ("symbolic det ≠ 0 prevents no zero or uncancelled
pole at an individual q₀ = p^δ"). We package the good locus as the subring `OKat q₀` (denom
nonvanishing at q₀) with a genuine `RingHom` `evalAt q₀ : OKat q₀ →+* ℚ`; matrix determinants
then commute with evaluation via `RingHom.mapMatrix`/`Matrix.det` naturality (`RingHom.map_det`).

**D5 — the infinitude arguments run through `Polynomial.eq_zero_of_infinite_isRoot`**
(Roots.lean:145): a RatFunc vanishing at infinitely many OK points has a numerator with
infinitely many roots, hence is 0. One reusable unit (`ratfunc_eval_infinite`) serves BOTH
RS.3(ii)'s symbolic det ≠ 0 (contrapositive, one witness pool suffices) and RS.4's checksum.

**D6 — base change q ↦ q^δ is a ring hom `powSubst δ : Qq →+* Qq`**, built by
`IsFractionRing.lift` over `Polynomial.aeval (X^δ : ℚ[X])` (nonzero polynomials map to nonzero,
hence to units of the fraction field). [2r]'s BASE-INDEX CONVENTION (δ ABSOLUTE) is a docstring
duty on the field `Member.δ`, not re-derived.

**D7 — verdict-type multisets are literal `Multiset VType`**, with [2a]'s finiteness entering
as a Finset field `SigSet` (the σ′ actually occurring) — never a global Fintype on multisets.
The split convolution's decomposition index `{g : Fin m → Multiset V // ∑ j, g j = σ′}` gets a
constructed `Fintype` instance (unit `decompFintype`); the τ-halted members contribute factor 1
with σ_j their verdict singleton, per §T.4's leaf convention cited at S.0's b_e^split display.

**D8 — the μ̂-type fence is a TYPE.** The marked total ι_e^T(I−K_e)^{−1}b_e is wrapped in a
one-field structure `MuHat` so it CANNOT be summed into a density silently — the note's
RS.1-MARKED fence ("NEVER summed into R_σ"; "equating any μ̂ object with an f-event mass
outside [3t]'s displayed conversion is a TYPE ERROR") enforced by the elaborator.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesS/Defs.lean` (inline, part 1: states/outcomes/dispatch)

Section binder throughout: `variable {n : ℕ}` (the degree; block sizes e ∈ 1..n ride as plain
`ℕ` arguments with hypotheses where needed — states of out-of-range e are empty at wave 4).

```lean
import Mathlib

namespace LeanUrat.MovesS
open Matrix Polynomial

/-- ℚ(q). Field: `RatFunc.instField`. The variable is the note's q. -/
abbrev Qq := RatFunc ℚ

/-- One INDIVIDUATED member of an outcome ([3t] SIBLING INDEXING — member-indexed,
    no order, no symmetry factor). `δ` is the ABSOLUTE base-change index ([2r] (e2)).
    `status`: halted with a verdict type, or continuing into a block-`size` state. -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ
  status : V ⊕ State size

def Member.continuing {V State} (μ : Member V State) : Prop := μ.status.isRight = true

/-- An outcome o at a block-e state: its member list. m := total members, c := continuing. -/
structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ := (o.mem.filter (·.status.isRight)).length

/-- The (m, c) CLASSIFICATION's three routes (S.0, rev 6 — a DISPLAYED DEFINITION the
    note ADOPTS; the roster supplies the two axes, never the routing itself). -/
inductive Route | kcol | termFin | split
  deriving DecidableEq

/-- The dispatch: (c = 0, any m) → termFin; (c = 1, m = 1) → kcol; (c ≥ 1, m ≥ 2) → split. -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

/-- The verdict multiset v(o) of an ALL-HALTED outcome's members (σ′ = v(o), the FULL
    multiset — multi-member values licit: m_H3 (1,1)³, m_H12 "[1,1]+[1,2]"). -/
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  (o.mem.filterMap (fun μ => μ.status.getLeft?) : List V)

/-- HYPOTHESIS STRUCTURE (owner MovesV = §V-TABLES; wave-4 discharge): the table family
    T over ℚ(q) — block states, per-state outcome rosters, resummed masses. -/
structure TableFamily (n : ℕ) where
  State  : ℕ → Type            -- block-e states τ (the [1v] CTS-S cells at cluster size e)
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type                 -- verdict types
  deqV   : DecidableEq VType
  SigSet : Finset (Multiset VType)  -- the σ′ occurring (finite by [2a] M1/M5 — HYPOTHESIS)
  Out    : ∀ e, State e → Type  -- the outcome roster at (e, τ)
  finO   : ∀ e τ, Fintype (Out e τ)
  odata  : ∀ e τ, Out e τ → Outcome VType State
  TG     : ∀ e τ, Out e τ → Qq  -- the one-step resummed mass T·G ((iv): T_{m,o}·G, NO
                                --   source-mass division; licit product per (U-A)+(XHD-u))
  J      : ∀ e τ, Out e τ → Qq  -- the CELL-LEVEL resummed branching mass J_{τ,o}
                                --   ((J-RAT)'s object — NEVER the marked per-branch T·G)
  ι      : ∀ e, State e → Qq    -- CTS-M(iii) ENT-AGG entrance vector (INIT-RAT: cited burden)
  kcolSameSize : ∀ e τ (o : Out e τ), routeOf (odata e τ o) = .kcol →
    ∀ μ ∈ (odata e τ o).mem, μ.size = e
    -- (SCS)'s payload as a FIELD, so `Kmat` typechecks; unit `MovesS.scs` DISCHARGES it
    -- from the deeper SP.1/stage-law fields (SCSData below) — instantiators supply those.

attribute [instance] TableFamily.fin TableFamily.deq TableFamily.deqV TableFamily.finO
```

**The kernel, exit vectors, and the solve target** (Defs part 2 — the (m,c)-routed objects):

```lean
variable {n : ℕ} (T : TableFamily n)

/-- K_e: entries = Σ over (c=1, m=1)-routed outcomes whose continuing member lands in β
    of T·G. Entrance-height-FREE by construction (D8/XRB typing). -/
def Kmat (e : ℕ) : Matrix (T.State e) (T.State e) Qq :=
  fun τ β => ∑ o ∈ {o : T.Out e τ | routeOf (T.odata e τ o) = .kcol ∧
                    kTarget T e τ o = some β}.toFinset, T.TG e τ o
  -- `kTarget` reads the unique continuing member's state, cast along `kcolSameSize`.

/-- b_e^{term,fin}(τ)(σ′): Σ over (c=0)-routed outcomes with v(o) = σ′ of T·G. -/
def bTerm (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq :=
  fun τ => ∑ o ∈ {o | routeOf (T.odata e τ o) = .termFin ∧
                  (T.odata e τ o).verdicts = σ'}.toFinset, T.TG e τ o

/-- b_e^split(τ)(σ′) GIVEN the family of already-solved smaller blocks `βlt`:
    Σ over (c≥1, m≥2)-routed o of J_{τ,o} · Σ_{σ′ = ⊎ σ_j} ∏_j leg(σ_j) — halted members
    factor 1 on σ_j = {verdict} (§T.4 leaf convention, cited); continuing members
    (powSubst μ.δ) (βlt μ.size ⋯ σ_j), sizes < e by (K-TRI). -/
def bSplit (e : ℕ) (βlt : ∀ e' < e, T.State e' → Multiset T.VType → Qq)
    (σ' : Multiset T.VType) : T.State e → Qq := sorry -- skeleton: unit `bSplit_def` elaborates
```

**Defs part 3 — the hypothesis bundles** (each a trust boundary, audit §4):

```lean
/-- DEG-CONS (CL-11, owner [1v]; "per member, from M1's degree identity; the check runs
    over the FULL roster" — halted members INCLUDED): each e_j ≥ 1 and Σ_j e_j ≤ e. -/
structure DegCons (T : TableFamily n) : Prop where
  size_pos : ∀ e τ (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e τ (o : T.Out e τ), ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-- (SCS)'s SUPPLY (owners [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via [2a] SP.2 (B1)/(B3)):
    per (c=1,m=1) outcome, the letter data W, D, ℓ, g, μ, W', D' with the cited laws.
    Fields are the DISPLAYED cites, one each. -/
structure SCSData (T : TableFamily n) where
  W D ℓ g μ W' D' : ∀ e τ (o : T.Out e τ), ℕ           -- per-outcome letter data
  flank_empty : ∀ {e τ o}, (T.odata e τ o).m = 1 → W T e τ o = e * ℓ T e τ o
    -- SP.1: every flank side / non-selected residual factor is a member; m = 1 forces
    -- the read side to span the window (unit `scs_flank` DERIVES this from the finer
    -- member-injection fields if MovesSp lands first; at wave 2 it is the field).
  lam_singleton : ∀ {e τ o}, (T.odata e τ o).m = 1 → g T e τ o * μ T e τ o = ℓ T e τ o
  stage_D : ∀ e τ o, D' T e τ o = e * g T e τ o * D T e τ o    -- (B1): D′ = e·g·D
  stage_W : ∀ e τ o, W' T e τ o = μ T e τ o                     -- (B3): W′ = μ
  cluster_parent : ∀ e τ o, W T e τ o * D T e τ o = e           -- cluster size IS W·D
  cluster_child  : ∀ {e τ o} (h : routeOf (T.odata e τ o) = .kcol),
    ∀ μm ∈ (T.odata e τ o).mem, μm.size = W' T e τ o * D' T e τ o

/-- The NINE-input CL-5 ledger + PART-1's routed partition identity (owners [1v]/[2b];
    items opaque at wave 2 — named so tags are CITABLE, never silently dropped). -/
structure LedgerIV (T : TableFamily n) : Prop where
  xhd : True      -- (1) XHD = M4a-X exact height domains/weights/sums   [placeholder Props:
  d4r0 : True     -- (2) D4R.0 disjointness after height grouping        wave-4 retargeting
  part_meas : True -- (3)(5) (iv)-PART measurability                      replaces each True
  rep : True      -- (4) (iv)-REP = M2(ii); probe STATE-probe-2           by the real
  hmc : True      -- (6) CTS-M(v) HMC (OPEN kernel)                       statement]
  act : True      -- (7) CTS-M(ii) ACT
  init : True     -- (8) CTS-M(iii) INIT + ENT-COUNT
  comp : True     -- (9) (COMP-h)→(COMP-Σ) heights-once typing
  part1 : ∀ e τ, (∑ o : T.Out e τ, oneStepMass T e τ o) = 1
    -- PART-1 in its ROUTED form: oneStepMass := TG on kcol/termFin, J on split —
    -- "the digit-cell partition identity, per representative, countable across heights"

/-- ESCAPE(E0) (OPEN KERNEL, CL-1, owner THIS note; PER-POOL q₀ = p^δ, rev-3 widening):
    the evaluated active matrix escapes. A named HYPOTHESIS, never proved in MovesS. -/
structure EscapeE0 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ))) Filter.atTop (nhds 0)

/-- The per-pool package (S.4): the active-state set at q₀, entry evaluability into it,
    vanishing into inactive cells, the recorded junk determinants, active-value agreement
    (CTS-M(ii-c), weakened REV-7 form) — all FIELDS. (REG-p) for MovesU := this bundle
    at every relevant pool q₀ = p^δ of the prime p. -/
structure PoolHyp (T : TableFamily n) (e : ℕ) (q₀ : ℚ) where
  Act : Finset (T.State e)                          -- sealed active list
  evalOK : ∀ τ β, τ ∈ Act → β ∈ Act → (Kmat T e τ β).denom.eval q₀ ≠ 0
  A : Matrix Act Act ℚ                              -- the evaluated active submatrix
  A_eval : ∀ τ β, A τ β = RatFunc.eval (RingHom.id ℚ) q₀ (Kmat T e τ.1 β.1)
  inactive_vanish : ∀ τ β, τ ∈ Act → β ∉ Act →
    RatFunc.eval (RingHom.id ℚ) q₀ (Kmat T e τ β) = 0
  e0 : EscapeE0 A                                   -- the open kernel rides HERE
  active_value_agreement : True                     -- (ii-c) per pool; wave-4 statement

def RegP (T : TableFamily n) (p : ℕ) (Δ : Finset ℕ) : Prop :=
  ∀ e ≤ n, ∀ δ ∈ Δ, Nonempty (PoolHyp T e ((p : ℚ) ^ δ))

/-- μ̂-TYPE FENCE (D8): the marked-entrance total, wrapped so it can never be summed
    into a density. RS.1-MARKED's object; consumed by (COMP-AGG)/gates ONLY. -/
structure MuHat where val : Qq

/-- (BDY) BOUNDARY CONVENTION (S.0, pinned ONCE, EDGE-BASED): reads of an entered path
    split as `entrance` (up to AND INCLUDING the entering read) vs `block` (from the
    first in-block read). Abstract model: a path with a first-entrance edge index. -/
inductive ReadOwner | entrance | block
def bdyOwner (firstEntrance : ℕ) (readIdx : ℕ) : ReadOwner :=
  if readIdx ≤ firstEntrance then .entrance else .block
```

**Defs part 4 — the RS.1/RS.4 tree-assembly interfaces** (owners MovesT/[5]/[2r]; wave 4):

```lean
/-- RS.1's hypothesis bundle (S.2's displayed GIVEN-list, one field per named input).
    `SplitTy`/`Shape` abstract the σ and Ŝ index types; finiteness = [2a] fields. -/
structure RS1Bundle (T : TableFamily n) where
  SplitTy : Type; finS : Fintype SplitTy            -- splitting types σ
  Shape : Type;  finSh : Fintype Shape              -- shallow tree shapes Ŝ (CUT-3's image)
  R : SplitTy → Qq                                  -- the density components (the TARGET)
  Wsh : Shape → Qq                                  -- W_Ŝ (CL-17(ii): production OPEN, cited)
  shapeData : Shape → List (Σ e, T.State e) × Multiset T.VType × List ℕ
       -- (block entrances (e_i, τ_i); σ₀(Ŝ); the δ_i legs)
  -- named [3t]/[2r]/CL tags (opaque at wave 2, citable):
  treeExp : True   -- [3t] TREE-EXP fin/ns + TREE-N + ONE-F
  sib : True       -- (SIB)/(SIB-STEP) + (JC-multi), CL-10 OPEN
  tbcapVp : True   -- TB-CAP / VP per their [3t] statuses
  rel2 : True      -- [2r] REL.2 (a)–(e) at every base-changed leg, CL-8 OPEN
  xrbSet : True    -- XRB's displayed hypothesis set (XHD + (JC-INV) + …), CL-9
  nineInputs : LedgerIV T                           -- CL-5 rides RS.1 wholesale
  -- the MEASURED clauses, as the wave-4-dischargeable interface fields:
  recursion : ∀ e ≤ n, ∀ σ' ∈ T.SigSet, ∀ hβ,      -- (R_e-lump): the solve family is
    βfam e σ' = (Kmat T e) *ᵥ βfam e σ' + bTerm T e σ' + bSplit T e hβ σ'
  shallow_expansion : ∀ σ,                          -- (CUT-WD)-regrouped tree expansion:
    R σ = ∑ Ŝ, Wsh Ŝ * shConv T Ŝ σ                 -- shConv := the S.2 convolution DEF
  marked_pairing : ∀ e ≤ n,                         -- RS.1-MARKED's supply
    markedTotal e = MuHat.mk (T.ι e ⬝ᵥ solveVec T e)

/-- RS.4's FULL tag chain (S.5: "RS.4 inherits EVERY condition of the block solve"),
    a hypothesis STRUCTURE — the checksum theorem consumes it whole. -/
structure RS4TagChain (T : TableFamily n) where
  bundle : RS1Bundle T                              -- RS.1's set + CL-5 (via nineInputs)
  e0 : ∀ e ≤ n, ∀ q₀ ∈ relevantPools, Nonempty (PoolHyp T e q₀)   -- ESCAPE(E0), CL-1
  x3 : True                                         -- X.3 (CL-4, [5]) — total-mass identity
  ivPoly : True                                     -- CTS-M(iv)-POLY (CL-6)
  xhdS : True                                       -- XHD-s
  initRat : True                                    -- INIT-RAT ([1v] burden)
  wshRat : True                                     -- CL-17(ii)'s rational W_Ŝ
  jRat : True                                       -- (J-RAT) ([1v]/[2b], rev 2)
  primewise : { S : Set ℚ // S.Infinite ∧ ∀ q₀ ∈ S,
    (∑ σ, bundle.R σ).denom.eval q₀ ≠ 0 ∧
    RatFunc.eval (RingHom.id ℚ) q₀ (∑ σ, bundle.R σ) = 1 }
    -- X.3's primewise decided-mass total = 1, evaluated: the wave-4 discharge point
```

*(Skeleton licenses: `kTarget`, `oneStepMass`, `shConv`, `solveVec`, `markedTotal`,
`relevantPools`, `βfam` are Defs-level definitions elaborated by their owning units below;
`True` placeholders are RETARGETED at wave 4 — each is a named field so no consumer can
compile without citing it, the tag-chain discipline in Lean form.)*

---

## 3. The unit DAG — 4 layers, 28 units (10 easy / 15 medium / 3 hard)

Format per campaign §2. Each unit = one file `lean/LeanUrat/MovesS/<Id>.lean` importing
`MovesS.Defs` + deps. `moves_ref` quotes the rev-6 display (≤ 3 lines).

### Layer S0 — dispatch, arithmetic core, conventions [7 units]

**U1 · `MovesS.dispatch_spec` · Dispatch.lean · easy**
`statement`: `theorem dispatch_spec (o : Outcome V State) (h1 : 1 ≤ o.m) (hc : o.c ≤ o.m) :`
`(routeOf o = .termFin ↔ o.c = 0) ∧ (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧`
`(routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m)`
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION: the three predicates partition
{(m, c) : m ≥ 1, 0 ≤ c ≤ m} (c ≥ 1 with m = 1 forces c = 1)."
deps: Defs · hypothesis_fields: none · sketch: unfold `routeOf`; `omega` per branch
(c ≥ 1 ∧ m = 1 ⟹ c = 1 since c ≤ m). Both directions of each iff by `split_ifs`.

**U2 · `MovesS.ktri` · KTri.lean · easy**
`statement`: `theorem ktri (T) (hdc : DegCons T) {e τ o} (hm : 2 ≤ (T.odata e τ o).m) :`
`∀ μ ∈ (T.odata e τ o).mem, μ.size < e`
moves_ref: "each member e_j ≥ 1, Σ_j e_j ≤ e; hence at m ≥ 2 EVERY e_j < e (two same-size
children would need 2e > e; a same-size child with any sibling needs e + 1 > e)."
deps: Defs · hypothesis_fields: DegCons (CL-11, [1v]) · sketch: μ.size + (m−1)·1 ≤ Σ sizes
≤ e via `List.sum` bound over the other members (each ≥ 1 by `size_pos`); `omega`.

**U3 · `MovesS.kcol_agree` · KColAgree.lean · easy**
`statement`: `theorem kcol_agree (T) (hdc : DegCons T) {e τ o} (he : 1 ≤ e)`
`(hmem : ∃ μ ∈ (T.odata e τ o).mem, μ.continuing ∧ μ.size = e) : (T.odata e τ o).m = 1`
moves_ref: "the degree law … gives m ≥ 2 ⟹ every e_j ≤ e − 1 < e ⟹ no member is a block-e
state ⟹ o is NO K_e column. So [1v]'s columns sit inside the (c = 1, m = 1) bucket"
deps: U2 · hypothesis_fields: DegCons · sketch: contrapose: m ≥ 2 + U2 gives size < e,
contradicting size = e. (Agreement check (ii) — the pass-6 missing premise, now derived.)

**U4 · `MovesS.scs_flank` · ScsFlank.lean · medium**
`statement`: `theorem scs_flank (T) (S : SCSData T) {e τ o} (hm : (T.odata e τ o).m = 1) :`
`S.W e τ o = e * S.ℓ e τ o ∧ S.g e τ o * S.μ e τ o = S.ℓ e τ o`
moves_ref: "(1) m = 1 LEAVES NO ROOM TO SHRINK … m = 1 forces NO flank side (the read side
spans the window: e·ℓ = W) and a SINGLETON residual shape λ = {(g, μ)}, i.e. g·μ = ℓ."
deps: Defs · hypothesis_fields: SCSData.flank_empty/lam_singleton ([2a] SP.1's letter-field
typing — flank sides and non-selected residual factors ARE members) · sketch: at wave 2 the
two conclusions ARE the fields fired at hm; if MovesSp lands first, restate the fields as
member-injections (each flank side ↪ mem, each residual factor ↪ mem) and derive by counting
(m = 1 leaves no room). FLAG: field-vs-derivation status recorded for the audit.

**U5 · `MovesS.scs_stage` · ScsStage.lean · easy**
`statement`: `theorem scs_stage (T) (S : SCSData T) {e τ o} (hm : (T.odata e τ o).m = 1) :`
`S.W' e τ o * S.D' e τ o = S.W e τ o * S.D e τ o`
moves_ref: "W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D equals the parent's — and cluster
size IS the stage product W·D"
deps: U4 · hypothesis_fields: SCSData.stage_D/stage_W (§B2-DEF D.5 "deg Φ̂ = e·g·deg Φ",
D.8/D.10 "the child window is [0, μ]") · sketch: rewrite stage_W, stage_D; U4 gives
g·μ = ℓ and W = e·ℓ; `ring_nf` + substitute: μ·(e·g·D) = (g·μ)·e·D = ℓ·e·D = W·D.

**U6 · `MovesS.scs` · Scs.lean · medium**
`statement`: `theorem scs (T) (S : SCSData T) (hdc : DegCons T) {e τ o}`
`(hk : routeOf (T.odata e τ o) = .kcol) : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e`
moves_ref: "(SCS) a (c = 1, m = 1) outcome's single child inherits the block size: e₁ = e —
a size-dropping child never comes alone."
deps: U1, U4, U5 · hypothesis_fields: SCSData.cluster_parent/cluster_child (the [1v] CTS-S
datum "cells at cluster size e") · sketch: hk + U1 gives m = 1; cluster_child: size =
W′·D′; U5: = W·D; cluster_parent: = e. DISCHARGES `TableFamily.kcolSameSize` — instantiators
supply SCSData + DegCons instead of the raw field. (The SP-DAG "e = g = 1, μ < W" edge is a
species edge through a (c ≥ 1, m ≥ 2) outcome — fenced by hk, no unit needed.)

**U7 · `MovesS.bdy_partition` · Bdy.lean · medium**
`statement`: `theorem bdy_partition (fe : ℕ) : ∀ r : ℕ, (bdyOwner fe r = .entrance ↔`
`r ≤ fe) ∧ (bdyOwner fe r = .block ↔ fe < r)` — plus
`theorem bdy_no_double (fe r) : ¬(bdyOwner fe r = .entrance ∧ bdyOwner fe r = .block)`
moves_ref: "(BDY) … the ENTERING READ of a block entrance belongs to the ENTRANCE SIDE …
Node shadow: the first entrance node ν is BLOCK-side as a STATE INDEX, while the edge INTO
ν is entrance-side MASS — no read omitted, none double-charged."
deps: Defs · hypothesis_fields: none · sketch: unfold; `split_ifs` + `omega`. The point is
the PINNED DEFINITION (edge-based, entrance-inclusive) consumed by β's conditioning and by
(CUT-WD) at wave 4 — the lemma certifies exhaustive/exclusive read ownership.

### Layer S1 — (K-SUB) sub-stochasticity [3 units]

**U8 · `MovesS.ksub_regroup` · KSubRegroup.lean · medium**
`statement`: `theorem ksub_regroup (T) (e τ) : (∑ o : T.Out e τ, oneStepMass T e τ o) =`
`(∑ β, Kmat T e τ β) + (∑ σ' ∈ T.SigSet, bTerm T e σ' τ) + (∑ o ∈ splitOuts T e τ, T.J e τ o)`
moves_ref: "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′} b_e^{term,fin}(τ)(σ′) + (branching-cell one-step
mass, per cell once) = 1, the third summand being exactly Σ_o J_{τ,o}"
deps: U1 · hypothesis_fields: TableFamily.SigSet covers all occurring v(o) (an
instantiation duty — add field `sig_covers`); kcolSameSize (via Kmat) · sketch: partition
the roster Finset by `routeOf` (U1: exhaustive/exclusive); `Finset.sum_fiberwise_of_maps_to`
regroups kcol terms by target β and termFin terms by verdict multiset; split terms are J by
`oneStepMass` defn. Pure finite regrouping — no measure content.

**U9 · `MovesS.ksub` · KSub.lean · easy**
`statement`: `theorem ksub (T) (L : LedgerIV T) (e τ) : (∑ β, Kmat T e τ β) +`
`(∑ σ' ∈ T.SigSet, bTerm T e σ' τ) + (∑ o ∈ splitOuts T e τ, T.J e τ o) = 1`
moves_ref: "PART-1 (the digit-cell partition identity, per representative, countable across
heights — [1v] V.3(iv)'s route) gives (K-SUB) …"
deps: U8 · hypothesis_fields: LedgerIV.part1 ((iv)-PART-1 + XHD-s, owner [1v] — the routed
form; the NINE CL-5 tags ride the structure) · sketch: U8 ▸ L.part1. CONDITIONALITY note in
docstring: GIVEN the (iv) ledger + DEG-CONS + the (m,c) classification with (SCS) — exactly
the note's rev-6 bracket. PART-2's marked-row surplus is NEVER consumed (no field exists).

**U10 · `MovesS.ksub_pool` · KSubPool.lean · medium**
`statement`: `theorem ksub_pool (T) (L : LedgerIV T) (e τ) (P : PoolHyp T e q₀)`
`(hTG : ∀ o, 0 ≤ evalAt q₀ (T.TG e τ o)) (hJ : ∀ o, 0 ≤ evalAt q₀ (T.J e τ o)) :`
`(∀ β, 0 ≤ P.A ⟨τ,_⟩ ⟨β,_⟩) ∧ (∑ β, P.A ⟨τ,_⟩ ⟨β,_⟩) ≤ 1`
moves_ref: "K_e's rows are genuine sub-distributions with exits typed terminal/split …
every summand ≥ 0 (the ns-bound tail rides INSIDE the K_e term)"
deps: U9, U19 (evalAt) · hypothesis_fields: per-pool nonneg of the evaluated T·G/J masses
(a MovesV evaluation duty) · sketch: evaluate U9 at q₀ via evalAt (a RingHom on OKat);
drop the two nonnegative exit summands; row sum ≤ 1.

### Layer S2 — the block-indexed linear system over ℚ(q) and its solve [8 units]

**U11 · `MovesS.decompFintype` · Decomp.lean · medium**
`statement`: `instance decompFintype (V) [DecidableEq V] (m : ℕ) (σ' : Multiset V) :`
`Fintype { g : Fin m → Multiset V // ∑ j, g j = σ' }`
moves_ref: "Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m … — the MULTISET CONVOLUTION over children's
types"
deps: — · hypothesis_fields: none · sketch: induct on m; m = 0: subsingleton (σ' = 0);
step: a decomposition is (g 0, rest) with g 0 ≤ σ' (finitely many sub-multisets via
`Multiset.toFinset`-bounded counts / `Multiset.Powerset`) and rest decomposing σ' − g 0.
Build via `Fintype.ofSurjective` from the sigma of powerset × recursive instance.

**U12 · `MovesS.powSubst` · PowSubst.lean · medium**
`statement`: `noncomputable def powSubst (δ : ℕ) : Qq →+* Qq` with
`theorem powSubst_X (δ) : powSubst δ (RatFunc.X) = RatFunc.X ^ δ` and
`theorem powSubst_C (δ c) : powSubst δ (RatFunc.C c) = RatFunc.C c`
moves_ref: "each leg is an already-solved block's entry composed with q ↦ q^{δ_j} (which
maps ℚ(q) → ℚ(q)); the ARGUMENT convention is [2r] (e2) (δ absolute)"
deps: — · hypothesis_fields: none (δ ≥ 1 where consumed) · sketch: `IsFractionRing.lift`
(RatFunc ℚ is the fraction field of ℚ[X]) over `(Polynomial.aeval (X^δ)).toRingHom`:
nonzero polynomials map to nonzero (aeval at X^δ on a domain: leading terms can't cancel;
degree multiplies by δ — for δ = 0 restrict or accept constants), hence to units of Qq.

**U13 · `MovesS.solve_iff` · SolveIff.lean · easy**
`statement`: `theorem solve_iff (K : Matrix ι ι Qq) (b β : ι → Qq) [Fintype ι] :`
`β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b`
moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} + b_e^split"
deps: — · hypothesis_fields: none · sketch: `sub_mulVec`, `one_mulVec`; both directions by
`funext` + abelian-group rearrangement (`sub_eq_iff_eq_add`).

**U14 · `MovesS.solve_exists_unique` · SolveEU.lean · medium**
`statement`: `theorem solve_exists_unique (K : Matrix ι ι Qq) (b : ι → Qq) [Fintype ι]`
`[DecidableEq ι] (hdet : (1 - K).det ≠ 0) : ∃! β, β = K *ᵥ β + b` — with the witness
`corollary solve_val : ((1 - K)⁻¹ *ᵥ b) = K *ᵥ ((1 - K)⁻¹ *ᵥ b) + b`
moves_ref: "THE SOLVE: GIVEN det(I − K_e) ≠ 0 in ℚ(q) (S.4), Cramer/adjugate gives …
every β_{e,τ}(σ′) is one fixed rational function."
deps: U13 · hypothesis_fields: hdet (supplied by U22 given E0) · sketch: `isUnit_iff_ne_zero`
+ `Matrix.isUnit_iff_isUnit_det` ⟹ IsUnit (1−K); existence: `Matrix.mul_nonsing_inv` +
`Matrix.mulVec_mulVec`; uniqueness: two fixpoints differ by v with (1−K) *ᵥ v = 0, kill via
`Matrix.nonsing_inv_mul` (left-multiply by the inverse).

**U15 · `MovesS.solve_cramer` · SolveCramer.lean · medium**
`statement`: `theorem solve_cramer (K b) [Fintype ι] [DecidableEq ι]`
`(hdet : (1 - K).det ≠ 0) (τ : ι) :`
`(1 - K)⁻¹ *ᵥ b = fun τ => ((1 - K).det)⁻¹ * ((1 - K).adjugate *ᵥ b) τ`
moves_ref: "Cramer/adjugate gives β_e = adj(I − K_e) b_e / det(I − K_e) entrywise —
finitely many +/×/÷ over ℚ(q)"
deps: U14 · hypothesis_fields: hdet · sketch: `Matrix.inv_def` (A⁻¹ = det⁻¹ʳ • adjugate) +
`Matrix.smul_mulVec_assoc`; or `Matrix.det_smul_inv_mulVec_eq_cramer` +
`Matrix.cramer_eq_adjugate_mulVec`. This is RS.2's DISPLAYED form — the adjugate
rationality theorem: entries are ratios of ℤ[entries]-polynomials, so fixed coefficients
⟹ fixed rational functions, p entering ONLY at evaluation q = p (docstring duty).

**U16 · `MovesS.blockSolve` · BlockSolve.lean · hard**
`statement`: `noncomputable def blockSolve (T) (hdc : DegCons T)`
`(hdet : ∀ e ≤ n, (1 - Kmat T e).det ≠ 0) : ∀ e ≤ n, T.State e → Multiset T.VType → Qq`
moves_ref: "b_e^split is multilinear in STRICTLY-SMALLER-BLOCK solutions only, (R_e) stays
LINEAR within block e … blocks solve bottom-up, each b_e^split leg already solved."
deps: U2 (ktri), U11, U12, U14 · hypothesis_fields: DegCons; per-e hdet · sketch: strong
recursion on e (`Nat.strong_induction_on`): given βlt on e' < e, form b := bTerm + bSplit
(bSplit's continuing legs have size < e by U2 — the WF certificate) and set
blockSolve e := (1 - Kmat T e)⁻¹ *ᵥ b, per σ' ∈ SigSet. The (K-TRI) triangularity IS the
recursion's legitimacy. Plumbing-heavy (dependent WF recursion + per-σ' vectors): HARD.

**U17 · `MovesS.blockSolve_spec` · BlockSolveSpec.lean · medium**
`statement`: `theorem blockSolve_spec (T hdc hdet) (e) (he : e ≤ n) (σ' ∈ T.SigSet) :`
`blockSolve T hdc hdet e he · σ' = Kmat T e *ᵥ (blockSolve … e he · σ')`
`+ bTerm T e σ' + bSplit T e (fun e' h' => blockSolve … e' …) σ'`
moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} + b_e^split [UNCONDITIONAL — the lump
form]; (R_e-exact) β_e^full = β_e [GIVEN (ns-null) — CLOSED at [3t] §T.2]"
deps: U16, U14 · hypothesis_fields: as U16 · sketch: unfold one recursion layer; U14's
witness equation. (R_e-exact) needs NO unit: (ns-null) is CLOSED and the lump/full split is
measure-side typing — docstring records the discharged tag, per the note's display.

**U18 · `MovesS.rsh_def` · RshDef.lean · easy**
`statement`: `noncomputable def Rsh (T) (B : RS1Bundle T) (σ : B.SplitTy) : Qq :=`
`∑ Ŝ, B.Wsh Ŝ * shConv T Ŝ σ` — with `theorem rsh_mem : True` replaced by the docstring
duty: Rsh is a FINITE ℚ(q)-combination of W_Ŝ, powSubst-legs of blockSolve, and factor-1
leaves — rationality BY TYPE (RS.2's conclusion for R_σ).
moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ …} ∏_{i=1}^{k(Ŝ)}
β_{e_i(Ŝ),τ_i(Ŝ)}(σ_i)(q^{δ_i})"
deps: U11, U12, U16 · hypothesis_fields: RS1Bundle.finSh ([2a] finiteness of
height-forgotten shapes); Wsh's production = CL-17(ii) OPEN (cited, never proved) ·
sketch: definition + `Fintype` sums; the convolution via U11's instance; σ₀(Ŝ) offsets the
multiset per shapeData. INIT-RAT/(J-RAT)/XHD-s ride as RS4TagChain cites, not proofs.

### Layer S3 — pools, evaluation, ESCAPE(E0) consequences [5 units]

**U19 · `MovesS.evalAt` · EvalAt.lean · medium**
`statement`: `def OKat (q₀ : ℚ) : Subring Qq` (elements with `denom.eval q₀ ≠ 0`) and
`noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ` with
`theorem evalAt_coe (q₀ f) : evalAt q₀ f = RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq)`
moves_ref: "EVALUATION IS PER POOL (rev 3): symbolic det ≠ 0 prevents no zero or
uncancelled pole at an individual q₀ = p^δ."
deps: — · hypothesis_fields: none · sketch: closure of the denom-nonvanishing locus under
+/× via `RatFunc.denom_add_dvd`-style divisibility (denom(x∘y) ∣ denom x · denom y; a
divisor of a q₀-nonvanishing product is q₀-nonvanishing over a field); hom laws from
`RatFunc.eval_add`/`eval_mul` (their hypotheses are exactly membership). Mathlib-search
duty: check for an existing localization `Polynomial.Localization`/valuation-subring route.

**U20 · `MovesS.eval_det` · EvalDet.lean · easy**
`statement`: `theorem eval_det (q₀) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (OKat q₀)) :`
`evalAt q₀ M.det = (M.map (evalAt q₀)).det`
moves_ref: "the sealed check that the evaluated object's q₀-value … equals the
active-subsystem solve there" (S.4 (ii), the eval/det compatibility it presupposes)
deps: U19 · hypothesis_fields: none · sketch: `RingHom.map_det` (mathlib) applied to
`evalAt q₀`; `Matrix.det` commutes with `RingHom.mapMatrix`.

**U21 · `MovesS.e0_det_ne_zero` · E0Det.lean · hard**
`statement`: `theorem e0_det_ne_zero {ι} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℚ}`
`(h : EscapeE0 A) : (1 - A).det ≠ 0`
moves_ref: "A(q₀) being a FINITE nonnegative matrix, ρ(A(q₀)) < 1, the Neumann series
converges, and (I − A(q₀))^{−1} ≥ 0" (the det ≠ 0 face; ρ-language not formalized)
deps: — · hypothesis_fields: EscapeE0 (CL-1 — the OPEN KERNEL as hypothesis; this unit is
the "hence", not the kernel) · sketch: contrapositive: det = 0 gives v ≠ 0 with
(1−A) *ᵥ v = 0 (`Matrix.exists_mulVec_eq_zero_iff`), so A *ᵥ v = v, so A^k *ᵥ v = v; bound
|v i| = |(A^k *ᵥ v) i| ≤ ‖v‖∞ · (A^k *ᵥ 1) i (nonneg entries) → 0; v = 0, contradiction.
Entrywise sup-norm estimates over ℚ — fiddly, no topology needed beyond the given Tendsto.

**U22 · `MovesS.rs3_det_symbolic` · Rs3Det.lean · medium**
`statement`: `theorem rs3_det_symbolic (T) (e) (P : PoolHyp T e q₀)`
`(hall : P.Act = Finset.univ) (hOK : ∀ τ β, (Kmat T e τ β) ∈ OKat q₀) :`
`(1 - Kmat T e).det ≠ 0`
moves_ref: "at all-active primes (cofinitely many …) K_e(p) = A and ρ(A) < 1 gives
det(I − A) ≠ 0; a rational function vanishing at infinitely many prime evaluations is 0,
so det(I − K_e) ≠ 0 in ℚ(q) — the SYMBOLIC block solve is licit."
deps: U19, U20, U21 · hypothesis_fields: PoolHyp at ONE all-active pool (E0 rides inside);
all-activity + entry evaluability = MovesV instantiation duties · sketch: ONE witness
suffices for ≠ 0 (the note's "infinitely many" is the same argument with slack): if
det(1−K) = 0 in Qq then U20 evaluates det(1−A) = 0 at q₀, contradicting U21. Docstring:
per-pool solvability at OTHER pools stays conditional on ITS PoolHyp — the rev-3 widening;
no uniformity in q₀ claimed anywhere (ESCAPE-UNIF is consumed by NOTHING).

**U23 · `MovesS.e0_inv_nonneg` · E0InvNonneg.lean · hard**
`statement`: `theorem e0_inv_nonneg {A : Matrix ι ι ℚ} (h : EscapeE0 A) (i j) :`
`0 ≤ (1 - A)⁻¹ i j`
moves_ref: "the Neumann series converges, and (I − A(q₀))^{−1} ≥ 0."
deps: U21 · hypothesis_fields: EscapeE0 · sketch: algebraic Neumann: with
S_k := Σ_{m<k} A^m, (1−A) S_k = 1 − A^k, so S_k = (1−A)⁻¹(1 − A^k) and (1−A)⁻¹ =
S_k + (1−A)⁻¹ A^k; entries of S_k are ≥ 0 and (1−A)⁻¹A^k → 0 entrywise (fixed matrix times
A^k *ᵥ bounds); limit of nonnegatives. Consumer: [4]/SQ.2 only — NOT on MovesS's own
downstream path; may be deferred without blocking U24–U28.

### Layer S4 — RS.1's three clauses and RS.4's checksum [5 units]

**U24 · `MovesS.rs1_deep` · Rs1Deep.lean · medium**
`statement`: `theorem rs1_deep (T) (B : RS1Bundle T) (hdc hdet) (e) (he : e ≤ n)`
`(σ') (hσ : σ' ∈ T.SigSet) : βfam B e σ' = (1 - Kmat T e)⁻¹ *ᵥ`
`(bTerm T e σ' + bSplit T e (βlt-of βfam) σ')`
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′) — the
ENTRANCE-FREE conditional subtree value (S.0 typing) … solvability of the inverse is
RS.3's (S.4)."
deps: U13, U14, U17 · hypothesis_fields: RS1Bundle.recursion (the measured (R_e-lump)
fixpoint — [3t]/TREE-EXP territory, wave-4 discharge) + hdet (U22 given PoolHyp) · sketch:
B.recursion says βfam solves the fixpoint; U14 uniqueness identifies it with the inverse
witness. The CONSUMPTION-DAG discipline (S.1 status line) holds: nothing here cites PCI.

**U25 · `MovesS.rs1_sh` · Rs1Sh.lean · medium**
`statement`: `theorem rs1_sh (T) (B : RS1Bundle T) (σ : B.SplitTy) :`
`B.R σ = Rsh T B σ`
moves_ref: "(RS.1-SH) THE SHALLOW CONVOLUTION (the base clause): R_σ = Σ_{Ŝ} W_Ŝ(q) ·
Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ …} ∏ β_{e_i,τ_i}(σ_i)(q^{δ_i})"
deps: U18 · hypothesis_fields: RS1Bundle.shallow_expansion ((CUT-WD)-regrouped TREE-EXP —
the measure-side content, wave 4; (SIB)/CL-10, REL.2/CL-8, XRB/CL-9 tags ride the bundle) ·
sketch: rewrite shallow_expansion against Rsh's definition. HONESTY FLAG (audit §4): at
wave 2 this unit is ASSEMBLY — the field is nearly the display; its VALUE is pinning the
exact convolution shape MovesT must discharge, quantifier-exact.

**U26 · `MovesS.rs1_marked` · Rs1Marked.lean · easy**
`statement`: `theorem rs1_marked (T) (B : RS1Bundle T) (e) (he : e ≤ n) :`
`(markedTotal B e).val = T.ι e ⬝ᵥ ((1 - Kmat T e)⁻¹ *ᵥ bAgg T e)` — `markedTotal : MuHat`
moves_ref: "(RS.1-MARKED) the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed
MARKED-entrance total (post-split marks, CTS-M(iii) POST-SPLIT) … NEVER summed into R_σ."
deps: U14 · hypothesis_fields: RS1Bundle.marked_pairing (ENT-AGG/(COMP-AGG), wave 4) ·
sketch: unfold the field. The FENCE is structural: `MuHat` has no coercion to `Qq` and no
`Add MuHat` instance — summing it into a density is a TYPE ERROR, as the note demands.
ORIENTATION duty (docstring): ι acts ONCE on the left; never inserted into K or b.

**U27 · `MovesS.ratfunc_eval_infinite` · EvalInfinite.lean · medium**
`statement`: `theorem ratfunc_eval_infinite (f : Qq) (S : Set ℚ) (hS : S.Infinite)`
`(hden : ∀ x ∈ S, f.denom.eval x ≠ 0) (hval : ∀ x ∈ S, RatFunc.eval (RingHom.id ℚ) x f = 0) :`
`f = 0`
moves_ref: "a rational function equal to 1 at infinitely many prime powers is identically 1"
(S.5; stated at 0 — apply to f − 1)
deps: — · hypothesis_fields: none · sketch: eval = num.eval x / denom.eval x; hden + hval
force `f.num.eval x = 0` on S; `Polynomial.eq_zero_of_infinite_isRoot` (S infinite ⊆ roots)
gives num = 0; `RatFunc.num_eq_zero_iff` (or num/denom reconstruction) gives f = 0.
REUSED by U22's route in its infinitely-many form and by U28 — the note's one argument.

**U28 · `MovesS.rs4` · Rs4.lean · medium**
`statement`: `theorem rs4 (T) (C : RS4TagChain T) : (∑ σ, C.bundle.R σ) = 1`
moves_ref: "(RS.4) Σ_σ R_σ = 1 identically in q. ROUTE (DERIVED, GIVEN its inherited set):
at each prime p the decided-mass series totals 1 — X.3's density form … RS.1 equates that
series with Σ_σ R_σ(p); a rational function equal to 1 at infinitely many prime powers is
identically 1."
deps: U27 · hypothesis_fields: the FULL RS4TagChain — E0 per-pool (CL-1), the nine CL-5
inputs, RS.1's set (CL-10/CL-17/CL-8 + XRB's), X.3 (CL-4), and the RS.2 rationality chain
(CL-6, XHD-s, INIT-RAT, CL-17(ii), (J-RAT)) — every field CITED by the docstring tag list;
`primewise` is the wave-4 discharge point · sketch: apply U27 to (Σ_σ R σ) − 1 on
C.primewise's infinite set (denominator control from the same field; denom(f−1) = denom f).
Docstring: "may NOT be marked unconditional before those close" — the acceptance fence.

---

## 3b. The claim DAG (load-bearing edges, acyclic by layer)

`U1 → {U3(via U2), U6, U8}` · `U2 → {U3, U16}` · `U4 → U5 → U6` (the (SCS) chain:
flank-fills-window → W′D′ = WD → size inheritance) · `U6 discharges TableFamily.kcolSameSize
→ {Kmat well-typed: U8, U16, U22, U24}` · `U8 → U9 → U10` ((K-SUB) chain) ·
`U11, U12 → {U16, U18}` · `U13 → U14 → {U15, U16, U24, U26}` · `U16 → U17 → U24` ·
`U19 → {U10, U20} ; U20, U21 → U22 → (hdet of U16/U24)` · `U18 → U25` · `U27 → U28`.
No unit cites RS.1's PCI sites from inside U24's proof (the CONSUMPTION-DAG discipline);
U23 hangs off U21 with no MovesS consumer (its consumer is [4]/MovesU).

---

## 4. Honest gaps & audit flags (for the Codex semantic audit — quote-and-classify targets)

1. **The `True` placeholder fields** (LedgerIV items 1–9 except part1; RS1Bundle
   treeExp/sib/tbcapVp/rel2/xrbSet; RS4TagChain x3/ivPoly/xhdS/initRat/wshRat/jRat;
   PoolHyp.active_value_agreement). They are NAMED so tags are citable and droppable-never;
   they carry NO content at wave 2. The audit should verify each maps 1:1 onto a note tag
   and that NO conclusion of a MovesS unit needs the placeholder's content (only part1,
   recursion, shallow_expansion, marked_pairing, primewise, e0 carry load).
2. **XRB baked in by type** (header): β has no h_ent index structurally. S.1's
   PROVED-under-hypotheses status is NOT re-established in Lean at wave 2 — flag any future
   claim that MovesS "proves XRB". Its hypothesis set rides `xrbSet`.
3. **`part1` is the ROUTED form of PART-1** — the note derives the routing ((K-SUB)) and
   CITES the partition; our field fuses "PART-1 + each cell's mass is TG-or-J per its
   route". Audit check: this matches "the third summand being exactly Σ_o J_{τ,o} — the
   (J-RAT) cell-level object supplied by PART-1, never the marked offspring row", and
   PART-2's surplus row has NO field (unconsumable — the rev-1 critical stays fixed).
4. **U4 (scs_flank) is field-vs-derivation** at wave 2 (SP.1's letter fields live in
   MovesSp): the unit fires the fields; the deeper member-injection derivation is a
   recorded UPGRADE path, not a silent strengthening.
5. **U25 (rs1_sh) is assembly-thin** by design; its value is the quantifier-exact pin of
   the convolution MovesT must discharge. Same for U26.
6. **ESCAPE(E0) is a hypothesis structure, NEVER proved** (CL-1, this note's own open
   kernel). U21/U23 are its displayed "hence" consequences. ESCAPE-UNIF does not exist in
   this corpus (consumed by nothing — the note's explicit fence).
7. **(REG-p)** is defined here as the per-pool bundle over all relevant δ; MovesU consumes
   it. The relevant-pool set Δ is a parameter, not computed (the [2r] (e2) δ-roster is a
   MovesT/MovesR duty).
8. **No measure theory anywhere**: every μ̂/density-typed statement enters through bundle
   fields. `MuHat` enforces the type fence structurally (no Add, no coercion).
9. **S.7 (gate RESUM-n3), the probe roster, and (CUT-WD)'s proof** are out of corpus scope
   (census-side / wave-4 measure-side); (BDY) is in scope as the pinned definition (U7).

---

## 5. Conventions for elaboration (phase E) and the prover fleet

Build per file: `lake env lean LeanUrat/MovesS/<file>.lean` (never bare `lake build
LeanUrat`, per repo gotcha). `Defs.lean` must compile sorry-free EXCEPT the four skeleton
`sorry` defs (`kTarget`, `oneStepMass`, `shConv`, `bSplit` body, `βfam`/`markedTotal`
wiring) which the E-phase elaborates BEFORE unit fan-out; end every unit file with
`#print axioms` (Lean-core only; `sorryAx` flagged in docstrings). Statement changes to
ANY structure field = statement-fence event (designer sign-off). Mathlib names verified
against the pinned cache 2026-07-28: `Matrix.isUnit_iff_isUnit_det`,
`Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul`, `Matrix.inv_def`,
`Matrix.cramer_eq_adjugate_mulVec`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`,
`Matrix.det_smul_inv_mulVec_eq_cramer`, `Polynomial.eq_zero_of_infinite_isRoot`,
`RatFunc.instField`, `RatFunc.eval`, `RatFunc.eval_add`/`eval_mul` (hypothesis-carrying),
`IsFractionRing.lift`, `RingHom.map_det`.

**Unit census: 28 units.** Easy {U1,U2,U3,U5,U7,U9,U13,U18,U20,U26} = 10; hard
{U16 blockSolve WF-recursion, U21 e0_det_ne_zero, U23 e0_inv_nonneg} = 3; medium (the
remaining 15: U4,U6,U8,U10,U11,U12,U14,U15,U17,U19,U22,U24,U25,U27,U28). Total 28.


codex
I’m auditing the 28 statements against the displays, with special attention to the hypothesis bundles: several “named” fields are propositions with no mathematical content, which affects both fidelity and non-vacuity.
codex
1. **CRITICAL — hypothesis tags are content-free and therefore silently dropped.**

   Offending specs:

   > `LedgerIV.xhd : True`  
   > `d4r0 : True`  
   > `part_meas : True`  
   > `rep : True`  
   > `hmc : True`  
   > `act : True`  
   > `init : True`  
   > `comp : True`

   > `RS1Bundle.treeExp : True`  
   > `sib : True`  
   > `tbcapVp : True`  
   > `rel2 : True`  
   > `xrbSet : True`

   > `RS4TagChain.x3 : True`  
   > `ivPoly : True`  
   > `xhdS : True`  
   > `initRat : True`  
   > `wshRat : True`  
   > `jRat : True`

   > `PoolHyp.active_value_agreement : True`

   A named `True` field does not encode the note’s open kernel. Every such structure is constructible without XHD, HMC, SIB, REL.2, X.3, INIT-RAT, J-RAT, or active-value agreement. Merely citing the field in a docstring does not make the theorem conditional on its mathematical content. This violates hypothesis fidelity and makes downstream claims weaker/vacuously satisfiable.

2. **CRITICAL — XRB is silently strengthened into a definition.**

   Offending specification:

   > “**XRB is baked in BY TYPE** … β has NO `h_ent` index … S.1’s proof … is NOT a MovesS unit.”

   The note proves height invariance under XHD, JC-INV, SIB/JC-multi, TB-CAP/VP, REL.2(a)/(b)/(d), and ns-null. Defining β without an entrance-height argument assumes the conclusion before those hypotheses are supplied. The contentless `xrbSet : True` does not repair this. MovesS consequently admits height-free β even when XRB is false.

3. **CRITICAL — open rationality burdens are also baked into data types.**

   Offending specs:

   > `TG : ∀ e τ, Out e τ → Qq`  
   > `J : ∀ e τ, Out e τ → Qq`  
   > `ι : ∀ e, State e → Qq`  
   > `Wsh : Shape → Qq`

   and U15:

   > `theorem solve_cramer ...`

   The note obtains these `ℚ(q)` memberships only GIVEN CTS-M(iv)-POLY, XHD-s, INIT-RAT, J-RAT, and CL-17(ii). Here arbitrary `Qq` data are admitted before those open hypotheses, so RS.2 rationality follows by typing alone. The contentless tag fields are unused and cannot express the note’s conditional claim.

4. **CRITICAL — SCS is assumed inside `TableFamily` before U6 purports to derive it.**

   Offending specs:

   > `kcolSameSize : ... routeOf ... = .kcol → ∀ μ ∈ ..., μ.size = e`

   and U6:

   > `theorem scs ... (hk : routeOf ... = .kcol) : ∀ μ ∈ ..., μ.size = e`

   `Kmat` already depends on `kcolSameSize`. U6 cannot “discharge” or replace a field of an existing `TableFamily`; it merely reproves a conclusion that every admissible `TableFamily` was required to contain. This makes the SCS derivation circular and silently assumes the note’s derived result.

5. **CRITICAL — U4 assumes exactly what it advertises as derived.**

   Offending unit:

   > **U4** `theorem scs_flank ... (hm : ...m = 1) :`  
   > `S.W e τ o = e * S.ℓ e τ o ∧ S.g e τ o * S.μ e τ o = S.ℓ e τ o`

   Its hypothesis structure contains:

   > `flank_empty : ... m = 1 → W = e * ℓ`  
   > `lam_singleton : ... m = 1 → g * μ = ℓ`

   Thus U4 is the conjunction of two assumed conclusions, not the note’s derivation from SP.1’s flank/residual-member typing. The promised future “upgrade path” is not a current hypothesis field.

6. **CRITICAL — U7 formalizes only half of the (BDY) convention.**

   Offending unit:

   > **U7** `bdyOwner fe r = .entrance ↔ r ≤ fe` and  
   > `bdyOwner fe r = .block ↔ fe < r`

   The cited display also requires:

   - the entrance read to carry entrance-side mass and retained entrance height;
   - β to charge neither mass nor height for it;
   - the first entrance node to be block-side as a state index;
   - Wₛ to include the entering read.

   `ReadOwner` describes only read indices. It cannot state the different node/edge ownership or the mass/height conditions, so U7 is strictly weaker than the quoted (BDY) display.

7. **CRITICAL — U8 is false for the declared `TableFamily`.**

   Offending unit:

   > **U8**  
   > `∑ o, oneStepMass ... = ∑ β, Kmat ... + ∑ σ' ∈ T.SigSet, bTerm ... + ∑ split ...`

   The unit itself admits the missing requirement:

   > “add field `sig_covers`”

   No such field exists. `SigSet` may omit the verdict multiset of a terminal outcome; that outcome then contributes on the left but not to the terminal sum on the right. The statement is not valid for its quantified `T`.

8. **CRITICAL — U9 assumes the already-routed K-SUB identity instead of the note’s inputs.**

   Offending unit:

   > **U9** `theorem ksub (T) (L : LedgerIV T) ... : ... = 1`

   with:

   > `LedgerIV.part1 : ∀ e τ, (∑ o, oneStepMass T e τ o) = 1`

   The note derives K-SUB GIVEN PART-1, DEG-CONS, the `(m,c)` classification, SCS, and the distinction between TG and cell-level J. Here `oneStepMass` has already fused those routing conclusions, while U9 has neither `DegCons` nor `SCSData`. This silently moves derived content into a hypothesis/definition.

9. **CRITICAL — U12 includes the forbidden `δ = 0` case.**

   Offending unit:

   > **U12** `noncomputable def powSubst (δ : ℕ) : Qq →+* Qq`  
   > `powSubst δ RatFunc.X = RatFunc.X ^ δ`

   For `δ = 0`, this demands a field homomorphism sending `X` to `1`. It cannot extend to `ℚ(X)`, because the nonzero denominator `X − 1` maps to zero. The note’s base-change indices are positive absolute indices. The statement must not quantify over zero.

10. **CRITICAL — `bSplit` cannot express its own smaller-block premise.**

    Offending definition:

    > `def bSplit (e) (βlt : ∀ e' < e, ...) ... := sorry`

    `bSplit` has no `DegCons` or other argument proving that a continuing member of a split outcome satisfies `μ.size < e`. Therefore it cannot legally apply `βlt μ.size` for the declared arbitrary `TableFamily`. An `if h : μ.size < e` fallback would admit malformed split outcomes and change the note’s convolution.

11. **CRITICAL — U16 adds a block `e = 0` absent from the note.**

    Offending unit:

    > **U16**  
    > `hdet : ∀ e ≤ n, ...`  
    > `... : ∀ e ≤ n, T.State e → ...`

    The note’s blocks have positive size: every member size is at least one, and the induction is over actual block sizes. The blueprint quantifies over every natural `e ≤ n`, including `e = 0`, without an empty-state convention or `1 ≤ e` hypothesis. This changes the edge cases and adds an unsupported determinant obligation.

12. **CRITICAL — U17 omits the second displayed recursion clause.**

    Offending unit:

    > **U17** `blockSolve_spec ...` formalizes only `(R_e-lump)`.

    Its `moves_ref` quotes both:

    > `(R_e-lump) ...`  
    > `(R_e-exact) β_e^full = β_e [GIVEN (ns-null)]`

    Saying that `(R_e-exact)` “needs NO unit” leaves no Lean statement connecting the full conditional density to the lump value. Closed `ns-null` is still a displayed hypothesis/tagged equality in the note, not definitional equality.

13. **CRITICAL — U18’s data cannot determine the quoted shallow convolution.**

    Offending unit:

    > **U18** `def Rsh ... := ∑ Ŝ, B.Wsh Ŝ * shConv T Ŝ σ`

    `shConv` is an opaque skeleton definition, while `shapeData` stores three independent lists:

    > `List (Σ e, T.State e) × Multiset T.VType × List ℕ`

    There is no proof that the entrance and δ lists have equal lengths, no member-index correspondence, and no β/block-solve family supplied to `Rsh`. Consequently the exact product  
    `∏ᵢ β_{eᵢ,τᵢ}(σᵢ)(q^{δᵢ})` and its multiset constraint cannot be recovered from the declared data.

14. **CRITICAL — U22 changes RS.3(ii)’s hypothesis package.**

    Offending unit:

    > **U22** `rs3_det_symbolic ... (P : PoolHyp T e q₀)`  
    > `(hall : P.Act = Finset.univ) ... : det(1-K) ≠ 0`

    The note derives symbolic nonvanishing from E0 plus `(iv)-POLY`, using cofinitely many all-active prime evaluations. U22 instead assumes one specially supplied all-active/evaluable pool and omits `(iv)-POLY`. Although one nonzero evaluation is algebraically sufficient, it is a different and stronger input package than the quoted display.

15. **CRITICAL — U24’s principal hypothesis is malformed and nearly assumes RS.1-DEEP.**

    Offending field and unit:

    > `recursion : ∀ e ≤ n, ∀ σ' ∈ T.SigSet, ∀ hβ, βfam e σ' = ... bSplit ... hβ ...`

    > **U24** `βfam B e σ' = (1 - Kmat T e)⁻¹ *ᵥ ...`

    Quantifying over every arbitrary `hβ` says the same measured β solves recursions with every possible smaller-block family. That is stronger than and generally incompatible with the note. Moreover `βfam` and `βlt-of βfam` are not fields tying this family to the triangular `blockSolve`.

16. **CRITICAL — U25 assumes RS.1-SH verbatim instead of deriving it.**

    Offending field and unit:

    > `shallow_expansion : ∀ σ, R σ = ∑ Ŝ, Wsh Ŝ * shConv T Ŝ σ`

    > **U25** `theorem rs1_sh ... : B.R σ = Rsh T B σ`

    The note derives RS.1-SH from TREE-EXP, CUT-WD, SIB, PCI/REL.2, XRB, and the Wₛ machinery. The structure field is already the target equality, while all those hypotheses are `True`. Thus U25 is a definitional rewrite and remains provable when every open kernel is false.

17. **CRITICAL — U26 likewise assumes RS.1-MARKED verbatim.**

    Offending field and unit:

    > `marked_pairing : ... markedTotal e = MuHat.mk (T.ι e ⬝ᵥ solveVec T e)`

    > **U26** `(markedTotal B e).val = T.ι e ⬝ᵥ ((1-K)⁻¹ *ᵥ bAgg T e)`

    The note derives this using COMP-h, COMP-hΣ, HMC/COMP-Σ, ENT-AGG, COMP-AGG, and representative independence. Those hypotheses have no content here; the measured conclusion is simply installed as a structure field.

18. **CRITICAL — U28 assumes the primewise heart of RS.4.**

    Offending field and unit:

    > `primewise : { S // S.Infinite ∧ ∀ q₀ ∈ S, ... eval ... (∑ σ, R σ) = 1 }`

    > **U28** `theorem rs4 ... : ∑ σ, C.bundle.R σ = 1`

    The note obtains the primewise equality from X.3 plus RS.1 and ns-null, then invokes the rationality chain. Here `x3 : True` and the RS.1 tags provide no content, while `primewise` directly assumes the required evaluated checksum. U28 formalizes only the final elementary RatFunc lemma, not RS.4 under the displayed inherited set.

19. **CRITICAL — the hypothesis structures have no inhabitation/nondegeneracy story.**

    Offending specs include:

    > `State : ℕ → Type` with only `Fintype (State e)`  
    > `Out : ∀ e, State e → Type` with only `Fintype (Out e τ)`  
    > `SplitTy : Type; finS : Fintype SplitTy`  
    > `Shape : Type; finSh : Fintype Shape`  
    > `Act : Finset (T.State e)`  
    > `RegP ... := ∀ ... δ ∈ Δ, Nonempty (PoolHyp ...)`

    `State e`, outcome rosters, splitting types, shapes, active sets, and `Δ` may all be empty. In particular, `RegP` is automatically true when `Δ = ∅`, despite the note requiring δ = 1 and every consumed base-change index. `LedgerIV.part1` is vacuous when `State e` is empty. No explicit instance unit connects these bundles to realized CTS blocks. This is precisely the prohibited degenerate-instance loophole.

20. **GAP — U10 is not a plausible Lean statement as written.**

    Offending unit:

    > **U10** `P.A ⟨τ,_⟩ ⟨β,_⟩`  
    > `hTG : ∀ o, 0 ≤ evalAt q₀ (T.TG e τ o)`

    There is no hypothesis `τ ∈ P.Act`; the quantified β likewise has no membership proof. Also `evalAt` accepts an element of `OKat q₀`, but `T.TG` and `T.J` have type `Qq`, with no denominator-nonvanishing witnesses. The evaluated exit sums needed to drop nonnegative terms are underspecified.

21. **GAP — U20’s `moves_ref` does not describe its statement.**

    Offending unit:

    > **U20** `evalAt q₀ M.det = (M.map (evalAt q₀)).det`

    Its quoted reference is the active-value-agreement requirement:

    > “the evaluated object's q₀-value … equals the active-subsystem solve there”

    Determinant naturality is useful infrastructure, but it is not that display. The blueprint needs a precise Defs/dependency reference for this helper rather than attributing a different mathematical claim to it.

22. **GAP — three “hard” units hide substantial multi-lemma developments.**

    Offending units:

    > **U16** `blockSolve`  
    > **U21** `e0_det_ne_zero`  
    > **U23** `e0_inv_nonneg`

    U16 combines dependent strong recursion, construction and typing of `bSplit`, substitution, and the per-block inverse solve. U21 needs a singular-kernel witness, preservation under powers, entrywise absolute-value bounds, and a finite sup-norm limit argument. U23 needs finite Neumann identities, positivity of powers and partial sums, decay of the matrix remainder, and order-closedness of limits. These sketches require several internal lemmas and do not satisfy the stated one-short-display/one-short-unit decomposition.

Counts: **19 CRITICAL / 3 GAP**

**REJECT (19 crit / 3 gap)**
tokens used
48,189
1. **CRITICAL — hypothesis tags are content-free and therefore silently dropped.**

   Offending specs:

   > `LedgerIV.xhd : True`  
   > `d4r0 : True`  
   > `part_meas : True`  
   > `rep : True`  
   > `hmc : True`  
   > `act : True`  
   > `init : True`  
   > `comp : True`

   > `RS1Bundle.treeExp : True`  
   > `sib : True`  
   > `tbcapVp : True`  
   > `rel2 : True`  
   > `xrbSet : True`

   > `RS4TagChain.x3 : True`  
   > `ivPoly : True`  
   > `xhdS : True`  
   > `initRat : True`  
   > `wshRat : True`  
   > `jRat : True`

   > `PoolHyp.active_value_agreement : True`

   A named `True` field does not encode the note’s open kernel. Every such structure is constructible without XHD, HMC, SIB, REL.2, X.3, INIT-RAT, J-RAT, or active-value agreement. Merely citing the field in a docstring does not make the theorem conditional on its mathematical content. This violates hypothesis fidelity and makes downstream claims weaker/vacuously satisfiable.

2. **CRITICAL — XRB is silently strengthened into a definition.**

   Offending specification:

   > “**XRB is baked in BY TYPE** … β has NO `h_ent` index … S.1’s proof … is NOT a MovesS unit.”

   The note proves height invariance under XHD, JC-INV, SIB/JC-multi, TB-CAP/VP, REL.2(a)/(b)/(d), and ns-null. Defining β without an entrance-height argument assumes the conclusion before those hypotheses are supplied. The contentless `xrbSet : True` does not repair this. MovesS consequently admits height-free β even when XRB is false.

3. **CRITICAL — open rationality burdens are also baked into data types.**

   Offending specs:

   > `TG : ∀ e τ, Out e τ → Qq`  
   > `J : ∀ e τ, Out e τ → Qq`  
   > `ι : ∀ e, State e → Qq`  
   > `Wsh : Shape → Qq`

   and U15:

   > `theorem solve_cramer ...`

   The note obtains these `ℚ(q)` memberships only GIVEN CTS-M(iv)-POLY, XHD-s, INIT-RAT, J-RAT, and CL-17(ii). Here arbitrary `Qq` data are admitted before those open hypotheses, so RS.2 rationality follows by typing alone. The contentless tag fields are unused and cannot express the note’s conditional claim.

4. **CRITICAL — SCS is assumed inside `TableFamily` before U6 purports to derive it.**

   Offending specs:

   > `kcolSameSize : ... routeOf ... = .kcol → ∀ μ ∈ ..., μ.size = e`

   and U6:

   > `theorem scs ... (hk : routeOf ... = .kcol) : ∀ μ ∈ ..., μ.size = e`

   `Kmat` already depends on `kcolSameSize`. U6 cannot “discharge” or replace a field of an existing `TableFamily`; it merely reproves a conclusion that every admissible `TableFamily` was required to contain. This makes the SCS derivation circular and silently assumes the note’s derived result.

5. **CRITICAL — U4 assumes exactly what it advertises as derived.**

   Offending unit:

   > **U4** `theorem scs_flank ... (hm : ...m = 1) :`  
   > `S.W e τ o = e * S.ℓ e τ o ∧ S.g e τ o * S.μ e τ o = S.ℓ e τ o`

   Its hypothesis structure contains:

   > `flank_empty : ... m = 1 → W = e * ℓ`  
   > `lam_singleton : ... m = 1 → g * μ = ℓ`

   Thus U4 is the conjunction of two assumed conclusions, not the note’s derivation from SP.1’s flank/residual-member typing. The promised future “upgrade path” is not a current hypothesis field.

6. **CRITICAL — U7 formalizes only half of the (BDY) convention.**

   Offending unit:

   > **U7** `bdyOwner fe r = .entrance ↔ r ≤ fe` and  
   > `bdyOwner fe r = .block ↔ fe < r`

   The cited display also requires:

   - the entrance read to carry entrance-side mass and retained entrance height;
   - β to charge neither mass nor height for it;
   - the first entrance node to be block-side as a state index;
   - Wₛ to include the entering read.

   `ReadOwner` describes only read indices. It cannot state the different node/edge ownership or the mass/height conditions, so U7 is strictly weaker than the quoted (BDY) display.

7. **CRITICAL — U8 is false for the declared `TableFamily`.**

   Offending unit:

   > **U8**  
   > `∑ o, oneStepMass ... = ∑ β, Kmat ... + ∑ σ' ∈ T.SigSet, bTerm ... + ∑ split ...`

   The unit itself admits the missing requirement:

   > “add field `sig_covers`”

   No such field exists. `SigSet` may omit the verdict multiset of a terminal outcome; that outcome then contributes on the left but not to the terminal sum on the right. The statement is not valid for its quantified `T`.

8. **CRITICAL — U9 assumes the already-routed K-SUB identity instead of the note’s inputs.**

   Offending unit:

   > **U9** `theorem ksub (T) (L : LedgerIV T) ... : ... = 1`

   with:

   > `LedgerIV.part1 : ∀ e τ, (∑ o, oneStepMass T e τ o) = 1`

   The note derives K-SUB GIVEN PART-1, DEG-CONS, the `(m,c)` classification, SCS, and the distinction between TG and cell-level J. Here `oneStepMass` has already fused those routing conclusions, while U9 has neither `DegCons` nor `SCSData`. This silently moves derived content into a hypothesis/definition.

9. **CRITICAL — U12 includes the forbidden `δ = 0` case.**

   Offending unit:

   > **U12** `noncomputable def powSubst (δ : ℕ) : Qq →+* Qq`  
   > `powSubst δ RatFunc.X = RatFunc.X ^ δ`

   For `δ = 0`, this demands a field homomorphism sending `X` to `1`. It cannot extend to `ℚ(X)`, because the nonzero denominator `X − 1` maps to zero. The note’s base-change indices are positive absolute indices. The statement must not quantify over zero.

10. **CRITICAL — `bSplit` cannot express its own smaller-block premise.**

    Offending definition:

    > `def bSplit (e) (βlt : ∀ e' < e, ...) ... := sorry`

    `bSplit` has no `DegCons` or other argument proving that a continuing member of a split outcome satisfies `μ.size < e`. Therefore it cannot legally apply `βlt μ.size` for the declared arbitrary `TableFamily`. An `if h : μ.size < e` fallback would admit malformed split outcomes and change the note’s convolution.

11. **CRITICAL — U16 adds a block `e = 0` absent from the note.**

    Offending unit:

    > **U16**  
    > `hdet : ∀ e ≤ n, ...`  
    > `... : ∀ e ≤ n, T.State e → ...`

    The note’s blocks have positive size: every member size is at least one, and the induction is over actual block sizes. The blueprint quantifies over every natural `e ≤ n`, including `e = 0`, without an empty-state convention or `1 ≤ e` hypothesis. This changes the edge cases and adds an unsupported determinant obligation.

12. **CRITICAL — U17 omits the second displayed recursion clause.**

    Offending unit:

    > **U17** `blockSolve_spec ...` formalizes only `(R_e-lump)`.

    Its `moves_ref` quotes both:

    > `(R_e-lump) ...`  
    > `(R_e-exact) β_e^full = β_e [GIVEN (ns-null)]`

    Saying that `(R_e-exact)` “needs NO unit” leaves no Lean statement connecting the full conditional density to the lump value. Closed `ns-null` is still a displayed hypothesis/tagged equality in the note, not definitional equality.

13. **CRITICAL — U18’s data cannot determine the quoted shallow convolution.**

    Offending unit:

    > **U18** `def Rsh ... := ∑ Ŝ, B.Wsh Ŝ * shConv T Ŝ σ`

    `shConv` is an opaque skeleton definition, while `shapeData` stores three independent lists:

    > `List (Σ e, T.State e) × Multiset T.VType × List ℕ`

    There is no proof that the entrance and δ lists have equal lengths, no member-index correspondence, and no β/block-solve family supplied to `Rsh`. Consequently the exact product  
    `∏ᵢ β_{eᵢ,τᵢ}(σᵢ)(q^{δᵢ})` and its multiset constraint cannot be recovered from the declared data.

14. **CRITICAL — U22 changes RS.3(ii)’s hypothesis package.**

    Offending unit:

    > **U22** `rs3_det_symbolic ... (P : PoolHyp T e q₀)`  
    > `(hall : P.Act = Finset.univ) ... : det(1-K) ≠ 0`

    The note derives symbolic nonvanishing from E0 plus `(iv)-POLY`, using cofinitely many all-active prime evaluations. U22 instead assumes one specially supplied all-active/evaluable pool and omits `(iv)-POLY`. Although one nonzero evaluation is algebraically sufficient, it is a different and stronger input package than the quoted display.

15. **CRITICAL — U24’s principal hypothesis is malformed and nearly assumes RS.1-DEEP.**

    Offending field and unit:

    > `recursion : ∀ e ≤ n, ∀ σ' ∈ T.SigSet, ∀ hβ, βfam e σ' = ... bSplit ... hβ ...`

    > **U24** `βfam B e σ' = (1 - Kmat T e)⁻¹ *ᵥ ...`

    Quantifying over every arbitrary `hβ` says the same measured β solves recursions with every possible smaller-block family. That is stronger than and generally incompatible with the note. Moreover `βfam` and `βlt-of βfam` are not fields tying this family to the triangular `blockSolve`.

16. **CRITICAL — U25 assumes RS.1-SH verbatim instead of deriving it.**

    Offending field and unit:

    > `shallow_expansion : ∀ σ, R σ = ∑ Ŝ, Wsh Ŝ * shConv T Ŝ σ`

    > **U25** `theorem rs1_sh ... : B.R σ = Rsh T B σ`

    The note derives RS.1-SH from TREE-EXP, CUT-WD, SIB, PCI/REL.2, XRB, and the Wₛ machinery. The structure field is already the target equality, while all those hypotheses are `True`. Thus U25 is a definitional rewrite and remains provable when every open kernel is false.

17. **CRITICAL — U26 likewise assumes RS.1-MARKED verbatim.**

    Offending field and unit:

    > `marked_pairing : ... markedTotal e = MuHat.mk (T.ι e ⬝ᵥ solveVec T e)`

    > **U26** `(markedTotal B e).val = T.ι e ⬝ᵥ ((1-K)⁻¹ *ᵥ bAgg T e)`

    The note derives this using COMP-h, COMP-hΣ, HMC/COMP-Σ, ENT-AGG, COMP-AGG, and representative independence. Those hypotheses have no content here; the measured conclusion is simply installed as a structure field.

18. **CRITICAL — U28 assumes the primewise heart of RS.4.**

    Offending field and unit:

    > `primewise : { S // S.Infinite ∧ ∀ q₀ ∈ S, ... eval ... (∑ σ, R σ) = 1 }`

    > **U28** `theorem rs4 ... : ∑ σ, C.bundle.R σ = 1`

    The note obtains the primewise equality from X.3 plus RS.1 and ns-null, then invokes the rationality chain. Here `x3 : True` and the RS.1 tags provide no content, while `primewise` directly assumes the required evaluated checksum. U28 formalizes only the final elementary RatFunc lemma, not RS.4 under the displayed inherited set.

19. **CRITICAL — the hypothesis structures have no inhabitation/nondegeneracy story.**

    Offending specs include:

    > `State : ℕ → Type` with only `Fintype (State e)`  
    > `Out : ∀ e, State e → Type` with only `Fintype (Out e τ)`  
    > `SplitTy : Type; finS : Fintype SplitTy`  
    > `Shape : Type; finSh : Fintype Shape`  
    > `Act : Finset (T.State e)`  
    > `RegP ... := ∀ ... δ ∈ Δ, Nonempty (PoolHyp ...)`

    `State e`, outcome rosters, splitting types, shapes, active sets, and `Δ` may all be empty. In particular, `RegP` is automatically true when `Δ = ∅`, despite the note requiring δ = 1 and every consumed base-change index. `LedgerIV.part1` is vacuous when `State e` is empty. No explicit instance unit connects these bundles to realized CTS blocks. This is precisely the prohibited degenerate-instance loophole.

20. **GAP — U10 is not a plausible Lean statement as written.**

    Offending unit:

    > **U10** `P.A ⟨τ,_⟩ ⟨β,_⟩`  
    > `hTG : ∀ o, 0 ≤ evalAt q₀ (T.TG e τ o)`

    There is no hypothesis `τ ∈ P.Act`; the quantified β likewise has no membership proof. Also `evalAt` accepts an element of `OKat q₀`, but `T.TG` and `T.J` have type `Qq`, with no denominator-nonvanishing witnesses. The evaluated exit sums needed to drop nonnegative terms are underspecified.

21. **GAP — U20’s `moves_ref` does not describe its statement.**

    Offending unit:

    > **U20** `evalAt q₀ M.det = (M.map (evalAt q₀)).det`

    Its quoted reference is the active-value-agreement requirement:

    > “the evaluated object's q₀-value … equals the active-subsystem solve there”

    Determinant naturality is useful infrastructure, but it is not that display. The blueprint needs a precise Defs/dependency reference for this helper rather than attributing a different mathematical claim to it.

22. **GAP — three “hard” units hide substantial multi-lemma developments.**

    Offending units:

    > **U16** `blockSolve`  
    > **U21** `e0_det_ne_zero`  
    > **U23** `e0_inv_nonneg`

    U16 combines dependent strong recursion, construction and typing of `bSplit`, substitution, and the per-block inverse solve. U21 needs a singular-kernel witness, preservation under powers, entrywise absolute-value bounds, and a finite sup-norm limit argument. U23 needs finite Neumann identities, positivity of powers and partial sums, decay of the matrix remainder, and order-closedness of limits. These sketches require several internal lemmas and do not satisfy the stated one-short-display/one-short-unit decomposition.

Counts: **19 CRITICAL / 3 GAP**

**REJECT (19 crit / 3 gap)**
