# MovesS blueprint RE-AUDIT (Codex) — REV 2, 2026-07-28

Date run: 2026-07-27. Re-audit of rev 2 (22 rev-1 findings repaired, per §6 of the blueprint). Prompt = CAMPAIGN_AUDIT_CHARGE_2026-07-28.md (charge body, <CORPUS>→MovesS, <NOTE>→§S-RESUM) + re-audit-of-rev-2 addendum + MOVES_2026-07-24.md lines 11557–12431 (frozen §S-RESUM note, rev 6) + MOVESS_LEAN_BLUEPRINT_2026-07-28.md (full, 870 lines).

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa3d9-aa99-7833-97af-8d96fa0b6492
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

This is a RE-AUDIT of rev 2. The rev-1 findings (22, listed in the blueprint's
findings→repairs table §6) were repaired. Verify each repair is genuine AND sweep the
whole blueprint fresh — new defects introduced by the repairs count fully. Explicit
wave-4 deferrals (pinned sync statements W-1/W-1m etc.) are ACCEPTABLE design; a
deferral is a defect only if it mislabels a derivation the note actually performs
in-section.

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


THE BLUEPRINT UNDER RE-AUDIT (REV 2):

# MOVES §S-RESUM — Lean formalization blueprint (corpus MovesS) — REV 2 (post-Codex-audit, 22 findings repaired)

*REV 2, 2026-07-27. Round-1 text RETIRED (do not fan out from it). The Codex audit
`lean/notes/MOVESS_AUDIT_CODEX_2026-07-28.md` returned REJECT (19 crit / 3 gap); every
finding is repaired here in one batch; the findings→repairs table is §6. Source of truth
unchanged: the DUAL-ACCEPTED **§S-RESUM rev 6** of `lean/notes/MOVES_2026-07-24.md`
(lines ~11557–12430). Protocol-L; parent-CLAUDE.md discipline: NO new axioms,
statement-fence, every structure a flagged trust boundary (§4).*

## H. HEADER — the REV-2 design rulings

**R1 — NO `True`-typed hypothesis fields, anywhere** (findings 1, 3, 19). Every hypothesis
field states the note's actual condition as a contentful Prop over the structure's OWN
data. Where the condition's native vocabulary lives upstream (MovesV tables, MovesT trees,
[2b] height domains), the structure gains the **minimal abstract carriers needed to STATE
it** — the MovesD `PrefFamily` precedent (jet/enc/hist_inj as real fields with declared
owners). Concretely: a `MeasuredSide` interface (pool-indexed cell masses, height domains,
representatives, entrance shapes, k-step masses) over which all NINE CL-5 ledger items are
real Props (§2.B), and a `RatBurdens` structure in which every ℚ(q) table entry is DATA
**plus an interpolation law tying it to the measured per-pool values** — rationality is a
hypothesis package, never a bare field type (finding 3).

**R2 — NO assumed conclusions** (findings 4, 5, 8, 15, 16, 17, 18). A unit advertised as
deriving X takes the note's actual INPUTS. Where the derivation genuinely needs wave-4
vocabulary (TREE-EXP, CUT-WD, COMP-*), the unit moves to the explicit **WAVE-4 SYNC LIST**
(§3w) with its statement PINNED as a named Prop definition — a declared deferral, not a
fake derivation. Wave-2 keeps only what §S-RESUM itself marks DERIVED: the dispatch,
(K-TRI), the (SCS) chain from SP.1/stage-law carriers, (K-SUB) from PART-1's cell
partition, the solve, the E0 consequences, the evaluation/infinitude machinery, RS.1-DEEP
from the measured fixpoint, RS.4's rational-identity step.

**R3 — XRB reverts to an open hypothesis exactly as the note has it** (finding 2). The
measured subtree values `βmeas` carry an entrance-height index; `(XRB)` is the named field
`xrb : ∀ h h', βmeas … h … = βmeas … h' …` (CL-9; the note proves it at S.1 under its
displayed set — that proof is measure-side, wave-4/sync). The height-free symbolic family
`βfam` is only usable GIVEN `xrb`. Nothing in MovesS admits height-free β when XRB fails.

**R4 — inhabitation stories** (finding 19). Every structure carries a design note naming
its intended real instance + owner (§2, per structure), `RegP` quantifies over the
DEFINED pool set `consumedPools` (never a free Δ), pool/prime sets carry infinitude
fields where the note's arguments need them, and the corpus ships a **non-vacuity gate
unit** `instance_n2` building the note's own displayed 1×1 n = 2 instance (W6 geometric
series, denominator q² + q + 1) through the full structure stack.

**R5 — edge fidelity** (findings 6, 9, 10, 11, 12): both halves of (BDY) (edge rule AND
node shadow + the mass-split lemma; the consumption duties named on the sync list);
base-change indices are `ℕ+` (δ = 0 excluded); every block quantifier is `e ∈ Icc 1 n`
(no invented e = 0); `bSplit` takes the `DegCons` proof that licenses its smaller-block
applications; (R_e-exact) is a Lean statement (U-17b), not a docstring.

**R6 — splits** (finding 22): the three round-1 hards each split into one-display units:
`blockSolve` → {bSplit_def, blockSolve, blockSolve_spec}; `e0_det_ne_zero` →
{pow_fixed_vector, mulVec_abs_bound, e0_det_ne_zero}; `e0_inv_nonneg` →
{neumann_partial, pow_entry_nonneg, pow_entry_tendsto, e0_inv_nonneg}.

Downstream-corpus statement (per the campaign charge): MovesV/MovesT objects enter ONLY
through the §2 hypothesis structures (`TableShape`, `MeasuredSide`, `LedgerIV`,
`RatBurdens`, `RS1Bundle`, `RS4Chain`) — self-contained now, instantiable at wave 4 by
substituting the real objects; each field's owner is declared at the field.

---

## 0. What §S-RESUM is (one paragraph)

The depth direction of the classifier tree, resummed: per block size 1 ≤ e ≤ n, the
linear system
> (R_e-lump)  β_e = K_e β_e + b_e^{term,fin} + b_e^split
over ℚ(q); the (m, c) CLASSIFICATION routes every roster outcome to exactly one of
{K_e column, terminal exit, split exit}; (K-TRI) makes the block family triangular in e;
(K-SUB) makes K_e's rows sub-stochastic given the (iv) ledger; the solve is
β_e = adj(I−K_e)b_e/det(I−K_e) (RS.2, fixed coefficients); solvability rides the open
kernel ESCAPE(E0) per pool q₀ = p^δ (RS.3); RS.1 ties the solve to the density
components R_σ (DEEP/SH/MARKED); RS.4 is the checksum Σ_σ R_σ = 1 via "a rational
function equal to 1 at infinitely many prime evaluations is identically 1".

---

## 1. Mathlib design (verified names; unchanged from round 1 except D6/D9)

**D1** ℚ(q) := `abbrev Qq := RatFunc ℚ`; field structure `RatFunc.instField`
(pinned mathlib, FieldTheory/RatFunc/Basic.lean:480).
**D2** One matrix per block e, one vector per (e, σ′): K_e is σ′-independent (S.0), so
the system per σ′ is `β = K.mulVec β + b` over `Matrix (State e) (State e) Qq`.
**D3** Solve API: `Matrix.isUnit_iff_isUnit_det` (NonsingularInverse.lean:127),
`Matrix.mul_nonsing_inv`/`nonsing_inv_mul` (:211/:217), `Matrix.inv_def` (:172),
`Matrix.cramer_eq_adjugate_mulVec` (Adjugate.lean:245), `Matrix.mul_adjugate`/
`adjugate_mul` (:264/:269), `Matrix.det_smul_inv_mulVec_eq_cramer` (:656).
**D4** Per-pool evaluation is PARTIAL: subring `OKat q₀` (denominator nonvanishing at
q₀) with `evalAt q₀ : OKat q₀ →+* ℚ`, hom laws from the hypothesis-carrying
`RatFunc.eval_add`/`eval_mul` (AsPolynomial.lean:184/:203) — exactly S.4's per-pool
discipline. Determinants commute with evaluation via `RingHom.map_det`.
**D5** Infinitude arguments through `Polynomial.eq_zero_of_infinite_isRoot`
(Roots.lean:145), packaged once as `ratfunc_eval_infinite`; serves the measured→symbolic
lifts (K-SUB, RS.1-DEEP), interpolant uniqueness, RS.3(ii), and RS.4.
**D6** Base change `powSubst (δ : ℕ+) : Qq →+* Qq` via `IsFractionRing.lift` over
`Polynomial.aeval (X^(δ:ℕ))` — **δ = 0 excluded by type** (finding 9); [2r] (e2)'s
δ-ABSOLUTE convention is the `Member.δ : ℕ+` field's docstring duty.
**D7** σ′ = literal `Multiset VType`; finiteness via the Finset field `SigSet` + the
covering field `sig_covers` (finding 7); convolution index
`{g : Fin m → Multiset V // ∑ j, g j = σ'}` gets a constructed `Fintype`.
**D8** μ̂-type fence: `MuHat` (one field, no `Add`, no coercion) — RS.1-MARKED's
"NEVER summed into R_σ" enforced by the elaborator.
**D9 (NEW)** Measured values live in `ℝ` (per-pool masses/densities), symbolic tables in
`Qq`; the two meet ONLY through interpolation fields `(↑(evalAt q₀ f) : ℝ) = val q₀`
quantified over the infinite pool set — the note's "one polynomial …, valued correctly
at every prime power" (S.3), stated as data + law, never as bare typing.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesS/Defs.lean`

### 2.A Combinatorial layer (owner MovesV/MovesSp rosters; instance story: V.6's n = 3
rosters — 677 shapes / 9,494 outcomes per the dual-acceptance census — and U-29's n = 2 gate)

```lean
import Mathlib
namespace LeanUrat.MovesS
open Matrix Polynomial

abbrev Qq := RatFunc ℚ

/-- An INDIVIDUATED outcome member ([3t] SIBLING INDEXING). `δ : ℕ+` — base-change
    index, ABSOLUTE per [2r] (e2); δ = 0 unrepresentable (audit finding 9). -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+
  status : V ⊕ State size          -- halted-with-verdict | continuing into a block state

def Member.continuing (μ : Member V State) : Prop := μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ := (o.mem.filter (·.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  (o.mem.filterMap (fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split deriving DecidableEq
/-- The (m, c) CLASSIFICATION (S.0 rev 6, a DISPLAYED DEFINITION the note adopts). -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

/-- HYPOTHESIS STRUCTURE (owner §V-TABLES/[2a]): block states + outcome rosters.
    COMBINATORIAL ONLY — no masses here (they live in MeasuredSide/RatBurdens). -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  Out    : ∀ e, State e → Type
  finO   : ∀ e τ, Fintype (Out e τ)
  odata  : ∀ e τ, Out e τ → Outcome VType State
  SigSet : Finset (Multiset VType)      -- the occurring σ′ ([2a] M1/M5 finiteness)
  sig_covers : ∀ e ∈ Finset.Icc 1 n, ∀ τ (o : Out e τ),          -- audit finding 7
    routeOf (odata e τ o) = .termFin → (odata e τ o).verdicts ∈ SigSet
attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finO
```

**(SCS) supply — REDESIGNED (findings 4, 5): the SP.1 member-typing carriers, so U-4
DERIVES flank-emptiness instead of assuming it.** Owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10
via SP.2 (B1)/(B3). Intended instance: the letter fields of the MovesSp catalogue.

```lean
/-- Per-outcome window/letter data for the (SCS) derivation. All fields are the note's
    cited displays, one each; NONE states (SCS) or flank-emptiness itself. -/
structure SCSData (T : TableShape n) where
  W D ℓ g μsel : ∀ e τ (o : T.Out e τ), ℕ          -- window, degree, read-side width,
                                                    -- selected residual factor (g, μ)
  ℓpos : ∀ e τ o, 1 ≤ ℓ e τ o
  flankCount : ∀ e τ (o : T.Out e τ), ℕ            -- # flank sides of the window
  flankWidth : ∀ e τ (o : T.Out e τ), ℕ            -- their total raw width
  window_comp : ∀ e τ o, W e τ o = e * ℓ e τ o + flankWidth e τ o
    -- SP.1: "the horizontal compositions of the window span outside the read side"
  flankWidth_pos : ∀ e τ o, 0 < flankCount e τ o → 0 < flankWidth e τ o
  resFactors : ∀ e τ (o : T.Out e τ), Finset (ℕ × ℕ)     -- the residual shape λ
  sel_mem : ∀ e τ o, (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e τ o, ∑ x ∈ resFactors e τ o, x.1 * x.2 = ℓ e τ o   -- "Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ"
  -- EACH flank side and EACH non-selected residual factor IS a member, distinct from
  -- the designated continuing member ("each side carrying ≥ 1 residual factor … = ≥ 1
  -- member"; "the non-selected part of λ is the residual co-factor"):
  memberOf : ∀ e τ o, Fin (flankCount e τ o) ⊕
    {x // x ∈ resFactors e τ o ∧ x ≠ (g e τ o, μsel e τ o)} →
    Fin (T.odata e τ o).mem.length
  memberOf_inj : ∀ e τ o, Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e τ o (hc : routeOf (T.odata e τ o) = .kcol ∨ True) i,
    (T.odata e τ o).mem.get (memberOf e τ o i) |>.continuing = False ∨
    memberOf e τ o i ≠ selIdx e τ o          -- distinct from the designated member
  selIdx : ∀ e τ o, Fin (T.odata e τ o).mem.length   -- the designated/walked member
  stage_D : ∀ e τ o, D' e τ o = e * g e τ o * D e τ o        -- (B1): D′ = e·g·D
  stage_W : ∀ e τ o, W' e τ o = μsel e τ o                    -- (B3): W′ = μ
  W' D' : ∀ e τ (o : T.Out e τ), ℕ
  cluster_parent : ∀ e τ o, W e τ o * D e τ o = e             -- cluster size IS W·D
  cluster_child : ∀ e τ o (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o
```

*(E-phase note: field order/grouping to be normalized so `W'`/`D'` precede their laws;
`memberOf_ne_sel` simplifies to `memberOf e τ o i ≠ selIdx e τ o` — the disjunct above
is a drafting artifact to strike at elaboration. The LOAD-BEARING content: injections
from flanks + non-selected factors into member positions AVOIDING the designated one,
so m = 1 pigeonholes both sources empty — the note's step (1) verbatim.)*

### 2.B The measured side + the NINE-input ledger (findings 1, 8, 19 repaired)

Owner: [1v] CTS-M / [2b] XHD / [5]. Intended instance: the CTS cell space with its
digit-cell partition and XHD height classes (MovesV wave 4); the per-pool masses are the
O_δ conditional masses. Every CL-5 item is now a REAL Prop over these carriers.

```lean
/-- The measured (per-pool) side of the tables. Values in ℝ; pools are the prime powers
    q₀ = p^δ the note evaluates at. -/
structure MeasuredSide (T : TableShape n) where
  Pools : Set ℚ
  pools_infinite : Pools.Infinite         -- S.3/S.4: "at every prime power"/"cofinitely
                                          -- many all-active primes" need infinitude
  Cell : ∀ e, T.State e → Type            -- the one-step digit CELLS at (e, τ) —
  finC : ∀ e τ, Fintype (Cell e τ)        --   PART-1's partition objects ([1v] V.3(iv))
  cellOut : ∀ e τ, Cell e τ → T.Out e τ   -- each cell belongs to ONE outcome class
  Rep : ∀ e, T.State e → Type             -- concrete states of the cell-class τ
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ, Nonempty (Rep e τ)   -- non-vacuity (finding 19)
  μcell : ∀ e τ, Rep e τ → Cell e τ → ℚ → ℝ  -- XHD-resummed conditional cell mass,
                                              --   per representative, per pool
  Hgt : Type                               -- height points ([2b] M4a-X)
  HDom : ∀ e τ, Cell e τ → Set Hgt         -- the EXACT per-cell height domain (XHD-d)
  gwt : ∀ e τ (c : Cell e τ), Hgt → ℚ → ℝ  -- XHD-w fixed-height weight g(h) at pool
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ  -- measured k-step in-block mass
  EntShape : ∀ e, T.State e → Type         -- entrance shapes ε into (e, β₀) (CTS-M(iii))
  finE : ∀ e τ, Fintype (EntShape e τ)     -- finite family (ENT-COUNT's roster)
  hent : ∀ e τ, EntShape e τ → ℕ           -- the retained h_ent(ε)
  ιshH : ∀ e τ, EntShape e τ → Hgt → ℚ → ℝ -- FIXED-HEIGHT per-shape marked mass
                                            --   ((COMP-h)'s object: the monomial-g
                                            --   level, initial factor included)
  ιDom : ∀ e τ, EntShape e τ → Set Hgt     -- the shape's exact entrance-height classes
  ιsh : ∀ e τ, EntShape e τ → ℚ → ℝ        -- per-shape POST-SPLIT marked mass ι_{e,ε,β₀}
  ιval : ∀ e, T.State e → ℚ → ℝ            -- the ENT-AGG aggregate ι_e, per pool

/-- CL-5, the NINE-input conditionality ledger — every item a contentful Prop over
    MeasuredSide's carriers (audit finding 1). Owners as displayed at S.0. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  xhd_sum : ∀ e τ x c q₀, q₀ ∈ M.Pools →                        -- (1) XHD [2b]
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
    -- resummed cell mass = the sum of XHD-w weights over the EXACT domain
    -- ("else resummed rows sum masses of non-events")
  d4r0 : ∀ e τ c c', c ≠ c' → Disjoint (M.HDom e τ c) (M.HDom e τ c')   -- (2) D4R.0:
    -- disjointness after height grouping, per listed pairwise-disjoint component
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ τ x q₀, q₀ ∈ M.Pools →        -- (3) (iv)-PART-1 [1v]
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
    -- the digit-cell partition identity, per representative, countable across heights
  rep_indep : ∀ e τ (x y : M.Rep e τ), M.μcell e τ x = M.μcell e τ y   -- (4) (iv)-REP =
    -- M2(ii), weighted representative independence (probe: STATE-probe-2, BLOCKING)
  meas_nonneg : ∀ e τ x c q₀, 0 ≤ M.μcell e τ x c q₀              -- (5) (iv)-MEAS shadow:
    -- masses of events are nonnegative (the disjoint-measurability face rides (2)+(3))
  hmc : ∀ k e τ β q₀, q₀ ∈ M.Pools →                              -- (6) CTS-M(v) HMC
    M.kstep (k+1) e τ β q₀ = ∑ γ, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
    -- the k-step masses FACTOR through one-step (the whole-template height domains
    -- factor) — OPEN kernel; consumed by every K_e-power claim
  act : ∀ e τ x c q₀, q₀ ∈ M.Pools →                              -- (7) CTS-M(ii) ACT
    (∀ h ∈ M.HDom e τ c, M.gwt e τ c h q₀ = 0) → M.μcell e τ x c q₀ = 0
    -- empty-at-q₀ cells carry no mass (wild-p emptiness = weight vanishing)
  init_agg : ∀ e τ q₀, q₀ ∈ M.Pools →                             -- (8) CTS-M(iii)
    M.ιval e τ q₀ = ∑ ε : M.EntShape e τ, M.ιsh e τ ε q₀          --   INIT/ENT-AGG
    -- entrance heights are summed HERE and nowhere else (h_ent rides in ε alone)
  comp_once : ∀ e τ ε q₀, q₀ ∈ M.Pools →                          -- (9) COMP-TYPING:
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)
    -- heights summed EXACTLY ONCE: the resummed per-shape mass ιsh is THE height sum
    -- of the fixed-height (COMP-h) family over the shape's exact classes ((COMP-hΣ));
    -- the aggregate ιval (item 8) sums SHAPES, never heights again ((COMP-Σ)'s
    -- once-only discipline is structural: no other field of MeasuredSide takes a
    -- height sum — the only Hgt-summations in this corpus are xhd_sum and comp_once)
```

*(Design note for the re-audit: items (1)–(9) map 1:1 onto S.0's displayed ledger; each
is a Prop over MeasuredSide's own carriers with the owner at the field. Items (2)/(5):
D4R.0's disjointness is stated on the per-cell height domains (the note's "after height
grouping" per listed component) and MEAS's face here is nonnegativity + the partition
identity — the full measurable-disjointness statement needs [1v]'s event space and is a
recorded sync-list deliverable (§3w item W-9), not a silent drop.)*

### 2.C Rationality burdens, the kernel/exit objects, pools/E0/(REG-p)

```lean
/-- The evaluation locus and partial evaluation (D4). -/
def OKat (q₀ : ℚ) : Subring Qq := sorry            -- {f // f.denom.eval q₀ ≠ 0}; U-19
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ := sorry                       -- U-19

/-- THE RATIONALITY BURDENS (finding 3 repaired): the ℚ(q) tables are DATA + the
    interpolation LAW tying them to the measured per-pool values. Owners: CTS-M
    (iv)-POLY = CL-6 [1v]; XHD-s [2b]; INIT-RAT [1v]; (J-RAT) [1v]/[2b]. Intended
    instance: the computed [1v] blocks (V.6 rosters). A `RatBurdens` cannot exist
    unless the note's rationality claims actually hold of the measured side. -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  TG : ∀ e τ, T.Out e τ → Qq          -- the resummed one-step T·G per NON-split outcome
  J  : ∀ e τ, T.Out e τ → Qq          -- the CELL-LEVEL branching mass per split outcome
  ι  : ∀ e, T.State e → Qq            -- the ENT-AGG entrance vector
  tg_ok : ∀ e τ o q₀, q₀ ∈ M.Pools → TG e τ o ∈ OKat q₀            -- (iv)-POLY/XHD-s:
  tg_interp : ∀ e τ (x : M.Rep e τ) o q₀ (h : q₀ ∈ M.Pools),       -- valued correctly
    routeOf (T.odata e τ o) ≠ .split →                             -- at every pool
    (evalAt q₀ ⟨TG e τ o, tg_ok e τ o q₀ h⟩ : ℝ) =
      ∑ c ∈ {c : M.Cell e τ | M.cellOut e τ c = o}.toFinset, M.μcell e τ x c q₀
    -- kcol/term outcomes: T·G is the outcome's cell mass (each cell once — the
    -- (c=1,m=1)/(c=0) rows; NO source-mass division anywhere)
  j_ok : ∀ e τ o q₀, q₀ ∈ M.Pools → J e τ o ∈ OKat q₀              -- (J-RAT), OPEN:
  j_interp : ∀ e τ (x : M.Rep e τ) o q₀ (h : q₀ ∈ M.Pools),        -- per-cell rational
    routeOf (T.odata e τ o) = .split →                             -- tables
    (evalAt q₀ ⟨J e τ o, j_ok e τ o q₀ h⟩ : ℝ) =
      ∑ c ∈ {c : M.Cell e τ | M.cellOut e τ c = o}.toFinset, M.μcell e τ x c q₀
    -- J = the branching-cell mass, EACH CELL ONCE — NEVER the marked per-branch T·G
  ι_ok : ∀ e τ q₀, q₀ ∈ M.Pools → ι e τ ∈ OKat q₀                  -- INIT-RAT (cited
  ι_interp : ∀ e τ q₀ (h : q₀ ∈ M.Pools),                          -- burden, [1v])
    (evalAt q₀ ⟨ι e τ, ι_ok e τ q₀ h⟩ : ℝ) = M.ιval e τ q₀
  allActive : Set ℚ                    -- S.4(ii)'s all-active pools: "cofinitely many —
  allActive_sub : allActive ⊆ M.Pools  -- only finitely many primes are roots of some
  allActive_infinite : allActive.Infinite   -- not-identically-zero cell-size polynomial"

/-- K_e (S.0 display): entries sum T·G over (c = 1, m = 1)-routed outcomes landing in β.
    `hK` is the (SCS) conclusion AS AN ARGUMENT (finding 4: no structure field; U-6
    derives it from SCSData + DegCons, and every consumer instantiates it that way). -/
def kTarget (T : TableShape n) (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e := sorry  -- U-16a region:
    -- the unique continuing member's state, cast along hK (m = 1 from hk)
def Kmat (T) (RB : RatBurdens T M) (e : ℕ)
    (hK : ∀ τ o hk, ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) :
    Matrix (T.State e) (T.State e) Qq := sorry     -- Σ over kcol outcomes with target β
def bTerm (T) (RB : RatBurdens T M) (e : ℕ) (σ' : Multiset T.VType) :
    T.State e → Qq := sorry                        -- Σ over termFin outcomes, v(o) = σ'
-- bSplit is a UNIT-level definition (U-16a): it needs (K-TRI) to license its
-- smaller-block applications (finding 10) and so takes `hdc : DegCons T`.

/-- DEG-CONS (CL-11, [1v]): per member over the FULL roster, halted members included. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e τ (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ τ (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-- ESCAPE(E0) (OPEN KERNEL, CL-1, owner THIS note; per-pool, rev-3 widened form).
    NEVER proved in MovesS; U-21*/U-23* are its displayed "hence" consequences. -/
structure EscapeE0 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ))) Filter.atTop (nhds 0)

/-- Per-pool package (S.4). Intended instance: the CTS-M(ii) active submatrix at q₀. -/
structure PoolHyp (T) (RB : RatBurdens T M) (e : ℕ) (hK) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok _ _ τ.2 β.2⟩
  inactive_vanish : ∀ τ β (h : τ ∈ Act) (hβ : β ∉ Act)
    (hok : Kmat T RB e hK τ β ∈ OKat q₀), evalAt q₀ ⟨_, hok⟩ = 0
  e0 : EscapeE0 A

/-- CTS-M(ii-c)'s ACTIVE-VALUE AGREEMENT (weakened REV-7 form), PER POOL — a NAMED Prop
    consumers must cite before reading a value off at q₀ (the note: "must pass BEFORE it
    may be read off; a pole SURVIVING cancellation at a wild pool is (ii-c)'s FAIL").
    NOT a PoolHyp field: it is a per-object read-off gate, quantified at each consumer. -/
def AVAgree (P : PoolHyp T RB e hK q₀) (v : Qq) (bA : P.Act → ℚ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, evalAt q₀ ⟨v, hok⟩ = ((1 - P.A)⁻¹ *ᵥ bA) τ
  -- "the evaluated object's q₀-value (after cancellation where needed — membership in
  -- OKat is post-cancellation by RatFunc's reduced num/denom) equals the
  -- active-subsystem solve there"; junk-block determinants are census-side (S.7),
  -- recorded not required nonzero — no det(1 − D_{q₀}) ≠ 0 Prop exists here.

/-- The RELEVANT POOLS are COMPUTED from the roster, never a free parameter
    (finding 19): δ = 1 AND every base-change index a split leg or shallow leg consumes. -/
def consumedDeltas (T : TableShape n) (Sh : ShapeFam T) : Finset ℕ+ := sorry
  -- {1} ∪ split-leg δ's (U-16a) ∪ shape-leg δ's (U-18); ShapeFam is §2.D (forward ref,
  -- E-phase ordering)
def RegP (T) (RB) (p : ℕ) (hK) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ δ ∈ consumedDeltas T _, Nonempty (PoolHyp T RB e hK ((p:ℚ)^(δ:ℕ)))
```

### 2.D (BDY), shapes, the RS.1/RS.4 interfaces (findings 2, 6, 13, 15–18 repaired)

```lean
structure MuHat where val : Qq              -- μ̂-type fence (D8): no Add, no coercion

/-- (BDY), BOTH halves (finding 6): edge rule AND node shadow, on the abstract path
    model (reads/edges indexed 0..L, `fe` = the first-entrance edge index). -/
inductive ReadOwner | entrance | block deriving DecidableEq
def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance
-- node ν_fe is BLOCK-side (a STATE INDEX) while the edge INTO it is entrance-side MASS.

/-- Shallow tree shapes Ŝ — length-matched RECORD (finding 13: no independent lists). -/
structure Shape (T : TableShape n) where
  k    : ℕ                                   -- # block entrances
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)        -- the landed states (BDY: the entrance
  δOf  : Fin k → ℕ+                          --   node's index); the δ-legs, ABSOLUTE
  σ0   : Multiset T.VType                    -- verdicts of the shallow τ-halted leaves
structure ShapeFam (T : TableShape n) where  -- owner [2a] (finiteness) + [3t] (CUT-3)
  Sh : Finset (Shape T)                      -- the finite-up-to-heights family
  -- intended instance: CUT-3's choice-free image {Ŝ(T)}; the (BDY)-inclusive reads
  -- and every shallow τ-halt are part of Shape's intended semantics (§3w W-7/W-8)

/-- RS.1's interface (findings 2, 15, 16, 17): the MEASURED objects with height index,
    XRB as the OPEN field, the measured fixpoint as the wave-4-dischargeable input —
    the symbolic identities are DERIVED (U-24a/b), never fields. -/
structure RS1Bundle (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK) where
  βmeas : ∀ e ∈ Finset.Icc 1 n, ∀ (h_ent : ℕ) (τ : T.State e),
    Multiset T.VType → ℚ → ℝ               -- the measured conditional subtree value,
                                            -- ENTRANCE-HEIGHT-INDEXED (owner [3t])
  xrb : ∀ e he h h' τ σ', βmeas e he h τ σ' = βmeas e he h' τ σ'   -- (XRB), CL-9 —
    -- OPEN HERE (finding 2): the note proves it at S.1 GIVEN XHD+(JC-INV)+(SIB)/
    -- (JC-multi)+TB-CAP/VP+REL.2(a)(b)(d)+(ns-null); that derivation is measure-side
    -- (§3w W-2). MovesS consumes it only through this displayed field.
  βfam : ∀ e ∈ Finset.Icc 1 n, T.State e → Multiset T.VType → Qq   -- the symbolic family
  β_ok : ∀ e he τ σ' q₀, q₀ ∈ M.Pools → βfam e he τ σ' ∈ OKat q₀
  β_interp : ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools) (h_ent : ℕ),        -- interpolation: the
    (evalAt q₀ ⟨βfam e he τ σ', β_ok e he τ σ' q₀ h⟩ : ℝ)          -- symbolic β values
      = βmeas e he h_ent τ σ' q₀                                   -- the measured ones
  recursion_meas : ∀ e he τ σ' (hσ : σ' ∈ T.SigSet) q₀ (h : q₀ ∈ M.Pools) h_ent,
    βmeas e he h_ent τ σ' q₀ = evalRe T RB e hK τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
    -- the MEASURED (R_e-lump) fixpoint at every pool: `evalRe` (U-16a region) is the
    -- evaluated right side K·β + bTerm + bSplit with the split legs read from the SAME
    -- family at δ-shifted pools ([2r] (e2)) — smaller blocks only, licensed by (K-TRI).
    -- WAVE-4 DISCHARGE: TREE-EXP + TREE-N + ONE-F + (SIB)/CL-10 + PCI = REL.2(a)(b)(d)
    -- + CTS-M(iv)-REP + XRB (§3w W-3). This is the note's input, NOT its conclusion:
    -- RS.1-DEEP's identity β = (I−K)⁻¹b is DERIVED from it at U-24a/b.
  βfull : ∀ e ∈ Finset.Icc 1 n, ∀ h_ent (τ : T.State e), Multiset T.VType → ℚ → ℝ
  nsNull : Prop                              -- the (ns-null) tag ([3t] §T.2, CLOSED there;
  rexact : nsNull → ∀ e he h_ent τ σ' q₀,    --   discharged at wave 4 by [3t]'s closure)
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀     -- (R_e-exact), GIVEN (ns-null)

/-- RS.4's inherited chain (finding 18): the note's TWO named primewise inputs, each
    with its owner — never a fused "eval = 1" oracle. -/
structure RS4Chain (T M RB hdc hK) (B : RS1Bundle T M RB hdc hK) (F : ShapeFam T) where
  Wsh : Shape T → Qq                          -- W_Ŝ; production = CL-17(ii), OPEN —
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, Wsh Ŝ ∈ OKat q₀          -- its ℚ(q) membership
  R : SplitTy → Qq                            -- the density components (RS.1-SH's target)
  SplitTy : Type ; finS : Fintype SplitTy
  Rval : SplitTy → ℚ → ℝ                      -- measured densities at pools (owner [3t])
  r_ok : ∀ σ q₀, q₀ ∈ M.Pools → R σ ∈ OKat q₀
  r_interp : ∀ σ q₀ (h : q₀ ∈ M.Pools), (evalAt q₀ ⟨R σ, r_ok σ q₀ h⟩ : ℝ) = Rval σ q₀
  PrimePools : Set ℚ                          -- the evaluation primes (δ = 1 pools)
  prime_sub : PrimePools ⊆ M.Pools ; prime_infinite : PrimePools.Infinite
  decidedTotal : ℚ → ℝ                        -- the primewise decided-mass series total
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1     -- X.3's density form — CL-4, OPEN,
    -- owner [5] §X-EXHAUST (conditional there per its record line); (ns) residual 0
    -- GIVEN (ns-null); wave-4 discharge W-4
  rs1_total : ∀ p ∈ PrimePools, (∑ σ, Rval σ p) = decidedTotal p  -- "RS.1 equates that
    -- series with Σ_σ R_σ(p)" — provenance: RS.1-SH + ONE-F (its own derivation is the
    -- deferred W-1); stated on the MEASURED side, owner [3t]/THIS note's S.2
```

*(Field-order/universe plumbing (`SplitTy` before its uses, `M` binders) is E-phase
normalization; the trust surface is the field LIST above.)*

---

## 3. The unit DAG — REV 2: 38 units (12 easy / 25 medium / 1 hard)

Format per campaign §2; one file `MovesS/<Id>.lean` per unit. All block quantifiers
`e ∈ Finset.Icc 1 n` (finding 11).

### Layer S0 — dispatch, arithmetic, (SCS), (BDY) [7]

**U-1 `MovesS.dispatch_spec` · Dispatch.lean · easy** — as round 1 (audit-clean):
`(routeOf o = .termFin ↔ o.c = 0) ∧ (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧
(routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m)` given `1 ≤ o.m`, `o.c ≤ o.m`.
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION: the three predicates partition
{(m, c) : m ≥ 1, 0 ≤ c ≤ m}". deps: Defs · hyp: none · sketch: unfold + omega.

**U-2 `MovesS.ktri` · KTri.lean · easy** — as round 1: DegCons + `2 ≤ m` ⟹
`∀ μ ∈ mem, μ.size < e` (for `e ∈ Icc 1 n`). moves_ref: "at m ≥ 2 EVERY e_j < e".
deps: Defs · hyp: DegCons (CL-11) · sketch: sum bound + omega.

**U-3 `MovesS.kcol_agree` · KColAgree.lean · easy** — as round 1: a continuing block-e
member forces m = 1 (agreement check (ii)). deps: U-2 · hyp: DegCons.

**U-4 `MovesS.scs_flank` · ScsFlank.lean · medium — REDESIGNED (findings 4, 5).**
`statement`: `theorem scs_flank (T) (S : SCSData T) {e τ o} (hm : (T.odata e τ o).m = 1) :`
`S.flankCount e τ o = 0 ∧ S.resFactors e τ o = {(S.g e τ o, S.μsel e τ o)} ∧`
`S.W e τ o = e * S.ℓ e τ o ∧ S.g e τ o * S.μsel e τ o = S.ℓ e τ o`
moves_ref: "m = 1 forces NO flank side (the read side spans the window: e·ℓ = W) and a
SINGLETON residual shape λ = {(g, μ)}, i.e. g·μ = ℓ."
deps: Defs · hyp: SCSData's SP.1 carriers (memberOf/memberOf_inj/≠ selIdx, window_comp,
res_sum — owner [2a] SP.1) · sketch: m = 1 ⟹ Fin 1 member positions; `memberOf` avoids
`selIdx` injectively, so its domain is empty: flankCount = 0 and non-selected residual
factors = ∅, i.e. λ = {(g, μsel)}; `window_comp` + `flankWidth_pos` give W = e·ℓ;
`res_sum` on the singleton gives g·μ = ℓ. GENUINE pigeonhole derivation, no assumed
conclusion.

**U-5 `MovesS.scs_stage` · ScsStage.lean · easy** — `W' * D' = W * D` at m = 1 from
stage_D/stage_W + U-4. moves_ref: "W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D".
deps: U-4 · hyp: SCSData stage laws (§B2-DEF D.5/D.8/D.10 via [2a] SP.2 (B1)/(B3)).

**U-6 `MovesS.scs` · Scs.lean · medium** — `statement`:
`theorem scs (T) (S : SCSData T) (hdc : DegCons T) (e) (he : e ∈ Finset.Icc 1 n) τ o`
`(hk : routeOf (T.odata e τ o) = .kcol) : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e`
moves_ref: "(SCS) a (c = 1, m = 1) outcome's single child inherits the block size:
e₁ = e". deps: U-1, U-4, U-5 · hyp: SCSData.cluster_parent/cluster_child · sketch:
hk ⟹ m = 1 (U-1); the single member is selIdx and continuing; cluster_child +
U-5 + cluster_parent: size = W′D′ = WD = e. **PRODUCES the `hK` argument every
`Kmat`/`PoolHyp`/solve consumer takes — no structure field assumes it (finding 4).**

**U-7 `MovesS.bdy` · Bdy.lean · medium — EXPANDED (finding 6).** Three statements:
`bdy_edge_partition : ∀ fe r, (bdyEdgeOwner fe r = .entrance ↔ r ≤ fe) ∧
(bdyEdgeOwner fe r = .block ↔ fe < r)`; `bdy_node_shadow : ∀ fe,
bdyNodeOwner fe fe = .block ∧ bdyEdgeOwner fe fe = .entrance ∧
∀ r ≠ fe, bdyNodeOwner fe r = bdyEdgeOwner fe r`; `bdy_mass_split : ∀ (μm : ℕ → ℝ) L fe,
fe ≤ L → ∑ r ∈ Finset.range (L+1), μm r = (∑ r ∈ Finset.Icc 0 fe, μm r) +
(∑ r ∈ Finset.Icc (fe+1) L, μm r)` — no read omitted, none double-charged.
moves_ref: "the first entrance node ν is BLOCK-side as a STATE INDEX …, while the edge
INTO ν is entrance-side MASS — no read omitted, none double-charged."
deps: Defs · hyp: none · sketch: split_ifs/omega; Finset.sum split. The CONSUMPTION
duties (ι owns the ε-prefix with retained h_ent; W_Ŝ inclusive; β charges nothing for
the entering read) are §3w W-8 — named, owned, not silently dropped.

### Layer S1 — (K-SUB) [4]

**U-8 `MovesS.ksub_regroup` · KSubRegroup.lean · medium** — `statement` (per e ∈ Icc 1 n,
τ, with hK from U-6): `(∑ β, Kmat T RB e hK τ β) + (∑ σ' ∈ T.SigSet, bTerm T RB e σ' τ) +`
`(∑ o ∈ splitOuts T e τ, RB.J e τ o) = ∑ o : T.Out e τ, routedMass RB e τ o` where
`routedMass := if routeOf = .split then J else TG`.
moves_ref: "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′} b_e^{term,fin}(τ)(σ′) + (branching-cell
one-step mass, per cell once) = 1, the third summand being exactly Σ_o J_{τ,o}".
deps: U-1, U-6 · hyp: `T.sig_covers` (now a REAL field — finding 7) · sketch: partition
the roster by routeOf (U-1); regroup kcol terms by kTarget and termFin terms by
verdicts (`Finset.sum_fiberwise_of_maps_to`; sig_covers makes the σ'-sum exhaustive).

**U-9a `MovesS.ksub_eval` · KSubEval.lean · medium** — per pool: `∀ q₀ ∈ M.Pools, ∀ x,`
`(evaluated LHS of U-8's right side) = 1`. moves_ref: "PART-1 (the digit-cell partition
identity, per representative, countable across heights) gives (K-SUB)".
deps: U-8, U-19 · hyp: LedgerIV.part1 + RB.tg_interp/j_interp (the TG-vs-J cell
identifications — the routing derivation the audit demanded, finding 8) · sketch:
evaluate routedMass o via interp = Σ of o's cell masses; `Finset.sum_fiberwise` over
cellOut collapses Σ_o Σ_{cells of o} to Σ_cells; part1 closes at 1.

**U-9b `MovesS.ksub` · KSub.lean · medium** — the SYMBOLIC identity: U-8's left side
`= 1` in Qq. deps: U-8, U-9a, U-27 · hyp: as U-9a + M.pools_infinite · sketch: the
difference vanishes at every pool (U-9a); infinitude (U-27) kills it. (K-SUB)'s
conditionality bracket (iv)-ledger + DEG-CONS + (m,c) + (SCS) is now the LITERAL
hypothesis trace: LedgerIV + DegCons + routeOf + U-6.

**U-10 `MovesS.ksub_pool` · KSubPool.lean · medium — RESTATED (finding 20).**
`statement`: `theorem ksub_pool (P : PoolHyp T RB e hK q₀) (L : LedgerIV T M)`
`(hTG : ∀ o, ∃ h : RB.TG e τ o ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨_, h⟩)`
`(hJ : ∀ o, ∃ h : RB.J e τ o ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨_, h⟩)`
`(τA : P.Act) : (∀ βA : P.Act, 0 ≤ P.A τA βA) ∧ (∑ βA : P.Act, P.A τA βA) ≤ 1`
moves_ref: "K_e's rows are genuine sub-distributions … every summand ≥ 0".
deps: U-9a, U-19 · hyp: PoolHyp memberships explicit; nonneg evaluations supplied by
meas_nonneg + interp (a derivable lemma, folded here) · sketch: evaluate U-9a at q₀,
drop the two nonneg exit sums, restrict to Act via inactive_vanish.

### Layer S2 — the ℚ(q) system and its solve [11]

**U-11 `MovesS.decompFintype` · Decomp.lean · medium** — as round 1:
`instance : Fintype {g : Fin m → Multiset V // ∑ j, g j = σ'}` (DecidableEq V).
moves_ref: "the MULTISET CONVOLUTION over children's types". sketch: induct on m via
sub-multiset finiteness.

**U-12 `MovesS.powSubst` · PowSubst.lean · medium — δ = 0 EXCLUDED (finding 9).**
`noncomputable def powSubst (δ : ℕ+) : Qq →+* Qq` + `powSubst_X : powSubst δ X = X^(δ:ℕ)`
+ `powSubst_C`. moves_ref: "composed with q ↦ q^{δ_j} (which maps ℚ(q) → ℚ(q)); the
ARGUMENT convention is [2r] (e2) (δ absolute)". sketch: `IsFractionRing.lift` over
`aeval (X^(δ:ℕ))`; nonzero polys map to nonzero since δ ≥ 1 (degree scales by δ).

**U-13 `MovesS.solve_iff` · SolveIff.lean · easy** — as round 1:
`β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b`. moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{…}".

**U-14 `MovesS.solve_exists_unique` · SolveEU.lean · medium** — as round 1: `hdet ⟹
∃! β, β = K *ᵥ β + b`, witness `(1-K)⁻¹ *ᵥ b`. deps: U-13 · Mathlib:
`isUnit_iff_ne_zero`, `Matrix.isUnit_iff_isUnit_det`, `mul_nonsing_inv`/`nonsing_inv_mul`.

**U-15 `MovesS.solve_cramer` · SolveCramer.lean · medium** — as round 1 (adjugate/Cramer
entrywise form). moves_ref: "β_e = adj(I − K_e) b_e / det(I − K_e) entrywise". RS.2's
conditionality is now REAL (finding 3): `Kmat`/`bTerm`/`bSplit` exist only over a
`RatBurdens`, so "fixed coefficients in ℚ(q)" is exactly "GIVEN the cited rationality
burdens (each named)" — the burdens carry (iv)-POLY/XHD-s/INIT-RAT/(J-RAT) as
interpolation laws, and p enters only at `evalAt` (p-INDEPENDENCE, docstring duty).

**U-16a `MovesS.bSplit_def` · BSplitDef.lean · medium — NEW (findings 10, 22).**
`noncomputable def bSplit (T RB) (hdc : DegCons T) (e) (he : e ∈ Finset.Icc 1 n)`
`(βlt : ∀ e' ∈ Finset.Icc 1 (e-1), T.State e' → Multiset T.VType → Qq)`
`(σ' : Multiset T.VType) : T.State e → Qq` — per split outcome o:
`RB.J e τ o * ∑ g : decomps σ' o.m, ∏ j, legFactor j` where a halted member's factor is
`if σ_j = {verdict} then 1 else 0` (§T.4 leaf convention) and a continuing member μ's is
`powSubst μ.δ (βlt μ.size ⟨by exact ktri-bound⟩ (state of μ) σ_j)` — the βlt application
LICENSED INSIDE the definition by U-2's (K-TRI) bound (route = split ⟹ m ≥ 2 ⟹
μ.size < e, and μ.size ≥ 1 by DegCons). Also defines `evalRe` (the evaluated (R_e) right
side RS1Bundle.recursion_meas cites) and `consumedDeltas` (the δ's of all split legs ∪
shape legs ∪ {1}). moves_ref: "b_e^split(τ)(σ′) := Σ_{o branching} J_{τ,o}(q) ·
Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m β_{e_j,τ_j(o)}(σ_j)(q^{δ_j})".
deps: U-1, U-2, U-11, U-12 · hyp: DegCons — now an ARGUMENT of the definition itself.

**U-16b `MovesS.blockSolve` · BlockSolve.lean · medium (was hard; split per finding 22).**
`noncomputable def blockSolve (T RB) (hdc) (hK) (hdet : ∀ e ∈ Finset.Icc 1 n,`
`(1 - Kmat T RB e (hK e)).det ≠ 0) : ∀ e ∈ Finset.Icc 1 n, T.State e → Multiset T.VType → Qq`
by strong recursion on e (`Nat.strong_induction_on`), body
`(1 - Kmat)⁻¹ *ᵥ (bTerm + bSplit … (previously solved family))`. moves_ref: "blocks
solve bottom-up, each b_e^split leg already solved". deps: U-14, U-16a. NO e = 0 case
(finding 11): the domain is `Icc 1 n` throughout.

**U-17a `MovesS.blockSolve_spec` · BlockSolveSpec.lean · medium** — the defining
(R_e-lump) equation per e ∈ Icc 1 n, σ' ∈ SigSet: `blockSolve … e he · σ' =`
`Kmat *ᵥ (blockSolve … e he · σ') + bTerm … + bSplit … (restriction of blockSolve) σ'`.
moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} + b_e^split [UNCONDITIONAL]".
deps: U-16b, U-14 · sketch: unfold one recursion layer + U-14's witness equation.

**U-17b `MovesS.rexact_solve` · RexactSolve.lean · medium — NEW (finding 12).**
`statement`: `theorem rexact_solve (B : RS1Bundle …) (hns : B.nsNull) :`
`∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools → B.βfull e he h_ent τ σ' q₀ = B.βmeas e he h_ent τ σ' q₀`
— (R_e-exact) as a Lean statement: the FULL conditional subtree value equals the lump
value, GIVEN (ns-null). moves_ref: "(R_e-exact) β_e^full = β_e [GIVEN (ns-null) —
CLOSED at [3t] §T.2 …; the discharged tag stays displayed]". deps: Defs · hyp:
B.rexact + nsNull (the tag as a Prop field, discharged by [3t] at wave 4 — §3w W-5) ·
sketch: fire the field. The unit exists so the tag is a CITABLE Lean statement, per the
audit; combined with U-24b it yields βfull = the solve.

**U-18 `MovesS.rsh_def` · RshDef.lean · medium — REDESIGNED (finding 13).**
`noncomputable def shConv (T RB) (B) (Ŝ : Shape T) (σ : Multiset T.VType) : Qq :=`
`∑ g : {g : Fin Ŝ.k → Multiset T.VType // σ = Ŝ.σ0 + ∑ i, g i},`
`∏ i, powSubst (Ŝ.δOf i) (B.βfam (Ŝ.eOf i) (Ŝ.eIcc i) (Ŝ.τOf i) (g i))` and
`noncomputable def Rsh (F : ShapeFam T) … (σ) : Qq := ∑ Ŝ ∈ F.Sh, C.Wsh Ŝ * shConv … Ŝ σ`.
The Shape RECORD (§2.D) length-matches entrances/δ-legs BY CONSTRUCTION and supplies
σ₀; the β-family is B.βfam — every datum of the quoted display is now determined.
moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ …} ∏_{i=1}^{k(Ŝ)}
β_{e_i(Ŝ),τ_i(Ŝ)}(σ_i)(q^{δ_i})". deps: U-11, U-12 · hyp: ShapeFam ([2a] finiteness;
CUT-3's choice-free image is the intended instance, §3w W-7).

**U-18b `MovesS.interp_unique` · InterpUnique.lean · easy — NEW.** If f, g ∈ Qq are
OK and agree at every pool of an infinite set, f = g. moves_ref: "every coefficient of
(R_e) is ONE FIXED element of ℚ(q), the same at every prime" (S.3 — fixedness IS
uniqueness of the interpolant). deps: U-27 · sketch: apply U-27 to f − g. Ties every
RatBurdens/RS-bundle Qq datum UNIQUELY to its measured values — the non-degeneracy
counterpart of the interp fields (finding 19's "satisfiable by a wrong instance" is
now excluded up to measured equality).

### Layer S3 — pools, evaluation, ESCAPE(E0) consequences [10]

**U-19 `MovesS.evalAt` · EvalAt.lean · medium** — `OKat q₀ : Subring Qq` +
`evalAt q₀ : OKat q₀ →+* ℚ` + `evalAt_coe`. moves_ref: "EVALUATION IS PER POOL (rev 3):
symbolic det ≠ 0 prevents no zero or uncancelled pole at an individual q₀ = p^δ."
sketch: denom-divisibility closure; hom laws from `RatFunc.eval_add`/`eval_mul`.

**U-20 `MovesS.eval_det` · EvalDet.lean · easy — moves_ref CORRECTED (finding 21).**
`evalAt q₀ M.det = (M.map (evalAt q₀)).det` via `RingHom.map_det`. This unit is
INFRASTRUCTURE for S.4(ii)'s evaluation step, whose display it now quotes:
moves_ref: "at all-active primes … K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0" —
the implicit "det evaluated = det of evaluated matrix" reading of `K_e(p) = A`.
deps: U-19. (The active-value-agreement display now lives at `AVAgree` (§2.C), not here.)

**U-21a `MovesS.pow_fixed_vector` · PowFixed.lean · easy (split of round-1 U21).**
`A *ᵥ v = v → ∀ k, (A ^ k) *ᵥ v = v`. sketch: induction; `Matrix.mulVec_mulVec`.

**U-21b `MovesS.mulVec_abs_bound` · MulVecBound.lean · medium (split).**
For `0 ≤ A i j` entrywise: `|((A ^ k) *ᵥ v) i| ≤ (Finset.univ.sup' _ fun j => |v j|) *`
`((A ^ k) *ᵥ 1) i`. sketch: triangle inequality along the matrix–vector sum; powers of
nonneg matrices are nonneg (uses U-23b).

**U-21c `MovesS.e0_det_ne_zero` · E0Det.lean · medium (split).**
`EscapeE0 A → (1 - A).det ≠ 0`. moves_ref: "A(q₀) being a FINITE nonnegative matrix,
ρ(A(q₀)) < 1, the Neumann series converges" (the det ≠ 0 face). deps: U-21a, U-21b ·
hyp: EscapeE0 (CL-1 — the OPEN kernel; this is its displayed "hence") · sketch:
contrapositive via `Matrix.exists_mulVec_eq_zero_iff`; kernel vector rides U-21a; U-21b
+ escape kills it.

**U-22 `MovesS.rs3_det_symbolic` · Rs3Det.lean · medium — RESTATED (finding 14).**
`statement`: `theorem rs3_det_symbolic (T RB hdc hK) (L : LedgerIV T M)`
`(hact : ∀ q₀ ∈ RB.allActive, ∃ P : PoolHyp T RB e hK q₀, P.Act = Finset.univ) :`
`∀ e ∈ Finset.Icc 1 n, (1 - Kmat T RB e (hK e)).det ≠ 0`
moves_ref: "at all-active primes (cofinitely many — only finitely many primes are roots
of some not-identically-zero cell-size polynomial) K_e(p) = A and ρ(A) < 1 gives
det(I − A) ≠ 0; a rational function vanishing at infinitely many prime evaluations is 0".
deps: U-19, U-20, U-21c, U-27 · hyp: **the note's package** — E0 (inside PoolHyp) +
(iv)-POLY, the latter entering as `RB.allActive_infinite` + `tg_ok` (the (iv)-POLY/XHD-s
burden's all-active infinitude and entry evaluability, §2.C) — no bespoke single-pool
package (the round-1 defect) · sketch: if det = 0 symbolically it evaluates to 0 at
every all-active pool (U-20 + entry_ok); at any one of the infinitely many, U-21c gives
det(1 − A) ≠ 0 — contradiction. Per-pool value read-off stays guarded by `AVAgree`
(never derived here); ESCAPE-UNIF is consumed by NOTHING.

**U-23a `MovesS.neumann_partial` · NeumannPartial.lean · easy (split of round-1 U23).**
`(1 - A) * (∑ m ∈ Finset.range k, A ^ m) = 1 - A ^ k`. sketch: telescope.

**U-23b `MovesS.pow_entry_nonneg` · PowNonneg.lean · easy (split).**
`(∀ i j, 0 ≤ A i j) → ∀ k i j, 0 ≤ (A ^ k) i j`. sketch: induction + sum of products.

**U-23c `MovesS.pow_entry_tendsto` · PowTendsto.lean · easy (split).**
`EscapeE0 A → ∀ i j, Tendsto (fun k => (A ^ k) i j) atTop (nhds 0)`. sketch:
`0 ≤ (A^k) i j ≤ ((A^k) *ᵥ 1) i` (U-23b) + squeeze.

**U-23d `MovesS.e0_inv_nonneg` · E0InvNonneg.lean · medium (split).**
`EscapeE0 A → ∀ i j, 0 ≤ (1 - A)⁻¹ i j`. moves_ref: "the Neumann series converges, and
(I − A(q₀))^{−1} ≥ 0." deps: U-21c, U-23a/b/c · sketch: `(1-A)⁻¹ = Σ_{m<k} A^m +`
`(1-A)⁻¹ * A^k` (U-23a + inverse); partial sums nonneg (U-23b); remainder → 0 (U-23c);
order-closed limit. Consumer: [4]/SQ.2 only — not on MovesS's downstream path.

### Layer S4 — RS.1-DEEP, the marked pairing, RS.4 [6]

**U-24a `MovesS.rs1_deep_eval` · Rs1DeepEval.lean · medium — NEW DECOMPOSITION
(finding 15).** `statement`: the SYMBOLIC fixpoint from the measured one: for
B : RS1Bundle, e ∈ Icc 1 n, σ' ∈ SigSet:
`B.βfam e he · σ' = Kmat T RB e (hK e) *ᵥ (B.βfam e he · σ') + bTerm … σ' +`
`bSplit T RB hdc e he (restriction of B.βfam) σ'`
deps: U-16a, U-19, U-27 · hyp: B.recursion_meas (the measured per-pool fixpoint —
wave-4 discharge W-3) + B.β_interp/β_ok + B.xrb + interp fields of RB + pools_infinite ·
sketch: at each pool the evaluated difference of the two sides vanishes
(recursion_meas + the interp laws + `powSubst`-evaluation compatibility at δ-shifted
pools — the [2r] (e2) convention); entrywise infinitude (U-27) lifts to Qq. **The
round-1 `∀ hβ` malformation is GONE: the recursion is stated of B's OWN family, smaller
blocks read from the same family.**

**U-24b `MovesS.rs1_deep` · Rs1Deep.lean · hard** — RS.1-DEEP:
`B.βfam e he · σ' = ((1 - Kmat T RB e (hK e))⁻¹ *ᵥ (bTerm + bSplit …(B.βfam))) ·` and
`B.βfam = blockSolve T RB hdc hK hdet` (strong induction on e).
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)".
deps: U-14, U-16b, U-17a, U-24a · hyp: hdet (from U-22) + U-24a's set · sketch: per e,
U-24a + U-14 uniqueness identify βfam e with the inverse solve of ITS b; strong
induction on e (legs already identified) matches it with blockSolve. GENUINELY derived;
the only assumed input is the measured fixpoint, the note's actual GIVEN.

**U-25 `MovesS.marked_def` · MarkedDef.lean · easy — RESCOPED (finding 17).**
`noncomputable def markedPairing (T RB hK hdet) (e) (he) : MuHat :=`
`⟨RB.ι e ⬝ᵥ ((1 - Kmat T RB e (hK e))⁻¹ *ᵥ bAgg T RB hdc e he)⟩` — the ORIENTATION
display AS A DEFINITION (the scalar ι_e^T(I−K_e)^{−1}b_e), plus the fence lemma: no
`Add MuHat`/no coercion instance exists (a `#guard_msgs` elaboration check). The
IDENTIFICATION with the measured μ̂ marked total is NOT claimed here — it is sync entry
W-1m with its COMP-h/COMP-hΣ/HMC/ENT-AGG/(iv)-REP provenance. moves_ref: "(RS.1-MARKED)
the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed MARKED-entrance total … NEVER summed
into R_σ." deps: U-16a/b.

**U-27 `MovesS.ratfunc_eval_infinite` · EvalInfinite.lean · medium** — as round 1:
infinite OK vanishing set ⟹ f = 0 (via `Polynomial.eq_zero_of_infinite_isRoot`).
moves_ref: "a rational function equal to 1 at infinitely many prime powers is
identically 1" (applied to f − 1 by consumers).

**U-28 `MovesS.rs4_rational_step` · Rs4.lean · medium — RESCOPED (finding 18).**
`statement`: `theorem rs4_rational_step (C : RS4Chain …) : (∑ σ, C.R σ) = 1`
moves_ref: "at each prime p the decided-mass series totals 1 — X.3's density form …;
RS.1 equates that series with Σ_σ R_σ(p); a rational function equal to 1 at infinitely
many prime powers is identically 1." deps: U-27 · hyp: the note's TWO named primewise
inputs, separately (finding 18): `C.x3_total` (X.3/CL-4, owner [5], OPEN) and
`C.rs1_total` (RS.1's equating — provenance W-1) + `C.r_interp`/`r_ok` (the RS.2
rationality chain: the burdens + CL-17(ii)'s wsh_ok ride the R-construction) +
prime_infinite · sketch: eval(Σ R − 1) = Σ Rval − decidedTotal = 0 at every prime pool;
U-27. This IS the note's "RS.4's rational-identity step [S.5 — GIVEN its inherited
set]" (S.6's own DERIVED bracket) — the inherited set is the explicit field trace.

**U-29 `MovesS.instance_n2` · InstanceN2.lean · medium — NEW (finding 19).**
The NON-VACUITY GATE: construct concrete `TableShape`/`MeasuredSide`/`RatBurdens`
(+ DegCons, SCSData, LedgerIV) for the note's displayed n = 2 instance — ONE block-2
state, the 1×1 kernel, W6's geometric series — and verify by `decide`/`norm_num`:
`(1 - Kmat …).det ≠ 0` and the solve's denominator is `q² + q + 1` (up to units).
moves_ref: "The n = 2 instance is the 1×1 case (W6's geometric series, denominator
q² + q + 1)". deps: U-16b · sketch: `Fin 1` states; kernel entry the displayed
monomial ratio; `RatFunc` arithmetic by `field_simp`. Inhabits EVERY structure of §2 —
the audit's degenerate-instance loophole is closed by exhibition.

---

## 3w. THE WAVE-4 SYNC LIST (declared deferrals — statements PINNED, derivations owed)

Each entry: the pinned Lean Prop (definition, in `MovesS/SyncDefs.lean`), its note
display, its provenance/owner. NO wave-2 unit proves these; NO structure field states
their conclusion beyond the measured inputs listed in §2.

- **W-1 `RS1SH_holds`** := `∀ σ, C.R σ = Rsh F … σ` — RS.1-SH verbatim (S.2). Owed by:
  MovesT (TREE-EXP, TREE-N, ONE-F, (SIB)/CL-10, PCI) + (CUT-WD) + XRB + [2r] legs +
  CL-17(ii)'s W_Ŝ machinery. `C.rs1_total` (§2.D) is its evaluated shadow.
- **W-1m `RS1Marked_holds`** := the measured μ̂ marked total equals
  `(markedPairing …).val` evaluated per pool — RS.1-MARKED's identification. Owed by:
  MovesV/MovesT ((COMP-h) → (COMP-hΣ) → HMC/(COMP-Σ) → ENT-AGG/(COMP-AGG), (iv)-REP).
- **W-2 XRB discharge** — S.1's proof of `RS1Bundle.xrb` under XHD(w/u/d/s) + (JC-INV)
  + (SIB)/(JC-multi) + TB-CAP/VP + REL.2(a)(b)(d) + (ns-null): measure-side; recorded
  at the acceptance-only edge [3] → [3t]-FULL. Until then `xrb` is an open field.
- **W-3 `recursion_meas` discharge** — the measured (R_e-lump) fixpoint from TREE-EXP's
  per-fiber expansion (deep splits at b^split ONCE, per the ROUTING law; J per cell).
- **W-4 `x3_total` discharge** — X.3's density form (CL-4, owner [5], conditional per
  §X-EXHAUST's record; (ns) residual 0 GIVEN (ns-null); countability via (NS-c)).
- **W-5 `nsNull` discharge** — [3t] §T.2's closure of (ns-null) instantiates the field.
- **W-6 per-pool read-off** — every numeric consumption of a β/R value at q₀ cites
  `AVAgree` (§2.C) + its `PoolHyp`; the RESUM-n3/census layers (S.7) live here, not in
  Lean units.
- **W-7 ShapeFam instantiation** — CUT-3's choice-free Ŝ(T) image as `Sh`, with
  (CUT-WD)'s trichotomy (derived in the note GIVEN the CL-13 entrance-predicate supply).
- **W-8 (BDY) consumption duties** — ι owns the ε-prefix with retained h_ent (MovesV
  (COMP-h)); W_Ŝ inclusive of entering reads (MovesT); βmeas charges no mass/height for
  the entering read (MovesT's conditioning). U-7 pins the convention they must satisfy.
- **W-9 (iv)-MEAS full form** — disjoint measurable events over [1v]'s event space
  (LedgerIV carries its nonneg/partition/disjoint-domain shadow, §2.B design note).

## 3b. Load-bearing DAG edges (acyclic)

U-1 → {U-3(via U-2), U-6, U-8, U-16a} · U-2 → {U-3, U-16a} · U-4 → U-5 → U-6 ·
U-6 ⟹ the `hK` argument of every Kmat consumer {U-8, U-16b, U-22, U-24a/b, U-25, U-29} ·
U-8 → U-9a → {U-9b, U-10} · U-11, U-12 → {U-16a, U-18} · U-13 → U-14 → {U-15, U-16b,
U-24b} · U-16a → {U-16b, U-24a} · U-16b → {U-17a, U-25, U-29} · U-19 → {U-9a, U-10,
U-20, U-22} · U-21a, U-21b(←U-23b) → U-21c → {U-22, U-23d} · U-23a/b/c → U-23d ·
U-27 → {U-9b, U-18b, U-22, U-24a, U-28} · U-24a → U-24b · U-22 → hdet of {U-16b, U-24b}.
The CONSUMPTION-DAG discipline (S.1 status line) holds: U-24a/b consume `xrb` and
`recursion_meas`, never a PCI site; nothing proves toward `xrb`.

---

## 4. Trust surface & audit flags (REV 2)

1. **No `True` fields exist.** Grep-check duty at phase E: `grep -n ': True' Defs.lean`
   must return empty. The two round-1 placeholder habits (LedgerIV tags, avAgree) are
   replaced by the §2.B carriers and the `AVAgree` Prop definition.
2. **`xrb` is the corpus's honest XRB interface** (open field; W-2). Flag any future
   claim that MovesS proves XRB.
3. **The interp fields are the rationality trust boundary**: (iv)-POLY/XHD-s (tg_ok/
   tg_interp), (J-RAT) (j_ok/j_interp), INIT-RAT (ι_ok/ι_interp), CL-17(ii) (wsh_ok),
   plus `allActive_infinite` (S.4(ii)'s cofinite-activity face). Auditor: check each
   maps to its S.3 inventory line and none is derivable from the others.
4. **`recursion_meas`/`x3_total`/`rs1_total` are the three measured inputs** the note
   marks GIVEN (S.2's statement line, S.5's route). They are per-pool ℝ-statements —
   NOT the symbolic conclusions (those are U-24a/b, U-28's outputs).
5. **PART-2's marked surplus row has no field** — unconsumable, as rev 6 demands.
6. **ESCAPE-UNIF does not exist in this corpus** (consumed by nothing).
7. **S.7 / probe roster / (CUT-WD)'s own proof / junk-determinant recording** are
   census-side or wave-4 (W-6, W-7); (BDY) is in scope as U-7 + W-8.
8. **`SCSData.memberOf_ne_sel`'s drafting artifact** (the vacuous left disjunct) is
   struck at phase E: the field is `memberOf e τ o i ≠ selIdx e τ o`. Recorded here so
   the elaborated Defs cannot silently weaken it.

## 5. Conventions (phase E / prover fleet) + census

Build per file `lake env lean LeanUrat/MovesS/<file>.lean`; `#print axioms` per unit
(Lean-core only; `sorryAx` flagged). Defs skeleton `sorry`s (`OKat`, `evalAt` bodies,
`kTarget`, `Kmat`, `bTerm`) are elaborated at phase E BEFORE fan-out; `consumedDeltas`/
`evalRe`/`bSplit` live in U-16a. Statement changes to any §2 field = statement-fence
event. Mathlib names as §1 (all verified in the pinned cache).

**Census: 38 units = 12 easy / 25 medium / 1 hard.** Easy {U-1, U-2, U-3, U-5, U-13,
U-18b, U-20, U-21a, U-23a, U-23b, U-23c, U-25}; hard {U-24b (the strong-induction
identification)}; medium the remaining 25. Round-1's three hards are split per R6
(finding 22): 3 → 10 one-display units.

---

## 6. Findings → repairs table (audit `MOVESS_AUDIT_CODEX_2026-07-28.md`, 22 findings)

| # | class | repair | where |
|---|---|---|---|
| 1 | crit | ALL `True` tags deleted; NINE CL-5 items now contentful Props over MeasuredSide carriers; [3t]/[2r]/X.3 tags → measured input fields (`recursion_meas`, `x3_total`, `rs1_total`, `xrb`) + sync entries W-1..W-5 | §2.B, §2.D, §3w |
| 2 | crit | XRB reverted to open hypothesis: `βmeas` height-indexed, `xrb` a displayed field, discharge = W-2 | §2.D, R3 |
| 3 | crit | rationality = `RatBurdens` (Qq data + per-pool interpolation laws, owners named); no bare-Qq table fields; U-15/RS.2 conditional on RB by construction | §2.C, U-15 |
| 4 | crit | `kcolSameSize` field DELETED; (SCS) is the `hK` ARGUMENT produced by U-6 from SCSData + DegCons | §2.C, U-6 |
| 5 | crit | SCSData carries SP.1's member-injection carriers; U-4 derives flank-empty + λ-singleton by pigeonhole | §2.A, U-4 |
| 6 | crit | (BDY) both halves: edge rule + node shadow + mass-split (U-7); consumption duties named at W-8 | U-7, W-8 |
| 7 | crit | `sig_covers` is a real TableShape field; U-8 cites it | §2.A, U-8 |
| 8 | crit | fused `part1` deleted; PART-1 = cell-partition identity over the Cell carrier; TG-vs-J identifications are RatBurdens interp laws; (K-SUB) derived in the chain U-8 → U-9a → U-9b with DegCons/(SCS)/dispatch in the trace | §2.B/C, U-9a/b |
| 9 | crit | `powSubst (δ : ℕ+)`; `Member.δ : ℕ+` | D6, §2.A, U-12 |
| 10 | crit | `bSplit` takes `hdc : DegCons`; βlt application licensed by U-2 inside the definition | U-16a |
| 11 | crit | every block quantifier `e ∈ Finset.Icc 1 n`; no e = 0 anywhere | R5, §3 |
| 12 | crit | (R_e-exact) is unit U-17b over `βfull`/`nsNull`/`rexact`; nsNull discharge = W-5 | §2.D, U-17b |
| 13 | crit | `Shape` is a length-matched record (k/eOf/τOf/δOf/σ0); `shConv` fully defined from B.βfam; Rsh determined | §2.D, U-18 |
| 14 | crit | U-22 restated with the note's package: E0 + (iv)-POLY via `allActive_infinite`/`tg_ok`; no single-pool bespoke input | U-22 |
| 15 | crit | `∀ hβ` malformation gone: `recursion_meas` is per-pool, of B's OWN family; symbolic fixpoint DERIVED (U-24a), identification with blockSolve DERIVED (U-24b) | §2.D, U-24a/b |
| 16 | crit | `shallow_expansion` field deleted; RS.1-SH = pinned sync statement W-1 (no fake wave-2 derivation); its evaluated shadow `rs1_total` feeds only RS.4 | §3w W-1 |
| 17 | crit | `marked_pairing` field deleted; U-25 is the DEFINITION + type fence; identification = W-1m | U-25, W-1m |
| 18 | crit | fused `primewise` deleted; RS.4 takes the note's two named inputs `x3_total` (CL-4/[5]) + `rs1_total` (RS.1's equating) separately + the rationality chain; U-28 = the note's own DERIVED rational-identity step | §2.D, U-28 |
| 19 | crit | inhabitation: per-structure intended-instance notes; `rep_ne`; pool/prime infinitude fields; `consumedDeltas` computed (RegP never vacuous by free Δ); `interp_unique` (U-18b); the `instance_n2` gate (U-29) | R4, §2, U-18b, U-29 |
| 20 | gap | U-10 restated: Act-subtype binders, explicit memberships, OKat witnesses for TG/J evaluations | U-10 |
| 21 | gap | U-20 re-referenced to the S.4(ii) display it serves (INFRA); active-value agreement lives at `AVAgree` | U-20, §2.C |
| 22 | gap | splits: U-16a/16b/17a; U-21a/b/c; U-23a/b/c/d — 10 one-display units replace 3 hidden multi-lemma units | R6, §3 |

STATUS: REV 2 complete, 2026-07-27. All 22 findings repaired (none pushed back; W-1,
W-1m, W-2, W-3, W-4, W-5 are the explicit deferred-to-wave-4 items the audit's R2
guidance licenses). Awaits the single budgeted re-audit.

codex
1. **CRITICAL — `SCSData` does not actually require auxiliary members to avoid the selected member.**

   > `memberOf_ne_sel : ∀ e τ o (hc : routeOf ... = .kcol ∨ True) i,`
   > `(T.odata ...).mem.get (memberOf ... i) |>.continuing = False ∨`
   > `memberOf ... i ≠ selIdx e τ o`

   The `∨ True` premise is vacuous, and the conclusion permits `memberOf ... i = selIdx ...` whenever that member is halted. Thus the pigeonhole argument advertised for U-4 cannot establish that the injection’s domain is empty. The prose promise to strike this “at phase E” does not repair the audited specification.

2. **CRITICAL — U-4 derives zero flank width from insufficient hypotheses.**

   > `S.flankCount ... = 0 ∧ ... ∧ S.W ... = e * S.ℓ ...`

   Its only relevant field is:

   > `flankWidth_pos : 0 < flankCount ... → 0 < flankWidth ...`

   This does not imply `flankCount = 0 → flankWidth = 0`. Consequently `window_comp` does not yield `W = e·ℓ`. U-4 is stronger than its proposed hypotheses.

3. **GAP — several Defs declarations are not plausibly elaboratable in their stated order.**

   > `memberOf_ne_sel ... selIdx ...`
   >
   > `stage_D ... D' ...`
   >
   > `stage_W ... W' ...`

   Here `selIdx`, `D'`, and `W'` are declared later in the same structure. Likewise:

   > `R : SplitTy → Qq`
   >
   > `SplitTy : Type`

   uses `SplitTy` before declaration. The promised later normalization is not part of the audited skeleton.

4. **CRITICAL — `LedgerIV` replaces XHD/D4R.0/(iv)-MEAS with weaker or different numerical shadows.**

   > `xhd_sum : HasSum ... (M.μcell ...)`
   >
   > `d4r0 : c ≠ c' → Disjoint (M.HDom ... c) (M.HDom ... c')`
   >
   > `meas_nonneg : ... 0 ≤ M.μcell ...`

   XHD’s two-sided exact realizability and its representative/history quantifiers are absent. D4R.0 and MEAS concern disjoint measurable events after height grouping, not merely disjoint sets of height labels plus nonnegativity. W-9 admits that the full MEAS condition is missing, but supplies no hypothesis field. Therefore units claiming the literal nine-input trace, especially U-9b and U-10, do not have the note’s hypotheses.

5. **CRITICAL — `rep_indep` silently strengthens RS.0(α).**

   > `rep_indep : ∀ ... (x y : M.Rep e τ), M.μcell e τ x = M.μcell e τ y`

   The note assumes equality of the measured `T·G` row/entry after the specified weighted grouping. The blueprint requires every individual digit-cell mass to agree across representatives. That is strictly stronger unless a representative-independent cell identification and cellwise equality theorem is supplied.

6. **CRITICAL — ledger items HMC, ACT, INIT/ENT-COUNT, and COMP-TYPING are detached or incomplete.**

   > `hmc : M.kstep (k+1) ... = ∑ γ, M.kstep k ... * M.kstep 1 ...`
   >
   > `act : (∀ h ∈ M.HDom ..., M.gwt ... = 0) → M.μcell ... = 0`
   >
   > `init_agg : M.ιval ... = ∑ ε, M.ιsh ...`
   >
   > `comp_once : HasSum ... M.ιsh ...`

   `kstep` is not tied to `Kmat`, templates, or `μcell`, so it can be chosen independently (even identically zero). ACT has no active-cell/state classification. ENT-COUNT and the tie to cylinder/full counts are absent. `comp_once` only controls the entrance sum and does not state the full `(COMP-h)→(COMP-hΣ)→(COMP-Σ)` once-only factorization. These are not the displayed ledger conditions.

7. **CRITICAL — `RatBurdens` and its pool sets do not encode the note’s rationality hypotheses.**

   > `Pools : Set ℚ`
   >
   > `pools_infinite : Pools.Infinite`
   >
   > `TG ... : Qq`
   >
   > `J ... : Qq`
   >
   > `allActive : Set ℚ`
   >
   > `allActive_infinite : allActive.Infinite`

   `Pools` need not be the relevant prime powers and is not closed under `q₀ ↦ q₀^δ`. `allActive` need not be the cofinite all-active prime locus. The `(iv)-POLY` polynomial-valued count laws and their displayed degree bounds are absent and replaced by arbitrary rational functions interpolating on an arbitrary infinite set. This changes the hypotheses of RS.2 and RS.3(ii).

8. **CRITICAL — `PoolHyp` makes ESCAPE(E0) vacuous on an empty active subsystem.**

   > `Act : Finset (T.State e)`
   >
   > `e0 : EscapeE0 A`

   There is no condition identifying `Act` with all realized states or requiring it to contain any realized state. Taking `Act = ∅` makes the matrix and E0 condition vacuous. This recreates the forbidden degenerate-hypothesis trap for per-pool E0 and `AVAgree`.

9. **CRITICAL — `RS1Bundle.βfam` assumes the rationality that RS.2 is supposed to derive.**

   > `βfam : ... → Qq`
   >
   > `β_interp : ... evalAt ... βfam ... = βmeas ...`

   The note first defines the measured conditional values, derives the block equation, and then obtains fixed rational functions by triangular solving and Cramer/adjugate. Existence of a global rational interpolant for every measured β is therefore a conclusion, not an input. U-24a’s interpolation proof is circular relative to RS.2.

10. **CRITICAL — the recurrence and RS.1-DEEP are restricted to an inadequately specified `SigSet`.**

   > `recursion_meas : ... (hσ : σ' ∈ T.SigSet) ...`
   >
   > U-17a: `per ... σ' ∈ SigSet`
   >
   > U-24a: `σ' ∈ SigSet`

   The note states `(R_e)` and RS.1-DEEP for every verdict-type multiset. Moreover:

   > `sig_covers : ... routeOf ... = .termFin → verdicts ... ∈ SigSet`

   covers only terminal one-step verdicts, not multiset convolutions produced by split subtrees. U-24b then additionally claims unrestricted functional equality:

   > `B.βfam = blockSolve ...`

   which cannot follow from equations proved only on `SigSet`.

11. **CRITICAL — `RS4Chain.SplitTy` is unrelated to the verdict multisets in RS.1-SH.**

   > `R : SplitTy → Qq`
   >
   > `SplitTy : Type`
   >
   > W-1: `∀ σ, C.R σ = Rsh F … σ`

   `Rsh` is indexed by `Multiset T.VType`, while `C.R` is indexed by an arbitrary type. No equivalence or coercion is supplied. Thus W-1 is not typeable as written and U-28’s sum need not be the note’s `Σ_σ R_σ`.

12. **CRITICAL — U-10 silently requires nonnegativity of unused rational tables.**

   > `(hTG : ∀ o, ∃ h ..., 0 ≤ evalAt ... RB.TG ...)`
   >
   > `(hJ : ∀ o, ∃ h ..., 0 ≤ evalAt ... RB.J ...)`

   The note requires nonnegativity of the routed mass: `TG` for kernel/terminal outcomes and `J` for split outcomes. The blueprint requires `TG` to be nonnegative on split outcomes and `J` on nonsplit outcomes, where their interpolation laws impose no semantics. U-10 is therefore strictly stronger than the displayed `(K-SUB)` claim.

13. **CRITICAL — U-22 has the wrong block quantifier order.**

   > `(hact : ∀ q₀ ∈ RB.allActive, ∃ P : PoolHyp T RB e hK q₀, P.Act = Finset.univ) :`
   > `∀ e ∈ Finset.Icc 1 n, ...`

   The `e` in `hact` is an outer implicit parameter, while the conclusion introduces a new `e`. E0/all-active data for one block cannot prove determinant nonvanishing for every block. The note quantifies the per-pool E0 package over every `e ≤ n`.

14. **GAP — U-24a lacks the pool-closure hypothesis needed for base-changed legs.**

   > `powSubst`-evaluation compatibility at δ-shifted pools

   `β_interp` is available only when `q₀ ∈ M.Pools`, but a leg evaluated at `q₀` requires interpolation of β at `q₀^δ`. No field states `q₀ ∈ Pools → q₀^δ ∈ Pools` for consumed δ, nor identifies `Pools` with all relevant prime powers. The proposed proof cannot discharge its base-change step.

15. **GAP — U-7 is not a one-display unit.**

   > “Three statements: `bdy_edge_partition`; `bdy_node_shadow`; `bdy_mass_split`”

   These are three distinct lemmas, including a separate finite-sum decomposition. This violates the blueprint’s own one-display decomposition rule.

16. **GAP — U-21b is underspecified for an empty finite index type.**

   > `Finset.univ.sup' _ fun j => |v j|`

   `sup'` needs a proof that `Finset.univ` is nonempty, but the unit assumes only `Fintype ι`. This matters because `EscapeE0` and `PoolHyp.Act` explicitly permit empty index types.

17. **GAP — U-25 uses an undefined aggregate and W-1m has no measured marked-total carrier.**

   > `... *ᵥ bAgg T RB hdc e he`
   >
   > W-1m: “the measured μ̂ marked total equals `(markedPairing …).val` evaluated per pool”

   `bAgg` is absent from the Defs skeleton and U-16a. No field or parameter represents the measured marked total appearing in W-1m. The deferred proposition therefore cannot yet be stated with the advertised typing.

18. **GAP — several wave-4 “pinned” obligations are prose, not pinned propositions, and convergence is omitted.**

   > “W-2 XRB discharge”
   >
   > “W-3 `recursion_meas` discharge”
   >
   > “W-7 ShapeFam instantiation”
   >
   > “W-8 (BDY) consumption duties”
   >
   > “W-9 (iv)-MEAS full form”

   Unlike W-1, these have no Lean proposition signatures or abstract carriers for their hypotheses. In particular, the note’s unconditional convergence/Tonelli assertion for RS.1 is neither a unit nor a pinned sync proposition. Explicit deferral is acceptable, but an unformalized prose obligation is not a pinned deferral.

19. **GAP — U-28 does not carry RS.4’s displayed inherited hypothesis set or `(ns-null)` proof.**

   > `theorem rs4_rational_step (C : RS4Chain …) : (∑ σ, C.R σ) = 1`

   `RS4Chain` has no `LedgerIV`, per-pool E0/ACT package, proof of `B.nsNull`, CL-17(ii) production result, or the remaining RS.1/XRB hypothesis package. Instead, `x3_total` and `rs1_total` collapse upstream conclusions into fields. The frozen note explicitly requires the complete inherited set to remain attached to RS.4.

20. **CRITICAL — U-29 does not genuinely close the non-vacuity repair.**

   > “construct concrete `TableShape`/`MeasuredSide`/`RatBurdens` (+ DegCons, SCSData, LedgerIV)”
   >
   > “Inhabits EVERY structure of §2”

   The listed construction omits `ShapeFam`, `RS1Bundle`, `RS4Chain`, `PoolHyp`, and the wave-4 interfaces. The frozen note supplies only the n=2 scalar denominator shadow, not enough data to construct the full nine-input measured stack. A toy structure engineered to have denominator `q²+q+1` would not establish inhabitation by the note’s intended instance.

Counts: **13 CRITICAL / 7 GAP**

**REJECT (13 crit / 7 gap)**
tokens used
53,885
1. **CRITICAL — `SCSData` does not actually require auxiliary members to avoid the selected member.**

   > `memberOf_ne_sel : ∀ e τ o (hc : routeOf ... = .kcol ∨ True) i,`
   > `(T.odata ...).mem.get (memberOf ... i) |>.continuing = False ∨`
   > `memberOf ... i ≠ selIdx e τ o`

   The `∨ True` premise is vacuous, and the conclusion permits `memberOf ... i = selIdx ...` whenever that member is halted. Thus the pigeonhole argument advertised for U-4 cannot establish that the injection’s domain is empty. The prose promise to strike this “at phase E” does not repair the audited specification.

2. **CRITICAL — U-4 derives zero flank width from insufficient hypotheses.**

   > `S.flankCount ... = 0 ∧ ... ∧ S.W ... = e * S.ℓ ...`

   Its only relevant field is:

   > `flankWidth_pos : 0 < flankCount ... → 0 < flankWidth ...`

   This does not imply `flankCount = 0 → flankWidth = 0`. Consequently `window_comp` does not yield `W = e·ℓ`. U-4 is stronger than its proposed hypotheses.

3. **GAP — several Defs declarations are not plausibly elaboratable in their stated order.**

   > `memberOf_ne_sel ... selIdx ...`
   >
   > `stage_D ... D' ...`
   >
   > `stage_W ... W' ...`

   Here `selIdx`, `D'`, and `W'` are declared later in the same structure. Likewise:

   > `R : SplitTy → Qq`
   >
   > `SplitTy : Type`

   uses `SplitTy` before declaration. The promised later normalization is not part of the audited skeleton.

4. **CRITICAL — `LedgerIV` replaces XHD/D4R.0/(iv)-MEAS with weaker or different numerical shadows.**

   > `xhd_sum : HasSum ... (M.μcell ...)`
   >
   > `d4r0 : c ≠ c' → Disjoint (M.HDom ... c) (M.HDom ... c')`
   >
   > `meas_nonneg : ... 0 ≤ M.μcell ...`

   XHD’s two-sided exact realizability and its representative/history quantifiers are absent. D4R.0 and MEAS concern disjoint measurable events after height grouping, not merely disjoint sets of height labels plus nonnegativity. W-9 admits that the full MEAS condition is missing, but supplies no hypothesis field. Therefore units claiming the literal nine-input trace, especially U-9b and U-10, do not have the note’s hypotheses.

5. **CRITICAL — `rep_indep` silently strengthens RS.0(α).**

   > `rep_indep : ∀ ... (x y : M.Rep e τ), M.μcell e τ x = M.μcell e τ y`

   The note assumes equality of the measured `T·G` row/entry after the specified weighted grouping. The blueprint requires every individual digit-cell mass to agree across representatives. That is strictly stronger unless a representative-independent cell identification and cellwise equality theorem is supplied.

6. **CRITICAL — ledger items HMC, ACT, INIT/ENT-COUNT, and COMP-TYPING are detached or incomplete.**

   > `hmc : M.kstep (k+1) ... = ∑ γ, M.kstep k ... * M.kstep 1 ...`
   >
   > `act : (∀ h ∈ M.HDom ..., M.gwt ... = 0) → M.μcell ... = 0`
   >
   > `init_agg : M.ιval ... = ∑ ε, M.ιsh ...`
   >
   > `comp_once : HasSum ... M.ιsh ...`

   `kstep` is not tied to `Kmat`, templates, or `μcell`, so it can be chosen independently (even identically zero). ACT has no active-cell/state classification. ENT-COUNT and the tie to cylinder/full counts are absent. `comp_once` only controls the entrance sum and does not state the full `(COMP-h)→(COMP-hΣ)→(COMP-Σ)` once-only factorization. These are not the displayed ledger conditions.

7. **CRITICAL — `RatBurdens` and its pool sets do not encode the note’s rationality hypotheses.**

   > `Pools : Set ℚ`
   >
   > `pools_infinite : Pools.Infinite`
   >
   > `TG ... : Qq`
   >
   > `J ... : Qq`
   >
   > `allActive : Set ℚ`
   >
   > `allActive_infinite : allActive.Infinite`

   `Pools` need not be the relevant prime powers and is not closed under `q₀ ↦ q₀^δ`. `allActive` need not be the cofinite all-active prime locus. The `(iv)-POLY` polynomial-valued count laws and their displayed degree bounds are absent and replaced by arbitrary rational functions interpolating on an arbitrary infinite set. This changes the hypotheses of RS.2 and RS.3(ii).

8. **CRITICAL — `PoolHyp` makes ESCAPE(E0) vacuous on an empty active subsystem.**

   > `Act : Finset (T.State e)`
   >
   > `e0 : EscapeE0 A`

   There is no condition identifying `Act` with all realized states or requiring it to contain any realized state. Taking `Act = ∅` makes the matrix and E0 condition vacuous. This recreates the forbidden degenerate-hypothesis trap for per-pool E0 and `AVAgree`.

9. **CRITICAL — `RS1Bundle.βfam` assumes the rationality that RS.2 is supposed to derive.**

   > `βfam : ... → Qq`
   >
   > `β_interp : ... evalAt ... βfam ... = βmeas ...`

   The note first defines the measured conditional values, derives the block equation, and then obtains fixed rational functions by triangular solving and Cramer/adjugate. Existence of a global rational interpolant for every measured β is therefore a conclusion, not an input. U-24a’s interpolation proof is circular relative to RS.2.

10. **CRITICAL — the recurrence and RS.1-DEEP are restricted to an inadequately specified `SigSet`.**

   > `recursion_meas : ... (hσ : σ' ∈ T.SigSet) ...`
   >
   > U-17a: `per ... σ' ∈ SigSet`
   >
   > U-24a: `σ' ∈ SigSet`

   The note states `(R_e)` and RS.1-DEEP for every verdict-type multiset. Moreover:

   > `sig_covers : ... routeOf ... = .termFin → verdicts ... ∈ SigSet`

   covers only terminal one-step verdicts, not multiset convolutions produced by split subtrees. U-24b then additionally claims unrestricted functional equality:

   > `B.βfam = blockSolve ...`

   which cannot follow from equations proved only on `SigSet`.

11. **CRITICAL — `RS4Chain.SplitTy` is unrelated to the verdict multisets in RS.1-SH.**

   > `R : SplitTy → Qq`
   >
   > `SplitTy : Type`
   >
   > W-1: `∀ σ, C.R σ = Rsh F … σ`

   `Rsh` is indexed by `Multiset T.VType`, while `C.R` is indexed by an arbitrary type. No equivalence or coercion is supplied. Thus W-1 is not typeable as written and U-28’s sum need not be the note’s `Σ_σ R_σ`.

12. **CRITICAL — U-10 silently requires nonnegativity of unused rational tables.**

   > `(hTG : ∀ o, ∃ h ..., 0 ≤ evalAt ... RB.TG ...)`
   >
   > `(hJ : ∀ o, ∃ h ..., 0 ≤ evalAt ... RB.J ...)`

   The note requires nonnegativity of the routed mass: `TG` for kernel/terminal outcomes and `J` for split outcomes. The blueprint requires `TG` to be nonnegative on split outcomes and `J` on nonsplit outcomes, where their interpolation laws impose no semantics. U-10 is therefore strictly stronger than the displayed `(K-SUB)` claim.

13. **CRITICAL — U-22 has the wrong block quantifier order.**

   > `(hact : ∀ q₀ ∈ RB.allActive, ∃ P : PoolHyp T RB e hK q₀, P.Act = Finset.univ) :`
   > `∀ e ∈ Finset.Icc 1 n, ...`

   The `e` in `hact` is an outer implicit parameter, while the conclusion introduces a new `e`. E0/all-active data for one block cannot prove determinant nonvanishing for every block. The note quantifies the per-pool E0 package over every `e ≤ n`.

14. **GAP — U-24a lacks the pool-closure hypothesis needed for base-changed legs.**

   > `powSubst`-evaluation compatibility at δ-shifted pools

   `β_interp` is available only when `q₀ ∈ M.Pools`, but a leg evaluated at `q₀` requires interpolation of β at `q₀^δ`. No field states `q₀ ∈ Pools → q₀^δ ∈ Pools` for consumed δ, nor identifies `Pools` with all relevant prime powers. The proposed proof cannot discharge its base-change step.

15. **GAP — U-7 is not a one-display unit.**

   > “Three statements: `bdy_edge_partition`; `bdy_node_shadow`; `bdy_mass_split`”

   These are three distinct lemmas, including a separate finite-sum decomposition. This violates the blueprint’s own one-display decomposition rule.

16. **GAP — U-21b is underspecified for an empty finite index type.**

   > `Finset.univ.sup' _ fun j => |v j|`

   `sup'` needs a proof that `Finset.univ` is nonempty, but the unit assumes only `Fintype ι`. This matters because `EscapeE0` and `PoolHyp.Act` explicitly permit empty index types.

17. **GAP — U-25 uses an undefined aggregate and W-1m has no measured marked-total carrier.**

   > `... *ᵥ bAgg T RB hdc e he`
   >
   > W-1m: “the measured μ̂ marked total equals `(markedPairing …).val` evaluated per pool”

   `bAgg` is absent from the Defs skeleton and U-16a. No field or parameter represents the measured marked total appearing in W-1m. The deferred proposition therefore cannot yet be stated with the advertised typing.

18. **GAP — several wave-4 “pinned” obligations are prose, not pinned propositions, and convergence is omitted.**

   > “W-2 XRB discharge”
   >
   > “W-3 `recursion_meas` discharge”
   >
   > “W-7 ShapeFam instantiation”
   >
   > “W-8 (BDY) consumption duties”
   >
   > “W-9 (iv)-MEAS full form”

   Unlike W-1, these have no Lean proposition signatures or abstract carriers for their hypotheses. In particular, the note’s unconditional convergence/Tonelli assertion for RS.1 is neither a unit nor a pinned sync proposition. Explicit deferral is acceptable, but an unformalized prose obligation is not a pinned deferral.

19. **GAP — U-28 does not carry RS.4’s displayed inherited hypothesis set or `(ns-null)` proof.**

   > `theorem rs4_rational_step (C : RS4Chain …) : (∑ σ, C.R σ) = 1`

   `RS4Chain` has no `LedgerIV`, per-pool E0/ACT package, proof of `B.nsNull`, CL-17(ii) production result, or the remaining RS.1/XRB hypothesis package. Instead, `x3_total` and `rs1_total` collapse upstream conclusions into fields. The frozen note explicitly requires the complete inherited set to remain attached to RS.4.

20. **CRITICAL — U-29 does not genuinely close the non-vacuity repair.**

   > “construct concrete `TableShape`/`MeasuredSide`/`RatBurdens` (+ DegCons, SCSData, LedgerIV)”
   >
   > “Inhabits EVERY structure of §2”

   The listed construction omits `ShapeFam`, `RS1Bundle`, `RS4Chain`, `PoolHyp`, and the wave-4 interfaces. The frozen note supplies only the n=2 scalar denominator shadow, not enough data to construct the full nine-input measured stack. A toy structure engineered to have denominator `q²+q+1` would not establish inhabitation by the note’s intended instance.

Counts: **13 CRITICAL / 7 GAP**

**REJECT (13 crit / 7 gap)**
