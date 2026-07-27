# Codex re-audit of MovesU Lean blueprint, REV 2 (§U-SQUEEZE) — 2026-07-27
Verdict: REJECT (4 crit / 3 gap). Full transcript below (prompt echo + Codex response).

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa3d6-bcee-7842-8b80-9f10a451f8aa
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

This is a RE-AUDIT of rev 2. The rev-1 findings (13, listed in the blueprint's findings→repairs table) were repaired. Verify each repair is genuine AND sweep the whole blueprint fresh — new defects introduced by the repairs count fully.

THE FROZEN NOTE (ground truth):

## §U-SQUEEZE — the two-sided squeeze and Theorem U (assembly note 9, = plan [4]-COND)

*(2026-07-27. Assembly note 9 per ASSEMBLY_PLAN_2026-07-26.md §6, drafted
under the REV 16 [4] RE-RULING in the CONDITIONAL form [4]-COND — the
[4]-COND SPEC ADDENDUM (plan §1) governs this draft and its acceptance
record. Every spine input is consumed as FROZEN dual-accepted TEXT with
its own displayed hypothesis ledger attached — §S-RESUM's solve + its
S.6 set, §X-EXHAUST's X.3/CL-4 + X.2 envelope, §T-ASSEMBLY's
TREE-N/TREE-EXP — citing accepted STATEMENTS and named open obligations,
never a discharged obligation (plan §0's ledger rule). Nothing
SUBSTANTIVE in this note is unconditional — the only tag-free steps,
re-audited at rev 2, are: (BOX-N), a definitional count identity;
SQ.3's bracket arithmetic AS arithmetic (every input tagged);
Tonelli's extended-value existence in [0, ∞] (SQ.2's retyped clause —
existence only, never finiteness or identification); and the
env(N) → 0 ⟹ limit forcing in (U-n). Every density-typed claim
carries its ledger. The product is the two-sided bracketing
arithmetic, the named open lemma TRACK-COUNT, and THEOREM U in the
FULL HONEST FORM — the campaign's statement-of-record with the
complete capstone ledger inline.)*

**What this note is.** The assembly endgame, generalizing the n = 2
machine-checked precedent (W6: `msW_eighth_le` + the box partition, plan
§6 header). The level-N decided mass is bracketed two-sidedly against
§S's rational solve: decided_σ(N) ≤ R_σ(p)·p^{nN} from above (SQ.2 —
the decided series is a partial sum of RS.1's positive series, dominated
by its own fixpoint), and decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN} from
below (SQ.3 — the box partition, everyone else's upper bound, RS.4's
checksum; the envelope enters only to BOUND env(N)). env(N) → 0
(X.3/CL-4) then forces ρ_σ(p) = R_σ(p) at every p SATISFYING (REG-p) — Theorem U (SQ.4; a p failing (REG-p) is not adjudicated).
Finiteness of the level-N decided family is SQ.0's decided-budget
arithmetic — this note's owned kernel area, TRACK-COUNT its named open
lemma.

**Notation (fixed for this note).** The level-N box := the monic
degree-n coefficient box mod p^N (p^{nN} residue classes; μ its
normalized mass = the monic-box Haar). decided_σ(N) := #{f mod p^N :
T_can^τ(f) is a complete finite realizable tree, all leaves
(τ-irr)/(τ-hen), certified at level N (thr ≤ N per TREE-N's join), of
verdict-type multiset σ}. Undec(N) := the complement of the level-N
decided cells (X.3's object — never an exact-ns residue set, (NS-b)).
undec(N) := #Undec(N); env(N) := μ(Undec(N)) = undec(N)/p^{nN}.
R_σ ∈ ℚ(q) := §S RS.1-SH's object — the ONLY density-typed output of
the solve; the marked pairing ι_e^T(I − K_e)^{−1}b_e is μ̂-typed and
appears in NO display of this note (§S's type fence, binding).

### SQ.0 DECIDED-BUDGET — the finite decided family (kernel area; TRACK-COUNT displayed OPEN)

**Statement (plan §6 REV 5/8 form; consumes [1]/§C/L5fix + X.2's
PROGRESS mechanics ONLY — [3]-INDEPENDENT: no solve object appears
here).** If f's canonical tree T_can(f) has decision threshold ≤ N —
every branch terminal; each budget below read PER BRANCH, the family
bound taken over the finitely many branches of a degree-n tree — then,
proved from DECISION STABILITY (decomposition-note Thm 2.1 / X.2's
PROGRESS mechanics), never from the tail:
 (a) HEIGHT BUDGET [DERIVED]: every height of every read ≤ h*(N) —
   each move constrains levels ≥ an affine function of its heights,
   and every constrained level is ≤ N;
 (b) KEY-WEIGHT BUDGET [DERIVED given (a)]: every key weight ≤ w*(N) —
   a key's weight is a consumed side value, bounded by the height
   budget;
 (c) MULTI-TRACK ZERO-GAIN BOUND [OPEN at exactly TRACK-COUNT + the
   D(n) duty]:
       d_zero(H) ≤ L(n)·D(n)·w*(N),
   by exhibiting, per history: (c1) an assignment of EVERY zero-gain
   move to ONE of at most L(n) monotone weight TRACKS — keys, branches,
   and ladder restarts each open a track; the track COUNT is
   TRACK-COUNT's open duty, displayed below; (c2) a common denominator
   D(n) with all key weights in (1/D(n))·ℤ, so each zero-gain move
   strictly increases its own track by ≥ 1/D(n) (D.10's strict climb);
   (c3) a DISPLAYED interval, bounded via threshold ≤ N, containing
   every track's weight — the budget is SUMMED over tracks, never
   charged to one ladder (the REV 5 repair: one history can contain
   several keys, branches, and ladder restarts);
 (d) LEDGER BUDGET [DERIVED at the realized level; ONE sub-claim
   flagged]: for an individual realized lift-carrying history η,
   Theorem C gives the NONZERO integer count p^{nN−A(η)} of its level-N
   stratum, forcing A(η) ≤ nN; A is shape-determined (C.3), so every
   REALIZABLE template γ inherits A(γ) ≤ nN (unrealizable templates
   zero-extended, (†-AGG)(ii)) — NEVER derived from C_γ(p)·p^{nN−A} ∈ ℤ
   alone, which proves nothing; PLUS the positive genuine-increment
   sub-claim (FLAGGED OPEN: every genuine node strictly increments the
   ledger), giving #genuine nodes ≤ nN.
CONCLUSION (given (a)–(d)): histories with threshold ≤ N form a FINITE
family with an explicit bound T(n, N). X.1b appears NOWHERE in this
lemma. D(n) DUTY (open, owned here): candidate D(n) | n!, underived.

**The named open lemma (quoted VERBATIM from plan §6 — CL-7's first
item; this note displays it, does not advance it):**

> **TRACK-COUNT (OPEN).** Every degree-n canonical history H admits a
> track assignment as in (c1) with at most L(n) tracks, L(n) explicit —
> i.e. the number of track-OPENING events (key creations, branch
> openings, ladder RESTARTS) in H is bounded by a function of n alone,
> uniformly in p, N, and depth. The danger is precisely the restarts:
> each restart must be charged to a monotone consumable (a key-degree
> drop, a branch-budget decrement, or a weight-lattice coarsening) that
> can occur ≤ f(n) times; the candidate L(n) ≤ n² is NOT accepted
> without that charging argument.

STATUS HONESTY: the plan's REV 15 exception cleared SQ.0 + the
TRACK-COUNT charging derivation as a front-loadable kernel unit; that
unit has NOT been executed — the REV 16 clearance rode the kernel to
THIS draft, and the mathematics did not advance. TRACK-COUNT is OPEN,
the charging derivation is owed (C10B/C15-style, fresh-context), and
SQ.0(c) — hence SQ.1's finiteness, hence everything downstream — is
CONDITIONAL on it (CL-7).

**(TRK-RULE) — the sealed assignment-rule display (the TRACK-probe's
owed input; plan §7 unrun-roster row 11's blocker, discharged HERE as a
DISPLAY).** A counting DEFINITION sealed for the probe, not a theorem.
Track-OPENING events of a canonical history H, recognized per node from
move-species cell data alone:
 (t1) KEY CREATION — a node whose move creates a new key (a fresh
   integral weight ladder, in §B2-DEF's carry-algebra language);
 (t2) BRANCH OPENING — at a branching node (m ≥ 2 members), each member
   beyond the designated continuing one opens its own track;
 (t3) LADDER RESTART — a recentering node at which the current monotone
   weight ladder is abandoned (D.10's strict-climb chain broken by the
   frame change) and a new ladder begins on the same branch.
The probe COUNT is #(t1) + #(t2) + #(t3) per history. SEALED CANDIDATE:
L(n) ≤ n², i.e. L(3) = 9, L(4) = 16. HONESTY CLAUSE: the probe consumes
ONLY the event recognition (t1)–(t3) (per-node data); the assignment
MAP of (c1) — each zero-gain move to the open ladder its D.10 increment
extends — and that map's well-definedness are TRACK-COUNT's
charging-derivation duty, NOT sealed by this display.

**TRACK-probe (exploration-class; scope restated per plan REV 7 — a
CANDIDATE-REFUTER only).** On the STALL-probe boxes (the exhaustive 2²⁴
cubic box at N = 8 and the 2²⁶ quartic conditioned cylinder at N = 10):
extract each f's canonical history and count its track-opening events
under (TRK-RULE); ONE f exceeding the candidate L(n) refutes THAT
CANDIDATE before SQ.0 is finalized around it. SCOPE: the existential
TRACK-COUNT statement (SOME L(n) exists) is decided by the charging
derivation alone, never by the probe (plan §7's probe-language clause).
ACTIVATED by the REV 16 clearance; runs with the STALL-probe (roster
rows 3/11).

### SQ.1 The budgeted covering + the envelope side (SQ.3's X-leg, hypothesis-displayed)

**The partition (TREE-FIBER form, plan REV 8/12).** Every f in the
level-N box lies in EXACTLY ONE of:
 (a) the T_can^τ-FIBER of one complete finite realizable canonical tree
   T, all branches τ-halted ([3t] VP), with thr(T) ≤ N; or
 (b) Undec(N).
PARTITION, not mere covering: T_can^τ is a CHOICE-FREE function of f
([1] L2 + VP; [3t] ONE-F's totality) — NEVER via per-shape strata,
which are a multiplicity-weighted cover (F1). Fiber identification:
D4R.0's digit-cell partition + L6/L7 tree membership, with the
prefix/complete distinction per plan §2. The level-N fiber COUNT is
[3t] TREE-N, consumed as the dual-accepted statement (quoted): for
every N ≥ thr(T),
  #{ f mod p^N : T_can^τ(f) = T } = p^{nN} · μ(fiber T)
— an exact union of level-N residue classes; the per-fiber MASS is [3t]
TREE-EXP-fin GIVEN (SIB) — CL-10's tags ride every consumption. (ns)
ROUTING ((NS-ROUTE), verbatim duty): clause (a)'s trees are
AUTOMATICALLY 𝒯^fin — a finite threshold (TREE-N's thr joined with the
TB-CAP caps) EXISTS only when every leaf is (τ-irr)/(τ-hen) ((NS-a));
ns-leaf fibers lie in Undec(N) at EVERY N ((NS-d)), are accounted on
the envelope side, and carry limit mass 0 GIVEN (ns-null)
[PROVED/CLOSED at plan REV 15; the tag stays displayed per (NS-c)'s
rule]. FINITENESS of family (a): SQ.0 ALONE (the rev-3 conjunction is
retired; no X.1b anywhere in the partition). Consequently, at every N:
  (BOX-N)   p^{nN} = Σ_τ decided_τ(N) + undec(N)
— the box partition, EXACT and tag-free as an identity of counts — and
decided_σ(N) = Σ_{T : typemult(T) = σ, thr(T) ≤ N} #fiber(T) is a
FINITE sum (SQ.0/CL-7) of exact fiber counts (TREE-N/CL-10).

**The envelope side (env(N)'s two claims — §X-EXHAUST consumed as
accepted text, its honesty inherited verbatim).**
- QUALITATIVE [X.3 = CL-4, cited as [5]'s dual-accepted statement WITH
  its own displayed tags — the infinite-branch leg's disjunction
  [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)], VP-SOUND, the
  (ns-null) tag]: μ(Undec(N)) → 0 as N → ∞, and for each type σ the
  tree-fiber series sums the full density. X.3 discharges ONLY at [5]'s
  acceptance EVENT — the note acceptance did NOT discharge it (plan
  §0's rule).
- QUANTITATIVE [DISPLAYED HYPOTHESES, owed by [5]'s EVENT; constants
  named per §X-EXHAUST X.2]: GIVEN (X.2)'s linear form + both mass legs
  + the bridge — i.e. (X2-AFF), (X2-CAP), (X2-BRIDGE), (X2-TAILS)
  ([2b]-owed), and the deep leg's X.1b/WEIGHT-CHARGE ∧ (ALIGN-inc) —
    env(N) ≤ c₃(n)·p^{−c₄(n)·N},
  the constants traced to s(n), c₀, C_T, c_T, c_cap; GIVEN instead the
  √N fallback set ((X2-HYP) + (X2-AFF) + (X2-CAP) + (X2-BRIDGE) + the
  same two leg tags): env(N) ≤ c₃′(n)·p^{−c₄′(n)·√N} — subexponential,
  enough for the qualitative limit's rate flavor, NOT for the gate's
  bracket constants.
- §X's TOOTHLESS-ENVELOPE HONESTY, carried verbatim (X.5(iii)): at the
  sealed candidates env*(N) > 1 at EVERY N ≤ 8, both primes — the
  assembled envelope has NO teeth at census range; it is displayed for
  shape only and never sold as falsifiable there. Every consumer of the
  quantitative form in THIS note (the gate's theory-env lower leg)
  inherits that honesty line.

### SQ.2/SQ.3 The squeeze induction — the two-sided general-n bound

**SQ.2 (the fixpoint upper bound; the n = 2 (U) analogue).** For every
N and σ:
  decided_σ(N) ≤ R_σ(p)·p^{nN}   [hypothesis stack at (U-n) below].
ROUTE (plan REV 2 form, run on §S's FROZEN displays — every leg cited
WITH its S.6 hypothesis set, none re-derived). By SQ.1 + TREE-N,
decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
positive tree-fiber series for type σ. That series' full sum equals the
block solve through RS.1-SH (§S S.2, quoted):
  R_σ = Σ_Ŝ W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ … ⊎ σ_{k(Ŝ)}}
        ∏_{i=1}^{k(Ŝ)} β_{e_i(Ŝ),τ_i(Ŝ)}(σ_i)(q^{δ_i})
— TONELLI, retyped to exactly what it gives (rev 2, pass-1 critical
7): the positive series has a well-defined EXTENDED-VALUE sum in
[0, ∞] unconditionally (nonnegative terms; §S's display; the envelope
is needed only for RATES, never here); FINITENESS of that sum and its
IDENTIFICATION with R_σ(p) are NOT Tonelli's — they carry the tagged
stack: the fiber/mass interfaces TREE-N/TREE-EXP-fin (CL-10's tags),
the CL-5 mass identification, per-pool ESCAPE(E0) (CL-1), the CL-8
(e1)–(e5) legs, and RS.1-SH's assembly (CL-17). The solve
DOMINATES every partial sum by MATRIX MONOTONE ITERATION on §S's
displayed recursion (R_e-lump) β_e = K_eβ_e + b_e^{term,fin} +
b_e^split: with K_e ≥ 0 entrywise at q = p (the CTS-M(iv)/(K-SUB) typed
rows — §S S.0's displayed consumption, GIVEN the CL-5 nine-input
ledger), the depth-k Neumann partial sums increase to
(I − K_e)^{−1}b_e, converging by per-pool ESCAPE(E0)/CL-1 at the FIXED
evaluation q = p (per-p suffices, no uniformity consumed;
CONDITIONAL-ON-E0 until that kernel closes), with RS.3's positivity
((I − A(q₀))^{−1} ≥ 0) and R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN
E0 + the CL-5 mass identification, never formal solvability alone.
INDUCTION in cluster size e: every base-changed leg β_{e_j,τ_j}(q^{δ_j})
of b_e^split and of RS.1-SH enters as a [2r] REL.3 STATEMENT over O_δ,
cited by its CL-8 obligation names (e1)–(e5) — a certified input at a
strictly smaller block, never a formal substitution; ALL FIVE stay open
AS PROOFS (plan §0's [2r] row). Numeric evaluation at a pool q₀ = p^δ
is guarded by §S S.4's per-pool E0/ACT + the (e3)-FENCE, cited not
re-derived.

**The no-equal-e-feedback check (CL-11 — THIS note's displayed kernel
duty; plan §6 Kernels).** The well-founded order: (cluster size e;
within e, the Neumann iteration index). Base-changed hypotheses enter
ONLY at strictly smaller e and ONLY through REL.3. The check that no
(e, τ) leg feeds back at equal e outside M_e — the one place a
circularity could hide — reduces, on the frozen text, to: (i) equal-e
continuation rides EXCLUSIVELY in K_e's (c = 1, m = 1) rows ((K-SUB)'s
(m, c) classification, §S S.0 — the same-size single-child direction);
(ii) every b_e^split leg has e_j < e — (K-TRI)'s well-foundedness,
DERIVED in §S GIVEN DEG-CONS/CL-11's full-roster per-outcome degree law
(a [1v] display duty, OPEN). The check is DISPLAYED here and rides
CL-11's roster check; it is not independently closed by this note.

**SQ.3 (the lower bound — DERIVED from SQ.2 + the checksum; the
envelope enters ONLY to bound env(N)).** For every N and σ:
  decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN},
by exact arithmetic on (BOX-N): decided_σ(N) = p^{nN} −
Σ_{τ≠σ} decided_τ(N) − undec(N) ≥ p^{nN}·(1 − Σ_{τ≠σ} R_τ(p) − env(N))
= (R_σ(p) − env(N))·p^{nN}, applying SQ.2 to every τ ≠ σ and RS.4's
checksum Σ_τ R_τ = 1 (§S S.5, consumed WITH its full inherited set —
the standing tag rides in verbatim: E0, the CL-5 nine, RS.1's set,
X.3/CL-4, and the whole RS.2 rationality chain incl. (J-RAT)/CL-18).

**(U-n) THE TWO-SIDED GENERAL-n BOUND (displayed — this note's
product).** For every n, σ, N, and EVERY prime p satisfying (REG-p)
(SQ.4's named regularity schema — the qualifier binds the DISPLAYED
BOUNDS themselves, rev 3, pass-2 critical 7: at a p failing (REG-p)
neither inequality is asserted, R_σ(p) being unadjudicated there):
  (U-n)   (R_σ(p) − env(N))·p^{nN}  ≤  decided_σ(N)  ≤  R_σ(p)·p^{nN}
— the UPPER side GIVEN the finiteness stack {SQ.0's budgets with
TRACK-COUNT + D(n) + the genuine-increment sub-claim (CL-7); the [3t]
package (CL-10)} AND the solve stack {E0 (CL-1); the CL-5 nine; CL-6;
the CL-8 (e1)–(e5) legs; CL-9's displayed set (XRB
proved-under-hypotheses); CL-11; CL-13…CL-16's table inputs; CL-17;
CL-18; CL-19}; the LOWER side additionally GIVEN RS.4's inherited set
(X.3/CL-4 included). With env(N) → 0 (X.3/CL-4, the QUALITATIVE form —
the limit consumes no envelope constant):
  ρ_σ(p) := lim_{N→∞} decided_σ(N)/p^{nN}  EXISTS and  = R_σ(p),
at every such p — the same (REG-p) qualifier heading the display
(SQ.4's schema; rev 5, the Fable D-G2 repair: (REG-p) is a SEPARATE
NAMED HYPOTHESIS — RELATED to but NOT identical with the solve stack's
E0/CL-1 and ACT/CL-5 citations: (r1) demands the FULL determinant
(junk blocks included), which §S's S.4 does not require, and (r1) does
not supply E0's spectral condition; neither implies the other. The
direction is conservative — a p failing (REG-p) is simply not
adjudicated). The RATE form (gate SQUEEZE-n3's theory-env bracket)
substitutes X.2's envelope bound for env(N) and additionally inherits
CL-2/CL-3 + the (X2-*) family, WITH §X's toothless-honesty line.

### SQ.4 = THEOREM U — the campaign's target statement, in the FULL HONEST FORM

> **THEOREM U (CONDITIONAL — on the COMPLETE capstone ledger below;
> neither this display nor any acceptance record may drop a tag while
> any cited CL-item is open — plan §7's acceptance-record rule).** Fix
> n ≥ 2. For each splitting type σ of degree n (a multiset of pairs
> (e_i, f_i) with Σ e_i·f_i = n) there is ONE fixed rational function
> R_σ ∈ ℚ(q) — the p-independent Cramer/adjugate solution of the block
> system (R_e), assembled through RS.1-SH (§S S.2/S.3) — such that for
> EVERY prime p, WILD primes included:
>   ρ_σ(p) := lim_{N→∞} decided_σ(N)/p^{nN}  exists and equals R_σ(p),
> and ρ_σ(p) IS the splitting density of type σ over ℤ_p — the
> undecided complement has mass 0 and the classifier verdicts are the
> true factorization types (X.3/CL-4 + [3t] VP, with VP-SOUND's
> citation duty). Σ_σ R_σ = 1 identically in q (RS.4). NAMED
> HYPOTHESIS (REG-p), PER-POOL REGULARITY AT p (rev 3 SCHEMA, pass-2
> critical 6 — quantified explicitly over the FINITE ENTRY LIST the
> solve consumes; rev 5, the Fable D-G2 repair: (REG-p) is a SEPARATE
> hypothesis for the EVALUATION step — related to, but neither implied
> by nor implying, §S's per-pool ESCAPE(E0)/CL-1 and the CTS-M(ii)
> ACT agreement (ii-c)/CL-5: (r1)'s full determinant covers junk
> blocks S.4 excludes, and (r1) gives no spectral bound). Let Q(p) := the finite set of pools q₀ = p^δ
> arising for p (one per base-change depth δ in RS.1-SH's assembly).
> (REG-p) holds iff for EVERY q₀ ∈ Q(p) and EVERY block e:
>  (r1) det(I − K_e(q₀)) ≠ 0; and
>  (r2) for EVERY member of the DISPLAYED ENTRY LIST
>     E(e) := { each entry of K_e }
>          ∪ { each entry of b_e — BOTH components b_e^{term,fin}
>              and b_e^split, every per-cell J entry (CL-18)
>              included }
>          ∪ { each entry of ι_e }
>          ∪ { each W_Ŝ coefficient }
>          ∪ { each entry of every β_{e,τ} = (I − K_e)^{−1}b_e — the
>              base-changed legs β_{e_j,τ_j}(q^{δ_j}) the assembly
>              consumes, at every pool of Q(p) },
>     the fixed ℚ(q)-element's literal evaluation at q₀ is DEFINED
>     (q₀ is not a pole of it) AND AGREES with its ACT active value
>     at q₀ (CTS-M(ii)/(ii-c); §S S.4).
> The quantifier "for EVERY prime p" reads: every p satisfying
> (REG-p). UNDER (REG-p), the literal evaluation R_σ(p) of the fixed
> element of ℚ(q) is DEFINED and IS the active value — the two
> readings coincide, so ρ_σ(p) = R_σ(p) is well-typed. WILD-p
> READING: R_σ(p) at a non-all-active pool is read through the ACT
> semantics with the per-pool active-value agreement sealed ((r2)).
> At a p where (REG-p) FAILS, THIS THEOREM MAKES NO CLAIM: that p is
> a FAIL to adjudicate — no equality, no bound, and no statement
> about ρ_σ(p) or R_σ(p) is asserted. NOT ASSERTED (rev 3, pass-2
> critical 6's failure-semantics correction): that no value exists —
> a failure can be a REMOVABLE AUXILIARY ZERO (a vanishing
> det(I − K_e(q₀)) whose cancellation is removable in the final
> reduced R_σ) or a bare active-value disagreement; the reduced fixed
> R_σ may have a perfectly defined literal value at such a p, which
> this theorem simply does not adjudicate. NORMALIZATION (the
> honest sentence, per the standing directive): MONIC-BOX density —
> additive Haar on the monic degree-n coefficient box; the projective
> normalization and the palindromy functional equation are OUT OF
> SCOPE. O3 BASE-PIN DECLARATION (CL-12's display duty, discharged
> HERE, next to the canonical-policy/offset-P convention it rides): the
> pinned base digit section is TEICHMÜLLER (D4R0K S1.4 (B4)/O3) —
> adopted by the decomposition note's choice-function clause and
> consumed by Theorem A's base case; declared once, as the definitive
> write-up must.

**The COMPLETE conditionality — THE CAPSTONE LEDGER, quoted VERBATIM
from plan §6 SQ.4 (CL-1…CL-19, the REV 16 extent; dedented only). Every
other conditionality list in the campaign is a POINTER into this
display:**

> **THE CAPSTONE LEDGER (canonical, REV 9; CL-1…CL-19 at REV 16).**
> CL-1 ESCAPE(E0) — the active-block solvability kernel (§4).
> CL-2 X.1b WEIGHT-CHARGE — via X.2's env constants only (§5).
> CL-3 X.2 PROGRESS itself — the coercivity dichotomy with its constants,
>   consumed by SQ.3/SQ.4 and every envelope gate layer (§5).
> CL-4 X.3 termination a.e. — consumed by E0's route, RS.4's total-mass
>   identity, and (TGT)'s undecided-complement clause (§5, §4t).
> CL-5 the NINE RS.PRE inputs (§4/§2v): XHD = M4a-X; D4R.0; CTS-M(iv)-PART;
>   CTS-M(iv)-REP = M2(ii); CTS-M(iv)-MEAS; CTS-M(v) HMC; CTS-M(ii) ACT;
>   CTS-M(iii) INIT + ENT-COUNT (per-entrance-shape, h_ent-indexed, with
>   ENT-AGG/INIT-RAT); the CTS-M(vi) COMP-typing duty.
> CL-6 CTS-M(iv)-POLY — through RS.2; without it R_σ ∈ ℚ(q) and
>   p-independence are unfounded (§2v).
> CL-7 TRACK-COUNT + its D(n) and positive-genuine-increment companions —
>   through SQ.0/SQ.1; without them no finite decided family (§6).
> CL-8 REL.1 + REL.2(a)/(b)/(d)/(e) + REL.3 — the relative measure
>   statements, FIVE named REL.2 obligations at REV 15 (§R-LEDGER rev 2
>   added (e), the β-typing leg: the (e1)–(e5) checklist tying [3]'s
>   entry β_{e_j,τ_j(c)}(p^{δ_j}) to the REL.1 mass — §3r); (c)'s
>   content lives at CL-10's (SIB) (§3r). The [2r] note is dual-accepted
>   as a LEDGER (REV 15); every CL-8 item stays OPEN until its own pass.
> CL-9 RS.0 (α) lumpability consumed + (β) height-shift bisimulation (§4)
>   — (β) IS the prover of XRB, [3t]-COND's displayed height-elimination
>   hypothesis package (§4t, REV 13): proved in [3], discharged at the
>   acceptance-only edge [3] → [3t]-FULL.
> CL-10 the [3t] TREE-ASSEMBLY package (§4t): (SIB) — OPEN in its
>   MEASURE-LEVEL form (REV 11: joint-fiber equidistribution of the
>   cross-sibling read map; coordinate disjointness refuted; SIB-gate
>   PASSED 32/32, supports not closes; the residual kernel named
>   (SIB-STEP) in its JOINT-VECTOR form, REV 12 + the unimodularity
>   mechanism, §T.3(iv)) — with its PCI
>   interface (REL.2(a)/(b)/(d) + CTS-M(iv)-REP + XRB — REV 13, pass-12
>   critical 2: the height-elimination HYPOTHESIS package, consumed
>   hypothetically at [3t]-COND, proved by [3] as RS.0(β)/CL-9,
>   discharged at [3t]-FULL; PCI is consumed ONLY at the β-substitution
>   sites, NEVER by TREE-EXP — no [3t] ↔ [3] cycle);
>   TREE-EXP (-fin/-ns split) + TREE-N, both
>   (NS-ROUTE)-scoped (REV 12; TREE-N's ns clause on the LUMPED fiber
>   T[N], REV 13); VP = the D4R.0-K(c) pin
>   with duties (c2) exactly-one-verdict, (c3-b) = TB-CAP adjudicated
>   PER CLAUSE (§T.2, REV 11: (τ-hen) cap N_V = 1 PROVED; (τ-irr)
>   per-realized-cell cap PROVED, perimeter-conditional; (τ-ns) NO
>   uniform cap — pro-cylinder, REPLACED by (ns-lump) [proved] +
>   (ns-null) [PROVED/CLOSED at REV 15 — the single-state admissible-Z
>   argument survived the §T-ASSEMBLY dual bar (rev 7, four independent
>   verifications; ONE status governing, §4t); REFUTER CHANNEL, honest
>   scope: the finite-lump decay census — T-n3's lump layers falsify a
>   SEALED lump mass or decay rate at finite N — while NULLITY ITSELF
>   (the all-depth assertion) is PROOF-ONLY: finitely many
>   positive-mass lumps are compatible with a null intersection, so no
>   finite census can refute it; it closes or falls by derivation +
>   dual passes alone], routed plan-wide by (NS-ROUTE);
>   the blanket uniform wording
>   REFUTED), and VP-SOUND (a citation obligation — the PARI-oracle
>   refuters test IT, never the caps). Without CL-10 the
>   solve computes marked-branch totals, not densities — pass-8
>   critical 1.
> CL-11 SQ.2's no-equal-e-feedback check (§6 kernel) + DEG-CONS, the
>   per-outcome degree-conservation law licensing b_e^split's
>   strict-smaller-block well-foundedness (RS.PRE — derivable from M1;
>   the full-roster per-outcome check a display duty of the [1v] table
>   build; REV 10, pass-9 concern 5).
> CL-12 perimeter conditionality (SYNCHRONIZED at REV 11, pass-10
>   critical 2): §C DUAL-ACCEPTED at rev 14 (Codex 16+17 + Fable
>   confirm; the (SAE) repair LANDED — CLOSED); §B2-DEF DUAL-ACCEPTED
>   (D¹¹d — CLOSED); [1] §D4-R DUAL-ACCEPTED at rev 9 with kernel
>   D4R.0-K parts (a) totality + (b) digit-cell exhaustiveness
>   DISCHARGED (dual-verified derivation rev 3 — CLOSED); the kernel's
>   residual (c) = VP lives at CL-10, not here. O3 RESOLVED (REV 12,
>   pass-11 critical 1): D4R0K's O3 base-digit-section item is NOT an
>   open obligation — the section IS PINNED inside the dual-verified
>   derivation itself (S1.4 (B4): Teichmüller, the decomposition note's
>   choice-function clause, adopted and consumed by Theorem A's base
>   case — "CLOSED given the pin"), and O3's own text records only the
>   bookkeeping duty "the definitive write-up should declare it once,
>   next to the offset-P paragraph". That residue is a DISPLAY DUTY of
>   the capstone statement (owner [4], carried at SQ.4's closing
>   sentence below), never a mathematical residual — NOTHING at CL-12
>   is open, and the D4R.0-K residual is (c) = VP alone (CL-10).
>   PERIMETER SYNC (REV 15; extended REV 16): §T-ASSEMBLY (rev 7),
>   §V-TABLES (rev 7), §M-SPECIES (rev 8), §R-LEDGER (rev 5), and at
>   REV 16 §X-EXHAUST (rev 8), §H-DOMAINS (rev 6), §S-RESUM (rev 6)
>   are additionally DUAL-ACCEPTED as notes — TEN artifacts through
>   the full dual standard, the entire write-up drafted to date;
>   their event-level duties are NOT CL-12 items and stay tracked at
>   CL-1/CL-2/CL-4/CL-5/CL-8/CL-10/CL-13/CL-14/CL-18/CL-19 per the
>   §0 ledger.
> CL-13 CTS-M(i) SYNTAX (REV 10, pass-9 critical 2) — the ONE fixed
>   finite p-independent state set with DISPLAYED cell predicates and
>   globally compatible target-cell maps; without it no path product or
>   kernel index type-checks (§2v).
> CL-14 [2a] M1 + M5 (REV 10) — the finite exhaustive branch-shape
>   catalogue with the corrected degree bounds; every "over all
>   species/shapes" quantifier (Out(s), Theorem VAL, the entrance-shape
>   family {ε}, 𝒯_n's finiteness) reads from it (§3).
> CL-15 X.1a (REV 10) — the per-species GMN index dictionary; X.2's
>   constants and the depth ⟹ disc envelope consume it (§5).
> CL-16 M4b narrowed height-translation constancy + M4b-T equivariance
>   incl. the π_v clause (REV 10) — the count-closure interface at fixed
>   template, beyond the XHD portions already carried at CL-5 (§3).
> CL-17 the RS.1 SHALLOW-ASSEMBLY theorem (REV 11, pass-10 critical 1) —
>   the two-clause identity RS.1-DEEP + RS.1-SH (with RS.1-MARKED
>   separated), the ROUTING statement (every split at exactly one
>   multilinear site before any linear aggregation), the UNIQUE
>   SHALLOW-CUT DECOMPOSITION (exhaustive + nonoverlapping on every
>   complete tree — RS.1's displayed duty, §4), and the W_Ŝ rational
>   regrouping machinery. Without CL-17 the repaired shallow interface
>   could remain merely asserted while the ledger appears closed —
>   pass-10 critical 1's channel (§4).
> CL-18 (J-RAT) (NEW at REV 16 — owed by §S-RESUM's S.6 plan-sync flag,
>   rev 2/pass-2 finding 10; owner [1v], with [2b] on the height-sum
>   face): the PER-CELL rational branching-mass tables — per branching
>   digit cell of each outcome class o at each state τ, the cell-count
>   polynomial per the (iv)-POLY pattern + its XHD-s height sum, i.e.
>   J_{τ,o} ∈ ℚ(q) ENTRYWISE — a deliverable BEYOND PART-1's TOTAL
>   cell-partition mass, which is all the dual-accepted §V-TABLES
>   currently displays. Consumed by [3]'s b_e^split (each branching
>   cell's J once — never the marked T·G) and (K-SUB)'s third summand,
>   and cited by RS.2's rationality chain, riding RS.4's tag (§4).
>   §V-TABLES/§H-DOMAINS are ACCEPTED texts, not edited from here — the
>   owner notes' NEXT revision rounds record the deliverable; THIS
>   ledger entry is the cross-note authority binding it meanwhile.
> CL-19 (JC-INV) (NEW at REV 16 — same flag; owner [2b], the
>   joint-lumpability face alongside XHD-u's lumpability clauses): per
>   read, the JOINT digit-cell conditional law given the entrance (all
>   cells of the read jointly, branching cells INCLUDED — hence the
>   branching-cell selection law) is ONE function of the retained
>   state — invariant across representatives and admissible histories,
>   h_ent included. (u-R) does NOT supply it (single-branch marginals
>   tolerate different correlations), and (SIB) starts only AFTER
>   conditioning on the branching cell. Consumed by [3]'s XRB = RS.0(β)
>   derivation ((β-2b), §S-RESUM S.1); a surviving failure adjudicates
>   as R2's lumpability channel (one 𝒯-refinement round, then wall).

**EVERY NOTE'S CONDITIONALITY, inline (the plan §0 ledger reproduced at
the capstone — note-level dual acceptance ≠ the plan's acceptance
EVENTS, row-wise; nothing below claims beyond what the dual-accepted
notes deliver):**
- §B2-DEF (D¹¹d) + §C (rev 14): DUAL-ACCEPTED; the perimeter under
  everything — CL-12 records NOTHING open here (O3's residue is the
  base-pin display duty, discharged at this note's SQ.4 statement).
- [1] §D4-R (rev 9): note accepted; EVENT DONE — D4R.0-K (a)/(b)
  discharged by the dual-verified derivation; residual (c) = VP lives
  at CL-10.
- [2a] §M-SPECIES (rev 8): note accepted; event SATISFIED; carries the
  VP residual + the SP-FIN/SP-OUT coverage duties that [1v]/CL-13's
  (D1)–(D4) build consumes.
- [1v] §V-TABLES (rev 7): [1v]-COND SATISFIED (V-n3 178/178);
  [1v]-FULL BLOCKED on exactly [2b]'s SIX open H.6 fences —
  XHD-d-EX(∂), M4b-T-AUD, U-R-COUNT, XHD-u-X, H-LIST-GEN, E-POS — plus
  HMC an open [1v] kernel (probe specced, unrun). Owed deliverables:
  (J-RAT)/CL-18's per-cell tables (beyond PART-1's total), INIT-RAT,
  ENT-COUNT, DEG-CONS's full-roster check (CL-11).
- [3t] §T-ASSEMBLY (rev 7): [3t]-COND RECORDED with its displayed tag
  list; [3t]-FULL BLOCKED on [5]'s EVENT (X.3 discharge) AND [3]'s
  EVENT (XRB discharge) — BOTH owners now dual-accepted AS NOTES, which
  discharges NEITHER. (SIB)/(SIB-STEP) + (JC-multi) OPEN; (ns-null)
  CLOSED (tag still displayed at consumption sites).
- [2r] §R-LEDGER (rev 5): dual-accepted as an OBLIGATIONS LEDGER that
  derives NOTHING (its banner is literal); REL.1's re-scoping,
  REL.2(a)/(b)/(d)/(e), REL.3, and gate REL-n4's (g1)–(g7) are ENTIRELY
  open (CL-8). This note cites the (e1)–(e5) legs exactly as §S does —
  named open obligations, all five open AS PROOFS.
- [2b] §H-DOMAINS (rev 6): note DUAL-ACCEPTED (H-n3 PASSED 151/151);
  the [2b] EVENT stays OPEN on the six H.6 fences + STATE-probe-2.
  Owed: (JC-INV)/CL-19, the (X2-TAILS) leg, the H-n3 heterogeneous
  re-seal (roster row 7).
- [5] §X-EXHAUST (rev 8): note DUAL-ACCEPTED; the [5] EVENT stays OPEN
  on WEIGHT-CHARGE (X.1b, verbatim), (X1a-ALIGN), (X2-AFF)/(X2-CAP)/
  (X2-BRIDGE)/(X2-TAILS), VP-SOUND inherited; gate X-n3's census layers
  + the STALL-probe UNRUN. X.3/CL-4 discharges ONLY at this event.
- [3] §S-RESUM (rev 6): note DUAL-ACCEPTED in the [3]-COND form (the
  solve hypothesis-complete; XRB proved-under-hypotheses, its set
  displayed at S.1; ESCAPE(E0) the central open kernel, per-pool). The
  [3] EVENT stays BLOCKED on STATE-probe-2 + [1v]-FULL + RESUM-n3
  (whose seal artifact + (ORC-1) Krasner-radius display are owed before
  any run).
- [4] THIS NOTE: drafted in the [4]-COND form; its own open kernels are
  TRACK-COUNT + L(n), D(n), and the positive genuine-increment
  sub-claim (CL-7); gate SQUEEZE-n3 SPECIFIED, chained.

**THE EVENT DAG'S REMAINING BLOCKERS (one display; rev 3 — the [4] row
COMPLETED by the pass-2 sweep of everything SQ.1/SQ.2/Theorem U
consume, pass-2 critical 2: no event may fire on a proper subset of
its ledger row, and every consumed obligation must be REQUIRED by the
firing condition or be an explicit hypothesis of the theorem —
(REG-p) is the ONE explicit hypothesis; everything else is required
below):**
  [4] EVENT ⇐ [3] EVENT ∧ [5] EVENT ∧ [3t]-FULL ∧ [2b] EVENT
             ∧ the [2r] DISCHARGE of CL-8 (REL.1 + REL.2(a)/(b)/(d)/(e)
             + REL.3 — every PCI/REL β-substitution site SQ.2 cites)
             ∧ CL-7 CLOSED IN FULL (TRACK-COUNT + L(n), D(n), AND the
             positive genuine-increment sub-claim)
             ∧ the RESIDUAL TABLE INPUTS no row above implies:
             CL-5(iii)–(ix) ([1v]), CL-6 (iv)-POLY ([1v]), CL-13
             SYNTAX ([1v]), CL-15 = X.1a ([5]), CL-16's [1v] face,
             CL-17 beyond (ii) (the routing + unique-shallow-cut
             clauses)
             ∧ gate SQUEEZE-n3;
   IMPLICATION AUDIT (rev 3 — why this conjunction exhausts the
   consumption sweep): [3t]-FULL carries (SIB)/(SIB-STEP), (JC-multi),
   and VP-SOUND's two cites — i.e. TREE-N/TREE-EXP's CL-10 tags, which
   SQ.1's fiber counts, SQ.2's partial-sum reading, and the sibling
   products consume; [2b]'s EVENT carries (JC-INV)/CL-19, (X2-TAILS),
   CL-5(i) XHD, and CL-16's [2b] face; [3]'s EVENT carries E0/CL-1,
   CL-17(ii), and [1v]-FULL — hence the six fences, HMC, (J-RAT)/
   CL-18, INIT-RAT/ENT-COUNT, and DEG-CONS/CL-11; [5]'s EVENT carries
   CL-2, CL-3, CL-4 = X.3, and (X1a-ALIGN); CL-9 discharges at the
   acceptance-only edge [3] → [3t]-FULL; CL-12 is CLOSED and CL-14 is
   CLOSED as [2a]'s SATISFIED event (residuals route to CL-10's VP
   and CL-13's build); CL-5(ii)'s residual (c) = VP rides CL-10 at
   [3t]-FULL. Every OPEN CL-1…CL-19 item consumed by SQ.1/SQ.2/(U-n)/
   Theorem U is thereby REQUIRED — no proper subset fires [4].
  [3] EVENT ⇐ ESCAPE(E0)/CL-1 ∧ CL-17(ii) (the per-shape W_Ŝ
             production) ∧ STATE-probe-2 ∧ [1v]-FULL ∧ RESUM-n3;
  [5] EVENT ⇐ WEIGHT-CHARGE ∧ (X1a-ALIGN) ∧ the (X2-*) family
             ∧ VP-SOUND ∧ X-n3/STALL-probe run;
  [1v]-FULL ⇐ [2b]'s six H.6 fences ∧ HMC ∧ [1v]'s owed deliverables
             ((J-RAT)/CL-18's per-cell tables, INIT-RAT, ENT-COUNT,
             DEG-CONS's full-roster check (CL-11));
  [2b] EVENT ⇐ the fences ∧ STATE-probe-2 ∧ (JC-INV)/CL-19
             ∧ (X2-TAILS) ∧ the H-n3 heterogeneous re-seal;
  [3t]-FULL ⇐ [5] EVENT ∧ [3] EVENT ∧ (SIB)/(SIB-STEP) ∧ (JC-multi)
             ∧ VP-SOUND's two cites;
  SQUEEZE-n3 ⇐ RESUM-n3's sealed R_σ + env constants — the gates CHAIN.

**ACCEPTANCE SPLIT (the spec addendum, binding on this note's record;
rev 3 — synced to the completed [4] row, pass-2 critical 2).**
[4]-COND = acceptance of THIS package with all the above displayed. The
[4] acceptance EVENT additionally requires the COMPLETE conjunction of
the [4] row above — [3]'s EVENT, [5]'s EVENT, [3t]-FULL, [2b]'s EVENT,
the [2r] discharge of CL-8, CL-7 CLOSED IN FULL (TRACK-COUNT + L(n),
D(n), AND the positive genuine-increment sub-claim — rev 2, pass-1
critical 1: never droppable; SQ.0(d) is conditional on it), the
residual table inputs (CL-5(iii)–(ix), CL-6, CL-13, CL-15, CL-16's
[1v] face, CL-17 beyond (ii)), and gate SQUEEZE-n3. The [4] row IS the
firing condition; no proper subset fires it. NEITHER level may ever be
recorded unconditional while any cited CL-item is open (plan §7's
rule).

### SQ.5 Honest perimeter (derived vs open vs consumed) + gate SQUEEZE-n3

DERIVED here, each under its displayed set (site in brackets): SQ.0
(a)/(b) [GIVEN Thm 2.1 / PROGRESS mechanics — the affine
level-constraint reading]; SQ.0(d)'s Theorem-C leg [GIVEN §C +
(†-AGG)(ii); its genuine-increment sub-claim FLAGGED open]; SQ.1's
partition + (BOX-N) [(BOX-N) itself tag-free as a count identity;
the fiber counts GIVEN TREE-N/TREE-EXP-fin as accepted statements,
CL-10's tags riding; finiteness GIVEN SQ.0/CL-7]; SQ.2's domination
arithmetic [GIVEN the §S solve stack + E0 + the CL-8 legs + CL-11];
SQ.3 [DERIVED from SQ.2 + RS.4's tagged checksum]; (U-n) + the limit
[GIVEN the stacks displayed there].
OPEN KERNELS owned by THIS note (CL-7): TRACK-COUNT + its explicit
L(n); the D(n) common-denominator duty (candidate n!, underived); the
positive genuine-increment sub-claim. The CL-11 no-equal-e-feedback
check is DISPLAYED here and rides [1v]'s DEG-CONS roster duty.
CONSUMED OPEN ITEMS, owner elsewhere (cited, never proved here): E0
(CL-1, [3]); WEIGHT-CHARGE + s(n) (CL-2, [5]); the PROGRESS family
(X2-AFF)/(X2-BRIDGE)/(X2-CAP) (CL-3, [5]) + (X2-TAILS) ([2b]);
(X1a-ALIGN) ([5]); X.3 (CL-4, [5]); the nine CL-5 inputs; CTS-M(iv)-
POLY (CL-6, [1v]); the CL-8 REL legs ([2r] discharge); CL-9's
displayed hypothesis set; (SIB)/(SIB-STEP)/(JC-multi) + VP-SOUND
(CL-10, [3t]); CL-13…CL-16 ([1v]/[2a]); CL-17(ii) AND CL-17 beyond (ii) — the routing + unique-shallow-cut clauses SQ.2 consumes ([3]); (J-RAT)
(CL-18, [1v]/[2b]); (JC-INV) (CL-19, [2b]).
TYPE FENCES inherited, binding: R_σ is RS.1-SH's object and the ONLY
density in this note; no μ̂-typed marked total appears in any display
here; heights sum EXACTLY ONCE (CL-5 item 9); completed densities are
gated ONLY by two-sided brackets ((†-AGG) — no interpolation, no
truncated-census acceptance).

**Gate SQUEEZE-n3 (plan §6 feasible-exhaustive form — SPECIFIED, not
sealed; referee-derivable numbers; pass-1 obstruction 8's discipline).**
Seal, for ALL FIVE σ ∈ {(1,1)³, (1,1)+(1,2), (1,3), (1,1)+(2,1),
(3,1)}: p = 2 at N = 4, 6, 8 (2¹², 2¹⁸, 2²⁴ — exhaustive) and p = 3 at
N = 4, 5 (3¹², 3¹⁵ — exhaustive; the infeasible 3²⁴ and the circular
"stratified-exact" layer both DROPPED per the plan): the exact integers
  ⌈(R_σ(p) − env(N))·p^{3N}⌉ ≤ decided_σ(N) ≤ ⌊R_σ(p)·p^{3N}⌋,
with decided_σ(N) counted by EXHAUSTIVE enumeration under the PARI
oracle (NEVER the stratum formulas — the independence requirement), and
RESUM-n3's cylinder-decisiveness discipline riding verbatim
((ORC-1)–(ORC-4): certified determination radii; the UNRESOLVED bin
sealed as its own count; the typed equality target; symmetric
differences sealed). UPPER BOUND EXACT: ANY single-f overshoot
falsifies SQ.2. Plus the checksum row at each N. TWO LOWER-LEG
READINGS, sealed separately:
 (L-thy) the THEORY-ENV leg, env(N) := the X.2 assembled envelope at
   the sealed candidates — inherits §X.5(iii)'s honesty VERBATIM:
   env*(N) > 1 at every census N, so this leg is TOOTHLESS at census
   range (trivially true), displayed for shape only, NEVER sold as
   falsifiable there;
 (L-meas) the MEASURED-ENV leg, env(N) := undec(N)/p^{3N} from the
   census's own certified-undecided count — the discriminating lower
   layer, RETYPED (rev 2, pass-1 critical 5): by (BOX-N), for fixed σ
   this leg is EQUIVALENT to the AGGREGATE inequality
     Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ(p),   d_τ := decided_τ(N)/p^{3N},
   with no envelope hypothesis consumed. It is IMPLIED BY — not
   equivalent to — the conjunction {SQ.2 at every τ ≠ σ} + RS.4's
   checksum: individual per-τ upper-bound violations can CANCEL
   inside the sum, so a pass here SUPPORTS the conjunction without
   isolating any per-τ SQ.2; the per-τ upper legs test those
   separately.
CHAINING (plan §7 roster row 12): the brackets derive from RESUM-n3's
SEALED R_σ (S.7's seal artifact, owed) + the env constants; THIS gate
cannot be sealed before that artifact exists — a seal document
(SQUEEZE_N3_SEALED_PREDICTIONS.md pattern) must record the TWENTY-FIVE
bracket pairs — all five σ at each of the five (p, N) settings (2,4),
(2,6), (2,8), (3,4), (3,5); rev 2, pass-1 critical 4: "ten" left
fifteen specified cases unsealed — plus the five checksum rows (one
per setting) BEFORE any census runs. WHAT-THIS-GATE-CANNOT-
SEE: n = 3 exercises no μ ≥ 2 value kernel (the n = 5 layers gate
those, [1v] V-n5); two primes test evaluations, never the ℚ(q)
identity; a passing bracket SUPPORTS, never proves (plan §7
gate-epistemics); the (L-thy) leg has no teeth at census range.

### SQ.6 The campaign coda — the honest distance-to-done

What Theorem U's UNCONDITIONAL form still requires, as ONE displayed
list (owner in brackets; rev 2, pass-1 critical 3 — the list
enumerates EVERY open item the capstone ledger and SQ.5 consume,
CL-13…CL-16 and the full CL-5 nine included; rev 3, pass-2 gap —
entries whose events are already done are marked CLOSED inline, so
the exactness claim at the close is literal of the OPEN entries):
 KERNELS/OBLIGATIONS —
 1. ESCAPE(E0), per-pool q₀ = p^δ (CL-1) [[3]];
 2. WEIGHT-CHARGE = X.1b, + s(n) (CL-2) [[5]];
 3. PROGRESS: (X2-AFF), (X2-BRIDGE), (X2-CAP) (CL-3) [[5]] +
    (X2-TAILS) [[2b]];
 4. (X1a-ALIGN): (ALIGN-inc)/(ALIGN-rec) [[5]];
 5. X.3 a.e. termination (CL-4) — discharges at [5]'s EVENT given
    2/4 [[5]];
 6. the nine CL-5 inputs, ENUMERATED (rev 2 — the pointer "the nine"
    no longer substitutes for the list): (i) XHD = M4a-X (the XHD
    package + (ENT-U)) [[2b]]; (ii) D4R.0 — CLOSED ([1]'s event DONE,
    (a)/(b) dual-verified; the K-residual (c) = VP is item 10's
    CL-10; a ledger echo, NOT distance) [[1]]; (iii) CTS-M(iv)-PART;
    (iv) CTS-M(iv)-REP = M2(ii); (v) CTS-M(iv)-MEAS; (vi) CTS-M(v)
    HMC; (vii) CTS-M(ii) ACT with (ii-c) — RELATED to (REG-p)'s (r2) but a SEPARATE obligation (rev 6, the pass-6 sweep: (REG-p) is its own hypothesis, neither implying nor implied by ACT — the rev-5 clauses govern);
    (viii) CTS-M(iii) INIT + ENT-COUNT (with ENT-AGG/INIT-RAT);
    (ix) the CTS-M(vi) COMP-typing duty [(iii)–(ix): [1v]];
 7. CTS-M(iv)-POLY (CL-6) [[1v]];
 8. TRACK-COUNT + L(n), D(n), the positive genuine-increment sub-claim
    (CL-7) [[4] — THIS note];
 9. REL.1's re-scoping, REL.2(a)/(b)/(d)/(e), REL.3 (CL-8) [[2r]
    discharge];
 10. (SIB)/(SIB-STEP) + (JC-multi), VP-SOUND's two cites (CL-10)
    [[3t]];
 11. DEG-CONS's full-roster per-outcome check (CL-11) [[1v]];
 12. CL-17(ii): the per-shape W_Ŝ production; AND CL-17 beyond (ii): the routing + the exhaustive/nonoverlapping unique-shallow-cut decomposition + the rational regrouping machinery (pass-3 gap: SQ.2 consumes these — the firing condition already required them) [[3]];
 13. (J-RAT) (CL-18) [[1v]/[2b]] and (JC-INV) (CL-19) [[2b]];
 13a. CL-13 CTS-M(i) SYNTAX — the ONE fixed finite p-independent state
    set with displayed cell predicates and globally compatible
    target-cell maps [[1v]] (rev 2 addition, with 13b–13d);
 13b. CL-14 = [2a] M1 + M5 — CLOSED ([2a]'s event SATISFIED; the
    finite exhaustive branch-shape catalogue with the corrected degree
    bounds is delivered; residuals route elsewhere — VP to item 10,
    SP-FIN/SP-OUT to 13a's CL-13 build; a ledger echo, NOT distance)
    [[2a]];
 13c. CL-15 = X.1a, the per-species GMN index dictionary — DISTINCT
    from item 4's (X1a-ALIGN) proof duty [[5]];
 13d. CL-16 — narrowed M4b height-translation constancy + M4b-T
    equivariance incl. the π_v clause (beyond CL-5's XHD portions;
    distinct from item 14's M4b-T-AUD fence) [[1v]/[2b]];
 14. the six H.6 fences: XHD-d-EX(∂), M4b-T-AUD, U-R-COUNT, XHD-u-X,
    H-LIST-GEN, E-POS [[2b]] (= [1v]-FULL's fence blockers);
 EVENT BLOCKERS / UNRUN CENSUSES (plan §7 roster) —
 15. STATE-probe-2 (runnable NOW; unblocks the [2b] and [3] events);
 16. X-n3 layers + STALL-probe (runnable NOW, sealed);
 17. ESCAPE-probe layers (a)/(b) (runnable NOW; (a) is E0's genuine
    falsifier);
 18. TRACK-probe (activated by THIS draft's (TRK-RULE); runs with 16);
 19. RESUM-n3 — its seal artifact + the (ORC-1) Krasner-radius display
    owed FIRST;
 20. the SIB deg-≥5 faces; the H-n3 heterogeneous re-seal; HMC-probe;
    the n = 5 VALUE layers; REL-n4;
 21. gate SQUEEZE-n3 — chained last, behind 19.
With THIS note drafted, NO note of the campaign remains undrafted: the
remaining distance is exactly the OPEN entries of the list above —
every item named, owned, and (where empirical) either sealed or
seal-specified; the two entries marked CLOSED inline (6(ii) D4R.0 and
13b CL-14) are ledger echoes kept for CL-numbering completeness, not
distance (rev 3, pass-2 gap). Items 15–17 are the front-loaded cheap
discriminators (plan REV 16 wall status).

STATUS: drafted 2026-07-27 per the REV 16 [4] RE-RULING, in the
[4]-COND form; the spec addendum's five displays all present (SQ.0 with
TRACK-COUNT quoted verbatim + (TRK-RULE) sealed; SQ.1 + the envelope
hypotheses with §X's toothless honesty carried verbatim; SQ.2/SQ.3 on
§S's frozen displays with every β(q^δ) leg a CL-8 citation + the CL-11
duty displayed; SQ.4 = THEOREM U with CL-1…CL-19 quoted verbatim + the
§0 ledger reproduced + the O3 base-pin declaration; the acceptance
split). PROVED UNCONDITIONALLY here: nothing substantive — the only
tag-free steps (re-audited at rev 2, matching the opening): (BOX-N)'s
count identity; SQ.3's bracket arithmetic AS arithmetic; Tonelli's
extended-value existence in [0, ∞]; the env(N) → 0 limit forcing in
(U-n). OPEN KERNELS owned: TRACK-COUNT/L(n), D(n), the positive
genuine-increment sub-claim (CL-7). Gate SQUEEZE-n3 SPECIFIED (seal
artifact owed, chained behind RESUM-n3's; TWENTY-FIVE bracket pairs +
five checksum rows). TRACK-probe ACTIVATED. This draft asserts NO
acceptance-level claim. Rev 2 (2026-07-27) repaired pass 1's seven
criticals; rev 3 (2026-07-27) repaired pass 2's three criticals + one
gap (firing-condition completion, the (REG-p) schema + failure
semantics, the (U-n) qualifier, the exact list); awaits pass 3.


THE BLUEPRINT UNDER RE-AUDIT (REV 2):

# MovesU — Lean blueprint for §U-SQUEEZE (Theorem U, conditional form)
# REV 2 (post-Codex-audit, 13 findings repaired) — 2026-07-28

*Codex audit `MOVESU_AUDIT_CODEX_2026-07-28.md`: REJECT (10 crit / 3 gap). REV 2 repairs
ALL 13 in one batch; the findings→repairs table is §7. Architecture changes: `Census`
REPLACED by `ClassifierSpec` (the verdict IS the interface's canonical classifier map,
with characterizing Props — F1/F13); `SplittingType n` concrete (F11); `RegData` carries
the FULL displayed entry list + nonemptiness (F4/F10); the kernel ledger is a
`KernelStatements` pack asserted per-CL by `CapstoneLedger` (F5/F6/F7); U10 gains the
∃-ONE-fixed-R form + the density-identification conjuncts (F11/F12); exact partial-sum
identity (F3); positivity (F8); primality (F9).*

*Blueprint-writer deliverable (campaign wave 1, `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`).
Source of truth: the DUAL-ACCEPTED §U-SQUEEZE rev 7 (`lean/notes/MOVES_2026-07-24.md`,
lines ~12879–13629; Codex passes 8+9 + Fable confirm CLEAN on identical text). TARGET
(master plan §0): Theorem U machine-checked in its CONDITIONAL form — the open kernels as
NAMED HYPOTHESES, never axioms. Upstream objects (MovesS's solve, MovesX's envelope,
MovesD's trees) enter as HYPOTHESIS STRUCTURES: self-contained now, instantiable later.
Protocol L: verbatim names, statements re-bound at use, explicit DAG.*

Discipline: NO new axioms; the statement-fence holds; every structure field is a trust
surface flagged for the Codex semantic audit (§4). `sorry`-free ≠ non-vacuous.

---

## 0. What §U-SQUEEZE is, in one paragraph

The level-N monic coefficient box (p^{nN} classes) is partitioned by the choice-free
canonical-tree verdict into decided-of-type-σ and undecided; (BOX-N) is the exact count
identity. The decided count is bracketed two-sidedly against §S-RESUM's fixed rational
R_σ ∈ ℚ(q): decided_σ(N) ≤ R_σ(p)·p^{nN} (SQ.2 — partial sum of a positive series
dominated by its fixpoint) and decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN} (SQ.3 — pure
arithmetic from (BOX-N) + SQ.2-at-every-other-τ + RS.4's checksum). env(N) → 0 then
forces ρ_σ(p) = lim decided_σ(N)/p^{nN} = R_σ(p) at every prime p satisfying the named
regularity schema (REG-p). Nothing substantive is unconditional: the note's exactly FOUR
tag-free steps are (BOX-N); SQ.3's bracket arithmetic AS arithmetic; Tonelli's
extended-value existence in [0, ∞]; and the env(N) → 0 ⟹ limit forcing. Everything
density-typed rides the capstone ledger CL-1…CL-19.

## 1. Design decisions (D1–D9)

**D1 — Splitting types are CONCRETE (F11).** `SplittingType n := {σ : Multiset (ℕ × ℕ) //
(∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧ (σ.map fun x => x.1 * x.2).sum = n}` — literally the
note's "a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n". A Fintype instance is unit
U0b (entries bounded by n). No abstract label type anywhere; `hn : 2 ≤ n` now has
semantic force (the type is the real one).

**D2 — The box is concrete; the verdict is THE CLASSIFIER INTERFACE (F1/F13).**
`Box p n N := Fin n → ZMod (p ^ N)` (`Nat.card = p^(n*N)`). `Census` is DELETED. In its
place `ClassifierSpec n p` — the MovesC-precedent interface structure (cf. MovesD's
`PrefFamily` carrying jet/enc/hist_inj), owner MovesD + HC-2 (the OM engine) — carries:
`trueType N f` (the GROUND-TRUTH factorization type of the level-N class, abstract here,
the ONE semantic pin; owner HC-2); `canonical N f` (T_can^τ's verdict-type map — "a
CHOICE-FREE function of f", [1] L2 + VP + ONE-F); `canonical_sound` (a decided verdict
AGREES with `trueType` — VP/VP-SOUND at interface strength); `canonical_stable` (a
level-N decision persists to every N' ≥ N along `ZMod.castHom` reduction — TREE-N's
thr ≤ N join / Thm 2.1 decision stability). `decided`/`undec`/`env`/`dmass` are DEFINED
from `canonical` — an arbitrary labeling is no longer an instance: the verdict function
is pinned to the named upstream object with its characterizing Props. (BOX-N) stays a
tag-free count identity (it holds for the interface's canonical map by counting alone).

**D3 — Tonelli is typed in ℝ≥0∞** (unchanged). `seriesSum σ := ∑' T, mass σ T` exists
UNCONDITIONALLY (`ENNReal.summable`); partial sums are dominated (`ENNReal.sum_le_tsum`,
`ENNReal.tsum_eq_iSup_sum`). Rev 2's retyped SQ.2 clause verbatim: existence tag-free;
FINITENESS and IDENTIFICATION with R_σ(p) are ledger fields.

**D4 — FiberSeries is tied to the actual tree family (F2).** `FiberSeries` now carries
`thr : ∀ σ, Tree σ → ℕ` (each tree's decision threshold — "a finite threshold EXISTS",
(NS-a)) with the CHARACTERIZATION `mem_slice_iff : T ∈ thrSlice σ N ↔ thr σ T ≤ N` (the
slice IS the thr ≤ N slice; `slice_mono` becomes derivable and is dropped), plus
`slice_exhausts : ∀ T, T ∈ thrSlice σ (thr σ T)` (definitional corollary, kept explicit
for the audit). The tie to the CLASSIFIER is the ledger's `finiteness_stack` IDENTITY
(TREE-N): decided_σ(N) = p^{nN}·Σ_{thr≤N} mass — so `Tree σ` can be empty ONLY when the
canonical classifier never emits σ at any level (decided ≡ 0 is then forced, not
smuggled). The Finset type of `thrSlice` is still CL-7's finiteness riding the
instantiation (TRACK-COUNT + D(n) + genuine-increment, OPEN — named in KernelStatements,
D7).

**D5 — (REG-p) is a Prop schema over the FULL displayed entry bundle (F4/F10).**
`RegData p` now carries: `depthSet : Finset ℕ` with `one_mem_depthSet : 1 ∈ depthSet`
(the base-change depths of RS.1-SH's assembly, owner MovesS; δ = 1 always arises) and
`pool_eq : Pool = depthSet.image (p ^ ·)` — Q(p) is EXACTLY the pool set, nonempty by
construction (p ∈ Pool), never an arbitrary Finset; `Block` with `instNe : Nonempty
Block` (the top block exists); the matrices `K`; AND ALL remaining displayed entry
families as data: `bterm`/`bsplit` (both b_e components), `Jcell` (the per-cell J
entries, CL-18), `iota` (ι_e), `Wcoef` (the W_Ŝ coefficients), `betaLegs` (every
β_{e,τ} entry, all base-changed legs). `entryList e` is a DEFINITION — the union of the
seven families, exactly SQ.4's displayed E(e) — not a free field, so (r2) quantifies
over the whole display and nothing can be silently dropped. `act` stays abstract
(CTS-M(ii)'s semantics, owner [1v]); RegP stays the rev-5 SEPARATE hypothesis.

**D2 — Tonelli is typed in ℝ≥0∞.** The tree-fiber series (RS.1's positive series) lives
in `ℝ≥0∞`: `seriesSum σ := ∑' T, mass σ T` exists UNCONDITIONALLY (`ENNReal.summable` —
every ℝ≥0∞ family is summable), and every finite partial sum is dominated by the tsum
(`ENNReal.sum_le_tsum`, `ENNReal.tsum_eq_iSup_sum`). This is rev 2's retyped SQ.2 clause
verbatim: existence tag-free; FINITENESS (`seriesSum σ ≠ ⊤`) and IDENTIFICATION with
R_σ(p) are ledger fields (the tagged stack), never Tonelli's.

**D3 — Finiteness of the decided family is DATA-level.** `FiberSeries.thrSlice σ N :
Finset (Tree σ)` — the thr ≤ N slice is Finset-typed, so SQ.0/CL-7's finiteness
(TRACK-COUNT + D(n) + the genuine-increment sub-claim) rides the INSTANTIATION: whoever
builds a `FiberSeries` from MovesD trees must produce the Finset, which is exactly CL-7's
open duty. Flagged in the docstring; no silent strengthening — the abstract corpus never
proves finiteness, it consumes it.

**D6 — Literal evaluation.** `evalℝ S σ p := ((S.R σ).eval (RingHom.id ℚ) (p:ℚ) : ℝ)`
(Mathlib `RatFunc.eval`, junk-valued at poles). The theorem NEVER consumes `evalℝ` except
under `RegP D`, where the ledger's solve-stack field asserts the identification — so the
junk case is never load-bearing. The WILD-p/ACT reading is carried by (r2)'s agreement
clause inside `RegP`, exactly the note's "the two readings coincide, so ρ_σ(p) = R_σ(p)
is well-typed".

**D7 — The kernel ledger: a `KernelStatements` pack + per-CL assertion fields
(F5/F6/F7).** The open kernels are STATEMENTS owned upstream; MovesU cannot re-state
their content, but it CAN carry them as named Prop-valued parameters. `KernelStatements`
is a structure of ~30 `Prop` fields — one named slot per open kernel/obligation of the
capstone ledger (escapeE0, weightCharge, progressX2 with the (X2-*) family, the CL-5
nine individually, ivPoly, trackCount/dnDuty/genuineIncrement, the six CL-8 REL legs,
rs0LumpBisim, sib/sibStep/jcMulti/treeExpNs/vpSound, noEqualEFeedback/degCons,
ctsmSyntax (the move menus, empty-menu/(BDY) conventions, target-cell maps — F7),
ksubM1C1 (the (m,c) classification incl. the equal-e m = 1, c = 1 rows — F7), m1m5,
x1aDict, m4bConstancy, rs1Assembly, jRat, jcInv) — filled with the REAL statements at
instantiation (owners named per field). `CapstoneLedger` then has a field PER CL ITEM
(`cl1_escapeE0 : K.escapeE0`, …, `cl19_jcInv : K.jcInv` — CL-2/CL-3 INCLUDED even though
the qualitative limit never uses their constants: the frozen theorem is conditional on
the COMPLETE ledger, F6) PLUS the four operative consumption fields (`finiteness_stack`,
`solve_stack` — now with EXPLICIT positivity, F8 —, `rs4_checksum`/`rs4_eval`,
`cl4_env_tendsto`), each operative docstring naming the CL items whose consequence it
is. Every kernel is now a REAL hypothesis field, not a docstring (F5). (REG-p) is NOT a
ledger field: the ONE explicit hypothesis (rev 3, pass-2 critical 2).

**D8 — NO-CLAIM failure semantics = the restricted quantifier, no Lean artifact.** The
theorem's conclusion is `∀ p, p.Prime → RegP D → (...)`. At a p failing (REG-p) the
implication is vacuously satisfied — Lean asserts NOTHING there: no equality, no bound,
no non-existence (the removable-auxiliary-zero case needs no encoding). This is the
note's failure semantics EXACTLY, for free. Design note only; no unit.

**D9 — The intended instantiation chain, and the non-vacuity boundary (F13).** The
interfaces are pinned to named upstream objects with owners: `ClassifierSpec` ←
MovesD's T_can trees + the OM engine's factorization types (HC-2 — `trueType` is the
semantic anchor; instantiating it with anything but the true ℤ_p factorization type is
an instantiation-fidelity violation adjudicated at the HC-2 audit, exactly like
MovesC's `JetSetup`); `FiberSeries` ← MovesD/[3t]'s complete finite realizable trees
with TREE-N thresholds; `SolveData`/`RegData` ← MovesS's block solve ([3]);
`KernelStatements` ← the owner notes per field ([3], [5], [2b], [2r], [1v], [3t], [4]).
What the abstract corpus CAN pin, it now does (canonical soundness + stability, the
slice characterization, the full entry list, pool/block nonemptiness, concrete
SplittingType); what it CANNOT pin (that `trueType`/`canonical`/the kernel Props are the
real ones) is exactly the conditional-over-interface boundary of the MovesC precedent,
declared here and at every consuming unit. The audit's fake instance is dead: constant
verdicts now contradict `canonical_sound` against any faithful `trueType`, `RegP` is
never vacuous (Pool ∋ p, Block nonempty), and `K.trackCount := True` etc. is a
fidelity violation caught at instantiation review, not a satisfiable reading of THIS
corpus's claims.

**The four TAG-FREE units** (= the note's re-audited unconditional perimeter, and the
only units proved without ledger fields): `U1_boxN`, `U2_tonelli`, `U5_sq3_arith`,
`U7_squeeze`. Everything else consumes hypothesis-structure fields and says so.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesU/Defs.lean` (inline; elaboration-phase target)

```lean
import Mathlib
namespace LeanUrat.MovesU
open Filter Topology ENNReal

/-- A splitting type of degree n: "a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n"
    (SQ.4, verbatim; entries ≥ 1). CONCRETE — F11's repair. Fintype: unit U0b. -/
def SplittingType (n : ℕ) : Type :=
  {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n}

/-- The level-N monic coefficient box: n free coefficients mod p^N (p^{nN} classes). -/
abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

/-- The level reduction Box p n N' → Box p n N for N ≤ N' (`ZMod.castHom`, p^N ∣ p^N'). -/
noncomputable def boxProj (p n : ℕ) {N N' : ℕ} (h : N ≤ N') : Box p n N' → Box p n N :=
  fun f i => ZMod.castHom (pow_dvd_pow p h) _ (f i)

/-- THE CLASSIFIER INTERFACE (F1/F13 repair; replaces Census). HYPOTHESIS STRUCTURE,
    owner MovesD + HC-2 (the OM engine) — the MovesC `JetSetup` precedent.
    `trueType`: the GROUND-TRUTH factorization type of the level-N class (abstract; the
    semantic anchor, D9). `canonical`: T_can^τ's verdict-type map — "T_can^τ is a
    CHOICE-FREE function of f" ([1] L2 + VP; [3t] ONE-F); `some σ` = complete finite
    realizable tree, all leaves (τ-irr)/(τ-hen), certified at level N (thr ≤ N).
    `canonical_sound`: "the classifier verdicts are the true factorization types"
    (VP + VP-SOUND's citation duty, at interface strength). `canonical_stable`:
    TREE-N's join / Thm 2.1 decision stability — a decision persists upward. -/
structure ClassifierSpec (n p : ℕ) where
  trueType : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_sound : ∀ N f σ, canonical N f = some σ → trueType N f = some σ
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ

variable {n p : ℕ}

/-- decided_σ(N) — DEFINED from the canonical map (never a free field). -/
noncomputable def ClassifierSpec.decided (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.canonical N f = some σ}
/-- undec(N) := #Undec(N). -/
noncomputable def ClassifierSpec.undec (X : ClassifierSpec n p) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.canonical N f = none}
/-- env(N) := undec(N)/p^{nN} (the measured envelope). -/
noncomputable def ClassifierSpec.env (X : ClassifierSpec n p) (N : ℕ) : ℝ :=
  (X.undec N : ℝ) / (p : ℝ) ^ (n * N)
/-- d_σ(N) := decided_σ(N)/p^{nN}. -/
noncomputable def ClassifierSpec.dmass (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℝ :=
  (X.decided σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- HYPOTHESIS STRUCTURE (MovesS interface): the fixed p-independent rational output.
    R_σ := RS.1-SH's object — "the ONLY density-typed output of the solve" (§S type
    fence: no μ̂-typed marked total appears anywhere in MovesU). -/
structure SolveData (n : ℕ) where
  R : SplittingType n → RatFunc ℚ

/-- Literal evaluation of R_σ at q = p (Mathlib `RatFunc.eval`; junk 0 at poles —
    consumed ONLY under RegP, D6). -/
noncomputable def evalℝ (S : SolveData n) (σ : SplittingType n) (p : ℕ) : ℝ :=
  ((S.R σ).eval (RingHom.id ℚ) (p : ℚ) : ℚ)

/-- "The fixed ℚ(q)-element's literal evaluation at q₀ is DEFINED (q₀ not a pole)". -/
def DefinedAt (g : RatFunc ℚ) (q₀ : ℚ) : Prop := g.denom.eval q₀ ≠ 0

/-- HYPOTHESIS STRUCTURE (MovesS/§S S.4 interface; F4/F10 repair): the (REG-p) bundle.
    Q(p) = EXACTLY the image of the base-change depths (δ = 1 required — nonempty, never
    an arbitrary Finset); Block nonempty; K_e as literal matrices; ALL SEVEN displayed
    entry families as data (b_e BOTH components, per-cell J (CL-18), ι_e, W_Ŝ, every
    β_{e,τ} leg); ACT abstract (CTS-M(ii), owner [1v]). -/
structure RegData (p : ℕ) where
  depthSet : Finset ℕ                          -- base-change depths δ of RS.1-SH
  one_mem_depthSet : 1 ∈ depthSet              -- δ = 1 (the shallow pool) always arises
  Pool : Finset ℕ                              -- Q(p)
  pool_eq : Pool = depthSet.image (p ^ ·)      -- Q(p) IS the depth image (F4)
  Block : Type
  instB : Fintype Block
  instNe : Nonempty Block                      -- the top block exists (F4)
  bidx : Block → Type
  instBi : ∀ e, Fintype (bidx e)
  instBd : ∀ e, DecidableEq (bidx e)
  K : ∀ e : Block, Matrix (bidx e) (bidx e) (RatFunc ℚ)   -- {each entry of K_e}
  bterm : ∀ e : Block, bidx e → RatFunc ℚ      -- b_e^{term,fin}
  bsplit : ∀ e : Block, bidx e → RatFunc ℚ     -- b_e^split
  Jcell : Block → Finset (RatFunc ℚ)           -- every per-cell J entry (CL-18)
  iota : ∀ e : Block, bidx e → RatFunc ℚ       -- {each entry of ι_e}
  Wcoef : Finset (RatFunc ℚ)                   -- {each W_Ŝ coefficient}
  betaLegs : Block → Finset (RatFunc ℚ)        -- every β_{e,τ} entry, all pools' legs
  act : RatFunc ℚ → ℕ → ℚ                      -- ACT active value at a pool

/-- E(e) — a DEFINITION, verbatim the union SQ.4 displays (nothing droppable; F4/F10).
    (Classical DecidableEq on RatFunc ℚ for the images.) -/
noncomputable def RegData.entryList {p : ℕ} (D : RegData p) (e : D.Block) :
    Finset (RatFunc ℚ) :=
  letI := Classical.decEq (RatFunc ℚ); letI := D.instBi e; letI := D.instBd e
  (Finset.univ.image fun ij : D.bidx e × D.bidx e => D.K e ij.1 ij.2)
    ∪ (Finset.univ.image (D.bterm e)) ∪ (Finset.univ.image (D.bsplit e))
    ∪ D.Jcell e ∪ (Finset.univ.image (D.iota e)) ∪ D.Wcoef ∪ D.betaLegs e

/-- (REG-p), the rev-5 SEPARATE named hypothesis: (r1) full determinant (junk blocks
    included) defined and ≠ 0 at every pool; (r2) every member of the DEFINED E(e)
    (all seven displayed families, F10) defined at q₀ AND literal = ACT active value
    ((ii-c) agreement). Neither implies nor is implied by E0/CL-1 or ACT/CL-5 (D5).
    Never vacuous: Pool ∋ p^1, Block nonempty (F4). -/
def RegP {p : ℕ} (D : RegData p) : Prop :=
  ∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀

/-- HYPOTHESIS STRUCTURE (MovesD/[3t] interface; F2 repair): the tree-fiber series.
    `Tree σ` = the complete finite realizable canonical trees of verdict-type σ (owner
    MovesD); `thr` = TREE-N's decision threshold; `mem_slice_iff` CHARACTERIZES the
    slice as the thr ≤ N slice (no arbitrary Finset family). The Finset TYPE of
    `thrSlice` is CL-7's finiteness riding the instantiation (D4 — TRACK-COUNT + D(n)
    + genuine-increment, OPEN upstream, named in KernelStatements). The tie to the
    classifier's counts is the ledger's `finiteness_stack` IDENTITY (TREE-N):
    an empty `Tree σ` forces decided_σ ≡ 0 — nothing degenerate satisfiable (D4). -/
structure FiberSeries (n p : ℕ) (X : ClassifierSpec n p) where
  Tree : SplittingType n → Type
  mass : ∀ σ, Tree σ → ℝ≥0∞                     -- μ(fiber T): RS.1's positive series
  thr : ∀ σ, Tree σ → ℕ                         -- TREE-N's threshold
  thrSlice : ∀ σ : SplittingType n, ℕ → Finset (Tree σ)
  mem_slice_iff : ∀ σ N (T : Tree σ), T ∈ thrSlice σ N ↔ thr σ T ≤ N
  slice_exhausts : ∀ σ (T : Tree σ), T ∈ thrSlice σ (thr σ T)   -- kept explicit (F2)

/-- The extended-value sum of the σ tree-fiber series — EXISTS unconditionally in
    [0,∞] (Tonelli retype, rev 2): `ENNReal.summable`. -/
noncomputable def FiberSeries.seriesSum {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (σ : SplittingType n) : ℝ≥0∞ := ∑' T : F.Tree σ, F.mass σ T

end LeanUrat.MovesU
```

## 2b. The kernel pack + capstone ledger (Defs, continued) — THE trust surface

```lean
/-- THE KERNEL STATEMENT PACK (F5/F6/F7): one named Prop slot per open
    kernel/obligation of the capstone ledger. Filled with the REAL upstream statements
    at instantiation (owner per slot); filling a slot with `True` is an
    instantiation-fidelity violation adjudicated at the owner's audit (D9). -/
structure KernelStatements where
  escapeE0 : Prop         -- CL-1 [3]: per-pool ESCAPE(E0) active-block solvability
  weightCharge : Prop     -- CL-2 [5]: X.1b WEIGHT-CHARGE via X.2's env constants (F6)
  progressX2 : Prop       -- CL-3 [5]+[2b]: PROGRESS — (X2-AFF)/(X2-CAP)/(X2-BRIDGE)/
                          --   (X2-TAILS) with constants c₃(n), c₄(n), s(n) (F6)
  x3Termination : Prop    -- CL-4 [5]: X.3 termination a.e. (statement slot; its
                          --   operative trace is the `cl4_env_tendsto` field below)
  xhdM4aX : Prop          -- CL-5(i) [2b]: XHD = M4a-X (+ (ENT-U))
  d4r0 : Prop             -- CL-5(ii) [1]: D4R.0 — CLOSED upstream; ledger-echo slot
  ctsmIvPart : Prop       -- CL-5(iii) [1v]: CTS-M(iv)-PART
  ctsmIvRep : Prop        -- CL-5(iv) [1v]: CTS-M(iv)-REP = M2(ii)
  ctsmIvMeas : Prop       -- CL-5(v) [1v]: CTS-M(iv)-MEAS
  ctsmVHmc : Prop         -- CL-5(vi) [1v]: CTS-M(v) HMC
  ctsmIiAct : Prop        -- CL-5(vii) [1v]: CTS-M(ii) ACT + (ii-c) — RELATED to (r2),
                          --   SEPARATE (rev 6: neither implies the other)
  ctsmIiiInit : Prop      -- CL-5(viii) [1v]: CTS-M(iii) INIT + ENT-COUNT (ENT-AGG/INIT-RAT)
  ctsmViComp : Prop       -- CL-5(ix) [1v]: CTS-M(vi) COMP-typing
  ctsmIvPoly : Prop       -- CL-6 [1v]: (iv)-POLY — without it R_σ ∈ ℚ(q) unfounded
  trackCount : Prop       -- CL-7a [4]: TRACK-COUNT + explicit L(n)
  dnDuty : Prop           -- CL-7b [4]: the D(n) duty (candidate n!, underived)
  genuineIncrement : Prop -- CL-7c [4]: the positive genuine-increment sub-claim
  rel1 : Prop             -- CL-8 [2r]: REL.1 re-scoped
  rel2a : Prop            -- CL-8 [2r]: REL.2(a)
  rel2b : Prop            -- CL-8 [2r]: REL.2(b)
  rel2d : Prop            -- CL-8 [2r]: REL.2(d)
  rel2e : Prop            -- CL-8 [2r]: REL.2(e), the β-typing (e1)–(e5) leg
  rel3 : Prop             -- CL-8 [2r]: REL.3 over O_δ
  rs0LumpBisim : Prop     -- CL-9 [3]: RS.0 (α) lumpability + (β) bisimulation = XRB
  sib : Prop              -- CL-10 [3t]: (SIB)/(SIB-STEP), measure-level joint form
  jcMulti : Prop          -- CL-10 [3t]: (JC-multi)
  treeExpTreeN : Prop     -- CL-10 [3t]: TREE-EXP(-fin/-ns) + TREE-N, (NS-ROUTE)-scoped
  vpSound : Prop          -- CL-10 [3t]: VP (TB-CAP per clause) + VP-SOUND's two cites
  noEqualEFeedback : Prop -- CL-11 [4]/[1v]: no-equal-e-feedback + DEG-CONS full roster
  ksubM1C1 : Prop         -- CL-11/CL-13 face (F7): (K-SUB)'s (m,c) classification —
                          --   equal-e continuation EXCLUSIVELY in m = 1, c = 1 rows;
                          --   the empty-menu/(BDY) conventions ride here
  ctsmSyntax : Prop       -- CL-13 [1v]: CTS-M(i) SYNTAX — the ONE fixed finite state
                          --   set, move menus, cell predicates, target-cell maps (F7)
  m1m5 : Prop             -- CL-14 [2a]: M1 + M5 — CLOSED upstream; ledger-echo slot
  x1aDict : Prop          -- CL-15 [5]: the per-species GMN index dictionary
  m4bConstancy : Prop     -- CL-16 [1v]/[2b]: M4b constancy + M4b-T equivariance (π_v)
  rs1Assembly : Prop      -- CL-17 [3]: RS.1-SH + routing + unique shallow cut + W_Ŝ
  jRat : Prop             -- CL-18 [1v]/[2b]: (J-RAT) per-cell rational tables
  jcInv : Prop            -- CL-19 [2b]: (JC-INV) joint digit-cell law

/-- THE CAPSTONE LEDGER (SQ.4's CL-1…CL-19, REV 16 extent) as ONE Prop structure:
    a field PER CL ITEM asserting its kernel slot (F5; CL-2/CL-3 included, F6) PLUS
    the operative consumption fields. "Neither this display nor any acceptance record
    may drop a tag while any cited CL-item is open." (REG-p) is NOT a field: the ONE
    explicit hypothesis. CL-12 is CLOSED ("NOTHING at CL-12 is open") — no slot. -/
structure CapstoneLedger (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (S : SolveData n) (D : RegData p) (K : KernelStatements) : Prop where
  cl1 : K.escapeE0
  cl2 : K.weightCharge
  cl3 : K.progressX2
  cl4 : K.x3Termination
  cl5 : K.xhdM4aX ∧ K.d4r0 ∧ K.ctsmIvPart ∧ K.ctsmIvRep ∧ K.ctsmIvMeas ∧
        K.ctsmVHmc ∧ K.ctsmIiAct ∧ K.ctsmIiiInit ∧ K.ctsmViComp
  cl6 : K.ctsmIvPoly
  cl7 : K.trackCount ∧ K.dnDuty ∧ K.genuineIncrement
  cl8 : K.rel1 ∧ K.rel2a ∧ K.rel2b ∧ K.rel2d ∧ K.rel2e ∧ K.rel3
  cl9 : K.rs0LumpBisim
  cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN ∧ K.vpSound
  cl11 : K.noEqualEFeedback ∧ K.ksubM1C1
  cl13 : K.ctsmSyntax
  cl14 : K.m1m5
  cl15 : K.x1aDict
  cl16 : K.m4bConstancy
  cl17 : K.rs1Assembly
  cl18 : K.jRat
  cl19 : K.jcInv
  /-- OPERATIVE, the finiteness stack's consumed form (CL-7 + CL-10): TREE-N's exact
      fiber count summed over the thr ≤ N slice —
      "decided_σ(N) = Σ_{T : typemult(T) = σ, thr(T) ≤ N} #fiber(T) is a FINITE sum
      (SQ.0/CL-7) of exact fiber counts (TREE-N/CL-10)". This identity is also the
      series' tie to the classifier (D4, F2). -/
  finiteness_stack : ∀ σ N,
    (X.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T
  /-- OPERATIVE, the solve stack's consumed form (CL-1, CL-5, CL-6, CL-8, CL-9, CL-11,
      CL-13…CL-17, CL-18, CL-19 — the slots asserted above): UNDER (REG-p) the
      extended-value sum is finite, IS the literal R_σ(p), AND R_σ(p) ≥ 0 — "RS.3's
      positivity ((I − A(q₀))^{−1} ≥ 0) and R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN
      E0 + the CL-5 mass identification" (F8's repair: positivity is a conjunct, not
      an inference from `ofReal`). -/
  solve_stack : RegP D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
    0 ≤ evalℝ S σ p
  /-- RS.4's checksum (§S S.5) WITH its full inherited set riding verbatim: "E0, the
      CL-5 nine, RS.1's set, X.3/CL-4, and the whole RS.2 rationality chain incl.
      (J-RAT)/CL-18". The ℚ(q) identity — Theorem U's checksum conjunct.
      (Needs U0b's `Fintype (SplittingType n)`.) -/
  rs4_checksum : ∑ σ, S.R σ = 1
  /-- RS.4 EVALUATED at p under (REG-p) — the form SQ.3's arithmetic consumes. Same
      inherited set. (E-phase note: derivable from `rs4_checksum` + (r2)-definedness
      via RatFunc eval-hom side conditions; carried as a field until that unit lands.) -/
  rs4_eval : RegP D → ∑ σ, evalℝ S σ p = 1
  /-- OPERATIVE trace of CL-4 = X.3 (QUALITATIVE form — "the limit consumes no
      envelope constant"; the statement slot is `cl4` above; discharges only at [5]'s
      EVENT): env(N) → 0. The quantitative rate form (CL-2/CL-3's constants) is
      asserted via the `cl2`/`cl3` slots but not consumed by any MovesU proof — gate
      SQUEEZE-n3 is a census artifact, not a Lean unit. -/
  cl4_env_tendsto : Tendsto X.env atTop (𝓝 0)

/-- THE PER-p INSTANTIATION BUNDLE (for U10's quantifier shape): everything Theorem U
    needs at one prime, over the FIXED SolveData. -/
structure UInstance (n : ℕ) (S : SolveData n) (p : ℕ) where
  X : ClassifierSpec n p
  F : FiberSeries n p X
  D : RegData p
  K : KernelStatements
  L : CapstoneLedger n p X F S D K
```

Greppable audit: every CL-1 … CL-19 item is now a REAL hypothesis field (F5) — the
`cl1`…`cl19` assertions over named `KernelStatements` slots — with CL-2/CL-3 present
(F6) and CL-12 correctly absent (CLOSED — "NOTHING at CL-12 is open"; its O3 base-pin
display duty is a write-up sentence, out of Lean scope).

---

## 3. The unit DAG — 12 units, one file each: `lean/LeanUrat/MovesU/<id>.lean`

Layers: L0 Defs+counting (U0, U0b, U1) → L1 series (U2–U4) → L2 bracket (U5–U6) →
L3 limit (U7) → L4 schema/aux (U8–U9) → L5 capstone (U10). TAG-FREE = proved with no
ledger/structure hypothesis fields beyond definitions.

### U0b `MovesU.U0b_splitTypeFintype` — splitting types are a nonempty Fintype  [support]
- **file**: `MovesU/U0b_splitTypeFintype.lean`  ·  **difficulty**: medium  ·  **deps**: Defs
- **statement**: `instance : Fintype (SplittingType n)` and
  `theorem splittingType_nonempty (hn : 1 ≤ n) : Nonempty (SplittingType n)`
- **moves_ref**: "For each splitting type σ of degree n (a multiset of pairs (e_i, f_i)
  with Σ e_i·f_i = n)" (SQ.4)
- **sketch**: entries (e,f) have e·f ≤ n so e,f ≤ n and card σ ≤ n: embed into the
  multisets over `(Finset.range (n+1) ×ˢ Finset.range (n+1))` of card ≤ n
  (`Multiset.finite...`/`Set.Finite.fintype` route, classical OK); nonempty via
  ⟨{(n,1)}⟩. Needed by every `∑ σ` (rs4_checksum, (BOX-N), U10).
- **hypothesis_fields**: none.

### U0 `MovesU.U0_boxCard` — the box cardinality  [support, tag-free]
- **file**: `MovesU/U0_boxCard.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem boxCard (p n N : ℕ) [NeZero p] : Nat.card (Box p n N) = p ^ (n * N)`
- **moves_ref**: "the monic degree-n coefficient box mod p^N (p^{nN} residue classes)"
- **sketch**: `Nat.card (Fin n → ZMod (p^N)) = (p^N)^n = p^(n*N)`; `Nat.card_fun`/
  `Nat.card_eq_fintype_card`, `ZMod.card` (needs `NeZero (p^N)` from `NeZero p`), `pow_mul` (commuted).
- **hypothesis_fields**: none.

### U1 `MovesU.U1_boxN` — (BOX-N), the count identity  [TAG-FREE step 1]
- **file**: `MovesU/U1_boxN.lean`  ·  **difficulty**: medium  ·  **deps**: U0, U0b
- **statement**: `theorem boxN (X : ClassifierSpec n p) [NeZero p] (N : ℕ) :`
  `(∑ σ : SplittingType n, X.decided σ N) + X.undec N = p ^ (n * N)`
- **moves_ref**: "(BOX-N) p^{nN} = Σ_τ decided_τ(N) + undec(N) — the box partition,
  EXACT and tag-free as an identity of counts"
- **sketch**: partition the Fintype `Box p n N` by the value of `X.canonical N` in
  `Option (SplittingType n)`: `Finset.card_eq_sum_card_fiberwise` (Mathlib
  `Algebra/BigOperators/Group/Finset/Basic.lean`) over `Finset.univ`; fibers of
  `some σ` are `decided`, fiber of `none` is `undec` (`Nat.card_eq_fintype_card` +
  subtype/filter card transfer); close with U0. Tag-free BECAUSE it is a count
  identity for the interface's canonical map — the map's fidelity Props
  (`canonical_sound`/`_stable`) are carried by the structure, not consumed here.
- **hypothesis_fields**: none consumed (F1's repair: the verdict is now the pinned
  classifier interface, D2; no arbitrary labeling is an instance).

### U2 `MovesU.U2_tonelli` — extended-value existence + partial-sum domination  [TAG-FREE step 3]
- **file**: `MovesU/U2_tonelli.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem tonelli_partial_le {X : ClassifierSpec n p}`
  `(F : FiberSeries n p X) (σ : SplittingType n) (N : ℕ) :`
  `∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ`
- **moves_ref**: "the positive series has a well-defined EXTENDED-VALUE sum in [0, ∞]
  unconditionally (nonnegative terms) … FINITENESS … and IDENTIFICATION … are NOT
  Tonelli's" (rev 2, pass-1 critical 7)
- **sketch**: `ENNReal.sum_le_tsum` (`Topology/Algebra/InfiniteSum/ENNReal.lean`);
  existence is the totality of `∑'` in ℝ≥0∞ (`ENNReal.summable`,
  `ENNReal.tsum_eq_iSup_sum` — cite in a doc comment; no separate lemma needed).
- **hypothesis_fields**: none (the FiberSeries DATA is used, no Prop field).

### U3 `MovesU.U3_sq2_partial` — decided mass IS the thr ≤ N partial sum  [conditional]
- **file**: `MovesU/U3_sq2_partial.lean`  ·  **difficulty**: easy  ·  **deps**: U2
- **statement** (F3's repair — the IDENTITY is the claim; domination is the corollary):
  `theorem sq2_partial (L : CapstoneLedger n p X F S D K) (σ N) :`
  `(X.decided σ N : ℝ≥0∞) = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T`
  and `theorem sq2_partial_le … : (X.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ`
- **moves_ref**: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
  positive tree-fiber series for type σ" (SQ.2 ROUTE)
- **sketch**: the identity IS `L.finiteness_stack σ N` (re-exposed as the unit's named
  statement so the exact claim is auditable, not hidden — F3); the corollary rewrites
  by it and applies U2 + `mul_le_mul_left'`.
- **hypothesis_fields**: `finiteness_stack` (CL-7 + CL-10).

### U4 `MovesU.U4_sq2_upper` — SQ.2, the fixpoint upper bound  [conditional]
- **file**: `MovesU/U4_sq2_upper.lean`  ·  **difficulty**: medium  ·  **deps**: U3
- **statement**: `theorem sq2_upper (L : CapstoneLedger n p X F S D K)`
  `(hreg : RegP D) (hp : p.Prime) (σ N) :`
  `(X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)` (F9's repair: `p.Prime`,
  never `1 < p` — the note asserts SQ.2 only at primes satisfying (REG-p);
  composite p is NOT claimed)
- **moves_ref**: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
  "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 + the CL-5 mass
  identification"
- **sketch** (F8's repair): `L.solve_stack hreg σ` now GIVES `0 ≤ evalℝ S σ p` as its
  third conjunct — no bogus case split. Transfer ℝ≥0∞ → ℝ from U3's corollary:
  `ENNReal.toReal_le_toReal` (LHS ≠ ⊤ since the RHS is finite), `ENNReal.toReal_mul`,
  `ENNReal.toReal_ofReal` (its nonnegativity input = the positivity conjunct).
- **hypothesis_fields**: `finiteness_stack`, `solve_stack` (incl. the explicit
  positivity conjunct = RS.3's clause; the full solve stack CL-1, CL-5, CL-6, CL-8,
  CL-9, CL-11, CL-13…CL-19 rides the ledger's cl-slots); explicit `RegP D`, `p.Prime`.

### U5 `MovesU.U5_sq3_arith` — SQ.3's bracket arithmetic AS arithmetic  [TAG-FREE step 2]
- **file**: `MovesU/U5_sq3_arith.lean`  ·  **difficulty**: medium  ·  **deps**: U1
- **statement** (every tagged input an EXPLICIT argument — the tag-free content is the
  implication): `theorem sq3_arith (X : ClassifierSpec n p) [NeZero p] (hp : 1 < p)`
  `(R : SplittingType n → ℝ) (σ : SplittingType n) (N : ℕ)`
  `(hupper : ∀ τ, τ ≠ σ → (X.decided τ N : ℝ) ≤ R τ * (p : ℝ) ^ (n * N))`
  `(hsum : ∑ τ, R τ = 1) :`
  `(R σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ)`
  (`1 < p` here is ARITHMETIC SCAFFOLDING — p^{nN} ≠ 0 — not the note's quantifier;
  the note's display is asserted only through U6/U10, at primes)
- **moves_ref**: "decided_σ(N) = p^{nN} − Σ_{τ≠σ} decided_τ(N) − undec(N) ≥
  p^{nN}·(1 − Σ_{τ≠σ} R_τ(p) − env(N)) = (R_σ(p) − env(N))·p^{nN}" (SQ.3)
- **sketch**: cast U1's (BOX-N) to ℝ; `Finset.sum_erase_add`/`sub` bookkeeping;
  `env` unfolds to `undec/p^{nN}` with `div_mul_cancel₀` (`p^{nN} ≠ 0` from `hp`);
  finish by `linarith` over the τ ≠ σ sum of `hupper` + `hsum`. Pure ℝ arithmetic:
  no ledger, no RegP — the inputs carry the tags, as the note's re-audit says.
- **hypothesis_fields**: none (tag-free as an implication; instantiated at U6 with
  tagged inputs).

### U6 `MovesU.U6_un_bracket` — (U-n), the two-sided bracket  [conditional; the note's product]
- **file**: `MovesU/U6_un_bracket.lean`  ·  **difficulty**: easy  ·  **deps**: U4, U5
- **statement**: `theorem un_bracket (L : CapstoneLedger n p X F S D K)`
  `(hreg : RegP D) (hp : p.Prime) (σ N) :`
  `(evalℝ S σ p - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧`
  `(X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)` — `p.Prime` per F9
  (`NeZero p`/`1 < p` derived from `hp` inside)
- **moves_ref**: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
  every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing (REG-p) neither
  inequality is asserted" (the rev-3 qualifier = the `hreg` argument, D8)
- **sketch**: right leg = U4; left leg = U5 applied with `R := fun τ => evalℝ S τ p`,
  `hupper` from U4 at each τ ≠ σ, `hsum := L.rs4_eval hreg`.
- **hypothesis_fields**: `finiteness_stack`, `solve_stack`, `rs4_eval` (RS.4's full
  inherited set incl. X.3/CL-4); explicit `RegP D`.

### U7 `MovesU.U7_squeeze` — the limit forcing  [TAG-FREE step 4]
- **file**: `MovesU/U7_squeeze.lean`  ·  **difficulty**: medium  ·  **deps**: Defs
- **statement** (bracket + env-limit as EXPLICIT arguments; `1 < p` = arithmetic
  scaffolding, as at U5): `theorem squeeze_limit`
  `(X : ClassifierSpec n p) (hp : 1 < p) (r : ℝ) (σ : SplittingType n)`
  `(hbr : ∀ N, (r - X.env N) * (p:ℝ)^(n*N) ≤ (X.decided σ N : ℝ) ∧`
  `           (X.decided σ N : ℝ) ≤ r * (p:ℝ)^(n*N))`
  `(henv : Tendsto X.env atTop (𝓝 0)) :`
  `Tendsto (X.dmass σ) atTop (𝓝 r)`
- **moves_ref**: "With env(N) → 0 (X.3/CL-4, the QUALITATIVE form …):
  ρ_σ(p) := lim_{N→∞} decided_σ(N)/p^{nN} EXISTS and = R_σ(p)"
- **sketch**: divide `hbr` by `p^{nN} > 0` (`div_le_div_of_nonneg_right` forms) to get
  `r − env N ≤ dmass σ N ≤ r`; squeeze with Mathlib's
  `tendsto_of_tendsto_of_tendsto_of_le_of_le` (`Topology/Order/Basic.lean`; the `'`
  eventually-variant if convenient); lower leg `r − env N → r − 0 = r` by
  `Filter.Tendsto.const_sub` (`Topology/Algebra/Group/Basic.lean`, the `to_additive`
  of `Tendsto.const_div'`) + `sub_zero`; upper leg `tendsto_const_nhds`.
- **hypothesis_fields**: none (tag-free forcing; the tagged bracket/limit enter as
  arguments, instantiated at U10 from U6 + `cl4_env_tendsto`).

### U8 `MovesU.U8_regP_access` — (REG-p) accessors over the FULL entry list  [definitional]
- **file**: `MovesU/U8_regP_access.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement** (F10's repair — the generic accessor + one corollary PER displayed
  family + (r1) + nonemptiness):
  `theorem RegP.entry_agree {D : RegData p} (h : RegP D) (hq : q₀ ∈ D.Pool) (e)`
  `  {g} (hg : g ∈ D.entryList e) : DefinedAt g q₀ ∧ g.eval (RingHom.id ℚ) q₀ = D.act g q₀`
  — with corollaries `K_agree`, `bterm_agree`, `bsplit_agree`, `Jcell_agree`,
  `iota_agree`, `Wcoef_agree`, `betaLegs_agree` (membership in the `entryList` union,
  one per family — so ALL of (r2)'s displayed E(e) is exposed, not just K);
  `theorem RegP.det_ne_zero {D : RegData p} (h : RegP D) (hq : q₀ ∈ D.Pool) (e) :`
  `  (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) q₀ ≠ 0`;
  `theorem RegData.pool_self_mem (D : RegData p) : p ∈ D.Pool` (from `pool_eq` +
  `one_mem_depthSet`, `pow_one` — RegP is never pool-vacuous, F4).
- **moves_ref**: "(r1) det(I − K_e(q₀)) ≠ 0; and (r2) for EVERY member of the DISPLAYED
  ENTRY LIST E(e) := { each entry of K_e } ∪ { each entry of b_e — BOTH components …
  per-cell J … } ∪ { each entry of ι_e } ∪ { each W_Ŝ coefficient } ∪ { each entry of
  every β_{e,τ} … }" (SQ.4's rev-3 schema, now covered in full)
- **sketch**: unfold `RegP` + `RegData.entryList` (Finset union membership per family).
  The API the MovesS instantiation consumes; no content beyond the schema.
- **hypothesis_fields**: explicit `RegP D` only.

### U9 `MovesU.U9_lmeas` — (L-meas)'s retype: equivalence + IMPLIED-BY  [conditional on `rs4_eval` only]
- **file**: `MovesU/U9_lmeas.lean`  ·  **difficulty**: medium  ·  **deps**: U1, U4
- **statement** (two lemmas, fixed σ, N; `X : ClassifierSpec n p`,
  `R : SplittingType n → ℝ`; `1 < p` scaffolding as at U5):
  `theorem lmeas_equiv [NeZero p] (hp : 1 < p) (hsum : ∑ τ, R τ = 1) :`
  `((R σ - X.env N) * (p:ℝ)^(n*N) ≤ (X.decided σ N : ℝ)) ↔`
  `(∑ τ ∈ Finset.univ.erase σ, X.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ)` — and
  `theorem lmeas_implied (hupper : ∀ τ, τ ≠ σ → X.dmass τ N ≤ R τ) :`
  `∑ τ ∈ Finset.univ.erase σ, X.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ`
- **moves_ref**: "(L-meas) … by (BOX-N), for fixed σ this leg is EQUIVALENT to the
  AGGREGATE inequality Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ(p) … It is IMPLIED BY — not
  equivalent to — the conjunction {SQ.2 at every τ ≠ σ} + RS.4's checksum" (rev 2,
  pass-1 critical 5)
- **sketch**: `lmeas_equiv`: divide U1 by `p^{nN}` and rearrange (`Finset.add_sum_erase`,
  `hsum`); `lmeas_implied`: `Finset.sum_le_sum` — ONE direction only, faithfully: no
  converse is stated anywhere (per-τ violations can cancel; the note's honesty).
- **hypothesis_fields**: none as stated (`R : SplittingType n → ℝ` abstract, `hsum` explicit);
  at consumption `R := evalℝ`, `hsum := rs4_eval` — the gate-layer reading, recorded
  for SQUEEZE-n3's (L-meas) leg semantics only (the gate itself is NOT a Lean unit).

### U10 `MovesU.U10_theoremU` — THEOREM U, the ONE structure-carrying theorem  [capstone]
- **file**: `MovesU/U10_theoremU.lean`  ·  **difficulty**: medium  ·  **deps**: U6, U7
- **statement** (verbatim target; the campaign's statement-of-record):
```lean
/-- THEOREM U (CONDITIONAL — on the COMPLETE capstone ledger, carried per prime by
    `UInstance`; SQ.4). "For each splitting type σ of degree n … there is ONE fixed
    rational function R_σ ∈ ℚ(q)" — the ∃ binds ONE family BEFORE the prime
    quantifier (F11); witness: S.R, so the fixed family is the solve's. At EVERY
    prime p satisfying (REG-p): ρ_σ(p) exists and equals the literal R_σ(p); the
    undecided complement has vanishing mass; the classifier verdicts ARE the true
    factorization types (F12). Σ_σ R_σ = 1 identically in ℚ(q). At a p failing
    (REG-p): NO CLAIM (D8). -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (S : SolveData n)
    (inst : ∀ p : ℕ, p.Prime → UInstance n S p) :
    ∃ R : SplittingType n → RatFunc ℚ,
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
        (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        ∧ Tendsto (inst p hp).X.env atTop (𝓝 0)
        ∧ (∀ N f σ, (inst p hp).X.canonical N f = some σ →
            (inst p hp).X.trueType N f = some σ)
```
- **moves_ref**: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
  prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p), and ρ_σ(p) IS the
  splitting density of type σ over ℤ_p — the undecided complement has mass 0 and the
  classifier verdicts are the true factorization types … Σ_σ R_σ = 1 identically in q
  (RS.4). … The quantifier 'for EVERY prime p' reads: every p satisfying (REG-p)."
- **sketch**: witness `R := S.R`. Checksum: `(inst 2 Nat.prime_two).L.rs4_checksum`
  (p-independent, any prime's ledger). Per p: limit = U7 with `r := evalℝ S σ p`,
  bracket from U6 (`hp` supplies `NeZero p`, `1 < p`), env-limit = `L.cl4_env_tendsto`
  (also the second conjunct verbatim); third conjunct = `X.canonical_sound`. The three
  density-identification conjuncts TOGETHER are the note's "ρ_σ(p) IS the splitting
  density" AT INTERFACE STRENGTH (F12): limit + vanishing undecided + verdict truth,
  with `trueType`'s fidelity the declared HC-2 instantiation pin (D9). ≤ 20 lines.
- **hypothesis_fields**: the COMPLETE ledger — all 19 cl-slots + the operative fields —
  via `UInstance.L` at every prime, + explicit `RegP` per adjudicated p. Nothing else.

---

## 4. Semantic-guardian flags (the trust surface, for the Codex audit)

- **G1 `ClassifierSpec.trueType`/`canonical`**: the ONE semantic pin (D9). The
  interface now CARRIES soundness + stability, but that the instantiated `trueType`
  is the real ℤ_p factorization type (and `canonical` the real T_can^τ) is the
  HC-2/MovesD instantiation-fidelity duty. U10's density-identification conjuncts are
  interface-strength; say so in any progress claim.
- **G2 `evalℝ` junk values**: Mathlib `RatFunc.eval` returns 0 at poles. Audit that no
  unit consumes `evalℝ` outside a `RegP`-guarded context except as the LIMIT TARGET in
  U10, where `solve_stack`/`rs4_eval` (both RegP-guarded) give it content.
- **G3 `FiberSeries.thrSlice : Finset`**: finiteness-as-data = CL-7 riding the
  instantiation (D4); `mem_slice_iff` pins the slice to `thr`. Audit TRACK-COUNT +
  D(n) + genuine-increment stay named OPEN (`KernelStatements` slots + docstrings).
- **G4 the kernel slots**: every CL-1 … CL-19 item is an ASSERTED field (grep the
  `cl1`…`cl19` fields); `KernelStatements` slots are `Prop`-typed parameters — a
  `True`-filled slot is an instantiation-fidelity violation (D9), flag any instance
  unit that fills one. `solve_stack` MUST carry the explicit `0 ≤ evalℝ` conjunct
  (RS.3's clause, F8) — check it is not dropped in elaboration.
- **G5 `RegData.act` abstract**: (r2)'s ACT agreement is against an UNINTERPRETED
  `act`; the CTS-M(ii) semantics arrive at instantiation. (REG-p) stays the rev-5
  SEPARATE hypothesis — audit that no unit derives RegP from, or uses it to derive,
  any E0/ACT-shaped statement (the `ctsmIiAct` slot is a DIFFERENT obligation).
- **G6 statement-fence**: U5/U7 take their tagged inputs as EXPLICIT arguments with
  `1 < p` as declared arithmetic scaffolding; audit that the note's displays are
  asserted ONLY through U4/U6/U10 at `p.Prime` + `RegP` (F9), and that U6/U10
  re-supply the tagged arguments ONLY from ledger fields + RegP.
- **G7 `entryList` as definition**: (r2)'s domain is the DEFINED seven-family union —
  audit no family is dropped and none is quietly narrowed at instantiation (the β-legs
  Finset must contain EVERY base-changed leg at EVERY pool, per the display).

## 5. Verified Mathlib inventory (names checked against the pinned mathlib, 2026-07-28)

- `tendsto_of_tendsto_of_tendsto_of_le_of_le`, `...'` — `Mathlib/Topology/Order/Basic.lean` (the squeeze, U7).
- `Filter.Tendsto.const_sub` — `to_additive` of `Filter.Tendsto.const_div'`,
  `Mathlib/Topology/Algebra/Group/Basic.lean` (U7's lower leg); `tendsto_const_nhds`, `sub_zero`.
- `ENNReal.summable` (every ℝ≥0∞ family), `ENNReal.tsum_eq_iSup_sum`,
  `ENNReal.sum_le_tsum` — `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` (U2).
- `ENNReal.toReal_le_toReal`, `ENNReal.toReal_mul`, `ENNReal.toReal_ofReal`,
  `ENNReal.summable_toReal` — same area (U4's transfer).
- `RatFunc.eval` — `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`; `RatFunc.denom`,
  `RatFunc.denom_ne_zero` — `RatFunc/Basic.lean` (D5, `DefinedAt`).
- `Finset.card_eq_sum_card_fiberwise` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (U1).
- `ZMod.card`, `Nat.card_eq_fintype_card`, `pow_mul` (U0); `Finset.add_sum_erase`/
  `Finset.sum_erase_add`, `Finset.sum_le_sum`, `div_mul_cancel₀` (U5/U9).
- `ZMod.castHom` + `pow_dvd_pow` (`boxProj`, D2); `Set.Finite.fintype`/classical
  finiteness for `SplittingType n` (U0b — E-phase may swap in a cleaner
  `Multiset`-bounded construction; the instance's EXISTENCE is not in doubt).
- E-phase check (flagged, not assumed): eval-additivity side-condition lemmas for
  deriving `rs4_eval` from `rs4_checksum` (`RatFunc.eval_add`'s hypotheses) — if absent
  or awkward, `rs4_eval` stays a field (already the blueprint default).

## 6. Status and counts (REV 2)

12 units (U0, U0b, U1–U10): 4 TAG-FREE/unconditional (U1 (BOX-N), U2 Tonelli
existence, U5 SQ.3-as-arithmetic, U7 limit forcing — exactly the note's re-audited
tag-free perimeter) + 2 support (U0, U0b) + 6 conditional/definitional, every
hypothesis a named structure field, kernel slot, or explicit `RegP`. Difficulty:
5 easy, 7 medium, 0 hard. No new axiom; no `sorry` planned (conditional content =
hypothesis structures). Self-contained per the master plan; instantiation hooks per
D9: `ClassifierSpec` ← MovesD/HC-2, `FiberSeries` ← MovesD/[3t], `SolveData`/
`RegData`/`KernelStatements` ← MovesS + owner notes. Next gate: Codex re-audit
(one shot), charge = §4's guardian flags + the 13-finding disposition table (§7).

## 7. Findings→repairs table (Codex audit 2026-07-28, REJECT 10c/3g → REV 2)

| # | class | finding (short) | repair in REV 2 |
|---|---|---|---|
| 1 | crit | `Census` = arbitrary labeling, not the classifier | REDESIGNED: `ClassifierSpec` with `trueType`/`canonical`/`canonical_sound`/`canonical_stable` (D2, D9); decided/undec DEFINED from it |
| 2 | crit | `FiberSeries` empty/unrelated tree families | FIXED: `thr` + `mem_slice_iff` + `slice_exhausts`; tie = `finiteness_stack` identity (D4) |
| 3 | crit | U3 weakened "is the partial sum" to ≤ | FIXED: U3 states the exact identity; domination is the named corollary |
| 4 | crit | (REG-p) vacuous; entry list = K only | FIXED: `pool_eq` (Q(p) = depth image, ∋ p), `Nonempty Block`, all seven entry families, `entryList` a DEFINED union (D5) |
| 5 | gap | kernels are docstrings, not fields | FIXED: `KernelStatements` pack + per-CL `cl1`…`cl19` assertion fields (D7) |
| 6 | gap | CL-2/CL-3 omitted | FIXED: `weightCharge`/`progressX2` slots + `cl2`/`cl3` fields |
| 7 | gap | menus, m = 1, (BDY) absent | FIXED: `ksubM1C1` + `ctsmSyntax` slots carry them, named (D7) |
| 8 | crit | U4 positivity underivable from `ofReal` | FIXED: `solve_stack` gains explicit `0 ≤ evalℝ` (RS.3's clause, stated by the note) |
| 9 | crit | U4/U6 asserted at composite p > 1 | FIXED: `p.Prime` at U4/U6/U10; `1 < p` survives only as declared scaffolding in tag-free arithmetic units (U5/U7/U9, G6) |
| 10 | crit | U8 exposes only K-entries | FIXED: generic `entry_agree` + seven per-family corollaries + `pool_self_mem` |
| 11 | crit | U10: arbitrary σTy, no ∃-R, hn inert | FIXED: concrete `SplittingType n` (Σ eᵢfᵢ = n as data, U0b Fintype); conclusion `∃ R …` binding ONE fixed family before ∀ p |
| 12 | crit | U10 drops the density-identification clause | FIXED: conjuncts env → 0 + verdict-truth (`canonical_sound`) added; interface-strength caveat at G1 |
| 13 | crit | capstone satisfiable by fake instance | REDESIGNED: D9's non-vacuity boundary — pinned interfaces (soundness/stability, nonempty pools/blocks, defined entry list, concrete types); residual pin = `trueType`/kernel-slot fidelity, declared owner-audited (MovesC precedent) |


codex
I’m auditing the rev-1 repair claims against the actual Lean quantifiers and constructing degenerate instances mentally, rather than accepting the interface-fidelity prose. I’ll also check edge cases and the full capstone dependency flow unit by unit.
codex
1. **CRITICAL — U10 remains satisfiable by a degenerate classifier/solve instance.**

   Offending unit spec:

   > `theorem theoremU ... (inst : ∀ p : ℕ, p.Prime → UInstance n S p) : ∃ R ...`

   The rev-1 non-vacuity repair is not genuine. For any `n ≥ 2`, choose a fixed `σ₀ : SplittingType n` and instantiate:

   - `canonical N f = some σ₀`;
   - `trueType N f = some σ₀`;
   - one unit-mass tree for `σ₀`, empty tree types otherwise;
   - `R σ₀ = 1`, `R σ = 0` otherwise;
   - all `KernelStatements` fields as `True`;
   - a trivial regularity bundle.

   Then `canonical_sound`, `canonical_stable`, `finiteness_stack`, `solve_stack`, the checksum, and `env → 0` all hold. U10 therefore proves that every polynomial has type `σ₀`, with density one, without any connection to the canonical tree or actual factorization. This directly contradicts D9’s claim that “the audit’s fake instance is dead.”

2. **CRITICAL — U10 still does not state identification with the actual splitting density over `ℤ_p`.**

   Offending unit spec:

   > `∧ (∀ N f σ, (inst p hp).X.canonical N f = some σ →`
   > `    (inst p hp).X.trueType N f = some σ)`

   The note says:

   > “ρ_σ(p) IS the splitting density of type σ over ℤ_p”

   The Lean conclusion only compares two arbitrary fields of `ClassifierSpec`. There is no space of monic `ℤ_p` polynomials, Haar measure, factorization-type predicate, or assertion that `trueType` denotes that predicate. Calling `trueType` the “semantic anchor” in a comment does not put this content in the statement. Thus the F12 repair remains strictly weaker than the displayed theorem.

3. **CRITICAL — `(REG-p)` still need not quantify over the displayed entry list actually consumed by the solve.**

   Offending U8/Defs spec:

   > `Jcell : Block → Finset (RatFunc ℚ)`
   >
   > `Wcoef : Finset (RatFunc ℚ)`
   >
   > `betaLegs : Block → Finset (RatFunc ℚ)`
   >
   > `theorem RegP.entry_agree ... (hg : g ∈ D.entryList e) ...`

   These finite sets have no coverage or indexing property tying them to every branching cell, every shallow shape, every type, every base-change leg, or every pool in the note. They may all be empty. Moreover, `bidx e` may be empty, making the `K`, `bterm`, `bsplit`, and `iota` families empty too. With a nonempty singleton `Block` but empty `bidx`, the empty determinant is `1`, so `RegP` is readily satisfied while `(r2)` checks no entries at all.

   The seven union summands repair only their names, not the display’s universal coverage. F4/F10 are therefore not genuinely repaired.

4. **CRITICAL — U4/U10 do not assert that the literal value `R_σ(p)` is defined.**

   Offending U10 conclusion:

   > `Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p))`

   and operative hypothesis:

   > `F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p)`

   The note explicitly requires, under `(REG-p)`:

   > “the literal evaluation `R_σ(p)` ... is DEFINED and IS the active value”

   `S.R σ` is not included in `RegData.entryList`, and neither `solve_stack` nor U10 contains `DefinedAt (S.R σ) p`. Since `RatFunc.eval` returns its junk value at a pole, the current statement permits a pole of `R_σ` and can identify the density with that junk value. This changes the stated regular-prime semantics.

5. **GAP — the capstone kernels and the requested edge conventions are only uninterpreted proposition slots.**

   Offending hypothesis specification:

   > `ksubM1C1 : Prop`
   >
   > `ctsmSyntax : Prop`
   >
   > `cl11 : K.noEqualEFeedback ∧ K.ksubM1C1`
   >
   > `cl13 : K.ctsmSyntax`

   No Lean statement expresses move menus, empty-menu behavior, the `m = 1, c = 1` classification, `(BDY)` conventions, track assignments, or the other named kernels. Comments saying that these meanings “ride here” do not constrain the propositions. This leaves the Defs dependency underspecified and does not genuinely verify rev-1 repairs F5–F7.

6. **GAP — the O3 Teichmüller base pin is absent from the formal interface.**

   Offending U10 hypothesis description:

   > “the COMPLETE ledger — all 19 cl-slots ... Nothing else.”

   The frozen SQ.4 display explicitly declares the canonical policy’s pinned base digit section to be Teichmüller. Neither `ClassifierSpec`, `KernelStatements`, nor U10 contains that pin or a reference to a definition that enforces it. Treating it as “out of Lean scope” leaves a displayed Defs dependency unspecified.

7. **GAP — the proposed Defs/unit dependency graph is not elaboration-plausible as written.**

   Offending specs:

   > `U0b ... deps: Defs`
   >
   > `rs4_checksum : ∑ σ, S.R σ = 1`

   `CapstoneLedger` is placed in Defs and uses a finite sum over `SplittingType n`, but the required `Fintype (SplittingType n)` instance is only introduced by U0b, which itself depends on Defs. This is a circular dependency.

   Additionally:

   > `mem_slice_iff : ∀ σ N (T : Tree σ), T ∈ thrSlice σ N ↔ ...`

   requires `DecidableEq (Tree σ)`, but `FiberSeries` supplies no such instance and the skeleton does not establish a classical instance at that declaration.

All other unit displays—U0, U0b’s mathematical content, U1–U7, and U9—match their quoted arithmetic/series claims once their explicit hypotheses are accepted; the defects above lie in the semantic interfaces and capstone assembly.

**Counts: 4 critical / 3 gap**

**REJECT (4 crit / 3 gap)**
tokens used
43,493
1. **CRITICAL — U10 remains satisfiable by a degenerate classifier/solve instance.**

   Offending unit spec:

   > `theorem theoremU ... (inst : ∀ p : ℕ, p.Prime → UInstance n S p) : ∃ R ...`

   The rev-1 non-vacuity repair is not genuine. For any `n ≥ 2`, choose a fixed `σ₀ : SplittingType n` and instantiate:

   - `canonical N f = some σ₀`;
   - `trueType N f = some σ₀`;
   - one unit-mass tree for `σ₀`, empty tree types otherwise;
   - `R σ₀ = 1`, `R σ = 0` otherwise;
   - all `KernelStatements` fields as `True`;
   - a trivial regularity bundle.

   Then `canonical_sound`, `canonical_stable`, `finiteness_stack`, `solve_stack`, the checksum, and `env → 0` all hold. U10 therefore proves that every polynomial has type `σ₀`, with density one, without any connection to the canonical tree or actual factorization. This directly contradicts D9’s claim that “the audit’s fake instance is dead.”

2. **CRITICAL — U10 still does not state identification with the actual splitting density over `ℤ_p`.**

   Offending unit spec:

   > `∧ (∀ N f σ, (inst p hp).X.canonical N f = some σ →`
   > `    (inst p hp).X.trueType N f = some σ)`

   The note says:

   > “ρ_σ(p) IS the splitting density of type σ over ℤ_p”

   The Lean conclusion only compares two arbitrary fields of `ClassifierSpec`. There is no space of monic `ℤ_p` polynomials, Haar measure, factorization-type predicate, or assertion that `trueType` denotes that predicate. Calling `trueType` the “semantic anchor” in a comment does not put this content in the statement. Thus the F12 repair remains strictly weaker than the displayed theorem.

3. **CRITICAL — `(REG-p)` still need not quantify over the displayed entry list actually consumed by the solve.**

   Offending U8/Defs spec:

   > `Jcell : Block → Finset (RatFunc ℚ)`
   >
   > `Wcoef : Finset (RatFunc ℚ)`
   >
   > `betaLegs : Block → Finset (RatFunc ℚ)`
   >
   > `theorem RegP.entry_agree ... (hg : g ∈ D.entryList e) ...`

   These finite sets have no coverage or indexing property tying them to every branching cell, every shallow shape, every type, every base-change leg, or every pool in the note. They may all be empty. Moreover, `bidx e` may be empty, making the `K`, `bterm`, `bsplit`, and `iota` families empty too. With a nonempty singleton `Block` but empty `bidx`, the empty determinant is `1`, so `RegP` is readily satisfied while `(r2)` checks no entries at all.

   The seven union summands repair only their names, not the display’s universal coverage. F4/F10 are therefore not genuinely repaired.

4. **CRITICAL — U4/U10 do not assert that the literal value `R_σ(p)` is defined.**

   Offending U10 conclusion:

   > `Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p))`

   and operative hypothesis:

   > `F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p)`

   The note explicitly requires, under `(REG-p)`:

   > “the literal evaluation `R_σ(p)` ... is DEFINED and IS the active value”

   `S.R σ` is not included in `RegData.entryList`, and neither `solve_stack` nor U10 contains `DefinedAt (S.R σ) p`. Since `RatFunc.eval` returns its junk value at a pole, the current statement permits a pole of `R_σ` and can identify the density with that junk value. This changes the stated regular-prime semantics.

5. **GAP — the capstone kernels and the requested edge conventions are only uninterpreted proposition slots.**

   Offending hypothesis specification:

   > `ksubM1C1 : Prop`
   >
   > `ctsmSyntax : Prop`
   >
   > `cl11 : K.noEqualEFeedback ∧ K.ksubM1C1`
   >
   > `cl13 : K.ctsmSyntax`

   No Lean statement expresses move menus, empty-menu behavior, the `m = 1, c = 1` classification, `(BDY)` conventions, track assignments, or the other named kernels. Comments saying that these meanings “ride here” do not constrain the propositions. This leaves the Defs dependency underspecified and does not genuinely verify rev-1 repairs F5–F7.

6. **GAP — the O3 Teichmüller base pin is absent from the formal interface.**

   Offending U10 hypothesis description:

   > “the COMPLETE ledger — all 19 cl-slots ... Nothing else.”

   The frozen SQ.4 display explicitly declares the canonical policy’s pinned base digit section to be Teichmüller. Neither `ClassifierSpec`, `KernelStatements`, nor U10 contains that pin or a reference to a definition that enforces it. Treating it as “out of Lean scope” leaves a displayed Defs dependency unspecified.

7. **GAP — the proposed Defs/unit dependency graph is not elaboration-plausible as written.**

   Offending specs:

   > `U0b ... deps: Defs`
   >
   > `rs4_checksum : ∑ σ, S.R σ = 1`

   `CapstoneLedger` is placed in Defs and uses a finite sum over `SplittingType n`, but the required `Fintype (SplittingType n)` instance is only introduced by U0b, which itself depends on Defs. This is a circular dependency.

   Additionally:

   > `mem_slice_iff : ∀ σ N (T : Tree σ), T ∈ thrSlice σ N ↔ ...`

   requires `DecidableEq (Tree σ)`, but `FiberSeries` supplies no such instance and the skeleton does not establish a classical instance at that declaration.

All other unit displays—U0, U0b’s mathematical content, U1–U7, and U9—match their quoted arithmetic/series claims once their explicit hypotheses are accepted; the defects above lie in the semantic interfaces and capstone assembly.

**Counts: 4 critical / 3 gap**

**REJECT (4 crit / 3 gap)**
