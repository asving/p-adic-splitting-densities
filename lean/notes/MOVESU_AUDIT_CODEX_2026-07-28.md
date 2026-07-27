Date: 2026-07-27
Prompt construction: CAMPAIGN_AUDIT_CHARGE_2026-07-28.md charge (<CORPUS>=MovesU, <NOTE>=§U-SQUEEZE) + lean/notes/MOVES_2026-07-24.md lines 12879-13630 (the frozen §U-SQUEEZE note) + lean/notes/MOVESU_LEAN_BLUEPRINT_2026-07-28.md (full 481-line blueprint)

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa3c1-f373-7a83-8e7b-b86528626f06
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


THE BLUEPRINT UNDER AUDIT:
# MovesU — Lean blueprint for §U-SQUEEZE (Theorem U, conditional form; 2026-07-28)

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

## 1. Design decisions (D1–D7)

**D1 — The box is concrete; the verdict is data.** `Box p n N := Fin n → ZMod (p ^ N)`
(the n free coefficients of a monic degree-n polynomial mod p^N; `Nat.card = p^(n*N)`).
A `Census` carries per level N a TOTAL FUNCTION `verdict N : Box p n N → Option σTy`
(`some σ` = decided of type σ, `none` = Undec(N)). This encodes the note's load-bearing
"PARTITION, not mere covering: T_can^τ is a CHOICE-FREE function of f" — totality and
choice-freeness are BUILT IN by the function type, which is exactly what [1] L2 + VP +
ONE-F license upstream. `decided`/`undec`/`env` are then DEFINED from `verdict`, so
(BOX-N) becomes a genuinely tag-free Fintype partition count — the note's tag-free step 1.

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

**D4 — (REG-p) is a Prop schema over an entry-list bundle.** `RegData p` carries the pool
set Q(p) (Finset, each pool a power p^δ), the block index, the matrices K_e (so (r1) is a
literal determinant), the DISPLAYED ENTRY LIST E(e) as a `Finset (RatFunc ℚ)` with a
membership field putting every K-entry in it, and the ACT active-value semantics as an
abstract function `act` (upstream CTS-M(ii)). `RegP D : Prop` = (r1) det(I−K_e) defined
and ≠ 0 at every pool ∧ (r2) every entry of E(e) defined at q₀ (reduced denominator
nonvanishing, `RatFunc.denom` — "q₀ is not a pole") AND agreeing with `act`. Per rev 5
(the Fable D-G2 repair): (REG-p) is a SEPARATE named hypothesis — nothing in `RegData`
imports or implies E0/ACT's own statements; they live in ledger docstrings only.

**D5 — Literal evaluation.** `evalℝ S σ p := ((S.R σ).eval (RingHom.id ℚ) (p:ℚ) : ℝ)`
(Mathlib `RatFunc.eval`, junk-valued at poles). The theorem NEVER consumes `evalℝ` except
under `RegP D`, where the ledger's solve-stack field asserts the identification — so the
junk case is never load-bearing. The WILD-p/ACT reading is carried by (r2)'s agreement
clause inside `RegP`, exactly the note's "the two readings coincide, so ρ_σ(p) = R_σ(p)
is well-typed".

**D6 — The capstone ledger is ONE Prop structure; fields = the note's consumption
PACKAGES, docstrings = the CL entries verbatim.** At MovesU's boundary the 19 CL items
are consumed in exactly four operative packages, the note's own (U-n) grouping: the
FINITENESS STACK {CL-7, CL-10} → field `finiteness_stack` (TREE-N's exact fiber count:
decided_σ(N) as the thr ≤ N partial sum); the SOLVE STACK {CL-1, CL-5, CL-6, CL-8, CL-9,
CL-11, CL-13…CL-17, CL-18, CL-19} → field `solve_stack` (under RegP: seriesSum finite
and = R_σ(p)); RS.4's INHERITED SET → fields `rs4_checksum` (the ℚ(q) identity) and
`rs4_eval` (its evaluated form at p, what SQ.3 consumes); X.3/CL-4 QUALITATIVE → field
`cl4_env_tendsto` (env(N) → 0). Distributing one joint consequence over 19 fields would
FALSELY attribute per-item operative content; instead every CL-1…CL-19 number appears
VERBATIM in the docstring of the field that carries it (greppable audit: each of the 19
tags occurs — no tag dropped, per the theorem's own acceptance-record rule). (REG-p) is
NOT a ledger field: it is the ONE explicit hypothesis (rev 3, pass-2 critical 2), a
separate argument of every conditional unit.

**D7 — NO-CLAIM failure semantics = the restricted quantifier, no Lean artifact.** The
theorem's conclusion is `∀ p, p.Prime → ... → RegP D → (...)`. At a p failing (REG-p)
the implication is vacuously satisfied — Lean asserts NOTHING there: no equality, no
bound, no non-existence (the removable-auxiliary-zero case needs no encoding). This is
the note's failure semantics EXACTLY, for free. Design note only; no unit.

**The four TAG-FREE units** (= the note's re-audited unconditional perimeter, and the
only units proved without ledger fields): `U1_boxN`, `U2_tonelli`, `U5_sq3_arith`,
`U7_squeeze`. Everything else consumes hypothesis-structure fields and says so.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesU/Defs.lean` (inline; elaboration-phase target)

```lean
import Mathlib
namespace LeanUrat.MovesU
open Filter Topology ENNReal

/-- The level-N monic coefficient box: n free coefficients mod p^N (p^{nN} classes). -/
abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

/-- HYPOTHESIS STRUCTURE (instantiated later by MovesD's T_can^τ + MovesX's Undec).
    `verdict N f = some σ`: T_can^τ(f) complete finite realizable, all leaves
    (τ-irr)/(τ-hen), certified at level N, verdict-type multiset σ. `none`: Undec(N).
    TOTALITY + CHOICE-FREENESS are the function type ([1] L2 + VP + ONE-F, D1). -/
structure Census (n p : ℕ) (σTy : Type) [Fintype σTy] where
  verdict : ∀ N : ℕ, Box p n N → Option σTy

variable {n p : ℕ} {σTy : Type} [Fintype σTy]

/-- decided_σ(N), defined from the verdict function (never a field). -/
noncomputable def Census.decided (C : Census n p σTy) (σ : σTy) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // C.verdict N f = some σ}
/-- undec(N) := #Undec(N). -/
noncomputable def Census.undec (C : Census n p σTy) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // C.verdict N f = none}
/-- env(N) := undec(N)/p^{nN}, real-valued (the measured envelope). -/
noncomputable def Census.env (C : Census n p σTy) (N : ℕ) : ℝ :=
  (C.undec N : ℝ) / (p : ℝ) ^ (n * N)
/-- The normalized decided mass d_σ(N) := decided_σ(N)/p^{nN}. -/
noncomputable def Census.dmass (C : Census n p σTy) (σ : σTy) (N : ℕ) : ℝ :=
  (C.decided σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- HYPOTHESIS STRUCTURE (MovesS interface): the fixed p-independent rational output.
    R_σ := RS.1-SH's object — "the ONLY density-typed output of the solve" (§S type
    fence: no μ̂-typed marked total appears anywhere in MovesU). -/
structure SolveData (σTy : Type) where
  R : σTy → RatFunc ℚ

/-- Literal evaluation of R_σ at q = p (Mathlib `RatFunc.eval`; junk 0 at poles —
    consumed ONLY under RegP, D5). -/
noncomputable def evalℝ (S : SolveData σTy) (σ : σTy) (p : ℕ) : ℝ :=
  ((S.R σ).eval (RingHom.id ℚ) (p : ℚ) : ℚ)

/-- "The fixed ℚ(q)-element's literal evaluation at q₀ is DEFINED (q₀ not a pole)". -/
def DefinedAt (g : RatFunc ℚ) (q₀ : ℚ) : Prop := g.denom.eval q₀ ≠ 0

/-- HYPOTHESIS STRUCTURE (MovesS/§S S.4 interface): the (REG-p) bundle — the pool set
    Q(p), the blocks, K_e as literal matrices, the DISPLAYED ENTRY LIST E(e) (K, b both
    components incl. per-cell J (CL-18), ι_e, W_Ŝ, every β leg at every pool), and the
    ACT active-value semantics (CTS-M(ii), abstract here). -/
structure RegData (p : ℕ) where
  Pool : Finset ℕ                              -- Q(p), pools q₀ = p^δ
  pool_pow : ∀ q₀ ∈ Pool, ∃ δ ≥ 1, q₀ = p ^ δ
  Block : Type
  instB : Fintype Block
  bidx : Block → Type
  instBi : ∀ e, Fintype (bidx e)
  instBd : ∀ e, DecidableEq (bidx e)
  K : ∀ e : Block, Matrix (bidx e) (bidx e) (RatFunc ℚ)
  entryList : Block → Finset (RatFunc ℚ)       -- E(e), the rev-3 displayed list
  K_mem : ∀ e i j, K e i j ∈ entryList e       -- "{each entry of K_e} ⊆ E(e)"
  act : RatFunc ℚ → ℕ → ℚ                      -- ACT active value at a pool

/-- (REG-p), the rev-5 SEPARATE named hypothesis: (r1) full determinant (junk blocks
    included) defined and ≠ 0 at every pool; (r2) every E(e)-entry defined at q₀ AND
    literal = ACT active value ((ii-c) agreement). Neither implies nor is implied by
    E0/CL-1 or ACT/CL-5 — those never appear here (D4). -/
def RegP {p : ℕ} (D : RegData p) : Prop :=
  ∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀

/-- HYPOTHESIS STRUCTURE (MovesD/[3t] interface): the tree-fiber series for type σ.
    `thrSlice σ N` = the thr(T) ≤ N slice; ITS FINSET TYPE IS CL-7's finiteness riding
    the instantiation (D3 — TRACK-COUNT + D(n) + genuine-increment, OPEN upstream). -/
structure FiberSeries (n p : ℕ) (σTy : Type) [Fintype σTy] (C : Census n p σTy) where
  Tree : σTy → Type
  mass : ∀ σ, Tree σ → ℝ≥0∞                     -- μ(fiber T): RS.1's positive series
  thrSlice : ∀ σ : σTy, ℕ → Finset (Tree σ)
  slice_mono : ∀ σ, Monotone (thrSlice σ)

/-- The extended-value sum of the σ tree-fiber series — EXISTS unconditionally in
    [0,∞] (Tonelli retype, rev 2): `ENNReal.summable`. -/
noncomputable def FiberSeries.seriesSum {C : Census n p σTy}
    (F : FiberSeries n p σTy C) (σ : σTy) : ℝ≥0∞ := ∑' T : F.Tree σ, F.mass σ T

end LeanUrat.MovesU
```

## 2b. The capstone ledger structure (Defs, continued) — THE trust surface

```lean
/-- THE CAPSTONE LEDGER as ONE hypothesis structure (SQ.4's CL-1…CL-19, REV 16 extent).
    Fields = the note's four consumption packages (D6); every CL tag appears verbatim
    below — "neither this display nor any acceptance record may drop a tag while any
    cited CL-item is open". (REG-p) is NOT a field: the ONE explicit hypothesis. -/
structure CapstoneLedger (n p : ℕ) (σTy : Type) [Fintype σTy]
    (C : Census n p σTy) (F : FiberSeries n p σTy C)
    (S : SolveData σTy) (D : RegData p) : Prop where
  /-- FINITENESS STACK — CL-7 (TRACK-COUNT + L(n), D(n), the positive
      genuine-increment sub-claim: "without them no finite decided family") and CL-10
      (the [3t] TREE-ASSEMBLY package: (SIB)/(SIB-STEP), TREE-EXP(-fin/-ns) + TREE-N
      (NS-ROUTE)-scoped, VP with TB-CAP per clause, (ns-null) closed, VP-SOUND:
      "without CL-10 the solve computes marked-branch totals, not densities").
      Operative form = TREE-N's exact count summed over the thr ≤ N slice:
      decided_σ(N) = p^{nN} · Σ_{thr(T)≤N} μ(fiber T). -/
  finiteness_stack : ∀ σ N,
    (C.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T
  /-- SOLVE STACK — CL-1 (ESCAPE(E0), per-pool active-block solvability), CL-5 (the
      NINE RS.PRE inputs: XHD; D4R.0; (iv)-PART/-REP/-MEAS; (v) HMC; (ii) ACT; (iii)
      INIT + ENT-COUNT; (vi) COMP-typing), CL-6 ((iv)-POLY — without it R_σ ∈ ℚ(q) is
      unfounded), CL-8 (REL.1 + REL.2(a)(b)(d)(e) + REL.3 — every β(q^δ) leg), CL-9
      (RS.0 lumpability + height-shift bisimulation = XRB's prover), CL-11
      (no-equal-e-feedback + DEG-CONS), CL-13 (CTS-M(i) SYNTAX), CL-14 ([2a] M1+M5),
      CL-15 (X.1a dictionary), CL-16 (M4b/M4b-T), CL-17 (RS.1-SH: routing + unique
      shallow-cut + W_Ŝ regrouping), CL-18 ((J-RAT) per-cell tables), CL-19 ((JC-INV)).
      Operative form: UNDER (REG-p), the extended-value sum is finite and IS the
      literal R_σ(p) — the identification/finiteness that Tonelli never gives. -/
  solve_stack : RegP D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p)
  /-- RS.4's checksum (§S S.5) WITH its full inherited set riding verbatim: "E0, the
      CL-5 nine, RS.1's set, X.3/CL-4, and the whole RS.2 rationality chain incl.
      (J-RAT)/CL-18". The ℚ(q) identity — Theorem U's second conjunct. -/
  rs4_checksum : ∑ σ, S.R σ = 1
  /-- RS.4 EVALUATED at p under (REG-p) — the form SQ.3's arithmetic consumes. Same
      inherited set. (E-phase note: derivable from `rs4_checksum` + (r2)-definedness
      via RatFunc eval-hom side conditions; carried as a field until that unit lands.) -/
  rs4_eval : RegP D → ∑ σ, evalℝ S σ p = 1
  /-- CL-4 = X.3 termination a.e. (QUALITATIVE form — "the limit consumes no envelope
      constant"; discharges only at [5]'s EVENT): env(N) → 0. The quantitative
      (X2-*) envelope family (CL-2, CL-3) is NOT consumed by the limit and has no
      field — the rate form is out of MovesU's scope (gate SQUEEZE-n3 is a census
      artifact, not a Lean unit). -/
  cl4_env_tendsto : Tendsto C.env atTop (𝓝 0)
```

Greppable audit: CL-1 … CL-19 all appear above (CL-2/CL-3 in the `cl4_env_tendsto`
docstring as explicitly NOT consumed by the qualitative limit — the note's own scoping;
CL-12, perimeter conditionality, is CLOSED per SQ.4's ledger — "NOTHING at CL-12 is
open" — so it is correctly ABSENT as a hypothesis; its O3 base-pin display duty is a
write-up sentence, out of Lean scope).

---

## 3. The unit DAG — 11 units, one file each: `lean/LeanUrat/MovesU/<id>.lean`

Layers: L0 Defs+counting (U0–U1) → L1 series (U2–U4) → L2 bracket (U5–U6) →
L3 limit (U7) → L4 schema/aux (U8–U9) → L5 capstone (U10). TAG-FREE = proved with no
ledger/structure hypothesis fields beyond definitions.

### U0 `MovesU.U0_boxCard` — the box cardinality  [support, tag-free]
- **file**: `MovesU/U0_boxCard.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem boxCard (p n N : ℕ) [NeZero p] : Nat.card (Box p n N) = p ^ (n * N)`
- **moves_ref**: "the monic degree-n coefficient box mod p^N (p^{nN} residue classes)"
- **sketch**: `Nat.card (Fin n → ZMod (p^N)) = (p^N)^n = p^(n*N)`; `Nat.card_fun`/
  `Nat.card_eq_fintype_card`, `ZMod.card` (needs `NeZero (p^N)` from `NeZero p`), `pow_mul` (commuted).
- **hypothesis_fields**: none.

### U1 `MovesU.U1_boxN` — (BOX-N), the count identity  [TAG-FREE step 1]
- **file**: `MovesU/U1_boxN.lean`  ·  **difficulty**: medium  ·  **deps**: U0
- **statement**: `theorem boxN (C : Census n p σTy) [NeZero p] (N : ℕ) :`
  `(∑ σ : σTy, C.decided σ N) + C.undec N = p ^ (n * N)`
- **moves_ref**: "(BOX-N) p^{nN} = Σ_τ decided_τ(N) + undec(N) — the box partition,
  EXACT and tag-free as an identity of counts"
- **sketch**: partition the Fintype `Box p n N` by the value of `verdict N` in
  `Option σTy`: `Finset.card_eq_sum_card_fiberwise` (Mathlib
  `Algebra/BigOperators/Group/Finset/Basic.lean`) over `t := Finset.univ : Finset (Option σTy)`;
  fibers of `some σ` are `decided`, fiber of `none` is `undec`
  (`Nat.card_eq_fintype_card` + subtype/filter card transfer); close with U0.
- **hypothesis_fields**: none — genuinely tag-free per the note; totality is D1's
  function type (the upstream ONE-F duty, flagged §4).

### U2 `MovesU.U2_tonelli` — extended-value existence + partial-sum domination  [TAG-FREE step 3]
- **file**: `MovesU/U2_tonelli.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem tonelli_partial_le {C : Census n p σTy}`
  `(F : FiberSeries n p σTy C) (σ : σTy) (N : ℕ) :`
  `∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ`
- **moves_ref**: "the positive series has a well-defined EXTENDED-VALUE sum in [0, ∞]
  unconditionally (nonnegative terms) … FINITENESS … and IDENTIFICATION … are NOT
  Tonelli's" (rev 2, pass-1 critical 7)
- **sketch**: `ENNReal.sum_le_tsum` (`Topology/Algebra/InfiniteSum/ENNReal.lean`);
  existence is the totality of `∑'` in ℝ≥0∞ (`ENNReal.summable`,
  `ENNReal.tsum_eq_iSup_sum` — cite in a doc comment; no separate lemma needed).
- **hypothesis_fields**: none (the FiberSeries DATA is used, no Prop field).

### U3 `MovesU.U3_sq2_partial` — decided mass is a dominated partial sum  [conditional]
- **file**: `MovesU/U3_sq2_partial.lean`  ·  **difficulty**: easy  ·  **deps**: U2
- **statement**: `theorem sq2_partial (L : CapstoneLedger n p σTy C F S D) (σ N) :`
  `(C.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ`
- **moves_ref**: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
  positive tree-fiber series for type σ" (SQ.2 ROUTE)
- **sketch**: rewrite by `L.finiteness_stack`, apply U2 + `mul_le_mul_left'`.
- **hypothesis_fields**: `finiteness_stack` (CL-7 + CL-10).

### U4 `MovesU.U4_sq2_upper` — SQ.2, the fixpoint upper bound  [conditional]
- **file**: `MovesU/U4_sq2_upper.lean`  ·  **difficulty**: medium  ·  **deps**: U3
- **statement**: `theorem sq2_upper (L : CapstoneLedger n p σTy C F S D)`
  `(hreg : RegP D) (hp : 1 < p) (σ N) :`
  `(C.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)`
- **moves_ref**: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
  "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 + the CL-5 mass
  identification"
- **sketch**: from U3 and `L.solve_stack hreg σ` (finite, = `ofReal (evalℝ)`), transfer
  ℝ≥0∞ → ℝ: `ENNReal.toReal_le_toReal` (LHS ≠ ⊤ since RHS finite), `ENNReal.toReal_mul`,
  `ENNReal.toReal_ofReal` (needs `0 ≤ evalℝ` — extract from `ofReal`-form: if
  `evalℝ < 0` then `ofReal = 0`, forcing the sum = 0, bound trivial by case split;
  RS.3's positivity is thereby CONSUMED through the field, never re-derived).
- **hypothesis_fields**: `finiteness_stack`, `solve_stack` (the full solve stack:
  CL-1, CL-5, CL-6, CL-8, CL-9, CL-11, CL-13…CL-19); explicit `RegP D`.

### U5 `MovesU.U5_sq3_arith` — SQ.3's bracket arithmetic AS arithmetic  [TAG-FREE step 2]
- **file**: `MovesU/U5_sq3_arith.lean`  ·  **difficulty**: medium  ·  **deps**: U1
- **statement** (every tagged input an EXPLICIT argument — the tag-free content is the
  implication): `theorem sq3_arith (C : Census n p σTy) [NeZero p] (hp : 1 < p)`
  `(R : σTy → ℝ) (σ : σTy) (N : ℕ)`
  `(hupper : ∀ τ, τ ≠ σ → (C.decided τ N : ℝ) ≤ R τ * (p : ℝ) ^ (n * N))`
  `(hsum : ∑ τ, R τ = 1) :`
  `(R σ - C.env N) * (p : ℝ) ^ (n * N) ≤ (C.decided σ N : ℝ)`
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
- **statement**: `theorem un_bracket (L : CapstoneLedger n p σTy C F S D)`
  `(hreg : RegP D) [NeZero p] (hp : 1 < p) (σ N) :`
  `(evalℝ S σ p - C.env N) * (p : ℝ) ^ (n * N) ≤ (C.decided σ N : ℝ) ∧`
  `(C.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)`
- **moves_ref**: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
  every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing (REG-p) neither
  inequality is asserted" (the rev-3 qualifier = the `hreg` argument, D7)
- **sketch**: right leg = U4; left leg = U5 applied with `R := fun τ => evalℝ S τ p`,
  `hupper` from U4 at each τ ≠ σ, `hsum := L.rs4_eval hreg`.
- **hypothesis_fields**: `finiteness_stack`, `solve_stack`, `rs4_eval` (RS.4's full
  inherited set incl. X.3/CL-4); explicit `RegP D`.

### U7 `MovesU.U7_squeeze` — the limit forcing  [TAG-FREE step 4]
- **file**: `MovesU/U7_squeeze.lean`  ·  **difficulty**: medium  ·  **deps**: Defs
- **statement** (bracket + env-limit as EXPLICIT arguments): `theorem squeeze_limit`
  `(C : Census n p σTy) (hp : 1 < p) (r : ℝ) (σ : σTy)`
  `(hbr : ∀ N, (r - C.env N) * (p:ℝ)^(n*N) ≤ (C.decided σ N : ℝ) ∧`
  `           (C.decided σ N : ℝ) ≤ r * (p:ℝ)^(n*N))`
  `(henv : Tendsto C.env atTop (𝓝 0)) :`
  `Tendsto (C.dmass σ) atTop (𝓝 r)`
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

### U8 `MovesU.U8_regP_access` — (REG-p) accessor lemmas  [definitional]
- **file**: `MovesU/U8_regP_access.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement** (two lemmas): `theorem RegP.K_entry_agree {D : RegData p} (h : RegP D)`
  `(hq : q₀ ∈ D.Pool) (e i j) : DefinedAt (D.K e i j) q₀ ∧`
  `(D.K e i j).eval (RingHom.id ℚ) q₀ = D.act (D.K e i j) q₀` — via `D.K_mem`; and
  `theorem RegP.det_ne_zero {D : RegData p} (h : RegP D) (hq : q₀ ∈ D.Pool) (e) :`
  `(Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) q₀ ≠ 0`
- **moves_ref**: "(r1) det(I − K_e(q₀)) ≠ 0; and (r2) for EVERY member of the DISPLAYED
  ENTRY LIST E(e) … the literal evaluation at q₀ is DEFINED … AND AGREES with its ACT
  active value" (SQ.4's rev-3 schema)
- **sketch**: unfold `RegP`; direct projection. These are the API the MovesS
  instantiation will consume; no content beyond the schema.
- **hypothesis_fields**: explicit `RegP D` only.

### U9 `MovesU.U9_lmeas` — (L-meas)'s retype: equivalence + IMPLIED-BY  [conditional on `rs4_eval` only]
- **file**: `MovesU/U9_lmeas.lean`  ·  **difficulty**: medium  ·  **deps**: U1, U4
- **statement** (two lemmas, fixed σ, N; abbrev `d τ := C.dmass τ N`):
  `theorem lmeas_equiv [NeZero p] (hp : 1 < p) (hsum : ∑ τ, R τ = 1) :`
  `((R σ - C.env N) * (p:ℝ)^(n*N) ≤ (C.decided σ N : ℝ)) ↔`
  `(∑ τ ∈ Finset.univ.erase σ, C.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ)` — and
  `theorem lmeas_implied (hupper : ∀ τ, τ ≠ σ → C.dmass τ N ≤ R τ) :`
  `∑ τ ∈ Finset.univ.erase σ, C.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ`
- **moves_ref**: "(L-meas) … by (BOX-N), for fixed σ this leg is EQUIVALENT to the
  AGGREGATE inequality Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ(p) … It is IMPLIED BY — not
  equivalent to — the conjunction {SQ.2 at every τ ≠ σ} + RS.4's checksum" (rev 2,
  pass-1 critical 5)
- **sketch**: `lmeas_equiv`: divide U1 by `p^{nN}` and rearrange (`Finset.add_sum_erase`,
  `hsum`); `lmeas_implied`: `Finset.sum_le_sum` — ONE direction only, faithfully: no
  converse is stated anywhere (per-τ violations can cancel; the note's honesty).
- **hypothesis_fields**: none as stated (R : σTy → ℝ abstract with `hsum` explicit);
  at consumption `R := evalℝ`, `hsum := rs4_eval` — the gate-layer reading, recorded
  for SQUEEZE-n3's (L-meas) leg semantics only (the gate itself is NOT a Lean unit).

### U10 `MovesU.U10_theoremU` — THEOREM U, the ONE structure-carrying theorem  [capstone]
- **file**: `MovesU/U10_theoremU.lean`  ·  **difficulty**: medium  ·  **deps**: U6, U7
- **statement** (verbatim target; the campaign's statement-of-record):
```lean
/-- THEOREM U (CONDITIONAL — on the COMPLETE capstone ledger, a `CapstoneLedger`
    hypothesis; SQ.4). For each splitting type σ there is ONE fixed R_σ ∈ ℚ(q) (the
    `SolveData`, p-independent BY TYPE) with: at EVERY prime p satisfying (REG-p),
    ρ_σ(p) := lim_N decided_σ(N)/p^{nN} exists and equals the literal R_σ(p); and
    Σ_σ R_σ = 1 identically in ℚ(q). At a p failing (REG-p): NO CLAIM (D7 — the
    implication is simply not applicable; no equality, bound, or non-existence). -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (σTy : Type) [Fintype σTy]
    (S : SolveData σTy) :
    ∀ (p : ℕ) (hp : p.Prime) (C : Census n p σTy) (F : FiberSeries n p σTy C)
      (D : RegData p) (L : CapstoneLedger n p σTy C F S D),
      RegP D →
        (∀ σ : σTy, Tendsto (C.dmass σ) atTop (𝓝 (evalℝ S σ p)))
        ∧ ∑ σ, S.R σ = 1
```
- **moves_ref**: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
  prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p) … Σ_σ R_σ = 1
  identically in q (RS.4). … The quantifier 'for EVERY prime p' reads: every p
  satisfying (REG-p)." (SQ.4 = THEOREM U)
- **sketch**: first conjunct: U7 applied with `r := evalℝ S σ p`, bracket from U6
  (needs `1 < p` from `hp.one_lt`, `NeZero p` from `hp.pos`), env-limit from
  `L.cl4_env_tendsto`; second conjunct: `L.rs4_checksum`. ≤ 15 lines expected.
- **hypothesis_fields**: ALL FIVE ledger fields + explicit `RegP D` — the complete
  conditionality, nothing else. The "ρ_σ(p) IS the splitting density" clause and the
  wild-p ACT reading are instantiation semantics (§4 flags F2/F5), not extra fields.

---

## 4. Semantic-guardian flags (the trust surface, for the Codex audit)

- **F1 `Census.verdict`**: the abstract σTy/verdict makes "decided of type σ" a LABEL.
  The note's clause "the classifier verdicts are the true factorization types" is NOT
  stated here — it is the MovesD/OM instantiation's faithfulness duty (X.3/CL-4 +
  [3t] VP + VP-SOUND). Never describe U10 as certifying true splitting densities;
  it certifies the squeeze over the interface.
- **F2 `evalℝ` junk values**: Mathlib `RatFunc.eval` returns 0 at poles. Audit that no
  unit consumes `evalℝ` outside a `RegP`-guarded context except as the LIMIT TARGET in
  U10, where `solve_stack`/`rs4_eval` (both RegP-guarded) give it content.
- **F3 `FiberSeries.thrSlice : Finset`**: finiteness-as-data = CL-7 riding the
  instantiation (D3). Audit the docstring keeps TRACK-COUNT + D(n) + genuine-increment
  named OPEN.
- **F4 Ledger docstrings**: grep-check every one of CL-1 … CL-19 appears verbatim in
  `CapstoneLedger`'s docstrings (D6's no-tag-dropped rule); check no field silently
  strengthens (e.g. `solve_stack` must NOT assert `0 ≤ evalℝ` separately — positivity
  is consumed via the `ofReal` form only).
- **F5 `RegData.act` abstract**: (r2)'s ACT agreement is against an UNINTERPRETED
  `act`; the CTS-M(ii) semantics arrive at instantiation. (REG-p) stays the rev-5
  SEPARATE hypothesis — audit that no unit derives RegP from, or uses it to derive,
  any E0/ACT-shaped statement.
- **F6 statement-fence**: U5/U7 take their tagged inputs as EXPLICIT arguments; audit
  that this matches the note's "tag-free AS arithmetic / AS forcing" scoping and that
  U6/U10 re-supply those arguments ONLY from ledger fields + RegP.

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
- E-phase check (flagged, not assumed): eval-additivity side-condition lemmas for
  deriving `rs4_eval` from `rs4_checksum` (`RatFunc.eval_add`'s hypotheses) — if absent
  or awkward, `rs4_eval` stays a field (already the blueprint default).

## 6. Status and counts

11 units (U0–U10): 4 TAG-FREE/unconditional (U1 (BOX-N), U2 Tonelli existence,
U5 SQ.3-as-arithmetic, U7 limit forcing — exactly the note's re-audited tag-free
perimeter) + U0 support + 6 conditional/definitional, every hypothesis a named
structure field or explicit `RegP`. Difficulty: 6 easy, 5 medium, 0 hard. No new
axiom anywhere; no `sorry` planned (conditional content = hypothesis structures).
Consumes NO existing Moves/MovesC module (self-contained per the master plan;
instantiation hooks: `Census` ← MovesD T_can + MovesX Undec, `SolveData`/`RegData`
← MovesS, `FiberSeries` ← MovesD/[3t]). Next gate: Codex semantic audit (§3 B→A),
charge = §4's flags + the master plan's faithfulness bar.


codex
1. **CRITICAL — `Census` does not encode the note’s canonical classifier.**

   > `structure Census ... where verdict : ∀ N, Box p n N → Option σTy`

   > U1: `theorem boxN (C : Census n p σTy) ...`

   An arbitrary total function is not the choice-free canonical map \(T^\tau_{\rm can}\), nor does it ensure that `some σ` means a complete realizable halted tree of true type \(\sigma\). Thus U1 proves a partition for any labeling, including `verdict := fun _ _ => some arbitraryLabel`. Totality alone does not supply ONE-F, VP, VP-SOUND, or classifier correctness.

2. **CRITICAL — `FiberSeries` and U2 admit empty, unrelated tree families.**

   > `Tree : σTy → Type`

   > `thrSlice : ∀ σ, ℕ → Finset (Tree σ)`

   > U2: `∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ`

   `Tree σ` may be empty, and neither `mass` nor `thrSlice` is connected to canonical realizable trees, thresholds, or fibers. U2 is therefore trivially satisfied by an empty series. The note’s series is the actual positive canonical tree-fiber series, not arbitrary ENNReal data.

3. **CRITICAL — U3 weakens “is the partial sum” to mere domination.**

   > U3: `(C.decided σ N : ℝ≥0∞) ≤ p ^ (n * N) * F.seriesSum σ`

   Its `moves_ref` says that the normalized decided count **is** the `thr ≤ N` partial sum. The statement only records the resulting upper inequality; the exact identification is hidden inside `L.finiteness_stack`. This is not the quoted claim.

4. **CRITICAL — `(REG-p)` is vacuous and its displayed entry list is not represented.**

   > `Pool : Finset ℕ`

   > `Block : Type`

   > `entryList : Block → Finset (RatFunc ℚ)`

   > `K_mem : ∀ e i j, K e i j ∈ entryList e`

   `Pool` and `Block` may both be empty, making `RegP D` vacuously true. `pool_pow` proves only that listed pools are powers; it does not prove that every pool arising in RS.1-SH is listed. Moreover, only the \(K_e\)-entries are represented and required to belong to `entryList`; there is no data or membership requirement for either component of \(b_e\), per-cell \(J\), \(\iota_e\), \(W_{\widehat S}\), or any \(\beta\)-leg. Hence this is strictly weaker than SQ.4’s `(REG-p)`.

5. **GAP — the capstone’s open kernels are docstrings, not hypothesis fields.**

   > `finiteness_stack : ∀ σ N, ...`

   > `solve_stack : RegP D → ∀ σ, ...`

   The actual TRACK-COUNT, \(L(n)\), \(D(n)\), genuine-increment, E0, CL-5 inputs, REL obligations, DEG-CONS, SIB, JC-INV, J-RAT, and other open statements do not appear as fields. Instead, their downstream conclusions are assumed wholesale. Merely mentioning CL numbers in comments does not meet the frozen note’s complete hypothesis ledger.

6. **GAP — CL-2 and CL-3 are explicitly omitted despite SQ.4 requiring the complete capstone ledger.**

   > “The quantitative `(X2-*)` envelope family (CL-2, CL-3) ... has no field”

   The frozen THEOREM U is conditional on the complete CL-1…CL-19 ledger, even where a particular proof step does not use its quantitative constants. Omitting CL-2/CL-3 changes the theorem’s stated conditionality.

7. **GAP — menu, \(m=1\), and `(BDY)` dependencies are absent.**

   No definition or hypothesis field represents the move menus, the same-size \(m=1,c=1\) continuation case, empty-menu behavior, or the frozen `(BDY)` conventions. These are hidden behind `solve_stack`, so their edge-case fidelity cannot be checked from the formal interface.

8. **CRITICAL — U4 is not derivable because positivity was dropped.**

   > `solve_stack ... F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p)`

   > U4: `decided ≤ evalℝ S σ p * p^(n*N)`

   Equality with `ENNReal.ofReal r` does not imply \(0\le r\): every negative \(r\) maps to zero. If `evalℝ < 0` and the series and decided count are zero, the assumptions can hold while U4 demands \(0\le r p^{nN}<0\). The sketch’s claim that this case is “trivial” is false. The note explicitly requires \(R_\sigma(p)\ge0\), tagged by E0 and CL-5.

9. **CRITICAL — U4 and U6 omit primality and therefore assert stronger statements.**

   > U4: `(hp : 1 < p)`

   > U6: `(hreg : RegP D) [NeZero p] (hp : 1 < p)`

   SQ.2 and `(U-n)` are asserted for primes satisfying `(REG-p)`. These units also claim the bounds for composite \(p>1\), which the frozen display does not.

10. **CRITICAL — U8 does not state the quoted `(REG-p)` schema.**

    > `RegP.K_entry_agree ... D.K e i j ...`

    > `RegP.det_ne_zero ...`

    The quoted display quantifies over every member of the complete entry list and requires definedness plus ACT agreement. U8 exposes only \(K\)-entry agreement and determinant nonvanishing. Together with the incomplete `RegData`, it omits almost all of `(r2)`.

11. **CRITICAL — U10 changes the principal quantifier structure and type domain.**

    > `theorem theoremU ... (σTy : Type) [Fintype σTy] (S : SolveData σTy) : ∀ p ...`

    The note quantifies over the actual splitting types of degree \(n\) and asserts existence of one fixed family \(R_\sigma\). U10 accepts an arbitrary finite label type and an already supplied arbitrary `SolveData`; it neither encodes \(\sum e_i f_i=n\) nor asserts existence of the fixed rational functions. In particular, `σTy` may be empty or unrelated to splitting types, and `hn` has no semantic effect.

12. **CRITICAL — U10 omits the splitting-density conclusion.**

    > Conclusion: `(∀ σ, Tendsto (C.dmass σ) ... ) ∧ ∑ σ, S.R σ = 1`

    The frozen theorem additionally states that \(\rho_\sigma(p)\) **is the monic-box splitting density**, that the undecided complement has mass zero, and that verdicts are true factorization types via X.3, VP, and VP-SOUND. Calling these “instantiation semantics” removes a substantive conjunct from the theorem.

13. **CRITICAL — the entire capstone remains satisfiable by a degenerate fake instance.**

    > U10 quantifies over arbitrary `C`, `F`, `D`, and `L`.

    For a singleton label type, take `verdict` constantly `some`, an artificial singleton tree of mass \(1\), every threshold slice equal to that singleton, \(R=1\), and empty `RegData.Pool`/`Block`. Then `RegP` is vacuous, `env=0`, and all ledger fields can be populated, although no canonical tree or factorization type exists in the data. This is exactly the prohibited non-vacuity failure.

U5, U7, and U9 faithfully isolate the advertised arithmetic implications, including \(N=0\). U0’s cardinality formula is also sound as a support lemma.

**Counts: 10 CRITICAL / 3 GAP**

**REJECT (10 crit / 3 gap)**
tokens used
37,208
1. **CRITICAL — `Census` does not encode the note’s canonical classifier.**

   > `structure Census ... where verdict : ∀ N, Box p n N → Option σTy`

   > U1: `theorem boxN (C : Census n p σTy) ...`

   An arbitrary total function is not the choice-free canonical map \(T^\tau_{\rm can}\), nor does it ensure that `some σ` means a complete realizable halted tree of true type \(\sigma\). Thus U1 proves a partition for any labeling, including `verdict := fun _ _ => some arbitraryLabel`. Totality alone does not supply ONE-F, VP, VP-SOUND, or classifier correctness.

2. **CRITICAL — `FiberSeries` and U2 admit empty, unrelated tree families.**

   > `Tree : σTy → Type`

   > `thrSlice : ∀ σ, ℕ → Finset (Tree σ)`

   > U2: `∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ`

   `Tree σ` may be empty, and neither `mass` nor `thrSlice` is connected to canonical realizable trees, thresholds, or fibers. U2 is therefore trivially satisfied by an empty series. The note’s series is the actual positive canonical tree-fiber series, not arbitrary ENNReal data.

3. **CRITICAL — U3 weakens “is the partial sum” to mere domination.**

   > U3: `(C.decided σ N : ℝ≥0∞) ≤ p ^ (n * N) * F.seriesSum σ`

   Its `moves_ref` says that the normalized decided count **is** the `thr ≤ N` partial sum. The statement only records the resulting upper inequality; the exact identification is hidden inside `L.finiteness_stack`. This is not the quoted claim.

4. **CRITICAL — `(REG-p)` is vacuous and its displayed entry list is not represented.**

   > `Pool : Finset ℕ`

   > `Block : Type`

   > `entryList : Block → Finset (RatFunc ℚ)`

   > `K_mem : ∀ e i j, K e i j ∈ entryList e`

   `Pool` and `Block` may both be empty, making `RegP D` vacuously true. `pool_pow` proves only that listed pools are powers; it does not prove that every pool arising in RS.1-SH is listed. Moreover, only the \(K_e\)-entries are represented and required to belong to `entryList`; there is no data or membership requirement for either component of \(b_e\), per-cell \(J\), \(\iota_e\), \(W_{\widehat S}\), or any \(\beta\)-leg. Hence this is strictly weaker than SQ.4’s `(REG-p)`.

5. **GAP — the capstone’s open kernels are docstrings, not hypothesis fields.**

   > `finiteness_stack : ∀ σ N, ...`

   > `solve_stack : RegP D → ∀ σ, ...`

   The actual TRACK-COUNT, \(L(n)\), \(D(n)\), genuine-increment, E0, CL-5 inputs, REL obligations, DEG-CONS, SIB, JC-INV, J-RAT, and other open statements do not appear as fields. Instead, their downstream conclusions are assumed wholesale. Merely mentioning CL numbers in comments does not meet the frozen note’s complete hypothesis ledger.

6. **GAP — CL-2 and CL-3 are explicitly omitted despite SQ.4 requiring the complete capstone ledger.**

   > “The quantitative `(X2-*)` envelope family (CL-2, CL-3) ... has no field”

   The frozen THEOREM U is conditional on the complete CL-1…CL-19 ledger, even where a particular proof step does not use its quantitative constants. Omitting CL-2/CL-3 changes the theorem’s stated conditionality.

7. **GAP — menu, \(m=1\), and `(BDY)` dependencies are absent.**

   No definition or hypothesis field represents the move menus, the same-size \(m=1,c=1\) continuation case, empty-menu behavior, or the frozen `(BDY)` conventions. These are hidden behind `solve_stack`, so their edge-case fidelity cannot be checked from the formal interface.

8. **CRITICAL — U4 is not derivable because positivity was dropped.**

   > `solve_stack ... F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p)`

   > U4: `decided ≤ evalℝ S σ p * p^(n*N)`

   Equality with `ENNReal.ofReal r` does not imply \(0\le r\): every negative \(r\) maps to zero. If `evalℝ < 0` and the series and decided count are zero, the assumptions can hold while U4 demands \(0\le r p^{nN}<0\). The sketch’s claim that this case is “trivial” is false. The note explicitly requires \(R_\sigma(p)\ge0\), tagged by E0 and CL-5.

9. **CRITICAL — U4 and U6 omit primality and therefore assert stronger statements.**

   > U4: `(hp : 1 < p)`

   > U6: `(hreg : RegP D) [NeZero p] (hp : 1 < p)`

   SQ.2 and `(U-n)` are asserted for primes satisfying `(REG-p)`. These units also claim the bounds for composite \(p>1\), which the frozen display does not.

10. **CRITICAL — U8 does not state the quoted `(REG-p)` schema.**

    > `RegP.K_entry_agree ... D.K e i j ...`

    > `RegP.det_ne_zero ...`

    The quoted display quantifies over every member of the complete entry list and requires definedness plus ACT agreement. U8 exposes only \(K\)-entry agreement and determinant nonvanishing. Together with the incomplete `RegData`, it omits almost all of `(r2)`.

11. **CRITICAL — U10 changes the principal quantifier structure and type domain.**

    > `theorem theoremU ... (σTy : Type) [Fintype σTy] (S : SolveData σTy) : ∀ p ...`

    The note quantifies over the actual splitting types of degree \(n\) and asserts existence of one fixed family \(R_\sigma\). U10 accepts an arbitrary finite label type and an already supplied arbitrary `SolveData`; it neither encodes \(\sum e_i f_i=n\) nor asserts existence of the fixed rational functions. In particular, `σTy` may be empty or unrelated to splitting types, and `hn` has no semantic effect.

12. **CRITICAL — U10 omits the splitting-density conclusion.**

    > Conclusion: `(∀ σ, Tendsto (C.dmass σ) ... ) ∧ ∑ σ, S.R σ = 1`

    The frozen theorem additionally states that \(\rho_\sigma(p)\) **is the monic-box splitting density**, that the undecided complement has mass zero, and that verdicts are true factorization types via X.3, VP, and VP-SOUND. Calling these “instantiation semantics” removes a substantive conjunct from the theorem.

13. **CRITICAL — the entire capstone remains satisfiable by a degenerate fake instance.**

    > U10 quantifies over arbitrary `C`, `F`, `D`, and `L`.

    For a singleton label type, take `verdict` constantly `some`, an artificial singleton tree of mass \(1\), every threshold slice equal to that singleton, \(R=1\), and empty `RegData.Pool`/`Block`. Then `RegP` is vacuous, `env=0`, and all ledger fields can be populated, although no canonical tree or factorization type exists in the data. This is exactly the prohibited non-vacuity failure.

U5, U7, and U9 faithfully isolate the advertised arithmetic implications, including \(N=0\). U0’s cardinality formula is also sound as a support lemma.

**Counts: 10 CRITICAL / 3 GAP**

**REJECT (10 crit / 3 gap)**
