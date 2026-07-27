# MovesD FINAL pass 4 — Codex confirmation on rev 5 (2026-07-28)
Verdict: REJECT (4 crit / 3 gap). Full prompt: /tmp/leanaudit/movesd_final4_prompt.txt. Raw output below.

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa43a-92fa-7961-a0c8-6eb501b9db8c
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

FOURTH final pass, on REV 5. History: rev 4 split the verifiers maximally (you 7/1 REJECT, independent 0/0 ACCEPT, the same four pushbacks adjudicated oppositely; gate arithmetic dual-confirmed). The orchestrator issued RECONCILING designs; rev 5 implements them (§12 table): (1) Option-rooted TreeModel — root_mem : ∀ x, mem none x is a LAW (your root-existence demand) while chains stay nonempty (the L5-(ns) constraint); (2) PresentNorm now TYPED (Presented.hnorm via policy-free totality + Galois uniqueness — your C-3); (3) the ∅ case as a machine-checked bridge theorem PrefOpt = {none} (your C-5, the note's Pref(∅) = {∅} literally); (4) MonicTie definitional law (your C-1's junk-shape concern — such shapes void their own PrefSet); (5) Threshold = the note's N(P̂) with ∀ N ≥ NP and Nshape as constructive witness (your C-6); (6) CanonPolicy parameter + hnorm adequacy (your C-4's junk-policy concern without pinning offset-P, which is HC-1's POL-PIN); (7) ClassFiberWelldef wired as D15's hwd (your C-7); (8) VerdictModel deferral documented (your gap). VERIFY each reconciliation discharges YOUR original finding — the designs claim to satisfy both verifiers' readings simultaneously; check the implementation, not the intent. Sweep end to end. A clean pass = ACCEPTED for formalization.

THE FROZEN NOTE:
## §D4-R — the per-shape-prefix mass law (assembly note 1)

*(2026-07-26. Assembly note [1] per ASSEMBLY_PLAN_2026-07-26.md §2, drafted
under the pass-4 GO verdict with its MANDATORY REPAIR
(ASSEMBLY_PLAN_PASS4_2026-07-26.md): the note nowhere asserts that a prefix
cylinder is the union of its finite terminating completions — every
identification runs through the MAXIMAL finite-or-infinite canonical run
defined below. Consumes: the DUAL-ACCEPTED §C (Theorem C, rev 14 —
Codex passes 16+17 CLEAN + the fresh-Fable confirm CLEAN on identical
text; the §C DUAL-ACCEPTED record, 2026-07-27) [rev 9 — pass-10 F2: the
former "rev 11b, passes 12+13 CLEAN" cite predated the Fable puncture
and the rev-12/13/14 (SAE) spiral], the accepted §B2-DEF — whose D.5/(S6b′) offset-P-lift
construction is L1's cited source [rev-2 correction of the old "ONLY §C"
claim; pass-1 finding 1] — and the plan's §1s/§2 notation. OPEN KERNEL,
named once [rev 2; pass-1 findings 1, 2, 6; RESTATED at rev 6 — the Fable
dual pass's F1 refuted the single-run ontology, so part (b) now lives at
the DIGIT-CELL level]: D4R.0-K := (a) L1's totality derivation (the
boundary enumeration) + (b) L5's exhaustive DIGIT-OUTCOME enumeration
(value cells; branch data are cell data, never f-data — L5 rev 6).
D4R.0-K is OPEN; every theorem below is CONDITIONAL on it
and on §C. Independent of [1v] VALUE,
[2a]/[2b] MENU, [3] RESUM; the honest perimeter is §D4-R.5, the sealed-gate
obligation §D4-R.6. Lemma numbers L1–L12 match the pass-4 confirmed list
one-for-one (L3 is a definition block; item 10 is the mass-law theorem
D4R.1).)*

**What this note is.** The decomposition note's OPEN-D4 was the class-3
prefix bound (3i): μ(P) ≤ p^{−A_net(P)}, A_net(P) := A(P) − W(P), uniformly
in p. This note restates, and derives CONDITIONAL ON THE KERNEL D4R.0-K,
the EXACT law behind it on the
canonical-policy branch tree [rev 6 — F1: the run map does not exist;
the exact law is the branch-weighted SUM]: for a fixed shape-prefix P̂,

  Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)}   (the mass law, D4R.1 —
                                     EXACT, each summand Theorem C(b))
  μ(P̂) := μ(⋃_η S(η,⊤)) ≤ C_P̂(p)·p^{−A(P̂)}   (the event bound, D4R.1 —
                                     equality iff branch mult. ≡ 1)
  C_P̂(p) ≤ M(P̂)·p^{W(P̂)}          (the pool bound, D4R.2 — (3i) up to the
                                     p-FREE residual-degree shape factor
                                     M(P̂) ≤ n^{|P̂|};
                                     rev 2, pass-1 finding 4)

with C_P̂(p) a literal finite count of realized value prefixes — no
quotient, no uniformity claim, no polynomial structure in q (that is
[1v]'s burden), and no sum over terminal completions anywhere.

### D4-R.0 The canonical branch tree, made total (the mandatory repair; rev 6)

**REV-6 ARCHITECTURE DECISION [F1 repair — the choice displayed].** Two
candidate repairs. (i) JOINT MULTISET PREFIXES — the level-i node datum
is the multiset of branch data over all eligible (side, ψ), the run a
multiset-valued function of f: REJECTED, because accepted §C proves
Theorem C for SINGLE-BRANCH lift-carrying histories only (C.0: "a read
history H = (ν₀, ν₁, …, ν_k)", one ψᵢ per node; "Theorem C applies to
each lift-carrying history separately"; the (ZC) state cylinder is
per-chain) — a multiset node's locus at depth ≥ 1 constrains f along
SEVERAL branches in DIFFERENT frames simultaneously, and §C has no mass
theorem for joint-over-branch loci; deriving one would be new
mathematics, not a citation of the accepted source. (ii) BRANCH-INDEXED
FIBERS with explicit multiplicity weights — ADOPTED: Pref(P̂) stays a
set of §C-native single-branch histories, every D4R.1 summand is
Theorem C(b) verbatim, and the run map is replaced by the branch TREE
T_can(f) (L2), a genuine function of f. Consumer duty: μ(P̂) is an
EVENT BOUND, exact only where branch multiplicity ≡ 1 (displayed at
D4R.1, D4R.4, D4-R.5, D4-R.6).

**The canonical policy.** The classifier is run with ONE lift rule: at
every recentering, the (S6b) OFFSET-P-LIFT realizer (§C C.0's named
canonical choice; §B2-DEF D.5 (S6b) with the pass-11 offset repair — the
sum anchored at the forced slot class j₀ ≡ h⁻¹·(target) mod e, slots
j₀, …, j₀+(g−1)e, prescribed digits). All histories in this note carry
these lifts and no others.

**L1 (canonical-choice totality) [kernel part (a); pass-4 lemma 1].**
The offset-P-lift is DEFINED at every eligible recentering: whenever the
classifier consumes a recentering side (e_read = 1) with value ν and
prescribed residual class, ν lies strictly above the (S6b) threshold
w(Φ̂) (I-aug at the read), and the offset-P formula returns a realizer t
with w(t) = ν and the prescribed class — for EVERY class (the offset
choice of j₀ removes (S6b)'s zero-class restriction), including the
boundary cases: minimal eligible ν, g = 1 (single slot), a > 0 anchors.
*Sketch:* §B2-DEF's offset-P paragraph: the weights ν − (j₀+ek)h are
zero-class by the choice of j₀ and clear the threshold when ν does; the
digits t_k are FUNCTIONS of the node data (stage + side value + class),
so the policy is deterministic. No node exists where the policy is
partial. [OPEN — kernel D4R.0-K part (a); rev 2, pass-1 finding 1. The
sketch consumes §B2-DEF's (S6b′) paragraph, which PROVES realizability at
any prescribed class and weight above the threshold — but the totality
QUANTIFIER (every eligible node of every realizable prefix, including
minimal ν, g = 1, a > 0) is NOT derived there or here. L1 is stated and
CONSUMED AS OPEN; its fresh-context boundary enumeration is the kernel's
part (a), due before D4-n3's verdict is read as kernel support.]

**L2 (the maximal canonical branch tree) [pass-4 lemma 2; REWRITTEN at
rev 6 — F1: the next-NODE datum is NOT a function of f: the descended
factor ψ and, at multi-side polygons, the side are BRANCH data (the
canonical policy fixes only lifts), so the rev-5 unique maximal RUN
H_can^max does not exist — at F1's instance two same-shape factors are
simultaneously eligible and no rule picks one].** For every f in the
monic degree-n coefficient box there is a UNIQUE maximal canonical
BRANCH TREE T_can(f): its root is the empty chain ∅; the children of a
chain η ∈ T_can(f) (η realizable, canonical lifts) are ALL next-node
data ν = (side s, its digit tuple, ψ, canonical lift) where s is an
eligible side of the polygon f produces in η's frame Ψ_η (L4), the
digit tuple is that side's digits read off f, and ψ ranges over the
eligible factors {ψ monic irreducible : deg ψ = g, ord_ψ R_anch(s) = μ}
of the side's residual; a chain has NO children iff its read returns a
terminal verdict (carried as leaf data). T_can(f) is prefix-closed —
a tree; the polygon and ALL side-digit tuples at each node are
FUNCTIONS of f, while eligibility of (s, ψ) is a condition on the FIXED
read data (L5: CELL data). So T_can(f) is a deterministic, choice-free
object for EVERY input — uniqueness is restored at the TREE level;
branches may be finite (verdict leaves) or infinite; no almost-
everywhere-termination statement is consumed anywhere in this note.
Each single branch of T_can(f) is a lift-carrying history in §C's
sense; the complete finite terminal histories of f are exactly
T_can(f)'s finite maximal branches, verdicts appended.

**L3 (the three-level object dictionary — binding notation) [pass-4
lemma 3; plan §1s].** Three objects, never shared symbols:
- SHAPE-PREFIX P̂ — a chain prefix with node VALUES forgotten: species,
  (e, h, g, μ, a) per node, strides, residue degrees w_r, AND [rev 6,
  F2] the per-read SIDE DATA — endpoints s₀'_r (hence right endpoint
  s₀'_r + w'_r), raw width w'_r, the stride-position/slot sets p_j
  (hence the digit count d_r), anchor a_r, AND [rev 9 — pass-10 F1,
  CRITICAL] the SIDE HEIGHT u*_r — §C C.0's rev-12 node-datum field
  (the right-endpoint height of read r's side: the read line new_r is
  the slope −h_r/e_r line through (j*_r, u*_r); γ_r := e_r·u*_r +
  j*_r·h_r, §C's DERIVED list) — all RETAINED: L9's fresh
  inventory, L11's deg R_anch,r = w'_r/e_r, and W(P̂)'s d_r consume
  them as shape data, so they must live in P̂.
  WHY u*_r IS RETAINED, NOT RECOVERED (the pass-10 F1 resolution,
  displayed): partial recovery exists — at e_r ≥ 2 the Bézout
  coefficient t^B_r ≠ 0 (e·s^B + h·t^B = 1 forbids t^B = 0 when
  e ≥ 2), so D.3(c)'s stride rule p_j = (j − t^B_r·γ_r)/e_r returns
  γ_r = (j − e_r·p_j)/t^B_r from any retained slot/position pair,
  whence u*_r = (γ_r − j*_r·h_r)/e_r; and at ADJACENT reads §C pins
  u*_r = the standing window-vertex height (the side hangs from the
  pinned vertex). But at an e_r = 1 read t^B_r = 0 (D.5's e = 1 base
  (P2)), so the stride rule p_j = j and the anchor are γ-BLIND, and at
  a NON-ADJACENT e_r = 1 read (the root included) the realizability
  conditions (NA)/(SAE) only BOUND the line by strict inequalities:
  distinct on-lattice u*_r at identical endpoints/strides are distinct
  strata with DIFFERENT below-line pin depths. So u*_r is NOT a
  function of the other retained fields, and it rides in P̂ as data.
  The side-digit tuples
  (d_j) and the lifts forgotten (plan §2's object). |P̂| := its number
  of reads.
- REALIZED LIFT-CARRYING PREFIX η = (ν₀, …, ν_k) — full node data WITH
  values and the canonical lifts; realizable in §C C.0's sense — read
  throughout this note as (NA) + (HV) + (SAE) [rev 6: the fresh-Fable
  §C pass (FABLE_VERIFY_C_2026-07-26.md, Finding 1) shows (NA)+(HV)
  alone is INCOMPLETE — the span-entry inequality (SAE) (read side
  strictly above the old box line at span slots < μᵢ) is a third
  independent data condition, certified by an (NA)+(HV)-passing history
  with EMPTY stratum; the repair LANDED as §C rev 12 and the repaired
  §C is DUAL-ACCEPTED at rev 14 (Codex passes 16+17 + Fable confirm —
  the §C DUAL-ACCEPTED record, 2026-07-27): realizability =
  (NA)+(HV)+(SAE) is now §C C.0's own live definition, so this note's
  reading is a CITATION of the accepted source, no longer an
  anticipation — rev 9, pass-10 F2].
  A realized prefix IS a lift-carrying history
  in §C's sense (§C histories need not be terminal); "prefix" is this
  note's role word. shape(η) := its shape-prefix.
- COMPLETE FINITE TERMINAL HISTORY H — a realized prefix whose successor
  outcome is a terminal verdict, the verdict included in the data.
  Reserved letter: H.
Prefix order: η ⪯ η′ iff η is an initial segment of the chain η′
(literal node-data + lift equality); η ∈ T_can(f) means η is a chain of
f's tree (L2) — the rev-6 replacement for the withdrawn "η ⪯
H_can^max(f)". Define

  Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts },
  C_P̂(p)  := #Pref(P̂).

RENAMING RULE (supersedes the plan's label): the plan §2's "Hist(P̂)" IS
this note's Pref(P̂) — the finite set of realized VALUE PREFIXES of
shape P̂, NOT the (possibly infinite) set of terminal completions and
NOT a set of complete histories. C_P̂(p) counts value prefixes.
Ledger data (shape functions): A(P̂) := the ledger exponent — the sum
over P̂'s nodes of the shape-determined fresh-volume exponents (L9
below) [rev 9: A CONSUMES u*_r — the fresh inventory's strip depths run
between the recorded old/new lines, each pinned only WITH its height;
A is a function of P̂ only because u*_r ∈ P̂]; W(P̂) := Σ_r w_r·d_r — the
pool dimension: read r carries d_r
side digits ranging in a pool of size Q_r = p^{w_r} [rev 9: W does NOT
consume u*_r — d_r is the retained stride-set count]. μ(·) := the mass on
the box normalized to 1 (μ(·) = #{f mod p^N ∈ ·}·p^{−nN} at any
sufficient level, per §C); the bare letter μ inside node tuples
(e, h, g, μ, a) remains the multiplicity — argument position
disambiguates.

### D4-R.1 D4R.0 — the digit-cell partition and its branch sets (three burdens, displayed)

**L4 (common-frame coherence) [the plan's BURDEN label (c), common
frame — NOT a kernel part: D4R.0-K has parts (a), (b) only (rev 6,
F3 — the stale "kernel part (c)" label struck); pass-4 lemma 4].** If two
inputs f, f′ both realize the prefix η = (ν₀, …, ν_k) — i.e. η ∈
T_can(f) and η ∈ T_can(f′) — then the frame reached after η is
IDENTICAL for both: the composite Ψ_η := Θ_k∘…∘Θ₀ depends only on η's
node data and lifts, never on the input. *Sketch — induction on k.* Each
move map Θᵢ (development at the key; recentering translation by the
lift; §C C.0.5's maps) is constructed from (the current key, νᵢ's data,
the lift tᵢ) alone; the canonical lift tᵢ is a function of node data
(L1); equal prior node data ⟹ equal keys and lifts ⟹ equal Θᵢ; compose.
Consequently the node-(k+1) reads of f and f′ are performed on the SAME
development coordinates of ONE frame — the two patterns are different
digit VALUES of the same development, never data in transported
coordinates. [This is the new lemma the plan's D4R.0(c) charges: §C
alone does not supply it; it is to be PROVED, not assumed.]

**L5 (digit-outcome totality and CELL exclusivity) [kernel parts
(a)+(b); pass-4 lemma 5; REWRITTEN at rev 6 — F1: exclusivity holds for
DIGIT data only; the rev-5 clause silently included ψ in "outcome data"
(contradicting L11's node-datum sentence) and is WITHDRAWN].** Fix a
realized prefix η — INCLUDING the EMPTY prefix
η = ∅ (k = −1), whose state cylinder is the FULL BOX: Σ_{−1} := the
coefficient box, Ψ_∅ := id, S(∅,⊤) = the box (§C C.0's EMPTY HISTORY
clause T(∅, Z) := Z, at Z = ⊤: no constraint, vol 1) [rev 2, pass-1
finding 3 — this empty case is the base of L6's induction] — with state
cylinder Σ_k := Ψ_η(S(η,⊤)) (§C C.1.5's object). Every f ∈ S(η,⊤)
produces, in the common frame Ψ_η, EXACTLY ONE full next-outcome DIGIT
DATUM:
 (i) the window polygon of the current development together with EVERY
     side's digit tuple (at the read resolution); or
 (ii) one terminal verdict.
Each next-NODE datum ν_{k+1} = (side, digits, ψ, lift) is the digit
datum's side data PLUS a branch choice (ψ; the side, if several) PLUS
the canonical lift.
TOTALITY: the outcome case list is EXHAUSTIVE — the displayed obligation
for the kernel derivation, which must cover, by name:
 (z)  ZERO cases — vanishing digit blocks: slot coefficients with
      valuation above every tested line, including total window
      degeneracy (every candidate coordinate zero to the relevant
      height); such f lie in the deeper strata typed by higher valuation
      clauses — none orphaned;
 (ep) ENDPOINT cases — adjacent reads (j* = μ_k, the (HV) hinge) and the
      polygon's endpoint slots;
 (ns) NO-SIDE cases — the window polygon admits no eligible side: a
      terminal verdict, not an orphan.
CELL EXCLUSIVITY [rev 6]: the DIGIT datum is a function of f (polygon
and digit values are computed from f's digits in the frame), so its
value-CELLS partition Σ_k, and each f realizes the unique cell it
computes. BRANCH SETS ARE CELL DATA, NOT f-DATA: a cell's eligible
continuations — the pairs (side s, ψ) with ψ monic irreducible,
deg ψ = g, ord_ψ R_anch(s) = μ — are conditions on the cell's FIXED
residual polynomials, so each cell carries a finite BRANCH SET; a
next-NODE stratum (one side's (α)/(β)/(γ) clauses) is a UNION of cells,
and DISTINCT node data need NOT have disjoint strata: two same-shape ψ
in one R_anch give two nodes over the SAME cells (F1's refutation
instance, displayed at D4R.1). NO per-node exclusivity is claimed
anywhere in this note — the rev-5 sentence ("distinct outcome data have
DISJOINT strata") is struck as REFUTED, not open.
[OPEN — kernel D4R.0-K part (b); rev 2,
pass-1 finding 2. The case labels (z)/(ep)/(ns) above are the
ENUMERATION OBLIGATION, not its discharge: "lie in the deeper strata"
does not yet exhibit, per degeneracy, the typing clause that receives
it, nor is non-overlap derived from the polygon conventions. Nothing in
this note discharges L5; every consumer below is conditional on
D4R.0-K.]

**Theorem D4R.0 (CELL PARTITION + BRANCH SETS — the kernel RESTATED at
rev 6; the rev-5 per-node partition WITHDRAWN as refuted).** On every
state cylinder Σ_k of a realized prefix η, the value-CELLS of the full
next-outcome digit datum — all polygon/digit values AND all terminal
verdicts — PARTITION Σ_k, and each cell determines its finite BRANCH
SET (the eligible (side, ψ) continuations) as cell data. [The rev-5
statement — next-NODE strata partition Σ_k — is REFUTED by F1's
instance (two same-shape factors, literally equal strata) and is not
restored; the partition claim survives only at the cell level.] Burden
ledger [rev 2 — honest status, pass-1 finding 6; relabeled rev 6]:
(a) TOTALITY = L1 + L5(totality): OPEN — this
is kernel D4R.0-K; (b) DIGIT-CELL EXHAUSTIVENESS = L5's case list: OPEN —
kernel D4R.0-K, with the prefix/complete distinction below (L6/L7); the
completion-union formulation remains STRUCK per the pass-4 mandate;
(c) COMMON FRAME = L4 (the plan's burden label, NOT a kernel part —
F3): DISCHARGED CONDITIONAL ON L1 (§C C.0: a
lift-carrying history determines every Θ_i and Ψ_H; L4's induction
supplies the input-independence). Theorem D4R.0 is therefore OPEN — it
is the kernel's statement, displayed here for its consumers' wiring,
not established.

**L6 (realized-branch cylinder identification) [pass-4 lemma 6;
restated on the tree at rev 6].** For every η ∈ Pref(P̂) (any P̂):

  S(η, ⊤) = { f : η ∈ T_can(f) }.                            (D4R-CYL)

Here S(η,⊤) is §C's joint stratum with the tautological terminal system
(Z = ⊤: no constraint, vol(⊤) = 1 — the plan §2's notation note).
*Sketch.* EMPTY PREFIX FIRST [F2 dispatch, exactly as D4R.1/L12]: for
η = ∅ (present iff P̂ = ∅), S(∅,⊤) = the FULL BOX by definition of the
state cylinder / T(∅,⊤) (§C C.0's EMPTY HISTORY clause T(∅,⊤) := ⊤,
vol 1; L5's Σ_{−1}), and { f : ∅ ∈ T_can(f) } is the full box too
(every tree carries the empty chain, L2) — so (D4R-CYL) holds by display,
NOT by Theorem C(a), whose history quantifier begins at the root read.
The two inclusions below therefore range over NONEMPTY η.
⊇: if η ∈ T_can(f), the branch's reads emit each νᵢ, so f satisfies
each stratum in its frame; by Theorem C(a), S(η,⊤) is exactly the locus
of the transported system T(η,⊤) — f solves it. ⊆: induction on i ≤ k,
BASE i = 0 [rev 2, pass-1 finding 3]: η_{<0} = ∅ ∈ T_can(f) is
automatic (L2), and the L5 application below is L5 AT THE EMPTY PREFIX
(Σ_{−1} = the full box — now inside L5's stated scope).
Given f ∈ S(η,⊤) ⊆ S(η_{≤i},⊤) (the transported systems nest), suppose
η_{<i} ∈ T_can(f). By L4 the tree's step-i read at the chain η_{<i}
happens in the same
frame Ψ_{η_{<i}} in which νᵢ's stratum is written; f lies in νᵢ's
stratum; by L5's CELL exclusivity f's digit datum lies in the unique
cell it computes, a cell inside νᵢ's stratum (the stratum's (α)/(β)/(γ)
clauses assert exactly νᵢ's side and digits — kernel part (b) reads the
clauses as the polygon assertion), so νᵢ's side and digits are f's; νᵢ's
ψ is in that cell's branch set (η is realizable — eligibility is cell
data, L5); and the
lift is canonical and equals η's (L1: a function of node data). Hence
νᵢ is among the children of η_{<i} in T_can(f), i.e. η_{≤i} ∈ T_can(f);
induction closes: η ∈ T_can(f). ∎
THE MANDATORY REPAIR, displayed: (D4R-CYL) is exact for EVERY f,
including inputs whose canonical run is INFINITE — a finite prefix
cylinder may contain such inputs, so it is NOT asserted to be the union
of the fibers of finite terminating completions. No such union appears
in this note.
COROLLARY (multiplicity; realizable ⟺ realized — DISJOINTNESS
WITHDRAWN at rev 6). The rev-5 disjointness claim (S(η,⊤) ∩ S(η′,⊤) = ∅
for η ≠ η′ ∈ Pref(P̂)) is REFUTED — F1's instance exhibits two distinct
same-shape η with LITERALLY EQUAL strata; a length-|P̂| chain of
T_can(f) need not be unique. What replaces it: the BRANCH MULTIPLICITY

  mult_P̂(f) := #{ η ∈ Pref(P̂) : η ∈ T_can(f) }               (finite, L8)

— a genuine function of f (L2: the tree is), with S(P̂,⊤) := ⋃_η S(η,⊤)
= {f : mult_P̂(f) ≥ 1}. Positive mass survives: for η = ∅ (iff P̂ = ∅)
mass 1 > 0 (the FULL BOX, L5 — NOT Theorem C(b), whose quantifier
begins at the root read);
for NONEMPTY η, Theorem C(b) gives mass p^{−A(P̂)} > 0 — so Pref(P̂)
is exactly the set of prefixes the canonical tree actually realizes
(realizable ⟺ realized, now for EVERY branch — F1's "unchosen branch"
failure mode is gone: the tree carries all branches).

**L7 (complete-history branch identification — separate statement)
[pass-4 lemma 7; restated on the tree at rev 6 — the run-map fiber
language WITHDRAWN with the run map].** For a complete finite terminal
history H = (η; v)
(v the terminal verdict), S(H,⊤) := S(η,⊤) ∩ (v's stratum in Ψ_η), and

  S(H, ⊤) = { f : H is a terminal maximal branch of T_can(f) }.

*Sketch:* (D4R-CYL) for η, plus L5 at the last step: within Σ_k, v's
stratum is exactly the cell whose digit outcome is the verdict v, i.e.
the chain η has no children there. ∎ NO disjointness over distinct H is
claimed (one f's tree may carry several terminal branches); a terminal
branch is a completed chain, a prefix cylinder (L6) a chain membership
at fixed length. The two statements are never
interchanged. [L7 is bookkeeping for downstream notes; the mass law
below consumes L6 only.]

### D4-R.2 D4R.1 — the exact prefix mass law

**L8 (finite value-prefix lemma) [pass-4 lemma 8].** Pref(P̂) is FINITE.
*Sketch:* the shape fixes the number of reads and every read's digit
count d_r and pool F_{Q_r} (Q_r = p^{w_r}, finite); by L11's rev-2
ENLARGED encoding an η is determined by its side-digit tuples PLUS its
factor-selection indices (each read r's index in a set of size
≤ m̄_r ≤ n, L11's residual-degree bound); realizability only
removes tuples. Hence #Pref(P̂) ≤ M(P̂)·∏_r Q_r^{d_r} < ∞,
M(P̂) ≤ n^{|P̂|}. ∎ [Pref(P̂) — NOT the
possibly-infinite set of terminal completions — is the set whose
cardinality is C_P̂(p): pass-4 lemma 8's point, restated.]

**L9 (shape-constant fresh volume) [pass-4 lemma 9; a citation of §C
C.3].** For every η = (ν₀, …, ν_k) ∈ Pref(P̂):

  ∏_{i=0}^{k} vol(E_fresh(νᵢ)) = p^{−A(P̂)}.

Each vol(E_fresh(νᵢ)) is a product of per-digit factors (alphabet
cardinality)⁻¹, each alphabet cardinality a power of p determined by the
history's SHAPE data (§C C.3, verbatim). [Rev 9 — pass-10 F1: §C's
"SHAPE data" is the node datum minus digit values and lifts, WITH the
side heights u*_r — the fresh inventory (§C C.1(ii)'s species
inventory) takes its strip depths between the recorded old/new LINES,
and each line is the slope −h_r/e_r line through (j*_r, u*_r), pinned
only with its height. Constancy on Pref(P̂) therefore NEEDS u*_r ∈ P̂,
which L3 now retains; without it, two η with equal endpoint/stride
data but different side heights would share a P̂ with DIFFERENT fresh
exponents, and A(P̂) would be ill-defined.] So the product depends on P̂
alone; A(P̂) := the resulting shape exponent (the ledger exponent). ∎

**Theorem D4R.1 (the mass law — SUM form; the event demoted to a bound)
[pass-4 lemma 10; REWRITTEN at rev 6 — F1: the union is NOT disjoint
and the rev-5 ⨆/event identity is WITHDRAWN as refuted].** Define the
prefix EVENT of P̂ as the plain union over the branch fiber,

  S(P̂, ⊤) := ⋃_{η ∈ Pref(P̂)} S(η, ⊤)
            = { f : some length-|P̂| chain of T_can(f) has shape P̂ }
            = { f : mult_P̂(f) ≥ 1 }        (L6 and its corollary).

Then the EXACT law is the branch-weighted SUM,

  Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)}          (D4R.1-SUM)

(equivalently: at every level N ≥ N(P̂), the level-N average of mult_P̂
is C_P̂(p)·p^{−A(P̂)} — finitely many indicators, summed), and the event obeys

  μ(P̂) := μ(S(P̂,⊤)) ≤ C_P̂(p)·p^{−A(P̂)}                  (D4R.1-EV)

by subadditivity, with EQUALITY iff mult_P̂ ≡ 1 on the event (e.g.
whenever every realized cell's same-shape branch set is a singleton —
the m ≡ 1 regime; true at the D4-n3 gate, §D4-R.6).

*Proof.* (D4R.1-SUM): each f with mult_P̂(f) ≥ 1 realizes EACH of its
mult_P̂(f) chains η ∈ Pref(P̂) as a branch of T_can(f) (L6; each carries
canonical lifts by L2 and is realizable because the tree emits only
realizable patterns, §C C.0 — the (NA)+(HV)+(SAE) class per L3's rev-6
binding). The EMPTY prefix η = ∅ (present iff P̂ = ∅) is dispatched FIRST,
separately from Theorem C(b): its fiber S(∅,⊤) is the FULL BOX (L5,
Σ_{−1}), mass μ = 1 = C_∅·p^{−A(∅)} with C_∅ = #Pref(∅) = 1 and
A(∅) = 0, by L5's normalized full-box display — NOT by Theorem C(b),
whose history quantifier begins at the root read. Each NONEMPTY summand
is Theorem C(b) with Z = ⊤ on the lift-carrying
history η: μ(S(η,⊤)) = ∏ᵢ vol(E_fresh(νᵢ)) — and L9 makes every summand
the SAME p-power p^{−A(P̂)}. Sum: C_P̂(p)·p^{−A(P̂)}. No disjointness is
consumed anywhere — the sum is over the INDEX SET Pref(P̂), each summand
a §C mass. (D4R.1-EV): μ(⋃) ≤ Σ by subadditivity, and equality forces
the pairwise overlaps to be μ-null, i.e. mult_P̂ = 1 A.E. on the event.
POINTWISE UPGRADE (displayed): by L8 the event ⋃_η S(η,⊤) is a FINITE
union of fibers, each a finite-level digit cylinder (§C C.2 cuts S(η,⊤)
at level N(η,⊤)), so any nonempty pairwise overlap S(η,⊤) ∩ S(η′,⊤) is
itself a nonempty finite-level digit cylinder, of POSITIVE mass > 0.
Hence a μ-null overlap is EMPTY, so a.e.-equality forces mult_P̂ ≡ 1
POINTWISE on the event — the "iff" holds at pointwise strength, not
merely a.e. NO sum over
terminal completions is used, and no termination statement is
consumed. ∎

REV-6 CHECK AT F1's REFUTATION INSTANCE (uniqueness/no-overcount
restored — displayed): n = 4, p = 5, P̂₀ = the root-only shape with node
(e,h,g,μ,a) = (1,1,1,2,0), full-span side (0,4)–(4,0) — whose display
carries the heights, so u*₀ = 0 (the monic-lead endpoint) was pinned
all along [rev 9] — A(P̂₀) = 14
(4 cluster + 6 below-line + 4 on-line pins). At the digit cell
(d₃,d₂,d₁,d₀) = (4,3,3,4): R₀ = z⁴+4z³+3z²+3z+4 = (z−1)²(z−2)² over F₅ —
the cell's same-shape branch set is {z−1, z−2} (both deg 1 = g₀,
ord 2 = μ₀): CELL data, per L5. For f = x⁴+20x³+75x²+375x+2500, T_can(f)
carries BOTH branches — ONE tree, no choice: uniqueness restored at the
tree level (L2). Pref(P̂₀) contains two chains η₁ ≠ η₂ over this cell
with literally EQUAL strata: the cell partition (L5) is intact, the sum
(D4R.1-SUM) counts the cell TWICE (mult = 2; C_P̂₀ counts ψ-labels), and
the event (D4R.1-EV) counts it ONCE — with strict inequality: over the
six two-double-root cells the rev-5 ⨆-identity overcounted by exactly
6·5^{−14}, which the sum/event split now carries honestly instead of
asserting away. ✓

### D4-R.3 D4R.2 — the pool bound ((3i) up to a p-free shape factor; rev 2)

**L11 (pool encoding and bound) [pass-4 lemma 11; ENLARGED at rev 2,
pass-1 finding 4].** A §C node datum carries MORE than shape + digits:
the residual factor ψᵢ the read descends at (it enters R_anch's split
and vtx(νᵢ), §C C.0). The digit tuple determines R_anch(νᵢ) completely
(strides and anchor are shape data), but when R_anch has SEVERAL monic
irreducible factors of the SAME shape (degree gᵢ, ord = μᵢ), the digits
do NOT determine WHICH is ψᵢ — no reconstruction lemma is available, so
the encoding is enlarged instead. Per read r define the SELECTION INDEX
s_r := the rank of ψ_r among the eligible same-shape factors of
R_anch(ν_r) — {ψ monic irreducible : deg ψ = g_r, ord_ψ R_anch = μ_r} —
ordered lexicographically by coefficient vectors in D.3(e)'s fixed
residue bases; their number is m_r ≤ m̄_r, where the SHARPER
residual-degree bound m̄_r := ⌊deg R_anch,r/(g_r·μ_r)⌋ counts how many
degree-g_r, ord-μ_r factors R_anch(ν_r) can hold (each contributes
g_r·μ_r to its degree). deg R_anch,r is SHAPE-DETERMINED: R_anch(ν_r) is
the residual polynomial of read r's polygon side, so deg R_anch,r equals
that side's NORMALIZED horizontal length ℓ_r := w'_r/e_r — the side's raw
horizontal width w'_r (a shape datum, distinct from the pool width w_r)
over its stride e_r, per §C's DOM proof (width-confinement (3): "the
residual factor, of degree w'/e_{i+1}"); ℓ_r equals the raw width ONLY
when e_r = 1. It is fixed by the side endpoints/strides
(shape data in P̂), never by the digit VALUES. COARSE CHAIN (kept so the
header's bound survives verbatim): deg R_anch,r ≤ n always, hence
m̄_r ≤ ⌊n/(g_r·μ_r)⌋ ≤ n. The map

  enc′: η ⟼ ( the side-digit tuples (d_j) of its reads r = 0, …, k ;
              the selection indices (s_r) )

is an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1, …, m̄_r}), where read
r's digits range in a pool of size Q_r = p^{w_r}. Hence

  C_P̂(p) ≤ M(P̂)·p^{W(P̂)},   W(P̂) = Σ_r w_r·d_r,
  M(P̂) := ∏_r m̄_r ≤ ∏_r ⌊n/(g_r·μ_r)⌋ ≤ n^{|P̂|}   (m̄_r as above:
      the SHARPER per-read residual-degree bound; coarse chain displayed)
  — p-FREE: the residual-side lengths (shape data) and n only.

*Injectivity — induction on the read index via L4:* given the shape and
the digit tuples through read i−1 AND the indices s₀, …, s_{i−1}, the
node data ν₀, …, ν_{i−1} and hence the frame Ψ_{η_{<i}} are
reconstructed (digits give each R_anch; s_r picks ψ_r; canonical lifts
are functions of node data, L1); read i's node datum is its shape data
(from P̂) plus its digit tuple (from the encoding) read in that frame
plus ψᵢ (from sᵢ) — so enc′(η) = enc′(η′) forces νᵢ = νᵢ′ for every i.
[Rev 9 — pass-10 F1: "its shape data (from P̂)" INCLUDES the side
height u*_i, retained per L3 — the reconstructed SIDE DATA field of
§C's node datum is thereby COMPLETE (u* rides in the shape part of the
encoding, never in the digit part). Without u*_i ∈ P̂ the
reconstruction was underdetermined exactly at non-vertex-pinned
e_i = 1 reads (L3's recoverability display), and injectivity did not
close.]
WHY (NA)/(HV)/(SAE) ONLY REMOVE: all three are predicates on NODE DATA
alone (§C
C.0 — (NA) the data inequality old(μᵢ) > new(μᵢ); (HV) an equation
between pattern data and the transported vertex value; (SAE) the
span-entry inequality — read side strictly above the old box line at
span slots < μᵢ, both lines data [rev 6: the third condition, per the
§C fresh-Fable Finding 1, L3's rev-6 binding]), i.e. predicates
on the encoded tuple — AFTER the injection above, they carve out a
subset of the enumerated product and can never enlarge the count.
Unrealizable tuples contribute empty strata and are simply absent from
Pref(P̂). [Rev 6: the selection index s_r is genuine BRANCH data — two η
differing only in s_r may have EQUAL strata (F1); enc′ counts BRANCHES,
which is exactly what the sum law D4R.1-SUM needs.] ∎

**Corollary D4R.2 (the original (3i), up to a p-free shape factor —
rev 2, pass-1 finding 4).**

  μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} ≤ M(P̂)·p^{W(P̂)−A(P̂)} = M(P̂)·p^{−A_net(P̂)},
  A_net(P̂) := A(P̂) − W(P̂),   M(P̂) ≤ n^{|P̂|} p-FREE (L11)

[rev 6: the first step is now D4R.1-EV's UNION BOUND — the rev-5
equality is withdrawn with the ⨆; the (3i)-class consumer needs only
this inequality, so D4R.2 survives F1 intact as a bound],

an INEQUALITY, uniform in p up to the constant M(P̂) (both exponents and
M are shape data, none depends on p) — NOT the literal (3i): the rev-1
"verbatim" claim rested on the unenlarged injection and is withdrawn;
any consumer needing the bare p^{−A_net} must first bound M(P̂), e.g.
M(P̂) = 1 whenever every read's m̄_r = 1 — its residual R_anch,r admits at
most one factor of its shape, deg R_anch,r < 2·g_r·μ_r (true at the D4-n3
gate instance, §D4-R.6). Untouched
by the death of value-fiber uniformity (D4R.3's retirement, §D4-R.5).

**PLAN RECONCILIATION — the (3i) interface [rev 3, pass-2 finding 1].**
What this note ESTABLISHES is D4R.2′:

  C_P̂(p) ≤ M(P̂)·p^{W(P̂)},   M(P̂) ≤ n^{|P̂|} p-FREE (L11)

(equivalently μ(P̂) ≤ M(P̂)·p^{−A_net(P̂)}). The plan's LITERAL (3i) — the
coefficient-one bound C_P̂(p) ≤ p^{W(P̂)} (equivalently
μ(P̂) ≤ p^{−A_net(P̂)}) — is NOT established here: it is SUPERSEDED by the
M-carrying form D4R.2′, and is recovered only on shapes with M(P̂) = 1
(e.g. the D4-n3 instance, §D4-R.6: under L11's residual-degree
definition M(P̂*) = m̄₀·m̄₁ = ⌊deg R_anch,0/(g₀μ₀)⌋·⌊deg R_anch,1/(g₁μ₁)⌋
= ⌊3/2⌋·⌊1/1⌋ = 1, where the OLD coarse ⌊n/(g_rμ_r)⌋ product spuriously
gave ⌊3/1⌋ = 3 at the linear depth-1 read — pass-3 finding 1). The
plan-side interface still states
the bare (3i); its update to consume D4R.2′ (carry M(P̂), or discharge
M(P̂) = 1 per consumer) is QUEUED for the next plan revision — NOT applied
here (this note does not edit ASSEMBLY_PLAN_2026-07-26.md).

### D4-R.4 D4R.4 — N-stability on the unquotiented Pref(P̂)

**L12 (uniform finite-level realization) [pass-4 lemma 12; empty case
dispatched at rev 2 — pass-1 finding 5, CRITICAL].** Define

  N(P̂) := max_{η ∈ Pref(P̂)} N(η, ⊤)   if Pref(P̂) ≠ ∅,
  N(P̂) := 1                            if Pref(P̂) = ∅.

EMPTY CASE, dispatched by display: L8 gives finiteness, NOT nonemptiness
— realizability can remove every value assignment, and no restriction
to C_P̂(p) > 0 is imposed. If Pref(P̂) = ∅ then S(P̂,⊤) = ⋃_{η∈∅} S(η,⊤)
= ∅ and C_P̂(p) = 0, so for EVERY N ≥ 1:

  #{ f mod p^N ∈ ∅ } = 0 = 0·p^{nN − A(P̂)} = C_P̂(p)·p^{nN − A(P̂)}

— D4R.4 is trivially exact at every level; the max-over-∅ expression is
never formed. NONEMPTY CASE [REWRITTEN at rev 6 — F1: the fibers are
NOT disjoint, so the exact law is the BRANCH-WEIGHTED count]: N(P̂) is
finite, and for EVERY N ≥ N(P̂):

  Σ_{η ∈ Pref(P̂)} #{ f mod p^N ∈ S(η,⊤) } = C_P̂(p)·p^{nN − A(P̂)}
                                                          (D4R.4-SUM)
  — each level-N residue counted with its multiplicity mult_P̂ — and

  #{ f mod p^N ∈ S(P̂,⊤) } ≤ C_P̂(p)·p^{nN − A(P̂)}         (D4R.4-EV),

with equality in (D4R.4-EV) iff mult_P̂ ≡ 1 on the event (the m ≡ 1
regime; true at the D4-n3 gate, §D4-R.6, whose sealed exact counts
therefore keep their meaning). The rev-5 exact EVENT count is
WITHDRAWN: at F1's instance it overcounts (D4R.1's displayed check).

*Sketch:* each N(η,⊤) is finite (§C C.2: 1 + the largest base level
among T(η,⊤)'s finitely many equations); the max is over the FINITE
unquotiented set Pref(P̂) (L8) — no quotient enters, so no
representative-dependence question arises (the plan §2's pass-1
concern-4 repair, restated on Pref). The EMPTY prefix η = ∅ (present iff
P̂ = ∅, Pref(∅) = {∅}) is split off FIRST: its fiber is the FULL BOX,
level-N count p^{nN} = C_∅·p^{nN − A(∅)} (C_∅ = 1, A(∅) = 0), by L5's
normalized full-box display — NOT by Theorem C(b), whose quantifier
begins at the root read. Sum Theorem C(b) over the NONEMPTY η in the
fiber at level N: each contributes exactly p^{nN}·p^{−A(P̂)} members (L9)
— (D4R.4-SUM) is a sum over the INDEX SET, no disjointness consumed
[rev 6: "the fibers are disjoint" is struck — refuted, F1]; (D4R.4-EV)
is the union bound within the level-N box, with equality iff no level-N
residue lies in two fibers. POINTWISE (no a.e. slack at finite level):
since N ≥ N(P̂), by L8 each fiber S(η,⊤) is an EXACT union of level-N
residue classes (§C C.2 cuts it at N(η,⊤) ≤ N), so a shared residue puts
a whole positive-count class in the overlap. Hence count-equality ⟺ the
fibers are residue-disjoint ⟺ mult_P̂ ≡ 1 POINTWISE on the event — the
finite-level statement carries no measure-zero exception, and passing to
the μ-limit recovers D4R.1-EV's a.e.-to-pointwise upgrade. The fixed shape
bounds all heights, hence all constrained levels, hence each N(η,⊤); an
a priori shape bound on N(P̂) is available but not needed — the finite
max suffices. ∎

### D4-R.5 Honest perimeter (what this note does NOT establish)

DEFERRED TO [1v] VALUE (everything value-aggregated): any claim that
C_P̂(p) is a polynomial in p, or a universal polynomial in a pool size
q, or p-uniform in any sense; any per-vertex or value-fiber distribution
statement; any (†)-style census epistemics for the counts. D4R.3 (the
rev-1 torus lemma) REMAINS RETIRED — FALSE for extension-valued
vertices, counterexample on record (plan §2); nothing here cites it.
DEFERRED TO [2a]/[2b] MENU: finiteness or completeness of the
shape-prefix catalogue; state types τ; cone geometry; any aggregation of
μ(P̂) over shapes or over ℕ-parameters. CONSUMER DUTY [rev 6 — F1's
cross-shape face]: one f may realize prefixes of SEVERAL shapes at the
same length (branch sets mix shapes — e.g. a cubic cell R₀ = ψ·(z−r)
carries a quadratic-descend AND a linear-descend branch), so the shape
events {S(P̂,⊤)} are a multiplicity-weighted COVER, not a partition:
Σ_P̂ μ(P̂) may exceed 1, and any [2a]/[3]/[5] aggregation must consume
D4R.1-SUM (branch-weighted) or the event BOUNDS, never a
partition-of-the-box claim. The plan §2's "patterns are FUNCTIONS of f"
is REFUTED (F1); plan rev 8 must carry this repair (queued, not applied
here — this note does not edit ASSEMBLY_PLAN_2026-07-26.md).
DEFERRED TO [3] RESUM / [5] EXHAUST: any resummation (geometric series
in heights or loop counts, rational-function structure in q);
drainage/exhaustion; termination rates. This note consumes NO
almost-everywhere termination: the maximal-run formulation is exact
without it.
STATUS [rev 2 — pass-1 finding 6: "unconditional modulo an OPEN kernel"
is conditional, and the old ESTABLISHED-HERE list claimed the kernel;
both withdrawn]. OPEN: D4R.0 — the CELL partition IS the kernel D4R.0-K
(L1 totality + L5 digit-cell exhaustiveness), underived in this note.
REFUTED AND WITHDRAWN [rev 6, F1]: the single-run ontology (rev-5 L2),
per-node-outcome exclusivity/partition (rev-5 L5/D4R.0), fiber
disjointness (rev-5 L6-corollary/L12), and the exact EVENT identities
(rev-5 D4R.1's ⨆, D4R.4's event count) — all replaced by the branch
tree + sum-law forms, never restored.
CONDITIONAL, proved here GIVEN the accepted §C + §B2-DEF AND the open
kernel D4R.0-K [the rev-6 conditionality on §C's then-queued (SAE)
repair is DISCHARGED at rev 9 — pass-10 F2: the repair landed as §C
rev 12 and the repaired text is DUAL-ACCEPTED at rev 14 (Codex passes
16+17 + Fable confirm, the §C DUAL-ACCEPTED record, 2026-07-27); this
note's (NA)+(HV)+(SAE) reading per L3 is now §C's own live C.0]: for ONE
fixed shape-prefix P̂ — the exact SUM law D4R.1-SUM with the event
bound D4R.1-EV (equality iff mult_P̂ ≡ 1), the pool bound D4R.2 (with
its p-free factor M(P̂), L11), and
the finite-level exactness D4R.4-SUM with D4R.4-EV (empty case
dispatched, L12), all on
the canonical-policy branch tree. Nothing in this note is
unconditional. What
IS discharged here outright: the object dictionary (L3), the
common-frame induction L4 conditional on L1 alone, the finite-or-
infinite branch-tree formulation (no termination consumed; T_can(f) a
function of f), and the
L6/L7 prefix-vs-complete separation — each conditional on the lemmas
it names and nothing else.

### D4-R.6 Sealed gate D4-n3 (the obligation; the instance PINNED at rev 2)

[Rev 2 — pass-1 finding 7, CRITICAL: the rev-1 spec left free choices
("side data fixed" but not displayed; no alphabets, no A/W/N numbers), so
no referee could derive the predictions from the note alone. The instance
is now pinned COMPLETELY, every number's derivation displayed.
PROVENANCE: pinned to the v1 seal's documented choices, made before any
census ran — verification/CASE_D4N3_SEALED_PREDICTIONS.md §S0 "FREE
CHOICES MADE" (FC1–FC9), which appeared mid-repair. The repairer's
independent fresh pin, derived from the note text alone BEFORE reading
the seal, agreed with FC1–FC6 and with every derived number (A = 11,
W = 7, N(P̂*) = 5, C = 3 and 48) — a genuine two-way convergence check —
and is superseded only on the p = 2 level pair (seal: {6, 7}; fresh pin:
{5, 6}) and by the seal's explicit partition-check stratum lists
(FC8/FC9), all adopted VERBATIM below.]

THE PINNED INSTANCE P̂* (n = 3, class-3 prefix; all free choices made
here, pre-census):
- Box: monic cubics f = x³ + c₂x² + c₁x + c₀, (c₂, c₁, c₀) ∈ ℤ_p³;
  μ(·) = #{f mod p^N ∈ ·}·p^{−3N}, normalized to 1.
- Cluster (inside E(ν₀)): c₂ ≡ c₁ ≡ c₀ ≡ 0 (mod p) — 3 pins, alphabet F_p.
- ν₀ (root read): key x; side of slope h₀/e₀ = 1/1, FULL SPAN slots [0,3]
  (single-side polygon (0,3)–(3,0); slot 3 = the monic lead, digit 1).
  Node tuple (e₀,h₀,g₀,μ₀,a₀) = (1,1,2,1,0); descend at ψ := the unique
  monic irreducible quadratic factor; F₁ := F_p[z]/(ψ) = F_{p²}, w₁ = 2.
  Side digits (pool F_p; alphabet FULL F_p — base heights all attainable):
  d₂ = c₂'s level-1 digit, d₁ = c₁'s level-2, d₀ = c₀'s level-3; d₀ ≠ 0
  (endpoint). REALIZABILITY (shape membership): R₀(z) := z³+d₂z²+d₁z+d₀
  = ψ(z)·(z−r), ψ = z²+s₁z+s₀ irreducible, r ∈ F_pˣ ⟺ (d₂,d₁,d₀) =
  (s₁−r, s₀−rs₁, −rs₀). Fresh pins of E(ν₀): 3 cluster + 3 below-line
  zeros (c₀ levels 1,2; c₁ level 1) + 3 on-line digits = 9, all F_p:
  vol(E_fresh(ν₀)) = p^{−9}.
- Key pin (canonical, deterministic): φ := x² + p[s₁]x + p²[s₀], with
  [·] ∈ {0,…,p−1} the least residues; w(φ) = e₀h₀g₀ = 2.
- ν₁ (depth-1 read at φ): window [0, μ₀] = [0,1]; f = B₀ + B₁φ with
  B₁ = x + b₁, b₁ := c₂ − p[s₁], and B₀ = β₁x + β₀,
  β₁ = c₁ − p²[s₀] − p[s₁]·b₁, β₀ = c₀ − p²[s₀]·b₁.
  LANDING CHECKS (automatic, NO fresh pins — the algebra displayed):
  (VERTEX) w(B₁) = 1 (1 + w(φ) = w(f) = 3, attained at x); (BOX)
  w(B₀) > 3: B₀'s height-3 digit is the pair (β₀ level-3, β₁ level-2) =
  (d₀ − s₀(d₂−s₁), d₁ − s₀ − s₁(d₂−s₁)) = (−rs₀+rs₀, s₀−rs₁−s₀+rs₁) =
  (0, 0) — forced by ν₀'s digits alone.
  PINNED SIDE: (e₁,h₁) = (1,3) — the MINIMAL (I-aug) slope (h₁/e₁ > w(φ)
  = 2); the side (0,4)–(1,1), i.e. w(B₀) = 4 exactly. Node tuple
  (e₁,h₁,g₁,μ₁,a₁) = (1,3,1,1,0) — a RECENTERING read (e₁g₁ = 1; its
  canonical (S6b) lift t₁ is carried per L3 but pins nothing inside P̂*).
  Digits: slot-0 digit d'₀ := B₀'s height-4 digit, level set
  {(β₀,4), (β₁,3)}, alphabet FULL F_{p²} (D.3(e): both leaf heights
  attainable) — ONE F_{p²}-digit = 2 base pins, vol(E_fresh(ν₁)) = p^{−2};
  d'₀ ≠ 0 (endpoint). Slot-1 lead d'₁ := B₁'s height-1 digit =
  z̄ + (b₁'s level-1 digit) = z̄ + (d₂−s₁) = z̄ − r — TRANSPORTED data
  (its box digit is ν₀'s d₂; the z̄-part is the monic): ZERO fresh pins.
  (HV), CONCRETE (adjacent, j* = 1 = μ₀): d'₁ = vtx(ν₀) =
  z̄^{−μ₀m̂₀}·z̄^{a₀}·((R₀/ψ) mod ψ) = z̄ − r, with m̂₀ = 0 — verified
  literally against the displayed division. (NA), CONCRETE: none — P̂*
  has no non-adjacent read. Depth-1 descend: R₁(z) = d'₁z + d'₀ has the
  unique monic linear factor z − s, s = −d'₀/d'₁ ∈ F_{p²}ˣ: every
  d'₀ ∈ F_{p²}ˣ is realizable.
- FACTOR SELECTION (L11's enc′): m_r = 1 at both reads (a cubic has at
  most one irreducible quadratic factor; R₁ is linear) — both selection
  indices are 1. The BOUND M(P̂*) = m̄₀·m̄₁ = ⌊deg R_anch,0/(g₀μ₀)⌋·
  ⌊deg R_anch,1/(g₁μ₁)⌋ = ⌊3/(2·1)⌋·⌊1/(1·1)⌋ = 1·1 = 1 (L11's
  NORMALIZED residual-degree definition ℓ_r = w'_r/e_r: at BOTH reads
  e_r = 1 — ν₀ has e₀ = 1, raw width 3 over span [0,3]; ν₁ has e₁ = 1,
  raw width 1, the linear residual — so normalized length = raw width,
  giving deg R_anch,0 = w'₀/e₀ = 3/1 = 3 (the root cubic) and
  deg R_anch,1 = w'₁/e₁ = 1/1 = 1 (the linear depth-1 residual); thus
  ⌊3/2⌋ and ⌊1/1⌋ are UNCHANGED under the normalized definition) — the
  rev-2 enlargement is trivial here. [The OLD coarse ⌊n/(g_rμ_r)⌋ product gave ⌊3/1⌋ = 3 at
  the linear read: the pass-3 finding-1 inconsistency, removed by the
  residual-degree definition.]

SIDE HEIGHTS AT THE GATES [rev 9 — pass-10 F1 propagation]: both P̂*
reads' u* were implicitly PINNED by the seal's explicit side displays,
which carry the heights — ν₀: full span (0,3)–(3,0), so u*₀ = 0 (the
monic-lead endpoint); ν₁: side (0,4)–(1,1), so u*₁ = 1 (ADJACENT,
j* = 1 = μ₀ — the (HV) window vertex pins it). Likewise the D4-m2
shape P̂₀ (D4R.1's rev-6 check): full-span side (0,4)–(4,0), u*₀ = 0.
The gates therefore tested the u*-complete shapes; NO gate number
changes value or meaning.

THE LEDGER, every number derived:
  A(P̂*) = 9 + 2 = 11 (L9; cross-check by direct pin count of T(η,⊤):
    c₂ mod p² (2 pins), c₁ mod p³ (3), c₀ mod p⁴ (4), plus the two ν₁
    pins binding c₀'s level-4 and c₁'s level-3 digits to functions of
    c₂'s FREE level-2 digit — 11 total).
  W(P̂*) = Σ_r w_r·d_r = 1·3 + 2·2 = 7 (read 0: three F_p digits; read 1:
    the 2-digit tuple (d'₀, d'₁) in pool F_{p²}; the (HV)-forced lead
    makes the pool bound strict — slack displayed, not hidden).
  A_net(P̂*) = 11 − 7 = 4;   M(P̂*) = 1.
  N(P̂*) = 1 + (largest pinned base level = 4, at c₀) = 5 (§C C.2) —
    identical for every η ∈ Pref(P̂*) and for both primes.
  C_P̂*(p) = N₂(p)·(p−1)·(p²−1), N₂(p) := (p²−p)/2 monic irreducible
    quadratics, r ∈ F_pˣ, d'₁ forced (×1), d'₀ ∈ F_{p²}ˣ free (×(p²−1)).
    [Closed form is DISPLAY ONLY — the seal is the per-p enumeration;
    polynomiality in p is [1v]'s burden, NOT claimed here.]
    p = 2: ψ = z²+z+1, r = 1 — ONE root tuple (d₂,d₁,d₀) = (0,0,1)
           [R₀ = z³+1 = (z+1)(z²+z+1)]: C_P̂*(2) = 1·1·3 = 3.
    p = 3: ψ ∈ {z²+1, z²+z+2, z²+2z+2}, r ∈ {1,2} — SIX root tuples
           (e.g. ψ = z²+1, r = 1 ⟹ (2,1,2): (z²+1)(z+2) = z³+2z²+z+2 ✓):
           C_P̂*(3) = 3·2·8 = 48.

SEAL BEFORE ANY CENSUS RUNS — each prediction now a NUMBER derived from
this note's displayed statements, committed with falsifiers:
 (1) C_P̂*(2) = 3 and C_P̂*(3) = 48, by direct enumeration of realizable
     value assignments — L11's enc′ with (NA)/(HV) applied;
 (2) A(P̂*) = 11 from L9's ledger (and the 11-pin cross-check above);
 (3) the counts #{f mod p^N ∈ S(P̂*,⊤)} = C_P̂*(p)·p^{3N−11}, TWO pinned
     levels per prime, both ≥ N(P̂*) = 5 (L12), on EXHAUSTIVE boxes
     (levels per the seal's FC7):
       p = 2:  N = 6: 3·2⁷ = 384     of 2¹⁸ = 262144;
               N = 7: 3·2¹⁰ = 3072   of 2²¹ = 2097152;
       p = 3:  N = 5: 48·3⁴ = 3888   of 3¹⁵ = 14348907;
               N = 6: 48·3⁷ = 104976 of 3¹⁸ = 387420489
     [the p = 3, N = 6 box exceeds the plan's stated 3¹⁵ feasibility
      line — no second admissible p = 3 level exists below it (FC7's
      stated deviation); EXHAUSTIVE enumeration, sampling banned];
 (4) the net bound μ(P̂*) ≤ M(P̂*)·p^{−A_net(P̂*)} = p^{−4} (D4R.2,
     M(P̂*) = 1 by L11's residual-degree definition, FACTOR SELECTION
     above): 3·2^{−11} ≈ 0.00146 ≤ 2^{−4} = 0.0625, and
     48·3^{−11} ≈ 0.000271 ≤ 3^{−4} ≈ 0.0123;
 (5) the PARTITION check (D4R.0/L5 tested literally) at BOTH pinned
     states, at the seal's pinned resolutions: (i) step 0 on the FULL
     level-N box, FC8's stratum list — non-cluster ∪ 20 valuation lumps
     ∪ the p²(p−1) on-line digit cells of the target region (the
     census's resolution of L5's (z)/(ep)/(ns) enumeration at this
     depth); (ii) step 1 within each realized ν₀-cell (1 digit tuple at
     p = 2, 6 at p = 3), FC9's list — the p²−1 δ-cells {w(B₀) = 4,
     height-4 digit δ ≠ 0} ∪ DEEP {w(B₀) ≥ 5} (the (z) lump at this
     resolution) — membership sum EXACTLY 1 for every member: 0
     double-counts and 0 orphans tolerated, both primes, both levels.
FC8/FC9 REPRODUCED VERBATIM [rev 3, pass-2 finding 2 — so the step-0 and
step-1 partition tests of (5) are reconstructible from THIS NOTE ALONE;
this is what makes the provenance bracket's "adopted VERBATIM below" true]:
 FC8 (STEP-0 PARTITION), verbatim from the seal §S0: "the sibling strata
   of the root read are resolved as: NC (non-cluster) ∪ 20 valuation lumps
   (V₀, V₁, V₂) := (min(v(c₀),4), min(v(c₁),3), min(v(c₂),2)) on the
   cluster, EXCEPT the target region {V₀ = 3, V₁ ≥ 2} which is refined
   into its p²(p−1) on-line digit cells (d₂, d₁, d₀) ∈ F_p × F_p × F_pˣ.
   Deeper structure of non-target lumps is other prefixes' business (not
   resolved by this gate)." [The COUNT 20 derived: on the cluster
   v(c₀),v(c₁),v(c₂) ≥ 1, so V₀ ∈ {1,2,3,4}, V₁ ∈ {1,2,3}, V₂ ∈ {1,2} —
   4·3·2 = 24 cluster lumps, minus the 4 target-region lumps {V₀ = 3,
   V₁ ∈ {2,3}, V₂ ∈ {1,2}} carved into the digit cells = 20.]
 FC9 (STEP-1 PARTITION), verbatim from the seal §S0: "within each quad·lin
   digit cell, the ν₁-outcome strata are the p² − 1 δ-cells {w(B₀) = 4
   with ht-4 digit δ ≠ 0} plus DEEP {w(B₀) ≥ 5} (the (z) zero/deeper lump
   at this resolution)."
 So the step-0 system of (5)(i) is {NC} ∪ {the 20 valuation lumps} ∪ {the
   p²(p−1) on-line digit cells}, and the step-1 system of (5)(ii) inside
   each realized digit cell is {the p²−1 δ-cells} ∪ {DEEP} — the exact
   systems whose per-box membership sum the gate checks EQUALS 1 (0
   double-counts, 0 orphans).
REV-6 GATE RE-DERIVATION [F1 architecture change — every sealed number
RE-CHECKED under the branch reading, none adjusted]: the sealed numbers
keep their values AND their meanings because branch multiplicity ≡ 1 on
S(P̂*,⊤): at every realized ν₀-cell, R₀ = ψ·(z−r) holds EXACTLY ONE
irreducible quadratic ord-1 factor (deg R_anch,0 = 3 < 2·g₀·μ₀ = 4 —
two disjoint eligible ord-μ₀ quadratic factors would need degree ≥ 4; the
pinned factorization R₀ = ψ·(z−r) with deg R₀ = 3 makes the quadratic
unique) and R₁ exactly one monic linear factor — m_r = 1 PER CELL at
both reads (the FACTOR SELECTION line), so within P̂* distinct η occupy
distinct digit cells, mult_P̂* ≡ 1, and D4R.1-EV/D4R.4-EV hold with
EQUALITY here: predictions (1)–(4) retain their exact-count meaning
verbatim. Prediction (5)'s FC8/FC9 systems are digit-VALUE cells —
exactly rev 6's L5 CELL partition, so the passed partition test now
tests the RESTATED kernel statement directly, not the withdrawn
per-node one. CROSS-SHAPE face, recorded: the same realized cell also
carries the LINEAR-descend branch (z−r) — a prefix of a DIFFERENT shape
realized by the same f; the gate never tested shape-event disjointness
(its sibling strata are cells), consistent with its structural
blindness to F1 (dual-pass record). (SAE)-CLEANNESS [the §C Finding-1
condition, L3's rev-6 binding — since rev 9 a citation of the live §C
C.0 (rev 12, dual-accepted rev 14)]: an (SAE)-failing history has an EMPTY
stratum, so had any of the 3 (p = 2) or 48 (p = 3) counted prefixes been
(SAE)-violating, the census's exact per-cell counts would have exposed
the deficit — the exact match over all 4 configs is evidence the gate
instance is (SAE)-clean. VERDICT: NO sealed number changes value or
meaning; NO RE-RUN NEEDED. The multiplicity-> 1 regime (m ≥ 2 cells,
F1's n = 4 instance) is exercised by NO gate yet — a rev-6
multiplicity gate is left QUEUED for the assembly, not seal-adjusted here.
RECORDED LIMITATION (plan §2, verbatim scope): μ = 1 only — this gate
exercises D4R.0/1/2 and does NOT touch the value-count risk; the
μ ≥ 2 / a > 0 danger is gated in [1v] at n = 5 and over F_q. Also
m_r = 1 at both reads, so the rev-2 factor-selection coordinate is NOT
exercised by this gate. A PASS certifies the partition and the mass law
AT THE TESTED SHAPE and nothing on §D4-R.5's deferred list — in
particular a PASS does NOT close the kernel D4R.0-K (its derivation
burden is textual, not numerical); a FAIL on (5) REFUTES D4R.0-K.
Case-K discipline: this census may not be re-read as a pass if any
sealed falsifier fires.

---

ADDENDUM:
## §D4-R PASS RECORD (pass 10 on rev 8: 1 critical, 1 gap — the §C spiral crossing) and the rev-9 repairs

Pass 10 (`D4R_PASS10_2026-07-26.md`) punctured the dual-acceptance shot at the §C/§D4-R
SPIRAL CROSSING: §C's rev-12 (SAE) repair added the SIDE HEIGHT u* to the node datum,
and §D4-R rev 8 — written against the pre-puncture §C — never picked it up. F1
(CRITICAL): L3's shape data omitted u*_r, so L9's A(η)-constancy and L11's enc′
injectivity were unproved against the live §C. F2 (gap): the opening still cited
"rev 11b, passes 12+13 CLEAN" and D4-R.5 still called the (SAE) repair "queued".
Rev 9, in place (§C untouched):
- F1 RESOLUTION — RETAINED, not recovered: u*_r is NOT a function of the other retained
  fields. Partial recovery displayed in L3: at e_r ≥ 2, t^B_r ≠ 0 and D.3(c) gives
  γ_r = (j − e_r·p_j)/t^B_r, hence u*_r; adjacent reads are vertex-pinned. But at
  e_r = 1, t^B_r = 0 ((P2)) makes strides/anchor γ-blind, and non-adjacent e = 1 reads
  are bounded only by (NA)/(SAE) inequalities — distinct on-lattice u*_r = distinct
  strata with different below-line pin depths. So L3 retains u*_r (with γ_r displayed);
  L9 states constancy NEEDS u*_r ∈ P̂ (A consumes it via strip depths); L11's
  reconstruction notes u* rides in the SHAPE part (injectivity closed); the ledger
  paragraph splits A (consumes u*) from W (does not — d_r is the stride count).
- GATES: D4-n3's u* were implicitly pinned by the seal's side displays ((0,3)–(3,0):
  u*₀ = 0; (0,4)–(1,1): u*₁ = 1, adjacent) and D4-m2's by (0,4)–(4,0): u*₀ = 0 —
  bracket added at D4-R.6 + the D4R.1 rev-6 check; NO gate number changes.
- F2 — cite sweep (4 edits): opening → DUAL-ACCEPTED rev 14 (Codex 16+17 + Fable
  confirm); L3's REALIZED bullet + D4-R.5's STATUS → repair LANDED, conditionality
  DISCHARGED; D4-R.6's (SAE)-cleanness bracket → citation of the live C.0.
STATUS: rev 9 awaits fresh dual passes (Codex + Fable); §D4-R NOT accepted.

## §D4-R: DUAL-ACCEPTED (2026-07-27 — Codex pass 11 + Fable confirm, both CLEAN on identical rev-9 text)

The dual bar is met on §D4-R at rev 9: Codex pass 11 (0/0, `D4R_PASS11_2026-07-27.md`)
and the fresh-Fable confirm (0/0, `FABLE_CONFIRM_D4R_REV9_2026-07-27.md`) on the SAME
text. The Fable confirm ADJUDICATED the u* question against its own predecessor: at
e = 1, (P2) forces t^B = 0 so p_j = j is γ-blind (an explicit witness pair — cubics
identical in all u*-free retained fields, u* = 1 vs 2, different A — forces retention
in P̂). Full spiral: rev-5 acceptance → Fable puncture (F1) → branch-tree rebuild (revs
6–9, gates D4-n3 + D4-m2 both PASSED) → Codex 8+9 clean → the u* spiral-crossing (pass
10) → rev 9 → Codex 11 + Fable confirm CLEAN.

KERNEL-STATUS UPGRADE (same date): the kernel derivation `D4R0K_DERIVATION_2026-07-26.md`
(rev 3) is DUAL-VERIFIED (Codex pass 3 SOUND + Fable pass CLEAN; counterexample attempts
died at G3′/G2/G5). D4R.0-K parts (a) totality and (b) structural exhaustiveness are
DISCHARGED by it. §D4-R's conditionality is now: dual-accepted §C (rev 14) +
dual-accepted §B2-DEF (D¹¹d) + the residual D4R.0-K(c) — the verdict pin (alphabet V +
halting rule τ + the UNIFORM per-class detection cap), precisely stated, owned by the
plan's [3t] via VP. CROSS-NOTE RESIDUE (Fable confirm, gap-grade): §M-SPECIES's P̂ gloss
(word + one height slot) is refuted by the witness pair — owned by §M-SPECIES's spiral.

THREE artifacts now through the full dual standard: §B2-DEF, §C, §D4-R (+ the kernel
derivation dual-verified). 


CONSUMED INTERFACE (MovesC):
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL

/-!
# MovesC/Defs — shared vocabulary for §C, the composition theorem  [ROUND 6]

**ROUND 6 (2026-07-27).** ONE targeted change, closing the single defect of the round-5 audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R5_2026-07-27.md` (REJECT — finding 7 / blocking list
1–3: `inFreshBand` bounded the fresh band by the COARSE post-landing `childWidth` staircase
`Node.lineStep`, while rev 14 C.1(ii)'s species inventory runs per FINE slot — frame-`i`
blocks of width `Dwidth`, C.1.0(a). Since `childWidth = e·g·Dwidth` and the line descends, at
`e·g > 1` the coarse left-edge value exceeds the later fine slots' true valuations: coordinates
with heights in `(slotVal(fineSlot b), lineStep b]` — which rev 14 leaves UNCONSTRAINED — were
admitted into the band, tagged non-value, and forced into spurious zero strips by
`fresh_cover` + `fresh_assembled`: a locus shrink and an `mstar` inflation). The change:
* **the fine-slot band boundary** — `inFreshBand`'s upper edge is retyped to
  `H.htH i c ≤ ν.slotVal (ν.fineSlot idx)`: each coordinate is bounded by ITS OWN fine slot's
  exact valuation `new(j) = line.at(j·Dwidth)` — the recorded fine-slot valuation law, the SAME
  granularity at which round 5's `IsValueCoord`/`IsValueSupport` already read the geometry. The
  band at fine slot `j` is now exactly `(floor, new(j)]`: the strip zeros strictly between floor
  and `new(j)`, plus — at span slots — the on-lattice level set AT `new(j)` (the value
  positions, the band's upper edge): rev 14 C.1(ii)'s actual per-slot inventory, nothing above
  it. Past the (γ) crossing `new(j) ≤ floor` empties the slot's band — the self-truncation now
  cuts per FINE slot (no coarse overhang). `Node.lineStep` is retained as the post-landing
  (ZC-a) staircase convention ONLY (its docstring retagged); at recenterings
  (`childWidth = Dwidth`) the two boundaries coincide, so all round-5 semantics there are
  unchanged. `fresh_band`/`fresh_cover`/`mstar_eq` consume the band BY NAME — byte-stable; the
  23 frozen units are BYTE-STABLE.

[ROUND 5 header, kept for the audit trail:]

**ROUND 5 (2026-07-27).** ONE targeted change, closing the single blocking structure of the
round-4 audit `lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R4_2026-07-27.md` (REJECT — finding 10 /
blocking list 1–4: the fresh laws determined only a partition of the band and its total
cardinality, not the geometric clause SPECIES; an all-singleton-zero construction impersonated
the value clauses, changing Theorem C(a)'s locus). The 23 frozen units are BYTE-STABLE; every
other round-4 field is unchanged. The change:
* **exact geometric fresh-clause identification** — `Node.fineSlot`/`Node.spanSlot`/
  `Node.slotVal` name the read's OWN development geometry (C.1.0(a): frame-`i` blocks of width
  `Dwidth = deg Φ_i`; the side span `[s₀, s₀+wSide]`; the exact valuation
  `new(j) = line.at(j·Dwidth)`). `IsValueCoord` (the VALUE positions: span slot ∧ height = that
  slot's exact valuation — rev 14 C.1(ii)'s on-lattice value-digit locus: (α) digits + the
  non-adjacent endpoint; β/γ slots carry STRICT bounds, never a value) and `IsValueSupport`
  (support = the COMPLETE level set of ONE recorded span slot at its recorded exact valuation,
  membership as an IFF over the whole box — never `⊆`) retype `fresh_assembled`: the STRIP
  branch (singleton zero, codim 1) now additionally requires its coordinate NOT a value
  position; the VALUE branch requires `IsValueSupport` (subsuming round 4's bare
  constant-height law); the per-type codim laws are unchanged (strip: `codim = 1`; value:
  `codim = support.card`). The audit's all-singleton-zero construction is UNBUILDABLE — walk in
  `fresh_assembled`'s docstring and blueprint § ROUND 5. The only remaining freedom in a value
  clause is the emitted value `v` inside its alphabet — the declared graded-provenance boundary
  (blueprint R4.B.2), not geometry.

[ROUND 4 header, kept for the audit trail:]

**ROUND 4 (2026-07-27).** Retype of the global layer against §C REV 14 EXACTLY, after the
round-3 audit `lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R3_2026-07-27.md` (REJECT — the rev-14
delta). The 23 frozen units are BYTE-STABLE. Changes, keyed to the audit's final-disposition
list (its finding 20):
* **(SAE) + the full realizability class (findings 8/9)** — `TransitionAdmissible νp ν` is the
  NAMED per-step predicate: (NA)+(HV)+(SAE) at the appended read. (SAE) is rev 12's two-line
  display: `new(j) > old(j)` STRICT at every span slot `j ∈ [s₀', j*]` with `j < μ`, and
  `new(μ) = old(μ)` at the adjacent tie. `Realizable H` := every appended read is
  transition-admissible — the THREE-condition class (the round-3 two-condition docstring and
  definition are gone; the certified F-EMPTY configuration now violates `Realizable`).
* **TRANSITION-ADMISSIBLE per-step interface (findings 10/16)** — per-step consumers take it
  through `JetSetup.realizable` (definitionally the ∀-step form of `TransitionAdmissible`);
  `C3.lineDom` now HYPOTHESIZES `Realizable` (rev 14's DOM: "for every realizable prefix").
  The round-3 weak vertex-entry ties (`old ≤ new` at `j*`, hinge equality) are DELETED from
  `HistoryCoherent`: the span-entry inequality is (SAE)'s, sourced from REALIZABILITY, never
  from coherence (finding 16's "wrong semantic hypothesis boundary" repaired).
* **u*, the side height (finding 11)** — `Node.ustar` (absolute v_p-scale) with `hLineU`: the
  read line passes through `(j*, u*)` — slope from coherence's slope law, intercept pinned by
  `u*`. `Node.gam : ℤ` records the augmented-scale TOTAL SIDE WEIGHT `γ = e·(STR·u*) + j*·h`
  (rev 14 C.0, the argument of D.3(c)'s stride positions); the tie lives in `HistoryCoherent`
  (where `STR` exists) and its ℤ-typing IS the on-lattice condition. Adjacent vertex
  anchoring (`u* =` the standing window-vertex height) = (SAE)'s equality line + `hLineU`.
* **canonical Bézout pair (finding 12)** — `hbezCanon : 0 ≤ t < e` selects THE canonical pair:
  unique in the window, hence a FUNCTION of `(e, h)` only (rev 14's `(sᴮ, tᴮ)`). It extends
  the accepted `Stage.he1t` (P2) pinning to every `e`: at `e = 1` the window FORCES
  `t = 0, s = 1`, so `m̂ = 0` at recenterings BY the convention — rev 14's exact sentence;
  the round-3 field `hspecRecBez` is deleted as now derivable.
* **ψ irreducible (finding 13)** — `hψirr : Irreducible ψ` (rev 14: "monic irreducible over
  F_i"; recenterings are consistent — degree-1 polynomials over a field are irreducible).
* **anchored-residual provenance (finding 14)** — `hAnchor : e·a = s₀ − t·γ` pins the anchor
  to D.3(c/d): `a = p_{s₀}(γ) = (s₀ − t·γ)/e` is the z-order of the side residual (its lead
  digit is nonzero, `hpat0`), so with `hRanch`'s consecutive powers `Ranch` IS rev 14's
  `R_anch = Σ_j d_j·z^{p_j(γ)−a}`; `a` can no longer move freely under (HV).
* **fresh-species coverage (finding 17)** — `inFreshBand` names the D.11 band as a coordinate
  predicate; `fresh_band` (every clause support ⊆ the band — replaces
  `fresh_above`/`fresh_interior`, adding the upper edge), `fresh_cover` (every band coordinate
  lies in SOME clause's support — EXACTLY one, by `FreshData.disj`), and `fresh_assembled`'s
  value branch adds the per-clause `codim = support.card` (TYP(b)'s |alphabet| = |piece|,
  now placed PER CLAUSE). The permutation loophole is dead: the total codimension decomposes
  coordinate-by-coordinate over the band; nothing can move to unrelated above-floor supports.
* **cutoff (finding 18)** — `hN : 1 ≤ N` (Theorem C's quantifier is `N ≥ N(H,Z)` with
  `N(H,Z) ≥ 1`; the `≥ N(H,Z)` half is automatic inside the box — `coordOf_lt` bounds every
  equation level below `N` — and otherwise existence-side). `N = 0` presentations are gone.
* **root-side height (finding 19)** — `root_height`: the root line dominates the cluster
  floor (`1 ≤ line₀.at b` on the root factor interior — DOM's rev-11 base display), so
  `mstar_eq` at `i = 0` counts the cluster zeros; the root intercept is no longer free.

[ROUND 3 header, kept for the audit trail:]

**ROUND 3 (2026-07-26).** Rebuild of the GLOBAL layer after the round-2 audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R2_2026-07-26.md` (REJECT: blockers 55-60 — the local
layer certified sound, the global layer admitted trivial presentations). The local layer
(C0/C1/C2 clause vocabulary, `LevelClause`/`FreshData`/`TypObject`/`DomData`/`ZCData`, lines,
species) is BYTE-STABLE. Changes, keyed to blockers:
* **B55 (no provenance ties)** — `JetSetup` gains the presentation spine `pres`
  (`pres_zero` = the concrete frame-0 p-adic digit chart `baseDigit`; `pres_theta` = each
  `Theta i` translates frame-(i+1) presentations of `f` to frame-i presentations of the SAME
  `f`; `pres_block` = frame-(i+1) presentations are block-local over the recorded landing key's
  development — C.1.0(a)); the recorded landing keys `keys` with `keys_mid`+`landing`
  (`LandingKey`, D.5/D.10 at the node's data); `Sigma`'s `recursion` now runs through the
  STRATUM (`stratum` + `inh_implied` — C.1(i) as a sentence); `fresh` is pinned by
  `fresh_assembled` (strip / TypObject-value shapes on ht-level sets) and `mstar_eq`.
* **B56 (final landing)** — `landing` holds at EVERY `i < len` including the last: the final
  read's landing key obeys the same recorded-data lift law (`LandingKey`).
* **B57 (mstar RHS)** — `mstar_eq`: `(fresh i).mstar` EQUALS the D.11 species-inventory count,
  the fresh-band cardinality `#{c : idx < prevRim, floor_i < htH_i(c) ≤ lineStep_i(c)}`
  computed from node data (the band self-truncates at the (γ) crossing slot).
* **B58 (thmC_a)** — `S(H,Z)` is INDEPENDENTLY defined (`JetSetup.SHZ`, the transported system
  `T(H,Z)` as an ∃-chain over the recorded moves); `thmC_a` states the classifier-locus =
  transported-image EQUALITY plus the mass carriage.
* **B59 (ht + line ties)** — the bare `ht` field is DELETED: heights are the DEFINED K1-chain
  formula `History.htH` (LST(i)'s sentence now exists; the graded-bridge FLAG moves to its
  docstring). The read-line intercept is tied by the new `HistoryCoherent` vertex-entry clauses
  (endpoint comparison at `j*`, hinge EQUALITY at adjacent reads).
* **B60 (degenerate fresh)** — `fresh_assembled` + `mstar_eq` exclude empty/afresh-free
  presentations wherever the recorded geometry has a nonempty fresh band.
* **F10 (the m̂ index)** — CONFIRMED A REAL BUG and fixed: D.3's header fixes "(a stage with)
  READ INDEX (e,h) and Bézout (s,t)" — the D.5 lift positions and D.8 normalization
  `m̂ = −t·h·g` use the READ's own pair, while `Stage.(e,h,s,t)` records the frame-CREATING
  read's. `Node` now records its read-side Bézout pair `(s,t)` (`hbez`, recentering pinning
  `hspecRecBez`), `Node.mhat := −t·h·g` uses it, `IsNodeLift` replaces the mis-indexed
  `IsStandardLift σ` call in `HistoryCoherent`, and the child-frame ties `σ'.s = ν.s`,
  `σ'.t = ν.t` pin the recorded pair to the tower.

[ROUND 2 header, still accurate for the local layer:]

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §C REV 2 (ACCEPTED 2026-07-26, passes 12+13
CLEAN), derivations `C10B_DERIVATION_2026-07-26.md` / `C15_DERIVATION_2026-07-26.md` (Route B).
ROUND-2 rebuild after the round-1 STOP-THE-LINE audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_2026-07-26.md`. Point-by-point answers:
blueprint `MOVESC_LEAN_BLUEPRINT_2026-07-26.md` § ROUND 2. Definitions only — no theorems,
no `sorry`, no axioms.

## What round 2 changes (the audit's five principal failures)

1. **`Node`/`History` now ENFORCE the §C meanings as `Prop` fields**: `Ranch` is literally the
   anchored residual `Σ_k pat(k)·z^k` (stride positions collapse to consecutive powers since
   `e·s + h·t = 1`); `ψ` is monic of degree `g` with `ord_ψ(Ranch) = μ` exactly; species
   constraints (`increment → e·g > 1`, `recentering → e = g = 1`, `ψ = z − center`); the frame
   link `Dwidth = deg Φ`; the residue root `z̄` is a genuine root of `ψ`. `HistoryCoherent` keys
   the transition on the PARENT node's recorded data (`IsStandardLift` of the recorded `ψ, g` +
   `TransitionCoreL` at the recorded `e, h, z̄`; `IsRecenteringCore` at the RECORDED lift — no
   free existentials), adds window containment `s₀'+w' ≤ μ`, the (I-aug) slope chain, the width
   chain `D_{i+1} = e·g·D_i`, the absolute-scale slope law `slope·(e·STR·D) = h`, and the root
   frame `deg Φ₀ = 1`. Later `root` species are excluded by `History.root_iff`.
2. **`Realizable` is the genuine (NA)/(HV)**: (NA) compares the two lines at the BASE index
   `μ_i·D_{i+1}` (the audit's slot/base mismatch fixed); (HV) is the data IDENTITY
   `pattern lead of ν_{i+1} = vtx(ν_i)` with the FULL transported vertex value
   `vtx = z̄^{a−μ·m̂}·((Ranch/ψ^μ) mod ψ)(z̄) ∈ F` — scalar factors included, valued through the
   ambient field (the round-1 `∃ lead, vtxPoly = lead` tautology is gone).
3. **The counting layer is ADDRESS-FREE (Route B / rev 9)**: `FreshData` no longer assigns
   coordinate values. A fresh clause is a `LevelClause` — a constraint carried by a SUPPORT
   (the weight-γ′ level set / strip region), a codimension, and an EXACT-FIBER-COUNT law
   (division-free: `#{supported y | sat y}·p^codim = p^{|support|}`) — exactly what TYP(b)'s
   kernel-coset argument supplies (`TypObject → LevelClause` is a manifest unit). The state is
   loci + masses + the (ZC) invariant; no pin address is data anywhere.
4. **`JetSetup` is re-indexed and LINKED**: `Sigma 0` is the FULL BOX `Σ_{−1}` (field `init`),
   `fresh i` is consumed once, between `Sigma i` and `Sigma (i+1)` (the audit's k = 0
   countermodel is unbuildable); all recursion/invariant fields are bounded by
   `H.nodes.length`; it carries `HistoryCoherent` + `Realizable` (so every consuming theorem
   consumes them), the ≺-SORTED coordinate chart `coordOf` (`Fin`-order ⟺ `CoordPrec`, range
   the `n×N` box — `m = n·N` enforced), the height map `ht`, and the NODE-TIED (ZC) data:
   per-prefix `ZCData` whose floor is the HISTORY's staircase max `floorH` and whose rim
   threshold is the recorded `μ_i·D_{i+1}`; fresh supports are pinned strictly above the floor
   and inside the previous read's factor interior. Freshness-on-`Σ` is now a THEOREM
   (`C2.freshFree`) consuming these links, not an assumed field.
5. **The final statements are Theorem C**: C(b) counts `S(H,Z)` — the `Ψ_H`-image of
   `Σ_k ∩ locus(Z)` under the RECORDED move composite `JetSetup.Psi` — against
   `p^{nN}·∏vol(E_fresh)·vol(Z)` in division-free pin arithmetic; C(a) is the bijective
   carriage with equal mass; `AdmissibleZ` is checked against the FINAL state `Sigma len`.

## The honest boundary (deferred, never approximated)

The EXISTENCE of a `JetSetup` for a real classifier history — the global jet-coordinate
presentation (Fact A down the tower, D.3(e)(ii)), the K1-height reading of `ht`, the graded
piece maps behind each fresh `LevelClause`, and (ZC) persistence — is the unbuilt graded ring
(§B2-DEF gap R4.5 items 1&3). It enters ONLY as the `JetSetup`/`TypObject` hypotheses, exactly
as `L6.measureExact` takes `codeN`/`ΘN`/`hcylN`. Everything in the manifest is provable from
the interface. Flagged for semantic-guardian review throughout.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesC

open Polynomial LeanUrat.Moves

/-! ## C0. Base coordinates, the global order ≺, loci, unitriangular moves -/

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
no vacuous clause instance exists. -/
structure LevelClause (p m : ℕ) where
  /-- the constrained coordinate set: a strip region or a weight-γ′ level set. -/
  support : Finset (Fin m)
  /-- the D.11-nominal codimension this clause cuts (`log_p` of the digit alphabet). -/
  codim : ℕ
  /-- the constraint itself (e.g. `R_δ'(level set) = v`); never a coordinate assignment. -/
  sat : (Fin m → ZMod p) → Prop
  /-- `sat` reads only the support coordinates. -/
  dep : ∀ x y : Fin m → ZMod p, (∀ c ∈ support, x c = y c) → (sat x ↔ sat y)
  /-- EXACT CONDITIONAL VOLUME (TYP(b)'s kernel-coset count, division-free):
  `#{y supported in support | sat y} · p^codim = p^{|support|}`. -/
  count : Nat.card {y : Fin m → ZMod p // sat y ∧ ∀ c ∉ support, y c = 0} * p ^ codim
    = p ^ support.card

/-- **The fresh data of one read** (§C.1(ii)'s species inventory, address-free): the finite
clause list (α-strips/value digits, β-strips, γ-strips left of `j×`, the non-adjacent endpoint —
after BLOCK-CONVENTION expansion), with pairwise-DISJOINT supports (one clause per slot/level
region; §C.1.5′ "pairwise disjoint: the factors multiply"). Freeness on the state cylinder is
NOT a field: it is the theorem `C2.freshFree`, derived from the (ZC) floor exactness and the
above-floor/interior placement links of `JetSetup`. -/
structure FreshData (p m : ℕ) where
  clauses : List (LevelClause p m)
  disj : clauses.Pairwise (fun c₁ c₂ => Disjoint c₁.support c₂.support)

/-- The D.11-nominal fresh base-digit count `m*(ν) = Σ codim`; `vol_nom(E_fresh) = p^{−m*}`. -/
def FreshData.mstar {p m : ℕ} (fd : FreshData p m) : ℕ :=
  (fd.clauses.map LevelClause.codim).sum

/-- The joint membership predicate of the fresh clauses. -/
def FreshData.sat {p m : ℕ} (fd : FreshData p m) (x : Fin m → ZMod p) : Prop :=
  ∀ cl ∈ fd.clauses, cl.sat x

/-- **TYP object** (§C Lemma TYP, the typed degree-γ′ initial form) — BOUNDARY-DEFERRED (needs
the graded piece `gr^Ĉ_{δ'}` and its piece map `R_δ`, the unbuilt graded ring). The fresh value
digit of a slot coefficient is an ADDITIVE map of exactly the weight-γ′ level set `S`, SURJECTIVE
onto the digit alphabet (image = the additive span of the slot images, D.3(e)(i)). Its provable
consequences: equal kernel-coset fibers (`C1.TYP_fiberCount`), hence a `LevelClause` of the
alphabet's codimension (`C1.TYP_toClause`). -/
structure TypObject (p m : ℕ) (S : Finset (Fin m)) (α : Type*) [AddCommGroup α] where
  /-- the piece map `R_δ'` composed with the level-set assignment (graded content; DEFERRED). -/
  φ : (Fin m → ZMod p) →+ α
  /-- `φ` reads only the level-set coordinates `S` (LST/TYP support typing). -/
  dep : ∀ x y : Fin m → ZMod p, (∀ c ∈ S, x c = y c) → φ x = φ y
  /-- surjective onto the alphabet (D.3(e)(i): the emitted value lies in the image). -/
  surj : Function.Surjective φ

/-! ## C3. Read species and nodes (§C.0), with the §C meanings as Prop fields -/

/-- The **species of a read** (§C.0): the ROOT read `ν₀`, an INCREMENT (`e·g > 1`, genuine
stage growth), or a RECENTERING (`e_read = 1`, `g = 1`, degree unchanged, recorded lift). -/
inductive ReadSpecies where
  | root
  | increment
  | recentering
deriving DecidableEq

/-- **A node** `ν` — one read of the OM classifier (§C.0). Frame `σ : Stage p F` (the stage it
reads in), read side `(e, h)` on slots `[s0, s0+wSide]`, descend data `(ψ, g, μ)`, anchor `a`,
the fixed side-pattern digits `pat` (D.3(c): `pat k` at stride position `k` past the anchor —
consecutive `z`-powers, since consecutive lattice slots differ by `e·s + h·t = 1`), the anchored
residual `Ranch`, the read-side `line` (absolute v_p-scale), the residue root `zbar` selected by
the read (D.6/D.7 witness), the recentering `center`/`lift` (D.10), and the frame block width
`Dwidth = deg Φ`. The `Prop` fields make every recorded datum carry its §C meaning (round-1
audit: "many appropriately named fields … not enforced"). -/
structure Node (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  species : ReadSpecies
  σ : Stage p F
  e : ℕ
  h : ℕ
  /-- ROUND 3 (audit R2 F10): the READ side's own Bézout pair `e·s + h·t = 1` — D.3's header
  data "read index (e, h) and Bézout (s, t)". D.5's realizer positions and D.8's normalization
  `m̂ = −t·h·g` consume THIS `t` (the frame's `σ.t` is the frame-CREATING read's — wrong index).
  `HistoryCoherent` ties the child frame's recorded pair to it (`σ'.s = s`, `σ'.t = t`). -/
  s : ℤ
  t : ℤ
  g : ℕ
  μ : ℕ
  a : ℤ
  s0 : ℕ
  wSide : ℕ
  Dwidth : ℕ
  line : Line
  /-- ROUND 4 (audit R3 finding 11): the **SIDE HEIGHT** `u*` — the read side's right-endpoint
  height, ABSOLUTE v_p-scale (rev 14 C.0: "on-lattice; at an ADJACENT read, u* = the standing
  window-vertex height"). Its three rev-14 roles: (i) it pins the read line's INTERCEPT
  (`hLineU`: the line of slope `−h/e` per slot passes through `(j*, u*)`); (ii) it is
  on-lattice — the augmented-scale weight `γ = e·(STR·u*) + j*·h` is the INTEGER `gam`
  (`HistoryCoherent`'s γ-tie, where the stretch `STR` lives); (iii) at an adjacent read it is
  vertex-anchored ((SAE)'s equality line + `hLineU`). -/
  ustar : ℚ
  /-- ROUND 4 (findings 11/14): the read's **TOTAL SIDE WEIGHT** `γ := e·u* + j*·h` in the
  augmented (stage) scale — rev 14 C.0's `γ_i`, the argument of D.3(c)'s stride positions
  `p_j(γ) = (j − t·γ)/e`. Recorded as an INTEGER: its ℤ-typing is the on-lattice condition;
  `HistoryCoherent` ties it to `(ustar, e, h, s0, wSide)` at the history's stretch. -/
  gam : ℤ
  zbar : Fˣ
  center : ↥σ.K
  lift : Polynomial ℤ_[p]
  ψ : Polynomial ↥σ.K
  pat : ℕ → ↥σ.K
  Ranch : Polynomial ↥σ.K
  /-- the read side is a genuine polygon side: `e, h ≥ 1`, coprime (lowest terms). -/
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  /-- the recorded pair is a genuine Bézout pair for the read side (ROUND 3, F10). -/
  hbez : (e : ℤ) * s + (h : ℤ) * t = 1
  /-- ROUND 4 (audit R3 finding 12): the pair is CANONICAL — `t` in the window `[0, e)` is the
  UNIQUE Bézout coefficient there (any two solutions differ by `(h·k, −e·k)`), so `(s, t)` is
  rev 14's `(sᴮ, tᴮ)`: "a function of `(e, h)` only", not a recorded choice. Extends the
  accepted `Stage.he1t` (D.5 P2) pinning to every `e`: at `e = 1` the window forces `t = 0`,
  whence `s = 1` by `hbez` — so at a recentering `m̂ = −t·h·g = 0` BY the convention (rev 14:
  "NOT because the lift `t_i` is zero"); the round-3 `hspecRecBez` field is deleted as
  derivable. -/
  hbezCanon : 0 ≤ t ∧ t < (e : ℤ)
  /-- the descend data are genuine: `g ≥ 1`, `μ ≥ 1` (the read DESCENDS into `ψ`). -/
  hg : 1 ≤ g
  hμ : 1 ≤ μ
  /-- the side width is a whole number of lattice cells: `e ∣ wSide` (`deg R_S = wSide/e`). -/
  hEdvd : e ∣ wSide
  /-- FRAME LINK: `Dwidth` IS the frame's block width `deg Φ` (C.1.0(a)). -/
  hDwidth : Dwidth = σ.Φ.natDegree
  /-- `ψ` is monic of degree `g` (D.3(c)). -/
  hψmonic : ψ.Monic
  hψdeg : ψ.natDegree = g
  /-- ROUND 4 (audit R3 finding 13): `ψ` is IRREDUCIBLE over the stage's residue field (rev 14
  C.0: "ψ_i: … monic irreducible over F_i"; D.3's header). Reducible residual factors are no
  longer legal nodes; `F_{i+1} = F_i[z]/(ψ_i)` is a field. (Recenterings are consistent:
  `ψ = z − c̃` has degree 1.) -/
  hψirr : Irreducible ψ
  /-- ANCHORED RESIDUAL (§C.0, rev 8): `Ranch = Σ_k pat(k)·z^k`, `k ≤ wSide/e` — the pattern
  DETERMINES `Ranch` (pattern-only data; the anchor `a` locates it: absolute position `a + k`). -/
  hRanch : Ranch = ∑ k ∈ Finset.range (wSide / e + 1), Polynomial.C (pat k) * Polynomial.X ^ k
  /-- polygon conventions: the endpoint digits are nonzero (anchor exact, side width exact). -/
  hpat0 : pat 0 ≠ 0
  hpatTop : pat (wSide / e) ≠ 0
  /-- ROUND 4 (audit R3 finding 14) — **ANCHORED-RESIDUAL PROVENANCE**: the anchor is D.3(c)'s
  stride position of the side's LEFT endpoint, `a = p_{s₀}(γ) = (s₀ − t·γ)/e` — displayed
  division-free. Why this is `ord_z R` (D.8's anchoring, as recorded stratum data): the side's
  minimizing slots are `s₀, s₀+e, …, s₀+wSide` at the constant total weight `γ`, their
  positions `p_j(γ)` increase by 1 per `e`-step (D.3(c)), and the lead digit is nonzero
  (`hpat0`) — so the smallest occupied position is `p_{s₀}(γ)`. With `hRanch`'s consecutive
  powers, `Ranch` is exactly rev 14's `R_anch = Σ_j d_j·z^{p_j(γ)−a}`; `a` can no longer be
  shifted independently of the side data (the (HV) exponent `z̄^{a−μm̂}` is now pinned). -/
  hAnchor : (e : ℤ) * a = (s0 : ℤ) - t * gam
  /-- ROUND 4 (finding 11, role (i)): the read line PASSES THROUGH `(j*, u*)` — evaluated at
  the right endpoint's base index `j*·Dwidth`. Slope is fixed by `HistoryCoherent`'s
  absolute-scale slope law, so `u*` pins the intercept: intercept translations (audit R2
  B59's residue) are dead. -/
  hLineU : line.at ((s0 + wSide) * Dwidth) = ustar
  /-- `ord_ψ(Ranch) = μ` EXACTLY (D.3(c): `ψ^μ ∥ Ranch`). -/
  hOrd : OrdPsiPoly ψ Ranch μ
  /-- `zbar` is a genuine root of `ψ` in the ambient field (D.6: `F' = K(z̄)`, `ψ(z̄) = 0`). -/
  hzbarRoot : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0
  /-- SPECIES (§C.0): an increment grows the stage, `e·g > 1`. -/
  hspecInc : species = ReadSpecies.increment → 1 < e * g
  /-- SPECIES (§C.0/D.10): a recentering has `e_read = 1` and degree unchanged (`g = 1`). -/
  hspecRec : species = ReadSpecies.recentering → e = 1 ∧ g = 1
  /-- SPECIES (D.10): a recentering consumes the linear factor `ψ = z − c̃` at its recorded
  center, and its residue "root" is the center itself (no field growth). -/
  hspecRecCenter : species = ReadSpecies.recentering →
    ψ = Polynomial.X - Polynomial.C center ∧ ((zbar : Fˣ) : F) = ((center : ↥σ.K) : F)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The CHILD frame's block width `D_{i+1} = e·g·D_i` (C.1.0(a); recenterings: `e = g = 1`,
unchanged). `HistoryCoherent` pins the successor node's `Dwidth` to this. -/
def Node.childWidth (ν : Node p F) : ℕ := ν.e * ν.g * ν.Dwidth

/-- The D.8 normalization exponent `m̂ = −t·h·g` of the READ (the vertex unit `z̄^{−μm̂}` of
D.8's (VERTEX)). ROUND 3 (audit R2 F10 — a REAL index bug in round 2): `(t, h)` are the read
side's OWN slope numerator and recorded Bézout coefficient (D.3's header pair), NOT the
frame's `(σ.t, σ.h)` (which record the frame-CREATING read, one step earlier). ROUND 4: the
pair is CANONICAL (`hbezCanon`); at `e = 1` — every recentering — the window forces `t = 0`,
so `m̂ = 0` BY the convention (D.10's normalization, rev 14's exact sentence). -/
def Node.mhat (ν : Node p F) : ℤ := -ν.t * (ν.h : ℤ) * (ν.g : ℤ)

/-- The polynomial factor `(Ranch/ψ^μ) mod ψ` of the transported vertex value — pattern-only
data (§C.0 rev 8: the descend stratum fixes the side-digit tuple, which determines `Ranch`;
D.8's split is a factorization OF this fixed polynomial). Nonzero by `hOrd`
(`C3.vtxPolyNe`). -/
noncomputable def Node.vtxPoly (ν : Node p F) : Polynomial ↥ν.σ.K :=
  (ν.Ranch /ₘ ν.ψ ^ ν.μ) %ₘ ν.ψ

/-- **The transported vertex value** `vtx(ν) := z̄^{a−μ·m̂}·((Ranch/ψ^μ) mod ψ)(z̄) ∈ F`
(§C.0, rev 8) — ALL scalar factors included, valued in the ambient field (which contains
`F_{i+1} = K(z̄)`). An explicit function of node data alone, so (HV) below is a predicate on
the history. [Round-1 audit: `vtxPoly` "omits the scalar factors … valued in the parent
field" — repaired.] -/
noncomputable def Node.vtx (ν : Node p F) : F :=
  (((ν.zbar ^ (ν.a - (ν.μ : ℤ) * ν.mhat)) : Fˣ) : F) *
    Polynomial.eval₂ ν.σ.K.subtype ((ν.zbar : Fˣ) : F) ν.vtxPoly

/-- The node's **line staircase** (§C (ZC-a)/DOM floor form): on its factor interior
`[0, μ·D_{i+1})`, the line's value at the LEFT EDGE of the base index's frame-`(i+1)` block;
`⊥` outside (its clause region contributes no floor beyond the interior). -/
noncomputable def Node.staircase (ν : Node p F) (b : ℕ) : WithBot ℚ :=
  if b < ν.μ * ν.childWidth
    then ((ν.line.at ((b / ν.childWidth) * ν.childWidth) : ℚ) : WithBot ℚ)
    else ⊥

/-- The read line as a COARSE step function of the base index over the WHOLE window
(`childWidth` block-left-edge value; NO factor-interior cutoff — cf. `staircase`, its
factor-interior truncation). ROUND 6 (audit R5 finding 7): NO LONGER the fresh-band upper edge
— `childWidth = e·g·Dwidth` groups `e·g` fine slots under ONE left-edge value, so at `e·g > 1`
this exceeds the later fine slots' true valuations (the line descends); the band boundary is
now the fine-slot law `Node.slotVal ∘ Node.fineSlot` (`inFreshBand`). Retained SOLELY as the
post-landing (ZC-a) staircase convention; the two boundaries coincide at recenterings
(`childWidth = Dwidth`). -/
def Node.lineStep (ν : Node p F) (b : ℕ) : ℚ := ν.line.at ((b / ν.childWidth) * ν.childWidth)

/-- ROUND 5 (audit R4 blocking list): the **FINE SLOT** of base index `b` — the read's OWN
frame-`i` development slot, blocks of width `Dwidth = deg Φ_i` (C.1.0(a): slot `j`'s
coefficient `B_j` occupies base indices `[j·Dwidth, (j+1)·Dwidth)`). The read's per-slot
clauses ((α)/(β)/(γ), the value digits) live at THIS granularity; `lineStep`'s coarser
`childWidth` blocks are the post-landing (ZC-a) staircase convention. -/
def Node.fineSlot (ν : Node p F) (b : ℕ) : ℕ := b / ν.Dwidth

/-- ROUND 5: `j` is a **SPAN SLOT** of the read — `j ∈ [s₀, s₀+wSide]`, the side's own slots
(C.1.0(b)(i)(α)). Exact-valuation VALUE digits live only at span slots (the (α) on-lattice
digits and the non-adjacent endpoint); β (`j < s₀`) and γ (`j > s₀+wSide`) slots assert
STRICT bounds — pure strip content, zeros through the line level included. -/
def Node.spanSlot (ν : Node p F) (j : ℕ) : Prop := ν.s0 ≤ j ∧ j ≤ ν.s0 + ν.wSide

/-- ROUND 5: the read line's **EXACT VALUATION at fine slot `j`** — `new(j) = line.at(j·Dwidth)`,
the height of slot `j`'s value digit (C.1.5′(1): "fresh VALUE clauses pin the first residual
digit of a slot coefficient B at its exact valuation γ′ = new(slot)"). -/
def Node.slotVal (ν : Node p F) (j : ℕ) : ℚ := ν.line.at (j * ν.Dwidth)

/-- **The node's standard lift** — D.5 displayed AT THE NODE's READ INDEX (ROUND 3, audit R2
F10): `Φ̂ = Φ^{e·g} + Σ_{ψ_k ≠ 0} t_k·Φ^{e·k}` over the frame's key/valuation/residual map,
with stride `ν.e`, realizer weights `σ.w(t_k) = h·(g−k)` (the READ's `h`, on the frame's
CURRENT valuation — the scale the coming augmentation stretches), digit scalars the literal
`ψ`-coefficients at the frame's forced (S5) positions `−σ.t·wPrev(t_k)`. Round 2 invoked
`IsStandardLift ν.σ`, whose stride/weights are the frame's stage pair `(σ.e, σ.h)` — the
frame-CREATING read's index, wrong for the node's own read. Replaces it in `HistoryCoherent`
and supplies the FINAL read's landing key (`LandingKey`, blocker 56). -/
def IsNodeLift (ν : Node p F) (Φhat : Polynomial ℤ_[p]) : Prop :=
  ∃ tt : ℕ → Polynomial ℤ_[p],
    (∀ k, ν.ψ.coeff k = 0 → tt k = 0) ∧
    (∀ k, k < ν.g → ν.ψ.coeff k ≠ 0 →
        tt k ≠ 0 ∧ inC ν.σ.Φ (tt k) ∧
          ν.σ.w (tt k) = (ν.h : ℤ) * ((ν.g : ℤ) - (k : ℤ)) ∧
          ν.σ.R (tt k) = LaurentPolynomial.C (ν.ψ.coeff k) *
            LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (tt k))) ∧
    Φhat = ν.σ.Φ ^ (ν.e * ν.g) + ∑ k ∈ Finset.range ν.g, tt k * ν.σ.Φ ^ (ν.e * k)

/-- **The landing-key law of one read** (D.5 increment/root; D.10 recentering — ROUND 3,
blocker 56): the key the read's landing produces, tied to the RECORDED node data. At a
recentering: `Φ' = Φ − lift` with the recorded lift a genuine center realizer (`w(lift) =
w(Φ)`, digit = the recorded center at position 0 — `IsRecentering`'s lift clauses, stated on
the node alone). Otherwise: the standard lift of the recorded `(ψ, g)` at the read's index.
`JetSetup.landing` imposes this at EVERY read `i < len` on the recorded key `keys i` —
including the FINAL read, whose landing transition round 2 left unrepresented. -/
def LandingKey (ν : Node p F) (Φtop : Polynomial ℤ_[p]) : Prop :=
  (ν.species = ReadSpecies.recentering →
    inC ν.σ.Φ ν.lift ∧ ν.lift ≠ 0 ∧ ν.σ.w ν.lift = ν.σ.w ν.σ.Φ ∧
      ν.σ.R ν.lift = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0 ∧
      Φtop = ν.σ.Φ - ν.lift) ∧
  (ν.species ≠ ReadSpecies.recentering → IsNodeLift ν Φtop)

end

/-! ## C4. Histories: coherence (tower provenance) and realizability ((NA)/(HV)) -/

/-- **A read history** `H = (ν₀, …, ν_k)` (§C.0): nonempty, the root read FIRST and ONLY first
(round-1 audit: "a later node may have species root" — excluded by `root_iff`). -/
structure History (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  nodes : List (Node p F)
  nonempty : nodes ≠ []
  root_iff : ∀ (j : ℕ) (hj : j < nodes.length),
    (nodes[j]'hj).species = ReadSpecies.root ↔ j = 0

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The accumulated stretch `STR_i = ∏_{m<i} e_m` of frame `i`'s valuation over `v_p`
(C.1.0(c)/the scale declaration: each transition stretches coefficient weights by its read's
`e`). -/
def History.strFrame (H : History p F) (i : ℕ) : ℕ := ((H.nodes.take i).map Node.e).prod

/-- **The cumulative floor** `F_{i−1}` carried by the prefix of length `i` (§C.1.5 (ZC-a)): the
pointwise max of the first `i` nodes' line staircases over their factor interiors, as a step
function of the base index. `floorH 0 = ⊥` (the root reads against an empty floor:
`E_fresh(ν₀) = E(ν₀)`). -/
noncomputable def History.floorH (H : History p F) (i b : ℕ) : WithBot ℚ :=
  ((H.nodes.take i).map (fun ν => ν.staircase b)).foldr max ⊥

/-- Level-`r` weight `κ_r = h_r/(e_r·STR_r)` (the C.1.5 scale declaration / LST(i)): FIXED by
node `r`'s READ data at the read that created the level; recenterings create no level (their
`innerslotH` below is 0, since `childWidth = Dwidth`). Junk `0` beyond the history. -/
noncomputable def History.kappaH (H : History p F) (r : ℕ) : ℚ :=
  (H.nodes[r]?).elim 0 (fun ν => (ν.h : ℚ) / ((ν.e : ℚ) * (H.strFrame r : ℚ)))

/-- The level-`r` inner slot of base index `b`: `(b mod D_{r+1}) / D_r` on the recorded width
chain (C.1.0(a) BLOCKS). At a recentering `D_{r+1} = D_r`, so the slot is 0 — no level. -/
def History.innerslotH (H : History p F) (r b : ℕ) : ℕ :=
  (H.nodes[r]?).elim 0 (fun ν => (b % ν.childWidth) / ν.Dwidth)

/-- **The K1-chain height, DEFINED from node data** (LST(i)/KEY OBS 1 — ROUND 3, audit R2
F47 + blocker 59; the round-2 bare `JetSetup.ht` field is DELETED): the frame-`i` absolute
v_p-height of base coordinate `c = (ℓ, b)` is `ℓ + Σ_{r<i} innerslot_r(b)·κ_r` — the current
key never enters (levels `r < i` only), κ's are birth-fixed, recentering levels contribute 0.
FLAG (the deferred graded bridge, its content unchanged but now attached to a SENTENCE):
that this formula is the K1-chain weight of the basis monomial `p^ℓ·Π_r Φ̂_r^{innerslot_r}`
(LST(i)) and that `log_p|𝔸(γ)| = |{c : htH = γ}|` per block (D.3(e)(ii)'s attainable
accounting, consumed by `mstar_eq`) are graded-ring content. -/
noncomputable def History.htH (H : History p F) (i : ℕ) (c : Coord) : ℚ :=
  (c.1 : ℚ) + (Finset.range i).sum (fun r => (H.innerslotH r c.2 : ℚ) * H.kappaH r)

/-- Read `i`'s constraint-region bound (C.1(ii)'s rim rule): fresh content of read `i` sits at
base indices `< μ_{i−1}·D_i` (the PREVIOUS read's rim threshold); the root read constrains the
whole `n`-index box. -/
def History.prevRim (H : History p F) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => (H.nodes[i]?).elim n (fun ν => ν.μ * ν.childWidth)

/-- **History coherence** (§C.0 + C.1.0): the recorded frames are linked by the ACCEPTED
§B2-DEF transitions AT THE RECORDED NODE DATA — no free existentials (round-1 audit repairs:
the increment transition consumes the PARENT node's recorded `ψ, g, e, h, zbar` through
`IsNodeLift` + `TransitionCoreL`; the recentering consumes the RECORDED `center`/`lift`
through `IsRecenteringCore`; the root frame is the base frame `deg Φ₀ = 1`; windows are
contained (`s₀'+w' ≤ μ`); the width chain `D_{i+1} = e_i·g_i·D_i` holds; lines steepen along
the history ((I-aug), absolute scale) and obey the absolute-scale slope law
`slope_i·(e_i·STR_i·D_i) = h_i`).
ROUND 3 additions: `IsNodeLift` replaces the round-2 `IsStandardLift ν.σ` call (F10: the lift
must use the READ's index, not the frame-creating read's); the child frame's Bézout pair is
tied to the node's recorded read pair (`σ'.s = s`, `σ'.t = t` — so `Node.mhat`/`vtx` carry the
tower's D.8 unit).
ROUND 4 (audit R3 findings 11/16): the round-3 vertex-entry/hinge clauses — a WEAKENED,
non-strict shadow of (SAE) — are DELETED: the span-entry inequality belongs to the
REALIZABILITY class (`TransitionAdmissible`/`Realizable`), rev 14's hypothesis boundary, and
never to coherence. In their place, the per-node **γ-TIE** (the on-lattice condition, role
(ii) of `Node.ustar`): the recorded integer `gam` equals the augmented-scale total side
weight `e_i·(STR_i·u*_i) + j*_i·h_i` (stage scale = `STR_i ×` absolute, C.1.0(c); `γ ∈ ℤ`
IS on-lattice, and `hAnchor` reads the stride-position anchor off it). -/
def HistoryCoherent (H : History p F) : Prop :=
  (∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (H.nodes[i]'hi).line.slope *
        (((H.nodes[i]'hi).e : ℚ) * (H.strFrame i : ℚ) * ((H.nodes[i]'hi).Dwidth : ℚ))
      = ((H.nodes[i]'hi).h : ℚ)) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (((H.nodes[i]'hi).gam : ℤ) : ℚ)
      = ((H.nodes[i]'hi).e : ℚ) * ((H.strFrame i : ℚ) * (H.nodes[i]'hi).ustar)
        + ((((H.nodes[i]'hi).s0 + (H.nodes[i]'hi).wSide) : ℕ) : ℚ) * ((H.nodes[i]'hi).h : ℚ)) ∧
  ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    ((H.nodes[i]'(by omega)).species = ReadSpecies.recentering →
      IsRecenteringCore (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
        (H.nodes[i]'(by omega)).center (H.nodes[i]'(by omega)).lift) ∧
    ((H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering →
      IsNodeLift (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi).σ.Φ ∧
        TransitionCoreL (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
          (H.nodes[i+1]'hi).σ.Φ (H.nodes[i]'(by omega)).e (H.nodes[i]'(by omega)).h
          (H.nodes[i]'(by omega)).zbar) ∧
    ((H.nodes[i+1]'hi).σ.s = (H.nodes[i]'(by omega)).s) ∧
    ((H.nodes[i+1]'hi).σ.t = (H.nodes[i]'(by omega)).t) ∧
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide ≤ (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).Dwidth = (H.nodes[i]'(by omega)).childWidth) ∧
    ((H.nodes[i]'(by omega)).line.slope < (H.nodes[i+1]'hi).line.slope)

/-- **TRANSITION-ADMISSIBLE** (§C.0, rev 13 — ROUND 4, audit R3 finding 10): the read `ν`
appended after the standing node `νp` satisfies the THREE data conditions (NA)+(HV)+(SAE) at
the appended read — all equations/inequalities of NO `E`, on node data alone. Lines are
compared at BASE indices: standing-window slot `j` ↔ `j·νp.childWidth` (= `j·ν.Dwidth` under
coherence). This is THE per-step interface rev 14's C.1/C.1.0(b)(iii)/C.1.5 hypothesize of
their appended reads (consumed here through `Realizable`/`JetSetup.realizable`, and directly
by `C3.lineDom`); without it their conclusions are FALSE on the certified F-EMPTY data.
* **(NA)** at a NON-ADJACENT read (`s₀'+w' < μ`): the pinned old vertex lies STRICTLY ABOVE
  the extended new line at the vertex's base index `μ·D_{i+1}`;
* **(HV)** at an ADJACENT read (`s₀'+w' = μ`): the pattern LEAD of `ν` (its endpoint digit
  `pat(wSide/e)`, the vertex digit) EQUALS the transported vertex value `vtx(νp)` in `F`;
* **(SAE)** SPAN-ENTRY INEQUALITY (rev 12 — the third condition; ROUND 4, audit R3 findings
  8/9: absent in round 3, whose coherence tie allowed equality — the F-EMPTY configuration):
  the read side lies STRICTLY ABOVE the old box line at every span slot below the window
  vertex, and MATCHES it at the vertex when the span reaches it:
    `new(j) > old(j)` for every span slot `j ∈ [s₀', j*]` with `j < μ`;
    `new(μ) = old(μ)` when `j* = μ` (adjacent — the vertex-anchored side height:
    with `hLineU`, `u* =` the standing window-vertex height). -/
def TransitionAdmissible (νp ν : Node p F) : Prop :=
  (ν.s0 + ν.wSide < νp.μ →
    ν.line.at (νp.μ * νp.childWidth) < νp.line.at (νp.μ * νp.childWidth)) ∧
  (ν.s0 + ν.wSide = νp.μ →
    ((ν.pat (ν.wSide / ν.e) : ↥ν.σ.K) : F) = νp.vtx) ∧
  (∀ j : ℕ, ν.s0 ≤ j → j ≤ ν.s0 + ν.wSide → j < νp.μ →
    νp.line.at (j * νp.childWidth) < ν.line.at (j * νp.childWidth)) ∧
  (ν.s0 + ν.wSide = νp.μ →
    ν.line.at (νp.μ * νp.childWidth) = νp.line.at (νp.μ * νp.childWidth))

/-- **Realizability** (§C.0, rev 12/14 — ROUND 4, audit R3 finding 9: the FULL three-condition
class): a lift-carrying history is REALIZABLE iff EVERY appended read is transition-admissible
— (NA)+(HV)+(SAE) at every read `ν_{i+1}`, `i ≥ 0`. A history failing any of the three has
EMPTY joint stratum (the classifier never emits it), and Theorem C's quantifier ranges over
realizable histories only. The round-3 two-condition version admitted (SAE)-violating
histories (the F-EMPTY instance: nominal fresh volume `2⁻⁶`, actual census count 0). -/
def Realizable (H : History p F) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    TransitionAdmissible (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi)

end

/-! ## C5. The (ZC) invariant and the presented history (jet setup) -/

/-- **The (ZC) invariant on a state cylinder** (§C.1.5), against a coordinate chart `coordOf`,
a height map `ht`, the cumulative floor `floor` (a step function of the base index), and the
rim threshold `rimIdx = μ_i·D_{i+1}` (a BASE-INDEX region — round-1 audit: a rim condition "is
not a suffix of the global order"; the `rimStart : Fin m` encoding and its `rimStart := 0`
vacuity are gone, and `m = 0` is unproblematic):
* **(ZC-a) EXACT DOWNSET** — at interior base indices (`< rimIdx`), a coordinate is pinned IFF
  its height is at most the floor (BOTH directions: the round-1 `pin_dichotomy` allowed
  under-pinning);
* **(ZC-a) LITERAL ZEROS** — interior pins solve to the constant `0` (the zero downset
  `Z(F_i)`);
* **(ZC-b) LEADS AT RIM** — every other pin is at a rim base index; its `solve` is
  unrestricted (`DIG_i`: unitriangular, non-lead arguments free). [The finer §C statement that
  each `DIG_i` equation solves for one rim-block LEVEL SET is presentation content of the
  deferred jet bridge; the counting consumes rim-ness of the leads only — C15 S4c.] -/
structure ZCData {p m : ℕ} (D : Locus p m) (coordOf : Fin m → Coord) (ht : HtMap)
    (floor : ℕ → WithBot ℚ) (rimIdx : ℕ) : Prop where
  downset_exact : ∀ j : Fin m, (coordOf j).2 < rimIdx →
    (D.pinned j = true ↔ ((ht (coordOf j) : ℚ) : WithBot ℚ) ≤ floor (coordOf j).2)
  interior_zero : ∀ j : Fin m, (coordOf j).2 < rimIdx → D.pinned j = true →
    ∀ f : (j' : Fin m) → j' < j → ZMod p, D.solve j f = 0

/-- The `ℓ`-th base-`p` digit of a p-adic integer, valued in `ZMod p` — concretely
`(a mod p^{ℓ+1}) / p^ℓ`. The FRAME-0 jet chart (`JetSetup.pres_zero`) reads a polynomial's
base coordinate `(ℓ, i)` as `baseDigit p ℓ (f.coeff i)`: the presentation spine bottoms out
at literal p-adic digits of literal coefficients (ROUND 3, blocker 55). -/
noncomputable def baseDigit (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (a : ℤ_[p]) : ZMod p :=
  (((PadicInt.toZModPow (ℓ + 1) a).val / p ^ ℓ : ℕ) : ZMod p)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The FRESH BAND of read `i`** (ROUND 4, audit R3 finding 17 — §C.1(ii)'s D.11 species
inventory, named as a COORDINATE predicate; ROUND 6, audit R5 finding 7 / blocking list — the
upper edge moved from the coarse `childWidth` staircase to the FINE-slot boundary): coordinate
`c` is in read `i`'s band iff it lies in the read's constraint region (base index `< prevRim`
— C.1(ii)'s rim rule), STRICTLY ABOVE the cumulative floor (LST(iii) selection), and
AT-OR-BELOW its own fine slot's EXACT VALUATION `new(j) = slotVal (fineSlot idx)` — the
recorded fine-slot valuation law, rev 14 C.1(ii)'s per-slot inventory granularity (C.1.0(a):
frame-`i` blocks of width `Dwidth`). The round-4/5 bound `Node.lineStep` (coarse `childWidth`
left edges — the post-landing (ZC-a) staircase) exceeds `slotVal (fineSlot b)` at the later
fine slots of each coarse block whenever `e·g > 1` (the line descends), so it admitted
coordinates rev 14 leaves UNCONSTRAINED and — via `fresh_cover` + `fresh_assembled`'s strip
tag — forced spurious zeros there. The band at fine slot `j` is now exactly `(floor, new(j)]`:
strip zeros strictly between floor and `new(j)`, plus the on-lattice level set AT `new(j)` at
span slots (`IsValueCoord`, the value positions — the band's upper edge). Past the (γ)
crossing slot `new(j) ≤ floor`: the band self-truncates per FINE slot — C.1(i)(γ)'s cut,
exact. `ν` is instantiated at `H.nodes[i]`; heights are the DEFINED `History.htH`. Consumed BY
NAME (byte-stable) by `JetSetup.fresh_band`/`fresh_cover`/`mstar_eq`: together they say each
band coordinate belongs to EXACTLY its strip/level-set clause and nothing else. -/
def inFreshBand (H : History p F) (n : ℕ) {m : ℕ} (coordOf : Fin m → Coord)
    (i : ℕ) (ν : Node p F) (c : Fin m) : Prop :=
  (coordOf c).2 < H.prevRim n i ∧
  H.floorH i (coordOf c).2 < ((H.htH i (coordOf c) : ℚ) : WithBot ℚ) ∧
  H.htH i (coordOf c) ≤ ν.slotVal (ν.fineSlot (coordOf c).2)

/-- **The VALUE POSITIONS of read `i`** (ROUND 5, audit R4 finding 10 / blocking item 2 — the
strip/value species label, now a FUNCTION of node geometry, per coordinate): `c` is a VALUE
position iff its FINE slot (the read's own development slot, width `Dwidth` — C.1.0(a)) is a
SPAN slot AND its height is that slot's EXACT VALUATION `new(j)`. This is rev 14 C.1(ii)'s
on-lattice value-digit locus: the (α) span digits and the non-adjacent endpoint's value digit
(the adjacent hinge block sits at/beyond `prevRim`, outside the band — the (HV) no-pin
clause). Everything else in the band is STRIP content: (α)-strips strictly between floor and
exact valuation, (β)/(γ)-strips through the line at off-span slots (their clauses are strict
bounds, so the line-level coordinate is a ZERO there, not a value), cluster zeros at the
root. Off-lattice span heights select the empty level set — no coordinate sits there. -/
def IsValueCoord (H : History p F) {m : ℕ} (coordOf : Fin m → Coord)
    (i : ℕ) (ν : Node p F) (c : Fin m) : Prop :=
  ν.spanSlot (ν.fineSlot (coordOf c).2) ∧
    H.htH i (coordOf c) = ν.slotVal (ν.fineSlot (coordOf c).2)

/-- **The VALUE-SUPPORT law** (ROUND 5, audit R4 blocking item 3): a value clause's support is
the COMPLETE height-level set of ONE recorded span slot at its recorded exact valuation —
membership as an IFF over the whole box, never a `⊆`:
`c ∈ S ⟺ (c lies in fine block j) ∧ (ht(c) = new(j))`, `j` a span slot. Cross-block subsets,
partial level sets, level sets of off-span slots, and arbitrary constant-height supports (the
round-4 permutations, audit finding 10) are all illegal. Membership in a legal value support
is exactly `IsValueCoord` at the recorded slot. -/
def IsValueSupport (H : History p F) {m : ℕ} (coordOf : Fin m → Coord)
    (i : ℕ) (ν : Node p F) (S : Finset (Fin m)) : Prop :=
  ∃ j : ℕ, ν.spanSlot j ∧
    ∀ c : Fin m, c ∈ S ↔ (ν.fineSlot (coordOf c).2 = j ∧ H.htH i (coordOf c) = ν.slotVal j)

/-- **The jet presentation of a history** — the BOUNDARY-DEFERRED bridge from the accepted
tower to digit systems (§C.2's `Ψ_H`; D.3(e)(ii) down the whole tower, at a level cutoff
`N ≥ N(H, Z)` — largeness of `N` is an existence condition on the presentation). Indexing:
`Sigma 0` = the full box; read `ν_i` is consumed once between `Sigma i` and `Sigma (i+1)`;
junk beyond `H.nodes.length` is never consumed. ROUND 3 (blockers 55-60): every field now
carries a PROVENANCE law tying it to `H.nodes` — see the module header. The deferred content
(the unbuilt graded ring, R4.5 items 1&3) is the EXISTENCE of this bundle for a real
classifier history, plus the two flagged identifications on `History.htH`; the SENTENCES all
exist below. FLAGGED for semantic-guardian review throughout. -/
structure JetSetup (H : History p F) (n N m : ℕ) where
  /-- the box is the `n·N` coefficient box (BLOCK CONVENTION, base digits). -/
  hm : m = n * N
  /-- ROUND 4 (audit R3 finding 18) — the CUTOFF condition: Theorem C's quantifier is
  "for every `N ≥ N(H, Z)`", with `N(H, Z) := 1 + the largest base level among `T(H,Z)`'s
  equations `≥ 1`. The `≥ 1` floor is recorded here (killing the `N = 0`, `m = 0` degenerate
  presentations, whose `pres_zero` was vacuous); the `≥ N(H, Z)` half is automatic INSIDE the
  box (`coordOf_lt` bounds every equation's level below `N`) and is otherwise the
  existence-side largeness condition on the presentation. -/
  hN : 1 ≤ N
  /-- the ≺-SORTED coordinate chart: `Fin m`-order IS the global order `≺`. -/
  coordOf : Fin m → Coord
  coordOf_sorted : ∀ j j' : Fin m, j < j' ↔ CoordPrec (coordOf j) (coordOf j')
  /-- the chart lands in the box: levels `< N`, base indices `< n`. -/
  coordOf_lt : ∀ j : Fin m, (coordOf j).1 < N ∧ (coordOf j).2 < n
  /-- the presented history is coherent (consumed by every downstream theorem). -/
  coherent : HistoryCoherent H
  /-- and realizable — ROUND 4: the FULL (NA)+(HV)+(SAE) class, definitionally
  `∀ i, TransitionAdmissible ν_i ν_{i+1}`: every per-step consumer (the C.1/C.1.5 mirrors
  `C2.EInh_implied`/`C4.stepMass`) receives rev 13's per-step hypothesis for its read through
  this field; §C's quantifier ranges over realizable histories only. -/
  realizable : Realizable H
  /-- ROUND 4 (audit R3 finding 19) — the ROOT-SIDE HEIGHT condition (DOM's rev-11 base
  display): the root line dominates the CLUSTER FLOOR — height `≥ 1` at every base index of
  the root factor interior (D.4's ROOT case: every side slope `≥ 1`; the cluster zeros pin
  level 0, floor height 1). So `mstar_eq` at `i = 0` COUNTS the cluster zeros (level-0
  coordinates sit in the root band), and the root intercept can no longer be translated
  below the cluster floor. -/
  root_height : ∀ (hj : 0 < H.nodes.length) (b : ℕ),
    b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth → 1 ≤ (H.nodes[0]'hj).line.at b
  /-- the state cylinder before read `i`: `Sigma i = Σ_{i−1}` in frame-`i` coordinates. -/
  Sigma : ℕ → Locus p m
  /-- INITIALIZATION: `Σ_{−1}` is the full box — nothing is pinned before the root read. -/
  init : ∀ c : Fin m, (Sigma 0).pinned c = false
  /-- the fresh clause data of read `ν_i` (§C.1(ii)'s species inventory, address-free);
  PINNED to the node by `fresh_assembled`/`mstar_eq`/`fresh_band`/`fresh_cover` (ROUND 4). -/
  fresh : ℕ → FreshData p m
  /-- the move maps `Θ_i` (child-to-parent coordinate reading); PINNED to the recorded keys
  by `pres_theta`/`pres_block` (ROUND 3, blocker 55). -/
  Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  /-- (§C.0.5) each move is unitriangular for `≺` (Fact A's division accounting; DEFERRED). -/
  Theta_uni : ∀ i : ℕ, IsUnitriangular (Theta i)
  /-- the recorded LANDING KEYS: `keys i` = the key read `ν_i`'s landing produces (frame-(i+1)
  key). Interior: pinned to the child frame (`keys_mid`); ALL reads incl. the FINAL one obey
  the recorded-data landing law (`landing` — ROUND 3, blocker 56). -/
  keys : ℕ → Polynomial ℤ_[p]
  keys_mid : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ
  landing : ∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i)
  /-- **the presentation spine** (ROUND 3, blocker 55): `pres i x f` = "`x` is the frame-`i`
  digit presentation of the integral polynomial `f`". The spine is what ties the abstract
  digit-level data to actual polynomials; its EXISTENCE laws are the deferred jet bridge. -/
  pres : ℕ → (Fin m → ZMod p) → Polynomial ℤ_[p] → Prop
  /-- frame 0 is the LITERAL p-adic coefficient chart — fully concrete. -/
  pres_zero : ∀ (x : Fin m → ZMod p) (f : Polynomial ℤ_[p]),
    pres 0 x f ↔ ∀ j : Fin m, x j = baseDigit p (coordOf j).1 (f.coeff (coordOf j).2)
  /-- every monic degree-`n` integral polynomial has a frame-`i` presentation (D.3(e)(ii)
  existence; DEFERRED — the graded bridge). -/
  pres_total : ∀ i : ℕ, i ≤ H.nodes.length → ∀ f : Polynomial ℤ_[p],
    f.Monic → f.natDegree = n → ∃ x, pres i x f
  /-- **`Θ_i` IS read `ν_i`'s move** (blocker 55): it translates frame-(i+1) presentations of
  `f` to frame-`i` presentations of the SAME `f` — the Fact-A re-reading, on actual
  polynomials. -/
  pres_theta : ∀ i : ℕ, i < H.nodes.length →
    ∀ (x : Fin m → ZMod p) (f : Polynomial ℤ_[p]), pres (i+1) x f → pres i (Theta i x) f
  /-- frame-(i+1) presentations are BLOCK-LOCAL over the recorded landing key's development
  (C.1.0(a)): the digits over slot `j`'s base-index block depend on the development slot
  `B j` alone. -/
  pres_block : ∀ i : ℕ, i < H.nodes.length →
    ∀ (f f' : Polynomial ℤ_[p]) (x x' : Fin m → ZMod p), pres (i+1) x f → pres (i+1) x' f' →
    ∀ (B B' : ℕ → Polynomial ℤ_[p]) (Nd Nd' : ℕ),
      IsDevelopment (keys i) f B Nd → IsDevelopment (keys i) f' B' Nd' →
      ∀ c : Fin m,
        B ((coordOf c).2 / (keys i).natDegree) = B' ((coordOf c).2 / (keys i).natDegree) →
        x c = x' c
  /-- read `ν_i`'s STRATUM, in frame-`i` coordinates (the full clause content `E(ν_i)`,
  inherited + fresh). -/
  stratum : ℕ → (Fin m → ZMod p) → Prop
  /-- **the stratum equation** (ROUND 3, F43/blocker 55 — replaces the round-2 fresh-only
  `recursion`): `Σ_i = Θ_i(Σ_{i−1} ∩ stratum(ν_i))` — D.8/D.10 two-sidedness AT THE STRATUM,
  no implication absorbed. -/
  recursion : ∀ i : ℕ, i < H.nodes.length → ∀ x : Fin m → ZMod p,
    (Sigma (i+1)).IsSolution x ↔ ((Sigma i).IsSolution (Theta i x) ∧ stratum i (Theta i x))
  /-- **C.1(i) AS A SENTENCE** (ROUND 3): on the state cylinder, the stratum's inherited
  content is implied — the stratum reduces to exactly its fresh clauses. -/
  inh_implied : ∀ i : ℕ, i < H.nodes.length → ∀ y : Fin m → ZMod p,
    (Sigma i).IsSolution y → (stratum i y ↔ (fresh i).sat y)
  /-- the (ZC) invariant at every prefix, at the HISTORY's floor, the DEFINED K1 heights
  (`History.htH`, frame `i+1`), and the RECORDED rim threshold (§C.1.5). -/
  zc : ∀ (i : ℕ) (hi : i < H.nodes.length),
    ZCData (Sigma (i+1)) coordOf (H.htH (i+1)) (H.floorH (i+1))
      ((H.nodes[i]'hi).μ * (H.nodes[i]'hi).childWidth)
  /-- **every fresh clause support lies INSIDE the band** (ROUND 4, audit R3 finding 17 —
  replaces the round-3 `fresh_above` + `fresh_interior`, which gave only the floor and rim
  bounds and left the band's UPPER EDGE open): each supported coordinate is in read `i`'s
  region (`< prevRim`), strictly above the cumulative floor (LST(iii)), and at-or-below its
  own fine slot's exact valuation (ROUND 6: `inFreshBand`'s fine boundary). No fresh
  codimension can sit on unrelated above-floor coordinates. -/
  fresh_band : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (fresh i).clauses,
    ∀ c ∈ cl.support, inFreshBand H n coordOf i (H.nodes[i]'hi) c
  /-- **every band coordinate is covered** (ROUND 4, finding 17): each coordinate of read
  `i`'s fresh band lies in SOME fresh clause's support — and in EXACTLY ONE, by
  `FreshData.disj`. With `fresh_band` (supports ⊆ band) and `fresh_assembled`'s per-clause
  codimension, every counted band coordinate belongs to exactly its strip/level-set clause:
  the permutation loophole (equal totals on permuted supports) is unbuildable. -/
  fresh_cover : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ c : Fin m,
    inFreshBand H n coordOf i (H.nodes[i]'hi) c → ∃ cl ∈ (fresh i).clauses, c ∈ cl.support
  /-- **fresh clauses are ASSEMBLED from the two §C shapes, GEOMETRICALLY TAGGED** (ROUND 3,
  blocker 60; ROUND 4, finding 17; ROUND 5, audit R4 finding 10 / blocking list — the one
  remaining loophole). Each clause is
  * a **STRIP** — singleton support `{c}`, `codim = 1`, the literal zero `x c = 0`, at a
    coordinate that is NOT a value position (`¬ IsValueCoord` — the ROUND-5 tag): β/γ strips
    through the line, (α)-strips strictly between floor and exact valuation, cluster zeros; or
  * a **VALUE clause** — support THE COMPLETE level set of ONE recorded span slot at its exact
    valuation (`IsValueSupport`, an IFF — subsumes round 4's bare constant-height law),
    `codim = support.card` (TYP(b)'s `|alphabet| = |piece|` / D.3(e)(ii)'s attainable
    accounting, per clause), constraint a `TypObject` surjection onto `(ZMod p)^codim` at an
    emitted value `v` (whose provenance from the node's pattern digit is the declared graded
    boundary — blueprint R4.B.2, not geometry).
  THE IMPERSONATION WALK (audit R4 blocking item 4, the all-singleton-zero construction: cover
  every band coordinate by its own `x c = 0` strip): at any VALUE position `c₀` (a span slot's
  exact-valuation level set), the strip branch now FAILS — `IsValueCoord c₀` holds and the tag
  forbids it; a "value" clause with support `{c₀} ⊊ L` FAILS the `IsValueSupport` iff whenever
  the level set `L` has a second coordinate (block convention: every residue degree ≥ 2); and
  `fresh_cover` + `FreshData.disj` put `c₀` in EXACTLY one clause — which must therefore be THE
  complete-level-set value clause of its slot. Where `L` is a genuine singleton the forced
  clause IS the species-correct value clause (only `v` stays existential — R4.B.2). So clause
  species and support geometry are functions of node data; the construction is unbuildable. -/
  fresh_assembled : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (fresh i).clauses,
    (∃ c : Fin m, cl.support = {c} ∧ cl.codim = 1 ∧ (∀ x, (cl.sat x ↔ x c = 0)) ∧
      ¬ IsValueCoord H coordOf i (H.nodes[i]'hi) c) ∨
    (IsValueSupport H coordOf i (H.nodes[i]'hi) cl.support ∧
      cl.codim = cl.support.card ∧
      ∃ (T : TypObject p m cl.support (Fin cl.codim → ZMod p)) (v : Fin cl.codim → ZMod p),
        ∀ x, (cl.sat x ↔ T.φ x = v))
  /-- **`m*(ν_i)` IS the D.11 species inventory** (ROUND 3, blocker 57; ROUND 4: stated via
  the named band `inFreshBand`): the presented fresh codimension sum equals the FRESH-BAND
  count computed from node data (strips + value level sets; past the (γ) crossing the
  fine-slot value `new(j)` is below the floor, so the band self-truncates per fine slot —
  C.1(i)(γ), ROUND 6's exact boundary; at an adjacent read the hinge
  block sits at/beyond `prevRim`, so it is excluded — the (HV) no-pin clause). With
  `fresh_band`/`fresh_cover`/`fresh_assembled` this total now also decomposes PER CLAUSE. -/
  mstar_eq : ∀ (i : ℕ) (hi : i < H.nodes.length),
    (fresh i).mstar = Nat.card {c : Fin m // inFreshBand H n coordOf i (H.nodes[i]'hi) c}

/-- The partial move composite `seg i k = Θ_i ∘ Θ_{i+1} ∘ … ∘ Θ_{k−1}` (frame-`k` coordinates
down to frame-`i` coordinates); `seg 0 k` is `Ψ_H^{−1}` up to prefix `k`. -/
def JetSetup.seg {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (i : ℕ) :
    ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  | 0 => id
  | k + 1 => if i ≤ k then J.seg i k ∘ J.Theta k else id

/-- **The recorded move composite** `Ψ_H^{−1}`-side: `Psi k = Θ_0 ∘ … ∘ Θ_{k−1}` carries the
final-frame presentation back to `f`-coordinates (§C.2: `S(H,Z) = Ψ_H^{−1}(Σ_k ∩ locus Z)`,
stated in `C6.thmC_a/b` about THIS composite — round-1 audit: "no history move composition"). -/
def JetSetup.Psi {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (k : ℕ) :
    (Fin m → ZMod p) → (Fin m → ZMod p) := J.seg 0 k

/-- **The classifier locus `S(H, Z)`, INDEPENDENTLY defined** (ROUND 3, blocker 58 — §C.2's
transported system `T(H, Z)` as a sentence): `x` (frame-0 digits) lies in `S(H, Z)` iff it
carries a presentation chain `y` down the recorded moves (`y 0 = x`, `y i = Θ_i (y (i+1))`)
whose frame-`i` stage satisfies read `ν_i`'s fresh clauses and whose final stage solves `Z`.
This is `E(ν₀) ∪ Θ₀*(E_fresh(ν₁) ∪ Θ₁*( … ∪ Θ_k*(Z)))` with the pullbacks unfolded as the
∃-chain — NO reference to `Sigma` or to any image; `C6.thmC_a` PROVES the equality with the
transported image of the final joint locus. -/
def JetSetup.SHZ {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (Z : Locus p m) :
    Set (Fin m → ZMod p) :=
  {x | ∃ y : ℕ → (Fin m → ZMod p), y 0 = x ∧
    (∀ i : ℕ, i < H.nodes.length → y i = J.Theta i (y (i+1))) ∧
    (∀ i : ℕ, i < H.nodes.length → (J.fresh i).sat (y i)) ∧
    Z.IsSolution (y H.nodes.length)}

/-- **Admissible terminal system `Z`** (§C.2, rev 9 — a LOCUS condition): `Z` solves only for
coordinates FREE on the FINAL state cylinder (round-1 audit: admissibility was checked against
the wrong prefix in the `k = 0` countermodel; consumers instantiate `Sigma := J.Sigma
H.nodes.length`). -/
def AdmissibleZ {p m : ℕ} (Sigma Z : Locus p m) : Prop :=
  ∀ c : Fin m, Z.pinned c = true → Sigma.pinned c = false

/-- The **total pin count** of `T(H, Z)`: `Σ_{i<len} m*(ν_i) + |pins(Z)|` — the codimension of
the joint locus, read off the mass (PIN-WELLDEF; division-free form `mass·p^K = p^{nN}`). -/
def totalPins {H : History p F} {n N m : ℕ} (J : JetSetup H n N m)
    (Z : Locus p m) : ℕ :=
  (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) + Z.numPinned

end

end LeanUrat.MovesC

THE BLUEPRINT (REV 5):
# MOVESD LEAN BLUEPRINT — REV 5

Campaign unit-spec per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2. Writer: Fable.
REV 5 (2026-07-28): the rev-4 verdicts SPLIT maximally — Fable#3 ACCEPT 0/0
(`MOVESD_AUDIT_FABLE3_2026-07-28.md`: gate recomputed, all four pushbacks UPHELD)
vs Codex FINAL#3 REJECT 7/1 (`MOVESD_AUDIT_CODEX_FINAL3_2026-07-28.md`: all four
pushbacks rejected). ORCHESTRATOR ADJUDICATION: most disputes are two-readings-
both-right; REV 5 implements RECONCILING DESIGNS satisfying both (each pointed at
EXPLICITLY where the auditors looked; table §12):
(1) TreeModel is OPTION-ROOTED with the root's presence a LAW (`root_mem` — L2's
"its root is the empty chain ∅") while nonempty-chain inhabitation stays unforced
(L5's (ns) leaf case — Fable's computation stands);
(2) PRESENT-NORM is now the TYPED Prop `PresentNorm` — source set POLICY-FREE
(`PrefSetAny`), so a junk policy or a truncated normalization VIOLATES the field
`Presented.hnorm` (this also implements (6): CanonPolicy adequacy — L1 totality +
the L6-corollary "realizable ⟺ realized" — without pinning offset-P, still POL-PIN);
(3) the ∅ representation is a machine-checked BRIDGE THEOREM (F3 on the new
Option-level `PrefOpt`: literally `Pref(∅) = {∅}` + the CD correspondence);
(4) monicTop keeps the Boolean + guard (Fable's L11 reconstruction stands) PLUS the
definitional tie `MonicTie` (monicTop ↔ the root window's degree-n slot) as a
PrefSet clause — junk-monicTop shapes void their own PrefSet;
(5) D4R4_all is restated at the NOTE's threshold: `Threshold` structure with field
NP + its L12-visible defining properties; Nshape = the constructive witness
(`threshold_witness`); L12/D4R.4 quantifier quoted and matched;
(7) ClassFiberWelldef displayed as a Defs Prop and WIRED as D15's hypothesis;
(8) VerdictModel's cell tie stays the honest declared deferral.
REV-2 table §9, REV-3 §10, REV-4 §11, REV-5 reconciliation §12.

## 0. Source and ground truth

SOURCE: `lean/notes/MOVES_2026-07-24.md`, `## §D4-R — the per-shape-prefix mass law`
(lines ~4580–5432), **rev 9**, DUAL-ACCEPTED 2026-07-27 (Codex pass 11 + Fable confirm
CLEAN on identical text). KERNEL STATUS: D4R.0-K parts (a) L1 totality and (b) L5
digit-cell exhaustiveness DISCHARGED by `D4R0K_DERIVATION_2026-07-26.md` rev 3
(dual-verified); residual (c) = the verdict pin VP (alphabet V + halting rule τ + the
uniform per-class detection cap), OPEN, owned by §T-ASSEMBLY → MovesT. §D4-R's
conditionality: dual-accepted §C (rev 14) + §B2-DEF (D¹¹d) + (c)/VP.

TARGET DISPLAYS: D4R.1-SUM, D4R.1-EV (equality iff mult ≡ 1), D4R.2′ (C ≤ M·p^W,
M ≤ n^{|P̂|}), Corollary D4R.2 (A_net), D4R.4-SUM/EV at every N ≥ N(P̂), and the η = ∅
dispatch (Pref(∅) = {∅}, C_∅ = 1, A(∅) = 0, S(∅,⊤) = the full box) — quoted per unit.

## 0.5 THE ROUTE-(1) ADJUDICATION REPORT (offSlots_forced — what the note supports)

Re-reading L11's injectivity proof verbatim: "given the shape and the digit tuples
through read i−1 AND the indices s₀,…,s_{i−1}, the node data … are reconstructed
(digits give each R_anch; s_r picks ψ_r; canonical lifts are functions of node data,
L1)". The mechanism is: digit tuple → R_anch → (with s_r) → ψ. It needs NO off-slot
data at any read where the digit tuple covers all of R_anch's coefficients — which by
the note's own pinned instance is EVERY read except one case: the ROOT full-span read,
where "slot 3 = the monic lead, digit 1" (§D4-R.6) is excluded from the tuple
(d₀ = 3, not 4) and R₀ = z³+d₂z²+d₁z+d₀ is reconstructed using the MONIC lead 1 — a
fact of the monic degree-n BOX, displayed by the note, not a per-shape convention.
At depth ≥ 1 the lead IS in the tuple (d'₁ counted in W, "the (HV)-forced lead makes
the pool bound strict — slack displayed"). VERDICT: **route (i) holds at every slot
except the root monic lead, whose forcing the note itself displays as the monic-box
convention.** REV 3 therefore DELETES the blanket `offSlots_forced` and replaces the
free `slots` field by a single Boolean `monicTop` per read (is the side's top slot the
box's monic lead?) with the ONE scoped Matches tie `monicTop → sideDigit(ℓ_r) = 1` —
an interface equality justified by the quoted display; d_r := ℓ_r + (monicTop ? 0 : 1)
reproduces the note's counts (d₀ = 3 at ℓ₀ = 3; d₁ = 2 at ℓ₁ = 1). No blanket rule,
no new open hypothesis.

## 0.6 THE η-GRANULARITY REBUILD + THE MANDATORY GATE CHECK (Fable#2 C1)

THE REV-3 DEFECT (gate-evidenced): ambient-valued `etaData` split one note-η into
Galois-conjugate presentations. Fable#2's witness at the sealed gate (§D4-R.6, P̂*,
p = 2): ν₀.zbar ∈ {ω, ω²} (the two roots of ψ = z²+z+1 in the order-4 subfield);
both choices extend to PrefSet members (conjugated stages satisfy every law by
equivariance); (HV) forces the depth-1 lead d'₁ = z̄ − r = ω−1 vs ω²−1 — DISTINCT
F-values, distinct rev-3 classes, ONE note-η. Corpus C = 6 vs the SEALED
C_P̂*(2) = 3; corpus mult ≡ 2 vs the note's gate re-derivation "mult_P̂* ≡ 1 …
EV-equality". The note's η carries NO residue-root datum (L2: children are "(side s,
its digit tuple, ψ, canonical lift)"; digits range in the abstract pool 𝔸_r).

THE REBUILD (Fable#2's recommended route, parallel to the lift normalization): the
CANONICAL PRESENTATION rule gains a residue-root clause. `canonRoot ν` := the
`fieldEnum`-least root of `ψImage ν` in F (§3.4); `IsCanonPres pol H` := the lift
rule AND `(ν_r.zbar : F) = canonRoot ν_r` at every read (§3.2). `PrefSet` requires
`IsCanonPres`. Each note-η then has exactly ONE presentation class: the root choice
at every read is pinned (recenterings were already pinned — `hspecRecCenter`), so
`etaData` no longer sees a conjugation orbit, and by induction the residue-tower
embedding per read is CANONICAL (root: the prime field embeds uniquely; depth r+1:
z ↦ the pinned least root) — abstract-η data ⟺ image data. The residual semantic
duty (every η HAS a root-normalized presentation, via conjugation equivariance of
the Stage/Node laws — Fable#2 exhibited the action; and uniqueness via embedding
rigidity of finite fields) is the DECLARED pin **PRESENT-NORM** (§2 ledger, HC-2) —
exactly parallel to the junk-lift normalization already declared.

THE MANDATORY GATE CHECK (re-derived step by step from the rebuilt construction;
acceptance test per the triage protocol):
- P̂* data: read 0: (e,h,g,μ,a) = (1,1,2,1,0), span [0,3], u*₀ = 0, monicTop = true,
  ℓ₀ = 3, d₀ = 3, w₀ = 1; read 1: (1,3,1,1,0), span [0,1], u*₁ = 1, monicTop = false,
  ℓ₁ = 1, d₁ = 2, w₁ = 2. W = 1·3 + 2·2 = 7 ✓; m̄₀ = ⌊3/2⌋ = 1, m̄₁ = ⌊1/1⌋ = 1,
  M = 1 ✓; Nshape = 1 + max(⌈3⌉, ⌈4⌉) = 5 = N(P̂*) ✓; A = 9 + 2 = 11 ✓ (Fable#2
  reproduced all four from these defs).
- C_P̂*(2), by enumerating the rebuilt classes: read-0 digit tuples (d₂,d₁,d₀) ∈ F₂³
  with realizability R₀ = ψ·(z−r): the unique irreducible quadratic ψ = z²+z+1 and
  r = 1 give R₀ = z³+1, tuple (0,0,1) — 1 tuple × 1 ψ-image. zbar₀: rev 3 had 2
  choices (ω, ω²) → NOW PINNED to canonRoot = the fieldEnum-least root: ×1. Read 1:
  recentering — ψ₁ = z − s determined by the digits (s = −d'₀/d'₁), zbar₁ = center
  pinned by `hspecRecCenter`; digit tuple (d'₀, d'₁): d'₁ = z̄ − r is (HV)-FORCED
  (×1, now the CANONICAL value ω₀ + 1), d'₀ ∈ F₄ˣ free (×3).
  **C_P̂*(2) = 1·1·3 = 3 ✓ = the sealed count** (note: "C_P̂*(2) = 1·1·3 = 3").
  Likewise p = 3: 3 quadratics × r ∈ {1,2} = 6 tuples, d'₀ ∈ F₉ˣ free (×8):
  **C_P̂*(3) = 6·8 = 48 ✓**.
- mult ≡ 1: within P̂*, distinct classes occupy distinct digit cells (per cell the
  eligible quadratic is UNIQUE: deg R₀ = 3 < 2·g₀·μ₀ = 4, and R₁ is linear — the
  note's FACTOR SELECTION line), and the rev-3 conjugate pair is now ONE class; so
  each f in the event realizes exactly the one class of its cell: **mult_P̂* ≡ 1 ✓**,
  D4R.1-EV/D4R.4-EV with EQUALITY — the note's gate re-derivation verbatim.

## 1. The consumption design (what is consumed, what is proved, what remains open)

CONSUMED from MovesC (36/36 PROVED): `History`/`Node` (a realized prefix IS a MovesC
history; `ustar`/`gam`/`pat` are the rev-9 retained fields), `Realizable`
((NA)+(HV)+(SAE)), `HistoryCoherent`, `JetSetup`/`SHZ`/`totalPins`/`mstar_eq`,
`C6_thmC_b` (each summand), the node Props `hRanch`/`hpat0`/`hpatTop`/`hψmonic`/
`hψdeg`/`hψirr`/`hOrd`/`hbezCanon` (these power the PROVED encoding chain).

PROVED IN-CORPUS at rev 3 (previously assumed — findings 3/4/7 of the final audit):
- L8 finiteness and the L11 injection: the note's η is (shape, digit tuples, ψ's,
  canonical lifts) with lifts FUNCTIONS of node data (L1) — so the corpus counts the
  η-CLASS `etaData H` (digit tuples + ψ-coefficient tuples, ambient-field-valued) of
  histories in `PrefSet`. `EtaData` is a finite type, L8 is structural, and the
  injection (digits, factor-rank) ↦ class is PROVED (chain E1–E9) from the node Props:
  deg R_anch = ℓ_r, g·μ ≤ ℓ, the eligible-factor count ≤ m̄_r (coprimality of distinct
  monic irreducibles), the frame-field image = THE p^w subfield (uniqueness in a
  finite field), rank injectivity on the common eligible set. D4R.2′ follows PROVED.
- "deg R_anch,r ≤ n always" (finding 4): PROVED for members via `InBox` (the root side
  lies in the degree-n box — a clause of `PrefSet`, i.e. of "§C history of the
  degree-n box") + the coherence window chain + g·μ ≤ ℓ; `Mfac_le` carries the
  shape-transported `Wellformed` hypothesis PROVED for every inhabited shape (W1) —
  no free rider remains.
- The family is CONSTRUCTED (finding 3): `PrefIdx := ↥(etaData '' PrefSet)`,
  `reprOf` a classical section (a def, not a field), enumeration laws are THEOREMS
  (F1). The SOLE assumed field left is `Presented.jet` (HC-2 presentations).

REMAINING OPEN SURFACE (each a named, typed object — §2 ledger):
`CanonPolicy` parameter `pol` (WHICH policy = the (S6b) offset-P formula; §B2-DEF/
HC-1 pins it; the POLICY LAWS — lift a function of node data, per-node, hence
prefix-monotone and never-empty — are structural, so `Canon := False` is gone:
finding 2); `Presented.jet` (HC-2); the pinned Prop `D4R_CYL` (L6's theorem —
EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus, a hypothesis of D15's bridges,
never a structure field restated as a theorem: finding 7); the `TreeModel` child-
relation data with L2's laws (gap 8); `VerdictModel`'s typed (c)/VP surface with the
halt dichotomy and the per-class detection-cap law (gap 9).

FINITE-LEVEL POLICY: unchanged — `Nat.card` over `Box p m`, division-free. NEW at
rev 3 (finding 5): the count C := `Nat.card (PrefIdx n pol P)` is N-FREE by
construction; the exponent `A′ P n := P.A n (Nshape P)` is N-free via the shape
height bound `Nshape` (the note: "an a priori shape bound on N(P̂) is available");
D10/D12/D13 quantify `∀ N ≥ Nshape P` over all presented setups at that N — D4R.4's
uniform quantifier, with cross-level compatibility automatic (same C, same A′).

## 2. Open-surface ledger (never silently strengthened or dropped)

| object | encodes | status |
|---|---|---|
| `pol : CanonPolicy p F` (parameter) | WHICH canonical policy (the (S6b) offset-P formula) | OPEN parameter, pinned by §B2-DEF/HC-1; its LAWS (lift = function of node data, per-node) are structure fields — `False` not expressible |
| `Matches.hmonic` + `ShapePrefix.MonicTie` (PrefSet clause) [REV 5] | root monic lead digit = 1 (scoped, §0.5) + monicTop ⟺ the root window's degree-n slot (reconciliation (4)) | interface equalities; junk-monicTop shapes void their own PrefSet |
| `InBox n` (PrefSet clause) | the root side lies in the degree-n box | part of "§C history of the degree-n box" (the note's setting); consumed by W1 |
| `Presented.jet` + `Presented.hnorm` [REV 5] | per-class presentations (§C C.2) + the typed dictionary pin | HC-2 bridge — the corpus's two assumed structure fields; `Threshold.{hstab, jets}` packages them at the note's NP (reconciliation (5)) |
| `D4R_CYL S T` (pinned Prop, def) | L6's (D4R-CYL) | note-PROVED given kernel (a)+(b) (both dual-verified-discharged) + Thm C(a); Lean proof EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus; D15 consumes it as a named hypothesis |
| `TreeModel` data (`mem`, `child`) + laws | L2's T_can | interface data; laws are fields; uniqueness/eligibility semantics = kernel-(b) content, HC-2 |
| `VerdictModel` (whole) | D4R.0-K(c)/VP: alphabet V, emission, halt dichotomy, per-class cap law | **OPEN** — owned by §T-ASSEMBLY → MovesT; typed, consumed by nothing in MovesD |
| `hN : 1 ≤ N`, `hm : m = n*N` (D14a/D14b hyps) | L12's empty-case N(P̂) := 1 convention; the box shape | explicit theorem hypotheses (no jet available) |
| **PresentNorm** (TYPED Prop + the FIELD `Presented.hnorm`) [REV 5 ⇐ rev-4 prose pin] | the two-sided classes ↔ η dictionary: totality from the POLICY-FREE `PrefSetAny` (L1 kernel-(a) totality + L6-corollary realizable ⟺ realized + conjugation equivariance) ∧ Galois uniqueness (embedding rigidity) | HC-2 discharge; VIOLATED by truncated normalizations AND by history-voiding junk policies (reconciliations (2)+(6)); gate-checked §0.6 |
| **PRESENT-EXIST** (declared hyp) [REV 4] | `∀ N ≥ Nshape P, Nonempty (Presented …)` — presentability at every sufficient level (§C C.2) | HC-2; sole consumer: `TW_threshold_witness` (Nshape as the constructive `Threshold` witness — reconciliation (5)) |
| **ClassFiberWelldef** (Defs Prop, §3.4) [REV 5: displayed AND wired] | representative independence: one η-class, one classifier locus (§C L4) | HC-2 (wave-4 tree corpus, with D4R_CYL); WIRED as D15's explicit hypothesis `hwd` (reconciliation (7)) |
| **POL-PIN** (future unit, named) [REV 4, Codex#2 f.4] | the instance `pol := the (S6b) offset-P policy` with its realizer laws | owned by HC-1/§B2-DEF corpus; until then all MovesD theorems are ∀-pol |

GONE at rev 3 (previously assumed): `henc` (→ PROVED, E1–E9), `hn : ℓ_r ≤ n`
(→ PROVED, W1), `complete`/`hist_inj`/`hshape`/`hcanon` (→ the construction, F1),
`offSlots_forced` (→ the scoped `hmonic`), `TreeModel.cyl` field (→ the pinned
deferred Prop `D4R_CYL`), bare `cap`/`hcap` (→ the typed cap law).

## 3. Defs skeleton — `lean/LeanUrat/MovesD/Defs.lean` (definitions only)

### 3.1 Box, top locus, shape reads (monicTop replaces slots — §0.5)

```lean
import Mathlib
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

abbrev Box (p m : ℕ) : Type := Fin m → ZMod p

/-- Z = ⊤ (§D4-R L6: "no constraint, vol(⊤) = 1"). -/
def topLocus (p m : ℕ) : Locus p m := { pinned := fun _ => false, solve := fun _ _ => 0 }

/-- One read of a shape-prefix — §D4-R L3 rev 9 retained fields: species, (e,h,g,μ,a),
side data (s0, wSide, Dwidth), the height PAIR (h, u*) [pass-10 F1 CRITICAL], γ, pool
degree w (Q_r = p^w, w ≥ 1), and `monicTop` — whether the side's top slot is the box's
monic lead (§0.5; the stride-position/slot-set datum of L3, reduced to its one degree
of freedom: all other positions always carry tuple digits). Values and lifts forgotten. -/
structure ShapeRead where
  species : ReadSpecies
  e h g μ : ℕ
  a : ℤ
  s0 wSide Dwidth : ℕ
  ustar : ℚ
  gam : ℤ
  w : ℕ
  monicTop : Bool
  he : 1 ≤ e
  hg : 1 ≤ g
  hμ : 1 ≤ μ
  hw : 1 ≤ w
  hDw : 1 ≤ Dwidth
  /-- [REV 4, Codex#2 finding 1 — partial concession]: the monic lead exists only at
  the ROOT read (the box's top coefficient; deeper windows sit inside the box). -/
  hmonicRoot : monicTop = true → species = ReadSpecies.root

def ShapeRead.len (R : ShapeRead) : ℕ := R.wSide / R.e         -- ℓ_r = deg R_anch,r
/-- d_r (the tuple size). [REV 5, reconciliation (4) — Codex#3 finding 1]: the
Boolean is EXACT because at most ONE slot per read is off-box (the degree-n monic
slot, root only — Fable#3 C-1), AND `monicTop` is now SEMANTICALLY TIED by
`ShapePrefix.MonicTie` (a PrefSet clause, §3.2): monicTop = true ⟺ the read is the
root AND its top slot IS the degree-n coefficient position (s0 + wSide = n). A junk
shape faking (or omitting) monicTop violates MonicTie and voids its own PrefSet —
the "artificially smaller W" instance is unbuildable on C-carrying territory. -/
def ShapeRead.d (R : ShapeRead) : ℕ :=
  R.len + (if R.monicTop then 0 else 1)
def ShapeRead.mbar (R : ShapeRead) : ℕ := R.len / (R.g * R.μ)   -- m̄_r (Nat ⌊·⌋)
def ShapeRead.childWidthS (R : ShapeRead) : ℕ := R.e * R.g * R.Dwidth

structure ShapePrefix where
  reads : List ShapeRead

def ShapePrefix.W (P : ShapePrefix) : ℕ := (P.reads.map (fun R => R.w * R.d)).sum
def ShapePrefix.Mfac (P : ShapePrefix) : ℕ := (P.reads.map ShapeRead.mbar).prod

/-- Shape wellformedness over the degree-n box (W1 proves it for every shape with a
member; W2 turns it into M ≤ n^{|P̂|}): the root side fits the box and the window/
degree chain descends — the note's "deg R_anch,r ≤ n ALWAYS", shape-side. -/
def ShapePrefix.Wellformed (P : ShapePrefix) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (hr : r < P.reads.length), (P.reads[r]'hr).len ≤ n

/-- [REV 5, reconciliation (4)] **The monic-slot tie**: `monicTop` is true EXACTLY at
the root read whose side's top slot is the box's degree-n coefficient position
(root frame width 1: slot index = base index). Both directions: faking monicTop
(omitting a genuine digit, shrinking W) AND hiding it (inflating W past the box)
violate the tie. A PrefSet clause (§3.2), so violating shapes have empty PrefSet. -/
def ShapePrefix.MonicTie (P : ShapePrefix) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).monicTop = true ↔ (r = 0 ∧ (P.reads[r]'hr).s0 + (P.reads[r]'hr).wSide = n)
```

### 3.2 Canonical policy, PrefSet, η-classes, the constructed family (findings 1–3)

```lean
section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- A node's side digit at pattern position k, in the AMBIENT field. -/
def _root_.LeanUrat.MovesC.Node.sideDigit (ν : Node p F) (k : ℕ) : F :=
  ((ν.pat k : ↥ν.σ.K) : F)

/-- `R.Matches ν` — field equalities on the retained data (heights INCLUDED), the pool
card, and the ONE scoped monic tie (§0.5). -/
def ShapeRead.Matches (R : ShapeRead) (ν : Node p F) : Prop :=
  ν.species = R.species ∧ ν.e = R.e ∧ ν.h = R.h ∧ ν.g = R.g ∧ ν.μ = R.μ ∧
  ν.a = R.a ∧ ν.s0 = R.s0 ∧ ν.wSide = R.wSide ∧ ν.Dwidth = R.Dwidth ∧
  ν.ustar = R.ustar ∧ ν.gam = R.gam ∧ Nat.card ↥ν.σ.K = p ^ R.w ∧
  (R.monicTop = true → ν.sideDigit R.len = 1)

def ShapePrefix.MatchesHist (P : ShapePrefix) (H : History p F) : Prop :=
  ∃ hlen : H.nodes.length = P.reads.length,
    ∀ (r : ℕ) (hr : r < H.nodes.length), (P.reads[r]'(hlen ▸ hr)).Matches (H.nodes[r]'hr)

/-- **The canonical-lift policy** [REV 3, finding 2]: a DETERMINISTIC per-node lift
rule — L1's defining law "the digits t_k are FUNCTIONS of the node data … the policy
is deterministic", as structure. `liftOf` reads the node MINUS its lift (`blind`), so
a policy can never encode "no history is canonical": `IsCanon pol` is per-node,
automatically prefix-monotone (unit T1a) and total on lift-assignments — the REV-2
lawless `Canon := fun _ => False` is NOT expressible as any `IsCanon pol`. WHICH
policy (the (S6b) offset-P formula) is the open parameter, pinned by §B2-DEF/HC-1.
Junk normalization (documented): the note's policy constrains RECENTERING lifts; we
apply `liftOf` at EVERY node so the non-recentering `lift` junk field is normalized —
this is what makes the η-class granularity (below) carry the note's "canonical lifts
are functions of node data" exactly. -/
structure CanonPolicy (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  liftOf : Node p F → Polynomial ℤ_[p]
  blind : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), liftOf { ν with lift := t } = liftOf ν

def CanonPolicy.IsCanon (pol : CanonPolicy p F) (H : History p F) : Prop :=
  ∀ (r : ℕ) (hr : r < H.nodes.length), (H.nodes[r]'hr).lift = pol.liftOf (H.nodes[r]'hr)

/-- [REV 4, Fable#2 C1] The canonical RESIDUE-ROOT of a node: the `fieldEnum`-least
root of `ψImage ν` in F (junk 0 if none — realizable nodes always have one,
`hzbarRoot`). The presentation-normalization twin of the lift rule. -/
noncomputable def canonRoot (ν : Node p F) : F :=
  ((ψImage ν).roots.toFinset.image (fieldEnum F)).min.elim 0 (fun j => (fieldEnum F).symm j)

/-- **The CANONICAL PRESENTATION class** [REV 4, Fable#2 C1 — the η-granularity
rebuild, §0.6]: canonical lifts (the policy) AND the canonical residue root at every
read. The note's η carries NO root datum (L2's child data: side, digits, ψ, lift);
the root clause is a presentation normalization — each η has exactly ONE normalized
presentation class (PRESENT-NORM, §2 ledger: conjugation equivariance + finite-field
embedding rigidity, HC-2). Recenterings were already pinned (`hspecRecCenter`). -/
noncomputable def CanonPolicy.IsCanonPres (pol : CanonPolicy p F) (H : History p F) : Prop :=
  pol.IsCanon H ∧
  ∀ (r : ℕ) (hr : r < H.nodes.length),
    (((H.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H.nodes[r]'hr)

/-- The root read's side fits the degree-n box (part of "§C history of the degree-n
box" — the note's ambient setting; powers W1's ℓ_r ≤ n chain). -/
def InBox (n : ℕ) (H : History p F) : Prop :=
  ∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).s0 + (H.nodes[0]'hj).wSide ≤ n

/-- **The LITERAL Lean Pref(P̂)** (L3: shape-match + realizable + canonical lifts, in
the degree-n box). -/
def PrefSet (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) : Set (History p F) :=
  {H | P.MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧ InBox n H ∧
       P.MonicTie n ∧ pol.IsCanonPres H}
-- [REV 4] `IsCanon` → `IsCanonPres` (root-normalized presentation class, §0.6).
-- [REV 5, reconciliation (4)] + the `MonicTie` clause.
-- Defs-file order note: `RanchImage`/`ψImage`/`poolSubfield` (§3.4) precede this
-- section in the actual `Defs.lean` (canonRoot consumes ψImage).

/-- [REV 5, reconciliations (2)+(6) — Codex#3 findings 2/3; Fable#3 OBS-1's own
recommendation] The POLICY-FREE realizable prefix set: shape-matched, coherent,
realizable, in-box — NO canonicity clause of either kind. The reference set for the
typed dictionary pin `PresentNorm` below. -/
def PrefSetAny (n : ℕ) (P : ShapePrefix) : Set (History p F) :=
  {H | P.MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧ InBox n H ∧ P.MonicTie n}

/-- Coordinatewise field-automorphism action on η-class data (the Galois relation
between conjugate presentations — Fable#2 C1's witness action). -/
def EtaGalEq {P : ShapePrefix} (d d' : EtaData F P) : Prop :=
  ∃ φ : F ≃+* F, ∀ r : Fin P.reads.length,
    ((d' r).1 = fun k => φ ((d r).1 k)) ∧ ((d' r).2 = fun k => φ ((d r).2 k))

/-- **PRESENT-NORM, TYPED** [REV 5, reconciliation (2)+(6) — supersedes the rev-4
prose pin]: the two-sided dictionary between the note's η's and the normalized
classes. (i) TOTALITY (= L1's kernel-(a) totality + the L6-corollary "realizable ⟺
realized" + conjugation equivariance): every POLICY-FREE realizable prefix has a
normalized class-mate up to Galois — so BOTH a truncated normalization (empty
PrefIdx against nonempty PrefSetAny) AND a history-voiding junk policy VIOLATE this
Prop; (ii) UNIQUENESS (embedding rigidity): Galois-related normalized classes
coincide — classes never double-count an η. Math status: note-supported (L1
dual-verified-discharged; equivariance/rigidity per Fable#2 C1); Lean discharge =
HC-2. Carried as the FIELD `Presented.hnorm` — every consumer of a presented family
consumes it (the auditors' wiring demand). -/
def PresentNorm (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) : Prop :=
  (∀ H ∈ PrefSetAny n P, ∃ i : PrefIdx n pol P, EtaGalEq (etaData P H) (i : EtaData F P)) ∧
  (∀ H H', H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    EtaGalEq (etaData P H) (etaData P H') → etaData P H = etaData P H')

/-- [REV 5, reconciliation (3) — Codex#3 finding 5] The OPTION-LEVEL Pref: the
note's chain ontology with the empty prefix as a first-class member (`none` = the
empty chain ∅). F3 proves `Pref(∅) = {∅}` LITERALLY on this object, and the CD
correspondence — the representation deviation is machine-checked, not declared. -/
def PrefOpt (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) :
    Set (Option (History p F)) :=
  {c | match c with
       | none => P.reads = []
       | some H => H ∈ PrefSet n pol P ∧ P.reads ≠ []}

/-- Option-level class data (none ↦ none — the η = ∅ class). -/
noncomputable def etaDataO (P : ShapePrefix) :
    Option (History p F) → Option (EtaData F P)
  | none => none
  | some H => some (etaData P H)

/-- **The η-class data** — the note's η-granularity [REV 3, finding 3's enabler]: per
read, the side-digit tuple AND ψ's coefficient tuple, ambient-field-valued. Everything
else in the note's η is shape-pinned (Matches), derived (line by coherence+u*; (s,t)
the canonical Bézout pair; Ranch by hRanch), or policy-determined (lifts, L1). A
FINITE type: L8 is structural, and C is N-free. -/
def EtaData (F : Type*) (P : ShapePrefix) : Type :=
  ∀ r : Fin P.reads.length,
    (Fin ((P.reads.get r).len + 1) → F) × (Fin ((P.reads.get r).g + 1) → F)

noncomputable def etaData (P : ShapePrefix) (H : History p F) : EtaData F P :=
  fun r => ((H.nodes[(r : ℕ)]?).elim (fun _ => 0) (fun ν k => ν.sideDigit k),
            (H.nodes[(r : ℕ)]?).elim (fun _ => 0) (fun ν k => ((ν.ψ.coeff k : ↥ν.σ.K) : F)))

/-- **The canonical index of Pref(P̂)**: the η-classes of PrefSet. C_P̂(p) counts THESE
(the note's C counts η's = (shape, digits, ψ's, canonical lifts); lifts are
policy-determined, so classes ↔ η's — F1's semantic display). N-FREE. -/
def PrefIdx (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) : Type :=
  ↥(etaData P '' PrefSet n pol P)

/-- The classical representative section (a DEF, not a field — finding 3). -/
noncomputable def reprOf {n : ℕ} {pol : CanonPolicy p F} {P : ShapePrefix}
    (i : PrefIdx n pol P) : History p F := i.2.choose

/-- The corpus C with the note's η = ∅ dispatch baked in at the note's own
definition level (Pref(∅) = {∅} — §D4-R L12/D4R.1: "present iff P̂ = ∅"). -/
noncomputable def ShapePrefix.CD (P : ShapePrefix) (n : ℕ) (pol : CanonPolicy p F) : ℕ :=
  if P.reads = [] then 1 else Nat.card (PrefIdx n pol P)

/-- S(∅,⊤) — §C C.0's EMPTY HISTORY clause at Z = ⊤ (the FULL BOX; never Thm C(b)). -/
def emptyFiber (p m : ℕ) : Set (Box p m) := Set.univ

/-- **The presented family** [REV 3, finding 3]: everything is CONSTRUCTED from
`PrefSet` except the two genuinely-open data — the HC-2 presentations and the typed
dictionary pin. [REV 5, reconciliation (2)+(6) — Codex#3 findings 2/3, Fable#3
OBS-1]: `hnorm` makes PRESENT-NORM a FIELD: a family over a truncated normalization
(empty `PrefIdx`, nonempty `PrefSetAny`) or over a history-voiding junk policy is
NOT `Presented` — the vacuity instances Codex exhibited violate `hnorm`, and every
mass-law unit consumes it through its `S` binder. -/
structure Presented (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) where
  jet : (i : PrefIdx n pol P) → JetSetup (reprOf i) n N m
  hnorm : PresentNorm n pol P

/-- [REV 5, reconciliation (5) — Codex#3 finding 4] **The note's threshold, as
data with its L12-visible defining properties.** L12 QUOTED: "N(P̂) :=
max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅ … N(P̂) is finite, and for EVERY
N ≥ N(P̂): (D4R.4-SUM) … (D4R.4-EV)". `N(η,⊤)` is a §C-presentation quantity, so
its corpus-visible content is exactly: (i) `hstab` — the ledger exponent is stable
from NP on (each fiber is cut at level ≤ NP: no band content above); (ii) `jets` —
presentations exist at EVERY level ≥ NP (§C C.2). `Nshape` is the CONSTRUCTIVE
WITNESS: unit TW proves `Threshold` inhabited with NP := Nshape under PRESENT-EXIST
(the note: "an a priori shape bound on N(P̂) is available but not needed"), i.e.
Nshape ≥ N(P̂) materialized. The note does NOT quantify over presentations (its
counts are intrinsic); the per-level count is presentation-mediated here, with
intrinsic-ness = ClassFiberWelldef (declared). -/
structure Threshold (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) where
  NP : ℕ
  hNP1 : 1 ≤ NP
  hstab : ∀ N : ℕ, NP ≤ N → P.A n N = P.A' n
  jets : ∀ N : ℕ, NP ≤ N → Presented p F n N (n * N) pol P

def Presented.fiber (S : Presented p F n N m pol P) (i : PrefIdx n pol P) :
    Set (Box p m) := (S.jet i).SHZ (topLocus p m)
def Presented.event (S : Presented p F n N m pol P) : Set (Box p m) := ⋃ i, S.fiber i
noncomputable def Presented.mult (S : Presented p F n N m pol P) (x : Box p m) : ℕ :=
  Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i}
```

REPRESENTATIVE CAVEAT (displayed for the audit): `fiber i` is the chosen
representative's `SHZ ⊤`. That all representatives of one η-class present the SAME
classifier locus is HC-2 semantic content (the class determines the classifier run);
formally the corpus is exact about the chosen representatives, and every mass-law
statement consumes only `jet`, Theorem C(b), and the class count — nothing
representative-dependent beyond the jet itself. Flagged for the guardian.

### 3.3 The ledger exponent A(P̂), Nshape, the N-free A′ (findings 4/5)

Unchanged mechanism from rev 2 (the shape-side replica of MovesC's fresh band; u*
enters through the line intercept — the rev-9 point), plus the N-stabilization:

```lean
def ShapePrefix.strS (P : ShapePrefix) (i : ℕ) : ℕ := ((P.reads.take i).map ShapeRead.e).prod
noncomputable def ShapePrefix.lineS (P : ShapePrefix) (r : ℕ) : Line :=
  (P.reads[r]?).elim ⟨0, 0⟩ (fun R =>
    let sl : ℚ := (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ) * (R.Dwidth : ℚ))
    ⟨R.ustar + sl * (((R.s0 + R.wSide) * R.Dwidth : ℕ) : ℚ), sl⟩)
noncomputable def ShapePrefix.kappaS (P : ShapePrefix) (r : ℕ) : ℚ :=
  (P.reads[r]?).elim 0 (fun R => (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ)))
def ShapePrefix.innerslotS (P : ShapePrefix) (r b : ℕ) : ℕ :=
  (P.reads[r]?).elim 0 (fun R => (b % R.childWidthS) / R.Dwidth)
noncomputable def ShapePrefix.htS (P : ShapePrefix) (i : ℕ) (c : Coord) : ℚ :=
  (c.1 : ℚ) + (Finset.range i).sum (fun r => (P.innerslotS r c.2 : ℚ) * P.kappaS r)
noncomputable def ShapeRead.staircaseS (R : ShapeRead) (L : Line) (b : ℕ) : WithBot ℚ :=
  if b < R.μ * R.childWidthS then ((L.at ((b / R.childWidthS) * R.childWidthS) : ℚ) : WithBot ℚ) else ⊥
noncomputable def ShapePrefix.floorS (P : ShapePrefix) (i b : ℕ) : WithBot ℚ :=
  ((List.range i).map (fun r => (P.reads[r]?).elim ⊥ (fun R => R.staircaseS (P.lineS r) b))).foldr max ⊥
def ShapePrefix.prevRimS (P : ShapePrefix) (n : ℕ) : ℕ → ℕ
  | 0 => n | i + 1 => (P.reads[i]?).elim n (fun R => R.μ * R.childWidthS)
noncomputable def ShapePrefix.bandS (P : ShapePrefix) (n r : ℕ) (c : Coord) : Prop :=
  c.2 < P.prevRimS n r ∧ P.floorS r c.2 < ((P.htS r c : ℚ) : WithBot ℚ) ∧
  (P.reads[r]?).elim False (fun R => P.htS r c ≤ (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth))
open Classical in
noncomputable def ShapePrefix.A (P : ShapePrefix) (n N : ℕ) : ℕ :=
  (Finset.range P.reads.length).sum (fun r =>
    ((Finset.range N ×ˢ Finset.range n).filter (fun c => P.bandS n r c)).card)
/-- The a-priori SHAPE bound on the band's levels (the note's L12: "an a priori shape
bound on N(P̂) is available"): 1 + max over reads of ⌈intercept of lineS⌉₊ — every
band coordinate has level ℓ ≤ htS ≤ line value ≤ intercept, so levels ≥ Nshape are
band-free. -/
noncomputable def ShapePrefix.Nshape (P : ShapePrefix) : ℕ :=
  1 + ((List.range P.reads.length).map (fun r => ⌈(P.lineS r).intercept⌉.toNat)).foldr max 0
/-- **The N-FREE ledger exponent A′(P̂, n)** (finding 5): A at the stabilization level. -/
noncomputable def ShapePrefix.A' (P : ShapePrefix) (n : ℕ) : ℕ := P.A n (P.Nshape)
noncomputable def ShapePrefix.Anet (P : ShapePrefix) (n : ℕ) : ℤ := (P.A' n : ℤ) - (P.W : ℤ)
```

### 3.4 The encoding target, the tree, the verdict layer (findings 3/7 + gaps 8/9)

```lean
/-- The pool: THE order-p^w root set in F (units E1–E3 identify it with every matched
frame field's image). -/
def pool (p w : ℕ) (F : Type*) [Field F] : Set F := {x : F | x ^ (p ^ w) = x}

/-- A classically-fixed enumeration of F — the shared "fixed residue bases" order
(D.3(e)) for the rank; one choice for the whole corpus. -/
noncomputable def fieldEnum (F : Type*) [Finite F] : F ≃ Fin (Nat.card F) :=
  (Finite.equivFin F).trans (finCongr (Nat.card_eq_fintype_card (α := F)).symm)

/-- The rank of ψ among the eligible same-shape factors of Ranch (L11's s_r), via the
shared enumeration — DEFINED, not data. Stated on F-coefficient images so classes
compare across members (units E6–E8 give rank < m̄ and rank-injectivity). -/
/-- [REV 4, Fable#2 G1 ≈ Codex#2 finding 3 — the gloss was FALSE as written: without
irreducibility E7 fails (Fable's counterexample: 4 distinct linear factors, g = 2,
μ = 1 → SIX monic ord-1 quadratic divisors vs m̄ = 2); with Irreducible-over-F it
fails the other way (a deg-≥2 image SPLITS over F ⊇ F_{p^{w·g}}). The correct
predicate is the TRANSPORTED one, spelled out:] -/
def RanchImage (ν : Node p F) : Polynomial F := ν.Ranch.map (SubfieldClass.subtype _ …)
def ψImage (ν : Node p F) : Polynomial F := ν.ψ.map (SubfieldClass.subtype _ …)
/-- `pool p w F` as a subfield (Frobenius-power fixed points — closed under the field
operations in char p). -/
def poolSubfield (p w : ℕ) (F : Type*) [Field F] : Subfield F := ⟨…carrier := pool p w F…⟩
/-- **The transported eligibility predicate** (the note's "{ψ monic irreducible :
deg ψ = g_r, ord_ψ R_anch = μ_r}", read on F-images): q is monic of degree g with
ord_q(Rq) = μ AND q is the image of an IRREDUCIBLE polynomial over the POOL SUBFIELD
(equivalently: coefficients in the pool + irreducible over it — never over F). -/
def EligibleImage (p w g μ : ℕ) {F : Type*} [Field F] (Rq q : Polynomial F) : Prop :=
  q.Monic ∧ q.natDegree = g ∧ OrdPsiPoly q Rq μ ∧
  ∃ q₀ : Polynomial ↥(poolSubfield p w F),
    Irreducible q₀ ∧ q₀.map (poolSubfield p w F).subtype = q

noncomputable def selRank {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (w : ℕ) (ν : Node p F) : ℕ :=
  Nat.card {q : {q : Polynomial F // EligibleImage p w ν.g ν.μ (RanchImage ν) q} //
    lexLt (fieldEnum F) q.1 (ψImage ν)}
  -- `lexLt` = coefficient-lex through the classically fixed `fieldEnum` (the
  -- D.3(e)-order substitute; the encoding bound is order-invariant — Fable#2 §3.8).

/-- The L11 encoding target (pool-valued digit tuples of the RETAINED sizes d_r +
selection indices). -/
def EncTargetP (p : ℕ) (F : Type*) [Field F] (P : ShapePrefix) : Type :=
  ∀ r : Fin P.reads.length,
    ((Fin (P.reads.get r).d → ↥(pool p (P.reads.get r).w F)) × Fin (P.reads.get r).mbar)

/-- Appending a non-root node to a history (for the tree's child laws). -/
def _root_.LeanUrat.MovesC.History.snoc (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) : History p F := ⟨H.nodes ++ [ν], by simp, …⟩

def _root_.LeanUrat.MovesC.History.IsPrefixOf (H H' : History p F) : Prop := H.nodes <+: H'.nodes

/-- **T_can(f) with L2's structure** [REV 3, gap 8]: membership AND the child
relation (`none` = children of the EMPTY chain — the root reads), with the two
generation laws; prefix-closure becomes a THEOREM (T1a). Eligibility semantics of
`child` ("ALL eligible (side, ψ) continuations", cell data) is kernel-(b) content —
HC-2; uniqueness of the tree per input is the model's meta-duty, documented. -/
structure TreeModel (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) where
  /-- [REV 5, reconciliation (1) — Codex#3 finding 6 ∧ Fable#3 C-8, BOTH satisfied]:
  the node carrier is `Option (History p F)` — `none` IS the empty chain ∅, a
  first-class tree node. -/
  mem : Option (History p F) → Box p m → Prop
  child : Option (History p F) → Node p F → Box p m → Prop
  /-- **THE ROOT'S PRESENCE IS A LAW** (L2: "its root is the empty chain ∅" — the
  root exists for EVERY input; Codex's reading). It may be a LEAF (no children —
  L5's (ns) case; Fable's computation), so NO nonempty-chain inhabitation is forced:
  both rev-4 readings hold on this carrier. -/
  root_mem : ∀ x : Box p m, mem none x
  mem_single : ∀ (ν : Node p F) (h1 : _) (x), mem (some ⟨[ν], h1.1, h1.2⟩) x ↔ child none ν x
  mem_snoc : ∀ (H ν hν x), mem (some (H.snoc ν hν)) x ↔ (mem (some H) x ∧ child (some H) ν x)
  mem_realizable : ∀ H x, mem (some H) x →
    HistoryCoherent H ∧ Realizable H ∧ pol.IsCanonPres H

/-- [REV 5, reconciliation (1) — superseding the rev-4 pushback display]: the
rev-4 dispute is RESOLVED on the Option carrier: Codex#3-f.6's "the empty root
always exists" is now the LAW `root_mem`; Fable#3-C-8's "nonempty chains need not
exist" (L5 (ns): ∅ can be a leaf) remains respected — no law forces `some`-chains;
and the old falsifying computation still guards consumers (`mem some· := False`
fails `D4R_CYL` against D0c's nonempty fibers). Exhaustive-children semantics stays
kernel-(b) content behind the D4R_CYL / ClassFiberWelldef pins. §12 row 1. -/

/-- L6's (D4R-CYL), as the PINNED Prop [REV 3, finding 7]: S(η,⊤) = {f : η ∈ T_can(f)}
for every enumerated class. Note-PROVED (kernel (a)+(b) dual-verified-discharged +
Thm C(a)); its LEAN proof is EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus.
D15 consumes it as a named hypothesis — it is NOT a TreeModel field. -/
def D4R_CYL {n N m : ℕ} {pol : CanonPolicy p F} {P : ShapePrefix}
    (S : Presented p F n N m pol P) (T : TreeModel p F n N m pol) : Prop :=
  ∀ (i : PrefIdx n pol P) (x : Box p m), x ∈ S.fiber i ↔ T.mem (some (reprOf i)) x

/-- [REV 5, reconciliation (7) — Codex#3 finding 7: now DISPLAYED and WIRED (D15's
`hwd` hypothesis), no longer ledger-only] Representative independence: one η-class,
one classifier locus, over ALL representatives and ALL jets (§C L4's semantic
content). Deferred to the wave-4/HC-2 tree corpus together with `D4R_CYL`; the two
jointly restore L6's every-η/every-presentation reading. -/
def ClassFiberWelldef (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) : Prop :=
  ∀ (H H' : History p F), H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    etaData P H = etaData P H' →
    ∀ (J : JetSetup H n N m) (J' : JetSetup H' n N m),
      J.SHZ (topLocus p m) = J'.SHZ (topLocus p m)

/-- **The (c)/VP surface, typed** [REV 3, gap 9]: alphabet V; the emission map vdict
(none = the read continues); the HALT DICHOTOMY = L2's "a chain has NO children iff
its read returns a terminal verdict" (both directions in one iff — `leaf` is now the
DEFINED `T.mem H x ∧ vdict H x ≠ none`, not a field, so no `leaf := False` instance
exists); the PER-CLASS DETECTION CAP with its law: verdict v is determined by the
digits below level `cap v` — the "uniform per-class detection cap" typed against
vdict. τ-as-cell-data and the VP-1/VP-2 semantics remain MovesT's — this structure is
the OPEN kernel-(c) surface, consumed by nothing in MovesD. -/
structure VerdictModel {n N m : ℕ} {pol : CanonPolicy p F}
    (T : TreeModel p F n N m pol) where
  V : Type
  hVfin : Finite V
  hVne : Nonempty V
  vdict : History p F → Box p m → Option V
  halt_iff : ∀ H x, T.mem (some H) x →
    (vdict H x ≠ none ↔ ∀ (ν : Node p F) (hν : ν.species ≠ ReadSpecies.root),
      ¬ T.child (some H) ν x)
  -- [REV 5] vdict stays on NONEMPTY chains; the ∅-root's own (ns) verdict is
  -- MovesT's corner (VP-2's root clause), documented not modeled.
  /-- the box level of each digit coordinate (the presented charts' first component;
  MovesT pins it to the jets' `coordOf`). -/
  levelOf : Fin m → ℕ
  /-- [REV 4, Codex#2 finding 10] the chart-range consistency of `levelOf` (the full
  chart tie `levelOf = (coordOf ·).1` per presented jet is MovesT's, at consumption). -/
  levelOf_lt : ∀ c : Fin m, levelOf c < N
  cap : V → ℕ
  cap_law : ∀ (v : V) (H : History p F) (x x' : Box p m),
    vdict H x = some v → (∀ c : Fin m, levelOf c < cap v → x c = x' c) →
      vdict H x' = some v
  /-- [REV 4, Codex#2 finding 10] FINITE-LEVEL LOCALITY (both branches, `none`
  included): vdict is a function of the digits below the cap envelope — the typed
  finite-level shadow of "τ is a function of CELL data alone, never of f" (VP-2).
  The cell-exact tie (vdict factors through the digit-cell of H's frame) needs the
  frames and is MovesT's VP duty — documented, not silently claimed. -/
  vdict_local : ∀ (H : History p F) (x x' : Box p m),
    (∀ c : Fin m, (∃ v : V, levelOf c < cap v) → x c = x' c) → vdict H x = vdict H x'

end
end LeanUrat.MovesD
```

## 4. Unit specs (46 units [REV 4: +W3, +D4R4_all; REV 5: +F3]; all in `lean/LeanUrat/MovesD/`)

Common binders (elided): `{p} [Fact p.Prime] {F} [Field F] [Finite F] {n N m : ℕ}
{pol : CanonPolicy p F} {P : ShapePrefix}`; `S : Presented p F n N m pol P`;
`top := topLocus p m`. AUX = no note display; informal statement given.

### D0a — topLocus_laws · `D0a_topLocus.lean` — as rev 2 (sol/numPinned/admissible).
moves_ref: "Z = ⊤: no constraint, vol(⊤) = 1" (L6). deps: MovesC. easy.

### D0b — thmC_top · `D0b_thmCtop.lean` — as rev 2 (`totalPins_top`, `thmC_top`).
moves_ref: "Each NONEMPTY summand is Theorem C(b) with Z = ⊤". deps: C6_thmC_b, D0a.
easy. hypothesis_fields: none (J a binder; existence = `Presented.jet`, HC-2).

### D0c — fiber_pos · `D0c_fiberPos.lean`
statement: `theorem fiber_pos (S) (i : PrefIdx n pol P) : (S.fiber i).Nonempty`
moves_ref: "Theorem C(b) gives mass p^{−A(P̂)} > 0" (L6 corollary). deps: D0b. easy.

### THE ENCODING CHAIN E1–E9 (L11 PROVED — final-audit findings 1/3/4)

### E1 — digit_in_pool · `E1_digitPool.lean` (AUX)
informal: a matched node's side digits lie in the order-p^w root set.
statement: `theorem digit_in_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) (k : ℕ) : ν.sideDigit k ∈ pool p R.w F`
deps: Defs. sketch: `FiniteField.pow_card` on ↥ν.σ.K (card p^w by hM); ring-hom
coercion. medium.

### E2 — pool_card_le · `E2_poolCard.lean` (AUX)
statement: `theorem pool_card_le (hp : 2 ≤ p) (hw : 1 ≤ w) : Nat.card ↥(pool p w F) ≤ p ^ w`
deps: Defs. sketch: roots of the nonzero X^{p^w} − X; `Polynomial.card_roots`. medium.

### E3 — frameField_eq_pool · `E3_frameField.lean` (AUX)
informal: the frame field's image in F IS the pool (the unique subfield per order —
what lets classes of DIFFERENT members share one eligible-factor universe).
statement: `theorem frameField_eq_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) : (Set.range (fun a : ↥ν.σ.K => (a : F))) = pool p R.w F`
deps: E1, E2. sketch: range is a subfield of card p^w inside pool (E1); pool has ≤ p^w
elements (E2); equal cards force equality. medium.

### E4 — Ranch_deg · `E4_ranchDeg.lean` (AUX)
informal: deg R_anch = ℓ_r — the note's "deg R_anch,r equals that side's NORMALIZED
horizontal length ℓ_r := w'_r/e_r" (L11), PROVED from the node Props.
statement: `theorem Ranch_deg (ν : Node p F) : ν.Ranch.natDegree = ν.wSide / ν.e`
deps: MovesC. sketch: `hRanch` (the pattern sum) + `hpatTop` (top digit ≠ 0):
natDegree of Σ_{k≤len} C(pat k)·X^k with nonzero top. medium.

### E5 — gmu_le_len · `E5_gmuLe.lean` (AUX)
informal: g·μ ≤ ℓ_r (each eligible factor contributes g·μ to deg R_anch — L11).
statement: `theorem gmu_le_len (ν : Node p F) : ν.g * ν.μ ≤ ν.wSide / ν.e`
deps: E4. sketch: `hOrd` gives ψ^μ ∣ Ranch, Ranch ≠ 0 (hpatTop); degrees:
μ·g = deg ψ^μ ≤ deg Ranch = ℓ (hψdeg, E4). medium.

### E6 — eligible_card_le · `E6_eligibleCard.lean` (AUX)
informal: R_anch holds at most m̄ = ⌊ℓ/(g·μ)⌋ monic irreducible degree-g ord-μ
factors — L11's "each contributes g_r·μ_r to its degree".
statement: `theorem eligible_card_le (ν : Node p F) : Nat.card {q : Polynomial ↥ν.σ.K // q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ} ≤ (ν.wSide / ν.e) / (ν.g * ν.μ)`
deps: E4. sketch: distinct monic irreducibles are coprime; the product of q^μ over
any k eligible factors divides Ranch (UFD), so k·g·μ ≤ deg Ranch = ℓ, k ≤ ⌊ℓ/(gμ)⌋.
medium-hard.

### E7 — selRank_lt · `E7_rankLt.lean` (AUX)  [REV 4: re-verified against the
TRANSPORTED `EligibleImage` (§3.4) — Fable#2 G1's counterexample (six reducible
ord-1 quadratics vs m̄ = 2) hits only the withdrawn gloss]
informal: the defined rank is a legal selection index: selRank < m̄_r.
statement: `theorem selRank_lt {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) : selRank R.w ν < R.mbar`
deps: E3, E6. sketch: (i) MEMBERSHIP: ψImage ν satisfies the transported predicate —
monic/deg/ord push through the coefficient embedding, and ν.ψ itself is the
irreducible lift over ↥σ.K ≃ poolSubfield (E3's identification); (ii) CARD: the
transported eligible set pulls back injectively to E6's K-side set (map injective on
poolSubfield-coefficient polynomials), so its card ≤ m̄ (E6 + Matches ties ℓ, g, μ);
rank = a proper-initial-segment count in a set of card ≤ m̄ containing ψImage.
medium-hard.

### E8 — rank_inj · `E8_rankInj.lean` (AUX)
informal: on ONE eligible set, rank determines the factor (lex through the shared
`fieldEnum` is a strict total order — the note's "ordered lexicographically by
coefficient vectors in D.3(e)'s fixed residue bases").
statement: `theorem rank_inj {R : ShapeRead} {ν ν' : Node p F} (hM : R.Matches ν) (hM' : R.Matches ν') (hg : ν.g = ν'.g) (hμ : ν.μ = ν'.μ) (hR : RanchImage ν = RanchImage ν') (hs : selRank R.w ν = selRank R.w ν') : ψImage ν = ψImage ν'`
deps: E3, E6. sketch: equal Ranch-images + E3's common subfield give literally equal
F-side eligible sets; two members of a finite set with equal strict-initial-segment
counts under a strict total order are equal. medium-hard.

### E9 — encIdx_inj · `E9_encInj.lean`
statement: `theorem encIdx_inj : Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F P)`
  (Defs addendum: `encIdx i := fun r => (digits of the class at the d_r counted
  positions, ⟨selRank (node r of reprOf i), E7⟩)`.)
moves_ref: "The map enc′: η ⟼ (the side-digit tuples (d_j) of its reads; the
selection indices (s_r)) is an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1,…,m̄_r})"
(L11 — now a THEOREM at the η-class granularity).
deps: E1, E3, E4, E7, E8; Defs (Matches.hmonic). sketch: classes are (digit-tuple,
ψ-image) sequences; the d_r counted digits + the scoped monic tie (§0.5) recover the
FULL digit tuple; the digit tuple determines RanchImage (hRanch, coefficient images);
E8 recovers ψImage from the rank. So encIdx equal ⟹ etaData equal ⟹ i = j
(subtype ext). [REV 4: classes are now ROOT-NORMALIZED (§0.6) — the injection's
source is conjugation-free, so its count is the note's C; the chain itself is
unchanged (Fable#2: "NOT contaminated: the E1–E9 chain itself").] medium-hard.

### D2a — L8_finite_C · `D2a_finite.lean`
statement:
  `instance : Finite (PrefIdx n pol P)` — L8, structural (a subtype of the finite `EtaData`).
  `theorem CD_eq (hne : P.reads ≠ []) : P.CD n pol = Nat.card (PrefIdx n pol P)`
moves_ref: "L8: Pref(P̂) is FINITE … Hence #Pref(P̂) ≤ M(P̂)·∏_r Q_r^{d_r} < ∞".
deps: Defs. sketch: EtaData is a Pi of finite types; `if_neg`. easy.
hypothesis_fields: none — the finiteness mechanism is now the η-class construction
itself (final-audit finding 3 repaired).

### F1 — the constructed enumeration · `F1_enum.lean`
statement:
  `theorem reprOf_mem (i : PrefIdx n pol P) : reprOf i ∈ PrefSet n pol P`
  `theorem etaData_reprOf (i : PrefIdx n pol P) : etaData P (reprOf i) = (i : EtaData F P)`
  `theorem card_classes : Nat.card (PrefIdx n pol P) = Nat.card (etaData P '' PrefSet n pol P)`
moves_ref: "Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts }, C_P̂(p) :=
#Pref(P̂)" — the enumeration is CONSTRUCTED, completeness/injectivity are definitional
theorems (final-audit finding 3: nothing assumed). [REV 5, reconciliation (2) —
Codex#3 finding 3, ANSWERED WHERE IT LOOKED: "classes ↔ η's" is NO LONGER prose —
it is the TYPED Prop `PresentNorm n pol P` (§3.2: totality from the POLICY-FREE
`PrefSetAny` + Galois uniqueness), carried by every family as the FIELD
`Presented.hnorm`. The truncated-normalization instance (empty PrefIdx, nonempty
PrefSetAny) VIOLATES it. Gate-checked at §0.6 — C_P̂*(2) = 3, C_P̂*(3) = 48,
mult ≡ 1.]
deps: Defs. sketch: `Exists.choose_spec` twice; `Nat.card` of a subtype of a set
coerced. easy.

### W1 — wellformed_of_mem · `W1_wellformed.lean`
statement: `theorem wellformed_of_mem {H : History p F} (hH : H ∈ PrefSet n pol P) : P.Wellformed n`
moves_ref: "COARSE CHAIN … deg R_anch,r ≤ n always" (L11) — PROVED: no `hn` rider
(final-audit finding 4).
deps: E4, E5. sketch: induction down the reads: root — ℓ₀ = wSide/e ≤ s0+wSide ≤ n
(`InBox`, a PrefSet clause); step — coherence's window containment
s0'+wSide' ≤ μ_prev, so ℓ_{r+1} ≤ wSide' ≤ μ_prev ≤ ℓ_prev/(g·μ)·(g·μ) ≤ ℓ_prev
(E5 at the parent) ≤ n; transport each ℓ to the shape via Matches. medium.

### W2 — Mfac_le · `W2_MfacLe.lean`
statement: `theorem Mfac_le (hwf : P.Wellformed n) : P.Mfac ≤ n ^ P.reads.length`
moves_ref: "M(P̂) := ∏_r m̄_r ≤ ∏_r ⌊n/(g_rμ_r)⌋ ≤ n^{|P̂|} (m̄_r as above … coarse
chain displayed)". deps: Defs. sketch: m̄_r = ℓ_r/(gμ) ≤ ℓ_r ≤ n (hwf, Nat.div_le_self);
List.prod ≤ pow. easy-medium. hypothesis_fields: `hwf` — PROVED by W1 for every
inhabited shape; for uninhabited shapes the D4R.2 chain never needs it (C = 0).

### W3 — D4R2'_coarse · `W3_coarseBound.lean`  [REV 4, Codex#2 finding 5]
statement: `theorem D4R2'_coarse : Nat.card (PrefIdx n pol P) ≤ n ^ P.reads.length * p ^ P.W`
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, M(P̂) ≤ n^{|P̂|} p-FREE (L11)" — the two displayed
inequalities CHAINED ON C, now UNCONDITIONAL: no Wellformed hypothesis survives.
deps: D3a, W1, W2, F1. sketch: case split on `Nonempty (PrefIdx n pol P)`: empty —
C = 0 ≤ anything; nonempty — pull a member via `reprOf`/F1, W1 gives `Wellformed n`,
chain D3a with W2. easy. hypothesis_fields: NONE. [The BARE `Mfac ≤ n^{|P̂|}` for
junk shape data (ℓ_r > n) is FALSE and not the note's claim — the note's "always"
ranges over shapes of degree-n classifier histories; on C-carrying territory the
display is now hypothesis-free. Pushback recorded at §11 row 5.]

### D1c — encTargetP_card · `D1c_encCard.lean` (AUX)
statement: `theorem encTargetP_card (hp : 2 ≤ p) : Nat.card (EncTargetP p F P) ≤ P.Mfac * p ^ P.W`
moves_ref: (L11's codomain count ∏_r Q_r^{d_r}·m̄_r). deps: E2. sketch: Pi/product
cards; (card pool)^{d} ≤ (p^w)^d; regroup = p^W·Mfac. medium.

### D3a — D4R2' · `D3a_poolBound.lean`
statement: `theorem D4R2' : Nat.card (PrefIdx n pol P) ≤ P.Mfac * p ^ P.W`
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}" (D4R.2′ display; the M ≤ n^{|P̂|} clause is W2).
deps: E9, D1c. sketch: `Nat.card_le_card_of_injective encIdx encIdx_inj` + D1c.
easy. hypothesis_fields: NONE — the injection is PROVED (final-audit finding 4
repaired: nothing assumed, no rider).

### D3b — D4R2_cor · `D3b_corD4R2.lean`
statement: `theorem D4R2_cor (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : Nat.card S.event * p ^ (P.A' n) ≤ P.Mfac * p ^ (P.W + n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} ≤ M(P̂)·p^{W(P̂)−A(P̂)} = M(P̂)·p^{−A_net(P̂)},
A_net(P̂) := A(P̂) − W(P̂)" (Corollary D4R.2), division-free (`Anet` records the named
exponent). deps: D12, D3a, D2a. sketch: chain D4R1_EV with D4R2' (via CD_eq);
pow_add. easy.

### THE L9 CHAIN (D4a–D9, L9s) — substance unchanged from rev 2 (no final-audit
finding hit it except D10's quantifier); one lemma per unit; specs abbreviated.

### D4a — chart_bij · `D4a_chartBij.lean` (AUX) — as rev 2: `Injective J.coordOf` +
surjectivity onto the N×n grid (sorted chart + card pigeonhole via `J.hm`). medium.
### D4b — chart_count · `D4b_chartCount.lean` (AUX) — as rev 2: pulled-back predicate
counts over `Fin m` = grid filter counts. deps: D4a. medium.
### D5a — Dwidth_pos · `D5a_dwidthPos.lean` (AUX) — as rev 2 (root deg 1 + width
chain). deps: MovesC. medium.
### D6a — strFrame_shape · `D6a_strShape.lean` — `H.strFrame i = P.strS i` under
`MatchesHist`. easy.
### D5b — line_shape · `D5b_lineShape.lean` — `(H.nodes[r]'hr).line = P.lineS r`
under coherence + Matches (slope law; `hLineU` pins the intercept THROUGH u* — the
rev-9 bracket, quoted in the unit). deps: D5a, D6a. medium.
### D6b — kappaH_shape · easy. D6c — innerslot_shape · easy. D6d — htH_shape ·
deps D6b/D6c, easy. D6e — prevRim_shape · easy. (Files `D6*_*.lean`; moves_ref: L9's
"SHAPE data" sentence, one formula each.)
### D7a — staircase_shape · deps D5b. easy. D7b — floorH_shape · deps D7a (fold
congruence). medium. D7c — slotVal_shape · deps D5b (the fine-slot edge). easy.
### D8 — band_shape · `D8_bandShape.lean` — `inFreshBand H n J.coordOf r ν c ↔
P.bandS n r (J.coordOf c)` under Matches (+ J.coherent). deps: D6d, D6e, D7b, D7c.
medium.
### D9 — L9_A · `D9_L9.lean`
statement: `theorem L9_A (S : Presented p F n N m pol P) (i : PrefIdx n pol P) : totalPins (S.jet i) (topLocus p m) = P.A n N`
moves_ref: "∏ vol(E_fresh(νᵢ)) = p^{−A(P̂)} … the product depends on P̂ alone; A(P̂) :=
the resulting shape exponent" (L9). deps: D0b, D8, D4b, F1 (reprOf ∈ PrefSet gives
Matches/coherence); MovesC `mstar_eq`. sketch: as rev 2 (mstar_eq per read → band
count → grid filter → A's summand). medium.
### L9s — A_stable · `L9s_Astable.lean` (AUX)
informal: A(P̂, n, N) is N-stable above the shape height bound (the note's "a priori
shape bound … available but not needed" — HERE it IS needed, to make A′ N-free).
statement: `theorem A_stable (hN : P.Nshape ≤ N) : P.A n N = P.A' n`
deps: Defs. sketch: band coordinates satisfy ℓ ≤ htS ≤ line value ≤ intercept <
Nshape, so levels in [Nshape, N) contribute nothing; filter congruence on the grid
split. medium.

### THE MASS LAWS (final-audit finding 5: the uniform quantifier ∀ N ≥ N(P̂))

### D10 — D4R1_SUM · `D10_sumLaw.lean`
statement: `theorem D4R1_SUM (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : (∑ᶠ i : PrefIdx n pol P, Nat.card (S.fiber i)) * p ^ (P.A' n) = Nat.card (PrefIdx n pol P) * p ^ (n * N)`
moves_ref: "Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (D4R.1-SUM)" ≡ "N(P̂) is
finite, and for EVERY N ≥ N(P̂): Σ_η #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)}
(D4R.4-SUM)". THE QUANTIFIER [REV 5]: N and S universally bound at every
level where the ledger has stabilized — `hA : P.A n N = P.A' n`, DISCHARGED by L9s
whenever `Nshape ≤ N` and by `Threshold.hstab` from the note's own NP on (so
D4R4_all covers [N(P̂), Nshape) too); C and A′ are N-FREE, so all levels share their
constants — D4R.4's content. The uniform-threshold packaging is D4R4_all.
deps: D0b, D9, L9s, D2a (Fintype from Finite for ∑ᶠ). sketch: per summand
thmC_top + D9 + A_stable; sum the constant. NO disjointness consumed. medium.
hypothesis_fields: `S.jet` only.

### D11a — mult_sum · `D11a_multSum.lean` — as rev 2 on the new types:
`∑ x, S.mult x = ∑ᶠ i, Nat.card (S.fiber i)` (double counting). medium.
### D11b — event_iff_mult · `D11b_eventMult.lean` — `x ∈ S.event ↔ 1 ≤ S.mult x`.
easy.

### D12 — D4R1_EV · `D12_evBound.lean`
statement: `theorem D4R1_EV (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : Nat.card S.event * p ^ (P.A' n) ≤ Nat.card (PrefIdx n pol P) * p ^ (n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡ "(D4R.4-EV) …
the union bound within the level-N box", at every N ≥ N(P̂) (same quantifier note as
D10). deps: D10, D11a, D11b. sketch: card event = #{mult ≥ 1} ≤ Σ mult. medium.

### D13 — D4R1_EV_iff · `D13_evIff.lean`
statement: `theorem D4R1_EV_iff (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : (Nat.card S.event * p ^ (P.A' n) = Nat.card (PrefIdx n pol P) * p ^ (n * N)) ↔ (∀ x ∈ S.event, S.mult x = 1)`
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … count-equality ⟺ …
mult_P̂ ≡ 1 POINTWISE on the event — the finite-level statement carries no
measure-zero exception" (D4R.1/L12). deps: D10, D11a, D11b. sketch: cancel p^{A′}
(p ≥ 2); Finset double counting, pointwise. medium-hard.

[REV 4, Codex#2 finding 6, second half — CONCEDED: D10/D12/D13/D3b now carry
`hne : P.reads ≠ []`, so with `CD_eq` their constant IS the corpus C (`P.CD`) on
their whole domain, and the P̂ = ∅ display is carried ONLY by D14a — the note's own
two-mechanism proof ("The EMPTY prefix η = ∅ … is dispatched FIRST, separately from
Theorem C(b)"). First half PUSHED BACK — §11 row 6.]

### D4R4_all — the law at the NOTE's threshold · `D4R4all_wrapper.lean`
[REV 5, reconciliation (5) — Codex#3 finding 4; restated on `Threshold`]
statement:
  `theorem D4R4_all (hne : P.reads ≠ []) (T : Threshold p F n pol P) : ∀ N, T.NP ≤ N → (((∑ᶠ i, Nat.card ((T.jets N ‹_›).fiber i)) * p ^ (P.A' n) = P.CD n pol * p ^ (n * N)) ∧ (Nat.card (T.jets N ‹_›).event * p ^ (P.A' n) ≤ P.CD n pol * p ^ (n * N)))`
  `theorem TW_threshold_witness (hex : ∀ N, P.Nshape ≤ N → Nonempty (Presented p F n N (n*N) pol P)) : Nonempty (Threshold p F n pol P)`
moves_ref: L12 QUOTED VERBATIM: "N(P̂) is finite, and for EVERY N ≥ N(P̂):
Σ_{η ∈ Pref(P̂)} #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)} (D4R.4-SUM) …
#{f mod p^N ∈ S(P̂,⊤)} ≤ C_P̂(p)·p^{nN − A(P̂)} (D4R.4-EV)". MATCH: ∀ N ≥ NP (the
threshold DATA with its L12-visible properties), the SUM equality ∧ the EV bound,
constants CD and A′ N-free. The note quantifies over LEVELS only (its counts are
intrinsic — no ∃-over-presentations remains in the conclusion; presentation-
intrinsic-ness = ClassFiberWelldef, declared). `TW`: Nshape is the CONSTRUCTIVE
WITNESS (NP := Nshape, hstab := L9s, jets := hex via choice) — "Nshape ≥ N(P̂)"
materialized as witness-hood; PRESENT-EXIST (§2) is consumed HERE and only here.
deps: D10, D12, D2a (CD_eq), L9s; T.hstab bridges A n N to A′ below Nshape.
sketch: apply D10/D12 at T.jets N (their hN-argument replaced by T.hstab — D10/D12
generalize to any N with `P.A n N = P.A' n`, a one-line hypothesis swap noted in
their specs). easy-medium.
hypothesis_fields: `T : Threshold` (fields hstab/jets = the L12 threshold content,
HC-2); `hex` (PRESENT-EXIST) only in TW. Non-vacuity: T.jets carry `hnorm`
(PresentNorm), so truncated/junk-policy instantiations violate the field — the
"trivially satisfiable hex" instance is unbuildable.

### F3 — the ∅-representation BRIDGE · `F3_emptyBridge.lean`
[REV 5, reconciliation (3) — Codex#3 finding 5 ∧ Fable#3 C-6: the deviation is now
a THEOREM on the Option-level object, not a prose declaration]
statement:
  `theorem PrefOpt_empty (hP : P.reads = []) : PrefOpt n pol P = {Option.none}`
  `theorem PrefOpt_nonempty (hne : P.reads ≠ []) : PrefOpt n pol P = Option.some '' PrefSet n pol P`
  `theorem CD_correspondence : P.CD n pol = Nat.card (etaDataO P '' PrefOpt n pol P)`
moves_ref: "Pref(∅) = {∅}" (L12/D4R.1's dispatch) — now LITERAL: the Option-level
Pref of the empty shape IS the singleton of the empty chain, and the corpus C (`CD`)
equals the class count of `PrefOpt` UNIFORMLY (both branches machine-checked: ∅ —
image = {none}, card 1; nonempty — etaDataO ∘ some classes = the PrefIdx classes).
The consumed arithmetic (D14a's law, D10's constant via CD_eq) is thereby EQUIVALENT
to the note's ontology by theorem.
deps: Defs, D2a, F1. sketch: set ext + match unfolding; `Option.some` injective for
the card transport. easy.

### D14a — emptyShape_law · `D14a_emptyShape.lean` (final-audit finding 6)
[REV 5: `Pref_empty_shape`'s History-level display now sits UNDER the F3 bridge —
the Option-level `PrefOpt_empty` carries the note's "Pref(∅) = {∅}" literally; this
unit keeps the History-level honesty display + the mass law.]
statement:
  `theorem Pref_empty_shape (hP : P.reads = []) : PrefSet n pol P = ∅ ∧ P.CD n pol = 1`
  `theorem A'_nil (hP : P.reads = []) : ∀ n, P.A' n = 0`
  `theorem emptyShape_law (hm : m = n * N) (hN : 1 ≤ N) (hP : P.reads = []) : Nat.card (emptyFiber p m) * p ^ (P.A' n) = P.CD n pol * p ^ (n * N)`
moves_ref: "Pref(∅) = {∅} … its fiber is the FULL BOX, level-N count p^{nN} =
C_∅·p^{nN − A(∅)} (C_∅ = 1, A(∅) = 0), by L5's normalized full-box display — NOT by
Theorem C(b)". CONNECTED IN CORPUS VOCABULARY: `emptyFiber` IS the defined S(∅,⊤),
`P.CD` IS the corpus C (its `if` branch is the note's own definition-level dispatch
Pref(∅) = {∅} — the History type has no empty chain, which is WHY CD carries the
dispatch; `Pref_empty_shape` displays that the History-level set is empty, so 1 is
the η = ∅ class and nothing else), `P.A'` IS the corpus A. deps: Defs. sketch:
if_pos; card univ = p^m; empty sum. easy. hypothesis_fields: `hm`, `hN` explicit.

### D14b — D4R4_emptyPref · `D14b_emptyPref.lean`
statement: `theorem D4R4_emptyPref (hne : P.reads ≠ []) (hemp : IsEmpty (PrefIdx n pol P)) (hN : 1 ≤ N) (hm : m = n * N) (S : Presented p F n N m pol P) : S.event = ∅ ∧ P.CD n pol = 0 ∧ Nat.card S.event * p ^ (P.A' n) = P.CD n pol * p ^ (n * N)`
moves_ref: "If Pref(P̂) = ∅ then S(P̂,⊤) = … = ∅ and C_P̂(p) = 0, so for EVERY N ≥ 1:
#{f mod p^N ∈ ∅} = 0 = C_P̂(p)·p^{nN − A(P̂)}" (L12). deps: Defs, D2a. sketch: empty
iUnion over an empty index; CD_eq + Nat.card of an empty type. easy.
hypothesis_fields: `hN`, `hm` explicit (L12's N(P̂) := 1 convention).

### THE TREE UNITS (final-audit finding 7 + gap 8)

### T1a — tree_prefix_closed · `T1a_prefixClosed.lean`
statement: `theorem tree_prefix_closed (T : TreeModel p F n N m pol) : ∀ H H' x, H.IsPrefixOf H' → T.mem (some H') x → T.mem (some H) x` — plus the base `∀ H x, T.mem (some H) x → T.mem none x` (immediate from `root_mem`). [REV 5: Option carrier.]
moves_ref: "T_can(f) is prefix-closed — a tree" (L2) — now a THEOREM from the
generation laws, not a field. deps: Defs. sketch: downward induction along
`mem_snoc` (peel the last node; a prefix of a snoc is the history or a prefix of it).
medium.

### D15 — tree_bridge · `D15_tree.lean`
statement:
  `theorem mult_eq_tree (S) (T : TreeModel p F n N m pol) (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P) (x : Box p m) : S.mult x = Nat.card {i : PrefIdx n pol P // T.mem (some (reprOf i)) x}`
  `theorem event_iff_tree (S) (T) (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P) (x : Box p m) : x ∈ S.event ↔ ∃ i : PrefIdx n pol P, T.mem (some (reprOf i)) x`
moves_ref: "mult_P̂(f) := #{ η ∈ Pref(P̂) : η ∈ T_can(f) } … S(P̂,⊤) = {f : mult_P̂(f)
≥ 1}" (L6 corollary). `hcyl` is the PINNED, EXPLICITLY DEFERRED L6 obligation (§2
ledger; wave-4/HC-2 owns its proof) — a named theorem hypothesis, NOT a structure
field restated as a theorem (final-audit finding 7). deps: Defs, D11b. sketch:
rewrite fibers along hcyl; `Nat.card_congr`. easy.
[REV 4, Codex#2 finding 9 — the per-representative scope: the second pinned Prop
**ClassFiberWelldef** (§2 ledger — one η-class, one classifier locus, over ALL
representatives and jets; §C L4's semantic content) is DECLARED alongside D4R_CYL;
together they restore the note's every-η reading of (D4R-CYL). Both deferred to the
wave-4/HC-2 tree corpus; D15 stays exact about the constructed enumeration.]

## 5. Perimeter (mirror of §D4-R.5 — unchanged from rev 2 except as noted)

No p-polynomiality of C ([1v]); no catalogue/aggregation ([2a]/[2b] — the events are
a multiplicity-weighted COVER, consumer duty in Defs docstrings); no resummation/
drainage/termination ([3]/[5]); no L7 unit (VerdictModel carries the typed object for
MovesT); no D4-n3 re-derivation; the literal (3i) not stated (D3a+W2 is the
M-carrying D4R.2′). NEW: the representative caveat (§3.2, displayed) — per-class
fibers are the chosen representative's SHZ; class-independence is HC-2 semantic
content. `Nshape ≥ N(η,⊤)`-adequacy of the presentations is existence-side (HC-2).

## 6. Build order

  wave A (parallel): D0a, E1, E2, E4, D5a, D6a, D6c, D6e, D14a → D0b, E3, E5, D0c.
  wave B: E6 → E7, E8 → E9; D2a, F1 → D3a, D1c; W1 → W2.
  wave C: D5b → D6b, D6d, D7a, D7c → D7b → D4a → D4b → D8 → D9; L9s.
  wave D: D10 → D11a, D11b → D12 → D13 → D3b (Corollary D4R.2, as rev 2 §D3b with
    A′); D14b; T1a; D15.
  Hardest: E6/E8 (polynomial arithmetic over the frame field), D13, D4a, T1a.

## 7. Codex-audit checklist (gate A)

1. ShapeRead retains rev-9 L3 exactly (heights PAIRED; `monicTop` is the slot-set
   datum reduced per §0.5 — reject if that reduction misreads L3).
2. No disjointness anywhere; sums over the INDEX type (rev-6 F1).
3. `D4R_CYL` consumed only as a named deferred hypothesis; no unit proves or assumes
   it as a field. Kernel (a)/(b) cited as MATH-discharged only; (c)/VP only in
   `VerdictModel`.
4. The EV criterion pointwise-on-the-event; the level quantifier via
   `hA : P.A n N = P.A' n` (discharged by L9s at N ≥ Nshape, by `Threshold.hstab`
   at N ≥ NP) and the note-threshold form at D4R4_all — present on
   D10/D12/D13 with N-free C and A′.
5. `ShapePrefix.A`/`A'`/`CD` are DEFINITIONS; `CD`'s if-branch is the note's own
   Pref(∅) = {∅} dispatch — reject any unit weakening it to a hypothesis.
6. The encoding chain E1–E9 must consume ONLY MovesC node Props + Matches — any new
   assumption there is a statement-fence breach.
7. `Presented.jet` is the ONLY assumed structure field in the corpus.

## 8. MANIFEST stub

corpus: MovesD · source: §D4-R rev 9 (DUAL-ACCEPTED 2026-07-27) · consumes: MovesC ·
units: 46 (D0a–c; E1–E9; D1c; D2a; F1; F3; W1–W3; D3a–b; D4a–b; D5a–b; D6a–e; D7a–c;
D8; D9; L9s; D10; D4R4_all(+TW); D11a–b; D12; D13; D14a–b; T1a; D15; 13 AUX) · defs: 1 file ·
open surface: `pol : CanonPolicy` (parameter), `Presented.jet` (HC-2), `D4R_CYL`
(deferred pinned Prop), `TreeModel`/`VerdictModel` data + laws, `Matches.hmonic`
(scoped, §0.5), explicit `hN`/`hm` on the empty units — §2 ledger.

## 9. REV 2 findings→repairs table (first audit, `MOVESD_AUDIT_CODEX_2026-07-28.md`)

[Kept for the record; several REV-2 repairs are SUPERSEDED by REV 3 — see §10.]
1 empty-family vacuity → PrefSet + complete/hcanon fields (superseded: rev 3
constructs the enumeration outright). 2 enc untied → encOf on actual data + henc
field (superseded: rev 3 PROVES the injection, E1–E9). 3 M ≤ n^{|P̂|} dropped →
restored with `hn` rider (superseded: rev 3 proves it, W1/W2). 4 A undefined →
`ShapePrefix.A` defined; D9 = L9 theorem; hA gone. 5 empty shape mis-modeled →
`hne` + connected display (extended at rev 3: corpus-level CD/emptyFiber). 6 N = 0
leak → explicit hN/hm. 7 TreeModel degenerate → mem_realizable + D0c (extended at
rev 3: child relation + generation laws). 8 VerdictModel vacuous → typed fields
(extended at rev 3: halt dichotomy + cap law). 9 chart unit hidden multi-lemma →
split D4a/D4b. 10 D6/D7 bundles → one lemma per unit.

## 10. REV 3 findings→repairs table (final audit, `MOVESD_AUDIT_CODEX_FINAL_2026-07-28.md`)

| # | finding (short) | repair |
|---|---|---|
| 1 | `offSlots_forced` invented (off-slot ≡ 1 not in the note) | ADJUDICATED §0.5: route (i) holds everywhere except the root monic lead, which the note itself displays (§D4-R.6 "slot 3 = the monic lead, digit 1"); blanket clause DELETED; `slots` → per-read Boolean `monicTop` with the ONE scoped tie `monicTop → sideDigit(ℓ) = 1`; d_r := ℓ_r + (monicTop ? 0 : 1) reproduces the note's d-counts |
| 2 | `Canon` lawless; `False` kills PrefSet | `CanonPolicy` structure: `liftOf` a FUNCTION of node data (L1's determinism), `blind` to the lift field; `IsCanon` per-node ⟹ prefix-monotone (T1a-style, free) and total on lift-assignments; `fun _ => False` is not an `IsCanon pol` for any pol; the open content is exactly WHICH pol (offset-P, §B2-DEF/HC-1) |
| 3 | family fields (`complete`, `henc`) assume what L8/L11 prove; no construction | the family is CONSTRUCTED: `PrefIdx := ↥(etaData '' PrefSet)` (the note's η-granularity: digits + ψ-images; lifts policy-determined per L1), `reprOf` classical, F1 proves the enumeration laws; L8 structural (D2a); L11's injection PROVED (E1–E9: pool identification, deg R_anch = ℓ, g·μ ≤ ℓ, eligible count ≤ m̄, rank injectivity); sole assumed field: `Presented.jet` (HC-2) |
| 4 | D3a consumes `henc` (assumed L11) + `hn` rider on the coarse bound | D4R2′ now PROVED with NO hypothesis (E9 + D1c); `hn` DELETED — W1 proves ℓ_r ≤ n for every member from `InBox` (the degree-n box clause of PrefSet) + the coherence window chain + E5; W2 gives M ≤ n^{|P̂|} from the proved `Wellformed` |
| 5 | one fixed N; no ∀ N ≥ N(P̂); no cross-level compatibility | D10/D12/D13 quantify `(N) (hN : Nshape P ≤ N) (S : Presented … N …)`; `Nshape` DEFINED (the note's "a priori shape bound"); C := Nat.card PrefIdx and A′ := A n Nshape are N-FREE, so constants agree across levels; L9s proves A-stability |
| 6 | empty-shape law a bare box identity, disconnected from Pref/C/S(∅,⊤) | corpus vocabulary supplied: `emptyFiber` (= S(∅,⊤), §C's empty-history clause), `ShapePrefix.CD` (C with the note's own Pref(∅) = {∅} dispatch at definition level), `Pref_empty_shape` (the History-level set is empty — so CD's 1 is exactly the η = ∅ class), `A'_nil`; D14a states the law on THESE |
| 7 | D15 restates the assumed `cyl` field as a theorem | `cyl` field DELETED; `D4R_CYL S T` is a PINNED Prop (def), EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus (§2 ledger); D15's bridges consume it as a named hypothesis |
| 8 | TreeModel lacks T_can structure (children, maximality) | `child : Option (History) → Node → Box → Prop` (none = root children) + generation laws `mem_single`/`mem_snoc`; prefix-closure now a THEOREM (T1a); maximal branch DEFINABLE (mem ∧ no child) and consumed by VerdictModel's dichotomy; eligibility semantics = kernel-(b), HC-2 (documented) |
| 9 | cap/τ law missing; `leaf := False` satisfiable | `leaf` field deleted (leaf := mem ∧ vdict ≠ none, DEFINED); `halt_iff` = L2's "NO children iff terminal verdict" (both directions); `cap : V → ℕ` with `cap_law`: a class-v verdict is determined by digits below level cap v (the uniform per-class detection cap, typed against vdict via `levelOf`); τ-as-cell-data remains MovesT's VP |

## 11. REV 4 adjudication table (Codex FINAL#2 8/2 vs Fable#2 1/1 — evidence-triaged)

| # | finding (verdict) | adjudication | disposition |
|---|---|---|---|
| F-C1 = C-2 | η-granularity: Fable#2 C1 (ambient etaData SPLITS one η by the residue-root choice — gate numbers C = 6 vs sealed 3, mult ≡ 2 vs 1) vs Codex 2 (classes might MERGE distinct η's; injectivity unproved) | Fable's direction gate-evidenced and verified (the note's η has no root datum — L2's child data quoted). Codex 2's merge direction: with root-normalized classes the per-read embedding is canonical by induction (§0.6), so abstract-η ⟺ image data; the residual two-sided dictionary is ONE declared pin | **FIXED** (Fable's route): `canonRoot` + `IsCanonPres` (§3.2), PrefSet root-normalized; PRESENT-NORM declared (§2); MANDATORY gate check §0.6 re-derives C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1, plus Nshape = 5, A = 11, W = 7, M = 1 |
| F-G1 ≈ C-3 | `EligibleImage` gloss omits irreducibility/subfield (Fable: gloss FALSE both ways, counterexamples; Codex: irreducibility transport invalid) | both verifiers right about the GLOSS; the intended transported predicate (E7's own deps line) is sound — Fable verified the chain with it | **FIXED**: explicit `RanchImage`/`ψImage`/`poolSubfield`/`EligibleImage` Defs (§3.4 — irreducible OVER THE POOL SUBFIELD via the ∃-lift clause, never over F); E7/E8 restated and re-verified |
| C-1 | monicTop reduction unsupported; Boolean unconstrained | Fable#2 §3.2 accepted §0.5 with the gate numbers (d₀ = 3, d₁ = 2, W = 7 ✓); my re-check: side slots map into the box except at most the single degree-n slot, which exists only at the ROOT full span ("slot 3 = the monic lead, digit 1", §D4-R.6); junk `monicTop` shapes constrain their OWN PrefSet coherently (smaller W, pinned digit — the encoding stays injective) | **PUSHBACK + partial concession**: root-species guard `hmonicRoot` added to `ShapeRead`; the Boolean stays (at most ONE off-box slot exists, so a Boolean is exact) |
| C-4 | CanonPolicy lawless (constant liftOf; junk normalization; no pinning) | Fable#2 §3.3 verified: `False` inexpressible, `blind` kills the real attack, liftOf-as-function IS L1's determinism ("the digits t_k are FUNCTIONS of the node data … deterministic"); WHICH policy is §B2-DEF/HC-1's by the campaign DAG — encoding offset-P laws here would formalize (S6b) out of scope; adversarial pol = junk data, no consumer | **PUSHBACK**: POL-PIN named in §2 (the future HC-1 instance unit); junk-lift normalization already documented |
| C-5 | Mfac_le conditional; Wellformed unenforced; false for junk shapes | correct that the BARE M ≤ n^{|P̂|} fails on junk data (ℓ_r > n) — but the note's "always" ranges over degree-n classifier shapes; on C-carrying territory the display can be made hypothesis-free | **FIXED**: W3 `D4R2'_coarse` — `C ≤ n^{|P̂|}·p^W` UNCONDITIONAL (empty case + W1/W2 via a member); Mfac_le keeps `Wellformed`, discharged by W1 whenever a member exists; bare-junk case pushed back |
| C-6 | empty ontology: "Pref_empty_shape gives the wrong set"; mass laws lack `hne` and yield a vacuous zero law at ∅ | FIRST half — Fable#2 §3.5 verified the D14a decomposition faithful ("mirrors the note's own two-mechanism proof"; the History type HAS no empty chain — CD's if-branch IS the note's definition-level dispatch, `Pref_empty_shape` honestly displays it); SECOND half — correct: D10-at-∅ read `Nat.card PrefIdx = 0` where the note's C_∅ = 1 | **half PUSHBACK / half FIXED**: `hne` added to D10/D12/D13/D3b (their constant now = `P.CD` via CD_eq on their whole domain); P̂ = ∅ carried ONLY by D14a |
| C-7 | no Presented witness at any/every N; Nshape-domination unproved | genuine: JetSetup existence IS the HC-2 boundary (MovesC's declared honest boundary — D0c gives fiber nonemptiness GIVEN a jet, not a jet); the note's unconditional quantifier rests on §C C.2 presentability | **FIXED (honest-hypothesis route)**: PRESENT-EXIST declared (§2) + wrapper unit `D4R4_all` — ∀ N ≥ Nshape ∃ witness S with SUM+EV, under `hex`; Nshape-domination documented (in-box levels are automatic — the note's own remark) |
| C-8 | TreeModel admits mem := False; no root inhabitation / exhaustive children | falsifying computation DISPLAYED at §3.4: the empty tree fails `D4R_CYL` against D0c's nonempty fibers — no consumer accepts it; root-inhabitation would be UNFAITHFUL (L5 (ns): ∅ can be a leaf — quoted); exhaustive children = kernel-(b) cell content behind the pins | **PUSHBACK** (with the displayed construction) |
| C-9 | D4R_CYL covers representatives only; representative-independence missing | correct as a scope gap | **FIXED**: ClassFiberWelldef pinned (§2) + D15 spec cites both pins |
| C-10 | VerdictModel: no vdict↔cell tie, no levelOf↔chart link | partially correct: full cell tie needs frames (MovesT); a finite-level locality law and chart-range consistency are expressible here | **FIXED (partial, typed)**: `vdict_local` (vdict a function of the digits below the cap envelope — the finite-level shadow of "τ is a function of CELL data, never of f") + `levelOf_lt`; the cell-exact tie documented as MovesT's VP duty |

Unit count at rev 4: 45; at rev 5: 46 (+F3). AUX still 13. Gate acceptance test
(per the triage protocol): §0.6 — C_P̂*(2) = 3 ✓, C_P̂*(3) = 48 ✓, mult_P̂* ≡ 1 ✓,
Nshape(P̂*) = 5 ✓, A(P̂*) = 11 ✓, W = 7 ✓, M = 1 ✓.

## 12. REV 5 reconciliation table (Fable#3 ACCEPT 0/0 vs Codex FINAL#3 REJECT 7/1 — orchestrator-adjudicated designs)

| # | dispute (who held what) | the reconciling design (both readings satisfied) |
|---|---|---|
| 1 | TreeModel root: Codex f.6 "the empty root ALWAYS exists" (L2: "its root is the empty chain ∅") vs Fable C-8 upheld "root-inhabitation on nonempty History would be unfaithful (L5 (ns): ∅ can be a leaf)" — BOTH RIGHT | node carrier = `Option (History)`: `root_mem : ∀ x, mem none x` is a LAW (Codex's reading); NO law forces `some`-chains (Fable's (ns) computation stands); `mem_single`/`mem_snoc`/`D4R_CYL`/T1a/D15 requantified on `some`; VerdictModel stays on nonempty chains (∅-verdict = MovesT's VP-2 root corner, documented) |
| 2 | PresentNorm: Codex f.3 "prose pin, PrefIdx may truncate Pref" vs Fable OBS-1 (same recommendation, non-blocking) | `PresentNorm n pol P` TYPED (§3.2): totality from the POLICY-FREE `PrefSetAny` + Galois uniqueness; carried as the FIELD `Presented.hnorm` — the empty-PrefIdx-vs-nonempty-Pref instance VIOLATES it, and every mass unit consumes it through S |
| 3 | ∅ representation: Codex f.5 "Pref_empty_shape states the wrong set" vs Fable C-6 upheld "the History type has no empty chain; CD's if-branch IS the note's dispatch" | the deviation is now a THEOREM (F3, on the new Option-level `PrefOpt`): `PrefOpt_empty : PrefOpt = {none}` = the note's "Pref(∅) = {∅}" LITERALLY; `CD_correspondence` machine-checks the consumed arithmetic equivalence; D14a keeps the History-level honesty display |
| 4 | monicTop: Codex f.1 "Boolean unfaithful to L3's slot sets; junk root shapes shrink W" vs Fable C-1 upheld (L11 reconstruction + at most one off-box slot + gate d-counts) | Boolean + root guard STAND (Fable), PLUS the definitional tie `ShapePrefix.MonicTie` (monicTop ⟺ root ∧ s0+wSide = n) as a PrefSet clause — faking/hiding monicTop voids the shape's PrefSet (Codex's instance unbuildable on C-carrying territory) |
| 5 | D4R4_all: Codex f.4 "starts at Nshape not N(P̂); ∃-S conclusion; hex trivially satisfiable" vs Fable §5 PASS (documented boundary, note licenses the shape bound) | `Threshold` structure = the note's NP with its L12-VISIBLE properties (`hstab`, `jets`); D4R4_all restated ∀ N ≥ NP with NO ∃-over-presentations in the conclusion (L12 quantifies over LEVELS only — quoted verbatim in the spec); D10/D12/D13/D3b generalized to `hA : P.A n N = P.A' n` (covers [N(P̂), Nshape)); `TW_threshold_witness`: Nshape = the constructive witness under PRESENT-EXIST; hnorm kills the trivial-hex instance |
| 6 | CanonPolicy: Codex f.2 "junk pol can void the corpus; POL-PIN not a hypothesis" vs Fable C-4 upheld (L1 verbatim; ∀-pol sound; DAG ownership) | parameter design STANDS (Fable) + the note-supported adequacy is now INSIDE `PresentNorm`'s totality clause (source set = policy-FREE `PrefSetAny`): a history-voiding policy violates `Presented.hnorm` — vacuity killed WITHOUT pinning offset-P (POL-PIN stays HC-1) |
| 7 | ClassFiberWelldef: Codex f.7 "not shown, not a hypothesis" | displayed as a Defs Prop (§3.4) and WIRED: D15's two theorems carry `hwd : ClassFiberWelldef …` explicitly |
| 8 | VerdictModel cells: Codex f.8 (GAP) "no digit-cell factorization" — acknowledged by both as the declared MovesT boundary | stays the honest deferral: `vdict_local`/`levelOf_lt`/`cap_law` are the interface-expressible shadow; the cell-exact tie is VP-2/MovesT's, stated in the structure docstring — no silent claim |

Gate acceptance (unchanged from §0.6, re-affirmed by BOTH rev-4 verdicts'
independent recomputations): C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1, Nshape = 5,
A = 11, W = 7, M = 1.

codex
1. **CRITICAL — `MonicTie` still creates a vacuous malformed-shape instance.**

   Offending specs:

   > `def ShapePrefix.MonicTie ...`

   > `def PrefSet ... := {H | ... P.MonicTie n ∧ pol.IsCanonPres H}`

   > “A junk shape ... violates MonicTie and voids its own PrefSet.”

   The note makes the retained slot sets part of what a shape-prefix *is*. A malformed monic-slot encoding is therefore not a valid shape-prefix; it cannot be converted into a valid shape having `Pref(P̂)=∅`. Here the law is only a predicate inside both `PrefSet` and `PrefSetAny`. If it fails, both sets are empty, `PresentNorm` is vacuous, `PrefIdx` is empty, and `Presented` is inhabited by its empty `jet` function. Thus the advertised “voids its own PrefSet” mechanism is precisely the prohibited degenerate-instance escape. Reconciliation (4) does not discharge the original finding.

2. **CRITICAL — policy adequacy is not wired into the L8/L11/pool-bound units.**

   Offending unit specs:

   > **D2a:** `instance : Finite (PrefIdx n pol P)`

   > **F1:** `theorem card_classes : Nat.card (PrefIdx n pol P) = Nat.card (etaData P '' PrefSet n pol P)`

   > **E9:** `theorem encIdx_inj : Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F P)`

   > **D3a:** `theorem D4R2' : Nat.card (PrefIdx n pol P) ≤ P.Mfac * p ^ P.W`

   > **W3:** `theorem D4R2'_coarse : Nat.card (PrefIdx n pol P) ≤ n ^ P.reads.length * p ^ P.W`

   These statements quantify over an arbitrary `pol` and do not assume `PresentNorm`, `Presented`, or POL-PIN. A policy whose prescribed lifts admit no matching history makes `PrefIdx` empty, so L8/L11/D4R.2′ become trivial statements about `0`, even when the policy-free note-prefix set is nonempty. Adding `Presented.hnorm` repairs mass-law units carrying `S`, but not these standalone units. They are weaker than the quoted displays about the note’s fixed offset-P canonical policy. Reconciliations (2) and (6) are therefore incomplete.

3. **CRITICAL — the standalone factor bound from L11 remains weakened.**

   Offending specs:

   > **W2:** `theorem Mfac_le (hwf : P.Wellformed n) : P.Mfac ≤ n ^ P.reads.length`

   > **W3:** `theorem D4R2'_coarse : Nat.card (PrefIdx n pol P) ≤ n ^ P.reads.length * p ^ P.W`

   The note displays both

   `C_P̂(p) ≤ M(P̂)·p^{W(P̂)}` and `M(P̂) ≤ n^{|P̂|}`

   for a shape-prefix of the degree-`n` classifier. W2 adds an external `Wellformed` hypothesis, while W3 replaces the missing `M` statement by a bound only on `C`. This is not equivalent, especially for a valid but unrealizable shape with `C=0`: the note still asserts the shape-side `M` bound. Degree-`n` wellformedness belongs in the shape type or its universally consumed validity structure, not only in an inhabitation argument.

4. **CRITICAL — `Threshold.NP` is not definitionally the note’s `N(P̂)`.**

   Offending specs:

   > `structure Threshold ... where`
   >
   > `NP : ℕ`
   >
   > `hstab : ∀ N, NP ≤ N → P.A n N = P.A' n`
   >
   > `jets : ∀ N, NP ≤ N → Presented ...`

   > **D4R4_all:** `∀ N, T.NP ≤ N → ...`

   > **TW:** “`NP := Nshape`”

   L12 defines `N(P̂)` by the maximum of the individual `N(η,⊤)`, with the explicit empty-set convention. The proposed fields neither state that maximum nor characterize the individual cutoffs. Any larger sufficient `NP` satisfies them, so `D4R4_all` proves the laws only on the smaller range `N ≥ NP`, omitting possible levels `N(P̂) ≤ N < NP`. `TW` merely constructs the advertised a priori shape upper bound. Reconciliation (5) therefore remains weaker than the exact quantifier in D4R.4.

5. **GAP — `VerdictModel` still omits two pieces of its claimed kernel interface.**

   Offending spec:

   > “`vdict` stays on NONEMPTY chains; the ∅-root’s own (ns) verdict is MovesT’s corner ... documented not modeled.”

   > “The cell-exact tie ... is MovesT’s VP duty — documented, not silently claimed.”

   Documentation makes the deferral honest, but the ledger calls `VerdictModel` the typed surface for the verdict alphabet, halting rule, and cell-data detection kernel. Root `(ns)` verdicts and exact factorization through the digit cell are absent fields. This remains an underspecified Defs dependency, though nothing in MovesD currently consumes it.

6. **GAP — the displayed Defs skeleton is not order-correct Lean.**

   Offending specifications include:

   > `EtaGalEq ... (d d' : EtaData F P)` before `EtaData` is defined.

   > `PresentNorm ... PrefIdx ...` before `PrefIdx` is defined.

   > `Threshold.hstab ... P.A ... P.A'` before §3.3 defines `A` and `A'`.

   The note about actual-file ordering mentions only `RanchImage`/`ψImage` preceding `canonRoot`; it does not resolve these additional forward references. Reordering appears possible, but the proposed skeleton as written is not Lean 4 code.

7. **GAP — several unit specs have no auditable `statement` field.**

   Offending units include:

   > **D0a:** “as rev 2 (sol/numPinned/admissible)”

   > **D0b:** “as rev 2 (`totalPins_top`, `thmC_top`)”

   > **D4a/D4b/D5a:** “as rev 2”

   > **D6b–D6e:** names such as “`kappaH_shape · easy`” without full statements

   > **D7a–D7c:** dependency summaries without quantified statements

   Because the referenced rev-2 specifications are not part of this blueprint, their quantifiers, side conditions, empty cases, and decomposition cannot be checked against the frozen note in this pass.

Counts: **4 critical / 3 gaps**

**REJECT (4 crit / 3 gap)**
tokens used
80,500
1. **CRITICAL — `MonicTie` still creates a vacuous malformed-shape instance.**

   Offending specs:

   > `def ShapePrefix.MonicTie ...`

   > `def PrefSet ... := {H | ... P.MonicTie n ∧ pol.IsCanonPres H}`

   > “A junk shape ... violates MonicTie and voids its own PrefSet.”

   The note makes the retained slot sets part of what a shape-prefix *is*. A malformed monic-slot encoding is therefore not a valid shape-prefix; it cannot be converted into a valid shape having `Pref(P̂)=∅`. Here the law is only a predicate inside both `PrefSet` and `PrefSetAny`. If it fails, both sets are empty, `PresentNorm` is vacuous, `PrefIdx` is empty, and `Presented` is inhabited by its empty `jet` function. Thus the advertised “voids its own PrefSet” mechanism is precisely the prohibited degenerate-instance escape. Reconciliation (4) does not discharge the original finding.

2. **CRITICAL — policy adequacy is not wired into the L8/L11/pool-bound units.**

   Offending unit specs:

   > **D2a:** `instance : Finite (PrefIdx n pol P)`

   > **F1:** `theorem card_classes : Nat.card (PrefIdx n pol P) = Nat.card (etaData P '' PrefSet n pol P)`

   > **E9:** `theorem encIdx_inj : Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F P)`

   > **D3a:** `theorem D4R2' : Nat.card (PrefIdx n pol P) ≤ P.Mfac * p ^ P.W`

   > **W3:** `theorem D4R2'_coarse : Nat.card (PrefIdx n pol P) ≤ n ^ P.reads.length * p ^ P.W`

   These statements quantify over an arbitrary `pol` and do not assume `PresentNorm`, `Presented`, or POL-PIN. A policy whose prescribed lifts admit no matching history makes `PrefIdx` empty, so L8/L11/D4R.2′ become trivial statements about `0`, even when the policy-free note-prefix set is nonempty. Adding `Presented.hnorm` repairs mass-law units carrying `S`, but not these standalone units. They are weaker than the quoted displays about the note’s fixed offset-P canonical policy. Reconciliations (2) and (6) are therefore incomplete.

3. **CRITICAL — the standalone factor bound from L11 remains weakened.**

   Offending specs:

   > **W2:** `theorem Mfac_le (hwf : P.Wellformed n) : P.Mfac ≤ n ^ P.reads.length`

   > **W3:** `theorem D4R2'_coarse : Nat.card (PrefIdx n pol P) ≤ n ^ P.reads.length * p ^ P.W`

   The note displays both

   `C_P̂(p) ≤ M(P̂)·p^{W(P̂)}` and `M(P̂) ≤ n^{|P̂|}`

   for a shape-prefix of the degree-`n` classifier. W2 adds an external `Wellformed` hypothesis, while W3 replaces the missing `M` statement by a bound only on `C`. This is not equivalent, especially for a valid but unrealizable shape with `C=0`: the note still asserts the shape-side `M` bound. Degree-`n` wellformedness belongs in the shape type or its universally consumed validity structure, not only in an inhabitation argument.

4. **CRITICAL — `Threshold.NP` is not definitionally the note’s `N(P̂)`.**

   Offending specs:

   > `structure Threshold ... where`
   >
   > `NP : ℕ`
   >
   > `hstab : ∀ N, NP ≤ N → P.A n N = P.A' n`
   >
   > `jets : ∀ N, NP ≤ N → Presented ...`

   > **D4R4_all:** `∀ N, T.NP ≤ N → ...`

   > **TW:** “`NP := Nshape`”

   L12 defines `N(P̂)` by the maximum of the individual `N(η,⊤)`, with the explicit empty-set convention. The proposed fields neither state that maximum nor characterize the individual cutoffs. Any larger sufficient `NP` satisfies them, so `D4R4_all` proves the laws only on the smaller range `N ≥ NP`, omitting possible levels `N(P̂) ≤ N < NP`. `TW` merely constructs the advertised a priori shape upper bound. Reconciliation (5) therefore remains weaker than the exact quantifier in D4R.4.

5. **GAP — `VerdictModel` still omits two pieces of its claimed kernel interface.**

   Offending spec:

   > “`vdict` stays on NONEMPTY chains; the ∅-root’s own (ns) verdict is MovesT’s corner ... documented not modeled.”

   > “The cell-exact tie ... is MovesT’s VP duty — documented, not silently claimed.”

   Documentation makes the deferral honest, but the ledger calls `VerdictModel` the typed surface for the verdict alphabet, halting rule, and cell-data detection kernel. Root `(ns)` verdicts and exact factorization through the digit cell are absent fields. This remains an underspecified Defs dependency, though nothing in MovesD currently consumes it.

6. **GAP — the displayed Defs skeleton is not order-correct Lean.**

   Offending specifications include:

   > `EtaGalEq ... (d d' : EtaData F P)` before `EtaData` is defined.

   > `PresentNorm ... PrefIdx ...` before `PrefIdx` is defined.

   > `Threshold.hstab ... P.A ... P.A'` before §3.3 defines `A` and `A'`.

   The note about actual-file ordering mentions only `RanchImage`/`ψImage` preceding `canonRoot`; it does not resolve these additional forward references. Reordering appears possible, but the proposed skeleton as written is not Lean 4 code.

7. **GAP — several unit specs have no auditable `statement` field.**

   Offending units include:

   > **D0a:** “as rev 2 (sol/numPinned/admissible)”

   > **D0b:** “as rev 2 (`totalPins_top`, `thmC_top`)”

   > **D4a/D4b/D5a:** “as rev 2”

   > **D6b–D6e:** names such as “`kappaH_shape · easy`” without full statements

   > **D7a–D7c:** dependency summaries without quantified statements

   Because the referenced rev-2 specifications are not part of this blueprint, their quantifiers, side conditions, empty cases, and decomposition cannot be checked against the frozen note in this pass.

Counts: **4 critical / 3 gaps**

**REJECT (4 crit / 3 gap)**
