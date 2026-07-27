# MovesSp §M-SPECIES final confirmation pass (rev 5, third/closing pass) — Codex verdict
2026-07-27. Verdict: ACCEPT (0 CRITICAL / 0 GAP). Full transcript below (codex exec, sandbox danger-full-access).
OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa448-d1a5-7d52-8686-70827508a12c
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

THIRD final pass, on REV 5 — the CLOSING rev. History: your rev-4 verdict was 1/1 (all adjudications checked out): the critical was the len-0 vacuity path at n=1; the gap was thresholdData's bundling; the independent auditor added one quantifier gap (succ_terminal). Rev 5: hN1 : n = 1 → ∀ η, 0 < len η + the new Sp.n1Branch unit (len = 1 ∧ datum = confirmingRoot1, the note's "single root letter" display quoted; len 0 stays real at n ≥ 2 per (τ-hen)); thresholdData split into 6 one-display units; succ_terminal gains hs : InCatalogue. VERIFY the three repairs (does hN1 + n1Branch genuinely kill the all-len-0 model while preserving the note's n ≥ 2 len-0 case?) and sweep end to end one last time. A clean pass = ACCEPTED for formalization.


THE FROZEN NOTE:
## §M-SPECIES — the finite branch-shape catalogue (assembly note 2, = plan [2a])

*(2026-07-27. Assembly note [2a] per ASSEMBLY_PLAN_2026-07-26.md §3, drafted in
its branch-aware COUNT-FREE form (plan pass-7 clearance, re-confirmed at pass 8
on the rev-8 restatement). Consumes: the dual-accepted §B2-DEF (the move engine
— D.4 (I-aug), D.5 (standard lift), D.7 (TRANS), D.8 (increment landing), D.10
(recentering/RS-landing), D.11 (per-move ledger)), §D4-R (the canonical branch
tree T_can(f), the L3 object dictionary; rev 9, DUAL-ACCEPTED 2026-07-27 —
Codex pass 11 + Fable confirm CLEAN), and
the plan's §1s/§2/§2v/§3 notation. Everything in this note is SYNTAX: no
residue field is evaluated, no mass is computed, no count is assigned.
Inherited conditionality, displayed where consumed [rev 3]: kernel D4R.0-K
parts (a) totality and (b) structural exhaustiveness are DISCHARGED
(D4R0K_DERIVATION rev 3, dual-verified 2026-07-27); the residual is part
(c) — the verdict pin, owned by [3t] via VP — and the completeness theorem
SP-COMP is conditional on exactly that residual (§C's (SAE)
repair, this note's second draft condition, is DISCHARGED by §C's rev-14
dual acceptance, 2026-07-27); the finiteness
theorem SP-FIN and the menu construction SP-OUT are unconditional bookkeeping
over the accepted §B2-DEF vocabulary. DELIVERY under the plan's [2a]/[2b]
split: Theorem MENU's FINITENESS and COMPLETENESS clauses, in per-read form;
the parameter-geometry and state-type clauses (M2, M4a, M4a-X, M4b/M4b-T) are
[2b]'s and are nowhere anticipated here.)*

**What this note is.** The raw catalogue 𝒮_n^raw of read SPECIES: a finite,
p-independent ALPHABET in which every branch of every canonical tree T_can(f)
spells its shape, one letter per read (through its CATALOGUE WORD — the
reads through the first confirming W = 1 read; SP-COMP's quantifier, rev 3;
the confirming read sits BELOW VP's halt — (τ-irr) at n ≥ 2, (τ-hen) at
n = 1, where the halt precedes every read — and consumers' τ-WORDS
stop one letter earlier, at the halt — SP.4's HALT CONVENTION, rev 4;
n = 1 clause at rev 5).
A species is read off ONE chain of
T_can(f) — a §C single-branch history in its own frame (§D4-R L2/L3) — NEVER
off f: this is F1's discipline (one f carries several chains, of equal or
different shapes; nothing here quantifies over "the" run of f, which does not
exist). The catalogue assigns NO counts and NO masses: shape events over the
box are a multiplicity-weighted COVER (Σ_P̂ μ(P̂) may exceed 1 — §D4-R's
consumer duty), and every counting duty routed through this catalogue is owned
elsewhere: the per-shape sum/event laws by [1] (D4R.1-SUM/-EV, D4R.4-SUM/-EV),
the tree-assembly conversion to f-level masses by [3] RS.1, the per-cell value
counts by [1v]'s tables. [2a] is the index set, never the measure.

### SP.1 The species datum (value-free, height-free, per read)

Fix n. A READ of a chain η ∈ T_can(f) (§D4-R L2) consumes one side of the
current window polygon in the chain's own frame Ψ_η (§D4-R L4) and either
descends — an increment or a recentering, §B2-DEF D.8/D.10 — or is terminal
(⊥; the leaf's verdict is V_term data, SP.4 — rev-3 typing). Its SPECIES is
the tuple of RETAINED fields below: §D4-R
L3's shape fields for one node, with heights and digit values struck.

- **(tag)** the read's position class: ROOT (the r = 0 read at the initial
  key x), POST-INC (immediately preceded by a D.8 increment landing), POST-REC
  (immediately preceded by a D.10 RS-landing). [§B2-DEF D.4: "Every non-root
  read is immediately preceded by a landing of one of the two species — that
  is the read process's definition: a branch reads one side."]
- **(stage)** degree bookkeeping: current key degree D = deg Φ, current pool
  residue degree w = [F : F_p], current window width W (POST-INC/POST-REC:
  W = μ_prev, the previous selection's multiplicity — D.8 (BOX)/(VERTEX) and
  D.10's RS-landing land on the window [0, μ]; ROOT: W = n).
- **(side)** the read side's data, HORIZONTAL only: the stride e (= e_read,
  lowest-terms denominator of the side slope), raw left endpoint s₀′, raw
  width w′ = e·ℓ, the CENSUS slot set {p̂_k} (hence the digit count
  d := #slots), the CENSUS anchor a := ⌊s₀′/e⌋ ≥ 0 [rev 4, pass-2 C1 —
  the census system (SH-C) of the shift block below, = FC4's convention:
  the number of stride-lattice positions on the extended side line strictly
  left of the side, = (s₀′ − (s₀′ mod e))/e. Its GEOMETRIC counterpart is
  a^geo := ord_z R(f) = a − ⌊tγ/e⌋ (D.3(c); the shift block) — height- and
  Bézout-carrying, hence NOT a letter field at e ≥ 2. At e = 1 the two
  COINCIDE (t = 0 by (P2), so D.3(c)'s positions are p_j = j and the least
  occupied one is the left endpoint s₀′): that common value is the anchor
  D.10's monomial (z + c̃)^a consumes — and D.10 is invoked ONLY at
  e_read = 1 (Species lemma), so no anchor monomial ever fires at e ≥ 2;
  D.8's e ≥ 2 ANCHORING is realized-read (η-level) data, pinned per read,
  never a letter field]; ℓ := w′/e = deg R_anch is the normalized side
  length (§D4-R L11's residual-degree datum; R_anch is SHIFT-INVARIANT —
  the shift block — so λ and the selection are system-independent).
- **(residual shape)** the degree–multiplicity partition λ of the anchored
  residual: the multiset {(g⁽¹⁾, μ⁽¹⁾), …, (g⁽ᵏ⁾, μ⁽ᵏ⁾)} recording, for each
  monic-irreducible factor of R_anch, its degree and its order, with
  Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ. WHICH polynomial R_anch is — hence which partition fires
  — is digit-value CELL data (§D4-R L5); the catalogue lists every partition
  as a value-free LABEL.
- **(selection)** the branch datum: the pair (g, μ) ∈ λ the branch descends
  at, or the TERMINAL MARKER ⊥ (the read continues no branch) [rev 3,
  pass-1 C2 — ONE type, fixed here: verdicts are NOT species and carry no
  species field. WHICH verdict closes a ⊥-read's chain is LEAF data (§D4-R
  L2), drawn from the disjoint verdict alphabet V_term of SP.4 — never a
  field of the letter]. The selection INDEX s_r — WHICH of several
  same-shape factors — is NOT species data: it is branch data owned by [1]'s
  L11 encoding, and two chains differing only in s_r have the same species at
  every read.
- **(flank/co-factor)** the co-factor pattern: the horizontal compositions of
  the window span outside the read side (the other sides' raw widths, left
  and right of the read side), heights and values forgotten. [Retained per
  Theorem MENU's flank/co-factor clause; well-defined shape data because L5's
  digit datum includes EVERY side of the window polygon, so the shape-prefix
  retains every side's horizontal span.] The non-selected part of λ is the
  residual co-factor and is already carried by (λ, selection).

FORGOTTEN, by design (Theorem MENU's quotient, plan §3): the side HEIGHTS —
each read carries a height PAIR (h_r, u*_r) ∈ ℕ² as parameters (the slope
height h_r AND the side height u*_r, §D4-R L3 rev 9: u*_r is retained P̂
data, NOT recoverable from the other fields at non-adjacent e = 1 reads —
the witness pair f₁ = x³+px+p³ vs f₂ = x³+p²x+p⁴ has every u*-free field
identical yet distinct strata), never catalogue
fields; self-loop repetition counts (DEPTHS — run-lengths of equal-species
consecutive reads); all digit values; all lifts. gcd(e, h) = 1 and every other
height-typed constraint is parameter GEOMETRY: [2b] M4a's congruence lattices,
not catalogue data.

**THE TWO COORDINATE SYSTEMS AND THE SHIFT ISOMORPHISM (rev 4, pass-2 C1 —
the census/geometric conflation repaired by DISPLAY, not by re-enumeration).**
Two position systems attach to one read side; rev 3 silently mixed them.
Both are now defined, with the coordinate change displayed and every
consumer told which system it reads.

GEOMETRIC (§B2-DEF D.3(c) — Bézout-pinned, height-carrying; what §D4-R L3
retains and D.8's ANCHORING/D.10 consume per realized read). At a stage with
read index (e, h) and pinned Bézout pair (s, t) (e·s + t·h = 1; (P2): t = 0
at e = 1), a read side of side weight γ (:= e·u* + j*·h, constant along the
side line — §D4-R L3's derived γ_r) has its on-line lattice slots
j_k := s₀′ + k·e (k = 0, …, ℓ) at the z-positions

  (SH-G)   p_j(γ) = (j − t·γ)/e ∈ ℤ    (D.3(c)),

so the geometric slot set is {a^geo, a^geo+1, …, a^geo+ℓ} with the GEOMETRIC
ANCHOR a^geo := p_{s₀′}(γ) = (s₀′ − t·γ)/e = ord_z R (the left endpoint is a
vertex, its digit nonzero). These positions depend on the struck height γ
AND on the mod-e Bézout representative (t ↦ t + e·m shifts every p_j by
−m·γ): at e ≥ 2 they are NOT height-free shape data.

CENSUS (FC4's normalization — height-free, Bézout-free; the LETTER's
fields). Census anchor and slots

  (SH-C)   a := ⌊s₀′/e⌋ = #(on-line lattice slots strictly left of s₀′),
           p̂_k := a + k   (k = 0, …, ℓ)

— functions of the retained (e, s₀′, ℓ) alone. (FC3's raw display
j_k = s₀′ + k·e is the e-stretch of the same data: j_k = e·p̂_k + (s₀′ mod e).)

THE SHIFT. Set σ := ⌊t·γ/e⌋. INTEGRAL AND WELL-DEFINED, always: with u₀ :=
the left endpoint's height, γ = e·u₀ + s₀′·h, so modulo e
t·γ ≡ t·h·s₀′ ≡ (1 − e·s)·s₀′ ≡ s₀′, whence t·γ mod e = s₀′ mod e and
σ = (t·γ − (s₀′ mod e))/e ∈ ℤ — the census convention is NOT lossy. Then

  (SH)   Sh_{t,γ} : ℤ → ℤ,  p ↦ p + σ ;    p̂_k = Sh_{t,γ}(p_{j_k}),
         a = a^geo + σ.

Proof of the displayed identities: p_{j_k} + σ = (j_k − t·γ)/e +
(t·γ − (s₀′ mod e))/e = (j_k − (s₀′ mod e))/e = (s₀′ − (s₀′ mod e))/e + k
= ⌊s₀′/e⌋ + k = p̂_k; k = 0 is the anchor identity. At e = 1: t = 0 ((P2)),
σ = 0 — THE SYSTEMS COINCIDE (a = a^geo = s₀′ = ord_z R; FC4's e = 1 clause).

BIJECTION AND TRANSPORT OF THE CLOSURE RELATIONS. Sh_{t,γ} is an affine
bijection carrying the geometric slot set onto the census slot set and a^geo
onto a, ALL OTHER FIELDS FIXED — in particular the anchored residual is
SHIFT-INVARIANT: R_anch := z^{−ord_z R}·R = Σ_k c_{j_k}·z^k in BOTH displays
(relabeling p ↦ p + σ multiplies R by z^σ, which the anchoring cancels), so
λ, the selection, and ℓ = deg R_anch never see σ. On species tuples:
(G1)/(G4)/(G5)/(G6) mention no position — transported verbatim; (G2)^geo
(a^geo = (s₀′ − tγ)/e = ord_z R) ⟺ (G2) (a = ⌊s₀′/e⌋) and (G3)^geo
({p_j} = {a^geo, …, a^geo+ℓ}) ⟺ (G3) ({p̂_k} = {a, …, a+ℓ}), each
equivalence BY Sh_{t,γ} at the read's own (t, γ). A "geometric catalogue"
would be ill-typed (its tuples carry the struck γ): the catalogue is
enumerated in CENSUS coordinates, and the census-to-theory identification
is PER READ, through the displayed map — a realized read's retained §D4-R
L3 datum (geometric positions, height pair) maps to its letter by Sh; the
geometric data is recovered by Sh⁻¹ (γ = e·u*_r + j*_r·h_r from the
retained height pair, t from the stage's pin). Nothing is lossy either way.

THE ANCHOR BOUND IN BOTH SYSTEMS ((B5)'s clause, re-derived). CENSUS — the
letter-level bound; (B5) as corrected at rev 3 HOLDS in census coordinates:
from (B3)'s 0 ≤ s₀′ ≤ W − w′ and floor-monotonicity,

  0 ≤ a ≤ ⌊(W − w′)/e⌋,   a + ℓ = ⌊(s₀′ + w′)/e⌋ ≤ ⌊W/e⌋ ≤ W ≤ n.

GEOMETRIC IMAGE (through Sh⁻¹, per realized read): −σ ≤ a^geo ≤
⌊(W − w′)/e⌋ − σ with σ = ⌊tγ/e⌋ — height- and Bézout-dependent, hence NOT
a species-level bound; a^geo < 0 occurs at e ≥ 2 (example below). At e = 1
the two statements are ONE: 0 ≤ a = a^geo ≤ W − w′ (R3's a = 2 = 3 − 1
saturates it).

THE VERIFIER'S EXAMPLE (pass-2 C1), side by side. Root side (1,1)–(3,0):
e = 2, h = 1, ℓ = 1, s₀′ = 1, γ = 2·1 + 1·1 = 3 (= 2·0 + 3·1 at the right
endpoint); Bézout 2·0 + 1·1 = 1 pins (s, t) = (0, 1); σ = ⌊3/2⌋ = 1.

  GEOMETRIC:  p₁ = (1 − 3)/2 = −1,  p₃ = (3 − 3)/2 = 0 —
              slots {−1, 0},  a^geo = ord_z R = −1  (< 0: e ≥ 2).
  CENSUS:     a = ⌊1/2⌋ = 0,  slots {0, 1}  — the R7 s₀′ = 1 letter.
  SHIFT:      {−1, 0} + 1 = {0, 1} ✓;  −1 + 1 = 0 ✓.  Anchor bounds:
              census 0 ≤ 0 ≤ ⌊(3 − 2)/2⌋ = 0 (saturated); geometric image
              −1 ≤ −1 ≤ −1 (saturated).
  BÉZOUT CHECK: the representative (s, t) = (1, −1) gives p₁ = 2, p₃ = 3,
              σ = ⌊−3/2⌋ = −2 — the same census image ✓ (the geometric
              system moves with t; the census image is invariant).

Both rev-3 records were correct records OF DIFFERENT SYSTEMS; the defect
was citing D.3(c) for census fields. D.10's well-typedness lemma (a ≥ 0)
remains an e = 1 statement — nothing here extends it to e ≥ 2.

**The compatibility relations (displayed; rev 3, pass-1 C1; stated in
CENSUS coordinates — rev 4, the shift block above holds their geometric
images).** A species tuple is GEOMETRICALLY COHERENT iff:
  (G1) FLANK–SPAN: left-flank span = s₀′, and s₀′ + w′ + right-flank span
       = W (the read side and its flanks compose the whole window span);
       each flank is a composition of its span.
  (G2) ANCHOR–POSITION: a = ⌊s₀′/e⌋ (the CENSUS anchor, (SH-C); its
       geometric form a^geo = (s₀′ − tγ)/e = ord_z R(f) is equivalent
       under Sh_{t,γ} — the shift block; at e = 1 the systems coincide
       and a = s₀′ = ord_z R(f) by D.10's well-typedness lemma).
  (G3) SLOT-SET: {p̂_k} = {a, a + 1, …, a + ℓ} and d = ℓ + 1 — the census
       positions step by 1 per e-step of j (= D.3(c)'s geometric stride
       rule transported by Sh_{t,γ}); OCCUPANCY (which
       digits vanish) is value data, struck like all values, so the slot
       set rides for free on (a, ℓ).
  (G4) RESIDUAL–SELECTION: Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ (deg R_anch = ℓ, §C DOM via
       §D4-R L11), and the selection is a member of λ or ⊥.
  (G5) STAGE REACHABILITY: tag = ROOT forces (D, w, W) = (1, 1, n); a
       POST-* tuple's stage is (e·g·D, g·w, μ) for SOME catalogue tuple at
       the parent stage with continuing selection (g, μ) and stride e —
       tag POST-INC iff e·g ≥ 2, POST-REC iff e = g = 1 (the (B1)–(B3)
       recursions read as a generation rule; without it, budget-admissible
       tuples at unreachable stages — e.g. (D, w) = (2, 3), w ∤ D — would
       inflate the catalogue past the enumeration).
  (G6) TERMINAL RULE: selection = ⊥ iff W = 1. [A W = 1 window forces the
       whole side datum — e = ℓ = 1, s₀′ = a = 0, λ = {(1,1)}, no flanks —
       and a W = 1 read is CONFIRMING: its parent's selection had μ = 1,
       [3t] VP's (τ-irr) saturation (or W = n = 1 at the root — the
       degenerate degree). The catalogue closes every word at its first
       W = 1 read — the ONE engine read below VP's halt: at n ≥ 2 the
       (τ-irr) halt, which sits at the PARENT (saturation ⟺ μ = 1 at the
       latest read, VP verbatim); at n = 1 the (τ-hen) halt at the
       level-0 track, which precedes every read (SP.4's HALT CONVENTION,
       rev 4; n = 1 clause, rev 5): the confirming read IS a
       letter (census data, gate-walked), consumers' τ-words stop at the
       halt, and engine reads below the confirming read are no object at
       all — not letters, not censused.]

**Definition (the raw catalogue; rev 3 — C1 repair).** 𝒮_n^raw := the least
set of species tuples as above that contains every (G1)–(G4)+(G6)-coherent,
(B1)–(B5)-admissible ROOT-stage tuple and is closed under (G5)'s generation
rule (each generated tuple again (G1)–(G4)+(G6)-coherent and budget-
admissible) — a finite closure (it injects into SP-FIN's encoding).
A BRANCH SHAPE is a finite word in this alphabet (a shape-prefix P̂ of
§D4-R L3 = a word plus its per-read height-pair parameters (h_r, u*_r) and
its collapsed-run
depths); the catalogue itself carries no words, no counts, no parameters — it
is the alphabet.

### SP.2 Theorem SP-FIN — the catalogue is finite and p-independent (M1)

**The budget inequalities (displayed; M1's one degree budget, plan §3).** At
every read of every realizable chain, with D_r, w_r, W_r the stage fields and
(e_r, ℓ_r, a_r, s₀′_r, λ_r, (g_r, μ_r)) the side/residual/selection fields:

  (B1) DEGREE BUDGET.  D₀ = 1 (key x);  D_{r+1} = e_r·g_r·D_r  (§B2-DEF D.5:
       deg Φ̂ = e·g·deg Φ; a recentering is the e = g = 1 case, D.10);
       D_r ≤ n at every read, i.e. ∏_{i<r} e_i·g_i ≤ n — hence a chain
       carries at most log₂ n GENUINE increments (each factor e·g ≥ 2).
  (B2) RESIDUE BUDGET.  w₀ = 1;  w_{r+1} = g_r·w_r  (D.6: F′ = F[z]/(ψ),
       deg ψ = g);  w_r = ∏_{i<r} g_i ≤ n  (M1's cumulative residue degree).
  (B3) WINDOW CONFINEMENT.  W_root = n;  at a non-root read W_r = μ_{r−1}
       (D.8 (BOX)/(VERTEX), D.10 RS-landing: the child window is [0, μ]);
       the read side fits the window: s₀′_r + w′_r ≤ W_r,  w′_r = e_r·ℓ_r,
       a_r + ℓ_r ≤ W_r,  d_r ≤ w′_r + 1;  and W_r ≤ ⌊n/D_r⌋ (the development
       of a degree-n f at a degree-D_r key has ≤ n/D_r slots).
  (B4) SELECTION BUDGET.  g_r·μ_r ≤ Σᵢ g⁽ⁱ⁾μ⁽ⁱ⁾ = ℓ_r  (the partition
       identity: deg R_anch = ℓ, §C DOM's width-confinement via §D4-R L11),
       hence the Σ eᵢgᵢμᵢ-type constraint  e_r·g_r·μ_r·D_r ≤ e_r·ℓ_r·D_r
       = w′_r·D_r ≤ n.
  (B5) PER-FIELD CAPS (M1 for the ≤ n caps; anchor clause CORRECTED at
       rev 3 — the drafted "anchors ≤ side width" is FALSE (R3: a = 2 >
       w′ = 1) and is struck).  e ≤ n, g ≤ n, μ ≤ n, ℓ ≤ n, 0 ≤ s₀′ ≤ n,
       d ≤ n + 1, D ≤ n, w ≤ n, W ≤ n; strides e ≤ w′ (= e·ℓ) ≤ n; the
       ANCHOR bound, IN CENSUS COORDINATES (the letter's field — rev 4;
       re-derived with its geometric image at SP.1's shift block),
       from (G2) + the side-in-window constraint
       (B3): a = ⌊s₀′/e⌋ ≤ (W − w′)/e, i.e.
         0 ≤ a ≤ ⌊(W − w′)/e⌋,  hence  a + ℓ ≤ ⌊W/e⌋ ≤ W ≤ n
       (at e = 1: a ≤ W − w′ exactly — R3's a = 2 = 3 − 1 saturates it;
       the GEOMETRIC anchor obeys only the Sh⁻¹-image −⌊tγ/e⌋ ≤ a^geo ≤
       ⌊(W − w′)/e⌋ − ⌊tγ/e⌋, height-dependent, a^geo < 0 possible —
       never a species-level bound);
       every flank composition is a composition of a span ≤ n.

(B1)–(B5) are inequalities between INTEGERS attached to shape fields; no
residue field, no digit value, and no height enters any of them.

**Theorem SP-FIN.** 𝒮_n^raw is FINITE and INDEPENDENT of p, with the explicit
(crude) bound

  |𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}.

*Proof (an encoding count; ranges corrected at rev 3, pass-1 gap 1).* Every
species tuple is determined by an integer
vector with all entries in {0, 1, …, n+1} (each entry ≤ n + 2 values — the
old {0..n} range was false twice: d may equal n + 1, and at n = 1 a
{0..n}-entry has 2 < 3 values, too few for the tag): tag (1 entry, values
0/1/2 — and n + 2 ≥ 3 for every n ≥ 1); D, w, W
(3); e, ℓ, a, s₀′, d (5); the slot set as an indicator vector on {0, …, n}
(n+1 entries — redundant given (G3), kept for crudeness); λ as its
multiplicity matrix c : {1..n}² → {0..n} with
c(g, μ) := the number of factors of shape (g, μ) (n² entries; (B4) forces
Σ g·μ·c(g,μ) = ℓ ≤ n); the selection — (g, μ) ∈ λ, or ⊥ encoded as the
reserved pair (0, 0) (2 entries);
the two flank compositions as indicator vectors of their cut sets (≤ 2n
entries, spans ≤ n by (B5)). Total length ≤ 1 + 3 + 5 + (n+1) + n² + 2 + 2n
= n² + 3n + 12, each entry taking ≤ n + 2 values; 𝒮_n^raw injects into the
encoded set ((G1)–(G6) only shrink it). Hence the
displayed bound. p-INDEPENDENCE: no field of the datum, no relation of
(G1)–(G6), and no inequality of
(B1)–(B5) mentions p — the same list serves every prime. ∎

**Corollary SP-FIN′ (words).** For every L, the set of length-L words over
𝒮_n^raw is finite, of size ≤ |𝒮_n^raw|^L; in particular the shape-prefixes P̂
of each fixed length form a finite p-independent list (the height pairs
(h_r, u*_r) and depths
being parameters, not letters).

**The count-free reading of Theorem MENU's finiteness clause (binding for
this note's consumers).** What [2a] delivers as "𝒮_n is finite" is ALPHABET +
MENU finiteness: the finite p-independent letter list (SP-FIN) and the finite
syntactic successor menus (SP-OUT, SP.4) — i.e. the CTS automaton over a
finite state alphabet. A branch shape is a WALK in this finite automaton
together with its (height pair (h_r, u*_r), depth) ℕ-parameters; every
consumer reads it
prefixwise: [1v]'s templates are finite paths, each at its own length; [3]'s
depth direction is the matrix fixpoint (I − K_e)^{−1}, never a length bound;
[1] quantifies over one fixed P̂ at a time. [REVISED at rev 3, pass-1 C3:]
the collapsed LETTER length of a walk (the number of letters after
collapsing self-loop runs) IS bounded — Lemma SP-DAG (SP.4): the
loop-collapsed menu graph is a DAG, every collapsed walk has ≤ 6n² letters.
SCOPE OF THAT BOUND, displayed so nothing stronger is read off: it bounds
letter ALTERNATIONS only. The number of READS stays unbounded (self-loop
runs — the depth parameters — are arbitrarily long; [3]'s depth direction
is still the matrix fixpoint (I − K_e)^{−1}), and WITHIN-read ladder events
(zero-gain moves, restarts) are invisible to letters entirely — [4]'s named
OPEN lemma TRACK-COUNT (plan §6) is neither implied, cited, nor owed here.

### SP.3 Theorem SP-COMP — completeness (M5, branch-typed, per read)

**Theorem SP-COMP.** For every n, every prime p, every f in the monic
degree-n coefficient box, every chain η ∈ T_can(f) (§D4-R L2 — terminal-
verdict branches and infinite branches alike, prefixwise), and every read r
of η's CATALOGUE WORD — the reads of η up to and including its first
W = 1 read, if any [quantifier sharpened at rev 3; ENDPOINT PINNED at
rev 4, pass-2 C2 (SP.4's HALT CONVENTION): at n ≥ 2 VP's (τ-irr) halt sits
at the confirming read's PARENT — the saturating μ = 1-selection read,
where the verdict v = {(E, F)} is pinned; at n = 1 the confirming read is
the ROOT, no parent exists, and the halt is VP's (τ-hen) at the level-0
track (SP.4's n = 1 clause, rev 5) — either way the confirming read is
itself below the halt; it stays in the catalogue word as the census's
closing letter
(gate M-n3 walks it), while density consumers walk the τ-WORD = this word
minus that final letter (at n = 1 the EMPTY word — T_can^τ's leaf is the
track itself) (T_can^τ, [3t] VP); engine reads below the
confirming read are outside the alphabet, the word, and every
walk] —: the read's retained datum is a member of
𝒮_n^raw, and each consecutive
read pair is linked by an edge of the syntactic menu Out (SP.4). No
almost-everywhere-termination statement is consumed.

*Proof, with the citations exact.*
(1) **Taxonomy — the read list is closed.** The r = 0 read is the root read
at the key x (tag ROOT). Every non-root read is immediately preceded by a
landing of one of the TWO move species — §B2-DEF D.4, verbatim: "Every
non-root read is immediately preceded by a landing of one of the two species
(that is the read process's definition — a branch reads one side)": either a
D.8 INCREMENT landing (descend at ψ, deg ψ = g, at a side of stride e) or a
D.10 RS-LANDING (recentering). NO OTHER MOVE EXISTS: at an e_read = 1 side
the recentering is the g = 1 case of the increment theory (D.10: "every
recentering is the g = 1 case of the increment theory", ψ′ = z − c̃), and at
an e_read ≥ 2 side recenterings DO NOT EXIST (D.10 Species lemma: a
same-degree recentering needs w(t) = the slot-1 value, which at e_read ≥ 2
lies outside the coefficient value group since gcd(e, h) = 1) — so the
increment/recentering dichotomy is total over reads, exactly as the plan's
§B2-DEF read-move taxonomy states.
(2) **Vocabulary closure — nothing outside the fields occurs.** §B2-DEF D.7
(TRANS) constructs the stage-(r+1) package out of exactly the retained
vocabulary: the new key degree e·g·D (D.5, deg Φ̂ = e·g·deg Φ), the new pool
residue degree w·g (D.6: F′ = F[z]/(ψ)), the child window [0, μ] with its
sides (D.8 (BOX)/(VERTEX) after an increment; D.10's RS-landing after a
recentering — both two-sided), the side slopes legitimized by (I-aug) (D.4),
and the residual/anchor transport laws (D.8 (TRANSPORT); D.10: a′ = μ,
R′_anch(z′) = (z′ + c̃)^a·h(z′ + c̃)). This is Theorem MENU's M5 sketch
("TRANS constructs stage r+1 data of exactly the retained vocabulary;
nothing else occurs"), here consumed per READ: the stage fields of read r+1
are the D.7/D.8/D.10 outputs, so they are of catalogue type.
(3) **Budgets hold at every read.** (B1)/(B2): D.5's degree identity and
D.6's residue growth, iterated; D ≤ n and w ≤ n because a degree-D key with
D > n has an empty window over a degree-n f (M1's displayed degree budget).
(B3): the child window is [0, μ] by D.8/D.10; side-in-window and slot-count
constraints are the polygon conventions (D.3 stride rule and width bound).
(B4): deg R_anch = ℓ = w′/e per §C DOM's width-confinement, quoted at §D4-R
L11 ("the residual factor, of degree w′/e"); the partition identity is the
factorization of R_anch over F. (B5): the ≤ n caps are M1's; the anchor
clause is derived at (B5)'s display from (G2) + (B3).
(3′) **Geometric coherence holds at every read [rev 3; census-to-theory
identification THROUGH the shift map at rev 4, pass-2 C1].** (G1): §D4-R
L5's digit datum lists EVERY side of the window polygon, so the read side
and the other sides' spans compose the window span exactly. (G2)/(G3):
a realized read's retained §D4-R L3 datum carries D.3(c)'s GEOMETRIC
positions (Bézout-pinned, height-carrying); its LETTER's census fields
are BY DEFINITION the Sh_{t,γ}-image (SP.1's shift block): a = a^geo +
⌊tγ/e⌋ = ⌊s₀′/e⌋ and the slot set shifted likewise — so (G2)/(G3) hold
for the letter because their geometric forms hold for the read (D.3(c))
and Sh transports them; at e = 1 (t = 0) the systems coincide and
a = ord_z R(f) by D.10's well-typedness lemma. The identification is
through the DISPLAYED map, never a silent equality. (G4): §C DOM /
§D4-R L11 as in (B4), and a read either descends at a factor of R_anch
(D.8/D.10) or continues no branch (⊥). (G5): the r = 0 read is at the
root stage (key x: D = 1; pool F_p: w = 1; window [0, n]: W = n), and
step (5)'s stage laws generate every later read's stage — reachability by
induction along the word. (G6): a realized W = 1 window forces the
confirming side datum, and the word closes there per SP.4's HALT
CONVENTION (the halt itself sitting one read up, at the saturating
μ = 1 selection — at n = 1, at the level-0 track per VP's (τ-hen),
SP.4's n = 1 clause).
(4) **Verdict reads [retyped at rev 3, pass-1 C2].** A read with selection
⊥ continues no branch; its chain's τ-leaf carries a verdict from V_term
(SP.4), attached as §D4-R L2 leaf data — the verdict is NOT part of any
letter, and per the HALT CONVENTION a (τ-irr) verdict is pinned at the
⊥-read's PARENT (the halt), never at the ⊥-read itself (at n = 1 the
⊥-read is the ROOT, the verdict is (τ-hen)'s, and it is pinned at the
level-0 track — SP.4's n = 1 clause). The case list (z)/(ep)/(ns) behind V_term is §D4-R L5's; its
structural exhaustiveness — every f in the state cylinder lands in a
listed case, none orphaned — is kernel D4R.0-K part (b), DISCHARGED
(D4R0K_DERIVATION rev 3, dual-verified 2026-07-27); what remains on the
verdict side is the residual (c) — the pin (alphabet V + halting rule τ +
detection cap), owned by [3t] via VP.
(5) **Menu edges.** Consecutive reads are linked by the stage laws displayed
in (2): D′ = e·g·D, w′_pool = w·g, W′ = μ, tag′ = POST-INC iff e·g ≥ 2,
POST-REC iff e = g = 1 — which is precisely SP.4's edge relation; so each
realized transition is an Out edge. ∎

**Conditionality (displayed, inherited — LEDGER UPDATED at rev 3, pass-1
gap 2).** Kernel D4R.0-K parts (a) (L1 canonical-choice totality, consumed
wherever T_can(f)'s totality is — §D4-R L2) and (b) (case-list
exhaustiveness, step (4)) are DISCHARGED by the dual-verified kernel
derivation (D4R0K_DERIVATION rev 3, Codex SOUND + Fable CLEAN,
2026-07-27). SP-COMP's remaining conditionality is exactly the D4R.0-K(c)
residual — the verdict pin (alphabet V + halting rule τ + the uniform
detection cap), owned by [3t] via VP — entering at step (4)'s leaf
verdicts. The draft's
condition (ii) — §C's (SAE) repair, consumed through §D4-R L3's
realizability class (NA)+(HV)+(SAE) — is DISCHARGED: §C rev 14 is
dual-accepted (2026-07-27). CITES [corrected at rev 3, pass-1 gap 2]:
steps (1), (2), (3′), and (5) cite only the dual-accepted §B2-DEF; step
(3) additionally cites §C DOM through §D4-R L11 (both dual-accepted) —
all five are unconditional given those. Note the QUANTIFIER: completeness is per
BRANCH and per READ — f-level completeness is the tree statement (every
chain of T_can(f) is a catalogued word), and no single-run totality is
invoked (F1).

### SP.4 SP-OUT — the syntactic successor menus, and the entrance sub-catalogue

**Definition (V_term; rev 3, pass-1 C2 — the verdict alphabet, DISJOINT
from 𝒮_n^raw).** V_term := { (z), (ep), (ns) } — §D4-R L5's terminal-verdict
case labels, carried here as three bare LABELS. Verdicts are not species:
they have no fields, satisfy no budgets, own no menus, and are never
counted in 𝒮_n^raw. Their SEMANTICS (which multiset of (E, F) pairs a halt
reports, when τ fires) is [3t]'s verdict pin VP (VP-1/VP-2, §T-ASSEMBLY
T.1) — cited as owner, not consumed.

**Definition (Out; retyped at rev 3).** For s ∈ 𝒮_n^raw, the OUTGOING MENU
Out(s) ⊆ 𝒮_n^raw ∪ V_term (disjoint union) is

  Out(s) := SUCC(s) ∪ V_term,   where for continuing selection (g, μ) at
  stage (D, w) and stride e:
  SUCC(s) := { s′ ∈ 𝒮_n^raw :  D(s′) = e·g·D,   w(s′) = g·w,   W(s′) = μ,
              tag(s′) = POST-INC if e·g ≥ 2, POST-REC if e = g = 1,
              and s′'s own fields satisfy (G1)–(G6) + (B1)–(B5) at that
              stage },
  and SUCC(s) := ∅ for terminal s (selection ⊥).

An edge into V_term ENDS the word: the chain's τ-leaf carries that verdict
(§D4-R L2 leaf data; for the confirming W = 1 letters the τ-leaf is their
PARENT read, and at n = 1 the level-0 track — the HALT CONVENTION and its
n = 1 clause below). The five W = 1 letters of SP.6
have Out(s) = V_term
exactly. V_term ⊆ Out(s) for every s is the SUPERSET discipline on the
verdict side — whether a verdict is realizable after s at a given p is
never a [2a] claim (τ's firing is VP's, realizability [1v]'s). Every
SUCC clause is an INTEGER comparison between shape fields: no residue field is
evaluated, no digit is tested, no height enters — Out is p-INDEPENDENT BY
CONSTRUCTION (the plan's pass-5 concern-1 duty, discharged by definition: a
species inadmissible at a particular p KEEPS its label in the menu and
contributes empty landing sets, which is CTS-M(ii)'s zero-extension).
FINITENESS: |Out(s)| ≤ |𝒮_n^raw| + 3 by SP-FIN. That is all CTS-S consumes
to make its meet finite: JREF^src(s) = ⋀_{m ∈ Out(s)} JREF_m^source is a
finite meet of finite partitions (plan §2v).

**THE HALT CONVENTION (rev 4, pass-2 C2 — pinned to [3t] VP verbatim,
ONE convention for the (τ-irr) endpoint; n = 1 exceptional clause added
at rev 5, pass-3 C1).** VP's (τ-irr) fires at
SATURATION, "equivalent to μ = 1 at the branch's latest read": the HALT
READ — T_can^τ's leaf, carrying v = {(E, F)} — is the first read whose
selection is (g, 1), i.e. the confirming W = 1 read's PARENT (which
exists: at n ≥ 2 the confirming read is non-root — the n = 1 case is
the clause below, and is NOT a (τ-irr) case). The
confirming read is the engine's single read below the halt: a catalogue
LETTER (the census walks it — gate M-n3's depth-2 objects) but NOT a read
of T_can^τ. Words, once and for all: the CATALOGUE WORD (SP-COMP's
quantifier, the census's object) closes at the confirming read; the
τ-WORD (every density consumer's object) is the catalogue word with that
final confirming letter removed, closing at the halt read. The five
W = 1 letters' menus Out = V_term are the catalogue word's CLOSURE
MARKER — the verdict itself is pinned at the halt read (their parent),
never doubled at the confirming letter (VP (c2) exactly-one-verdict).
Edges into V_term from a CONTINUING letter (the (z)/(ep)/(ns) statuses of
the NEXT window, where no next read exists) end both words at that letter
— there catalogue word and τ-word agree.

**THE n = 1 CLAUSE (rev 5, pass-3 C1 — the root confirming letter is
governed by VP's (τ-hen), not (τ-irr)).** At n = 1 the catalogue word is
the single ROOT letter (W = n = 1, selection ⊥ — (G6)'s degenerate
degree), which has NO parent; the (τ-irr) endpoint above does not apply
to it, by VP's OWN domain split, quoted verbatim from §T-ASSEMBLY (VP-2)
— each quote locatable BY ITS TEXT (grep anchors; line numbers drift as
the file grows and are deliberately not cited):
 · (τ-irr)'s domain EXCLUDES it: "(τ-irr) IRREDUCIBILITY
   CERTIFICATE — domain: BRANCHES carrying ≥ 1 window read". At n = 1 no
   window read exists: deg f̄ = 1 forces the unique level-0 reduction
   factor SIMPLE (m₁ = 1, deg ψ₁ = 1), and VP's covering case analysis
   is total on exactly this point: "At level 0, m_i = 1
   gives τ-hen and m_i ≥ 2 opens the window — total".
 · (τ-hen) CLAIMS it: "(τ-hen) ROOT HENSEL LEAVES — domain:
   level-0 TRACKS. […] A track with m_i = 1 (simple reduction factor,
   residue degree g := deg ψ_i) halts with NO window read ever opened:
   v = {(1, g)}". At n = 1: g = 1, so v = {(1, 1)}.
So at n = 1 the HALT is VP's (τ-hen) halt: T_can^τ's leaf is the level-0
TRACK itself — it PRECEDES every read — carrying v = {(1,1)}; the τ-WORD
is EMPTY (the standing rule "catalogue word minus the final confirming
letter" applied to the one-letter word, consistent with (τ-hen)'s zero
window reads); the CATALOGUE WORD is the single confirming root letter —
census data, gate-walked, its Out = V_term edge the same closure marker
as at n ≥ 2; and the verdict is pinned at the track leaf, never at the
letter — exactly-one-verdict holds by VP's own depth split [(c2) MUTUAL
EXCLUSIVITY — locate by the quoted text; line numbers drift]: "(τ-hen) fires only on level-0
tracks with NO window read; (τ-irr) requires ≥ 1 read — disjoint by
depth." CONTRAST, so the two degenerate-looking cases are not conflated:
VP's FC5 reconciliation [locate by the quoted text; line
numbers drift] — "strictly it is a
one-read branch, hence τ-irr with v = {(1,1)}" — concerns the cubic
cell's linear μ = 1 branch, whose single read IS a window read (its
cluster's window is OPENED by m = 3 ≥ 2), so (τ-irr) fires AT that read
and the confirming child sits below it; at n = 1 the window never opens,
the root letter is not a window read, and (τ-irr)'s domain is empty.
Uniform picture: the confirming letter is ALWAYS the engine's one
below-halt read (VP: "The engine's below-halt continuations exist
syntactically but are NOT walked") — below the (τ-irr) parent-halt at
n ≥ 2, below the (τ-hen) track-halt at n = 1.

**Bridge to CTS-S skeletons (typing only — no new object).** The plan's
bounded current-state skeleton s = (residual degrees/multiplicities, anchor
a, tower phase — values forgotten) is the STATE-SIDE FACE of a catalogue
member: stage (D, w, W) + tag (the tower phase) + anchor a + the residual
partition λ. Out above instantiates the plan's Out(s) "emittable from s by
the [2a] + M1 degree/bound bookkeeping ALONE — evaluated over NO residue
field" (CTS-S, verbatim). A source cell's BRANCH SET may list several
(side, ψ) continuations; the syntactic menu lists them ALL — one edge per
(side-species, selection) pair — and branching itself exits to FAM per the
§2v branch-cell decision; nothing here re-imports it.

**SELF-LOOPS, syntactically.** s has a self-loop edge iff s ∈ SUCC(s):
necessarily e = g = 1 (else D grows strictly, (B1)) with W(s) = μ(s) — the
POST-REC species whose window equals their own selection multiplicity.
These are the depth-direction letters; their run-lengths are the forgotten
DEPTH parameters. [The drafted sentence "all other edges strictly increase
D or change (W, λ, a)" is WITHDRAWN as false (pass-1 gap 3): two distinct
POST-REC letters can share (D, W, λ, a) and differ only in side position,
flanks, slots, or selection. The true progress statement is the lemma.]

**Lemma SP-DAG (the collapsed-walk bound; rev 3, pass-1 C3).** Call
s ∈ 𝒮_n^raw FULL if its selection is (1, W(s)) — by (G6) full letters live
at W ≥ 2 only (W = 1 forces ⊥). (i) At each fixed
(tag, D, w, W) there is AT MOST ONE full letter: μ = W with (B4)'s
g·μ ≤ ℓ and (B3)'s a + ℓ ≤ W forces g = 1, ℓ = W, a = 0, λ = {(1, W)}
(the partition identity Σ gᵢμᵢ = ℓ = W with one part of size W); then
(B3)'s s₀′ + w′ ≤ W with w′ = e·ℓ = e·W forces e = 1 and s₀′ = 0
(consistent with (G2): ⌊0/1⌋ = 0 = a), by (G1) both flanks empty, by (G3)
slots {0, …, W} — every field determined. (ii) The rank
  ρ(s) := ( D,  tagord,  n − W,  1 − [s is full] ),
tagord := 0/1/2 for ROOT/POST-INC/POST-REC, STRICTLY increases
lexicographically along every non-self-loop SUCC edge s → s′:
 · e·g ≥ 2: D′ = e·g·D > D.
 · e = g = 1, μ < W(s): D′ = D; tagord′ = 2 ≥ tagord; if tagord < 2 done,
   else n − W′ = n − μ > n − W(s).
 · e = g = 1, μ = W(s): s is full (by (i)'s derivation applied to s);
   D′ = D, W′ = μ = W(s). If tagord(s) < 2, tagord jumps to 2. If
   tagord(s) = 2, then s is THE full POST-REC letter at its stage, so
   s′ ≠ s (self-loops excluded) is non-full by (i)'s uniqueness: the last
   coordinate rises 0 → 1. (Conversely no SUCC edge leaves a NON-full
   letter at constant (D, W): a source with its own μ = W would be full.)
(iii) Hence the menu graph with self-loops collapsed is a DAG; every
collapsed walk visits pairwise-distinct ranks, so it has at most
|range(ρ)| ≤ n·3·n·2 = 6n² letters; with SP-FIN, the set of collapsed
words over 𝒮_n^raw is FINITE, of size ≤ (|𝒮_n^raw| + 1)^{6n²}. ∎
[SCOPE: letters only — reads, depths, and ladder events are NOT bounded;
SP.2's revised count-free reading displays the fence. n = 3 check: the
two loop classes Q2.3▸(1,2) and Q3▸(1,3) are exactly the full POST-REC
letters at stages (1,1,2) and (1,1,3), per (i).]

**Definition (the entrance sub-catalogue {ε}).** An ENTRANCE SHAPE into a
block entry (e-block, landing cell β₀ — [1v] CTS-M(iii)'s objects) is a
finite word ε in 𝒮_n^raw, linked by Out edges, whose LAST letter is the
block-entry read and whose designated continuing branch enters the size-e
block — a shallow shape-prefix P̂ of the root/branch cascade in [1]'s sense,
its height pairs (h_r, u*_r) retained as ℕ-parameter slots (§D4-R L3 rev 9)
and its self-loop runs carried as
depth parameters (one marker letter + one depth slot per maximal run). What
[2a] supplies about {ε} (plan §2v: "the shape family {ε} is FINITE up to its
height parameters ([2a]/M1)") — PROVED at rev 3 (pass-1 C3: the drafted
argument "finite alphabet + finite menus ⇒ finite {ε}" was a non sequitur —
a finite graph can carry infinitely many collapsed walks; the finiteness
needs and now has Lemma SP-DAG): a loop-collapsed entrance word is a
collapsed walk in the menu graph, so it has ≤ 6n² letters (SP-DAG(iii));
with SP-FIN the family of such words is finite and p-independent — {ε} is
finite up to its (height pair, depth) parameters, which is exactly the
finiteness CTS-M(iii) consumes,
its per-shape masses ι_{e,ε,β₀} and entrance counts I^ent_{ε,β₀} being
[1]/[1v] objects, never assigned here. The n = 3 instance is displayed in
SP.6.

**The SUPERSET duty (binding on every consumer).** Out(s) is a SUPERSET of
the transitions realized at any given p. Three separate reasons an edge can
be empty at p, with three separate owners:
 (i)   FIELD SIZE — λ or a selection needs more distinct nonzero roots or
       distinct irreducible factors than F_q holds (e.g. λ = {(1,1)³} needs
       three distinct nonzero roots: empty at q ∈ {2, 3}); owner: [1v]'s
       tables (the entry is the zero polynomial or vanishes at q₀ —
       CTS-M(ii) ACT).
 (ii)  VALUE/COLLISION constraints — (NA)/(HV)/(SAE), nonzero endpoints,
       factor collisions; owner: [1v]'s cells and tables.
 (iii) HEIGHT-LATTICE emptiness — no height point of the step's exact
       domain; owner: [2b] XHD/M4a-X.
Realizability of a given menu edge at a given p is therefore NEVER a [2a]
claim; the menu is the index superset the CTS zero-extends over.

### SP.5 Honest perimeter (what this note does NOT establish)

- **NO COUNTS, NO MASSES.** The catalogue indexes; it never counts. Every
  count or mass routed through a shape is owned elsewhere: per-shape
  sum/event laws and pool bounds by [1] (D4R.1-SUM/-EV, D4R.2′, D4R.4;
  branch multiplicities mult_P̂ included); per-cell value counts and table
  entries by [1v] (CTS-M); resummed masses and the f-level tree assembly by
  [3] (RS.1 — where MULT ACCOUNTING converts branch-weighted sums to
  f-events); tail bounds by [5]. Any consumer counting f's through this
  catalogue owes the mult-cover duty: shape events are a multiplicity-
  weighted COVER, Σ_P̂ μ(P̂) may exceed 1, and each use must declare
  D4R.1-SUM/D4R.4-SUM (branch-weighted) or the event BOUNDS — a
  partition-of-the-box-by-shapes claim is banned (§D4-R consumer duty,
  plan §2).
- **NO REALIZABILITY.** Whether a catalogue member or menu edge is realized
  at a given p, at a given height point, in a given cell: [1v] (tables,
  ACT) and [2b] (XHD/M4a-X). The menus are supersets (SP.4).
- **NO STATE TYPES, NO GEOMETRY.** The loop state type τ = (s, α), the
  lumpability theorem, cones, congruence lattices, exact height domains,
  translation equivariance: all [2b] (M2, M4a, M4a-X, M4b/M4b-T). 𝒮_n =
  𝒮_n^raw enriched by [2b]'s types happens THERE.
- **LENGTH BOUND — LETTERS ONLY [revised at rev 3].** Lemma SP-DAG bounds
  the collapsed LETTER-length of a walk (≤ 6n²); NO bound on reads, depths
  (self-loop run-lengths), or within-read ladder events is claimed —
  [4]'s TRACK-COUNT stays the named OPEN lemma for those, not cited here.
- **NO TERMINATION.** Infinite branches are catalogued prefixwise;
  drainage/exhaustion is [3]/[5]'s.
- **CONDITIONALITY LEDGER [updated at rev 3, pass-1 gap 2].**
  Unconditional given dual-accepted §B2-DEF (+ §C DOM via §D4-R L11 where
  cited): SP.1's datum being well-typed, the (G1)–(G4) coherence, SP-FIN,
  SP-FIN′, SP-OUT and its p-independence, the self-loop characterization,
  Lemma SP-DAG. Conditional: SP-COMP — on the D4R.0-K(c) RESIDUAL only
  (the verdict pin, owned by [3t] via VP; parts (a)/(b) DISCHARGED by the
  dual-verified kernel derivation, 2026-07-27); the draft's second
  condition, §C's (SAE) repair, is DISCHARGED
  (rev 14 dual-accepted 2026-07-27; §D4-R L3's realizability class
  (NA)+(HV)+(SAE) stands as stated). Nothing else in the campaign is
  assumed; [1v]/[2b]/[3]/[3t] artifacts
  are referenced only as OWNERS of deferred duties, never consumed.

### SP.6 Sealed gate M-n3 (the obligation; catalogue and predictions pinned)

**The hand catalogue at n = 3 (exhaustive; SEALED).** Notation per letter:
(e, ℓ, a | λ ▸ sel | flanks), stage in the group head. Windows: ROOT W = 3;
POST-REC W = μ_prev ∈ {1, 2, 3}; POST-INC W = 1 always at n = 3 (every
genuine increment here has μ = 1: g·μ ≤ ℓ and e·ℓ ≤ 3 force μ ≥ 2 into
e = g = 1, the recentering class). W = 1 letters read the confirming side
(ℓ = 1, a = 0, λ = {(1,1)}) and are TERMINAL: selection ⊥ [retyped at
rev 3, C2 — formerly "carry the TERMINAL verdict as selection"; the verdict
is V_term leaf data per §D4-R L2, not a species field]; their menus are
Out = V_term (the catalogue word's closure marker — the (τ-irr) halt and
its verdict sit at their PARENT read, per SP.4's HALT CONVENTION, rev 4).
Each stays ONE letter under the retype: |𝒮₃^raw| = 53 is
UNCHANGED.

**R3's membership check under the rev-3 definition (spot-display; the
drafted (B5) EXCLUDED R3 — a = 2 > w′ = 1 — which contradicted the count).**
R3 = (ROOT, (D,w,W) = (1,1,3), e = 1, ℓ = 1, a = 2, s₀′ = 2, slots {2,3},
λ = {(1,1)} ▸ (1,1), left flank (2) or (1,1), right empty):
(G1) left span 2 = s₀′; 2 + 1 + 0 = 3 = W ✓. (G2) a = ⌊2/1⌋ = 2 ✓.
(G3) slots {a, a+ℓ} = {2, 3}, d = 2 = ℓ + 1 ✓. (G4) Σ = 1 = ℓ, sel ∈ λ ✓.
(B3) s₀′ + w′ = 3 ≤ W, a + ℓ = 3 ≤ W, d = 2 ≤ w′ + 1 ✓. (B5, corrected
anchor bound) a = 2 ≤ ⌊(W − w′)/e⌋ = 2 ✓ (saturated). (B1)/(B2)/(B4) ✓.

GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters.
  R1  e=1, ℓ=1, a=0 | {(1,1)}▸(1,1) | right span 2: flanks (2) or (1,1) — 2
  R2  e=1, ℓ=1, a=1 | {(1,1)}▸(1,1) | flanks (1)|(1)                    — 1
  R3  e=1, ℓ=1, a=2 | {(1,1)}▸(1,1) | left span 2: (2) or (1,1)         — 2
  R4  e=1, ℓ=2, a=0 | λ ∈ {(2,1)}▸(2,1); {(1,2)}▸(1,2); {(1,1)²}▸(1,1)
      | right flank (1)                                                 — 3
  R5  e=1, ℓ=2, a=1 | same three λ▸sel | left flank (1)                 — 3
  R6  e=1, ℓ=3, a=0 | {(3,1)}▸(3,1); {(2,1),(1,1)}▸(2,1) and ▸(1,1);
      {(1,3)}▸(1,3); {(1,2),(1,1)}▸(1,2) and ▸(1,1); {(1,1)³}▸(1,1)     — 7
  R7  e=2, ℓ=1, a=0 | {(1,1)}▸(1,1) | s₀′ ∈ {0, 1}                      — 2
  R8  e=3, ℓ=1, a=0 | {(1,1)}▸(1,1) | full span                         — 1
GROUP Q3 — POST-REC, stage (1, 1, 3): the same 21 rows as R1–R8.   — 21
GROUP Q2 — POST-REC, stage (1, 1, 2): 6 letters.
  Q2.1 e=1, ℓ=1, a=0 (right flank (1)); Q2.2 e=1, ℓ=1, a=1 (left (1));
  Q2.3 e=1, ℓ=2, a=0: three λ▸sel as R4; Q2.4 e=2, ℓ=1, a=0, s₀′=0.
GROUP Q1 — POST-REC, stage (1, 1, 1): 1 letter (confirming; ⊥).       — 1
GROUP I — POST-INC, W = 1, confirming TERMINAL (⊥) letters, one per landing
  stage (D, w) ∈ {(2,1), (2,2), (3,1), (3,3)}                          — 4
  [(2,1) via e=2 sides; (2,2) via ▸(2,1) — D4-n3's second read; (3,1)
  via e=3; (3,3) via ▸(3,1).]

  |𝒮₃^raw| = 21 + 21 + 6 + 1 + 4 = 53.

[RE-VERIFIED against the rev-3 definition: the (G5) closure from the root
stage (1,1,3) generates exactly the five displayed stage groups (root
selections (1,1)/(1,2)/(1,3) → stages (1,1,1)/(1,1,2)/(1,1,3); ▸(2,1),
▸(3,1), e=2, e=3 → the four POST-INC W = 1 stages; nothing further from
Q2/Q3; W = 1 terminal by (G6)); per stage, the (G1)–(G6)+(B1)–(B5corrected)
letters are exactly the displayed rows — e.g. ROOT: e=1 gives
(ℓ, s₀′)-cells (1,0):2, (1,1):1, (1,2):2, (2,0):3, (2,1):3, (3,0):7 by
flank-composition × λ▸sel counts, e=2 gives 2 (s₀′ ∈ {0,1}), e=3 gives 1,
total 21. The C2 retype and the corrected (B5) change NO letter and NO
count: 53 stands. R3's check is displayed above.]

**The n = 3 menu map (Out, sealed; stage laws of SP.4).** ▸(1,1) → Q1;
▸(1,2) → Q2 letters; ▸(1,3) → Q3 letters; ▸(2,1) → I(2,2); ▸(3,1) → I(3,3);
e=2 letters → I(2,1); e=3 letters → I(3,1). SELF-LOOPS: Q2.3▸(1,2) → Q2
(the μ = 2 loop) and Q3's ▸(1,3) rows → Q3 (the μ = 3 loop) — exactly two
loop classes at n = 3, both POST-REC, as SP.4's characterization forces
(W = μ). Every remaining outcome is an edge into V_term [rev 3 typing]:
(z)/(ep)/(ns) after any letter, and the W = 1 letters' menus are exactly
V_term (their leaves' verdicts are V_term leaf data, never letters; per
SP.4's HALT CONVENTION the (τ-irr) verdict is pinned at the μ = 1-selection
read — the confirming letter closes the word without a second verdict).
ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as
depth slots): into the μ=2 block: root▸(1,2) [R4/R5 rows], or
root▸(1,3)·(Q3-loop)^d·▸(1,2); into the μ=3 block: root▸(1,3); into each
increment landing (D ≥ 2): the ▸(2,1)/▸(3,1)/e=2/e=3 rows of R, Q2, Q3
prefixed by their cascades — a finite list, displayed by the same map.

**Realizability predictions, THRESHOLD FORM (rev 2, made PER-PRIME at
rev 3 = v3 — supersedes the sealed
clause; the gate record below has the adjudication).** Two independent
exclusion mechanisms in a level-N census box, with separate owners:
  (1) FIELD SIZE (p-dependent, N-free; SP.4(i)) — the sealed lists,
  UNCHANGED: λ demanding more distinct nonzero roots of F_q than exist
  (nonzero by the endpoint convention: a is split off, so z ∤ R_anch):
  p = 2 (one nonzero root): the 11 letters with λ ⊇ two distinct linears —
    {(1,1)²}: R4, R5, Q3(R4), Q3(R5), Q2.3 (5 letters);
    {(1,2),(1,1)}: R6 ▸(1,2), R6 ▸(1,1), Q3(R6) both (4);
    {(1,1)³}: R6, Q3(R6) (2).
  p = 3 (two nonzero roots): exactly the 2 letters with λ = {(1,1)³}.
  (2) DECIDABILITY LEVEL (N-dependent; PER PRIME — definition corrected at
  rev 3, pass-1 C4: the rev-2 form quantified over no prime, so
  field-size-excluded letters had no least N and the "iff" was ill-formed;
  made EXPLICITLY CONDITIONAL ON EXISTENCE at rev 4, pass-2 gap C4):
  for each prime p and each letter that IS EVENTUALLY REALIZED at p (some
  depth-≤2 chain of some T_can(f), f in some level-N box at p, realizes it),
    N*_p(letter) := the least such N, with every retained field DECIDED
    at cap N
  — DEFINED exactly on the eventually-realized letters. The field-size
  pass (1) is NECESSARY for realization, NOT sufficient: SP.4's exclusion
  mechanisms (ii) value/collision and (iii) height-lattice emptiness are
  independent, and no theorem here rules out a field-size-passing letter
  empty at every level. At p ∈ {2, 3}, n = 3, existence is CENSUSED, not
  proved: all 42 p = 2-admissible letters realized at N ≤ 8; all 51
  p = 3-admissible letters realized by the N ≤ 6 censuses plus the two
  constructed N = 7 witnesses — so N*_2 and N*_3 are TOTAL on the
  admissible letters there BY CENSUS. For other primes, totality of N*_p
  on the field-size-passing letters is part of the PREDICTION below, not
  a statement of this note. P-DEPENDENCE, stated honestly: the (I-aug)-forced height
  arithmetic below is p-UNIFORM (integer slopes and heights, no residue
  field), so its LOWER bounds on N*_p hold at every p, and N*_p is
  EXPECTED p-uniform on letters realizable at both primes — a REMARK, not
  a claim; only N*_3 is computed and censused here (N*_2 is bounded by the
  p = 2, N = 8 census: ≤ 8 on all 42 admissible letters).
  THE SIX COMPUTATIONS (all at p = 3 — the labels are N*_3): the
  exceptions are the multi-side μ = 3 letters — the sel-carrying Q3 copies
  whose child window [0,3] has ≥ 2 sides: Q3(R1, right flank (1,1)),
  Q3(R2), Q3(R3, left flank (1,1)), and the three Q3(R4) λ-rows. After the
  root ▸(1,3) recentering, (I-aug) convexity forces the child slopes
  strictly decreasing left of the vertex (s₁ > s₂ ≥ 1), so:
    · the three Q3(R4)-copies (read side [0,2] e=1, right side [2,3]):
      v(B′₀) = s₂ + 2s₁ ≥ 1 + 2·2 = 5 — decided only at N ≥ 6: N*_3 = 6;
    · Q3(R2)/Q3(R3)-copies (slot 0 provably ABOVE the [1,2]-line
      extension, a height-5 line): v(B′₀) ≥ 6 certified at cap 6: N*_3 = 6;
    · the Q3(R1)-copy (reads side [0,1]; slot 0 at EXACT height 6):
      N*_3 = 7.
  For the other 45 of the 51 letters passing (1) at p = 3: N*_3 ≤ 5 (the
  N = 5 census realizes them).
  PREDICTION (v3, per prime — RETYPED at rev 4, pass-2 gap C4: this is
  the queued re-seal gate's SEALED PREDICTION, not a theorem of this
  note; in particular its "iff" asserts, beyond every displayed
  computation, that each field-size-passing letter IS eventually realized
  at every p — i.e. N*_p total on them — which is censused only at
  p ∈ {2, 3}): a letter is realized in the level-N box at p
  iff it passes (1) at p and N ≥ N*_p(letter); realized means by a
  depth-≤2 chain of some T_can(f) — root letters at depth 1, POST-*
  letters at depth 2. At
  p = 2, N = 8: 42/53 (the censused N*_2 ≤ 8 on all 42 — clause (2)
  vacuous there, as in the sealed run; note the p-uniform lower bounds
  give N*_2 ≥ 6/6/7 on the five p = 2-admissible multi-side letters, the
  sixth — the Q3(R4) {(1,1)²} row — carrying NO N*_2 at all).
  At p = 3: N = 5 gives 45/53 (= the CENSUSED count; the 2
  field-size exclusions + the six N*_3 > 5 letters); N = 6 gives 50/53;
  N ≥ 7 gives 51/53. Any unrealized letter beyond (1)+(2) is a FINDING
  (a catalogue-vs-engine mismatch), not a tolerated gap. Height-dependent
  side-splitting (e.g. slope-0 sides absorb their right span, so R1's
  flanked variants live at h ≥ 1 only) is PARAMETER geometry ([2b] M4a):
  the letter is realized if realized at ANY height within the level budget
  — clause (2) is exactly this height clause made quantitative; the sealed
  list failed to apply it at p = 3, N = 5.
**Worked witnesses (two, displayed for the referee).** p = 2,
f = x³+x²+x+2: f̄ = z(z²+z+1) — the R5 letter with λ = {(2,1)} ▸(2,1)
(a = 1, side [1,3], left flank (1)) → I(2,2): D4-n3's shape up to the
anchor. p = 2, f = (x−1)³ − 2 = x³−3x²+3x−3: f̄ = (z−1)³ — R6 ▸(1,3) → the
Q3 e=3 letter (slope-1/3 side after the recentering) → I(3,1): the
wild-loop entrance and exit, both at depth ≤ 2.

**Census spec (the gate; run AFTER sealing the three lists above).**
(a) SCOPE: p = 2 at N = 8 (all 2²⁴ monic cubics mod 2⁸), p = 3 at N = 5
(all 3¹⁵) — the MENU-n3 boxes (plan §3). For every f: compute the root
digit-cell datum and ALL branches to depth 2 (root read + each eligible
continuation's read), canonical (S6b) lifts; f's undecidable-at-N reads
marked UNDECIDED and reported (they still contribute their decided
prefix reads).
(b) CHECKS, zero tolerance: (i) STRAYS — every realized read datum (tag,
stage, side, λ, selection, flanks) is one of the 53 letters: 0 strays;
(ii) TWO-SIDED REALIZATION — every letter predicted realized at that p is
realized (≥ 1 witness chain), every excluded letter is absent, and each
absence matches its displayed field-size explanation: 0 orphans, 0
unexplained absences; (iii) MENUS — every realized consecutive read pair
is an edge of the sealed n = 3 menu map: 0 off-menu transitions; (iv) the
loop classes realized are exactly the two displayed (Q2, Q3).
(c) PERIMETER OF THE GATE: it exercises the catalogue, menus, and
completeness ONLY — no counts, no masses, no per-cell distributions (those
are D4-n3's, D4-m2's, MENU-n3's, and [1v]'s gates). A pass supports SP-COMP
at n = 3 and the menu superset discipline; it does NOT discharge the
D4R.0-K(c) residual — the verdict pin, [3t]'s VP (§D4-R's standing caveat:
gate verdicts are not kernel support; parts (a)/(b) were discharged by the
dual-verified derivation, not by any gate) [ledger updated at rev 3].
LIMITATION RECORDED: n = 3 exercises POST-INC species only in confirming
position and no deep-wild stacked increments; the plan's R3 escalation
clause (n = 4) stands.

**GATE RECORD M-n3 (2026-07-27; census case_mn3_gate.py; seal + verdict:
verification/CASE_MN3_SEALED_PREDICTIONS.md §S3; machine-readable:
verification/results/case_mn3_results.json).** Both sealed boxes exhaustive
(p = 2, N = 8: all 2²⁴; p = 3, N = 5: all 3¹⁵). CONTENT: PASS — 0 strays
and 0 off-menu transitions at both primes (the 53-letter catalogue and menu
map complete over ~31.1M boxes); loop classes exactly the two sealed
(Q2.3▸(1,2), Q3▸(1,3)); 0 engine faults (BOX/VERTEX/I-aug/partition); both
worked witnesses confirmed; p = 2 realizability EXACT 42/42, all 11
field-size exclusions absent. REALIZABILITY CLAUSE: FAIL AS SEALED at
p = 3 — sealed 51/53 at N = 5, censused 45/53, the six absences being the
multi-side μ = 3 letters above. ADJUDICATION (prediction-DERIVATION error,
Case-K precedent class — the content is right, the sealed clause was
mis-derived): the absences are deterministic consequences of the sealed
level N = 5, provable from the budget inequalities via the (I-aug)-forced
height arithmetic (the N* display above); the sealed list drew exclusions
from field size alone and failed to apply SP.6's own any-height clause at
p = 3, N = 5. Post-census diagnostics (outside the seal, marked as such):
p = 3, N = 6 exhaustive (3¹⁸; 0 strays, 0 faults) realizes five of the six;
constructed N = 7 witnesses (f = g(x−1), g = x³+3x²+27x+729u, u = 1, 2)
realize the last (the Q3(R1)-copy); the FIVE p = 2-admissible of the six
realized in the sealed p = 2, N = 8 box [corrected at rev 3 against
results/case_mn3_results.json: the sixth, the Q3(R4) {(1,1)²} row, is
p = 2 field-size excluded — 0 hits there, correctly; the drafted "all six"
was false]. STATUS: the content clauses (catalogue, menus, loops,
completeness-to-depth-2) are census-pinned at both primes; the v2 THRESHOLD
clause above supersedes the sealed realizability list, and its RE-SEAL
**PASSED (2026-07-27, rev 6 update)**: gate CASE_MN3_V2 — p = 3 exhaustive
at EVERY level N = 1..7 (through the 3²¹ box): the realized sets exactly
9/22/32/43/45/50/51; all 45 fresh N* thresholds SHARP from both sides
(45, not 47: the two {(1,1)³} rows carry no N* — field-size-excluded at
every level; the Fable dual pass's F2 correction)
(present at N*, absent at N*−1); five first-appearance counts exact;
0 strays/off-menu/faults at every level; the diagnosed six consistent
with their v1 diagnostics; the contamination ledger drawn honestly in the
seal (fresh vs v1-observed vs machinery-touched; one pre-census
derivation correction on record — slope-0 root reads). Support, never
closure. The D4R.0-K(c) residual (the verdict pin) remains OPEN per
SP.6(c) — gate verdicts are
not kernel support — and the n = 3 POST-INC limitation stands. [Rev 3: the
threshold clause is v3 (per-prime N*_p); "v2" above names the rev-2 event.]

## §C: DUAL-ACCEPTED (2026-07-27 — Codex passes 16+17 CLEAN + Fable confirm CLEAN on identical rev-14 text)

§C meets the dual-verification bar: Codex 16+17 consecutive 0/0 (`C_PASS16/17_2026-07-26.md`)
and the fresh-Fable confirming pass 0/0 (`FABLE_CONFIRM_C_REV14_2026-07-26.md`) on the
same rev-14 text. The Fable confirm: F-EMPTY re-run live against (SAE) — excluded by
exact arithmetic (new(2) > old(2) ⟺ 1 > 1 fails); a NEW empty-stratum hunt found NONE
(5 realizable configs incl. two uncensused e=2 stretch species all nonempty at exactly
2^{−m*}; 3 excluded configs all exactly 0, incl. a nominal-500000/actual-0 instance);
an own no-record trace (root recentering → non-adjacent e=2 increment at an off-lattice
slot → adjacent tail) exact at every step; the m̂/γ/vtx arithmetic and the 8-item fence
swept clean. Puncture-to-dual-acceptance spiral: Fable puncture (the (SAE)
incompleteness) → revs 12/13/14 → Codex 14 (1c/3g) → 15 (1c/2g) → 16+17 CLEAN + Fable
CLEAN. §C and §B2-DEF are now BOTH through the full dual standard.

## §D4-R FABLE-PASS RECORD (rev 7: 0 critical, 2 display gaps — B1/B2) and the rev-8 repairs

The Fable dual pass on rev 7 (`FABLE_VERIFY_D4R_REV7_2026-07-26.md`): F1/F2/F3 all
GENUINELY answered; own mult = 3 trace (n = 6, p = 7, no record) census-verified exact;
the D4-m2 p = 3 family independently recomputed, 0 discrepancies; no silent single-branch
semantics; 0 criticals. Two display gaps, repaired in place as REV 8 (both one-liners):
B1 — the stale rev-5 heading 'the partition into prefix fibers' retitled 'the digit-cell
partition and its branch sets' (the rebuilt theorem beneath it); B2 — the D4R.1-SUM
average parenthetical now carries the 'at every level N ≥ N(P̂)' qualifier. Both
confirming passes (Codex + Fable, identical rev-8 text) = the dual-acceptance shot.



THE ERRATUM RECORD:
mismatches. F4: det(I−K_e) exact at ALL THREE pools q₀ = 2, 3, 4 (the per-pool
E0/(REG-p) evidence; junk blocks empty). F5: decided + undecided = p³ᴺ exactly, every
N. F7 (adjudicated finding): certified∖decided EMPTY — conservative, no counted
quantity affected. Scope honest: the value-kernel/μ ≥ 2 machinery untested (n = 5).
CONSEQUENCE for the event ledger: §S's [3] event was blocked on STATE-probe-2 (PASSED)
+ RESUM-n3 (now PASSED) + [1v]-FULL — the remaining blocker is [1v]-FULL alone (the
six §H fences). 22 sealed censuses, all passing.

## ERRATUM RECORD (2026-07-28, found by the Lean formalization campaign — MovesSp E-audit)

§M-SPECIES, the entrance sub-catalogue display, the gloss bracket "into the μ=2
block: root▸(1,2) [R4/R5 rows]": the bracket omits R6. The note's own R6 row
displays "{(1,2),(1,1)}▸(1,2)" — a root (1,2)-selection letter — and the menu
law "▸(1,2) → Q2 letters" is row-unrestricted, so R6's ▸(1,2) row enters the
μ=2 block alongside R4/R5's. Corrected reading: "[the ▸(1,2) rows of
R4/R5/R6]". The head clause is correct as displayed; only the gloss bracket is
incomplete; NO count, menu, or gate quantity changes (the 53-catalogue, N*₃
thresholds, and all sealed censuses are unaffected). Full quoted verification:
MOVESSP_LEAN_BLUEPRINT_2026-07-28.md §9. Frozen text above left untouched per
house style; this record governs.


THE BLUEPRINT (REV 5):
# MOVESSP LEAN BLUEPRINT (2026-07-28) — the §M-SPECIES corpus, unit specs
# REV 5 (closing rev: Codex 1c/1g + Fable 0c/1g on rev 4 — the n = 1
# catalogue word WIRED into CanTreeModel (hN1 + Sp.n1Branch); thresholdData
# split one-display-each (6 units); succTerminal gains the C-3 domain; §7c)

# REV 4 (split-verdict adjudication: Codex REJECT 5c/8g vs Fable ACCEPT 0/0;
# per-finding dispositions at §7b — 11 Codex findings FIXED, 2 part-fixed with
# quoted pushback; Fable's two NOTES folded in)

REV 3 (Fable audit `lean/notes/MOVESSP_AUDIT_FABLE_2026-07-28.md`): C1 loops3
order corrected + an ORDER DISCIPLINE rule for every pinned-list decide target
(§4); C2 the ▸(1,2) entrance roster corrected to its TRUE three members per
group — the note-side bracket flagged as an erratum candidate (§9), verified,
never silently baked in; G1 collapseRuns pinned by its defining equations; G2
the n1 dependency cycle split; G3 the group-F fence retargeted to closure-side
objects only; G4 the non-detachability overclaim weakened to what the encoding
enforces. Table extended at §8.

# REV 2 (post-Codex-audit, 17 findings repaired)

REV 2 repairs ALL findings of `lean/notes/MOVESSP_AUDIT_CODEX_2026-07-28.md`
(6 crit / 11 gap): SP-COMP de-circularized over the `CanTreeModel` engine
interface with the note's full (n, p, f, η, r) quantifier prefix and D4R.0-K(c)
as the EXPLICIT field `hVerdictPin` (F1/F2/F7); `CatalogueWord` forces the halt
endpoint (F3); `EntranceShape` carries the block-entry datum + parameter slots
and feeds the finiteness theorem (F4); n = 3 data content-pinned (F5/F16/F17);
both R3 flank variants (F6); every binder/hypothesis spelled (F8–F14); the
(m, c) roster DEFERRED to MovesS (F15). Findings→repairs table at the end.

Campaign wave-1 blueprint (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md §5; unit-spec
format per §2). SOURCE OF TRUTH: `lean/notes/MOVES_2026-07-24.md`, the DUAL-ACCEPTED
rev-8 §M-SPECIES text (lines between `## §M-SPECIES` and `## §C: DUAL-ACCEPTED`;
acceptance record `## §M-SPECIES: DUAL-ACCEPTED (2026-07-27 — Codex pass 7 + the
Fable confirm ...)`). Every `moves_ref` below quotes that text. Corpus namespace
`LeanUrat.MovesSp`; files under `lean/LeanUrat/MovesSp/`.

## 0. Scope and conditionality (the note's own ledger, transposed)

DELIVERED BY THIS CORPUS (unconditional bookkeeping over ℕ/ℤ/Multiset — the note's
SP.5 ledger: "Unconditional given dual-accepted §B2-DEF (+ §C DOM via §D4-R L11 where
cited): SP.1's datum being well-typed, the (G1)–(G4) coherence, SP-FIN, SP-FIN′,
SP-OUT and its p-independence, the self-loop characterization, Lemma SP-DAG"):
the species datum structure; (G1)–(G6) + (B1)–(B5) as decidable predicates; the
closure 𝒮ₙ^raw; the shift map Sh + integrality; SP-FIN's catalogue bound; SP-DAG;
Out/V_term; the n = 3 layer (53 letters, menu map, loops) by `decide`.

CONDITIONAL, RIDING AS HYPOTHESES (never axioms, never silently strengthened):
- SP-COMP consumes the ENGINE (§B2-DEF D.4/D.5/D.7/D.8/D.10 read laws, §C DOM via
  §D4-R L11, §D4-R L2/L3/L5). Those live in Moves/MovesD/HC-1, not here. Lean form
  [REV 2, F1/F2]: the engine interface `CanTreeModel` (§2), whose FIELDS are the
  RAW per-read laws (root stage, StageLaws, coherence/budgets, halt, verdict pin)
  that SP-COMP's proof steps (1)–(3′)/(5) derive from the engine — the catalogue
  conclusions (InCatalogue/SuccStep/Out) occur in NO field; the corpus proves the
  closure absorbs any such tree, under the note's full (n, p, f, η, r) quantifier
  prefix. Discharging the fields = HC-1/MovesD territory.
- The D4R.0-K(c) residual (verdict pin: alphabet V + halting rule τ + detection cap,
  owner [3t] via VP) is an EXPLICIT hypothesis field [REV 2, F7]: `CanTreeModel.
  hVerdictPin` (§2) — the ⊥-read leaf-verdict law SP-COMP's step (4) consumes.
  `Verdict` stays three bare labels (no semantics: WHICH verdict, WHEN τ fires =
  VP's); the FIELD carries the residual, named, in every SP-COMP unit's
  hypothesis_fields. moves_ref: "SP-COMP's remaining conditionality is exactly the
  D4R.0-K(c) residual — the verdict pin …, owned by [3t] via VP — entering at step
  (4)'s leaf verdicts."
- §C's (SAE): DISCHARGED (rev-14 dual acceptance) — no hypothesis needed; recorded.
- N*₃ threshold data: DEFINITIONS only (the note: gate-censused data + a SEALED
  PREDICTION, "not a theorem of this note"). No realizability theorem is stated.
- p-independence: discharged BY TYPING — `SnRaw : ℕ → Set Species` mentions no
  prime (the note: "no field of the datum ... mentions p — the same list serves
  every prime"). No unit; recorded here as the faithfulness witness.

NOT IN SCOPE (SP.5): counts/masses ([1]/[1v]/[3]); realizability at a given p
(menus are SUPERSETS — SP.4's superset duty); state types/geometry ([2b]); read/
depth/ladder bounds (SP-DAG bounds LETTERS only; TRACK-COUNT stays open, uncited);
termination.

## 1. Design decisions (the decidable layer)

1. **Species = one flat structure over ℕ/Multiset/List, `deriving DecidableEq`.**
   [REV 4, Codex-6/NOTE A — the honest decidability statement: the Prop forms
   of (G4)/(B4)'s selection clauses (`∀ gm, s.sel = some gm → …`) have NO
   off-the-shelf Decidable instance (unbounded ∀ over the Eq-antecedent);
   Prop-side decidability is NOT claimed or used anywhere. EVERY decide target
   routes through the hand-written Bool reflection layer (coherentB/budgetB/
   succStepB/rootAdmissibleB, which `match` on s.sel) plus `decide (…)` for
   the two ambient Prop atoms (≤ on ℕ, list membership via DecidableEq) —
   never a Prop-to-Bool coercion, which Lean 4 does not have.]
   Fields exactly SP.1's retained tuple: tag, stage (D, w, W), side (e, s₀′, ℓ,
   census anchor a, digit count d, slot Finset), λ (Multiset (ℕ × ℕ)), selection
   (Option (ℕ × ℕ) — ⊥ = none, per the rev-3 retype "verdicts are NOT species"),
   two flank compositions (List ℕ). a/d/slots are FIELDS with (G2)/(G3) as
   RELATIONS (faithful to the note's tuple + coherence split), not derived defs.
   Heights (h_r, u*_r), depths, digit values: ABSENT — the note's FORGOTTEN list.
2. **Coherent/Budget/SuccStep as plain `Prop` conjunctions/matches, all decidable
   without instance gymnastics**, PLUS Bool reflection functions (`coherentB` etc.)
   with soundness iffs, so n = 3 facts kernel-`decide` over Bool — `native_decide`
   is BANNED (axiom fence: `Lean.ofReduceBool` is outside the allowed set).
3. **𝒮ₙ^raw as an inductive Prop closure** (`InCatalogue`): least set containing the
   coherent+admissible ROOT-stage tuples, closed under SuccStep — literally the
   rev-3 definition. Finiteness/decidability recovered via (a) the SP-FIN encoding
   injection, (b) a GENERATED enumeration `speciesEnum n : List Species` (coherent-
   by-construction candidates; a/d/slots computed from (s₀′, e, ℓ)) with a
   completeness lemma, making the n = 3 catalogue equality a closure induction over
   `decide`-checked base/step facts.
4. **Two coordinate systems**: census fields live in the letter; the shift block is
   a pure-ℤ lemma family (`Int.fdiv`, e ≥ 1) with hypotheses NAMED to match
   `Moves.Stage` (e h s t, hbez, he1t) + one bridging corollary consuming an actual
   `σ : Moves.Stage p F` (reuse, not duplication — the only Stage-typed unit).
   `R_anch` shift-invariance reuses `Moves.HasAnchorK` verbatim.
5. **Rank for SP-DAG as a mixed-radix ℕ** (order-isomorphic to the note's lex
   4-tuple on the bounded ranges), so the collapsed-walk bound is "strictly
   increasing ℕ-list below 6n² has length ≤ 6n²".
6. **Perf fences for `decide`**: enum generated with dependent bounds (n = 3 raw
   size ~2–3k, letters' numerals ≤ 7); decide targets phrased as `List.all … =
   true`; the three enum-quantified checks split PER STAGE GROUP (R/Q3/Q2/Q1/I) if
   a single decide exceeds ~60s kernel time. Fallback beyond that: designer round
   (statement-fence: additive helper lemmas only). NEVER native_decide.

## 2. Proposed `MovesSp/Defs.lean` skeleton (structures/defs only, no proofs)

```lean
import Mathlib
import LeanUrat.Moves.Defs   -- reuse: HasAnchorK, Stage (bridging unit only)

namespace LeanUrat.MovesSp

/-- (tag) the read's position class (SP.1): ROOT / POST-INC / POST-REC. -/
inductive Tag | root | postInc | postRec deriving DecidableEq, Repr

/-- SP.1's species datum: the retained, value-free, height-free fields of one read.
Heights (h_r, u*_r), depths, digit values, lifts: FORGOTTEN by design. -/
structure Species where
  tag : Tag
  D : ℕ            -- current key degree
  w : ℕ            -- pool residue degree
  W : ℕ            -- window width
  e : ℕ            -- stride e = e_read
  s0 : ℕ           -- raw left endpoint s₀′
  ell : ℕ          -- normalized side length ℓ = w′/e = deg R_anch
  a : ℕ            -- CENSUS anchor ⌊s₀′/e⌋  ((SH-C); (G2) is the relation)
  d : ℕ            -- digit count = #slots   ((G3) pins d = ℓ + 1)
  slots : Finset ℕ -- census slot set {p̂_k} ((G3) pins {a, …, a+ℓ})
  lam : Multiset (ℕ × ℕ)   -- residual partition λ = {(g⁽ⁱ⁾, μ⁽ⁱ⁾)}
  sel : Option (ℕ × ℕ)     -- selection (g, μ) ∈ λ, or ⊥ = none (rev-3 retype)
  lflank : List ℕ  -- left flank composition (composition of span s₀′)
  rflank : List ℕ  -- right flank composition (span W − s₀′ − w′)
deriving DecidableEq, Repr

namespace Species
/-- raw side width w′ = e·ℓ. -/
def wraw (s : Species) : ℕ := s.e * s.ell
end Species

/-- `c` is a composition of `span`: positive parts summing to `span` ([] ↔ span 0). -/
def IsComposition (c : List ℕ) (span : ℕ) : Prop := (∀ x ∈ c, 1 ≤ x) ∧ c.sum = span

/-- Structural positivity (typing: D, w, W, e, ℓ ≥ 1; λ-parts positive). -/
def WellTyped (s : Species) : Prop :=
  1 ≤ s.D ∧ 1 ≤ s.w ∧ 1 ≤ s.W ∧ 1 ≤ s.e ∧ 1 ≤ s.ell ∧
    ∀ gm ∈ s.lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2

/-- (G1)–(G4)+(G6), stated in CENSUS coordinates (rev 4). (G5) is `SuccStep`. -/
def Coherent (s : Species) : Prop :=
  WellTyped s ∧
  -- (G1) FLANK–SPAN: left span = s₀′; s₀′ + w′ + right span = W
  (IsComposition s.lflank s.s0 ∧ s.s0 + s.wraw + s.rflank.sum = s.W ∧
     ∀ x ∈ s.rflank, 1 ≤ x) ∧
  -- (G2) ANCHOR–POSITION (census): a = ⌊s₀′/e⌋
  (s.a = s.s0 / s.e) ∧
  -- (G3) SLOT-SET: {p̂_k} = {a, …, a+ℓ}, d = ℓ + 1
  (s.slots = Finset.Icc s.a (s.a + s.ell) ∧ s.d = s.ell + 1) ∧
  -- (G4) RESIDUAL–SELECTION: Σ g⁽ⁱ⁾μ⁽ⁱ⁾ = ℓ; selection ∈ λ or ⊥
  ((s.lam.map fun gm => gm.1 * gm.2).sum = s.ell ∧
     ∀ gm, s.sel = some gm → gm ∈ s.lam) ∧
  -- (G6) TERMINAL RULE: selection = ⊥ iff W = 1
  (s.sel = none ↔ s.W = 1)

/-- (B1)–(B5), the PER-TUPLE budget clauses ((B1)/(B2)'s recursions live in
`SuccStep`; the anchor clause is the rev-3/4 CENSUS bound). -/
def Budget (n : ℕ) (s : Species) : Prop :=
  s.D ≤ n ∧ s.w ≤ n ∧                                     -- (B1)/(B2) caps
  (s.s0 + s.wraw ≤ s.W ∧ s.a + s.ell ≤ s.W ∧
     s.d ≤ s.wraw + 1 ∧ s.W ≤ n / s.D) ∧                  -- (B3)
  (∀ gm, s.sel = some gm → gm.1 * gm.2 ≤ s.ell) ∧          -- (B4)
  (s.e ≤ n ∧ s.ell ≤ n ∧ s.s0 ≤ n ∧ s.d ≤ n + 1 ∧ s.W ≤ n ∧
     (∀ gm ∈ s.lam, gm.1 ≤ n ∧ gm.2 ≤ n) ∧
     s.e ≤ s.wraw ∧ s.a ≤ (s.W - s.wraw) / s.e)            -- (B5, census anchor)

/-- ROOT stage pin ((G5) root clause): tag = ROOT forces (D, w, W) = (1, 1, n). -/
def RootStage (n : ℕ) (s : Species) : Prop :=
  s.tag = .root ∧ s.D = 1 ∧ s.w = 1 ∧ s.W = n

def RootAdmissible (n : ℕ) (s : Species) : Prop :=
  RootStage n s ∧ Coherent s ∧ Budget n s

/-- The RAW per-read stage laws (SP-COMP steps (2)/(5): the D.5/D.6/D.7/D.8/D.10
outputs — D′ = e·g·D, w′ = g·w, W′ = μ, tag′ = POST-INC iff e·g ≥ 2, POST-REC iff
e = g = 1). NO coherence/budget clause: the ENGINE-facing half, so the catalogue's
SuccStep is never assumed where it must be concluded [REV 2, F1]. `match` (not ∃)
keeps it decidable. -/
def StageLaws (s s' : Species) : Prop :=
  match s.sel with
  | none => False
  | some (g, μ) =>
      s'.D = s.e * g * s.D ∧ s'.w = g * s.w ∧ s'.W = μ ∧
      (s'.tag = .postInc ↔ 2 ≤ s.e * g) ∧
      (s'.tag = .postRec ↔ (s.e = 1 ∧ g = 1))

/-- SP.4's SUCC clause = (G5)'s generation rule: the stage laws AND the target
coherent and budget-admissible. -/
def SuccStep (n : ℕ) (s s' : Species) : Prop :=
  StageLaws s s' ∧ Coherent s' ∧ Budget n s'

/-- 𝒮ₙ^raw (rev 3): the LEAST set containing every coherent, admissible ROOT-stage
tuple, closed under (G5)'s generation rule — an inductive Prop closure. -/
inductive InCatalogue (n : ℕ) : Species → Prop
  | root {s} : RootAdmissible n s → InCatalogue n s
  | step {s s'} : InCatalogue n s → SuccStep n s s' → InCatalogue n s'

def SnRaw (n : ℕ) : Set Species := {s | InCatalogue n s}

/-- V_term (SP.4, rev 3): three BARE labels, disjoint from Species. No fields, no
budgets, no menus; semantics owned by [3t]'s VP — deliberately absent here. -/
inductive Verdict | z | ep | ns deriving DecidableEq, Repr

/-- SUCC(s) ⊆ 𝒮ₙ^raw (SP.4); ∅ for terminal s (sel = none ⇒ SuccStep is False). -/
def Succ (n : ℕ) (s : Species) : Set Species :=
  {s' | InCatalogue n s' ∧ SuccStep n s s'}

/-- Out(s) := SUCC(s) ∪ V_term (disjoint union via Sum). -/
def Out (n : ℕ) (s : Species) : Set (Species ⊕ Verdict) :=
  (Sum.inl '' Succ n s) ∪ (Sum.inr '' Set.univ)

/-! ### The two coordinate systems and the shift map (SP.1's shift block) -/

/-- σ := ⌊t·γ/e⌋ (floor division: `Int.fdiv`). -/
def shSigma (t γ e : ℤ) : ℤ := (t * γ).fdiv e

/-- (SH) Sh_{t,γ} : ℤ → ℤ, p ↦ p + σ. -/
def Sh (t γ e : ℤ) (pz : ℤ) : ℤ := pz + shSigma t γ e

/-- (SH-G) the geometric position p_j(γ) = (j − t·γ)/e (D.3(c)); exact division on
on-line slots (the integrality lemma), `fdiv` as the total function. -/
def geoPos (e t γ j : ℤ) : ℤ := (j - t * γ).fdiv e

/-! ### SP-DAG rank and fullness -/

def tagord : Tag → ℕ | .root => 0 | .postInc => 1 | .postRec => 2

/-- FULL letter (SP-DAG): selection = (1, W). By (G6) full letters live at W ≥ 2. -/
def IsFull (s : Species) : Prop := s.sel = some (1, s.W)

/-- The rank's last coordinate "1 − [s is full]", as a ℕ [REV 2, F14]. -/
def fullBit (s : Species) : ℕ := if s.sel = some (1, s.W) then 0 else 1

/-- ρ(s) = (D, tagord, n − W, 1 − [full]) as a mixed-radix ℕ, order-isomorphic to
the note's lex tuple on catalogue ranges (D ∈ [1,n], tagord < 3, n − W < n,
bit < 2); rankNat < 6n² on catalogue members. -/
def rankNat (n : ℕ) (s : Species) : ℕ :=
  (((s.D - 1) * 3 + tagord s.tag) * n + (n - s.W)) * 2 + fullBit s

/-- A collapsed walk: consecutive SuccStep edges with self-loops struck (rev 3:
"the collapsed LETTER length of a walk"). -/
def CollapsedWalk (n : ℕ) (l : List Species) : Prop :=
  (∀ s ∈ l, InCatalogue n s) ∧ l.Chain' (fun s s' => SuccStep n s s' ∧ s ≠ s')

/-! ### SP-COMP interface [REV 2, F1/F2/F3/F4/F7 — de-circularized] -/

/-- THE ENGINE INTERFACE: an abstract canonical tree over a fixed (p, f) with
per-read retained data. EVERY field is an OPEN engine law, cited to the note's
SP-COMP proof step that derives it from §B2-DEF/§C DOM/§D4-R (owner HC-1/MovesD);
NONE is proved in this corpus, and the catalogue conclusions (`InCatalogue`,
`SuccStep`, `Out`-membership) appear in NO field — they are what the SP-COMP
units derive by closure induction. -/
structure CanTreeModel (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p]) where
  /-- η ∈ T_can(f): the chains (§D4-R L2 — "terminal-verdict branches and
  infinite branches alike, prefixwise"); abstract here. -/
  Branch : Type
  /-- TOTALITY PIN [REV 4, Codex-1]: T_can(f) is nonempty — "kernel D4R.0-K
  parts (a) totality … are DISCHARGED (D4R0K_DERIVATION rev 3, dual-verified
  2026-07-27)"; the EMPTY model now violates a field. -/
  hTotal : Nonempty Branch
  /-- length of η's CATALOGUE WORD in ℕ∞ [REV 4, Codex-1 — infinite branches
  are REPRESENTED: len η = ⊤ is the prefixwise-catalogued infinite chain
  ("Infinite branches are catalogued prefixwise", SP.5). len η = 0 stays a
  REAL case AT n ≥ 2 ("(τ-hen) ROOT HENSEL LEAVES — … halts with NO window
  read ever opened": a Hensel track below a SPLIT f̄ carries no catalogue
  letter). REFINED at REV 5 (Codex rev-4 crit — the conflation conceded AT
  n = 1): at n = 1 the note's word is NONEMPTY — see hN1.] -/
  len : Branch → ℕ∞
  /-- THE n = 1 CLAUSE AS A MODEL LAW [REV 5, Codex rev-4 crit]: "At n = 1 the
  catalogue word is the single ROOT letter (W = n = 1, selection ⊥ — (G6)'s
  degenerate degree)" — only the τ-WORD is empty. So at n = 1 no branch has an
  empty catalogue word; the all-len-0 CanTreeModel at n = 1 now VIOLATES this
  field. Stated as nonemptiness only: len η = 1 and datum η 0 = the confirming
  root letter are then DERIVED (Sp.n1Branch) via hRoot + hHalt + n1singleton —
  the minimal field carrying the display. -/
  hN1 : n = 1 → ∀ η, 0 < len η
  /-- the retained datum of read r < len η (junk above). -/
  datum : Branch → ℕ → Species
  /-- step (1)+(3)+(3′) at r = 0: root stage (D, w, W) = (1, 1, n), datum
  coherent and budget-admissible [§B2-DEF D.0 key x; §D4-R L3/L5; §C DOM]. -/
  hRoot : ∀ η, 0 < len η →
    RootStage n (datum η 0) ∧ Coherent (datum η 0) ∧ Budget n (datum η 0)
  /-- steps (2)/(5): the raw stage laws per consecutive read pair ["the stage
  fields of read r+1 are the D.7/D.8/D.10 outputs"]. -/
  hStage : ∀ η (r : ℕ), (r + 1 : ℕ∞) < len η →
    StageLaws (datum η r) (datum η (r + 1))
  /-- steps (3)+(3′) at every read: budgets and coherence ["Budgets hold at
  every read" / "Geometric coherence holds at every read"]. -/
  hCoh : ∀ η (r : ℕ), (r : ℕ∞) < len η →
    Coherent (datum η r) ∧ Budget n (datum η r)
  /-- the catalogue-word endpoint: the word closes AT its first confirming
  W = 1 read [SP-COMP: "up to and including its first W = 1 read"]. -/
  hHalt : ∀ η (r : ℕ), (r : ℕ∞) < len η → (datum η r).W = 1 →
    len η = (r + 1 : ℕ∞)
  /-- step (4): the leaf verdict of a FINITELY-ENDED chain, from V_term. -/
  verdict : Branch → Option Verdict
  /-- step (4)'s law — THE D4R.0-K(c) RESIDUAL AS AN EXPLICIT, NAMED RIDER
  [REV 2 F7; REV 4, Codex-2 — scope WIDENED to every finite nonempty word:
  the note ends words at terminal ⊥-reads AND at V_term edges from CONTINUING
  letters ("Edges into V_term from a CONTINUING letter … end both words at
  that letter"), and in both cases "the chain's τ-leaf carries that verdict";
  infinite branches (len = ⊤) carry none]. HONEST PERIMETER (the G4 record
  stands): the field carries the residual's ALPHABET (V_term as codomain) and
  its ATTACHMENT SITE (finite words), NOT the halting rule τ or the uniform
  detection cap — those are the kernel's CONTENT, owned by [3t] via VP and
  deliberately not encodable from §M-SPECIES's text; the field is the
  ledger's named carrier, weak by design, trivially dischargeable, and every
  SP-COMP unit's hypothesis_fields says so. -/
  hVerdictPin : ∀ η (m : ℕ), len η = (m : ℕ∞) → 0 < m → (verdict η).isSome

/-- A CATALOGUE WORD (SP-COMP's quantifier + SP.4's HALT CONVENTION) [REV 2,
F3]: letters in 𝒮ₙ^raw, Out-linked, and FORCED to close at the FIRST confirming
W = 1 read — the endpoint is a structure law, not an antecedent. (Words ended by
a V_term edge from a CONTINUING letter, and infinite branches, are catalogued
prefixwise via `CanTreeModel`, not by this structure.) -/
structure CatalogueWord (n : ℕ) where
  word : List Species
  hne : word ≠ []
  hMem : ∀ s ∈ word, InCatalogue n s
  hChain : word.Chain' (SuccStep n)
  /-- the last letter IS confirming: W = 1 (hence sel = ⊥ by (G6)). -/
  hLast : ∀ s, word.getLast? = some s → s.W = 1
  /-- …and it is the FIRST confirming read: no earlier letter has W = 1. -/
  hFirstW1 : ∀ s ∈ word.dropLast, s.W ≠ 1

/-- The τ-WORD: the catalogue word minus its final confirming letter (SP.4; at
n = 1 the empty word). -/
def CatalogueWord.tauWord {n : ℕ} (cw : CatalogueWord n) : List Species :=
  cw.word.dropLast

/-- Collapse self-loop runs: keep one letter per maximal run of equal
consecutive letters (the depth direction struck). PINNED by its defining
equations [REV 3, G1 — the const-[] degenerate satisfier is excluded: it
violates the singleton equation]. Equals `List.destutter (· ≠ ·)`. -/
def collapseRuns : List Species → List Species
  | [] => []
  | [s] => [s]
  | s :: s' :: rest =>
      if s = s' then collapseRuns (s' :: rest)
      else s :: collapseRuns (s' :: rest)

/-- An ENTRANCE SHAPE into a block entry [REV 2, F4]: an Out-linked word in
𝒮ₙ^raw whose LAST letter is the block-entry read with DESIGNATED continuing
selection (g, μ) — the size-e block/landing-cell β₀ identification of that
datum is [1v] CTS-M(iii)'s, cited as owner — carrying its height-pair
ℕ-parameter SLOTS (§D4-R L3 rev 9's (h_r, u*_r); bare data, no [2a] law) and
one depth slot per maximal self-loop run. -/
structure EntranceShape (n gsel μsel : ℕ) where
  word : List Species
  hne : word ≠ []
  hMem : ∀ s ∈ word, InCatalogue n s
  hChain : word.Chain' (SuccStep n)
  /-- the last letter's designated continuing branch: selection (gsel, μsel). -/
  hEntry : ∀ s, word.getLast? = some s → s.sel = some (gsel, μsel)
  /-- height-pair parameter slots (h_r, u*_r), one per read — data only. -/
  heights : Fin word.length → ℕ × ℕ
  /-- depth parameter slots, one per maximal self-loop run — data only. -/
  depths : Fin (collapseRuns word).length → ℕ

/-! ### CTS bridge (typing only) -/

/-- The plan's bounded current-state skeleton (SP.4's bridge display, typing
only): "stage (D, w, W) + tag (the tower phase) + anchor a + the residual
partition λ" — values forgotten. -/
def stateSkeleton (s : Species) : Tag × (ℕ × ℕ × ℕ) × ℕ × Multiset (ℕ × ℕ) :=
  (s.tag, (s.D, s.w, s.W), s.a, s.lam)

/- [REV 2, F15 — DEFERRAL RECORD] The rev-1 (m, c)-roster defs (mOf, cOf,
OutcomeClass, outcomeClass) and unit Sp.mcRoster are STRUCK from this corpus:
their sole anchor, the (m, c) CLASSIFICATION rows, is a display of §S-RESUM's
(K-SUB), NOT of the frozen §M-SPECIES text — no in-scope moves_ref exists.
They move to the MovesS blueprint (wave 4), where (K-SUB) is ground truth;
MovesS may define them on this corpus's `Species.lam` field (the import is
additive). Recorded also at §6/§7. -/

end LeanUrat.MovesSp
```

Bool reflection (`coherentB budgetB rootAdmissibleB succStepB : … → Bool`, literal
Bool transcriptions) and the generated enumeration (`compEnum : ℕ → List (List ℕ)`,
`lamEnum : ℕ → ℕ → List (Multiset (ℕ × ℕ))` [bound n, weight ℓ], `speciesEnum : ℕ →
List Species`) live in `MovesSp/DefsEnum.lean`; the n = 3 letters + data tables in
`MovesSp/DefsN3.lean` (§4 below).

## 3. `MovesSp/DefsEnum.lean` sketch (defs only)

```lean
/-- All compositions of `span` (positive parts, ordered). compEnum 0 = [[]]. -/
def compEnum : ℕ → List (List ℕ)          -- recursion on span
/-- All multisets of pairs (g, μ), 1 ≤ g, μ ≤ bound, with Σ g·μ = weight. -/
def lamEnum (bound weight : ℕ) : List (Multiset (ℕ × ℕ))
/-- Generated candidates: for tag/D/w/W/e/s0/ell in dependent bounds, lam ∈ lamEnum,
sel ∈ none :: (lam.toList.map some), flanks ∈ compEnum; a := s0/e, d := ell + 1,
slots := Finset.Icc a (a + ell) COMPUTED (coherent-by-construction on (G2)/(G3)). -/
def speciesEnum (n : ℕ) : List Species
def coherentB (s : Species) : Bool
def budgetB (n : ℕ) (s : Species) : Bool
def rootAdmissibleB (n : ℕ) (s : Species) : Bool
def succStepB (n : ℕ) (s s' : Species) : Bool
-- [REV 4, Codex-6] Bool routing conventions, binding on every decide target:
--   list membership   → `l.contains x`  (BEq Species := instBEqOfDecidableEq)
--   ℕ-inequalities    → `decide (a ≤ b)`
--   Option tests      → `o.isSome` / `o == some v`
-- NEVER `(P : Bool)` on a Prop — Lean 4 has no Prop→Bool coercion.
```

## 4. `MovesSp/DefsN3.lean` sketch (defs only — the SEALED n = 3 data)

```lean
/-- The 53 letters (SP.6's hand catalogue, exhaustive; grouped R/Q3/Q2/Q1/I).
Helper constructors keep each row one line (e.g. `mkRoot e s0 ell lam sel lf rf`). -/
def groupR : List Species    -- 21 rows: R1..R8 with flank/λ▸sel variants
def groupQ3 : List Species   -- 21: the R rows retagged postRec, stage (1,1,3)
def groupQ2 : List Species   -- 6: Q2.1, Q2.2, Q2.3 (3 λ▸sel rows), Q2.4
def groupQ1 : List Species   -- 1: confirming ⊥ letter, stage (1,1,1)
def groupI  : List Species   -- 4: confirming ⊥ letters, stages (2,1),(2,2),(3,1),(3,3), W = 1
def catalogue3 : List Species := groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI
/-- The sealed menu map (SP.6): ▸(1,1)→Q1; ▸(1,2)→Q2; ▸(1,3)→Q3; ▸(2,1)→I(2,2);
▸(3,1)→I(3,3); e=2→I(2,1); e=3→I(3,1); terminal→[]. By selection/stride match. -/
def menuMap3 (s : Species) : List Species
/-- NAMED LETTERS consumed by unit statements [REV 2, F5/F6/F17 — no positional
or cardinality-only references]. Each is an explicit `Species` literal. -/
def loopQ23 : Species   -- Q2.3's {(1,2)}▸(1,2) row (the μ = 2 loop)
def loopQ3  : Species   -- Q3(R6)'s {(1,3)}▸(1,3) row (the μ = 3 loop)
def R3letterA : Species -- R3, left flank [2]      [F6: BOTH variants]
def R3letterB : Species -- R3, left flank [1, 1]   [F6]
def rootR4sel12 : Species -- R4's {(1,2)}▸(1,2) row
def rootR5sel12 : Species -- R5's {(1,2)}▸(1,2) row
def rootR6sel12 : Species -- R6's {(1,2),(1,1)}▸(1,2) row [REV 3, C2/§9]
def rootR6sel13 : Species -- R6's {(1,3)}▸(1,3) row
def letterI21 : Species -- I, stage (D,w) = (2,1)  (via e = 2 sides)
def letterI22 : Species -- I, stage (2,2)          (via ▸(2,1))
def letterI31 : Species -- I, stage (3,1)          (via e = 3)
def letterI33 : Species -- I, stage (3,3)          (via ▸(3,1))
/-- The six multi-side μ = 3 letters (SP.6's SIX COMPUTATIONS), BY NAME:
"Q3(R1, right flank (1,1)), Q3(R2), Q3(R3, left flank (1,1)), and the three
Q3(R4) λ-rows". -/
def msQ3R1 : Species  -- Q3(R1)-copy, right flank [1, 1];  N*₃ = 7
def msQ3R2 : Species  -- Q3(R2)-copy;                       N*₃ = 6
def msQ3R3 : Species  -- Q3(R3)-copy, left flank [1, 1];    N*₃ = 6
def msQ3R4a : Species -- Q3(R4), λ = {(2,1)} ▸ (2,1);       N*₃ = 6
def msQ3R4b : Species -- Q3(R4), λ = {(1,2)} ▸ (1,2);       N*₃ = 6
def msQ3R4c : Species -- Q3(R4), λ = {(1,1)²} ▸ (1,1);      N*₃ = 6
def multiSide6 : List Species := [msQ3R1, msQ3R2, msQ3R3, msQ3R4a, msQ3R4b, msQ3R4c]
/-- λ's demand for distinct nonzero roots (the field-size criterion): the number
of monic-linear factors, WITH multiset multiplicity ("nonzero by the endpoint
convention: a is split off, so z ∤ R_anch"). -/
def linCount (s : Species) : ℕ := Multiset.card (s.lam.filter fun gm => gm.1 = 1)
/-- Field-size exclusion lists as LITERAL lists of named letters [F5]; their
λ-content is PINNED by Sp.n3exclusionLists' filter identities (q = 2: ≥ 2
distinct linears, q = 3: ≥ 3), not by cardinality. -/
-- [REV 4, Codex-9/12] literal bodies + row-named letters (order = catalogue3):
def exR4c : Species   -- R4 {(1,1)²}▸(1,1) row          (groupR)
def exR5c : Species   -- R5 {(1,1)²}▸(1,1) row          (groupR)
def exR6b12 : Species -- R6 {(1,2),(1,1)}▸(1,2) row (= rootR6sel12)
def exR6b11 : Species -- R6 {(1,2),(1,1)}▸(1,1) row
def exR6t : Species   -- R6 {(1,1)³}▸(1,1) row
def exQ3R4c : Species -- Q3 copy of exR4c
def exQ3R5c : Species -- Q3 copy of exR5c
def exQ3R6b12 : Species ; def exQ3R6b11 : Species ; def exQ3R6t : Species
def exQ23c : Species  -- Q2.3 {(1,1)²}▸(1,1) row        (groupQ2)
def fieldSizeExcluded2 : List Species :=
  [exR4c, exR5c, exR6b12, exR6b11, exR6t,
   exQ3R4c, exQ3R5c, exQ3R6b12, exQ3R6b11, exQ3R6t, exQ23c]   -- 11
def fieldSizeExcluded3 : List Species := [exR6t, exQ3R6t]     -- 2
def confirmingRoot1 : Species :=          -- [REV 4, Codex-12] the n = 1 letter
  ⟨.root, 1, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩
/- ORDER DISCIPLINE [REV 3, C1 — this bug class repeats]: every literal list
that a unit equates with a `catalogue3.filter …` (or `groupX.filter …`) MUST
list its members in catalogue3 order — groups R → Q3 → Q2 → Q1 → I, and within
a group in the displayed row order — because `List.filter` preserves order and
Nodup pins one occurrence each. Audit of all pinned-list targets under this
rule: fieldSizeExcluded2/3 (declared here in catalogue3 order), loops3
([loopQ3, loopQ23] — Q3 before Q2), terminal3 (groupQ1 ++ groupI ✓),
entrance3_patterns' groupR filter ([rootR4sel12, rootR5sel12, rootR6sel12] —
R4 < R5 < R6 ✓); all other n = 3 targets are membership/`all` forms,
order-free. -/
/-- N*₃ on the six (SP.6): per-NAME table, `none` off multiSide6. -/
def Nstar3six : Species → Option ℕ
```

## 5. Unit specs

Format per campaign §2: id · file (`lean/LeanUrat/MovesSp/<id>.lean`) · statement ·
moves_ref (≤ 3 lines, from the rev-8 text) · deps (Defs* always implicit) · sketch ·
difficulty · hypothesis_fields (DEFAULT: none — unconditional bookkeeping per SP.5's
ledger; only deviations are listed).

### A. Reflection and closure basics

**Sp.reflCoherent** · SP0_reflCoherent.lean
statement: `theorem coherentB_iff (s : Species) : coherentB s = true ↔ Coherent s`
moves_ref: "(G1)–(G6) … A species tuple is GEOMETRICALLY COHERENT iff" (the display).
deps: — · sketch: unfold both; `decide`-friendly Bool/Prop transcription, `simp
[coherentB, Coherent, List.all_eq_true, …]`. · difficulty: easy

**Sp.reflBudget** · SP0_reflBudget.lean
statement: `theorem budgetB_iff (n : ℕ) (s : Species) : budgetB n s = true ↔ Budget n s`
moves_ref: "(B1)–(B5) are inequalities between INTEGERS attached to shape fields".
deps: — · sketch: as reflCoherent. · difficulty: easy

**Sp.reflSucc** · SP0_reflSucc.lean
[REV 2, F8 — both statements in full]
statement: `theorem succStepB_iff (n : ℕ) (s s' : Species) :
succStepB n s s' = true ↔ SuccStep n s s'` AND
`theorem rootAdmissibleB_iff (n : ℕ) (s : Species) :
rootAdmissibleB n s = true ↔ RootAdmissible n s`
moves_ref: "SUCC(s) := { s′ ∈ 𝒮_n^raw : D(s′) = e·g·D, w(s′) = g·w, W(s′) = μ, …}"
and "(G5) STAGE REACHABILITY: tag = ROOT forces (D, w, W) = (1, 1, n)" (the
root-admissibility face).
deps: Sp.reflCoherent, Sp.reflBudget · sketch: match on sel (the StageLaws half);
And-transport with the two reflection iffs; rootAdmissibleB_iff = the RootStage
equality checks + the same transport. · difficulty: easy

**Sp.succTerminal** · SP0_succTerminal.lean
statement: `theorem succ_terminal (n : ℕ) (s : Species)
(hs : InCatalogue n s) (h : s.sel = none) : Succ n s = ∅` AND
`theorem stageLaws_terminal (s s' : Species) (h : s.sel = none) :
¬ StageLaws s s'` [REV 2: second statement in full; REV 5, Fable rev-4 gap —
hs added per the C-3 pattern: the clause sits inside SP.4's catalogue-scoped
definition block, and hs is faithfulness-only, unused by the proof;
stageLaws_terminal stays unrestricted (corpus-internal bookkeeping)]
moves_ref: "For s ∈ 𝒮_n^raw, the OUTGOING MENU Out(s) ⊆ 𝒮_n^raw ∪ V_term …
and SUCC(s) := ∅ for terminal s (selection ⊥)."
deps: — · sketch: unfold StageLaws; the match's none-branch is False; Succ empty
via its StageLaws conjunct. · difficulty: easy

**Sp.memCoherent** · SP0_memCoherent.lean
statement: `theorem InCatalogue.coherent_budget {n s} (h : InCatalogue n s) :
Coherent s ∧ Budget n s`
moves_ref: "the least set … that contains every (G1)–(G4)+(G6)-coherent,
(B1)–(B5)-admissible ROOT-stage tuple … (each generated tuple again … admissible)".
deps: — · sketch: induction on h; both constructors carry the conjuncts.
difficulty: easy

### B. The two coordinate systems and the shift map (SP.1's shift block)

Pure-ℤ units; hypothesis names mirror `Moves.Stage` fields (hbez ↔ `hbez`, e = 1 ⇒
t = 0 ↔ `he1t`) so the bridging unit is verbatim.

**Sp.shCongr** · SP1_shCongr.lean
statement: `theorem sh_congr (e h s t γ u0 s0 : ℤ) (hbez : e * s + h * t = 1)
(hγ : γ = e * u0 + s0 * h) : t * γ ≡ s0 [ZMOD e]`
moves_ref: "with u₀ := the left endpoint's height, γ = e·u₀ + s₀′·h, so modulo e
t·γ ≡ t·h·s₀′ ≡ (1 − e·s)·s₀′ ≡ s₀′".
deps: — · sketch: substitute hγ; t·γ − s₀′ = e·(t·u0) + s₀′·(t·h − 1) =
e·(t·u0 − s₀′·s); `Int.ModEq` via dvd, `ring_nf`. · difficulty: easy

**Sp.shDvd** · SP1_shDvd.lean
[REV 2, F9 — binders in full]
statement: `theorem sh_dvd (e h s t γ u0 s0 : ℤ) (hbez : e * s + h * t = 1)
(hγ : γ = e * u0 + s0 * h) (k : ℤ) : e ∣ (s0 + k * e - t * γ)`
(no `1 ≤ e` hypothesis: pure divisibility, degenerate e included)
moves_ref: "(SH-G) p_j(γ) = (j − t·γ)/e ∈ ℤ (D.3(c))" [j = j_k = s₀′ + k·e].
deps: Sp.shCongr · sketch: s0 − t·γ ≡ 0 [ZMOD e] from shCongr; add k·e.
difficulty: easy

**Sp.shSlots** · SP1_shSlots.lean
[REV 2, F10 — binders in full, both theorems]
statement: `theorem sh_slots (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e)
(hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) (k : ℤ) :
Sh t γ e (geoPos e t γ (s0 + k * e)) = s0.fdiv e + k` AND
`theorem sh_anchor (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e)
(hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) :
Sh t γ e (geoPos e t γ s0) = s0.fdiv e` (= sh_slots at k = 0)
moves_ref: "p_{j_k} + σ = (j_k − t·γ)/e + (t·γ − (s₀′ mod e))/e = … = ⌊s₀′/e⌋ + k;
k = 0 is the anchor identity."
deps: Sp.shDvd · sketch: fdiv-additivity on the exact divisions (shDvd + the σ
congruence give both remainders); `Int.add_mul_fdiv_right`, `omega` after
extracting the two dvd witnesses. · difficulty: medium

**Sp.shE1** · SP1_shE1.lean
statement: `theorem sh_e1 (h s t γ s0 : ℤ) (ht : t = 0) :
shSigma t γ 1 = 0 ∧ Sh t γ 1 (geoPos 1 t γ s0) = s0`
moves_ref: "At e = 1: t = 0 ((P2)), σ = 0 — THE SYSTEMS COINCIDE (a = a^geo = s₀′
= ord_z R; FC4's e = 1 clause)."
deps: — · sketch: `simp [shSigma, Sh, geoPos, Int.fdiv_one, ht]`. · difficulty: easy

**Sp.shEquiv** · SP1_shEquiv.lean
[REV 2, F11 — the spurious hypothesis struck; both statements in full]
statement: `def shEquiv (σ : ℤ) : ℤ ≃ ℤ := Equiv.addRight σ` +
`theorem sh_image (t γ e ag : ℤ) (ℓ : ℕ) :
(Finset.Icc ag (ag + ℓ)).image (Sh t γ e) = Finset.Icc (ag + shSigma t γ e)
(ag + shSigma t γ e + ℓ)` (pure interval translation — NO extra hypothesis) AND
the census identification `theorem sh_geo_slots (e h s t γ u0 s0 : ℤ)
(he : 1 ≤ e) (hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) (ℓ : ℕ) :
(Finset.image (fun k : Fin (ℓ + 1) => Sh t γ e (geoPos e t γ (s0 + k * e)))
Finset.univ) = Finset.Icc (s0.fdiv e) (s0.fdiv e + ℓ)` (the geometric slot set
carried onto the census slot set)
moves_ref: "Sh_{t,γ} is an affine bijection carrying the geometric slot set onto
the census slot set and a^geo onto a, ALL OTHER FIELDS FIXED".
deps: Sp.shSlots (for sh_geo_slots) · sketch: sh_image by
`Finset.image_add_right_Icc`; sh_geo_slots: rewrite each image point by
Sp.shSlots, then Fin-indexed image of k ↦ a + k is the Icc. · difficulty: easy

**Sp.shAnchorInv** · SP1_shAnchorInv.lean
statement: `theorem hasAnchorK_T_mul {K : Type*} [Field K] (x : LaurentPolynomial K)
(a σ : ℤ) (R : Polynomial K) (h : Moves.HasAnchorK x a R) :
Moves.HasAnchorK (LaurentPolynomial.T σ * x) (a + σ) R`
moves_ref: "the anchored residual is SHIFT-INVARIANT: R_anch := z^{−ord_z R}·R =
Σ_k c_{j_k}·z^k in BOTH displays (relabeling p ↦ p + σ multiplies R by z^σ, which
the anchoring cancels), so λ, the selection, and ℓ = deg R_anch never see σ."
deps: — (REUSES `Moves.HasAnchorK` — the corpus-link unit) · sketch: unfold
HasAnchorK; `LaurentPolynomial.T_add`, `mul_assoc`. · difficulty: medium

**Sp.shStage** · SP1_shStage.lean
[REV 2, F12 — the corollary spelled in full]
statement: `theorem sh_congr_stage {p : ℕ} {F : Type u} [Fact p.Prime] [Field F]
[Finite F] (σs : Moves.Stage p F) (γ u0 s0 : ℤ)
(hγ : γ = σs.e * u0 + s0 * σs.h) : σs.t * γ ≡ s0 [ZMOD σs.e]` AND
`theorem sh_e1_stage {p : ℕ} {F : Type u} [Fact p.Prime] [Field F] [Finite F]
(σs : Moves.Stage p F) (γ s0 : ℤ) (he1 : σs.e = 1) :
shSigma σs.t γ σs.e = 0 ∧ Sh σs.t γ σs.e (geoPos σs.e σs.t γ s0) = s0`
(σ = 0 AND the position identity — the "systems coincide" display at a Stage;
via `σs.he1t he1 : σs.t = 0` and Sp.shE1)
moves_ref: "At a stage with read index (e, h) and pinned Bézout pair (s, t)
(e·s + t·h = 1; (P2): t = 0 at e = 1)".
deps: Sp.shCongr, Sp.shE1 · sketch: instantiate at (σs.e, σs.h, σs.s, σs.t) via
σs.hbez (mind the ℕ→ℤ casts); sh_e1_stage rewrites σs.t = 0 (he1t) into
Sp.shE1. · difficulty: easy

**Sp.shExample** · SP1_shExample.lean
statement: `example : geoPos 2 1 3 1 = -1 ∧ geoPos 2 1 3 3 = 0 ∧ shSigma 1 3 2 = 1
∧ Sh 1 3 2 (-1) = 0 ∧ Sh 1 3 2 0 = 1 ∧ shSigma (-1) 3 2 = -2 ∧
Sh (-1) 3 2 (geoPos 2 (-1) 3 1) = 0 := by decide` (named theorem)
moves_ref: "THE VERIFIER'S EXAMPLE (pass-2 C1) … GEOMETRIC: p₁ = (1 − 3)/2 = −1,
p₃ = (3 − 3)/2 = 0 … CENSUS: a = ⌊1/2⌋ = 0 … BÉZOUT CHECK: (s, t) = (1, −1) …
σ = ⌊−3/2⌋ = −2 — the same census image ✓".
deps: — · sketch: `decide` (Int literals). · difficulty: easy

### C. Coherence/budget consequences

**Sp.anchorBoundCensus** · SP1_anchorBound.lean
statement: `theorem anchor_bound {n : ℕ} {s : Species} (hc : Coherent s)
(hb : Budget n s) : s.a ≤ (s.W - s.wraw) / s.e ∧ s.a + s.ell ≤ s.W / s.e ∧
s.W / s.e ≤ s.W ∧ s.W ≤ n ∧ (s.e = 1 → s.a = s.s0 ∧ s.a ≤ s.W - s.wraw)`
moves_ref: "from (B3)'s 0 ≤ s₀′ ≤ W − w′ and floor-monotonicity, 0 ≤ a ≤
⌊(W − w′)/e⌋, a + ℓ = ⌊(s₀′ + w′)/e⌋ ≤ ⌊W/e⌋ ≤ W ≤ n" (+ "At e = 1 the two
statements are ONE: 0 ≤ a = a^geo ≤ W − w′").
deps: — · sketch: (G2) a = s0/e; Nat.div_le_div_right on s0 ≤ W − w′; for a + ℓ:
a + ℓ ≤ (s0 + e·ℓ)/e (Nat.add_div_right arithmetic) ≤ W/e; Nat.div_le_self.
NOTE: a ≥ 0 is free in ℕ (the note's 0 ≤ a). · difficulty: medium

**Sp.anchorBoundGeo** · SP1_anchorBoundGeo.lean
statement: `theorem anchor_bound_geo {n} {s : Species} (hc : Coherent s)
(hb : Budget n s) (σ ageo : ℤ) (hshift : (s.a : ℤ) = ageo + σ) :
-σ ≤ ageo ∧ ageo ≤ ((s.W - s.wraw) / s.e : ℕ) - σ`
moves_ref: "GEOMETRIC IMAGE (through Sh⁻¹, per realized read): −σ ≤ a^geo ≤
⌊(W − w′)/e⌋ − σ with σ = ⌊tγ/e⌋ — height- and Bézout-dependent, hence NOT a
species-level bound".
deps: Sp.anchorBoundCensus · sketch: rearrange hshift with 0 ≤ a ≤ bound; omega.
difficulty: easy

**Sp.g6Forcing** · SP1_g6Forcing.lean
statement: `theorem w1_forces {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
(hW : s.W = 1) : s.e = 1 ∧ s.ell = 1 ∧ s.s0 = 0 ∧ s.a = 0 ∧ s.lam = {(1,1)} ∧
s.lflank = [] ∧ s.rflank = [] ∧ s.sel = none`
moves_ref: "(G6) TERMINAL RULE: selection = ⊥ iff W = 1. [A W = 1 window forces
the whole side datum — e = ℓ = 1, s₀′ = a = 0, λ = {(1,1)}, no flanks —]".
deps: — · sketch: s0 + e·ℓ ≤ 1 with e, ℓ ≥ 1 pins e = ℓ = 1, s0 = 0; a = 0/1 = 0;
Σ gμ = 1 with positive parts pins λ singleton (1,1) (Multiset: sum-1 with parts
≥ 1 ⇒ one part of weight 1 ⇒ g = μ = 1); flanks: compositions of span 0; sel by
(G6)→. Multiset step: induction/`Multiset.sum_eq_zero` on the erase. · difficulty: medium

**Sp.b4Derived** · SP2_b4Derived.lean
statement: `theorem egμD_le {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
{g μ : ℕ} (hsel : s.sel = some (g, μ)) : s.e * g * μ * s.D ≤ s.wraw * s.D ∧
s.wraw * s.D ≤ n`
moves_ref: "(B4) … hence the Σ eᵢgᵢμᵢ-type constraint e_r·g_r·μ_r·D_r ≤
e_r·ℓ_r·D_r = w′_r·D_r ≤ n."
deps: — · sketch: g·μ ≤ ℓ (B4) scaled by e·D; w′ ≤ W ≤ n/D (B3) ⇒ w′·D ≤ n
(Nat.div: W ≤ n/D → W·D ≤ n via Nat.le_div_iff_mul_le, D ≥ 1). · difficulty: easy

### D. SP-FIN — the catalogue bound (SP.2)

Code type: `Code n := Fin (n^2 + 3*n + 12) → Fin (n + 2)`, entries in the note's
order (tag 1; D w W 3; e ℓ a s₀′ d 5; slot indicator n+1; λ-matrix n²; sel 2;
flank cut-set indicators 2n). Needs `hn : 1 ≤ n` (the note: "n + 2 ≥ 3 for every
n ≥ 1" — the tag entry).

**Sp.compEncode** · SP2_compEncode.lean
statement: `def compCuts (c : List ℕ) : Finset ℕ` (partial-sum cut set) +
`theorem compCuts_inj {span} {c c' : List ℕ} (h : IsComposition c span)
(h' : IsComposition c' span) (he : compCuts c = compCuts c') : c = c'`
moves_ref: "the two flank compositions as indicator vectors of their cut sets
(≤ 2n entries, spans ≤ n by (B5))."
deps: — · sketch: partial sums of a positive composition are strictly monotone;
recover parts as gaps of the sorted cut set; induction on lists. · difficulty: medium

**Sp.lamEncode** · SP2_lamEncode.lean
statement [REV 4, Codex-10 — the injectivity spelled in full]:
`def lamMatrix (n : ℕ) (lam : Multiset (ℕ × ℕ)) : Fin n × Fin n → ℕ :=
fun gm => lam.count (gm.1.val + 1, gm.2.val + 1)` +
`theorem lamMatrix_inj {n : ℕ} {lam lam' : Multiset (ℕ × ℕ)}
(hbd : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n)
(hbd' : ∀ gm ∈ lam', 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n)
(heq : lamMatrix n lam = lamMatrix n lam') : lam = lam'`.
moves_ref: "λ as its multiplicity matrix c : {1..n}² → {0..n} with c(g, μ) := the
number of factors of shape (g, μ) (n² entries; (B4) forces Σ g·μ·c(g,μ) = ℓ ≤ n)".
deps: — · sketch: Multiset.ext + the (B5) part bound to shift indices into Fin n;
counts ≤ card ≤ ℓ ≤ n gives the {0..n} entry range. · difficulty: medium

**Sp.encodeInj** · SP2_encodeInj.lean
statement: `def encode (n : ℕ) (hn : 1 ≤ n) (s : Species) : Code n` +
`theorem encode_inj {n hn} {s s' : Species} (hs : Coherent s ∧ Budget n s)
(hs' : Coherent s' ∧ Budget n s') (h : encode n hn s = encode n hn s') : s = s'`
moves_ref: "Every species tuple is determined by an integer vector with all
entries in {0, 1, …, n+1} … Total length ≤ 1 + 3 + 5 + (n+1) + n² + 2 + 2n =
n² + 3n + 12, each entry taking ≤ n + 2 values".
deps: Sp.compEncode, Sp.lamEncode · sketch: field-by-field recovery: scalar
entries in range by (B5) (d ≤ n+1 the widened entry); λ via lamMatrix; sel via
the reserved (0,0) pair (WellTyped parts ≥ 1 keep it disjoint); flanks via
compCuts + spans s0 / W − s0 − w′ recovered from scalar entries; slots redundant
("kept for crudeness"). · difficulty: medium-hard (split candidate: scalar-block
recovery vs flank/λ blocks if > ~40 lines)

**Sp.encodeCard** · SP2_encodeCard.lean
statement: `theorem code_card (n : ℕ) : Nat.card (Code n) = (n+2)^(n^2 + 3*n + 12)`
moves_ref: "Hence the displayed bound." [|𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}]
deps: — · sketch: `Nat.card_fun`/`Fintype.card_fun`, card of Fin. · difficulty: easy

**Sp.finThm** · SP2_finThm.lean
statement: `theorem SP_FIN (n : ℕ) (hn : 1 ≤ n) : (SnRaw n).Finite ∧
Nat.card (SnRaw n) ≤ (n+2)^(n^2 + 3*n + 12)`
moves_ref: "Theorem SP-FIN. 𝒮_n^raw is FINITE and INDEPENDENT of p, with the
explicit (crude) bound |𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}."
deps: Sp.memCoherent, Sp.encodeInj, Sp.encodeCard · sketch: SnRaw ⊆ the coherent-
admissible set; encode injective there; `Set.Finite.of_finite_image`/
`Nat.card_le_card_of_injective`. p-INDEPENDENCE: by typing (§0) — record in the
docstring, no clause. · difficulty: medium

**Sp.finWords** · SP2_finWords.lean
statement: `theorem SP_FIN' (n L : ℕ) (hn : 1 ≤ n) : {w : List Species |
w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n}.Finite ∧ Nat.card {…} ≤
(Nat.card (SnRaw n))^L`
moves_ref: "Corollary SP-FIN′ (words). For every L, the set of length-L words
over 𝒮_n^raw is finite, of size ≤ |𝒮_n^raw|^L".
deps: Sp.finThm · sketch: inject into `Fin L → SnRaw-subtype` via get; standard
`List.injective` bookkeeping (`List.ext_get`). · difficulty: medium

### E. SP-OUT, self-loops, Lemma SP-DAG (SP.4)

**Sp.outFinite** · SP4_outFinite.lean  [REV 4, Codex-3 FIXED — restricted to
the note's own quantifier: SP.4 defines Out only on catalogue letters]
statement: `theorem out_finite (n : ℕ) (hn : 1 ≤ n) (s : Species)
(hs : InCatalogue n s) : (Out n s).Finite ∧
Nat.card (Out n s) ≤ Nat.card (SnRaw n) + 3`
moves_ref: "**Definition (Out; retyped at rev 3).** For s ∈ 𝒮_n^raw, the
OUTGOING MENU Out(s) ⊆ 𝒮_n^raw ∪ V_term" + "FINITENESS: |Out(s)| ≤ |𝒮_n^raw|
+ 3 by SP-FIN."
deps: Sp.finThm · sketch: Succ n s ⊆ SnRaw n; union card ≤ sum; card Verdict =
3 (`Fintype` on the 3-label inductive). (hs is not needed by the proof — the
restriction is FAITHFULNESS to the display's quantifier, per the adjudication:
never state more than the note does.) · difficulty: easy

**Sp.selfloopChar** · SP4_selfloopChar.lean  [REV 4, Codex-4 FIXED — the
note's SUCC is catalogue-restricted ("SUCC(s) := { s′ ∈ 𝒮_n^raw : … }"), so
the characterized relation is Succ-MEMBERSHIP for a catalogue letter, not bare
SuccStep; Fable's content re-derivation stands, its domain reading corrected]
statement: `theorem selfloop_iff {n : ℕ} {s : Species} (hs : InCatalogue n s) :
s ∈ Succ n s ↔ (s.tag = .postRec ∧ s.e = 1 ∧ s.sel = some (1, s.W))`
(helper, same file: `theorem selfloop_succStep_iff {n : ℕ} {s : Species}
(hc : Coherent s) (hb : Budget n s) : SuccStep n s s ↔ (s.tag = .postRec ∧
s.e = 1 ∧ s.sel = some (1, s.W))` — the StageLaws computation both directions
use; loops3's Bool filter reflects THIS one)
moves_ref: "SELF-LOOPS, syntactically. s has a self-loop edge iff s ∈ SUCC(s):
necessarily e = g = 1 (else D grows strictly, (B1)) with W(s) = μ(s) — the
POST-REC species whose window equals their own selection multiplicity."
deps: Sp.memCoherent · sketch: Succ-membership = InCatalogue s ∧ SuccStep s s;
the first conjunct is hs; then the helper: (→) D = e·g·D with D ≥ 1 forces
e·g = 1; W = μ; the tag iff gives postRec. (←) instantiate StageLaws' match;
laws reflexive at e = g = 1, μ = W; coherence/budget from memCoherent hs.
difficulty: medium

**Sp.selfloopFull** · SP4_selfloopFull.lean
[REV 2, F13 — hypothesis types in full]
statement: `theorem selfloop_isFull {n : ℕ} {s : Species} (hc : Coherent s)
(hb : Budget n s) (h : SuccStep n s s) : IsFull s ∧ s.tag = .postRec`
moves_ref: "n = 3 check: the two loop classes Q2.3▸(1,2) and Q3▸(1,3) are exactly
the full POST-REC letters at stages (1,1,2) and (1,1,3), per (i)."
deps: Sp.selfloopChar · sketch: unfold IsFull; direct from the characterization.
difficulty: easy

**Sp.fullForcing** · SP4_fullForcing.lean
statement: `theorem full_forces {n} {s : Species} (hc : Coherent s)
(hb : Budget n s) (hf : IsFull s) : s.e = 1 ∧ s.ell = s.W ∧ s.a = 0 ∧ s.s0 = 0 ∧
s.lam = {(1, s.W)} ∧ s.lflank = [] ∧ s.rflank = [] ∧ s.slots = Finset.Icc 0 s.W`
moves_ref: "(i) At each fixed (tag, D, w, W) there is AT MOST ONE full letter:
μ = W with (B4)'s g·μ ≤ ℓ and (B3)'s a + ℓ ≤ W forces g = 1, ℓ = W, a = 0,
λ = {(1, W)} …; then (B3)'s s₀′ + w′ ≤ W with w′ = e·ℓ = e·W forces e = 1 and
s₀′ = 0 …, by (G1) both flanks empty, by (G3) slots {0, …, W}".
deps: — · sketch: sel = (1, W): (B4) W ≤ ℓ; (B3) a + ℓ ≤ W so ℓ ≤ W ⇒ ℓ = W,
a = 0; λ: member (1, W) with Σ = W ⇒ erase has sum 0 & positive parts ⇒ singleton
(`Multiset.cons_erase` + sum_eq_zero); (B3) s0 + e·W ≤ W, e ≥ 1, W ≥ 1 ⇒ e = 1,
s0 = 0; (G1) flanks span 0; (G3). · difficulty: medium

**Sp.fullUnique** · SP4_fullUnique.lean
statement: `theorem full_unique {n} {s s' : Species} (hcs : Coherent s)
(hbs : Budget n s) (hcs' : Coherent s') (hbs' : Budget n s') (hf : IsFull s)
(hf' : IsFull s') (htag : s.tag = s'.tag) (hD : s.D = s'.D) (hw : s.w = s'.w)
(hW : s.W = s'.W) : s = s'`
moves_ref: "(i) At each fixed (tag, D, w, W) there is AT MOST ONE full letter …
every field determined."
deps: Sp.fullForcing · sketch: Species.ext; every remaining field pinned by
full_forces + (G2)/(G3) + sel = some (1, W). · difficulty: easy

**Sp.rankRadix** · SP4_rankRadix.lean  [REV 2, F14 — fullBit defined in §2;
hypotheses and the four-case disjunction spelled in full]
statement: `theorem rankNat_lt {n : ℕ} {s : Species} (hn : 1 ≤ n)
(hc : Coherent s) (hb : Budget n s) : rankNat n s < 6 * n ^ 2` AND
`theorem rankNat_lt_of_lex {n : ℕ} {s s' : Species}
(hc : Coherent s) (hb : Budget n s) (hc' : Coherent s') (hb' : Budget n s')
(h : s.D < s'.D ∨
     (s.D = s'.D ∧ tagord s.tag < tagord s'.tag) ∨
     (s.D = s'.D ∧ s.tag = s'.tag ∧ n - s.W < n - s'.W) ∨
     (s.D = s'.D ∧ s.tag = s'.tag ∧ s.W = s'.W ∧ fullBit s < fullBit s')) :
rankNat n s < rankNat n s'`
moves_ref: "(ii) The rank ρ(s) := ( D,  tagord,  n − W,  1 − [s is full] ),
tagord := 0/1/2 for ROOT/POST-INC/POST-REC" + "it has at most |range(ρ)| ≤
n·3·n·2 = 6n² letters".
deps: — · sketch: digit bounds D − 1 < n (B1 + WellTyped), tagord < 3,
n − s.W < n (W ≥ 1), fullBit < 2; both claims are mixed-radix arithmetic —
unfold rankNat, `rcases` the disjunction, `omega` per case (the ordinary
strict-mono of a 4-digit radix-(n,3,n,2) numeral). · difficulty: medium

**Sp.rankStepInc** · SP4_rankStepInc.lean
statement: `theorem rank_step_inc {n} {s s'} (h : SuccStep n s s')
(hcb : Coherent s ∧ Budget n s) (hg : ∀ g μ, s.sel = some (g,μ) → 2 ≤ s.e * g) :
s.D < s'.D`
moves_ref: "· e·g ≥ 2: D′ = e·g·D > D."
deps: — · sketch: D′ = e·g·D ≥ 2·D > D (D ≥ 1). · difficulty: easy

**Sp.rankStepRec** · SP4_rankStepRec.lean
statement: `theorem rank_step_rec {n} {s s'} (h : SuccStep n s s') (hne : s ≠ s')
(hin : InCatalogue n s) (hin' : InCatalogue n s')
(he1 : ∀ g μ, s.sel = some (g,μ) → s.e * g = 1) : rankNat n s < rankNat n s'`
moves_ref: "· e = g = 1, μ < W(s): D′ = D; tagord′ = 2 ≥ tagord; if tagord < 2
done, else n − W′ = n − μ > n − W(s). · e = g = 1, μ = W(s): s is full …; if
tagord(s) = 2, then s is THE full POST-REC letter at its stage, so s′ ≠ s … is
non-full by (i)'s uniqueness: the last coordinate rises 0 → 1."
deps: Sp.fullForcing, Sp.fullUnique, Sp.rankRadix, Sp.memCoherent · sketch: the
displayed three-way split on (μ vs W, tagord); the μ = W ∧ tagord = 2 branch:
s full; if s' full too then full_unique (stages match: D′ = D, w′ = w, W′ = μ =
W, tag′ = postRec = tag) forces s' = s, contra hne; so fullBit rises.
difficulty: medium-hard (the subtle case; keep the three branches as `have`s)

**Sp.rankStrict** · SP4_rankStrict.lean
statement: `theorem rank_strict {n} {s s'} (hin : InCatalogue n s)
(hin' : InCatalogue n s') (h : SuccStep n s s') (hne : s ≠ s') :
rankNat n s < rankNat n s'`
moves_ref: "(ii) The rank ρ(s) := (D, tagord, n − W, 1 − [s is full]) … STRICTLY
increases lexicographically along every non-self-loop SUCC edge s → s′".
deps: Sp.rankStepInc, Sp.rankStepRec, Sp.rankRadix · sketch: e·g = 1 ∨ e·g ≥ 2
(WellTyped positivity); dispatch. · difficulty: easy

**Sp.dagWalk** · SP4_dagWalk.lean
statement: `theorem SP_DAG_walk {n} (hn : 1 ≤ n) {l : List Species}
(h : CollapsedWalk n l) : l.length ≤ 6 * n^2`
moves_ref: "(iii) Hence the menu graph with self-loops collapsed is a DAG; every
collapsed walk visits pairwise-distinct ranks, so it has at most … 6n² letters".
deps: Sp.rankStrict, Sp.rankRadix · sketch: map rankNat: Chain' (· < ·) list of
ℕ < 6n²; strictly-increasing-below-B has length ≤ B (small induction or
`List.Sorted` + Nodup ⊆ range). · difficulty: medium

**Sp.dagWords** · SP4_dagWords.lean
statement: `theorem SP_DAG_words (n : ℕ) (hn : 1 ≤ n) : {l | CollapsedWalk n l}.Finite
∧ Nat.card {l | CollapsedWalk n l} ≤ (Nat.card (SnRaw n) + 1)^(6 * n^2)`
moves_ref: "with SP-FIN, the set of collapsed words over 𝒮_n^raw is FINITE, of
size ≤ (|𝒮_n^raw| + 1)^{6n²}."
deps: Sp.dagWalk, Sp.finThm · sketch: inject length-≤L lists into
`Fin L → Option (SnRaw-subtype)` (pad with none); card arithmetic. · difficulty: medium

### F. SP-COMP (conditional — the interface layer), words, entrances

[REV 2, F1/F2: restated over `CanTreeModel` with the note's full quantifier
prefix (n, p, f, η ∈ T_can(f), r); the conclusions `InCatalogue`/`SuccStep`/
`Out`-membership occur in NO hypothesis field — the fields are the RAW engine
laws (§2), and the units' content is the note's own "reachability by induction
along the word".]

STANDING hypothesis_fields FOR THIS GROUP (each cited at its §2 field): hRoot,
hStage, hCoh, hHalt (SP-COMP proof steps (1)/(2)/(3)/(3′)/(5) — §B2-DEF
D.4/D.5/D.6/D.7/D.8/D.10 + §C DOM via §D4-R L11 + §D4-R L2/L3/L5; owner
HC-1/MovesD; OPEN, never proved here) and hVerdictPin (THE D4R.0-K(c)
RESIDUAL — the verdict pin, owner [3t] via VP; explicit per F7). FENCE
[REV 3, G3 — retargeted to the closure side]: NEVER strengthen — no field may
mention the CLOSURE-side objects `InCatalogue`, `Succ`, or `Out` (the
conclusions; the inductively generated catalogue). The per-read fields ARE the
note's engine outputs, and jointly they unfold to RootAdmissible at r = 0 and
to SuccStep per step — that is not a leak but the note's own scoping: steps
(1)–(3′)/(5) hand the closure exactly its premises, and the units' content is
the quantified induction, not a logical gap between fields and premises.
NEVER drop (hCoh's coherence stays).

**Sp.compMember** · SP3_compMember.lean
statement: `theorem SP_COMP (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
(hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
(η : M.Branch) (r : ℕ) (hr : (r : ℕ∞) < M.len η) : InCatalogue n (M.datum η r)`
[REV 4, Codex-1: ℕ∞-length — the quantifier now reaches every read of every
finite AND infinite chain, prefixwise, exactly SP-COMP's domain]
(hf/hdeg carry the note's "f in the monic degree-n coefficient box" binder —
unused computationally, kept for quantifier fidelity, linter-silenced)
moves_ref: "For every n, every prime p, every f in the monic degree-n
coefficient box, every chain η ∈ T_can(f) …, and every read r of η's CATALOGUE
WORD …: the read's retained datum is a member of 𝒮_n^raw".
deps: — · sketch: induction on r: r = 0 via `InCatalogue.root` (M.hRoot gives
RootStage + Coherent + Budget = RootAdmissible); r + 1 via `InCatalogue.step`
with SuccStep ASSEMBLED from M.hStage (StageLaws) + M.hCoh at r + 1
(Coherent ∧ Budget) — the assembly is the derivation, not an assumption.
difficulty: easy-medium
hypothesis_fields: the standing group list above; hVerdictPin UNUSED by this
unit's proof but part of the interface it quantifies over. [REV 3, G4 — what
IS enforced:] the field keeps the D4R.0-K(c) conditionality VISIBLE — named in
the interface every consumer instantiates — but does NOT type-enforce it: a
model discharges (verdict, hVerdictPin) trivially (e.g. verdict := fun _ =>
some .z), WHICH verdict being deliberately VP-owned; the ledger rides in the
named field + its docstring, and Lean-side SP_COMP is equally strong without
it. Faithful to the note: the residual is a cited OPEN kernel, not a
consumed premise of steps (1)–(3′)/(5).

**Sp.compEdges** · SP3_compEdges.lean
statement: `theorem SP_COMP_edges (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
(hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
(η : M.Branch) (r : ℕ) (hr : (r + 1 : ℕ∞) < M.len η) :
Sum.inl (M.datum η (r + 1)) ∈ Out n (M.datum η r)`
moves_ref: "each consecutive read pair is linked by an edge of the syntactic
menu Out (SP.4)" + step (5): "which is precisely SP.4's edge relation; so each
realized transition is an Out edge."
deps: Sp.compMember · sketch: Succ-membership = InCatalogue (compMember at
r + 1) ∧ SuccStep (assembled as in compMember); then `Or.inl` into Out.
GENUINE step: the conclusion's Out is defined through InCatalogue, which no
field supplies. · difficulty: easy
hypothesis_fields: the standing group list above.

**Sp.compCollapsed** · SP3_compCollapsed.lean  [REV 4, Codex-1 — Branch/len
tied to SP-DAG as a CONCLUSION: real, non-vacuous content over the interface]
statement: `theorem SP_COMP_collapsed (n p : ℕ) (hn : 1 ≤ n) [Fact p.Prime]
(f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
(M : CanTreeModel n p f) (η : M.Branch) (m : ℕ) (hm : (m : ℕ∞) ≤ M.len η) :
(collapseRuns ((List.range m).map (M.datum η))).length ≤ 6 * n ^ 2`
moves_ref: "the collapsed LETTER length of a walk (the number of letters after
collapsing self-loop runs) IS bounded — Lemma SP-DAG (SP.4): … every collapsed
walk has ≤ 6n² letters. SCOPE OF THAT BOUND …: it bounds letter ALTERNATIONS
only. The number of READS stays unbounded".
deps: Sp.compMember, Sp.collapseWalk, Sp.dagWalk · sketch: the length-m read
prefix is a member-wise catalogued SuccStep chain (compMember + assembly);
collapseRuns gives a CollapsedWalk; dagWalk bounds it. NOTE the fence, kept:
m (the READ count) is NOT bounded — only the collapsed image is; this is the
note's own scope display transposed. · difficulty: medium (easy-medium)
hypothesis_fields: the standing group list above.

**Sp.tauWord** · SP3_tauWord.lean  [REV 2, F3 — the halt endpoint is now a
STRUCTURE LAW of CatalogueWord (§2: hLast forces W = 1 at the last letter,
hFirstW1 forbids earlier confirming reads); the theorem is unconditional]
statement: `theorem tauWord_spec {n : ℕ} (cw : CatalogueWord n) :
cw.tauWord.length + 1 = cw.word.length ∧
(∀ s, cw.word.getLast? = some s → s.W = 1 ∧ s.sel = none) ∧
(∀ s ∈ cw.tauWord, s.W ≠ 1 ∧ s.sel ≠ none)`
moves_ref: "the CATALOGUE WORD (SP-COMP's quantifier, the census's object)
closes at the confirming read; the τ-WORD (every density consumer's object) is
the catalogue word with that final confirming letter removed".
deps: Sp.memCoherent · sketch: length via `List.length_dropLast` + hne;
sel = none at the last letter from hLast + (G6) (memCoherent through hMem);
sel ≠ none on tauWord from hFirstW1 + (G6). · difficulty: easy
hypothesis_fields: verdict pinning (WHERE the halt verdict sits — parent read /
level-0 track) is VP's, NOT stated; only the word arithmetic is.

**Sp.n1RootConfirming** · SP3_n1Root.lean  [REV 3, G2 — split from the rev-2
Sp.n1Clause to break the n1singleton cycle: this half has NO n = 3/enum deps]
statement: `theorem n1_root_confirming {s : Species} (h : RootAdmissible 1 s) :
s.W = 1 ∧ s.sel = none`
moves_ref: "At n = 1 the catalogue word is the single ROOT letter (W = n = 1,
selection ⊥ — (G6)'s degenerate degree)".
deps: — · sketch: RootStage gives W = n = 1; (G6) gives sel = none.
difficulty: easy
hypothesis_fields: (τ-hen) SEMANTICS is VP's — only letter arithmetic stated.

**Sp.n1Word** · SP3_n1Word.lean  [REV 3, G2 — the other half; DAG:
n1RootConfirming → n1singleton → n1Word, acyclic]
statement: `theorem n1_word (cw : CatalogueWord 1) :
cw.word.length = 1 ∧ cw.tauWord = []`
moves_ref: "the τ-WORD is EMPTY (the standing rule 'catalogue word minus the
final confirming letter' applied to the one-letter word …); the CATALOGUE WORD
is the single confirming root letter".
deps: Sp.n1singleton, Sp.memCoherent · sketch: every letter of cw is
InCatalogue 1 (hMem) = confirmingRoot1 (n1singleton), so every letter has
W = 1; hFirstW1 then empties dropLast; length 1; tauWord = dropLast = [].
difficulty: easy-medium
hypothesis_fields: as Sp.n1RootConfirming.

**Sp.n1Branch** · SP3_n1Branch.lean  [REV 5, Codex rev-4 crit — the tie
between an ACTUAL CanTreeModel branch and the n = 1 CatalogueWord; with hN1,
an all-len-0 model at n = 1 is now unsatisfiable and this unit exhibits the
forced word]
statement: `theorem n1_branch_word (p : ℕ) [Fact p.Prime]
(f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 1)
(M : CanTreeModel 1 p f) (η : M.Branch) :
M.len η = 1 ∧ M.datum η 0 = confirmingRoot1` AND the packaging
`def CanTreeModel.n1CatalogueWord (M : CanTreeModel 1 p f) (η : M.Branch) :
CatalogueWord 1` with `word := [M.datum η 0]` (hMem via SP_COMP; hChain
trivial on a singleton; hLast from n1_root_confirming's W = 1; hFirstW1
vacuous) and `theorem n1_branch_word_eq (…) :
(M.n1CatalogueWord η).word = [confirmingRoot1]`
moves_ref: "At n = 1 the catalogue word is the single ROOT letter (W = n = 1,
selection ⊥ — (G6)'s degenerate degree) … the τ-WORD is EMPTY …; the
CATALOGUE WORD is the single confirming root letter — census data,
gate-walked".
deps: Sp.n1singleton, Sp.n1RootConfirming, Sp.compMember · sketch: hN1 gives
0 < M.len η; hRoot + n1_root_confirming give (M.datum η 0).W = 1; hHalt
closes M.len η = 1; SP_COMP + n1singleton pin datum η 0 = confirmingRoot1;
package the singleton word. · difficulty: medium (easy-medium)
hypothesis_fields: the standing group-F list; hN1 is the note-quoted n = 1
clause (rev 5 of the note), not an engine kernel.

**Sp.collapseSublist** · SP3_collapseSublist.lean  [REV 4, Codex-13 — the
rev-3 four-lemma unit split into four]
statement: `theorem collapseRuns_sublist (l : List Species) :
(collapseRuns l).Sublist l`
moves_ref: "(the number of letters after collapsing self-loop runs)".
deps: — · sketch: induction on the defining equations; if-branch via
sublist-cons. · difficulty: easy

**Sp.collapseNeNil** · SP3_collapseNeNil.lean
statement: `theorem collapseRuns_ne_nil {l : List Species} (h : l ≠ []) :
collapseRuns l ≠ []`
moves_ref: "one marker letter + one depth slot per maximal run" (a nonempty
word keeps ≥ 1 marker letter).
deps: — · sketch: induction; both branches of the two-head case keep a head.
difficulty: easy

**Sp.collapseEqSelf** · SP3_collapseEqSelf.lean
statement: `theorem collapseRuns_eq_self_iff (l : List Species) :
collapseRuns l = l ↔ l.Chain' (· ≠ ·)`
moves_ref: "self-loop repetition counts (DEPTHS — run-lengths of equal-species
consecutive reads)" (collapse is identity exactly on run-free words).
deps: Sp.collapseSublist · sketch: Mathlib `List.destutter_eq_self_iff` (the
§2 identity collapseRuns = destutter (· ≠ ·)), or direct induction.
difficulty: medium

**Sp.collapseWalk** · SP3_collapseWalk.lean
statement: `theorem collapseRuns_collapsedWalk {n : ℕ} {l : List Species}
(hmem : ∀ s ∈ l, InCatalogue n s) (hch : l.Chain' (SuccStep n)) :
CollapsedWalk n (collapseRuns l)`
moves_ref: "a loop-collapsed entrance word is a collapsed walk in the menu
graph".
deps: Sp.collapseSublist · sketch: membership via Sublist; the boundary-edge
preservation induction: consecutive-dedup keeps exactly the SuccStep edges
with s ≠ s′ (a run boundary is a non-loop edge); two-head case split.
difficulty: medium

**Sp.entranceDef** · SP3_entrance.lean  [REV 2, F4 — EntranceShape (§2) now
carries the block-entry selection (gsel, μsel) + height/depth parameter slots;
the finiteness theorem quantifies over EntranceShape itself]
statement: `theorem entrance_collapsed_finite (n gsel μsel : ℕ) (hn : 1 ≤ n) :
{l : List Species | ∃ E : EntranceShape n gsel μsel, collapseRuns E.word = l}.Finite`
AND `theorem entrance_collapsed_len {n gsel μsel : ℕ} (hn : 1 ≤ n)
(E : EntranceShape n gsel μsel) : (collapseRuns E.word).length ≤ 6 * n ^ 2`
moves_ref: "so it has ≤ 6n² letters (SP-DAG(iii)); with SP-FIN the family of
such words is finite and p-independent — {ε} is finite up to its (height pair,
depth) parameters, which is exactly the finiteness CTS-M(iii) consumes".
deps: Sp.collapseWalk, Sp.collapseNeNil, Sp.dagWalk, Sp.dagWords · sketch:
E.word is a member-
wise catalogued SuccStep chain (E.hMem, E.hChain); collapseRuns gives a
CollapsedWalk (collapseWalk), so ≤ 6n² (dagWalk) and the image set sits inside
the finite collapsed-word set (dagWords). The parameters (heights, depths) are
quantified AWAY by the image construction — "up to its parameters", exactly.
difficulty: medium
hypothesis_fields: the size-e-block / landing-cell β₀ IDENTIFICATION of the
entry datum is [1v] CTS-M(iii)'s (owner, cited); per-shape masses ι_{e,ε,β₀}
and entrance counts are [1]/[1v] objects, never assigned here.

[REV 2, F15] **Sp.mcRoster: STRUCK — deferred to MovesS (wave 4).** Its only
anchor is §S-RESUM (K-SUB)'s (m, c) CLASSIFICATION — not a display of the
frozen §M-SPECIES text, so it has no in-scope moves_ref. The defs (mOf, cOf,
OutcomeClass) move to the MovesS blueprint, defined there on this corpus's
`Species.lam` (additive import; §2's deferral record).

### G. The generated enumeration (feeds every n = 3 `decide`)

**Sp.compEnumComplete** · SP2_compEnum.lean
statement: `theorem compEnum_complete {span : ℕ} {c : List ℕ} :
IsComposition c span ↔ c ∈ compEnum span` AND [REV 4, Codex-11 — spelled]
`theorem compEnum_nodup (span : ℕ) : (compEnum span).Nodup`
moves_ref: "each flank is a composition of its span" (G1).
deps: — · sketch: strong induction on span; compEnum span = [[]] at 0, else
first-part split. · difficulty: medium

**Sp.lamEnumComplete** · SP2_lamEnum.lean
statement: `theorem lamEnum_complete {bound weight : ℕ} {lam : Multiset (ℕ × ℕ)}
(hpos : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2) (hbd : ∀ gm ∈ lam, gm.1 ≤ bound ∧
gm.2 ≤ bound) : ((lam.map fun gm => gm.1 * gm.2).sum = weight ↔ lam ∈ lamEnum
bound weight)`
moves_ref: "(residual shape) the degree–multiplicity partition λ … with
Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ" + (B5)'s part caps.
deps: — · sketch: enumeration by strong recursion on weight over a canonical
(sorted) representative; completeness by induction on the multiset. THE fiddly
enum unit — recommend List-of-sorted-lists internally, Multiset at the boundary.
difficulty: medium-hard

**Sp.speciesEnumComplete** · SP2_speciesEnum.lean
statement: `theorem speciesEnum_complete {n : ℕ} {s : Species} (hc : Coherent s)
(hb : Budget n s) : s ∈ speciesEnum n`
moves_ref: "𝒮_n^raw injects into the encoded set ((G1)–(G6) only shrink it)"
[here: the generated candidate list].
deps: Sp.compEnumComplete, Sp.lamEnumComplete · sketch: coherence pins a/d/slots
from (s0, e, ℓ) ((G2)/(G3)); budget pins every generator range ((B1)–(B5));
membership by product-list mem lemmas. · difficulty: medium-hard

### H. The n = 3 instance (SP.6) — the `decide` layer

All statements phrased over `List`/`Bool` (`List.all … = true`) for kernel
`decide`; perf fence §1.6 applies (split per stage group on overrun).

**Sp.n3card53** · SP6_card53.lean
statement: `theorem catalogue3_card : catalogue3.length = 53 ∧ catalogue3.Nodup`
(Nodup by `decide`; length by `rfl`) + `theorem groups_card : groupR.length = 21
∧ groupQ3.length = 21 ∧ groupQ2.length = 6 ∧ groupQ1.length = 1 ∧ groupI.length = 4`
moves_ref: "|𝒮₃^raw| = 21 + 21 + 6 + 1 + 4 = 53."
deps: DefsN3 · sketch: rfl/decide. · difficulty: easy

**Sp.n3rootLetters** · SP6_rootLetters.lean  [REV 2, F16 — ONE statement, the
membership equivalence the note asserts; multiplicity content carried by
n3card53's Nodup, so duplicate enum candidates (repeated equal λ-factors in
the generator) are harmless]
statement: `theorem rootAdmissible3_iff (s : Species) :
RootAdmissible 3 s ↔ s ∈ groupR`, proved from the two decide facts
`theorem root3_enum_check : ((speciesEnum 3).all fun s =>
rootAdmissibleB 3 s == groupR.contains s) = true` [REV 4, Codex-6] and
`theorem groupR_admissible : (groupR.all (rootAdmissibleB 3)) = true`
moves_ref: "GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters." + "per
stage, the (G1)–(G6)+(B1)–(B5corrected) letters are exactly the displayed rows".
deps: Sp.speciesEnumComplete, Sp.reflSucc (rootAdmissibleB_iff) · sketch: (→)
RootAdmissible ⇒ Coherent ∧ Budget ⇒ s ∈ speciesEnum 3 (enumComplete), then
root3_enum_check reads off membership; (←) groupR_admissible + the reflection
iff. · difficulty: medium (perf)

**Sp.n3closureStep** · SP6_closureStep.lean
statement: `theorem closure_step3 : (catalogue3.all fun s => (speciesEnum
3).all fun s' => !(succStepB 3 s s') || catalogue3.contains s') = true`
[REV 4, Codex-6 — Bool-routed via List.contains]
moves_ref: "the (G5) closure from the root stage (1,1,3) generates exactly the
five displayed stage groups … nothing further from Q2/Q3; W = 1 terminal by (G6)".
deps: DefsN3, DefsEnum · sketch: decide (≈53 × |enum3| succStepB evals — THE perf
hotspot; pre-split into 5 per-group units if needed). · difficulty: medium (perf)

**Sp.n3reachable** · SP6_reachable.lean
statement: `theorem reachable3 : (catalogue3.all fun s' => rootAdmissibleB 3 s' ||
groupR.any fun s => succStepB 3 s s') = true`
moves_ref: "root selections (1,1)/(1,2)/(1,3) → stages (1,1,1)/(1,1,2)/(1,1,3);
▸(2,1), ▸(3,1), e=2, e=3 → the four POST-INC W = 1 stages".
deps: DefsN3 · sketch: decide (53 × 21). Every non-root letter is one SuccStep
from a ROOT letter at n = 3. · difficulty: easy

**Sp.n3catalogueEq** · SP6_catalogueEq.lean
statement: `theorem SnRaw3_eq : ∀ s, InCatalogue 3 s ↔ s ∈ catalogue3`
moves_ref: "**Definition (the raw catalogue; rev 3 …)** 𝒮_n^raw := the least set
…" + "[RE-VERIFIED against the rev-3 definition: …]".
deps: Sp.memCoherent, Sp.speciesEnumComplete, Sp.reflSucc, Sp.n3rootLetters,
Sp.n3closureStep, Sp.n3reachable · sketch: (→) induction on InCatalogue: root
case via n3rootLetters (s ∈ enum by speciesEnumComplete); step via n3closureStep.
(←) each letter: root case by rootAdmissibleB + refl lemmas; non-root via
n3reachable + `.step`. · difficulty: medium

**Sp.n3menuMap** · SP6_menuMap.lean  [REV 4, Codex-6: Bool-routed; Codex-7
FIXED: the closure wiring is now IN the unit — global exactness over ALL
Species, the sealed menu display's real strength]
statement: `theorem menu3_local : (catalogue3.all fun s => catalogue3.all fun
s' => succStepB 3 s s' == (menuMap3 s).contains s') = true` (decide) AND
`theorem menu3_exact_global (s : Species) (hs : s ∈ catalogue3)
(s' : Species) : SuccStep 3 s s' ↔ s' ∈ menuMap3 s`
moves_ref: "The n = 3 menu map (Out, sealed; stage laws of SP.4). ▸(1,1) → Q1;
▸(1,2) → Q2 letters; ▸(1,3) → Q3 letters; ▸(2,1) → I(2,2); ▸(3,1) → I(3,3);
e=2 letters → I(2,1); e=3 letters → I(3,1)."
deps: Sp.reflSucc, Sp.speciesEnumComplete, Sp.n3closureStep · sketch: (→) a
SuccStep target carries Coherent ∧ Budget BY DEFINITION (SuccStep's second and
third conjuncts) ⇒ s' ∈ speciesEnum 3 (speciesEnumComplete) ⇒ s' ∈ catalogue3
(closure_step3 at s, via reflSucc) ⇒ menu3_local reads off membership in
menuMap3 s. (←) menuMap3 s ⊆ catalogue3 (its definition lists group members),
so menu3_local's ← direction applies. THE CHAIN, displayed: SuccStep →
(Coherent ∧ Budget) → enum → closure → catalogue → local table — no off-
catalogue SuccStep edge can exist, which is exactly the sealed exactness.
difficulty: medium (perf, moderate)

**Sp.n3selfloops** · SP6_selfloops.lean
[REV 3, C1 — target reordered to catalogue3's pinned order: loopQ3 ∈ groupQ3
precedes loopQ23 ∈ groupQ2 in groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI]
statement: `theorem loops3 : catalogue3.filter (fun s => succStepB 3 s s) =
[loopQ3, loopQ23]`
moves_ref: "SELF-LOOPS: Q2.3▸(1,2) → Q2 (the μ = 2 loop) and Q3's ▸(1,3) rows →
Q3 (the μ = 3 loop) — exactly two loop classes at n = 3, both POST-REC".
deps: DefsN3 · sketch: decide. Cross-check `Sp.selfloopFull`: both are the full
POST-REC letters. · difficulty: easy

**Sp.n3postincW1** · SP6_postincW1.lean
statement: `theorem postInc3_W1 : (catalogue3.all fun s => !(s.tag == .postInc)
|| (s.W == 1)) = true`
moves_ref: "POST-INC W = 1 always at n = 3 (every genuine increment here has
μ = 1: g·μ ≤ ℓ and e·ℓ ≤ 3 force μ ≥ 2 into e = g = 1, the recentering class)."
deps: DefsN3 · sketch: decide. · difficulty: easy

**Sp.n3terminal5** · SP6_terminal5.lean
statement: `theorem terminal3 : catalogue3.filter (fun s => s.W == 1) =
groupQ1 ++ groupI ∧ (catalogue3.all fun s => (s.W == 1) == (s.sel == none)) =
true ∧ ((groupQ1 ++ groupI).all fun s => catalogue3.all fun s' =>
!(succStepB 3 s s')) = true`
moves_ref: "The five W = 1 letters of SP.6 have Out(s) = V_term exactly." + "W = 1
letters read the confirming side … and are TERMINAL: selection ⊥".
deps: DefsN3 · sketch: decide ×3 (5 letters + the (G6) instance + empty menus =
the closure-marker face; V_term itself is unconditional in Out's definition).
difficulty: easy

**Sp.n3R3check** · SP6_R3check.lean  [REV 2, F6 — BOTH flank variants, as the
two named letters of §4]
statement: `theorem R3_members : coherentB R3letterA = true ∧
budgetB 3 R3letterA = true ∧ R3letterA ∈ groupR ∧ R3letterA.a = 2 ∧
R3letterA.lflank = [2] ∧ coherentB R3letterB = true ∧
budgetB 3 R3letterB = true ∧ R3letterB ∈ groupR ∧ R3letterB.a = 2 ∧
R3letterB.lflank = [1, 1]`
moves_ref: "R3 = (ROOT, (D,w,W) = (1,1,3), e = 1, ℓ = 1, a = 2, s₀′ = 2, slots
{2,3}, λ = {(1,1)} ▸ (1,1), left flank (2) or (1,1), right empty)" + "(B5,
corrected anchor bound) a = 2 ≤ ⌊(W − w′)/e⌋ = 2 ✓ (saturated)".
deps: DefsN3 · sketch: decide — the note's own saturating witnesses for the
corrected (B5), one per flank composition. · difficulty: easy

[REV 5, Codex rev-4 gap — the rev-4 Sp.n3thresholdData split ONE DISPLAY
EACH into the six units below; the literal-RHS pins and Bool routing of REV 4
are unchanged, only redistributed. Shared moves_ref head: SP.6's threshold
clause; docstring duties on every unit: field-size pass "NECESSARY for
realization, NOT sufficient"; N*₃ values are gate-censused data (M-n3-V2),
never theorems; realizability semantics stays out (§0).]

**Sp.n3exclusionLists** · SP6_exclusionLists.lean
statement: `theorem exclusion_lists_pinned :
catalogue3.filter (fun s => decide (2 ≤ linCount s)) = fieldSizeExcluded2 ∧
catalogue3.filter (fun s => decide (3 ≤ linCount s)) = fieldSizeExcluded3`
moves_ref: "p = 2 (one nonzero root): the 11 letters with λ ⊇ two distinct
linears — {(1,1)²}: …; {(1,2),(1,1)}: …; {(1,1)³}: …. p = 3 (two nonzero
roots): exactly the 2 letters with λ = {(1,1)³}."
deps: DefsN3 · sketch: decide (two 53-letter filters). · difficulty: easy

**Sp.n3exclusionCards** · SP6_exclusionCards.lean
statement: `theorem exclusion_cards : fieldSizeExcluded2.length = 11 ∧
fieldSizeExcluded3.length = 2`
moves_ref: "the 11 letters" / "exactly the 2 letters" (the displayed counts).
deps: DefsN3 · sketch: rfl/decide. · difficulty: easy

**Sp.n3multiSide6** · SP6_multiSide6.lean
statement: `theorem multiSide6_pinned : multiSide6 =
  [⟨.postRec, 1, 1, 3, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1),
     [], [1,1]⟩,                                        -- Q3(R1), rf (1,1)
   ⟨.postRec, 1, 1, 3, 1, 1, 1, 1, 2, Finset.Icc 1 2, {(1,1)}, some (1,1),
     [1], [1]⟩,                                         -- Q3(R2)
   ⟨.postRec, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1),
     [1,1], []⟩,                                        -- Q3(R3), lf (1,1)
   ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(2,1)}, some (2,1),
     [], [1]⟩,                                          -- Q3(R4) ▸(2,1)
   ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2),
     [], [1]⟩,                                          -- Q3(R4) ▸(1,2)
   ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)},
     some (1,1), [], [1]⟩]                              -- Q3(R4) ▸(1,1)`
(RHS = literal Species terms transcribing the note's rows — REV 4's C-8 pin;
field order: tag, D, w, W, e, s0, ell, a, d, slots, lam, sel, lflank, rflank)
moves_ref: "the exceptions are the multi-side μ = 3 letters — the sel-carrying
Q3 copies whose child window [0,3] has ≥ 2 sides: Q3(R1, right flank (1,1)),
Q3(R2), Q3(R3, left flank (1,1)), and the three Q3(R4) λ-rows" + the R1–R4
group-R row displays.
deps: DefsN3 · sketch: decide (list of literals). · difficulty: easy

**Sp.n3multiSideMem** · SP6_multiSideMem.lean
statement: `theorem multiSide6_mem : (multiSide6.all groupQ3.contains) = true
∧ multiSide6.Nodup`
moves_ref: "the sel-carrying Q3 copies" (six DISTINCT letters of group Q3).
deps: DefsN3 · sketch: decide; Nodup rules out repeated letters (the C-8
repeat scenario). · difficulty: easy

**Sp.n3NstarValues** · SP6_NstarValues.lean
statement: `theorem nstar_values : Nstar3six msQ3R1 = some 7 ∧
Nstar3six msQ3R2 = some 6 ∧ Nstar3six msQ3R3 = some 6 ∧
Nstar3six msQ3R4a = some 6 ∧ Nstar3six msQ3R4b = some 6 ∧
Nstar3six msQ3R4c = some 6`
moves_ref: "THE SIX COMPUTATIONS (all at p = 3 — the labels are N*_3): … the
three Q3(R4)-copies …: N*_3 = 6; · Q3(R2)/Q3(R3)-copies …: N*_3 = 6; · the
Q3(R1)-copy …: N*_3 = 7."
deps: DefsN3 · sketch: six rfl/decide reads of the table. · difficulty: easy

**Sp.n3NstarDomain** · SP6_NstarDomain.lean
statement: `theorem nstar_domain : (catalogue3.all fun s =>
(Nstar3six s).isSome == multiSide6.contains s) = true`
moves_ref: "N*_p(letter) := the least such N … — DEFINED exactly on the
eventually-realized letters" [here: the table's domain is exactly the six
displayed exceptions; the other 45 carry only the censused N*₃ ≤ 5 remark,
deliberately not a def]. deps: DefsN3 · sketch: decide over 53.
difficulty: easy

**Sp.n3entrancePatterns** · SP6_entrance.lean  [REV 2, F17: full roster, no
ellipses; REV 3, C2: the ▸(1,2) rosters corrected to their TRUE three members
per group — the note's own R6 row {(1,2),(1,1)}▸(1,2) is a root ▸(1,2) letter
and its menu law "▸(1,2) → Q2 letters" is row-unrestricted; the entrance
display's "[R4/R5 rows]" bracket is an ERRATUM CANDIDATE, verified at §9 and
NOT baked into any target]
statement: `theorem entrance3_patterns :
-- into the μ=2 block, direct: root▸(1,2) = the ▸(1,2) rows of R4/R5/R6
-- (three members; §9 — the note's bracket omits R6's)
(groupR.filter fun s => s.sel == some (1, 2)) =
  [rootR4sel12, rootR5sel12, rootR6sel12] ∧
-- into the μ=2 block, via the μ=3 loop: root▸(1,3)·(Q3-loop)^d·▸(1,2)
succStepB 3 rootR6sel13 loopQ3 = true ∧
succStepB 3 loopQ3 loopQ3 = true ∧
((groupQ3.filter fun s => s.sel == some (1, 2)).all fun q =>
  succStepB 3 loopQ3 q) = true ∧
((groupQ3.filter fun s => s.sel == some (1, 2)).length = 3) ∧
-- into the μ=3 block: root▸(1,3)
rootR6sel13.sel = some (1, 3) ∧ rootR6sel13 ∈ groupR ∧
-- into the increment landings (D ≥ 2): the ▸(2,1)/▸(3,1)/e=2/e=3 rows of
-- R, Q2, Q3, each stepping into its I letter
((catalogue3.filter fun s => s.sel == some (2, 1)).all fun s =>
  succStepB 3 s letterI22) = true ∧
((catalogue3.filter fun s => s.sel == some (3, 1)).all fun s =>
  succStepB 3 s letterI33) = true ∧
((catalogue3.filter fun s => (s.e == 2) && !(s.sel == none)).all fun s =>
  succStepB 3 s letterI21) = true ∧
((catalogue3.filter fun s => (s.e == 3) && !(s.sel == none)).all fun s =>
  succStepB 3 s letterI31) = true ∧
-- …and each such row lives in R, Q2, or Q3 (never I, Q1: those are terminal)
((catalogue3.filter fun s => s.sel == some (2, 1) || s.sel == some (3, 1) ||
  ((s.e == 2 || s.e == 3) && !(s.sel == none))).all fun s =>
  (groupR ++ groupQ2 ++ groupQ3).contains s) = true`
[REV 4, Codex-6 — Bool-routed via List.contains]
(the loop-power (Q3-loop)^d is witnessed by the ONE loop edge — depth d is a
parameter, not a letter: EntranceShape's depth slot, SP-DAG scope)
moves_ref: "ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as depth slots): into
the μ=2 block: root▸(1,2) [R4/R5 rows], or root▸(1,3)·(Q3-loop)^d·▸(1,2); into
the μ=3 block: root▸(1,3); into each increment landing (D ≥ 2): the
▸(2,1)/▸(3,1)/e=2/e=3 rows of R, Q2, Q3 prefixed by their cascades — a finite
list, displayed by the same map." [the bracket read per §9's verified
correction: the ▸(1,2) rows of R4/R5/R6]
deps: DefsN3 · sketch: decide per conjunct (filters over 53/21; edge checks).
difficulty: easy

**Sp.n1singleton** · SP6_n1singleton.lean
statement: `theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1`
(confirmingRoot1 := the W = 1 root letter at stage (1,1,1))
moves_ref: "(G6) … (or W = n = 1 at the root — the degenerate degree)" + the n = 1
clause: "At n = 1 the catalogue word is the single ROOT letter".
deps: Sp.speciesEnumComplete, Sp.n1RootConfirming, Sp.succTerminal,
Sp.g6Forcing [REV 4, Codex-12 + Fable NOTE B — the sketch's route declared;
confirmingRoot1 now a DefsN3 literal] [REV 3, G2 — was Sp.n1Clause; the cycle
is split: only the root-confirming half is consumed here, and Sp.n1Word
consumes THIS unit] · sketch: root-admissible
at n = 1 pins every field (g6Forcing at W = 1); terminal ⇒ no step case.
difficulty: easy-medium

## 6. Risks, fallbacks, and what deliberately is NOT here

1. **decide perf** (Sp.n3closureStep, Sp.n3rootLetters, Sp.n3menuMap): see §1.6.
   Estimated enum3 ≤ ~3k candidates; worst check ~160k cheap Bool evals. If kernel
   time explodes: split per stage group; then shrink enum3 by strengthening the
   generator bounds (additive change, no statement touched). native_decide BANNED.
2. **Multiset-in-kernel**: Multiset = Quotient List — `decide` reduces through
   `Quot.lift`; if it sticks, switch `lam` to a SORTED `List (ℕ × ℕ)` canonical
   representative (DESIGNER ROUND — statement fence: Species field type change
   needs sign-off; flag, do not improvise).
3. **The λ-multiset forcing steps** (Sp.g6Forcing, Sp.fullForcing) are the only
   hand-combinatorics; both ≤ ~40 lines with `Multiset.cons_erase`.
4. NOT HERE (per §0): realizability/census theorems; VP/verdict semantics; height
   parameters and depths (the P̂ enrichment — §D4-R L3 rev 9's (h_r, u*_r) pair);
   [2b] state types; any count or mass. Consumers: MovesV reads cells/menus from
   this corpus; MovesX reads SP.4/SP-DAG; MovesS defines its (m, c) roster on
   `Species.lam` ITSELF (the F15 deferral — §2's record; wave-4 sync item).

## 7. Roster summary  [REV 5]

67 units + 3 def-only files. By group: A 5 · B 8 · C 4 · D 6 · E 11 ·
F SP-COMP/words/entrance 12 (REV 5: +n1Branch) · G 3 · H 18 (REV 5:
thresholdData → 6 one-display units).

easy: 37 — all of A; shCongr/shDvd/shE1/shEquiv/shStage/shExample;
  anchorBoundGeo/b4Derived; encodeCard; outFinite/selfloopFull/fullUnique/
  rankStepInc/rankStrict; compEdges/tauWord/n1RootConfirming/collapseSublist/
  collapseNeNil; n3card53/n3reachable/n3selfloops/n3postincW1/n3terminal5/
  n3R3check/n3exclusionLists/n3exclusionCards/n3multiSide6/n3multiSideMem/
  n3NstarValues/n3NstarDomain/n3entrancePatterns.
medium: 26 (incl. 5 easy-medium: compMember, compCollapsed, n1Word,
  n1Branch, n1singleton) — shSlots/shAnchorInv; anchorBoundCensus/g6Forcing;
  compEncode/lamEncode/finThm/finWords; selfloopChar/fullForcing/rankRadix/
  dagWalk/dagWords; collapseEqSelf/collapseWalk/entranceDef; compEnumComplete;
  n3rootLetters/n3closureStep/n3catalogueEq/n3menuMap.
medium-hard: 4 — encodeInj, rankStepRec, lamEnumComplete, speciesEnumComplete.
hard: 0. Split points as before.

## 7c. REV 5 CLOSING ADJUDICATION (Codex rev-4: 1c/1g; Fable rev-4: 0c/1g)

  CX-1' crit  n = 1 len-0 vacuity   → CODEX RIGHT, FIXED: the rev-4 pushback
        conflated τ-hen's "NO window read" with an empty CATALOGUE word AT
        n = 1 — the note's n = 1 clause says "the catalogue word is the
        single ROOT letter", only the τ-WORD is empty. New model law hN1
        (n = 1 → 0 < len η, the minimal field carrying the display; len 0
        stays real at n ≥ 2 per (τ-hen)); new unit Sp.n1Branch derives
        len = 1 ∧ datum = confirmingRoot1 and packages every branch's
        CatalogueWord — the all-len-0 model at n = 1 now violates hN1.
  CX-2' gap   thresholdData 6-in-1  → CODEX RIGHT, FIXED: split one display
        each (exclusionLists / exclusionCards / multiSide6 / multiSideMem /
        NstarValues / NstarDomain); REV-4 pins unchanged, redistributed.
  FA-1' gap   succTerminal domain   → FABLE RIGHT, FIXED: hs : InCatalogue
        added per the C-3 pattern (SP.4's "For s ∈ 𝒮_n^raw" block quoted);
        stageLaws_terminal stays unrestricted (corpus-internal).
  Codex CONFIRMED the rev-4 refutations (unbounded reads; the VP rider) and
  all §7b dispositions; Fable walked the menu chain and verified both
  refutations independently. No other finding on either side.

## 7b. REV 4 SPLIT-VERDICT ADJUDICATION (Codex REJECT 5c/8g vs Fable ACCEPT
0/0 on identical rev-3 text; principle: evidence over plausibility; Lean
settles typing at E-phase)

  C-1  crit  CanTreeModel vacuity/∞   → CODEX PART-RIGHT, FIXED+PUSHBACK:
       len : ℕ∞ now REPRESENTS infinite chains prefixwise ("Infinite branches
       are catalogued prefixwise", SP.5); hTotal : Nonempty Branch pins the
       empty model (D4R.0-K(a) totality DISCHARGED — quoted at the field).
       PUSHBACK, note-quoted: len η = 0 is a REAL case, not degeneracy —
       "(τ-hen) … halts with NO window read ever opened"; branches are NOT
       finite ("The number of READS stays unbounded" — SP.2/SP-DAG scope), so
       NO finiteness pin is admissible; the SP-DAG tie lands as the new
       CONCLUSION unit Sp.compCollapsed (collapsed prefix ≤ 6n²).
  C-2  gap   hVerdictPin ≠ residual   → CODEX PART-RIGHT, FIXED+PUSHBACK:
       scope widened to ALL finite nonempty words (V_term edges from
       CONTINUING letters end words too — quoted at the field). PUSHBACK: τ +
       detection-cap CONTENT is [3t]/VP-owned and not encodable from
       §M-SPECIES's text; the field is the residual's named RIDER (alphabet +
       attachment site), weak by design — G4's honest-perimeter record stands.
  C-3  crit  outFinite too strong     → CODEX RIGHT, FIXED: hs : InCatalogue
       added; SP.4 quoted ("For s ∈ 𝒮_n^raw, the OUTGOING MENU Out(s) …").
  C-4  crit  selfloopChar domain      → CODEX RIGHT, FIXED: the note's SUCC is
       catalogue-restricted ("SUCC(s) := { s′ ∈ 𝒮_n^raw : …}"); main statement
       now s ∈ Succ n s ↔ … given InCatalogue; the StageLaws computation kept
       as the stated helper (loops3's Bool filter reflects it). Fable verified
       content, misread the domain.
  C-5  gap   EntranceShape datum      → PART-FIXED EARLIER (rev 3) + RECORDED:
       (gsel, μsel) is the letter-level face; size-e-block/β₀ identification
       is [1v] CTS-M(iii)'s OWNED datum (already in hypothesis_fields);
       depths stays inert parameter DATA (Fable's minor observation concurs) —
       no [2a] law constrains run-lengths, so none is stated. DISPOSITION:
       Codex's reading pointed at fields that §M-SPECIES does not own.
  C-6  gap   Prop/Bool ill-typing     → CODEX RIGHT, FIXED: routing convention
       block in DefsEnum; every flagged target rewritten (List.contains /
       decide (≤) / .isSome); §1.2's decidability sentence made honest
       (Fable NOTE A folded in).
  C-7  crit  menu exactness weak      → CODEX RIGHT, FIXED: menu3_exact_global
       added with the closure chain IN the unit (SuccStep → Coherent∧Budget →
       enum → closure_step3 → catalogue → local table) and its deps declared.
  C-8  crit  multiSide6 trivial pin   → CODEX RIGHT, FIXED: RHS = six LITERAL
       Species terms transcribing the R1–R4 rows + Nodup; a wrong/repeated
       letter or hand-tuned table now fails the decide.
  C-9  gap   exclusion-list bodies    → CODEX RIGHT, FIXED: literal bodies in
       DefsN3 (11 + 2 row-named letters, catalogue3 order).
  C-10 gap   lamEncode elision        → CODEX RIGHT, FIXED: lamMatrix def +
       lamMatrix_inj with full binders/bounds.
  C-11 gap   compEnum_nodup elision   → CODEX RIGHT, FIXED: spelled.
  C-12 gap   confirmingRoot1/deps     → CODEX RIGHT (Fable NOTE B concurs),
       FIXED: literal declared; Sp.g6Forcing added to deps.
  C-13 gap   collapseWalk 4-in-1      → CODEX RIGHT, FIXED: split into
       collapseSublist/collapseNeNil/collapseEqSelf/collapseWalk.
  FABLE ACCEPT: sustained on the erratum (§9; Codex CONCURS), order
  discipline, collapseRuns semantics, the fence, G4's weakening, and all
  content re-derivations; overturned on C-3/C-4 domain readings and on
  treating C-6/C-7/C-8 as non-blocking. Both-verdict lesson recorded: content
  audits (Fable) and Lean-surface audits (Codex) decorrelate — keep both.

## 8. REV 2 findings → repairs (audit MOVESSP_AUDIT_CODEX_2026-07-28.md)

  F1  crit compMember circular      → CanTreeModel (raw engine laws only: hRoot/
      hStage/hCoh/hHalt); full (n, p, f, η, r) prefix; SuccStep ASSEMBLED in
      the proof, InCatalogue concluded (§2 + group F).
  F2  crit compEdges circular       → same interface; Out-membership concluded
      through compMember's InCatalogue (no field mentions Out/Succ).
  F3  crit CatalogueWord endpoint   → structure laws hLast (last letter W = 1)
      + hFirstW1 (no earlier confirming read); tauWord_spec unconditional.
  F4  crit EntranceShape too weak   → block-entry selection (gsel, μsel) typed;
      height-pair + per-run depth parameter SLOTS as fields; finiteness theorem
      quantifies over EntranceShape via new collapseRuns/collapseWalk.
  F5  crit thresholdData unpinned   → filter identities on linCount (λ-content)
      + named-letter list equalities + per-name N*₃ values; lengths demoted to
      trailing sanity.
  F6  crit R3 single variant        → R3letterA ([2]) and R3letterB ([1,1])
      both defined, both checked.
  F7  gap  D4R.0-K(c) by omission   → explicit field CanTreeModel.hVerdictPin;
      §0 bullet rewritten; named in every group-F hypothesis_fields.
  F8  gap  reflSucc elided          → both iffs spelled with full binders;
      moves_ref extended to the root clause.
  F9  gap  shDvd "same hyps"        → full binder list; e ≥ 1 explicitly NOT
      assumed (recorded).
  F10 gap  shSlots elided           → both theorems with complete binders.
  F11 gap  shEquiv non-Prop hyp     → hypothesis struck; sh_image pure; census
      identification as fully-stated sh_geo_slots.
  F12 gap  shStage corollary        → sh_e1_stage spelled (σ = 0 + position
      identity at a Moves.Stage).
  F13 gap  selfloopFull types       → (hc : Coherent s) (hb : Budget n s) in
      the statement.
  F14 gap  rankRadix unauditable    → fullBit defined in §2; hypotheses and the
      four-case disjunction written out.
  F15 gap  mcRoster out-of-scope    → STRUCK; deferred to MovesS wave-4 (records
      in §2, group F, §6).
  F16 gap  rootLetters ambiguity    → ONE canonical statement (the membership
      equivalence) from two decide facts; multiplicity content via n3card53's
      Nodup; duplicate-candidate caveat recorded.
  F17 gap  entrancePatterns ellipsis→ full conjunction, one clause per displayed
      pattern, all letters named.

## 8b. REV 3 findings → repairs (audit MOVESSP_AUDIT_FABLE_2026-07-28.md)

  C1  crit loops3 order-false       → target reordered [loopQ3, loopQ23]
      (catalogue3 = R ++ Q3 ++ Q2 ++ Q1 ++ I); ORDER DISCIPLINE rule added at
      §4 with a full audit of every pinned-list decide target (terminal3 ✓,
      entrance groupR filter ✓, fieldSizeExcluded2/3 declared in catalogue3
      order, all other targets membership/`all`-form).
  C2  crit entrance ▸(1,2) roster   → corrected to the true THREE members per
      group ([rootR4sel12, rootR5sel12, rootR6sel12]; Q3 length 3), per the
      note's own R6 row and row-unrestricted menu law; the note-side
      "[R4/R5 rows]" bracket recorded as a VERIFIED erratum candidate (§9),
      cited by the unit, baked into no target.
  G1  gap  collapseRuns unpinned    → defining equations written into §2 (=
      List.destutter (· ≠ ·)); pinning lemmas collapseRuns_ne_nil +
      collapseRuns_eq_self_iff added to Sp.collapseWalk (const-[] now fails
      the def AND both lemmas).
  G2  gap  n1 dependency cycle      → Sp.n1Clause split: Sp.n1RootConfirming
      (no enum deps) → Sp.n1singleton → Sp.n1Word; deps rewritten; DAG
      acyclic.
  G3  gap  fence vs hRoot           → fence retargeted to CLOSURE-side objects
      only (InCatalogue/Succ/Out); the fields-unfold-to-premises fact stated
      as the note's own step-(1)–(3′)/(5) scoping, not a leak.
  G4  gap  non-detachable overclaim → weakened to "visible": the trivial
      (verdict, hVerdictPin) discharge displayed; ledger carried by the named
      field + docstring, not by the type.

## 9. NOTE ERRATUM CANDIDATE (routed to the coordinator; NOT applied to the
frozen note by this blueprint)

LOCATION: `lean/notes/MOVES_2026-07-24.md`, §M-SPECIES SP.6, the entrance
display (locate by text, per the note's own grep-anchor convention):

  "ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as
   depth slots): into the μ=2 block: root▸(1,2) [R4/R5 rows], or
   root▸(1,3)·(Q3-loop)^d·▸(1,2); …"

FINDING (CONFIRMED as an incomplete gloss; Fable audit C2 root cause): the
bracket "[R4/R5 rows]" omits R6's ▸(1,2) row. Cross-check against the note's
OWN displays:
 (1) the hand catalogue's R6 row lists a ▸(1,2) selection —
     "R6  e=1, ℓ=3, a=0 | {(3,1)}▸(3,1); {(2,1),(1,1)}▸(2,1) and ▸(1,1);
      {(1,3)}▸(1,3); {(1,2),(1,1)}▸(1,2) and ▸(1,1); {(1,1)³}▸(1,1)" —
     a ROOT letter whose designated selection is (1, 2);
 (2) the menu law is row-unrestricted — "▸(1,2) → Q2 letters" — so that
     letter's continuing branch opens the child window [0, 2]: the μ=2 block;
 (3) the same display's increment-landing clause quantifies over "the
     ▸(2,1)/▸(3,1)/e=2/e=3 rows of R, Q2, Q3" — the roster-of-rows form the
     ▸(1,2) clause evidently intends.
The head clause "root▸(1,2)" is CORRECT as stated; only the parenthetical
bracket is incomplete. PROPOSED CORRECTION: "[R4/R5 rows]" → "[the ▸(1,2)
rows of R4/R5/R6]" (three letters; likewise three Q3 copies on the loop-exit
path). No count, menu edge, or gate quantity of the note changes: the 53, the
menu map, and the M-n3/V2 gate records are untouched (the census walked the
true menu; only the gloss bracket under-listed). Blueprint-side: unit
Sp.n3entrancePatterns pins the TRUE roster and cites this section; nothing
silently repairs the note.

codex
1. No findings.

The three REV 5 repairs check out:

- `hN1` forces every branch at `n = 1` to have a nonempty catalogue word; `hRoot` makes read `0` confirming, `hHalt` forces `len η = 1`, and `Sp.n1Branch` plus `SnRaw1_eq` pins its datum to `confirmingRoot1`.
- The all-`len = 0` model is therefore impossible at `n = 1`, while `hN1` imposes no restriction at `n ≥ 2`, preserving genuine `(τ-hen)` zero-letter branches.
- The threshold material is split into six one-display units.
- `succ_terminal` now carries the required catalogue-domain hypothesis `hs : InCatalogue n s`.

Counts: 0 CRITICAL / 0 GAP

ACCEPT
tokens used
61,773
1. No findings.

The three REV 5 repairs check out:

- `hN1` forces every branch at `n = 1` to have a nonempty catalogue word; `hRoot` makes read `0` confirming, `hHalt` forces `len η = 1`, and `Sp.n1Branch` plus `SnRaw1_eq` pins its datum to `confirmingRoot1`.
- The all-`len = 0` model is therefore impossible at `n = 1`, while `hN1` imposes no restriction at `n ≥ 2`, preserving genuine `(τ-hen)` zero-letter branches.
- The threshold material is split into six one-display units.
- `succ_terminal` now carries the required catalogue-domain hypothesis `hs : InCatalogue n s`.

Counts: 0 CRITICAL / 0 GAP

ACCEPT
