# O5triple — O-5 + D-7a/b/c (the leaf/factor bijection triple) — Phase-B verification brief REV 3

**SELF-CONTAINED. Fable prover, 2026-07-31 (rev 1); REV 2 repaired the V18 hostile
pass; REV 3 repairs the V23 hostile pass on rev 2.** Verification target: hand THIS
document to a fresh-context adversarial verifier with the standing charge (quote each
offending passage; classify *critical error* vs *justification gap*; fix nothing).
V23's verdict on rev 2 was SOUND-WITH-GAPS: ZERO critical errors ("the main conditional
proof chain is coherent"; full-proof audit clean: H0, REP-IRR, NODE, STEEP — including
the V18-8 signed-slope repair — Theorems A–E, and every deliberate non-consumption
claim, each conditional on floor + flags-at-full-strength + interface). The four
findings, all justification gaps, were ledger/classification defects, not proof steps:
(1) (L5b)'s displayed source statement does not by itself pin the normalization STEEP
consumes; (2) (R-0)'s product characterization is assumed, not derived from the
displayed equivalence; (3) the [S]/[M] roster understates the present proof burden of
both [S] flags; (4) the (R-0) consumption ledger is undercounted. Every confirmed
passage is carried byte-stable (rev 3 = copy of rev 2, edited only at the finding
sites); §0″ is the finding-by-finding disposition table (§0′ = the V18 round's,
historical).

## 0. Charge and claims

Target nodes (MATH_COMPLETION_TREE_2026-08-01.md §2.4 O-5 + DELTA-1 node D-7a/b/c):

> **(O-5)** At a decided ns-free level-N verdict class of the canonical classifier, with
> carried tree T and verdict σ = typemult(T): for EVERY monic separable degree-n lift g,
> (LEAF) each leaf's halting verdict is the true factorization datum of an actual
> irreducible factor of g — (τ-hen) leaves via (HEN-LIFT), (τ-irr) leaves via (OM-SAT)
> through the engine↔GMN dictionary; (ASSEMBLY) the leaf map
> {leaves of T} → {monic irreducible factors of g} is a bijection onto
> factors-with-multiplicity, g = ∏(leaf factors), hence type(g) = typemult(T) = σ.
> **(D-7a)** distinct leaves determine DISTINCT (pairwise coprime) irreducible factors.
> **(D-7b)** every monic irreducible factor of every separable lift g is hit by some leaf.
> **(D-7c)** the leaf multiset's (e, f) data equals the factors-with-multiplicity
> invariants of g, uniformly over ALL lifts g of the decided class.

V6 finding 16 (the reason these are separate nodes): the previously listed inputs (product
formula + degree checksums + "histories are chains") do NOT alone yield a bijection. This
brief answers that finding by (i) proving a SEMANTIC leaf/factor bijection theorem
(Theorem A, §4) over the pinned GMN floor, CONDITIONAL on exactly the FIVE named
transcription flags of the §2 roster — classified at rev 3 by present proof burden:
four mathematical plus one mixed, no flag purely statement-matching except clause
(R-0a) (V23 finding 3 retired rev 2's "two statement-matching, three mathematical"
tally); rev 1
labeled this "unconditional … with reading flags", which V18 finding 9 correctly
rejected (a flag is an assumption until its duty is executed) — and (ii) deriving the
full triple from
Theorem A plus a DISPLAYED interface (I-1)–(I-3) (§5) whose clauses are priced item-by-item
to the tree's upstream leaves (O-2a, O-2b, O-3). Headline dependency sharpening:

> **D-7b (coverage) does NOT consume O-3's no-missing clause.** Injectivity of the leaf
> transport plus the engine's own degree checksum Σ e·f = n plus Theorem A's semantic
> checksum force surjectivity by counting (Theorem B). Only the no-phantom-side clauses
> of O-3 are consumed anywhere in the triple.

Status of everything here: PROVED-UNVERIFIED until fresh-context passes accept it.
Falsifiers ran FIRST: `verification/openmath/o5triple_check.gp`, 1341 checks, 0 failures
(§9), including a negative control showing the corner-certificate band of Lemma STEEP is
load-bearing (sub-band lifts DO change type).

## 0′. Rev-2 disposition table (V18 findings → repair sites)

V18 verdict on rev 1: SOUND-WITH-GAPS — no critical errors; "no quoted passage
establishes a demonstrably false theorem." Per-finding dispositions:

| # | V18 finding (class) | disposition at rev 2 |
|---|---|---|
| 1 | (GMN-COH) is the recursion's load-bearing glue — "substantial mathematical coherence, not merely cosmetic notation"; Theorem A is conditional on it (justification gap) | ACCEPTED. §2 roster: (GMN-COH) classified [M] (mathematical); §4 carries an explicit conditionality display; headline relabeled (see finding 9) |
| 2 | (R-2): "calling it a 'convention' understates what is required — factor extraction and degree exhaustiveness are mathematical assertions" (justification gap) | ACCEPTED. §2 roster: (R-2)/(L3+)_r reclassified [M]; rev 1's "NOT new mathematics" framing DELETED; NODE's seam-flag label corrected |
| 3 | (R-1) not spelled out by the supplied (L4) summary (justification gap) | ACCEPTED. §2 roster: (R-1) kept [S] (statement-matching), exact duty and consumption site (REP-IRR) displayed |
| 4 | the order-0 identification f_{t₀} = g_j is a FOURTH transcription obligation, absent from the named floor — "the honesty ledger therefore understates the open transcription surface" (gap + ledger leak) | ACCEPTED. NEW named flag (R-0) [S] in the §2 roster; Theorem A(2)surj cites (R-0); §8 ledger updated |
| 5 | (L13) applicability: the tree is built on an arbitrary admissible family; compatibility with GMN's process/type sets "plausible but not established" (justification gap) | ACCEPTED. NEW named flag (R-3) [M] in the §2 roster; Theorem A(1) cites (R-3) (and (GMN-COH) for non-completeness) |
| 6 | Theorem B presupposes β_g's existence without listing it (minor formal imprecision) | ACCEPTED. §6 Theorem B now assumes (I-1)'s map preamble explicitly |
| 7 | STEEP consumes Def 2.5's integer-valued normalization, unpinned — (L5) pins only Def 2.3/Lemma 2.4 (gap + consumption-ledger leak) | ACCEPTED. NEW floor pin (L5b) in §2 with the exact source statement from the verified citation ledger; STEEP's denominator step cites (L5b) |
| 8 | STEEP's [0,1]-separation assumes the signed steepness convention and principal-part membership without the one-line convex-hull argument (minor gap) | ACCEPTED. STEEP proof (b): conventions displayed + the hull step written out |
| 9 | "calling Theorem A 'unconditional' is … an overstatement" — the flags are assumptions until the transcription duties are executed (relabel) | ACCEPTED. Relabeled at §0, §4 (title + conditionality display), §8, VERDICT: Theorem A is FLAG-CONDITIONAL |

No V18 finding is disputed. The diff against rev 1 touches exactly the sites named
above plus this table and the header.

## 0″. Rev-3 disposition table (V23 findings → repair sites)

V23 verdict on rev 2: SOUND-WITH-GAPS — no critical errors; "the document is …
not unsound: its principal conclusions are explicitly conditional, and no quoted
passage proves a demonstrably false theorem." Four justification gaps:

| # | V23 finding (all: justification gap) | disposition at rev 3 |
|---|---|---|
| 1 | (L5b) does not unambiguously establish the normalization consumed by STEEP: Def 2.5's quoted words fix neither value group ℤ for the displayed function nor the reconciliation of "extending v" with v_r∣_K = e₁⋯e_{r−1}·v; the "value group ℤ" parenthetical was inference, not source | ACCEPTED. §2: NEW companion pin **(L5b′) = GMN Prop 2.6**, cited ACROSS packages from O-2a §1 (L2)'s transcription (the dictionary seam — SYNTH4 note) rather than re-transcribed: it states the on-K identity and integer-valuedness on O[x]∖{0} as SOURCE clauses. STEEP's denominator step re-keyed to (L5b′); its argument unchanged (V23 confirmed it "once integer-valued ordinates are granted") |
| 2 | (R-0)'s passage from the per-irreducible divisibility criterion to "f_{t₀} is the product of ALL such factors" uses product/cluster compatibility not contained in the quoted equivalence — the flag's assumption boundary is wider than its "DERIVED here … via H0" wording | ACCEPTED. §2 roster: (R-0) split into **(R-0a)** (divisibility vocabulary) + **(R-0b)** (product characterization), BOTH openly assumed; "derived" now labels only f_{t₀} = g_j and ω₁(g) = a_j, which do follow from (R-0a)+(R-0b)+H0+(L5); Theorem A(2)surj's bracket rewritten to match |
| 3 | both [S] entries carry mathematical content as written: (R-1) is substantive until its exact GMN statement is produced; (R-0) is mixed — "the roster's binary classification understates their present proof burden" | ACCEPTED. §2 roster: the escalation rule is now APPLIED, not merely stated — a flag counts [S] only when the exact source statement is already located and quoted. (R-1) reclassified **[M]** (pending its statement match; retro-classifies to [S] if the match lands); (R-0) classified **mixed** ((R-0a) [S], (R-0b) [M]). Tallies at §0, §8, VERDICT updated |
| 4 | "(R-0) in (2)surjective and (3) … and no others" is too narrow: the Definition-𝒯(g) track-node alignment and Theorem A's injectivity (root divergence: placing the track cluster in H0's list) also consume it | ACCEPTED. §4 conditionality display corrected — (R-0) at the 𝒯(g) alignment, (2)injective, (2)surjective, (3) — with the audit criterion displayed; A(2)inj's proof now cites (R-0) explicitly at its root-divergence step; the §2 roster's consumed-at line gains A(2)inj |

No V23 finding is disputed. V23 also ruled that rev 2's "No V18 finding is disputed"
was fair but must not be read as "every V18 finding completely repaired": V18-7 and
V18-4 carried residue, which is exactly V23's findings 1 and 2 — closed here; the §0′
table stands as the historical record. The diff against rev 2 touches exactly the
sites named in this table plus the header.


## 1. Setting and vocabulary

* K = ℚ_p, O = ℤ_p, v = v_p normalized by v(p) = 1, residue field F = F_p. (§7 remark 3:
  everything in §§2–4 holds verbatim over any complete discretely valued base with the
  stated properties; the ℚ_p pin matches the audited LIT-4 scope.)
* g ∈ O[x] monic of degree n ≥ 1, **separable** := squarefree in K[x] (⇔ disc g ≠ 0).
* For monic irreducible F ∈ K[x] dividing a monic g ∈ O[x]: F ∈ O[x] (Gauss); with
  L = K[x]/(F), write e(F) = e(L/K), f(F) = f(L/K). type(g) := the multiset
  {(e(F), f(F))} over the monic irreducible factors F of g counted with multiplicity
  (all multiplicities 1 when g is separable).
* **Classifier interface (opaque; quoted, not rebuilt).** A *decided ns-free class* is a
  level-N residue class x ∈ (ℤ/p^N)^n (coefficient tuple of a monic degree-n polynomial)
  at which a carried ns-free verdict tree T fibers with threshold thr(T) ≤ N (vocabulary:
  M06-vp-sound_fable.md §1, `VTree`/`fiberAt`; tree node O-5). T's **leaf slots** are:
  *hen slots* — one per simple irreducible factor ψ̄ in a Hensel payload, verdict
  (1, deg ψ̄); *irr slots* — halted (τ-irr) branches, each carrying an engine verdict
  (e_ℓ, f_ℓ) = (accE_ℓ, accF_ℓ), certified either by saturation (residual multiplicity
  μ = 1 at the last read) or by a corner certificate (the steep-corner read; §3 Lemma
  STEEP). ns-freeness: no (τ-ns) leaf occurs (the fence-24/26 repair; K-4/K-6 are FALSE
  without it — M06 §2). Nothing below depends on engine internals beyond the displayed
  clauses (I-0)–(I-3) of §5.

## 2. Literature floor (pinned statements; one-line contents)

All GMN items are quoted from `docs/GMN_citations.md` (verified against arXiv:0807.2620v2;
standing caveat: printed-TAMS numbering confirmation owed ⇒ LITERATURE-CONDITIONAL).
Guàrdia–Montes–Nart, Trans. AMS 364 (2012) 361–416.

* **(L1) Thm 1.15** (polygon, order 1): distinct finite slopes of N_φ^-(f) split the
  tracked factor f_φ into factors F_i with one-sided polygons S_i and R_{λ_i}(F_i) ∼
  R_{λ_i}(f).
* **(L2) Thm 1.19** (residual, order 1): a side's residual factorization R_λ(f) ∼
  ∏ ψ_i^{a_i} (distinct monic irreducibles) splits the side factor into G_i with
  R_λ(G_i) ∼ ψ_i^{a_i}.
* **(L3) Cor 1.20** (leaf dichotomy, order 1): a_i = 1 ⇒ G_i irreducible with
  f(L/K) = m·deg ψ_i, e(L/K) = e.
* **(L4) Thm 2.11 / Def 2.12** (representative): every type t of order r−1 has a monic
  representative φ_r ∈ O[x] of degree m_r = m_{r−1}e_{r−1}f_{r−1} (m₁ = f₀), of type t,
  with R_{r−1}(φ_r) ∼ ψ_{r−1}.
* **(L5) Def 2.3 / Lemma 2.4**: N_r is a lattice (principal) polygon; f_t is the
  largest-degree factor of f divisible by t, deg f_t = m_r·ω_r(f).
* **(L5b) Def 2.5** (the order-r valuation; PIN at rev 2, closing V18 finding 7's
  consumption leak): v_r(P) := e_{r−1}·H_{r−1}(S_{r−1}(P)) — "a discrete valuation on
  K(x)^* extending v with index e₁⋯e_{r−1}" [exact pinned statement:
  `docs/GMN_citations.md` §2.1 "Definition 2.5 (p-adic valuation of order r)", verified
  there against arXiv:0807.2620v2; the ledger's gloss: "integer-valued, p-independent
  denominators"]. V23 finding 1: Def 2.5's quoted words alone fix neither the value
  group of the displayed function nor the meaning of "extending" — the normalization
  STEEP consumes needs the companion result, pinned next.
* **(L5b′) Prop 2.6** (the normalization clauses; NEW PIN at rev 3 = the V23-1
  repair). Quoted from O-2a's transcription — `O2a_phaseB_verifybrief_rev5.md` §1
  (L2) "Order-r valuation (Def 2.5, Prop 2.6)" (byte-identical there to the rev-4
  text that the V25 pass covered), same source arXiv:0807.2620v2; a
  CROSS-PACKAGE CITE, deliberately not re-transcribed (the dictionary seam: one
  transcription, two consumers — SYNTH4 note):
  > "v_r(P) := e_{r−1}·H_{r−1}(S_{r−1}(P)) defines a discrete valuation on K(x)*
  > extending v with index e₁⋯e_{r−1}; v_r(a) = e_{r−1}·v_{r−1}(a) for a ∈ K. v₁ = v
  > on coefficients … On O[x]∖{0} the values are nonnegative integers."
  Provenance honesty: that transcription has stood through O-2a's five hostile passes
  (V10/V14/V20/P2/V25) with no finding against it — passes that demonstrably exercised
  the transcription-audit charge (V20 caught O-2a's (L6) up-to-translation
  overstatement) — and it remains LITERATURE-CONDITIONAL like every pin here; if it
  were ever found unfaithful, both packages fail at this ONE site (single-point seam
  by design). Displayed consequences consumed by Lemma STEEP, now read off SOURCE
  clauses rather than inferred from Def 2.5's words (the V23-1 repair):
  (i) [integrality] every finite point (i, u_i) of N_r(g) for monic g ∈ O[x] lies in
  ℤ × ℤ: u_i = v_r(a_i·φ_r^i) with a_i·φ_r^i ∈ O[x]∖{0} (a_i the φ_r-adic
  coefficients, in O[x]), and on O[x]∖{0} the values of v_r are nonnegative integers
  — the quoted clause verbatim;
  (ii) [the "extending" reconciliation] "extending v with index e₁⋯e_{r−1}" is
  extension-with-INDEX (value-group index), NOT value-preserving extension: the quoted
  on-K identity v_r(a) = e_{r−1}·v_{r−1}(a), unrolled with v₁ = v, gives
  v_r|_K = e₁⋯e_{r−1}·v as a displayed formula — the normalization is carried by a
  quoted identity, not by the word "extending".
  Normalization note (unchanged from rev 2): N_r is drawn with v_r-ordinates
  ((L5)/Def 2.3: the "φ_r-adic, v_r-" polygon), hence over the ℤ × ℤ lattice; the
  citation ledger's "ℤ × (1/(e₁⋯e_{r−1}))ℤ" gloss is the same object with ordinates
  divided by e₁⋯e_{r−1} — NOT the convention used here.
* **(L6) Def 2.21**: the order-r residual polynomial R_λ(f) ∈ F_r[y] is monic of degree
  d(S), never divisible by y; types require ψ_r ≠ y.
* **(L7) Thm 3.1** (polygon, order r): ω_r(f) > 0 and N_r^-(f) = S₁+…+S_g ⇒
  f_t = F₁⋯F_g, N_r(F_i) = S_i up to translation, R_{λ_i}(F_i) ∼ R_{λ_i}(f).
* **(L8) Cor 3.3**: d(S) = 1 ⇒ the side factor is irreducible with f = f₀⋯f_{r−1},
  e = e₁⋯e_r.
* **(L9) Thm 3.7** (residual, order r): R_λ(f) ∼ ∏ ψ_i^{a_i} ⇒ f_{t,λ} = G₁⋯G_t with
  N_r(G_i) one-sided of slope λ and R_λ(G_i) ∼ ψ_i^{a_i}.
* **(L10) Cor 3.8 / Def 3.9** (= (OM-SAT)): a_i = 1 ⇒ G_i irreducible with
  e = e₁⋯e_r, f = f₀f₁⋯f_r; a type with ω = 1 is f-complete and certifies an
  irreducible factor.
* **(L11) Def 3.10 / eq. (37)**: Hensel + the theorems of the polygon and residual
  polynomial in orders 1…r give the factorization f = f_{r,∞}·∏_{t ∈ T_r(f)} f_t.
* **(L12) Lemma 3.11**: descent past order r triggers exactly at a non-separable
  order-r residual.
* **(L13) Thm 4.18 / Cor 4.19** (termination): for monic separable f there is r ≥ 0 with
  every type in t_r(f) f-complete; the process finishes in ≤ ind(f) steps.
* **(HEN-LIFT)** [LIT-3; LITERATURE-CANDIDATE, exact numbers owed; Mathlib probe flagged
  — M06 §4.1]: f ∈ O[x] monic, f̄ = ψ̄·h̄ with ψ̄, h̄ coprime monic ⇒ unique monic lift
  factorization f = g·h with ḡ = ψ̄, h̄-part matching; if ψ̄ is irreducible then g is
  irreducible over K, generates the unramified extension of degree deg ψ̄, and
  (e, f)(g) = (1, deg ψ̄).
* **(DEFECTLESS)** [LIT-2, Serre LF II §3]: for finite L/ℚ_p, e(L/K)·f(L/K) = [L:K];
  hence deg F = e(F)·f(F) for every monic irreducible F ∈ O[x].

**The transcription-flag roster (REV 2: FIVE named flags — V18 findings 1–5; REV 3:
classification by PRESENT proof burden — V23 finding 3).** Each
flag is an ASSUMPTION of this brief until its transcription duty is executed against the
GMN text; Theorem A and everything downstream is CONDITIONAL on all five (the V18-9
relabel; rev 1's "reading duties, NOT new mathematics" framing is retracted for the [M]
flags). Classes: **[S]** = statement-matching — the duty is locating and quoting an
exact GMN statement whose content is the flag; if the expected statement is absent, the
flag ESCALATES to [M]. **[M]** = mathematical — the flag asserts genuine factorization
content, expected to be carried by GMN's text or proofs, but a compatibility lemma may
have to be proved, not merely quoted. REV 3 applies the escalation rule NOW rather
than at duty-execution time (V23 finding 3: "classifying it as purely [S] assumes the
very source match still owed"): a flag counts [S] only when the exact source statement
is ALREADY located and quoted. Under that standard the roster reads: (GMN-COH),
(R-2)/(L3+)_r, (R-3) [M]; (R-1) [M] (pending its statement match; retro-classifies to
[S] if the §2 duty produces the exact statement); (R-0) MIXED ((R-0a) [S], (R-0b)
[M]). Rev 2's "two statement-matching, three mathematical" tally is RETRACTED: as
written, every flag except clause (R-0a) carries mathematical content.

* **(GMN-COH)** [M] (flow coherence; the content of (L11)'s warrant sentence): for a
  sprouted type t′ = (t; λ_S, ψ) of order r (sprouted because a(S,ψ) ≥ 2), the (L9)
  dissection factor G_{S,ψ} of f equals f_{t′}, the type-t′ cluster of f, and ω_{r+1}(f)
  (w.r.t. t′ and its representative) = a(S,ψ). [The per-node identity underlying
  eq. (37) — the identity that lets Theorem A's induction recurse; V18 finding 1:
  load-bearing coherence, not cosmetic notation. Duty: match GMN §3's flow discussion;
  else PROVE the coherence lemma.] Consumed at: NODE(v) → Theorem A(1)/(2)/(3).
* **(R-0)** [MIXED: (R-0a) [S], (R-0b) [M]] (order-0 cluster identification; NEW named
  flag at rev 2 = V18 finding 4, previously an inline bracket in Theorem A's
  surjectivity; SPLIT at rev 3 = V23 finding 2). Two clauses, BOTH assumed:
  **(R-0a)** [S] (divisibility vocabulary): GMN's order-0 divisibility reads
  "t₀ | F ⇔ F̄ is a positive power of ψ̄_j" (GMN §1–§2 types-of-order-0 vocabulary).
  **(R-0b)** [M] (product characterization): f_{t₀} — (L5)'s largest factor of g
  divisible by t₀ — equals the product of the irreducible factors of g with
  ψ̄_j-power reduction. [V23 finding 2: (R-0b) does NOT follow from (R-0a) + H0
  alone — passing from the per-irreducible criterion to the full product uses
  compatibility of type divisibility with products/factor clusters, factorization
  content unless the eventually-matched GMN statement carries it; rev 2's "DERIVED
  here given the flag (via H0's per-factor clause)" overstated what was derived.]
  Displayed consequence, derived given BOTH clauses:
  f_{t₀} = ∏{F | g monic irreducible : F̄ a ψ̄_j-power} [(R-0b)] = g_j [H0's
  per-factor clause], and ω₁(g) at t₀ = a_j (degrees: deg f_{t₀} = m₁·ω₁(g) [(L5)],
  m₁ = deg ψ̄_j, deg g_j = a_j·deg ψ̄_j). Consumed at: the track-node/active-node
  alignment in Definition 𝒯(g) (ω₁(g) = a_j ≥ 2 at track nodes), Theorem
  A(2)injective (the root-divergence step — V23 finding 4), A(2)surjective (root
  descent), A(3) (root telescope).
* **(R-1)** [M — escalated at rev 3, V23 finding 3: the exact GMN statement is not
  yet produced, and as written the flag is substantive information about every
  constructed representative, load-bearing in REP-IRR; retro-classifies to [S] if the
  duty below finds the statement] (representative shape; the content of (L4)'s "of
  type t"): the
  constructed φ_r has one-sided N_i(φ_r) of slope λ_i with R_i(φ_r) ∼ ψ_i at every
  i ≤ r−1, top multiplicity 1. [Duty: confirm that GMN §2.1's chain display — stated for
  the type's own φ_{i+1}-chain — together with Def 2.12's "plays the analogous role…"
  sentence carries this for representatives; V18 finding 3: the (L4) pin alone does not
  spell it out.] Consumed at: REP-IRR.
* **(R-2)/(L3+)_r** [M] (exact-key polygon seam at order r): when j₀ := ord_{φ_r}(g) = 1
  the φ_r-adic development of g has a₀ ≡ 0 (mod the φ_r-slot), the polygon carries a
  side of slope −∞ of length j₀ contributing the EXACT factor φ_r^{j₀}, and the finite
  sides carry total length ω − j₀ with NODE(ii)'s degree bookkeeping. [V18 finding 2:
  factor extraction and degree exhaustiveness are mathematical assertions, hence [M] —
  not a "convention". The order-1 instance is O2a rev-2's (L3+), falsifier-covered there
  (871 forced exact-φ₁-divisibility samples, 0 findings).] Consumed at: NODE(ii),
  Theorem A(3).
* **(R-3)** [M] (process matching / termination applicability; NEW named flag at rev 2 =
  V18 finding 5): the types sprouted by §3's flow at the fixed admissible representative
  family are order-r types of g in GMN's sense, lying in the type sets t_r(g) to which
  (L13) applies — so (L13)'s r* bounds the order of every active node of 𝒯(g). [Duty:
  match §3's tree against GMN §4.1's process; the alignment point is (L12) — sprouting
  here (a(S,ψ) ≥ 2) is GMN's non-separable-residual descent. Until matched this is a
  compatibility ASSUMPTION, not a theorem.] Consumed at: Theorem A(1).

Standing vs rev 1: (GMN-COH), (R-1), (R-2)/(L3+)_r are rev 1's three declared flags,
contents unchanged; (R-0) and (R-3) are V18's two promotions of
inline asides to named flags; rev 3 reclassifies ((R-1) → [M] pending match, (R-0) →
mixed with its product clause split out) without changing any flag's asserted content
except the (R-0a)/(R-0b) split. (L5b)/(L5b′) are PINS (exact source statements on
file), NOT flags.

## 3. The semantic dissection tree and its factor system

Fix g monic separable of degree n and an **admissible representative family**: a choice of
representative φ (per (L4)) for every type sprouted by the flow below. All objects of this
section are relative to that fixed family. (The classifier's canonical key policy is one
such family — O-2a's OL-2a-1; cross-family invariance is D-5's business, NOT consumed.)

**Definition 𝒯(g).** A finite rooted tree:
* Root children, per monic irreducible ψ̄ | ḡ with multiplicity a: a **hen leaf** if
  a = 1; a **track node** (type of order 0) if a ≥ 2.
* At an **active node** t (a type of order r−1, r ≥ 1, with representative φ_r and
  ω := ω_r(g) ≥ 2), the children are: an **exact-key leaf**, present iff
  j₀ := ord_{φ_r}(g) = 1; and, for each finite side S of N_r^-(g) and each monic
  irreducible ψ | R_{λ_S}(g) with multiplicity a(S,ψ): an **(a=1) leaf** if a(S,ψ) = 1,
  an active node (the sprouted type t′ = (t; λ_S, ψ), order r) if a(S,ψ) ≥ 2.

**Lemma H0 (order-0 dissection).** Write ḡ = ∏_{j=1}^{s} ψ̄_j^{a_j}. There are unique
monic g_j ∈ O[x] with g = ∏_j g_j and ḡ_j = ψ̄_j^{a_j}; they are pairwise coprime; if
a_j = 1 then g_j is irreducible with (e,f) = (1, deg ψ̄_j). Moreover every monic
irreducible F | g has F̄ = a power of exactly one ψ̄_j, and F | g_j for that j.
*Proof.* Existence/uniqueness by induction on s from (HEN-LIFT)'s coprime split
(ψ̄_1^{a_1} vs the coprime rest; recurse on the second factor). Leaf clause: (HEN-LIFT)
part 2. Per-factor clause: if F̄ had two coprime nontrivial parts, (HEN-LIFT) would
factor F, contradicting irreducibility; so F̄ = ψ̄_j^a for a unique j. If F | g_i for
i ≠ j then F̄ | ψ̄_i^{a_i}, contradiction; F | g = ∏ g_i forces F | g_j. ∎

**Lemma REP-IRR.** A representative φ_r of a type t of order r−1 is irreducible over ℚ_p
with e(φ_r) = e₁⋯e_{r−1} and f(φ_r) = f₀f₁⋯f_{r−1} (empty products = 1).
*Proof.* r = 1: φ₁ is a monic lift of the irreducible ψ̄₀, so (HEN-LIFT) applied to φ₁
(whole reduction one simple irreducible) gives irreducibility and (1, f₀). r ≥ 2: by
(L4) + (R-1), φ_r carries one-sided polygons with residuals ∼ ψ_i, top multiplicity 1;
apply (L10) at order r−1 to f := φ_r with a = 1: the certified factor G of φ_r is
irreducible with f(G) = f₀⋯f_{r−1}, e(G) = e₁⋯e_{r−1}. By (DEFECTLESS),
deg G = e·f = (e₁⋯e_{r−1})(f₀⋯f_{r−1}) = m_r (unroll m_r = m_{r−1}e_{r−1}f_{r−1},
m₁ = f₀) = deg φ_r. A monic factor of φ_r of full degree is φ_r itself. ∎

**Lemma NODE (per-node dissection).** Let t be an active node of 𝒯(g) of order r−1 with
representative φ_r, ω = ω_r(g) > 0, j₀ = ord_{φ_r}(g). Then:
(i) j₀ ≤ 1 [φ_r² | g would contradict squarefreeness, φ_r being irreducible by REP-IRR];
(ii) f_t = φ_r^{j₀} · ∏_S ∏_ψ G_{S,ψ}, with S over the finite sides of N_r^-(g), ψ over
the distinct monic irreducible factors of R_{λ_S}(g), G_{S,ψ} ∈ O[x] monic with
N_r(G_{S,ψ}) one-sided of slope λ_S, R_{λ_S}(G_{S,ψ}) ∼ ψ^{a(S,ψ)}, and
deg G_{S,ψ} = m_r·e_S·a(S,ψ)·deg ψ ≥ 1;
(iii) the factors listed in (ii) are pairwise coprime, and every monic irreducible
F | f_t divides exactly one of them;
(iv) if a(S,ψ) = 1 then G_{S,ψ} is irreducible with
(e, f) = (e₁⋯e_{r−1}·e_S, f₀⋯f_{r−1}·deg ψ) [(L10)]; any side with d(S) = 1 — in
particular any side of horizontal length 1, which forces e_S = 1 = d(S) — has its factor
irreducible with (e, f) = (e₁⋯e_{r−1}·e_S, f₀⋯f_{r−1}) [(L8)];
(v) [(GMN-COH)] if a(S,ψ) ≥ 2 then G_{S,ψ} = f_{t′} for the sprouted type t′, with
ω_{r+1}(g) = a(S,ψ) > 0 at t′.
*Proof.* (ii): (L7) splits f_t along the finite sides; (L9) splits each side factor along
its distinct residual irreducibles. **Seam flag (R-2)/(L3+)_r [an [M] flag — §2 roster;
mathematical content, not a convention (V18 finding 2)]:** when
j₀ = 1 the φ_r-adic development of g has a₀ ≡ 0 (mod φ_r-slot), the polygon carries a
side of slope −∞ of length j₀, and the finite sides carry total length ω − j₀; the
−∞ part contributes the exact factor φ_r^{j₀}. Degree bookkeeping closes:
deg f_t = m_r·ω = m_r·j₀ + Σ_S m_r·ℓ(S) and Σ_ψ e_S·a(S,ψ)·deg ψ = e_S·deg R_{λ_S} =
ℓ(S). [The j₀ = 1 case at order 1 is exactly O2a rev-2's (L3+), falsifier-covered
there: 871 forced exact-φ₁-divisibility samples, 0 findings (`O2a_rev2_check.gp`); the
order-r transcription is owed with (GMN-COH).] (iii): distinct monic factors occurring in
one factorization of the squarefree g are pairwise coprime (a common irreducible divisor
would divide g twice); F | f_t = ∏(pairwise coprime) ⇒ exactly one. (iv): (L10)/(L8)
with the accumulated invariants; length-1 ⇒ e_S | ℓ(S) = 1 ⇒ e_S = 1, d(S) = ℓ/e_S = 1.
(v): consumed as (GMN-COH). ∎

**Lemma LEAF-INV (leaf invariants).** Each leaf L of 𝒯(g) carries a monic irreducible
factor G_L of g and invariants (e_L, f_L) = (e, f)(G_L), with deg G_L = e_L·f_L
[(DEFECTLESS)]: hen leaf (1, deg ψ̄_j) [H0]; (a=1) leaf (e₁⋯e_r, f₀⋯f_r) with
e_r = e_S, f_r = deg ψ [NODE(iv)]; exact-key leaf (e₁⋯e_{r−1}, f₀⋯f_{r−1}) [REP-IRR].

**Lemma STEEP (corner dichotomy — the one lift-variant leaf kind).** Let t be an active
node of order r−1 with representative φ_r, and suppose g satisfies the **corner
condition** at t: EITHER (a) j₀ = 1 (exact key), OR (b) j₀ = 0 and the segment from
(0, v_r(a₀)) to the polygon's leftmost vertex (1, u₁) on [1, ω] is strictly steeper than
the first finite side on [1, ω]. Then the [0,1] part of N_r(g) is a child separate from
every side on [1, ω] — in case (a) the exact-key leaf, in case (b) a length-1 finite side
(e_S = 1, d(S) = 1) — and in BOTH cases the associated factor is irreducible with the
SAME invariants (e, f) = (e₁⋯e_{r−1}, f₀⋯f_{r−1}).
*Proof.* (a): REP-IRR. (b): **Conventions (V18 finding 8).** N_r(g) is the lower convex
hull of the finite points (i, u_i) of the φ_r-adic development, drawn with v_r-ordinates
[(L5), (L5b)]; read left to right, its sides have strictly increasing slopes; "strictly
steeper" = strictly SMALLER (more negative) slope; N_r^-(g) is the negative-slope part.
**Hull step.** Write u₀ = v_r(a₀), μ = u₁ − u₀ (the [0,1] segment's slope); let H₁ be
the lower convex hull of ALL points (i, u_i) with i ≥ 1, and λ its first (leftmost,
hence smallest) slope — this is condition (b)'s comparator, since H₁'s slopes increase
left to right and its negative-slope sides are exactly the finite sides on [1, ω]; so
condition (b) says μ < λ. Every point (i, u_i) with i ≥ 2 lies on or above H₁, hence on
or above the line through (1, u₁) of slope λ (H₁'s minimum slope), hence STRICTLY above
the line through (0, u₀) of slope μ; and (1, u₁) lies ON the μ-line. So (1, u₁) is a
vertex of N_r(g) and [(0, u₀), (1, u₁)] is a full side of horizontal length ℓ(S) = 1.
Its slope satisfies μ < λ < 0 (λ is the slope of a finite side of the principal part),
so the side belongs to N_r^-(g). **Denominator step.** u₀, u₁ ∈ ℤ [(L5b′), clause (i):
v_r nonnegative-integer-valued on
O[x]∖{0} — the Prop-2.6 source clause, rev 3's V23-1 re-key], so μ ∈ ℤ: writing λ_S = μ = −h_S/e_S in lowest terms gives e_S = 1 and
d(S) = ℓ(S)/e_S = 1; NODE(iv)/(L8) gives irreducibility with
(e, f) = (e₁⋯e_{r−1}·1, f₀⋯f_{r−1}). Equal to (a)'s by inspection. ∎
[Falsifiers T1/T2 (§9): verdict constancy across exact-key and steep-side lifts of one
class, 71 checks, 0 failures — INCLUDING a degree-2 Eisenstein key; negative control:
6/10 lifts BELOW the corner band change type, so condition (b)'s band is load-bearing,
not slack.]

## 4. Theorem A — the semantic leaf/factor bijection (conditional exactly on the §2 floor + flag roster)

**Theorem A.** Let g ∈ ℤ_p[x] be monic separable of degree n ≥ 1, with a fixed admissible
representative family. Then:
1. 𝒯(g) is finite.
2. The leaf-factor assignment L ↦ G_L (Lemma LEAF-INV) is a BIJECTION from leaves(𝒯(g))
   onto the set of monic irreducible factors of g.
3. g = ∏_{L ∈ leaves(𝒯(g))} G_L.
4. Σ_{L} e_L·f_L = n, each term ≥ 1.

*Conditionality (the V18-9 relabel; the (R-0) ledger corrected at rev 3 — V23 finding
4).* Besides the pinned floor ((L1)–(L13), (L5b), (L5b′),
(HEN-LIFT), (DEFECTLESS)), the proof consumes ALL FIVE §2 flags, at these steps:
(R-3) and (GMN-COH) in (1); (R-1) via REP-IRR and (R-2) + (GMN-COH) via NODE,
throughout; (R-0) in Definition 𝒯(g)'s track-node/active-node alignment, in
(2)injective's root-divergence step, in (2)surjective, and in (3) [rev 2 listed only
the last two — the V23-4 undercount]. Audit criterion for the (R-0) itemization:
(R-0) fires exactly where an order-0 cluster f_{t₀} or its ω₁(g) is identified with
H0 data; the rev-3 line-by-line sweep found the four sites listed and no others.
Theorem A is proved over floor + flags; it
is NOT unconditional over the floor alone — each flag is an assumption until its §2
duty is executed.

*Proof.*
**(1) Finiteness.** Each node has finitely many children (a polygon of total finite
length ≤ n/m_r-scale has finitely many sides; residual polynomials have finitely many
irreducible factors). Depth: an active node of order r carries a sprouted type with
ω_{r+1}(g) = a ≥ 2 [(GMN-COH)], hence not g-complete (complete = ω 1, (L10)); by (R-3)
the sprouted types lie in GMN's type sets t_r(g), so (L13) applies: it gives r* with
every type in t_{r*}(g) g-complete, so no active node has order ≥ r*;
depth ≤ r* + 1 < ∞.
**(2) Well-defined.** G_L | g in every case: hen — H0; (a=1) — G_{S,ψ} | f_t | g
[(L5) + NODE(ii)]; exact-key — j₀ = 1 means φ_r | g. Irreducibility and invariants:
LEAF-INV.
**(2) Injective.** Let L ≠ L′ be leaves; both being leaves, neither is an ancestor of the
other, so their root paths diverge at a common node. First: by construction each leaf's
factor divides the cluster of every node on its path — G_L | (its own leaf factor);
one step up, the leaf is a child of a node t whose child-factor list (H0 at the root,
NODE(ii) elsewhere) contains the leaf factor; for higher ancestors, iterate NODE(v):
f_{t′} = G_{S,ψ} occurs in the parent's list, so f_{child} | f_{parent-cluster}
along the whole path — where the TOP step, placing a track node's cluster in the
ROOT's list, is the identification f_{t₀} = g_j [(R-0) — V23 finding 4: injectivity
consumes (R-0) at root divergence; rev 2 left this implicit in "H0 at the root"].
At the divergence node, G_L and G_{L′} divide DISTINCT members of
one pairwise-coprime factor list (H0/NODE(iii)). If G_L = G_{L′}, that common irreducible
would divide two coprime factors — contradiction. So G_L ≠ G_{L′}.
**(2) Surjective.** Let F | g be monic irreducible. Descend from the root: H0 places F in
exactly one root child's cluster. At a hen leaf, F = g_j (g_j irreducible, F | g_j
nonconstant). At a track node t₀: the type-0 cluster f_{t₀} per (L5) is the largest
factor divisible by t₀; order-0 divisibility reads as "F̄ is a ψ̄_j-power" [(R-0a)],
and f_{t₀} is the product of the irreducible factors with ψ̄_j-power reduction
[(R-0b) — ASSUMED, not derived: the passage from the per-irreducible criterion to the
full product is the flag's own content, V23 finding 2; rev 2's "so" overstated]; by
H0's
per-factor clause that product is exactly g_j, so f_{t₀} = g_j and F | f_{t₀} [(R-0)'s
displayed consequence, derived from (R-0a)+(R-0b)+H0]. At an active node t with F | f_t: NODE(iii) places F in exactly one listed
factor. Exact-key: F | φ_r ⇒ F = φ_r (leaf). (a=1): F | G_{S,ψ} irreducible ⇒
F = G_{S,ψ} (leaf). a ≥ 2: F | G_{S,ψ} = f_{t′} [NODE(v)] — continue at the child.
Orders strictly increase, bounded by (1), so the descent reaches a leaf L with F = G_L.
**(3) Product.** Finite induction up the tree: each node's cluster is the product of its
children's clusters/leaf factors (H0 at the root; NODE(ii)+(v) at active nodes;
exact-key contributes φ_r^{j₀}); telescope from the root.
**(4)** n = deg g = Σ_L deg G_L [by (3)] = Σ_L e_L f_L [(DEFECTLESS), LEAF-INV];
each e_L f_L = deg G_L ≥ 1. ∎

*Remark (relation to eq. (37)).* Theorem A is (L11)'s factorization driven to leaf
completeness: f_{r,∞} is the accumulated exact-key product, T_r(f) the complete types.
The transcription duty (GMN-COH) pins both at once.

## 5. The classifier interface (displayed hypotheses, priced to upstream nodes)

Fix a decided ns-free class x with carried tree T, thr(T) ≤ N, verdict σ = typemult(T).
Below, g ranges over the monic separable degree-n lifts of x. leafslots(T) = hen slots ⊎
irr slots (§1). Each interface clause is stated as consumed and attributed; NONE is proved
here.

* **(I-0) (context only; not consumed by any proof below).** Decided verdict classes are
  exact finite unions of level-N cylinders, one tree per box: the CYL package — DELTA
  node D-15 with O-1thr rev 2 Theorem 3 (pass-1 substantively clean; rev-2 hostile pass
  in flight). This grounds "the decided class" as an object; the theorems below only need
  x and T fixed.
* **(I-1) (leaf transport = O-3's no-phantom + acceptance clauses, composed with the
  dictionary Θ = O-2a, and the trace correspondence = O-2b).** For every g there is a map
  β_g : leafslots(T) → leaves(𝒯(g)) — 𝒯(g) built on the engine's canonical
  representative family (admissible per O-2a OL-2a-1) — such that for each slot ℓ:
  (a) [path data match] ℓ's engine history transports under Θ to the node path of
  β_g(ℓ): same order, and per level the engine read data map to g's semantic read data
  at that node (side data through OL-2a-2's frame/side dictionary; residual reads through
  OL-2a-3's residual identification).
  (b) [terminal event match] ℓ's halting certificate corresponds to β_g(ℓ)'s leaf kind:
  hen slot at ψ̄ ↦ the hen leaf at ψ̄; saturated (τ-irr) slot (μ = 1 at last read) ↦ an
  (a=1) leaf; corner-certified (τ-irr) slot ↦ the exact-key leaf OR a length-1
  steepest-side (a=1) leaf, i.e. g satisfies Lemma STEEP's corner condition at that node
  — WHICH of the two may depend on g.
  (c) [verdict match] (e_ℓ, f_ℓ) = (e_{β_g(ℓ)}, f_{β_g(ℓ)}) per LEAF-INV — O-2a
  Theorem 2's invariant matching (accE, accF) = (e₁⋯e_r, f₀⋯f_r), conditional on
  OL-2a-1..4.
* **(I-2) (transport injectivity — dictionary faithfulness).** For every g and all slots
  ℓ ≠ ℓ′: β_g(ℓ) ≠ β_g(ℓ′). Sufficient displayed form: distinct engine child data at a
  common history node transport to DISTINCT children of the corresponding 𝒯(g)-node
  (distinct side reads ↦ distinct sides; distinct residual reads ↦ ∼-inequivalent ψ's;
  a corner certificate vs a visible-side read ↦ the corner child vs that side's child —
  the corner side being strictly steeper than every visible side is the certificate's
  band content, cf. O-1thr rev 2's (N4) band; distinct hen payload elements ↦ distinct
  ψ̄'s); plus: distinct engine leaf histories differ in some read datum (leaves form an
  antichain — no leaf history extends another).
* **(I-3) (engine typing; available by construction of the carrier).** Each leaf slot
  carries (e_ℓ, f_ℓ) ∈ ℕ₊ × ℕ₊; σ = typemult(T) is a splitting type of degree n, so
  Σ_ℓ e_ℓ·f_ℓ = n (fiberAt clause (v) / σ's typing); each slot contributes multiplicity
  1 (ns-freeness: the μ-weighted (τ-ns) contributions are excluded by the standing
  perimeter).

**Attribution.** (I-1)(a,b) = O-3 K-RUN clauses "no-phantom" + "acceptance" (clause 4)
composed with O-2b's trace/tree correspondence (K-DICT-OB1) — the O-3 ⊕ O-2b joint
cluster of DELTA §D1.3. (I-1)(c) = O-2a Theorem 2(B)/(D) (rev 2 on file; conditional on
OL-2a-1..4). (I-2) = the faithfulness/injectivity face of the same dictionary (OL-2a-2/3)
plus the corner band (O-1/O-3 seam). Supporting evidence, discharging NOTHING: U6/
IFK-U6-FIRST exhaustive at length ≤ 2, all four (n, p) ∈ {2,3}² incl. both wild corners
(0 phantoms; PARI (e,f)-multiset tie 1600/1600).

**Deliberate NON-consumption.** No clause above says every leaf of 𝒯(g) is hit by some
slot (O-3's "no-missing" face). Surjectivity is PROVED below (Theorem B) from the
checksum. Also NOT consumed: K-OB-C (Okutsu proximity radii — the Krasner route to D-7a
is bypassed, §7 remark 6), D-16, any rate statement.

## 6. The triple

**Theorem B (transport bijectivity; the checksum-coverage mechanism).** Assume (I-1)'s
map preamble — the map β_g : leafslots(T) → leaves(𝒯(g)) exists for every g — together
with clauses (I-1)(c), (I-2), (I-3) [the preamble was implicit at rev 1; V18 finding 6:
(I-1)(c) and (I-2) already speak about β_g, so existence was recoverable but is now
listed]. For every monic separable lift g of x, β_g is a bijection
leafslots(T) → leaves(𝒯(g)).
*Proof.* Injective: (I-2). Surjective: Σ_ℓ e_ℓ f_ℓ = n [(I-3)]; each summand equals
e_{β_g(ℓ)}·f_{β_g(ℓ)} [(I-1)(c)]. By Theorem A(4), Σ over ALL leaves of 𝒯(g) of e·f is
also n, with every term ≥ 1. An injection whose image's total equals the whole total
forces the complement's total to be 0; with all terms ≥ 1 the complement is empty. ∎

**Theorem C (O-5 LEAF — verdict soundness at every leaf, uniform over lifts).** Assume
(I-1). For every lift g and every slot ℓ, G_ℓ(g) := G_{β_g(ℓ)} is a monic irreducible
factor of g with (e, f)(G_ℓ(g)) = (e_ℓ, f_ℓ) — the engine verdict, whose value is
g-independent. Per kind: hen slots through (HEN-LIFT) [H0]; saturated slots through
(OM-SAT) = (L10) via the dictionary [NODE(iv)]; corner slots through Lemma STEEP — the
two semantic realizations (exact key / steep length-1 side) differ across lifts but carry
the SAME (e, f).
*Proof.* Theorem A(2) well-definedness + LEAF-INV + (I-1)(b,c) + STEEP. ∎

**Theorem D (D-7a + D-7b).** Assume (I-1), (I-2), (I-3). For every lift g:
(a) [D-7a] distinct slots yield distinct, pairwise coprime irreducible factors;
(b) [D-7b] every monic irreducible factor of g equals G_ℓ(g) for exactly one slot ℓ;
(c) g = ∏_ℓ G_ℓ(g).
*Proof.* (a) β_g injective [(I-2)] and L ↦ G_L injective [Theorem A(2)] ⇒ the composite
is injective; distinct monic irreducibles are coprime (equivalently: a common divisor
would divide the squarefree g twice). (b) β_g onto [Theorem B] and L ↦ G_L onto
[Theorem A(2)] ⇒ composite onto; exactness of "one" by (a). (c) Theorem A(3) + B. ∎

**Theorem E (D-7c + O-5 ASSEMBLY).** Assume (I-1)–(I-3). For every monic separable lift
g of x: ℓ ↦ G_ℓ(g) is a bijection of leafslots(T) onto the monic irreducible factors of
g, each of multiplicity 1; the invariant multisets agree,
{(e_ℓ, f_ℓ) : ℓ ∈ leafslots(T)} = {(e(F), f(F)) : F | g monic irreducible}, and the
left-hand multiset is the SAME for every lift. Hence type(g) = typemult(T) = σ for every
lift; in particular any two monic separable lifts of x have equal splitting types.
*Proof.* Theorems B + C + D; multiplicities: g squarefree gives each factor once, and
each slot contributes once [(I-3)]. The left multiset is engine data, independent of g. ∎

## 7. Scope remarks and consumption ledger

1. **Per-claim consumption (the V6-f.16 answer, itemized).**
   | claim | consumes | does NOT consume |
   |---|---|---|
   | D-7a | (I-1)(a,b) + (I-2) + Thm A(2)inj [lit floor] | no-missing; K-OB-C; checksum |
   | O-5 LEAF | (I-1) + LEAF-INV/STEEP [lit floor] | no-missing; (I-2) |
   | D-7b | D-7a's set + (I-1)(c) + (I-3) + Thm A(4) | **O-3 no-missing** |
   | D-7c / ASSEMBLY | all of the above | rates; D-16 |
2. **Non-separable lifts.** All theorems quantify over separable lifts (the tree's
   standing precondition). Observation: disc is a fixed integer polynomial in the
   coefficients, so g ≡ g₀ (mod p^N) ⇒ disc g ≡ disc g₀ (mod p^N); hence if ONE lift
   has v_p(disc) < N, EVERY lift is separable with the same disc valuation. Whether
   every decided class pins v_p(disc) < N is O-1/O-4 territory; not asserted here.
3. **Unramified base (D-3 hygiene).** (L1)–(L13) are stated by GMN over an arbitrary
   complete discretely valued field; (HEN-LIFT) over any Henselian DVR; (DEFECTLESS)
   for complete discrete char 0. So §§3–4 (Theorem A) transfer verbatim to
   K_δ = W(F_{p^δ})[1/p]. The LIT-4 audit's "K = ℚ_p exactly" caveat constrains the
   AXIOM DECLARATION, not the mathematics; the interface (I-1)–(I-3) at K_δ awaits
   O-2/O-3's unramified restatements (D-3).
4. **Representative-family invariance.** 𝒯(g) depends on the chosen family; Theorem A
   holds per family; the leaf INVARIANTS are family-independent (they equal factor
   invariants of g). Node-level invariance = D-5, not consumed.
5. **Multiplicity vocabulary.** Under ns-freeness every slot has multiplicity 1; the
   "factors-with-multiplicity" clause is carried by g's squarefreeness (each factor
   once) + (I-3) (each slot once). The excluded (τ-ns) leaves are exactly the ones that
   carried μ ≥ 2 weights (M06 §2's refuted perimeter).
6. **The Krasner alternative (not consumed).** D-7a could instead run through root-disk
   separation: K-OB-C's tracking radii + divergence-node separation of key polynomials.
   The displayed route (coprime clusters in one factorization of a squarefree g) avoids
   K-OB-C entirely; the task hint's "key polynomial separates them" survives as intuition
   for WHY the divergence-node factors are coprime.

## 8. Honesty ledger

**Proved here, conditional exactly on the §2 floor + the FIVE §2 flags** [(GMN-COH),
(R-0), (R-1), (R-2)/(L3+)_r, (R-3); the flags are ASSUMPTIONS until their duties are
executed — rev 1's "unconditional over the §2 floor (with displayed reading flags)" is
RETRACTED as an overstatement, V18 finding 9]: Lemmas H0, REP-IRR [(R-1)], NODE [(R-2),
(GMN-COH)], LEAF-INV, STEEP [(L5b)/(L5b′) — pins, not flags]; Theorem A [additionally
(R-0) = (R-0a)+(R-0b),
(R-3)].
**Proved here, conditional on the displayed interface (I-1)–(I-3) AND the five flags
(through Theorem A):** Theorems B–E =
O-5 (LEAF + ASSEMBLY) + D-7a + D-7b + D-7c, for every monic separable lift, uniformly.
**Open, named, with owners (nothing else is consumed):**
* (I-1)(a,b) — O-3 no-phantom + acceptance ∘ O-2b trace correspondence [the O-3 ⊕ O-2b
  joint cluster; U6 supports at depth ≤ 2, discharges nothing].
* (I-1)(c) — O-2a Theorem 2 invariant matching [conditional on OL-2a-1..4; rev 2 on
  file, hostile re-verification pending].
* (I-2) — dictionary faithfulness/injectivity + the corner band [O-2a OL-2a-2/3 + the
  O-1/O-3 certificate seam].
* (GMN-COH) [M], (R-0) [mixed: (R-0a) [S] + (R-0b) [M]], (R-1) [M pending its
  statement match], (R-2)/(L3+)_r [M], (R-3) [M] — the §2 flag
  roster: GMN transcription duties, classified at rev 3 by PRESENT proof burden (V23
  finding 3); every flag except clause (R-0a) asserts genuine content and stands as an
  assumption
  [LITERATURE; (R-2)'s order-1 case falsifier-covered by O2a F5].
* (HEN-LIFT), (DEFECTLESS), (L1)–(L13), (L5b), (L5b′) — LITERATURE-CONDITIONAL/CANDIDATE
  per
  the standing pins ((L5b) NEW at rev 2, from the same verified citation ledger;
  (L5b′) NEW at rev 3, a CROSS-PACKAGE cite of O-2a §1 (L2) = GMN Prop 2.6 — the
  dictionary seam, single-point by design, noted for SYNTH4); no
  new axiom is declared by this brief.
**Not attempted:** discharging any part of O-2/O-3; Lean artifacts; D-16/rates;
non-separable lifts; cross-family canonicity (D-5).

## 9. Falsifier report (ran FIRST, 2026-07-31, this machine)

`verification/openmath/o5triple_check.gp` (PARI/GP 2.17.4; factorpadic + p-maximal
`nfinit([h,[p]])` + `idealprimedec` per the M06 tooling note). **1341 checks, 0 failures.**
* **T1** (order-1 STEEP): p ∈ {2,3,5}, M ∈ {2,3,4}; base x² + p^M·x (exact key x,
  j₀ = 1) vs lifts + c·p^{2M+1}, c·p^{2M+2} (steep finite corner side): type multiset
  CONSTANT = {(1,1),(1,1)}. 45 checks.
* **T2** (order-2 STEEP, Eisenstein key φ = x² − p): base φ² − p^M·φ (exact key φ) vs
  in-band constant-term lifts: type multiset CONSTANT = {(2,1),(2,1)}. 26 checks.
  **Negative control:** lifts at p^{2M−1} (below the corner band): 6/10 CHANGED type —
  the STEEP band hypothesis is load-bearing, not slack.
* **T3** (Theorem A(4) checksum + separable multiplicity 1): 4 primes × degrees 2..6 ×
  25 random separable samples: Σ e·f = n and all factorpadic multiplicities 1. 1000
  checks.
* **T4** (H0 per-factor + one-sided polygon surrogate for NODE): irreducible p-adic
  factors have single-irreducible reductions; fully x-tracked irreducible factors have
  one-sided Newton polygons. 270 checks.
Cited standing numerics: O2a F5 (871 j₀-corner samples, 0 findings); U6 (174/174 strata,
0 phantoms, 1600/1600 PARI (e,f) tie); M06 TB Krasner surrogate (40/40).

## VERDICT

**O-5 + D-7a/b/c: PROVED at the displayed interface, FLAG-CONDITIONAL** — the semantic
leaf/factor bijection (Theorem A) is proved over the pinned GMN/Hensel/defectlessness
floor CONDITIONAL on the five named transcription flags of the §2 roster, classified
at rev 3 by present proof burden ((GMN-COH), (R-1), (R-2)/(L3+)_r, (R-3) mathematical;
(R-0) mixed — (R-0a) statement-matching, (R-0b) mathematical; the V23-3
reclassification); NOT unconditional —
each flag is an assumption until its duty is executed against the GMN text (the V18
relabel). The classifier triple (Theorems B–E) additionally assumes (I-1)–(I-3), which
are exactly the tree's upstream O-2a / O-3 ⊕ O-2b faces, itemized per clause. Dependency
sharpening on record: D-7b consumes NO no-missing clause. Falsifiers: 1341/1341 with a
load-bearing negative control. Rev-3 ledger state: (L5b′) pins STEEP's normalization
through O-2a's (L2) transcription (cross-package, single-point seam — SYNTH4); the
(R-0) consumption itemization is corrected and audited. Pending: execution of the five
flag duties (the natural
next dedicated unit); fresh-context hostile verification of THIS rev.
