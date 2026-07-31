# O2a rev 3 — hostile verification, pass 2 (model-diverse; Claude Fable 5, fresh context)

**Target (only file read):** `lean/notes/openmath/O2a_phaseB_verifybrief_rev3.md`
**Charge:** quote-and-classify (critical error vs justification gap); fix nothing;
the five OLs are declared, an UNDECLARED dependence is a finding; first
verifier's report deliberately not consulted.

**VERDICT: UNSOUND — 1 critical, 3 justification gaps.**
Perimeter of the damage: the critical finding sits entirely at the Theorem 2(D)
engine seam (levels ≥ 2). Deliverable 1 (the carrier design), Theorem 1 (modulo
finding P2-2's missing one-line bridge), Lemma R, and Theorem 2(A)–(C) as
conditional proofs verified complete on their stated hypotheses, including all
k' = 0 corners and both lattice witnesses (recomputed independently below).

---

## Findings (most severe first)

### P2-1. CRITICAL — Theorem 2(D)'s induction step at levels ≥ 2 applies OL-2-min/OL-3 to the run's records without any declared law binding the run's (i+1)-th emitted record to "the engine's stage read at level i+1 on f over c" with c = the emitted prefix's chain

Quotes. Theorem 2(D), §5:

> "Fix a complete run of the stage flow on f and let 𝐇 be its emitted dressed
> history. … level i + 1 ≥ 2, given the prefix Cons_f-consistent — OL-2-min
> gives (c1) in full ((c′) the side data, (d′) the positional clause), OL-3
> gives (c2)"

OL-2-min's premise, §4:

> "suppose the engine's stage read at level i + 1 on f over c emits the record
> (e, h, ℓ, s, u, …)"

(OL-3: "Same setting".) To instantiate OL-2-min at the run's node ν_{i+1}, the
proof needs two things: (i) c := Θ(𝐇_{≤i}) is a Cons_f-consistent chain — this
is the induction hypothesis, fine; and (ii) **ν_{i+1}'s record was emitted by
"the engine's stage read at level i + 1 on f over c" for that specific c** —
i.e. that a complete run decomposes into successive stage reads whose chain
datum at level i + 1 is exactly the formal chain of the previously emitted
records/dressings. Premise (ii) is asserted NOWHERE:

* OL-4 gives only well-formedness of the emitted history + (c0) ("the emitted
  dressed history 𝐇 = (ρ₀; ν₁, …, ν_k) is a WELL-FORMED element of 𝔈" …
  "(d) the level-0 record satisfies a₀ = ord_{ψ̂₀}(f̄)") — no run-to-stage
  decomposition, no chain binding.
* OL-5 was phrased RUN-wise ("For every monic f … and every complete run …
  whose emitted history has a CONTINUING first node ν₁ … the first read is
  performed by the (D3)-displayed formulas w.r.t. φ₁ := Lift₀(ψ̂₀) (the run's
  level-0 dressing)") — precisely internalizing this glue at level 1. OL-2-min
  and OL-3 are NOT so phrased; they are hypotheticals about stage reads
  parameterized by (f, c).
* The displayed interface does not supply it either: in "[F.0] … the monic KEY
  Φ̂_{i+1} = Lift_i(c)" the variable **c is unbound** — nothing in §4's display
  ties the c of a stage occurring inside a complete run to the run's emitted
  prefix. Yet §4 opens with: "Their statements are exact relative to the
  following displayed interface, which is ALL of the engine text they consume."

Classification: **critical error**, by the note's own standard ("an UNDECLARED
dependence is [a finding]") and by exact parity with V14-1, which the rev-3
changelog itself records as critical for the same shape one level down ("no OL
asserts the engine's first read DOES compute the displayed formulas …
Undeclared emission dependence at i = 1; (D) cannot establish Cons_f"). Here:
no OL or interface clause asserts that the run's level-(i+1) record IS the
output of a stage read over the emitted prefix's chain; without it the
induction step at every level ≥ 2 is not licensed as written, so (D) cannot
establish Cons_f for emitted histories with k' ≥ 2. Downstream checked by
assuming the binding: with it, (D) is complete (see ledger item 7). The defect
is a statement/seam defect, not a mathematical one — the repair shape is the
same move as V14-1's (phrase OL-2-min and OL-3 run-wise like OL-5, or display
a run-decomposition + chain-binding law in the interface or in OL-4) — but per
the charge nothing is fixed here.

### P2-2. GAP — Theorem 1's unconditional appeals to (L9) at r = 1 presuppose the (L5) Convention, which the note itself instantiates only under (D4) + OL-1; the level-0-only bridge is missing

Quotes. Theorem 1, cases (i)/(ii): "(Ch°): … ind₁(f) ≤ ind(f) is (L9) at
r = 1"; case (iii) charge: "and ind₁(f) ≤ ind(f) (L9, r = 1)". Against (C2):

> "Under (D4) + OL-1 the Convention is instantiated and t_r(P), ind_t(P),
> ind_r(P) are single-valued over F_rep."

and OL-1's consumer note: "Consumed by: ι's well-definedness at orders ≥ 2 …
and by nothing at order ≤ 1." GMN's Thm 4.18(1) is stated over a universally
fixed family in (L5)'s sense; absent OL-1, F_rep is not known to be such a
family at levels ≥ 1, so citing (L9) — even at r = 1 — is not licensed
verbatim. The missing (easy, standard) bridge: ind₁(f) and t₀(f) depend only
on the level-0 layer (which (D4) proves admissible); a full family extending
Lift₀ exists by Thm 2.11's existence recursively (+ choice); apply Thm 4.18(1)
to that family and transport, since ind₁ agrees. None of this is displayed,
and Theorem 1 is advertised as unconditional. Classification: **justification
gap** (assume the bridge; everything downstream — (Ch°), the case-(iii)
charge — then checks). Side note: checklist item 7's "only at k' ≥ 1" is in
tension with (Ch°)'s k' = 0 use of (L9); the parenthetical scopes it to
Theorem 2(C) (whose k' = 0 branch correctly avoids (L9)), but the blanket
phrase as written is contradicted by Theorem 1's own text.

### P2-3. GAP — OL-5 names more than Theorem 2(D) consumes: clause (a) is engine-internal mechanism, while (D) needs only the GMN-intrinsic (b)+(c); this reintroduces at level 1 the exact minimality defect V14-2 charged on OL-2(a)–(b)

Quote. OL-5(a):

> "(a) [development + hull] the read computes the φ₁-adic development
> f = Σ_j b_j φ₁^j and its lower hull in the (L2) order-1 integer frame
> {(j, v(b_j)) : b_j ≠ 0}, with the (L3+) j₀ convention on the −∞ side"

Clauses (b) and (c) are already stated in GMN-intrinsic terms (a finite slope
of N₁^−(f) with the emitted side/position data; ψ̂₁ a factor of R_{λ₁}(f) with
the emitted multiplicity/degree) and are exactly (c1)+(c2) at i = 1 — all (D)
consumes. Clause (a) asserts the engine's internal computation (a materially
different and stronger proof burden: base-code-path inspection vs I/O
conformance), the same asymmetry for which OL-2 was split into OL-2-min
("2(D) consumes only the emitted side record, not the valuation tie on every
admissible coefficient"). By the note's own advertised standard ("each
theorem's hypothesis list names NO MORE than it consumes (minimality —
V14-2's charge)"), (D)'s hypothesis should be an OL-5-min = (b)+(c) [with
(b)'s "that frame" re-anchored intrinsically to (c1)'s positional clause,
which needs no engine text], with (a) re-advertised to the O-3 seam as the
intended proof route. Classification: **justification gap** (minimality; no
mathematical content at risk).

### P2-4. GAP — OL-1's statement is well-posed only as a joint induction over orders, which is not stated

Quote. OL-1: "For every well-formed chain datum c of order i ≥ 1, with t = its
type over F_rep: …". For the length-i datum c to HAVE "a type over F_rep" per
(L1), each lower-level Lift output must already be a Def-2.12 representative
of its truncation — i.e., OL-1(b) at orders < i. As literally quantified
(independently per i), the phrase "its type over F_rep" is undefined at order
i without the lower instances; the intended reading is a cumulative/strong-
induction statement. The note applies the same inductive discipline explicitly
elsewhere ("(c1) … inductively, reading GMN objects through ι — level 1
unconditional, levels ≥ 2 given OL-1") but not inside OL-1 itself.
Classification: **justification gap** (harmless; read OL-1 as a single joint
statement and every use checks).

---

## Clean-pass ledger (each charged area; all verified against the in-package transcriptions (L1)–(L9), per the charge)

1. **Carrier laws W1–W5 (C1).** Mutually consistent; W1 is in fact DERIVABLE
   from W2 + the sel-domain constraint μ_i g_i ≤ ℓ_i (ℓ = 1 forces g = μ = 1,
   so e ≥ 2 gives eg ≥ 2 → inc = 1, and e = 1 gives eg = 1 → inc = 0) —
   redundancy, not error. Rows T1–T4 exhaust continuing nodes (checked by case
   split on ℓ, e). μg ≤ ℓ is the correct residual-degree bound (deg R = d = ℓ,
   (L3)). The prefix-closure claim checks: for a prefix ending at continuing
   ν_j, every W3/W5 index i < j satisfies i < k. T4 (e = 1, ℓ = 1 ⇒
   g = μ = 1) can only be last, by W3 — checklist 4's corner confirmed.
   Equality on 𝔈 is literal on declared countable constituents; the towers
   are constructed quotients, no isomorphism classes. No choice smuggled.

2. **Intrinsic positional recovery / unique-slope-side well-definedness.**
   (c1)'s positional clause is intrinsic at every order: N_i^−(f) is a lower
   polygon, its sides have pairwise distinct slopes (strict convexity), so
   "the UNIQUE side of slope λ_i" is well-defined whenever (c1) grants
   existence; its initial point is a vertex of the point set
   {(j, v_i(b_j φ_i^j))} with nonnegative-integer coordinates ((L2): v_i ≥ 0
   integral on O[x]∖{0}). At orders ≥ 2 well-definedness of the objects
   (not of the frame) needs exactly OL-1, declared in-line in Lemma R and in
   (A). No engine frame occurs in (C4) — V10-C7's repair holds. Lemma R's
   recovery map reproduces every field of every node of 𝔈°_f (checked field
   by field: e, h from λ; ℓ = d(S); (s, u) from the positional clause; g, ψ̂
   from 𝔠; μ from (c2), ∼-invariant; inc from W2). The terminal non-recovery
   example ν = (1,1,1,0,0,⊥,0) vs ν′ = (1,2,1,0,0,⊥,0) verifies: W1/W2/W4
   constrain only sel ≠ ⊥ nodes, W3/W5 see only position, Cons_f constrains
   no terminal field, both coprimality conditions hold, both images = Θ(𝐇°).

3. **Injectivity restriction's threading.** Consistent everywhere probed:
   Lemma R restricted to 𝔈°_f; Theorem 1 (D0) asserts injectivity only on
   "{Cons_f, length ≤ 1, all nodes continuing}"; case (ii) displays the
   non-claim; Theorem 2(A) asserts injectivity only on 𝔈°_f; the consumer
   audit holds — Θ(𝐇) = Θ(𝐇°) by construction, dCert counts continuing nodes
   by definition, (B)/(C) quantify over i ≤ k', saturation reads μ_{k'} at the
   last CONTINUING node. No clause of Theorems 1/2 or the scope remarks
   claims recovery of terminal fields. (t-i)/(t-ii) stay non-consumed.

4. **The five OLs — exactness and mutual consistency.** Every object in
   OL-1/OL-2/OL-2-min/OL-3/OL-4/OL-5 is GMN-defined, carrier-defined,
   interface-displayed, or (D3)-displayed — attackable as stated — EXCEPT the
   run↔stage-read binding of P2-1 (and the unbound c of [F.0]), and P2-4's
   induction phrasing. OL-1(c)'s two forms are equivalent given (L4)'s
   Prop 2.7 identity (v_{i+1}(φ_i) = h_i + e_i V_i, substituted into eq. (16)
   — checked). OL-2(a)'s attackable consequence u_{i+1}(π) = E_i follows from
   (L2)'s v_{i+1}(a) = e_i·v_i(a) iterated: v_{i+1}(π) = e_i⋯e₁ ✓. The
   (a)+(b) ⇒ OL-2-min display genuinely collapses (checklist 12): under (b)
   the window polygon IS N_{i+1}(f), the emitted record is the read side's
   window-frame data (interface), the read side has finite negative slope so
   lies in N_{i+1}^−(f), and at-most-one-side-per-slope pins S — (c′)/(d′)
   verbatim. OL-3 is stated at the maximal meaningful sharpness (both
   residuals only ∼-defined); constant-term nonvanishing matches on both
   sides; factor-multiset transport under a global F^× scalar is sound; on
   the read side e | (j − j₀) for on-side minimizers (lattice points on a
   denominator-e side are spaced e apart), so R^st's exponents are integers.
   OL-4's clauses (a)–(d) are exactly W-laws + domains + tower dressing +
   (c0), no more. Mutual consistency: no overlaps contradict; the μ = 1 ⇒
   halt discipline (OL-4's route) matches W3's "terminal-after-saturation is
   ill-formed" (last-node-terminal forces μ_{k'} ≥ 2 — checked as the i < k
   quantifier's intended effect). Consumption audit: with P2-1's binding
   assumed and modulo P2-2/P2-3, no theorem consumes anything outside the
   OLs + pinned citations; Lemma R consumes no part of OL-2 (its data are
   (c1)-intrinsic — confirmed); (D) consumes no OL-2 clause beyond OL-2-min.

5. **Order ≤ 1 proofs vs the in-package GMN transcriptions.** (D4): a
   coefficientwise lift of a monic polynomial is monic and reduces correctly;
   (L5)'s level-0 layer asks exactly this ✓. (D3): reduction of the φ₁-adic
   development is the ψ₀-adic development of f̄ (deg b_j < f₀, monic
   division) ✓; ψ₀^a ∥ f̄ ⇔ v(b_j) ≥ 1 for j < a and v(b_a) = 0 ✓; principal
   part on [j₀, a] ✓; j₀ ≤ 1 for disc f ≠ 0 (φ₁² | f ⇒ multiple roots) ✓;
   j₀ = a forces a = 1 and kills all finite sides — correctly routed to
   cases (i)/(ii) ✓; the −∞ side carries exactly φ₁, Hensel leaf (1, f₀) ✓;
   charge unaffected since E_∞·H_fin ≥ 0 ✓; ∼-ambiguity does not move factor
   multisets ✓. (D1): f₁ = g₁, tower degree, m₂ = m₁e₁f₁ per (L1) ✓;
   v₂(φ₁) = h₁ + e₁·0 = h₁ per Prop 2.7 ✓; deg G = m₁·e₁·μ₁·f₁ = m₂μ₁
   matches (L6)'s "deg G_i = m₁·e·a_i·deg ψ_i" verbatim, and Cor 1.20 at
   a_i = 1 gives (e, f) = (e₁, f₀f₁) = (accE, accF) ✓. (D2): Def 3.10
   membership is verbatim (non-completeness from W3's a₀ ≥ 2) ✓. (D0/D0°):
   Lemma R instantiations ✓.

6. **Charge/index arguments.** Both lattice witnesses recomputed against the
   transcribed Remark-4.14 region (below/on the side, ordinate > last-point
   horizontal, abscissa > initial vertical; on-side points count — checked on
   E = H = d = 2 where the count is 1 = ½(EH−E−H+d)): T1's (s+e, u_s−h) is
   on-side, abscissa s+e > s, ordinate margin h(ℓ−1) > 0 at ℓ ≥ 2 ✓; T2's
   (s+1, u_s−h+1) membership ⇔ (e−1)(h−1) ≥ 1, true at e, h ≥ 2 (coprime,
   so never both 2... irrelevant — each ≥ 2 suffices) ✓. Closed form
   2·ind(S) = ℓ(ehℓ+1−e−h) recomputed from E = eℓ, H = hℓ, d = ℓ ✓; T3/T4
   give ind(S) = 0, correctly uncharged (undercharging only helps the
   inequality). The chain ind(S_i) ≥ 1 → ind(N_i^−) ≥ ind(S_i) (all summands
   ≥ 0, (L8)) → ind_{t^{(i−1)}} = f₀⋯f_{i−1}·ind(N_i^−) ≥ 1 (Def 4.15 at
   r = i, positive twist) → ind_i ≥ ind_{t^{(i−1)}} (t^{(i−1)} ∈ t_{i−1}(f)
   by (A), nonnegative terms) → Σ over the identity-placed distinct certified
   orders → ≤ Σ_{r=1}^{k'} ind_r ≤ ind(f) by (†) at R = {1..k'} — each link
   checked; (L9) consumed only in finite-sum form (with P2-2's caveat at
   order 1). Cross-check: F3's ind_2(f) = 4k+2 recomputed here from scratch
   (development points (0,2),(1,2),(2,2),(4,0); off-side slot j = 2
   correctly zeroed in the residual, R ∼ (z+w̄)²; order-2 points (0, 4k+3),
   (2, 4); ind = 2·2 + 2·(2k−1)) — exact agreement, including the twist
   factor and dCert = 2 (ν₁ = T1 with e₁g₁ = 2, ν₂ = T2 with h₂ = 4k−1 ≥ 3).

7. **Theorem 2 and the k' = 0 corners.** (A)'s induction: base from (c0) +
   W3; step is Def-3.10-verbatim from (c1)+(c2); interior non-completeness
   from W3 covers every sprouting site (i − 1 < k' always; when the last node
   is terminal W3 even gives μ_{k'} ≥ 2, harmlessly stronger) ✓. (B): m- and
   V-recursions from (L1)/OL-1(a)(c)+Prop 2.7 ✓; m_{k'+1} = accE·accF by
   unwinding ✓; saturation correctly guarded k' ≥ 1, Def 2.3's indexing
   (deg f_t = m_r·ω_r for t of order r−1) consistently instantiated at
   r = k'+1, Cor 3.8 at μ = 1 ✓; deg Φ̂_{i+1} = m_{i+1} is definitional via
   the pinned Lift + OL-1(a), no engine hypothesis needed ✓. (C)'s k' = 0
   branch cites only Def-4.11 nonnegativity, no (L9), no μ_{k'}, no "last
   read" ✓; Theorem 1's three cases exhaust length ≤ 1 and every clause is
   well-formed at k' = 0 (Ch°, D0°, D2° checked one by one) ✓. (D): at
   k' = 0 only OL-4(d) is needed ✓; at k' = 1 OL-5 (run-wise) + the PROVED
   (D3) close the base ✓ (modulo P2-3's minimality); at levels ≥ 2 the
   argument is complete IF P2-1's binding is granted — with it assumed,
   OL-2-min delivers (c1) verbatim and OL-3 delivers (c2), OL-1 keeps the
   next level defined, and (A)/(B)/(C) fire ✓. The terminal record's
   placement-only treatment is consistent with Lemma R ✓.

8. **Placement design (checklist 5).** The transcribed (L1) admits e_i = 1,
   h_i ≥ 1 arbitrary (coprime to 1) and f_i = 1; nothing in §1 forbids
   consecutive orders with e_i = f_i = 1; optimality is nowhere assumed ✓.

## Summary

The rev-2/rev-3 re-architecture survives this independent pass everywhere
except the one seam it has been converging on: the engine-side glue of
Theorem 2(D). Rev 3 closed V14-1's level-1 instance of that glue by phrasing
OL-5 run-wise, but left OL-2-min/OL-3 stage-wise, so the SAME class of
undeclared emission dependence persists at every level ≥ 2 (P2-1, critical).
The three gaps are statement-hygiene items (a missing one-line family bridge
for (L9) at order 1; OL-5's minimality; OL-1's induction phrasing), none of
which threatens the mathematics. Theorem 1, Lemma R, the carrier, and
Theorem 2(A)–(C) verified complete as conditional statements, with all
spot-check arithmetic (lattice witnesses, F3's 4k+2, the residual off-side
slot) independently recomputed and exact.
