# D4R.0-K derivation — offset-P lift totality (L1) + joint next-outcome partition (L5, retargeted) (2026-07-26)

Derivation unit for §D4-R's open kernel D4R.0-K (MOVES_2026-07-24.md §D4-R,
lines 4464 ff.). Staged build; each section appended after its derivation.
Sources consumed: accepted §B2-DEF (D.0–D.11, esp. (S6b′), D.4, D.5, D.8,
D.9, D.10), accepted §C REV 2 (C.0, C.0.5, C.1, C.1.5/LST), §D4-R's own
L2–L4/L6 wiring, FABLE_VERIFY_D4R_2026-07-26.md (finding F1), and the
coordinator's retarget directive (recorded in S0).

## S0. Charge, retarget record, and status summary

(to be appended)

## S1. Part (a): the offset-P canonical realizer is TOTAL and UNIQUE

### S1.1 Stage indexing and the demand at an eligible node
### S1.2 The construction with every choice displayed as forced
### S1.3 Theorem A (totality + uniqueness) and its proof
### S1.4 The boundary enumeration, case by case
### S1.5 What part (a) discharges downstream (L4)

## S2. Part (b), retargeted: the JOINT next-outcome partition

### S2.1 Why the per-branch form is false (F1 restated; no repair attempted)
### S2.2 The joint read datum 𝒟(f), defined
### S2.3 Verification on the refutation instance and on the D4-n3 cell
### S2.4 Theorem B (JOINT-L5: totality + exclusivity), with the full case tree
### S2.5 Per-leaf realized-or-empty witnesses
### S2.6 The (z)/(ep)/(ns) obligation, located clause by clause
### S2.7 What the joint form does NOT repair (consumer rewiring, not done here)

## S3. OPEN ISSUES (honest)

## S4. VERDICT

---
*(S0 appended.)*

### S0.1 The original charge and the mid-derivation retarget

ORIGINAL CHARGE (kernel D4R.0-K): (a) L1's totality — §B2-DEF's offset-P
lift policy is total and unique at EVERY eligible node; (b) L5's
next-outcome exhaustiveness/exclusivity — at every realized prefix state
(empty included) the outcome case list is a PARTITION of the state
cylinder.

RETARGET (coordinator, 2026-07-26, mid-derivation; independently
confirmed by this deriver before the message arrived): the Fable dual
pass (FABLE_VERIFY_D4R_2026-07-26.md, F1, CRITICAL) refutes part (b) AS
STATED: the per-branch next-node datum (which residual factor ψ; at
multi-side polygons which side) is NOT a function of f — worked
counterexample n = 4, p = 5, root digits (d₃,d₂,d₁,d₀) = (4,3,3,4),
R₀ = (z−1)²(z−2)²: two same-shape factors, two distinct realized
prefixes with literally equal strata (restated with the arithmetic
displayed in S2.1). Part (b) is therefore RETARGETED: derive
exhaustiveness/exclusivity for the JOINT (branch-multiset) formulation —
at each level the node datum is the full multiset of branch data over
all sides and all eligible factors (equal-shape branches unordered), so
the outcome IS a unique function of f under the canonical lift policy.
Part (a) is unaffected and kept as originally charged. S2.3 verifies
first, per the directive, that the joint form restores uniqueness on
the refutation instance.

### S0.2 Status summary (details in S4)

- Part (a): DERIVED (Theorem A, S1.3–S1.4): the offset-P policy is a
  total single-valued function of node data at every grammatical
  (I-aug)-legitimate node of every realizable prefix, all boundary
  cases enumerated and closed; one convention consumed (the base digit
  section, pinned — S1.4 (B4), open-issue O3 records the bookkeeping).
- Part (b), original per-branch form: FALSE — F1's counterexample is
  checked and adopted here (S2.1); no repair of the per-branch claim
  is attempted.
- Part (b), retargeted joint form: DERIVED (Theorem B, S2.4–S2.6),
  conditional on accepted §B2-DEF + §C only (L4's common frame becomes
  unconditional once Theorem A closes L1 — S1.5).
- What Theorem B does NOT restore: §D4-R's linear-run consumers (L2's
  unique run, L6's fiber form, D4R.1's disjoint union) still need the
  note-side rewiring recorded in S2.7 and O2. That is repair work on
  §D4-R, outside this unit's charge.

---
*(S1.1–S1.2 appended.)*

### S1.1 Stage indexing and the demand at an eligible node

STAGES (D.0, re-indexed once for this unit). Stage r ≥ 1 carries: key
Φ_r (monic, deg D_r), valuation w_r, coefficient space C_r := {deg <
D_r}, residue field F_r, read index (e_r, h_r) — the side of slope
h_r/e_r (lowest terms, gcd(e_r,h_r) = 1, Bézout e_r s_r + h_r t_r = 1)
read at stage r−1 that created stage r. Base: r = 1, Φ₁ = x on the
normalized cluster box, w₀(Φ₁) = 0 (D.4 ROOT normalization), C₁ = the
base coefficients (ℤ_p resp. O_Q), F₁ = F_Q. An INCREMENT read of side
(e, h) with residual factor ψ (deg g) at stage r builds Φ_{r+1} := Φ̂
(D.5's standard lift), F_{r+1} = F_r[z]/(ψ), D_{r+1} = e·g·D_r. A
RECENTERING (e_read = 1, deg ψ = 1) REPLACES the key (Φ′ := Φ̂ − t,
D.10) at the same tower depth; TRANS-RS rebuilds the same stage package
(the g = 1 instance of D.5, F unchanged). By the accepted §B2-DEF
induction ("the stage axioms (S1′)–(S5′), (S6a′), (S6b′) all hold: the
induction closes"), EVERY stage reached by either species carries the
full package — in particular (S6b′). PARENT SCALE: C_r's weights are
measured in w_{r−1}; the CLEAN THRESHOLD of C_r is w_{r−1}(Φ_r)
(= e_{r−1}h_{r−1}g_{r−1} at increments, D.5's equal weights; = the
consumed side value at recenterings, D.10).

THE DEMAND. An ELIGIBLE NODE of a realizable prefix is a read ν whose
species requires a lift; the policy's demand there is a pair
(W, T) = (weight, digit class):
- (i) RECENTERING lift (D.10; the policy's namesake): at an e_read = 1
  read of side value λ″ on the current key Φ_r, with center c̃ ∈ F_rˣ
  (a root of the side's ANCHORED residual): demand (W, T) = (λ″, c̃) in
  C_r, parent scale. Root instance: the M3 shift x ↦ x + ĉp^M on C₁.
- (ii) STANDARD-LIFT realizers (D.5, consumed inside every increment's
  key construction; included so that "canonical lift" is a function of
  node data for KEYS too, which L4 consumes): for each nonzero
  coefficient ψ_k of ψ, demand (W, T) = (h(g−k), ψ_k) in C_r.
GRAMMAR (what "eligible" presupposes): the read's side is a side of the
window polygon of a landing (D.8 box at increments; D.10 RS-landing at
recenterings; D.4 ROOT at the root) — so (I-aug) holds AT the read:
λ″ > w_{r-1}(Φ_r) for (i) (D.9(d) verbatim: "at any e_read = 1 read,
the side value λ″ satisfies λ″ > w(current key)"), and h/e >
w_{r−1}(Φ_r) for the side read in (ii). A data tuple violating this is
not a read of any landing (D.4's chord display) and realizes the empty
stratum; the totality quantifier below runs over grammatical nodes.

### S1.2 The construction with every choice displayed as forced

(S6b′)-CANONICAL REALIZER at stage r ≥ 2, demand (W, T), W ∈ ℤ,
W > w_{r−1}(Φ_r), T ∈ F_rˣ. Write (e, h, g, s, t) := (e_{r−1}, h_{r−1},
g_{r−1}, s_{r−1}, t_{r−1}) and ψ := ψ_{r−1} (so F_r = F_{r−1}[z̄],
z̄ := z mod ψ, z̄ ≠ 0 since ψ ≠ z). Four choices, each FORCED:

  (F-1) j₀ := the unique element of [0, e) with j₀·h ≡ W (mod e).
        [Forced: h is invertible mod e (gcd = 1). Slots j₀ + ek,
        0 ≤ k < g, all lie in [0, eg): j₀ + e(g−1) ≤ (e−1) + eg − e =
        eg − 1 < eg, so every summand below has degree < D_r: it lies
        in C_r.]
  (F-2) m := (j₀ − tW)/e ∈ ℤ.
        [Forced and integral: j₀ ≡ h⁻¹W and t ≡ h⁻¹ (mod e), so
        j₀ − tW ≡ h⁻¹W − h⁻¹W = 0 (mod e). Pass-12 record: "R(t) =
        z^m·P(z) is forced, m = (j₀ − tW)/e" — confirmed sound.]
  (F-3) P := the unique polynomial over F_{r−1} with deg P < g and
        z̄^m·P(z̄) = T in F_r.
        [Forced: z̄ ∈ F_rˣ, so z̄^{−m}T ∈ F_rˣ has a unique
        representative of degree < g; T ≠ 0 gives P ≠ 0 — at least one
        nonzero coefficient P_k exists.]
  (F-4) t := Σ_{k: P_k ≠ 0} t_k·Φ_{r−1}^{j₀+ek}, where t_k := the
        stage-(r−1) canonical realizer of demand (W_k, P_k),
        W_k := (W − (j₀+ek)h)/e.
        [Forced by recursion on r: W_k ∈ ℤ by (F-1)'s congruence; the
        threshold W_k > w_{r−2}(Φ_{r−1}) is checked in S1.3 step 2;
        slots with P_k = 0 are ABSENT (no realizer of scalar 0 exists
        or is needed — D.5's convention).]

BASE r = 1: the canonical realizer of demand (ℓ, c), ℓ ∈ ℤ≥0, c ∈ F_Qˣ,
is ĉ·p^ℓ ∈ C₁ with ĉ := the PINNED unit section of c (Teichmüller —
the decomposition note's fixed choice function, MATH_FULLTYPE §"Canonical
lifts": "Teichmüller digits / minimal-support lifts"). No threshold: the
base weight set is all of ℤ≥0 (D.9's 𝒲₁).

That w(t) = W exactly and dig(t) = T — i.e. that the construction MEETS
the demand — is the accepted (S6b′) computation: each summand has equal
weight W (weight of t_k is e·W_k parent-scaled, plus (j₀+ek)h), the
summand residuals occupy the DISTINCT z-exponents m + k (pass-12's
confirmed R(t) = z^m·P(z) display), so no cancellation occurs, w(t) = W,
and the class is z̄^m·P(z̄) = T. This unit re-derives none of that; its
burden is the QUANTIFIER (S1.3) and the boundaries (S1.4).

---
*(S1.3 appended.)*

### S1.3 Theorem A (totality + uniqueness)

**Theorem A.** Along every realizable prefix (grammatical node data,
canonical lifts), at every stage r and every demand (W, T) with W ∈ ℤ,
W > (the clean threshold of C_r), T ∈ F_rˣ: the (S6b′)-canonical
realizer of S1.2 is DEFINED, UNIQUE, and meets the demand. In
particular the offset-P lift policy is defined at every eligible node
(both demand species of S1.1), and the lift is a single-valued function
of the node data alone. No node exists where the policy is partial.

*Proof — strong induction on the stage index r.*

STEP 0 (eligibility ⟹ hypothesis). At an eligible node the demand's
weight clears the clean threshold: species (i) by D.9(d)/(I-aug)
verbatim (λ″ > w_{r−1}(Φ_r) — "(I-aug) is literally the hypothesis",
(S6b′) CONSUMERS (ii)); species (ii) by D.5's range check (h(g−k) ≥ h >
e·w_{r−1}(Φ_r) ≥ w_{r−1}(Φ_r), (I-aug) at the current read). And the
demand's class is a UNIT: species (i) c̃ ≠ 0 (S1.4 (B3): the anchor
convention makes every center a unit); species (ii) ψ_k ≠ 0 by
construction (zero slots absent). So every eligible demand is an
instance of the Theorem's (W, T) quantifier.

STEP 1 (base r = 1). Defined for EVERY ℓ ≥ 0 and c ∈ F_Qˣ (S1.2 BASE);
unique because the section is pinned; meets the demand because
v_p(ĉp^ℓ) = ℓ and dig = c. For the eligible instances: the root demand
weight is a root side value λ″ ≥ 1 > 0 (D.4 ROOT: positive slopes;
e_read = 1 makes λ″ an integer). Nonnegativity holds a fortiori.

STEP 2 (induction step, r ≥ 2). Assume Theorem A at all stages < r.
(F-1)–(F-3) are defined and forced unconditionally (S1.2's brackets:
only gcd(e,h) = 1, ψ ≠ z, T ≠ 0 are consumed — all stage-package
facts). For (F-4), each needed t_k has demand (W_k, P_k) with P_k ∈
F_{r−1}ˣ (only nonzero coefficients get realizers) and W_k ∈ ℤ; the
THRESHOLD CHAIN, displayed:

  W_k = (W − (j₀+ek)h)/e
      ≥ (W − (eg−1)h)/e            [j₀+ek ≤ eg−1, (F-1)]
      > (w_{r−1}(Φ_r) − (eg−1)h)/e [W > w_{r−1}(Φ_r), strict]
      = (ehg − egh + h)/e          [w_{r−1}(Φ_r) = ehg, D.5 — the
                                    increment case; recentered stages
                                    in S1.4 (B5)]
      = h/e
      > w_{r−2}(Φ_{r−1})           [(I-aug) at the stage-(r−1) read].

So (W_k, P_k) satisfies the stage-(r−1) hypothesis; by induction t_k is
defined, unique, and meets its demand. The sum (F-4) is then defined;
it meets (W, T) by the accepted (S6b′) computation (S1.2, last
paragraph). UNIQUENESS: every choice in the chain is forced — (F-1) by
the congruence, (F-2) by integrality, (F-3) by field-representative
uniqueness, each t_k by the induction's uniqueness, the base by the
pinned section. The construction consumes the node data (stage index,
(e,h,g), ψ, W, T) and NOTHING of f. ∎

WELL-FOUNDEDNESS: the recursion strictly decreases the stage index and
bottoms at r = 1 after finitely many steps (a prefix has finitely many
stages); no other recursion occurs.

SCALE REMARK (so the chain cannot be mis-read): all weights above are
in C_r's parent scale w_{r−1}; W_k is stated in C_{r−1}'s parent scale
w_{r−2} — the division by e in (F-4)'s W_k is exactly the D.0 scale
conversion w_{r−1}(B) = e·w_{r−2}(B) for B ∈ C_{r−1}, so "W_k clears
stage (r−1)'s clean threshold" is the literal induction hypothesis, no
unit mixing.

---
*(S1.4–S1.5 appended.)*

### S1.4 The boundary enumeration, case by case

(B1) MINIMAL ELIGIBLE WEIGHT, W = w_{r−1}(Φ_r) + 1. The chain's only
strict input is W > ehg; at the minimum, W − (eg−1)h = h + 1, so
W_k ≥ (h+1)/e > h/e > w_{r−2}(Φ_{r−1}) — the integer step SURVIVES the
strictness with room ≥ 1/e; nothing degenerates. (For a recentering the
true minimal eligible λ″ may sit higher — λ″ must also lie in the
coefficient value set, D.9(d) — but Theorem A covers every integer
above the threshold, a fortiori every eligible λ″.) CLOSED.

(B2) g = 1 (single slot). (F-3)'s P is a scalar P₀ = z̄^{−m}T ∈
F_{r−1}ˣ = F_rˣ (ψ linear: the extension is trivial); (F-4) is the
single summand t₀·Φ_{r−1}^{j₀}; the chain reads W_k = (W − j₀h)/e ≥
(W − (e−1)h)/e > (eh − eh + h)/e = h/e — same display at g = 1.
No step consumed g ≥ 2. CLOSED.

(B3) a > 0 ANCHORS. The anchor enters the demand only through WHICH
class is demanded, never through the demand's form: the read's side
residual splits as R = z^a·R_anch with R_anch(0) ≠ 0 (support-anchored
convention, D.0 (P4)/D.8 ANCHORING), and recentering centers are roots
of R_anch — hence NONZERO: c̃ ∈ F_rˣ is guaranteed BY the anchor
convention, at a = 0 and a > 0 alike (this is Step 0's unit claim).
The anchor monomial (z + c̃)^a of the RS transport is bookkeeping of
the LANDING (D.10's unit note), not of the lift demand. Since Theorem A
hits EVERY class in F_rˣ, a > 0 changes nothing. CLOSED.

(B4) BASE STAGE / ROOT SHIFT (M3). The root recentering demand is
(λ″, c̃) on C₁ with λ″ ≥ 1 an integer (D.4 ROOT + e_read = 1); realizer
ĉ·p^{λ″}, pinned Teichmüller section. The only convention consumed
anywhere in Theorem A is this base section; §B2-DEF's own base clause
("F_Q-unit lifts with no threshold") is section-agnostic, and the
decomposition note pins Teichmüller — adopted here; recorded as O3
(the definitive write-up should pin it in ONE place). CLOSED given the
pin.

(B5) RECENTERED STAGES / CONSECUTIVE RECENTERINGS. After a recentering,
TRANS-RS rebuilds the stage package on the SAME coefficient space with
the primed key Φ′ (the g = 1 instance of D.5: ψ′ = z − c̃, c̃ ≠ 0, so
ψ′ ≠ z; F unchanged); the clean threshold UPDATES to the primed key's
weight = the consumed side value λ″ (D.10: v(Φ′) = v(Φ̂) at the tie —
the recentered key carries the frame weight; the next side value only
grows, D.9(d) "subsequent side values only grow (convexity within the
frame + (I-aug))"). The next recentering's demand λ‴ > v(Φ′) = the new
clean threshold — Step 0 applies verbatim at the primed stage, and the
S1.3 chain runs with the primed package's numbers (the display's
"= ehg" line reads "= the primed key weight" via the same equal-weights
identity of the g = 1 standard lift). Ladders of ANY length are covered
by induction along the prefix. CLOSED.

(B6) e_{r−1} = 1 STAGES. j₀ = 0 forced ((F-1) mod 1); every weight is
zero-class automatically; m = −tW with t = t_{r−1} = h⁻¹ mod 1 = 0
Bézout-normalized (s = 1, t = 0 solves 1·s + h·0 = 1), so m = 0 and
P is the plain representative of T. The offset machinery degenerates
gracefully to the unshifted P-lift; no step divides by e − 1 or
consumes e ≥ 2. CLOSED.

(B7) SPARSE P (some P_k = 0, including #{k: P_k ≠ 0} = 1). Absent slots
take no realizer (D.5's convention, S1.2 (F-4)); the no-cancellation
argument (distinct exponents m + k) only ever sums PRESENT slots; P ≠ 0
guarantees at least one. CLOSED.

(B8) NONZERO WEIGHT CLASSES (the offset's raison d'être — the first
demand after a deep increment generically has W ≢ 0 mod e). (F-1)
produces j₀ ≠ 0; the slots j₀ + ek stay < eg ((F-1)'s bracket); the
class restriction of the old (S6b) is never consumed. This is the
pass-11 finding-1 repair, quantified: EVERY class mod e is reached.
CLOSED.

### S1.5 What part (a) discharges downstream

§D4-R's burden ledger has "(c) COMMON FRAME = L4: DISCHARGED
CONDITIONAL ON L1". Theorem A is L1 (with the boundary enumeration the
kernel demanded); therefore L4 (common-frame coherence — the composite
Ψ_η is a function of node data + lifts, input-independent) is now
DISCHARGED UNCONDITIONALLY relative to accepted §B2-DEF + §C. Theorem B
(S2) consumes L4 in exactly this form.

---
*(S2.1–S2.2 appended.)*

### S2.1 Why the per-branch form is false (F1, restated and checked)

L5's exclusivity sentence — "the outcome data are FUNCTIONS of f (…),
so distinct outcome data have DISJOINT strata" — is true for the
polygon and the side-digit tuples and FALSE for the full §C node datum,
which also carries the descended factor ψ (L11) and, at multi-sided
window polygons, the side choice. Neither is a function of f: the
D4-R.0 canonical policy fixes only the LIFT rule.

CHECKED INSTANCE (F1's, arithmetic re-verified here). n = 4, p = 5,
box = monic quartics with c₃, c₂, c₁, c₀ ≡ 0 (mod 5); member
f = x⁴ + 20x³ + 75x² + 375x + 2500: valuations v(c₃,…,c₀) =
(1, 2, 3, 4), so the root window [0,4] has points (0,4), (1,3), (2,2),
(3,1), (4,0): ONE full-span side of slope 1, on-line digits
(d₃,d₂,d₁,d₀) = (4,3,3,4). Residual R₀ = z⁴+4z³+3z²+3z+4; over F₅,
(z−1)²(z−2)² = (z²−3z+2)² = z⁴−6z³+13z²−12z+4 ≡ z⁴+4z³+3z²+3z+4 ✓.
Both ψ = z−1 and ψ = z−2 have (g, μ) = (1, 2): two DISTINCT length-1
prefixes η₁ ≠ η₂ of the same shape, and their strata are the SAME digit
cylinder (ord_ψ R_anch = μ is a condition on the FIXED tuple, not on
f). Every consequence in F1's damage chain follows; in particular no
lift rule can repair this — the ambiguity precedes any lift. Two
distinct SIDES with a common f arise the same way (any window polygon
with two hull sides; both sides' (α)/(β)/(γ) clauses and the (NA)/(HV)
side conditions hold simultaneously for the same f — checked against
C.1(i): a hull side's left neighbours are steeper, hence strictly above
its extension; its right neighbours shallower, hence strictly above;
and the pinned vertex sits strictly above every non-rightmost side's
extension, which is exactly (NA)). The per-branch partition claim is
REFUTED, not open. Nothing below attempts to repair it per-branch.

### S2.2 The joint read datum 𝒟(f), defined

Fix a realized prefix η = (ν₀, …, ν_k) with state cylinder Σ_k in the
common frame Ψ_η (L4, unconditional after S1.5), current key Φ̂ :=
Φ_{cur}, window [0, μ] (μ := μ_k; ROOT instance below), and the
standing Σ_k-facts from the last landing (D.8 resp. D.10 resp. D.4
ROOT): (BOX) w(B_j) > old(j) for j < μ; (VERTEX) w(B_μ) = old(μ) with
nonzero transported digit. For f ∈ Σ_k write B_j for the slot
coefficients of the frame's Φ̂-development and

  J(f) := { j ∈ [0, μ) : B_j ≠ 0 }.

CASE T (no side). J(f) = ∅. Then f = Φ̂^μ·(B_μ + B_{μ+1}Φ̂ + …) with
B_μ ≠ 0: the tracked factor is EXACTLY Φ̂^μ (a FIXED polynomial of the
frame). Outcome datum: the terminal status (ns, μ).

CASE R (read). J(f) ≠ ∅. Let Π(f) := the lower convex hull boundary of
{(j, w(B_j)) : j ∈ J(f)} ∪ {(μ, old(μ))}, from its leftmost point to
(μ, old(μ)) — a finite polygon with sides S₁, …, S_v ordered by span,
slopes strictly increasing leftward. Per side S (slope h′/e′ lowest
terms, span [s₀′, s₀′+w′], stride e′): the ON-LATTICE side digits
d_j := the height-line(j) digit of B_j (zero allowed at interior
on-lattice slots; NONZERO at both endpoints — they are hull vertices);
the side residual, support-anchored: R_S = z^{a_S}·R_anch,S with
R_anch,S(0) ≠ 0, anchor a_S ≥ 0, lead unit u_S ∈ F ˣ; the UNIQUE
factorization R_anch,S = u_S·∏_i ψ_i^{μ_i} into pairwise-distinct monic
irreducibles ψ_i ≠ z (F[z] is a UFD; ψ_i ≠ z since R_anch,S(0) ≠ 0).
Outcome datum:

  𝒟(f) := ( per side S, in span order:
            (e′, h′, s₀′, w′, a_S, u_S, (d_j)_j, {(ψ_i, μ_i)}_i ) ),

the factor collection per side an UNORDERED set (equal-shape factors
carry no order); to each branch (S, ψ_i) attach its species (e′·deg ψ_i
= 1: recentering; ≥ 2: increment) and, for recenterings, the canonical
lift of Theorem A — a function of the branch datum. EVERY component of
𝒟(f) is computed deterministically from f's digits in the common
frame: 𝒟 is a FUNCTION Σ_k → (countable datum set).

ROOT INSTANCE (empty prefix, Σ_{−1} = the full box). Level-0 outcome:
the multiset {(π̄_i, m_i)} of monic irreducible factors of f̄ = f mod p
(unique factorization in F_Q[x]) — a function of f; factors with
m_i = 1 are Hensel leaves (terminal branches); each m_i ≥ 2 opens a
track with key π̂_i (pinned Teichmüller-coefficient lift), window
[0, m_i], vertex (m_i, 0) pinned with unit digit (exact ord: the
cofactor ∏_{i′≠i} π̄_{i′}^{m_{i′}}(root) ≠ 0), sides of positive slope
(D.4 ROOT) — the same CASE T / CASE R dichotomy applies verbatim to
each opened track with old(j) := the box line through (m_i, 0). §C's
normalized single-cluster box (E(ν₀)'s cluster conditions) is the
one-track instance of this; the D4-n3 box is its n = 3 case.

---
*(S2.3 appended.)*

### S2.3 Verification on the refutation instance and on the D4-n3 cell

REFUTATION INSTANCE (S2.1's f, n = 4, p = 5), per the retarget
directive — verified FIRST. At the empty prefix: f̄ = x⁴, root outcome
{(x, 4)} — one datum. The opened track (key x, window [0,4]): J(f) =
{0,1,2,3} (valuations 4,3,2,1 all finite), hull = the single full-span
side of slope 1; datum

  𝒟(f) = ( (e′,h′,s₀′,w′,a,u) = (1,1,0,4,0,1), digits (4,3,3,4),
           factors {(z−1, 2), (z−2, 2)} )

— EXACTLY ONE outcome. The two per-branch prefixes η₁ (descend z−1)
and η₂ (descend z−2) are now the two CHILDREN of the one node, both
present, unordered (equal shape (g,μ) = (1,2)); each opens its own
continuation window [0,2] after its own recentering move (species:
e′·g = 1 — recentering; canonical lifts by Theorem A: centers 1 resp. 2,
weight = the side value at the respective slot — distinct lifts,
distinct children, ONE tree). Uniqueness restored: 𝒟 is single-valued
at f, and no selection between z−1 and z−2 is made or needed. ✓

D4-n3 TARGET CELL (n = 3; the gate's own cell, where L2's run was also
undefined — F1(i): R₀ = ψ·(z−r), ψ irreducible quadratic, r ∈ F_pˣ).
Joint outcome at the opened x-track (window [0,3]): single side of
slope 1, digits (d₂,d₁,d₀), factors {(ψ, 1), (z−r, 1)} — ONE datum;
branch (ψ,1) has species e′·g = 2 (increment: the key φ of the pinned
instance), branch (z−r,1) has species e′·g = 1 (recentering). Both
children carried; the gate's FC8 digit cells are precisely the
𝒟-strata at its resolution (which is WHY the gate's partition check
passed while the per-branch run map was undefinable). ✓

TWO-SIDED WINDOW CHECK (side-choice ambiguity, S2.1's second class).
Cubic instance p arbitrary, v(c₀) = 4, v(c₁) = 1, v(c₂) ≥ 1: window
[0,3] points (0,4), (1,1), (3,0) (slot 2 above): hull = TWO sides,
(0,4)–(1,1) slope 3 and (1,1)–(3,0) slope 1/2. Per-branch reading: both
sides are grammatical reads for the same f (S2.1). Joint reading: ONE
datum with side list ((3/1 side), (1/2 side)), each side carrying its
own digits and factors — no choice. ✓

---
*(S2.4 appended.)*

### S2.4 Theorem B (JOINT-L5), with the full case tree

**Theorem B.** Fix a realized prefix η (the empty prefix included, per
S2.2's ROOT INSTANCE) with state cylinder Σ_k in the common frame
(L4 + Theorem A). Then:
 (i) TOTALITY: the outcome map f ↦ 𝒟(f) (S2.2; value (ns, μ) in case T)
     is defined at EVERY f ∈ Σ_k — no orphan.
 (ii) EXCLUSIVITY: distinct outcome data have disjoint loci (fibers of
     one function), so the fibers PARTITION Σ_k; every emitted branch
     satisfies §C realizability ((NA)/(HV)) — the joint read emits only
     grammatical continuations.
 (iii) RESOLUTION: 𝒟 is measurable w.r.t. the window digit filtration:
     its fibers are countable nested intersections of finite digit
     cylinders, and at every finite height cap H the capped outcome
     (window digits at heights < H) induces a partition of Σ_k into
     FINITE digit cylinders refining to 𝒟 as H → ∞ — the census format
     (FC8/FC9 are its instances at the gate's caps), with the deeper
     data appearing as capped (z)-lumps, none orphaned.

*Proof.*

(i) TOTALITY — the case tree, every leaf displayed.
 T. J(f) = ∅: outcome (ns, μ), defined. [Uses only (VERTEX): B_μ ≠ 0,
    so the factorization f = Φ̂^μ·(unit-slot cofactor) is exact.]
 R. J(f) ≠ ∅: the finite nonempty point set {(j, w(B_j)) : j ∈ J(f)} ∪
    {(μ, old(μ))} has a unique lower-hull boundary (finite planar
    geometry; all heights finite by J's definition, the vertex height
    old(μ) finite by (VERTEX)). Leaf checks:
    R-a GRAMMAR: every hull side has per-slot drop > w(Φ̂): each point
        (j, w(B_j)), j < μ, lies strictly above the old-line ((BOX)),
        so every chord to (μ, old(μ)) drops faster than w(Φ̂) per slot,
        and hull convexity makes every side at least as steep as some
        such chord (D.4's display, re-run on the actual point set). At
        the ROOT instance the same reads: positive slopes (D.4 ROOT).
    R-b SIDE DATA: per side, the on-lattice slots carry well-defined
        digits (graded pieces at the attained heights, D.3(e));
        endpoints are hull vertices, so their heights are ATTAINED
        (w(B_j) = line) with NONZERO digit — the residual's endpoint
        convention holds by construction, not by assumption.
    R-c ANCHOR: R_S ≠ 0 (its lead is a hull-vertex digit ≠ 0), so
        a_S := ord_z R_S is finite and R_anch,S(0) ≠ 0.
    R-d FACTORS: F[z] is a UFD and R_anch,S is a nonzero polynomial
        with R_anch,S(0) ≠ 0: the factorization {(ψ_i, μ_i)} exists, is
        unique, and contains no ψ_i = z. Every irreducible factor is
        listed — none skipped, whatever its shape or multiplicity.
    R-e LIFTS: every recentering-species branch (e′·deg ψ_i = 1) has
        c̃ = the root of its linear ψ_i, c̃ ∈ Fˣ (R-c), and side value
        > w(Φ̂) (R-a): Theorem A supplies its unique canonical lift.
    So 𝒟(f) is defined, with every component forced. Cases T and R are
    complementary by the definition of J(f). ∎(i)

(ii) EXCLUSIVITY. 𝒟 is a single-valued function (every step of (i) is
 deterministic: J, the hull, the digits, the anchored factorization,
 the lifts (Theorem A's uniqueness)); distinct values have disjoint
 fibers — there is nothing else to prove for disjointness. BRANCH
 REALIZABILITY, derived (not assumed):
  (HV) the RIGHTMOST side ends at (μ, old(μ)) (the vertex is the
   point set's right endpoint, hence a hull vertex); its right-endpoint
   digit IS the pinned vertex digit, which the prefix's last landing
   transported as vtx(ν_k) (D.8 (VERTEX)+(TRANSPORT); D.10's unit note
   at recenterings; the Hensel unit at the ROOT) — so the adjacent
   branch's pattern lead equals vtx(ν_k): (HV) holds.
  (NA) every NON-rightmost side S: the hull strictly descends
   rightward of S at shallower slopes, so S's extension to slot μ lies
   strictly below the hull at μ, i.e. old(μ) > (S's extended line at
   μ): (NA) holds for every non-adjacent branch.
 So every branch of every emitted 𝒟 is §C-realizable. ∎(ii)

(iii) RESOLUTION. Each component of 𝒟(f) is computed from finitely
 many digit coordinates once the valuation profile is known; the
 profile's level sets ("w(B_j) = c" = zeros below c + a nonzero digit
 at c; "B_j = 0" = the nested intersection over all c) are digit-
 cylinder conditions. Capping at H: the map f ↦ (all window digits at
 heights < H) has finite-digit-cylinder fibers (pure equation systems:
 every digit VALUE fixed, §C's no-inequation convention) which
 partition Σ_k for every H; 𝒟(f) is a function of the full tower of
 caps (H → ∞ recovers J, the hull, the digits); hence 𝒟's fibers are
 the displayed countable intersections, and each capped partition
 refines the previous. FC8 (root cap: V-lumps + on-line cells) and FC9
 (depth-1 cap: δ-cells + DEEP) are literal instances. ∎(iii) ∎

---
*(S2.5–S2.6 appended.)*

### S2.5 Per-leaf realized-or-empty witnesses

The kernel asks, per leaf of the case tree, a witness that the leaf is
realized or a proof that it is empty. The dividing line is GRAMMAR:

**Lemma W (grammatical ⟹ realized).** Call an abstract datum 𝒟
GRAMMATICAL at the state if: every side slope exceeds w(Φ̂) (per-slot,
R-a's bound); side heights sit on the attainable height lattice of
their slots and side digits take values in the attainable alphabets at
those heights (D.3(e)(ii)); both endpoints of every side carry nonzero
digits, interior on-lattice digits arbitrary (zero allowed); the
rightmost side ends at (μ, old(μ)) with lead = vtx(ν_k) ((HV)); the
factor set is THE factorization of the digit tuple's anchored residual
(forced — not a free choice). Then S(𝒟) ∩ Σ_k ≠ ∅, i.e. some f ∈ Σ_k
computes 𝒟(f) = 𝒟.
*Proof.* The conditions "𝒟(f) = 𝒟" are: the fresh window digits
strictly above the state's floor take the prescribed values (the
on-hull digits and the zeros below the hull lines at heights above the
floor), and the slots left of the leftmost prescribed side vanish to
every height. Heights at or below the floor are already carried by
Σ_k ((BOX)/(VERTEX) via the landing; nothing new is demanded there —
grammaticality put every prescribed height strictly above old(j),
hence above the floor F_k = the old staircase on the interior,
LST(ii)). By §C freshness (C.1(ii)/C.1.5 with TYP: fresh clause
content strictly above the floor cuts exact positive alphabet
fractions on Σ_k; LST(iii): whole level sets above the floor are
free), each FINITE truncation of the condition set has positive mass,
in particular is a nonempty closed cylinder; the conditions are nested
as the truncation height grows; Σ_k and all cylinders are closed in
the compact level-∞ box, so the intersection is NONEMPTY (finite
intersection property). Any member realizes exactly 𝒟. ∎

**Lemma E (non-grammatical ⟹ empty).** If 𝒟 violates grammar, no
f ∈ Σ_k computes it: slope ≤ w(Φ̂) contradicts R-a's chord bound
((BOX)); an off-lattice or off-alphabet demand contradicts D.3(e)'s
attainability (the digit does not exist resp. cannot take the value);
a zero endpoint contradicts R-b (hull vertices have nonzero digits); a
rightmost side not ending at μ, or ending with lead ≠ vtx(ν_k),
contradicts (ii)'s (HV) derivation; a factor set ≠ the residual's true
factorization contradicts UFD uniqueness. Each clause names its
witness fact; no further case exists. ∎

Leaf T is realized at every state: apply Lemma W to the empty side
list (its condition set is "all window slots vanish to every height",
all strictly above the floor; same compactness) — the witness locus
is exactly {f = Φ̂^μ·g : g monic of cofactor degree, slot-μ digit
matching the pin} ∩ Σ_k ≠ ∅.

### S2.6 The (z)/(ep)/(ns) obligation of L5, located clause by clause

The kernel's displayed case list, discharged inside Theorem B:

(z) ZERO cases. Three strata of "vanishing", all typed, none orphaned:
  (z-1) off-hull slots with deep-but-finite valuation: invisible to
   𝒟 (the hull records only its own vertices); such f sit in the same
   fiber as their shallow-hull neighbours — typed by the hull they DO
   induce; at finite caps they sit in the capped cylinder, exactly
   (iii)'s lumps.
  (z-2) slots identically zero (w = ∞), including j_min > 0 (the key
   divides f within the window, Φ̂^{j_min} ∥ f): carried by J(f)'s
   definition; the leftmost-side location IS the record of j_min;
   fibers remain exact ((iii)'s nested intersections — these are the
   pro-cylinder classes, measure-carrying, partition-exact).
  (z-3) TOTAL window degeneracy J(f) = ∅: leaf T, the terminal status
   (ns, μ) — "every candidate coordinate zero to the relevant height"
   at EVERY height. Realized (S2.5), exclusive (complement of case R).
(ep) ENDPOINT cases. The adjacent read j* = μ: the rightmost hull side
   ALWAYS ends at the vertex — every joint read contains exactly one
   adjacent branch family, and its (HV) hinge is DERIVED (Theorem B
   (ii)); non-rightmost sides are the non-adjacent reads, their (NA)
   derived likewise; polygon endpoint slots carry nonzero digits by
   hull-vertex construction (R-b) — the polygon convention is a
   theorem of the joint read, not an assumption.
(ns) NO-SIDE case. Leaf T: a terminal verdict with an exact
   factor identification (the FIXED polynomial Φ̂^μ), not an orphan;
   its locus is nonempty at every state (S2.5) and disjoint from every
   read fiber (J(f) = ∅ vs ≠ ∅).

---
*(S2.7, S3, S4 appended — final.)*

### S2.7 What the joint form does NOT repair (recorded, not attempted)

Theorem B is the TRUE kernel available at this station; it does not by
itself restore §D4-R's linear-run superstructure. Specifically, still
broken as stated in the live §D4-R (F1's damage chain, adopted):
- L2: "the UNIQUE maximal canonical run (ν₀, ν₁, …)" — a single PATH —
  is undefined at multi-branch f. The true object is the unordered
  TREE H_joint^max(f) := the orbit of Theorem B's step (one joint read
  per open track; each branch of each read opens its own track;
  Theorem A's lifts per recentering; equal-shape branches unordered).
  H_joint^max(f) IS unique and total — that much of L2 survives, tree-
  valued.
- L6 (D4R-CYL) and its corollary: per-branch prefixes η are PATHS in
  the tree; {f : η a path-prefix of H_joint^max(f)} = S(η,⊤) survives
  in the path reading, but DISJOINTNESS over Pref(P̂) fails (F1's η₁,
  η₂ are both path-prefixes of one f's tree, with equal strata).
- D4R.1: the ⨆ form and the event identity fail; what survives is the
  SUM identity Σ_{η∈Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (each
  summand Theorem C(b)) and the union bound μ(⋃) ≤ C_P̂·p^{−A} ≤
  M(P̂)·p^{−A_net} — D4R.2′ as a union bound (F1's "what survives",
  concurred). An EXACT event law needs tree-shaped prefixes P̂^tree
  with a JOINT mass theorem (multi-branch freshness / sibling
  independence) — genuinely new §C-side work, out of this unit's
  charge: O2.
The rewiring choice (tree-formulated D4R.1 vs per-path sum-law
consumers) belongs to the §D4-R repair unit, with this note as input.

## S3. OPEN ISSUES (honest)

O1 (interface) TERMINAL-VERDICT LIST. The accepted sources pin no
  verdict list: §C takes "any admissible terminal system"; §D4-R never
  enumerates verdicts; the decomposition note's leaf rule (unopened
  μ = 1) is contradicted by the D4-n3 instance (opens a μ = 1, g = 2
  branch at ν₀ and a μ = 1, g = 1 branch at ν₁). This unit derives the
  one STRUCTURAL terminal status (ns, μ) and proves the partition at
  every state; any consumer-declared verdict set is compatible IFF it
  is a function of the joint branch datum (then it refines Theorem B's
  partition measurably). The verdict list must be pinned by the
  assembly ([2a]/SQ interface) — an interface obligation, not a gap in
  the partition itself.
O2 (downstream) JOINT MASS LAW. Sibling independence / multi-branch
  freshness (the mass of a TREE prefix as the product over all its
  nodes) is not derived here; §C's Theorem C is per-path. Until it
  exists, D4R.1 survives only as the sum law + union bound (S2.7).
O3 (bookkeeping) BASE DIGIT SECTION. Theorem A consumes one pinned
  unit section at the base (Teichmüller, per the decomposition note's
  choice-function clause); §B2-DEF's base text is section-agnostic.
  Any fixed section works; the definitive write-up should declare it
  once, next to the offset-P paragraph.
O4 (scope) ROOT MULTI-CLUSTER CASE. S2.2's ROOT INSTANCE derives the
  level-0 partition (reduction types) and per-cluster tracks; the
  cross-cluster mass product is MONTES L1's (outside §D4-R's
  normalized box, as in the live note). No gap for the kernel; noted
  so the quantifier "empty prefix included" is read at the right box.

## S4. VERDICT

- Part (a) L1: DERIVED — Theorem A (S1.3), all eight boundary cases
  closed (S1.4); consumes accepted §B2-DEF ((S6b′), D.4, D.5, D.9,
  D.10, TRANS/TRANS-RS) + the O3 base pin; L4 discharges (S1.5).
- Part (b) as originally stated: FALSE — F1's counterexample verified
  (S2.1: R₀ = (z−1)²(z−2)² at n = 4, p = 5; plus the two-sided-window
  class); refutation adopted, per-branch form not repaired.
- Part (b) as RETARGETED (joint/branch-multiset): DERIVED — Theorem B
  (S2.4): totality with the full case tree, exclusivity with derived
  (HV)/(NA), finite-cap resolution matching FC8/FC9; per-leaf
  realized-or-empty (S2.5, Lemmas W/E); (z)/(ep)/(ns) located (S2.6).
  Uniqueness verified FIRST on the refutation instance and the D4-n3
  cell (S2.3), per the retarget directive.
- Open issues: 4 (O1 interface, O2 downstream, O3 bookkeeping, O4
  scope note) — none touches Theorem A/B's own chains.
- Conditionality: accepted §B2-DEF + accepted §C throughout; nothing
  else consumed.

