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
### S2.3b The FC8 comparison, displayed [REV 2]
### S2.4 Theorem B (JOINT-L5, structural part), with the full case tree
### S2.5 Per-leaf realized-or-empty witnesses (Lemmas W/E, rebuilt at REV 2)
### S2.6 The (z)/(ep)/(ns) obligation + the D4R.0-K(c) residual [REV 2]
### S2.7 What the joint form does NOT repair (consumer rewiring, not done here)

## S3. OPEN ISSUES (honest)

## S4. VERDICT

## S5. CITE REGISTER [REV 2]

## S6. REV 2 RECORD

## S7. REV 3 RECORD

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
- Part (b), retargeted joint form: DERIVED AT STRUCTURAL STRENGTH
  (Theorem B, S2.4–S2.6): the partition by polygon + digits + factor
  multisets + no-side status. The terminal-verdict refinement is NOT
  derived — the sources underdetermine the verdict function — and is
  split off as the explicit OPEN interface obligation D4R.0-K(c)
  (S2.6; route (b) of the rev-2 charge; at REV 3 tightened and aligned
  to the assembly plan's VP pin — the pin supplies the data, note [3t]
  owes the proofs). Conditional on accepted §B2-DEF + §C only (L4's
  common frame becomes unconditional once Theorem A closes L1 — S1.5).
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

(B5) RECENTERED STAGES / CONSECUTIVE RECENTERINGS [REV 2 — pass-1
finding 4: the chain DISPLAYED with primed indices; no "verbatim"; the
rev-1 gloss "the '= ehg' line reads '= the primed key weight'" is
WITHDRAWN — the honest chain keeps ehg and gains a strict link].
Setting: depth r was created by an increment read of index (e, h, g)
(so w(Φ_r) = ehg, D.5's equal weights), then recentered ℓ ≥ 1 times
with consumed side values λ⁽¹⁾ < λ⁽²⁾ < … < λ⁽ℓ⁾ — strict growth:
(I-aug) at the i-th recentering read gives λ⁽ⁱ⁾ > v(Φ⁽ⁱ⁻¹⁾) = λ⁽ⁱ⁻¹⁾,
and first λ⁽¹⁾ > w(Φ_r) = ehg (D.9(d)). TRANS-RS rebuilds the package
on the SAME coefficient space (ψ⁽ⁱ⁾ = z − c̃⁽ⁱ⁾, c̃⁽ⁱ⁾ ≠ 0, F
unchanged); the clean threshold UPDATES to v(Φ⁽ⁱ⁾) = λ⁽ⁱ⁾ (D.10/D.4:
the recentered key carries the consumed side's value) — while the
REALIZER MACHINERY of C_r is LITERALLY UNCHANGED (D.10 TRANS-RS "S6:
the same 𝒜 and realizers"): (F-1)–(F-4) still run with the ORIGINAL
read index (e, h, g) and Φ_{r−1}-slots. One scale throughout (v = v′
on coefficients; e_read = 1 stretches nothing).
SINGLE RECENTERING (ℓ = 1): demand (W, T) at the primed stage, W >
λ⁽¹⁾ (Step 0 at the primed read, D.9(d) in the primed frame). Chain:
  W_k = (W − (j₀+ek)h)/e
      ≥ (W − (eg−1)h)/e      [j₀+ek ≤ eg−1, (F-1) — unchanged]
      > (λ⁽¹⁾ − (eg−1)h)/e   [W > λ⁽¹⁾ = v(Φ′), the UPDATED threshold]
      > (ehg − (eg−1)h)/e    [λ⁽¹⁾ > ehg — (I-aug) at the recentering
                              read: the NEW link the primed stage needs]
      = h/e                  [same arithmetic: ehg − egh + h = h]
      > w_{r−2}(Φ_{r−1})     [(I-aug) at the stage-(r−1) read; Φ_{r−1}
                              := the key CURRENT at that read, so this
                              IS C_{r−1}'s clean threshold — original
                              or itself recentered alike (S1.1's
                              threshold definition covers both)].
CONSECUTIVE RECENTERINGS (ℓ > 1): demand W > λ⁽ℓ⁾; one more link:
  W_k ≥ (W − (eg−1)h)/e > (λ⁽ℓ⁾ − (eg−1)h)/e
      > (λ⁽¹⁾ − (eg−1)h)/e   [λ⁽ℓ⁾ > λ⁽¹⁾: the (I-aug) ladder above]
      > (ehg − (eg−1)h)/e = h/e > w_{r−2}(Φ_{r−1})   [as at ℓ = 1].
Ladders of ANY length: the ladder link consumes only λ⁽ℓ⁾ > λ⁽¹⁾, true
for every ℓ by the displayed strict growth. (F-4)'s recursion still
descends to stage r−1 and bottoms as before — recenterings add NO
recursion depth (same C_r, same slots): well-foundedness untouched.
CLOSED.

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
children carried; the gate's FC8 digit cells agree with the capped
𝒟-values on the target region — the comparison DISPLAYED at S2.3b
[REV 2 — pass-1 finding 5: previously asserted, not displayed] —
which is why the gate's partition check passed while the per-branch
run map was undefinable. ✓

### S2.3b The FC8 comparison, displayed [REV 2 — pass-1 finding 5]

FC8's cell definitions, verbatim from the live §D4-R.6 (MOVES
2026-07-24.md lines 5271–5280; grep the quoted text — the file is
under §C-region edits, so line numbers may drift): "the sibling strata
of the root read are resolved as: NC (non-cluster) ∪ 20 valuation
lumps (V₀, V₁, V₂) := (min(v(c₀),4), min(v(c₁),3), min(v(c₂),2)) on
the cluster, EXCEPT the target region {V₀ = 3, V₁ ≥ 2} which is
refined into its p²(p−1) on-line digit cells (d₂, d₁, d₀) ∈
F_p × F_p × F_pˣ." Comparison with 𝒟, region by region:
- TARGET REGION {V₀ = 3, V₁ ≥ 2}: every member has window [0,3] points
  slot 0 AT height 3 (V₀ = 3, digit d₀ ≠ 0), slot 1 weakly above
  height 2 (V₁ ≥ 2), slot 2 weakly above height 1 (cluster), vertex
  (3,0) (monic lead) — so the hull is the SINGLE full-span side
  (0,3)–(3,0) of slope 1, and the FC8 cell equations {ht-3 digit of c₀
  = d₀ ≠ 0; ht-2 digit of c₁ = d₁; ht-1 digit of c₂ = d₂} are
  LITERALLY the capped-𝒟 fiber equations at the read heights (Theorem
  B(iii)'s cap: side (e′,h′,s₀′,w′,a) = (1,1,0,3,0), digits
  (d₂,d₁,d₀)). The full 𝒟-value adds only the factor multiset — a
  FORCED function of (d₂,d₁,d₀) (Lemma W's G7) — so on this region
  FC8 cells ↔ 𝒟-strata at the gate's resolution, bijectively; the
  gate's own cells are the (d₂,d₁,d₀) with R₀ = ψ·(z−r) as displayed
  above.
- THE 20 VALUATION LUMPS: capped valuation data off the target region
  — exactly Theorem B(iii)'s capped (z)-lumps ("deeper structure of
  non-target lumps is other prefixes' business", the FC8 text's own
  scope sentence): they do not resolve 𝒟 and are not claimed to.
- NC (non-cluster): the complement of the normalized cluster box —
  outside Σ_{−1}, hence outside the kernel's quantifier (the gate
  partitions the ambient level-N box; the kernel partitions Σ_k).
CLAIM STRENGTH: agreement is displayed FOR THE TARGET REGION cells
(the only FC8 cells at 𝒟-resolution); lumps match as capped lumps.
Nothing beyond the gate's own resolution is claimed.

TWO-SIDED WINDOW CHECK (side-choice ambiguity, S2.1's second class).
Cubic instance p arbitrary, v(c₀) = 4, v(c₁) = 1, v(c₂) ≥ 1: window
[0,3] points (0,4), (1,1), (3,0) (slot 2 above): hull = TWO sides,
(0,4)–(1,1) slope 3 and (1,1)–(3,0) slope 1/2. Per-branch reading: both
sides are grammatical reads for the same f (S2.1). Joint reading: ONE
datum with side list ((3/1 side), (1/2 side)), each side carrying its
own digits and factors — no choice. ✓

---
*(S2.4 appended.)*

### S2.4 Theorem B (JOINT-L5, structural part), with the full case tree

**Theorem B.** Fix a realized prefix η (the empty prefix included, per
S2.2's ROOT INSTANCE) with state cylinder Σ_k in the common frame
(L4 + Theorem A). VALUES [REV 2 — pass-1 finding 3, route (b)]: 𝒟's
values are the STRUCTURAL data only — case R: polygon + per-side digit
tuples + factor multisets (branch species and canonical lifts
attached); case T: the no-side STATUS (ns, μ); at the EMPTY prefix
(Σ_{−1} = T(∅,⊤) = the full box) the value is the ROOT datum 𝒟_root of
case R0 below — the level-0 factor multiset with the per-opened-track
T/R data, componentwise [REV 3 — pass-2 gap 6: the root case is now an
explicit tree root, no longer conflated with the one-cluster instance].
NO general
terminal-verdict function is defined or claimed in this theorem; the
verdict refinement of L5's clause (ii) is the OPEN interface
obligation D4R.0-K(c), stated exactly at S2.6. With that scope:
 (i) TOTALITY: the outcome map f ↦ 𝒟(f) (S2.2; value (ns, μ) in case T)
     is defined at EVERY f ∈ Σ_k — no orphan.
 (ii) EXCLUSIVITY: distinct outcome data have disjoint loci (fibers of
     one function), so the fibers PARTITION Σ_k; every emitted branch
     satisfies §C realizability in the FULL rev-12 three-condition
     sense (NA)/(HV)/(SAE) [REV 3 — pass-2 gap 4: (SAE) now named,
     derived, and stated in the interface], so appending any emitted
     branch to η is TRANSITION-ADMISSIBLE (§C rev 13, cite [c-sae]) —
     the joint read emits only grammatical continuations.
 (iii) RESOLUTION: 𝒟 is measurable w.r.t. the window digit filtration:
     its fibers are countable nested intersections of finite digit
     cylinders, and at every finite height cap H the capped outcome
     (window digits at heights < H) induces a partition of Σ_k into
     finite PURE digit cylinders, every capped OUTCOME CLASS (valuation
     lump, verdict cell) a FINITE UNION of these [REV 3 — pass-2
     wording gap: an exact capped valuation is a union over its
     possible nonzero digit values, not one pure cylinder], refining
     to 𝒟 as H → ∞ — the census format (FC8/FC9 are its instances at
     the gate's caps, in the union-of-cylinders reading), with the
     deeper data appearing as capped (z)-lumps, none orphaned.

*Proof.*

(i) TOTALITY — the case tree, every leaf displayed; ROOT FIRST [REV 3
 — pass-2 gap 6].
 R0. EMPTY PREFIX (Σ_{−1} = T(∅,⊤) = the full box): 𝒟_root(f) :=
    ( {(π̄_i, m_i)}_i, (𝒟^{(i)}(f))_{i: m_i ≥ 2} ) — the multiset of
    monic irreducible factors of f̄ (unique factorization in F_Q[x]:
    total, single-valued) together with, per OPENED track i (key π̂_i,
    window [0, m_i], its own frame — S2.2 ROOT INSTANCE), that track's
    case-T/R datum computed by the cases below IN THE TRACK'S FRAME.
    Factors with m_i = 1 are Hensel leaves (terminal root branches, no
    track opened). (BOX)/(VERTEX) hold per track (the cofactor unit
    gives the exact vertex ord, S2.2), so the T/R dichotomy below
    applies to each track separately; MIXED per-track statuses (some
    tracks T, some R) are carried componentwise by the product datum —
    one function value, no selection, no conflation. The normalized
    single-cluster box is the one-track instance (E(ν₀) pins one
    factor): on it 𝒟_root = the single track's 𝒟 and the cases below
    read verbatim.
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
    complementary by the definition of J(f), per track; R0's value
    aggregates the per-track values componentwise over the (total)
    level-0 factorization. ∎(i)

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
  (SAE) [REV 3 — pass-2 gap 4] every side S, at every span slot j < μ:
   S's endpoints are hull vertices, i.e. POINTS of the set — heights
   strictly above old at slots < μ ((BOX)), equal at μ ((VERTEX)) —
   and (new_S − old) is AFFINE on the span; an affine function
   strictly positive at both span endpoints (both < μ), or strictly
   positive at the left endpoint and zero exactly at the right
   endpoint μ, is strictly positive at every span slot j < μ:
   new_S(j) > old(j) there, and new_S(μ) = old(μ) when the span
   reaches the vertex — exactly §C rev 12's two displayed (SAE) lines
   ([c-sae]).
 So every branch of every emitted 𝒟 is §C-realizable in the full
 (NA)+(HV)+(SAE) sense, hence TRANSITION-ADMISSIBLE when appended to η
 (§C rev 13, [c-sae]); at R0 the same three displays run per track in
 the track's frame (nothing above used more than an arbitrary realized
 frame's (BOX)/(VERTEX)). ∎(ii)

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
 refines the previous. FC8's target-region cells are single pure
 cylinders (each digit VALUE fixed); its 20 V-lumps and FC9's DEEP
 class are finite UNIONS of the capped fibers (coarser,
 cell-data-measurable) — instances of the capped format in the
 union-of-cylinders reading [REV 3 — pass-2 wording gap]. At R0 the
 level-0 multiset is a function of the height-0 digits (a finite pure
 cylinder datum) and each track's window digits are capped functions
 of the box digits (C.0.5's unitriangular transport through the pinned
 key π̂_i), so the product datum is measurable cap by cap. ∎(iii) ∎

---
*(S2.5–S2.6 appended.)*

### S2.5 Per-leaf realized-or-empty witnesses

The kernel asks, per leaf of the case tree, a witness that the leaf is
realized or a proof that it is empty. The dividing line is GRAMMAR:

**Lemma W (grammatical ⟹ realized) [REBUILT at REV 2 — pass-1 finding
1: the grammar now carries the full hull topology; each condition is
consumed at a named step].** An abstract case-R datum 𝒟 (side list
with headers (e′,h′,s₀′,w′,a_S,u_S), digit tuples (d_j), factor sets)
is GRAMMATICAL at the state when:
 (G0) WELL-FORMED SIDES: the side list is NONEMPTY (a case-R datum;
   the no-side case is leaf T's DIRECT witness below, not a G0
   instance) and each header is a NONDEGENERATE lattice side over
   [0, μ]: gcd(e′,h′) = 1, w′ > 0 [REV 3 — pass-2 type omission:
   zero-width "sides" excluded], e′ | w′, span [s₀′, s₀′+w′] ⊆ [0, μ],
   digit tuple indexed by exactly the on-lattice slots
   s₀′ + e′·{0, …, w′/e′}. (With (G3)+(G5), w′ > 0 forces s_min < μ:
   case R is nonvacuous.)
 (G1) SLOPE BOUND: every side's per-slot descent slope h′/e′ > w(Φ̂)
   (ROOT: > 0) — R-a's bound.
 (G2) LATTICE/ALPHABET: prescribed heights lie on the attainable
   height lattice of their slots, digits in the attainable alphabets
   at those heights (D.3(e)(ii)); both endpoints of every side carry
   NONZERO digits; interior on-lattice digits arbitrary (zero OK).
 (G3) CONTIGUITY (shared vertices, no gaps/overlaps): the spans tile
   [s_min, μ]: side i's right endpoint slot = side (i+1)'s left
   endpoint slot, BOTH lines passing through ONE shared point (equal
   height there); no other slot doubly covered, none between uncovered.
 (G3′) SHARED-VERTEX DIGIT CONSISTENCY [REV 3 — pass-2 critical 1]: at
   each shared vertex slot j of (G3) (side i's right endpoint = side
   (i+1)'s left endpoint), the two sides prescribe THE SAME digit:
   d_j^{(i)} = d_j^{(i+1)} — ONE digit value for the ONE coefficient
   B_j at the ONE shared height, nonzero (both sides' endpoint-nonzero
   requirements met by the single value) and in the slot's attainable
   alphabet at that height (both (G2) memberships met by the single
   value). [The per-side tuples overlap at j; G3′ says the overlap is
   consistent — equal lines give one HEIGHT (G3), not one DIGIT.]
 (G4) CONVEX ORDER: descent slopes strictly increase leftward (§B2-DEF
   D.4's convention — S5 cite [c-hull]); successive sides have
   DISTINCT slopes, so every shared point is a genuine vertex.
 (G5) RIGHT ANCHOR + (HV): the rightmost side ends at (μ, old(μ)) with
   lead (= right-endpoint digit) = vtx(ν_k).
 (G6) (NA)+(SAE), derived clauses [REV 3 — (SAE) added, pass-2 gap 4]:
   (NA) every non-rightmost side's extension to slot μ lies strictly
   below old(μ) — IMPLIED by (G3)+(G4)+(G5): right of side S the chain
   descends at strictly shallower slopes (G4), unbroken (G3), to
   (μ, old(μ)) (G5), so old(μ) = chain(μ) > ext_S(μ). (SAE) every
   side's line lies strictly above the old line at its span slots
   j < μ, with equality at μ when the span reaches the vertex —
   IMPLIED by (G1)+(G3)+(G5): Step 2's telescoping display below IS
   this inequality (chain(j) > old(j)), and the vertex equality is
   (G5). Kept explicit for the §C interface (realizability =
   (NA)+(HV)+(SAE), rev 12 — [c-sae]) and Lemma E's clause-for-clause
   complement.
 (G7) DERIVED-FIELD COHERENCE: per side, (a_S, u_S, factor set) equal
   the values FORCED by (d_j): a_S = ord_z R_S, u_S = lead unit of
   R_anch,S, factor set = THE UFD factorization of R_anch,S.
Then S(𝒟) ∩ Σ_k ≠ ∅: some f ∈ Σ_k computes 𝒟(f) = 𝒟.
*Proof.* STEP 1 (the condition set 𝒞(𝒟) is well-defined). "𝒟(f) = 𝒟"
transcribes per slot: (left) B_j = 0 at every height for j < s_min;
(side) for j ∈ [s_min, μ): j lies on EXACTLY ONE side line — by (G3)
one covering side, or a shared vertex where the two lines AGREE (one
HEIGHT) and where, by (G3′), the two prescribed digits AGREE (one
DIGIT) — so "zeros strictly below line(j); digit at line(j) = d_j
where on-lattice" demands ONE height profile AND ONE digit value per
slot, never two [(G3) consumed: overlapping sides would demand two
heights at one B_j — no f satisfies both; (G3′) consumed [REV 3 —
pass-2 critical 1]: without it two adjacent sides could prescribe two
DISTINCT nonzero digits for the one coefficient B_j at the one shared
height — a datum passing rev-2's G0–G7 whose condition set is
instantly empty; a gap would leave a slot free to dip below the chain,
changing the hull]; (vertex) slot μ: NO new demand — Σ_k pins w(B_μ) = old(μ)
with digit vtx(ν_k), and (G5) says the prescribed value MATCHES the
pinned one [(G5) consumed: else 𝒞(𝒟) re-pins a DETERMINED coordinate
to a different value — instantly empty, and not a fresh demand].
STEP 2 (freshness of every demand). For chain slots j < μ: line(j) =
old(μ) + Σ(per-slot drops, j→μ) > old(μ) + (μ−j)·w(Φ̂) = old(j)
[consumed: (G3) — the chain is unbroken from j to μ; (G1) — each drop
> w(Φ̂); (G5) — it ends AT (μ, old(μ))]. So every demanded coordinate
sits strictly above the old line, hence above the floor F_k = the old
staircase on the interior (LST(ii), cite [c-floor]); demands at/below
old(j) are Σ_k's own (BOX) zeros — consistent, nothing new. By
LST(iii) + C.2's free-coordinate characterization (cites [c-free]) the
demanded level sets are FREE on Σ_k; by C.1.5/TYP(b) (cite [c-cut])
each zero clause cuts exactly p^{−1} and each value clause exactly
(alphabet)^{−1} — the demanded value is IN the alphabet by (G2)
[consumed]. All clauses are pure equations (cite [c-noineq]). Hence
every FINITE truncation (zero demands capped at height H) is a digit
cylinder of positive mass on Σ_k (mass(Σ_k) > 0: realized prefix);
truncations nest as H grows; all are closed in the compact level-∞
box: the intersection is NONEMPTY (finite intersection property). Fix
f in it.
STEP 3 (f computes 𝒟 — ONE polygon assembles). J(f) ∩ [0, s_min) = ∅
(left zeros); each prescribed vertex slot has w(B_j) = line(j) with
nonzero digit ((G2) endpoints); every other point of f lies weakly
above the chain (zeros below its line). The chain, as a function on
[s_min, μ], is CONVEX [(G4) consumed] and its vertices are touched;
hence hull = chain: the chain is a convex minorant of the point set
(chain ≤ hull); between touched vertices the hull is convex and equals
the chain at both endpoints, so hull ≤ chord = chain — equality. SIDE
DECOMPOSITION: the hull's maximal segments = the prescribed sides
[(G4) STRICTNESS consumed: each shared vertex is a genuine slope
break, so no two prescribed sides merge; no new break appears inside a
side — the hull is linear there]. DIGITS: read off f = the prescribed
(d_j); at a shared vertex the ONE digit of B_j is the ONE demanded
value, which BOTH adjacent sides' tuples carry [(G3′) consumed: both
per-side tuples are recovered from the single coefficient]. DERIVED
FIELDS: computed from (d_j) by the same forced
functions = the prescribed ones [(G7) consumed]. So 𝒟(f) = 𝒟
componentwise, with f ∈ Σ_k. ∎

**Lemma E (non-grammatical ⟹ empty) [REBUILT at REV 2 — pass-1
finding 2: exhaustive BY COMPLEMENTATION against the rebuilt
grammar].** GRAMMATICAL := G0 ∧ G1 ∧ G2 ∧ G3 ∧ G3′ ∧ G4 ∧ G5 ∧ G6 ∧ G7
(Lemma W — NINE conjuncts at rev 3, G3′ inserted); NON-GRAMMATICAL :=
the negation = ¬G0 ∨ ¬G1 ∨ ¬G2 ∨ ¬G3 ∨ ¬G3′ ∨ ¬G4 ∨ ¬G5 ∨ ¬G6 ∨ ¬G7
(De Morgan — the bijection RE-CHECKED after G3′'s insertion [REV 3]:
still one clause per conjunct, identity on indices). The case list
below carries EXACTLY ONE clause per grammar conjunct, so it is
complete BY CONSTRUCTION, not by hand enumeration. Witness schema: each step of
Theorem B(i)/(ii) proves every ACTUAL datum 𝒟(f) satisfies the
corresponding G_i; a 𝒟 violating G_i therefore equals no 𝒟(f).
 ¬G0 (malformed header): 𝒟(f)'s sides are maximal hull segments of a
   lattice point set — slopes in lowest terms with on-lattice endpoint
   slots (R-b): a malformed header never arises.
 ¬G1 (shallow slope): slope ≤ w(Φ̂) contradicts R-a's chord bound
   ((BOX)).
 ¬G2 (off-lattice / off-alphabet / zero endpoint): contradicts
   D.3(e)'s attainability (the digit does not exist resp. cannot take
   the value); a zero endpoint contradicts R-b (hull vertices carry
   nonzero digits).
 ¬G3 (gap / overlap / two-height junction): 𝒟(f)'s side list is the
   segment decomposition of ONE contiguous lower-hull boundary from
   its leftmost point to (μ, old(μ)) (case R's definition; finite
   planar geometry): successive segments share their vertex at ONE
   height, tile the span, never overlap — a datum violating any of
   this differs from every such decomposition.
 ¬G3′ (shared-vertex digit conflict) [REV 3 — pass-2 critical 1's
   matching negation clause]: every ACTUAL datum satisfies G3′ —
   𝒟(f)'s two adjacent side tuples at a shared vertex both read THE
   digit of the single coefficient B_j at the single shared height
   (R-b): one coefficient, one digit, so the two entries are EQUAL. A
   datum with d_j^{(i)} ≠ d_j^{(i+1)} therefore equals no 𝒟(f);
   moreover its emptiness is direct — its condition set demands two
   distinct values of one digit, which no f satisfies.
 ¬G4 (non-convex order / repeated slope): a hull's maximal segments
   have strictly increasing descent slopes leftward (D.4, cite
   [c-hull]); equal successive slopes would merge into one maximal
   segment, contradicting maximality.
 ¬G5 (bad right end / bad lead): a rightmost side not ending at
   (μ, old(μ)), or with lead ≠ vtx(ν_k), contradicts (ii)'s (HV)
   derivation ((VERTEX)+(TRANSPORT) via the landing).
 ¬G6 ((NA) or (SAE) violated) [REV 3 — (SAE) added; vacuity wording
   precisified per pass-2]: every actual datum satisfies BOTH — (NA)
   by (ii)'s convexity display, (SAE) by (ii)'s affine-interpolation
   display. [Precisely: ¬G6 is IMPOSSIBLE when G1, G3, G4, G5 all hold
   (G6 is implied, Lemma W), though it CAN co-occur with failures
   among them; a redundant conjunct does not break De Morgan
   complementation — recorded so the bijection stays
   clause-for-clause.]
 ¬G7 (derived-field mismatch): contradicts the forced computations:
   a_S = ord_z R_S, u_S = the anchored lead, and UFD uniqueness of the
   factorization in F[z] (ψ_i ≠ z since R_anch,S(0) ≠ 0).
Each clause names its witness fact; completeness is the displayed
complementation, one negation clause per grammar clause. ∎

Leaf T is realized at every state — DIRECT witness [REV 3 — pass-2
gap 3: this is NOT an application of Lemma W, which is stated for
case-R data with a NONEMPTY side list (G0 at rev 3); an empty list has
no s_min (G3) and no rightmost side (G5), and leaf T is case T]. Leaf
T's condition set on Σ_k is "B_j = 0 for every j < μ": the demands at
heights ≤ old(j) are Σ_k's own (BOX) zeros — nothing new; the FRESH
demands are the zeros at heights strictly above old(j), all at
coordinates free on Σ_k ([c-free]); each finite truncation (fresh
zeros at heights < H) is a pure digit cylinder of positive mass
([c-cut]: each zero clause cuts exactly p^{−1}; mass(Σ_k) > 0);
truncations nest as H grows and are closed in the compact level-∞
box: the intersection is NONEMPTY (finite intersection property —
Lemma W Step 2's MECHANISM, run directly on this condition set). Any
f in it has J(f) = ∅ and the pinned slot-μ digit (Σ_k's (VERTEX)), so
𝒟(f) = (ns, μ): the witness locus is exactly {f = Φ̂^μ·g : g the
unit-slot cofactor} ∩ Σ_k ≠ ∅.
ROOT LEAVES (case R0) [REV 3 — with pass-2 gap 6's root case]:
realized-or-empty splits as (a) the level-0 multiset: every
{(π̄_i, m_i)} with Σ m_i·deg π̄_i = n is realized (the Teichmüller-
coefficient monic lift of ∏ π̄_i^{m_i}), every other multiset empty
(degree budget); (b) per opened track: Lemmas W/E and the leaf-T
witness, applied in the track's frame; (c) the JOINT witness — all
tracks' data realized SIMULTANEOUSLY — is the cross-cluster product,
MONTES L1's territory (O4): consumed as a cite, NOT re-derived here;
rev 3 claims per-track realized-or-empty only.

### S2.6 The (z)/(ep)/(ns) obligation + the D4R.0-K(c) residual [REV 2]

The kernel's displayed case list, located clause by clause [REV 2 —
route (b)]: (z)/(ep) discharged at structural strength inside Theorem
B; (ns) discharged as STRUCTURAL STATUS, its verdict labeling split
off as the explicit interface obligation D4R.0-K(c) below:

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
(ns) NO-SIDE case. Leaf T: the structural terminal STATUS (ns, μ)
   with an exact factor identification (the FIXED polynomial Φ̂^μ),
   not an orphan; its locus is nonempty at every state (S2.5) and
   disjoint from every read fiber (J(f) = ∅ vs ≠ ∅). Its VERDICT
   LABEL — and every other halting decision — is D4R.0-K(c)'s to pin.

THE RESIDUAL, NAMED [REV 2 — pass-1 finding 3; route (b) of the rev-2
charge]. **D4R.0-K(c) (terminal-verdict interface — OPEN).** Supply:
 (c1) VERDICT DATA [REV 3 — the two attachment levels separated,
   per pass-2]: a pinned VERDICT ALPHABET V and a HALTING RULE τ
   assigning (i) to each BRANCH of each case-R cell's branch set a
   value in {CONTINUE} ∪ V (verdicts attach to BRANCHES) and (ii) to
   each no-side status (ns, μ) a value in V (the whole track halts);
   a CELL-level terminal outcome is DERIVED — the multiset of its
   halted branches' verdicts — never a second primitive. τ a function
   of CELL data alone (never of f).
 (c2) EXACTLY-ONE-VERDICT on a CLOSED domain [REV 3 — the "if in
   scope" conditional removed]: the non-continuing configurations are
   pinned as: every no-side cell, every τ-halted branch, AND the root
   Hensel leaves (m_i = 1 — explicit in case R0); each receives
   exactly one verdict, none orphaned, none doubled.
 (c3) COMPATIBILITY, two parts, only the first automatic [REV 3 —
   pass-2: rev 2's "automatic" was an overclaim]:
   (c3-a) PARTITION — automatic given (c1)+(c2): τ-refined cells are
     Theorem B's cells split by a cell-data function, hence fibers of
     a function of f: again a partition (B(ii)).
   (c3-b) FINITE-CAP DETECTABILITY — NOT automatic: a function of the
     complete (possibly infinite-height) cell datum need not be
     determined at any finite cap (exact fibers are pro-cylinders —
     B(iii)'s nested intersections, e.g. the (z-2) identically-zero
     slots). REQUIRED as a condition on τ: τ is a STOPPING RULE for
     the window digit filtration — every halt-and-verdict decision is
     determined by the capped cell datum at some finite height. Under
     (c3-b) each τ-refined cell is, at every cap at or beyond its
     detection height, a finite UNION of pure digit cylinders
     (B(iii)'s capped format as re-worded at rev 3); without (c3-b),
     τ-preimages are only countable unions of B(iii)'s fibers —
     measurable, but not cap-detectable, and the census format does
     not apply to them.
 DISCHARGING INSTANCE [REV 3 — the assembly pin consumed]. The
 assembly plan (ASSEMBLY_PLAN_2026-07-26.md §4t, rev 9) has PINNED the
 verdict system as VP ([c-vp]): (VP-1) V := finite multisets of pairs
 (E, F) ∈ ℕ_{≥1}² (a τ-halted leaf of a degree-d cluster carries v
 with Σ E·F = d) — (c1)'s alphabet; (VP-2) τ := the three displayed
 cell-data certificate clauses (τ-irr)/(τ-ns)/(τ-hen), a function of
 cell data alone, with the root Hensel leaves pinned IN SCOPE — (c1)'s
 rule with (c2)'s domain closed exactly as required here (and the
 leaf-rule refutation resolved by T_can^τ pruning); (VP-3) carries the
 proof duties = (c2) exactly-one-verdict + (c3) + VP-SOUND, owed by
 note [3t]. So D4R.0-K(c) is no longer an unaddressed specification:
 it is an interface CONSUMED by that pin. What remains open is VP-3's
 proofs at [3t] — including (c3-b)'s stopping-rule check for each of
 (τ-irr)/(τ-ns)/(τ-hen) — not any further specification in this unit.
WHY THE SOURCES UNDERDETERMINE τ (exact quotes with line numbers in
S5, cites [c-term], [c-hull]'s register): §C covers "any admissible
terminal system" (C.3) — a parameter, not a list; §D4-R's L2/L5 use
"terminal verdict" as an interface word with no enumeration; §B2-DEF
D.0–D.12 define no verdict taxonomy at all; and the decomposition
note's leaf rule (unopened μ = 1) is REFUTED by the D4-n3 instance
(μ = 1 branches OPEN at ν₀ and ν₁). Until (c1)–(c2) land: L5's clause
(ii) ("one terminal verdict") is discharged ONLY at the structural
status (ns, μ); Theorem D4R.0's cell values read "all polygon/digit
values AND the no-side statuses"; the FULL-verdict form of L5 is NOT
discharged by this unit — §D4-R's consumption of L5 splits into the
structural part (Theorem B, discharged) and the verdict part
(D4R.0-K(c), open).

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

O1 = D4R.0-K(c) (interface — OPEN, and BLOCKING for the full-verdict
  form of L5) [RESTATED at REV 2 — pass-1 finding 3 adopted: rev 1's
  "non-blocking" label was WRONG for Theorem B as then advertised].
  The accepted sources pin no verdict list: §C takes "any admissible
  terminal system" (C.3 — quote at S5 [c-term]); §D4-R never
  enumerates verdicts (L2/L5 carry "terminal verdict" as an interface
  word); §B2-DEF D.0–D.12 define none; the decomposition note's leaf
  rule (unopened μ = 1) is contradicted by the D4-n3 instance (opens a
  μ = 1, g = 2 branch at ν₀ and a μ = 1, g = 1 branch at ν₁). This
  unit therefore claims ONLY the structural partition (Theorem B as
  restated at rev 2) and derives the one STRUCTURAL terminal status
  (ns, μ); it does NOT define the general verdict function nor prove
  that every non-continuing configuration receives exactly one verdict
  — that is D4R.0-K(c), stated exactly at S2.6 ((c1)–(c3)), to be
  pinned by the assembly ([2a]/SQ interface). Non-blocking for the
  structural Theorems A/B; BLOCKING for adopting Theorem B as a
  discharge of L5's full next-outcome/terminal partition. [REV 3: the
  assembly plan's rev-9 VP pin ([c-vp]) now SUPPLIES (c1)–(c2)'s data
  and owns the proof duties at note [3t]; S2.6's (c1)–(c3) are
  tightened to consume it, with (c3-b) finite-cap detectability stated
  as the explicitly NON-automatic clause. Still open pending VP-3.]
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
  normalized box, as in the live note). Noted so the quantifier
  "empty prefix included" is read at the right box. [REV 3 — pass-2
  gap 6: the root state is now case R0 of Theorem B's displayed tree
  (product datum, mixed statuses componentwise); VP-2 ([c-vp]) pins
  the Hensel leaves IN verdict scope; realized-or-empty at the root is
  claimed PER TRACK only — the all-tracks-simultaneous witness stays
  MONTES L1's cite (S2.5 ROOT LEAVES).]

## S4. VERDICT

- Part (a) L1: DERIVED — Theorem A (S1.3), all eight boundary cases
  closed (S1.4); consumes accepted §B2-DEF ((S6b′), D.4, D.5, D.9,
  D.10, TRANS/TRANS-RS) + the O3 base pin; L4 discharges (S1.5).
- Part (b) as originally stated: FALSE — F1's counterexample verified
  (S2.1: R₀ = (z−1)²(z−2)² at n = 4, p = 5; plus the two-sided-window
  class); refutation adopted, per-branch form not repaired.
- Part (b) as RETARGETED (joint/branch-multiset): DERIVED AT
  STRUCTURAL STRENGTH [REV 2, route (b); REV 3 repairs in place] —
  Theorem B (S2.4): totality with the full case tree (root case R0
  displayed, rev 3), exclusivity with derived (HV)/(NA)/(SAE) (the
  full rev-12 realizability class, rev 3), finite-cap resolution
  matching FC8/FC9 (the target-region agreement DISPLAYED, S2.3b;
  pure-cylinder vs union wording fixed, rev 3); per-leaf
  realized-or-empty (S2.5, Lemmas W/E — grammar G0–G7 + G3′ at rev 3,
  nine-conjunct complementation-complete case list; leaf T by DIRECT
  witness; root leaves per track). The terminal-verdict refinement
  is NOT derived: D4R.0-K(c) (S2.6) is OPEN and blocks the full-verdict
  form of L5. Uniqueness verified FIRST on the refutation instance and
  the D4-n3 cell (S2.3), per the retarget directive.
- Open issues: 4 (O1 = D4R.0-K(c), OPEN interface, BLOCKING for
  full-verdict L5; O2 downstream; O3 bookkeeping; O4 scope note) —
  none touches Theorem A/B's own chains at their rev-2 strength.
- Conditionality: accepted §B2-DEF + accepted §C throughout; nothing
  else consumed.

## S5. CITE REGISTER [REV 2 — pass-1 findings 6–11 + rev-2 body tags]

Every quote is verbatim from the live MOVES_2026-07-24.md, line numbers
as read 2026-07-26. The file is under concurrent edit in its §C region,
so numbers may DRIFT: pass 2 should verify by grepping the quoted text,
with the number as a locator hint.

[c-multiside] (pass-1 finding 6 — S2.1's "checked against C.1(i)").
  The intended sources, quoted:
  - C.1.0(b)(i), lines 3531–3533: "a hull-side read asserts (α) span
    clauses on its side's slots [s₀', s₀'+w'], (β) strictly-above-
    extended-line clauses at slots < s₀', and (γ) the same at slots in
    (s₀'+w', μ_i]."
  - C.0 realizability, lines 3469–3472: "(NA) at a NON-ADJACENT read
    (right endpoint s₀'+w' < μ_i), the pinned old vertex lies strictly
    above the extended new line: old(μ_i) > new(μ_i); (HV) at an
    ADJACENT read ν_{i+1}: (pattern lead of ν_{i+1}) = vtx(ν_i)."
  S2.1's parenthetical re-derives exactly these for both hull sides of
  one f (steeper left neighbours / shallower right neighbours strictly
  above each side's extension); the register makes the match checkable.
[c-noineq] (pass-1 finding 7 — "§C's no-inequation convention").
  C.0, lines 3420–3422: "All pattern data below are FIXED tuples (with
  nonzero entries where the polygon conventions require), so strata are
  pure equation systems — no inequations occur."
[c-cut] (pass-1 finding 8 — Lemma W's freshness/counting input).
  - C.1(ii), lines 3819–3821: "E_fresh's realizations constrain only
    coordinates FREE on Σ_i — strictly above the floor at
    factor-interior indices, hence outside Z_i's downset and off
    DIG_i's rim leads".
  - C.1.5 proof, lines 3926–3929: "Fresh STRIP clauses are literal
    zeros at coordinates with ht strictly above F_i at factor-interior
    indices: not in Z_i, not leads of DIG_i ((ZC-b): rim), pairwise
    distinct — each cuts exactly p^{−1} on the graph." And lines
    3934–3937: "by TYP(b) — the composite assignment map is additive
    onto the digit's alphabet (= D.3(e)(i)'s piece-map image, D.11's
    convention), so its fibers are equal-size kernel cosets — the
    equation cuts exactly (alphabet)^{−1}".
  - LST(iii), lines 3660–3663: "SELECTION: for a factor-interior slot
    coefficient B with γ' > old_i(slot(B)), the ENTIRE level set
    L_{γ'}(B) lies strictly above the floor downset {ht ≤ F_i}".
[c-free] (with [c-cut]; Lemma W step 2's "free" claim).
  C.2 admissibility, lines 3966–3969: "Σ_k's determined coordinates
  are exactly its floor downset {(b, l) : ht(b, l) ≤ F_k(b)} plus
  DIG_k's lead level sets (rim blocks, at the history's read values)."
  Complement = free: coordinates strictly above the floor at interior
  indices are free on Σ_k — Lemma W's demands sit exactly there.
[c-floor] (pass-1 finding 9 — "floor = old staircase, LST(ii)").
  LST(ii), lines 3657–3659: "FLOOR CONSTANCY ON THE INTERIOR: on the
  factor interior — where all fresh content lives (C.1's rim bullet) —
  F_i(b) = old_i(slot(b)): ht-constant on each current block".
[c-term] (pass-1 finding 10 — "any admissible terminal system").
  C.3, lines 4015–4017: "COVERED: every lift-carrying classifier
  history (root; increments at any (e, h, g, μ, a); recenterings at
  e_read = 1 with recorded lifts; any interleaving and depth), any
  admissible terminal system." It confirms verdicts are a PARAMETER of
  §C, never a list — the basis of D4R.0-K(c)'s "underdetermined".
[c-perpath] (pass-1 finding 11 — "Theorem C is per-path").
  C.0, line 3436: "A read history H = (ν₀, ν₁, …, ν_k)"; lines
  3451–3452: "Theorem C applies to each lift-carrying history
  separately." And §D4-R's own rev-6 reading, lines 4513–4517:
  "accepted §C proves Theorem C for SINGLE-BRANCH lift-carrying
  histories only (C.0: 'a read history H = (ν₀, ν₁, …, ν_k)', one ψᵢ
  per node; 'Theorem C applies to each lift-carrying history
  separately'; the (ZC) state cylinder is per-chain)".
[c-hull] (rev-2 grammar G4 / Lemma E ¬G4 — the ordering convention).
  §B2-DEF D.4, lines 2240–2243: "CONVEXITY, displayed: on the lower
  hull of the child polygon over [0, μ], the side ENDING at the vertex
  μ is itself such a chord, so its slope exceeds w(Φ̂); the hull's
  descent slopes strictly increase leftward, so every side over the
  continuing window is steeper still."
[c-rs] (rev-2 B5's package facts).
  - D.4, lines 2245–2248: "AFTER A RECENTERING (D.10): all in the
    frame's single side valuation v = v' (one scale — B2⁗.2's typing):
    the recentered key's weight equals the consumed side's value, and
    the RS-landing box gives the same chord inequality and the same
    convexity step in the primed frame."
  - D.10 TRANS-RS, lines 2668–2677, items: "S1: same valuation
    (v = v')" … "S6: the same 𝒜 and realizers. The next read in the
    primed frame has a full stage."
  - D.9(d), lines 2586–2588: "Inside a RECENTERED frame the
    coefficient space and weight are unchanged (D.10: v = v'), and
    subsequent side values only grow (convexity within the frame +
    (I-aug)); so (d) persists along every history."
[c-sae] (rev-3 (SAE) wiring — Theorem B(ii), Lemma W G6, Lemma E ¬G6).
  §C C.0 rev 12, lines 3523–3531 as read 2026-07-27 (drift caveat as
  above): "(SAE) SPAN-ENTRY INEQUALITY [rev 12 — the third condition]:
  the read side lies strictly above the old box line at every span
  slot below the window vertex, and matches it at the vertex when the
  span reaches it: new(j) > old(j) for every span slot j ∈ [s₀', j*],
  j < μ_i; new(μ_i) = old(μ_i) when j* = μ_i (adjacent)." Rev 13's
  appended-read clause, lines 3546–3550: "a read ν_{i+1} appended to a
  prefix (ν₀, …, ν_i) is TRANSITION-ADMISSIBLE iff the extended prefix
  through ν_{i+1} satisfies the three data conditions (NA)+(HV)+(SAE)
  at the appended read ν_{i+1}". §D4-R's own binding, lines 4714–4715:
  realizability "read throughout this note as (NA) + (HV) + (SAE)".
[c-vp] (rev-3 (c1)–(c3) alignment — S2.6's discharging instance).
  ASSEMBLY_PLAN_2026-07-26.md §4t (rev 9), "VP (THE VERDICT PIN — the
  assembly-side definition discharging D4R.0-K(c); cites
  D4R0K_DERIVATION_2026-07-26.md §S2.6, clauses (c1)–(c3))": VP-1 (the
  alphabet — finite multisets of (E, F) pairs, Σ E·F = cluster
  degree); VP-2 (τ — "(τ-irr)/(τ-ns)/(τ-hen)", "a function of CELL
  data alone, never of f", root Hensel leaves "pinned IN scope",
  T_can^τ pruning resolving the leaf-rule refutation); VP-3 (proof
  duties: "(c2) EXACTLY-ONE-VERDICT", "(c3) compatibility", VP-SOUND;
  refuters: the PARI-oracle layers).

## S6. REV 2 RECORD (2026-07-26 — repairs to D4R0K_PASS1's verdict)

Pass 1 (D4R0K_PASS1_2026-07-26.md): UNSOUND — 3 critical, 2 gaps, 6
cite-unchecked. Finding → repair, one line each:

- CRITICAL 1 (Lemma W's grammar missing the hull topology, so
  "grammatical ⟹ realized" false) → Lemma W REBUILT (S2.5): grammar
  G0–G7 adds contiguity/shared vertices (G3), strict convex order
  (G4), right anchor (G5), explicit (NA) (G6, displayed as implied),
  derived-field coherence (G7); the re-proof consumes each topology
  condition at a NAMED step (G3: per-slot well-definedness + the
  above-old-line telescoping; G4: hull = chain + side decomposition;
  G5: no re-pin of the determined vertex coordinate).
- CRITICAL 2 (Lemma E's case list not exhaustive) → Lemma E REBUILT
  (S2.5): one negation clause ¬G_i per grammar conjunct, the bijection
  the identity on indices, completeness BY COMPLEMENTATION (De
  Morgan), each ¬G_i with its displayed emptiness witness (¬G6
  recorded vacuous relative to ¬G3–¬G5).
- CRITICAL 3 (terminal verdicts unpinned, O1 mislabeled non-blocking)
  → ROUTE (b) CHOSEN: the sources genuinely underdetermine the verdict
  function ([c-term]; §B2-DEF has no verdict taxonomy; the
  decomposition note's leaf rule refuted by D4-n3). Theorem B RESTATED
  at structural strength (S2.4 VALUES clause); the residual NAMED as
  D4R.0-K(c) with its exact statement (c1)–(c3) at S2.6; S0.2, S3 O1,
  and S4 now say plainly that the full-verdict form of L5 is NOT
  discharged and that O1/D4R.0-K(c) BLOCKS it.
- GAP 4 (B5's "verbatim" shortcut) → B5 REWRITTEN (S1.4): the
  recentered threshold chain displayed in full with primed indices,
  single AND consecutive recenterings; the rev-1 "= the primed key
  weight" gloss withdrawn — the honest chain keeps ehg and gains the
  strict link λ⁽¹⁾ > ehg ((I-aug) at the recentering read), package
  facts sourced at [c-rs].
- GAP 5 (D4-n3 gate-cell agreement asserted, not displayed) → S2.3b
  ADDED: FC8 quoted verbatim (MOVES 5271–5280) and compared region by
  region; the claim WEAKENED to what is displayed (target-region cells
  ↔ capped 𝒟-values; lumps as capped (z)-lumps; NC outside Σ_{−1}).
- CITE-UNCHECKED 6–11 → S5 CITE REGISTER: every cite now carries the
  exact source sentence from the live MOVES with its line number
  (drift caveat: §C region under concurrent edit — grep the text).

Statement changes beyond repairs: NONE — Theorem A untouched (pass 1:
"essentially established"); Theorem B narrowed, not strengthened;
no new claims added anywhere.

## S7. REV 3 RECORD (2026-07-27 — repairs to D4R0K_PASS2's verdict)

Pass 2 (D4R0K_PASS2_2026-07-26.md): UNSOUND — 2 critical, 4 gaps + 1
wording gap, 0 cite-unchecked; Theorem A adoptable. Finding → repair:

- CRITICAL 1 (shared-vertex digit conflict: two adjacent sides may
  prescribe DISTINCT nonzero digits for the one shared-endpoint
  coefficient; grammatical under rev-2's G0–G7 yet empty; plus G0's
  type omissions) → G3′ ADDED (S2.5): one digit at each shared vertex,
  satisfying both endpoint-nonzero and both G2 memberships; Lemma W
  Step 1 re-walked ("ONE height profile AND ONE digit value per slot",
  G3′ consumed at a named point) and Step 3 re-walked (both tuples
  recovered from the single coefficient); G0 TIGHTENED: nonempty side
  list, w′ > 0, s_min < μ noted as forced.
- CRITICAL 2 (Lemma E exhaustive only against the defective grammar)
  → Lemma E preamble now NINE conjuncts (G3′ inserted), De Morgan
  bijection RE-CHECKED (identity on indices, one clause per conjunct);
  ¬G3′ clause added with a DOUBLE witness (actual data satisfy G3′
  since one coefficient has one digit; violating data are directly
  empty); ¬G6's vacuity bracket precisified per the pass ("impossible
  when G1/G3/G4/G5 hold, can co-occur with their failures").
- GAP (no-side leaf mis-derived as a Lemma-W instance) → leaf T now a
  DIRECT witness (S2.5): the condition set displayed, fresh zeros at
  free coordinates, per-truncation positive mass, compactness run
  directly; explicitly NOT an application of Lemma W.
- GAP ((SAE) not wired into Theorem B's realizability conclusion) →
  Theorem B(ii) statement and proof now derive the FULL rev-12 class
  (NA)+(HV)+(SAE): the (SAE) display via affine interpolation from
  (BOX)/(VERTEX) at hull-vertex endpoints; emitted branches stated
  TRANSITION-ADMISSIBLE (§C rev 13); Lemma W's G6 extended to
  (NA)+(SAE) as derived clauses (Step 2's telescoping IS the grammar-
  side (SAE)); Lemma E's ¬G6 extended to match; new cite [c-sae].
- GAP (empty-prefix/full-box root case asserted, not in the tree) →
  case R0 ADDED as the tree root (S2.4(i)): 𝒟_root = level-0 factor
  multiset + per-opened-track T/R data, componentwise; mixed statuses
  carried by the product datum; (ii)/(iii) extended per track ((SAE)
  etc. per track frame; C.0.5 transport for cap measurability); S2.5
  ROOT LEAVES clause: realized-or-empty per track, the joint witness
  honestly left to MONTES L1's cite (O4 updated) — the one-cluster
  and full-box theorems no longer conflated.
- GAP (D4R.0-K(c)'s (c1)–(c3) not a dischargeable spec; c3 "automatic"
  an overclaim; c1's attachment level ambiguous; c2's domain open) →
  (c1)–(c3) TIGHTENED (S2.6): (c1) verdicts attach to BRANCHES + the
  no-side track halt, cell outcomes derived; (c2) domain CLOSED (root
  Hensel leaves in); (c3) split into (c3-a) partition (automatic) and
  (c3-b) finite-cap detectability (NOT automatic — τ must be a
  STOPPING RULE for the digit filtration; pro-cylinder fibers are the
  obstruction). ALIGNED to the assembly plan's rev-9 VP pin ([c-vp])
  as the discharging instance: VP-1/VP-2 supply (c1)–(c2)'s data,
  VP-3 owes the proofs at note [3t]. DISCREPANCY FLAGGED: the plan's
  VP-3 still glosses (c3) as "automatic given (c1)+(c2)" — this unit's
  (c3-b) says the finite-cap half is not; [3t] must add the
  stopping-rule check for (τ-irr)/(τ-ns)/(τ-hen).
- WORDING GAP (capped outcomes called "FINITE digit cylinders" too
  literally) → B(iii) statement + proof re-worded: the capped digit
  map's fibers are finite PURE cylinders; outcome classes (valuation
  lumps, verdict cells) are finite UNIONS of them; FC8's target cells
  are single cylinders, its V-lumps unions.

Consistency touches: S0.2 and S4 updated to the rev-3 claim set; O1
notes the VP pin; TOC gains S7. Statement changes: Theorem A UNTOUCHED
(adopted per the pass); Theorem B EXTENDED where the pass demanded it
(R0 root case; (SAE) in the realizability conclusion) — both
strengthenings repay defects, neither weakens any prior claim; Lemma
W's grammatical class is strictly NARROWER (G0 tightened, G3′ added) —
the safe direction for a realized-or-empty dichotomy, with Lemma E
widened in exact complement. MOVES untouched.
