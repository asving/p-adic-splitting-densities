# GENIND pass PE1 — HOSTILE VERIFICATION REPORT (fresh context, first arc pass)

**Target:** `lean/notes/openmath/GENIND_PROOF_2026-08-08.md` at HEAD `b49e111`
(file last touched at verdict commit `4984004`; seal `c3212cc`; skeleton `df5f1c9`).
**Role:** hostile verifier. I fix nothing. Every finding quotes the offending
passage and is classified CRITICAL (breaks the logical chain) / GAP
(justification missing, conclusion assumed downstream) / MINOR (display,
scope, or scar; no consequence for a stated theorem).
**Charges:** (1) GENIND-1 five-event completeness — hunt a sixth event;
(2) GENIND-2 α-transport + general bracket, exponent at m = 2..5;
(3) the composite criterion + the n = 5 prime-yet-composite-bearing example;
(4) GENIND.B's IH package — hidden strength?; (5) the [GENIND-H(n)] box's
members vs what GENHN / GENH4 / HE6 / HE7 actually discharged (drift after
five downstream notes); (6) supplier pins at read time. Plus the machine leg
and an independent-arithmetic fresh route.

---

## VERDICT

**UNREFUTED, NOT CLEAN. 0 CRITICAL, 3 GAP, 4 MINOR.** No clause of THEOREM
GENIND.A (I)(II)(IV), no clause of GENIND.C, and no step of GENIND-1/-2/-3/-0/-4
was refuted; every count law I re-derived from scratch came out on the nose,
including two never-independently-derived ones (CS5-V1E2, CS5-V4E2) and the
β-drain composition. The three GAPs are all at the SAME seam — the interface
between GENIND.B's induction and the [GENIND-H] box:

* **PE1-G1** the IH package P(n) has a member (exact-complement (A2)) that
  S6 Step 4 does not re-establish unconditionally, and [GENIND-H]'s three
  members do not ask for it — the strong induction does not close on that
  member at n ≥ 4;
* **PE1-G2** [GENIND-H]'s (CS-1) is stated in a form the note's own §S7.3
  (OB-a) says is not literally achievable (the ragged band), and Step 4
  charges the ragged residue to (CS-1)/(CS-2), which do not mention it;
* **PE1-G3** (CS-2) carries no declared normalization, and the discharger
  (GENH4 §S6.2) proves the genre-F bracket in the OTHER normalization — the
  two displays differ by (q²)^μ.

Grade recommendation: **0/2 stands, arc opened, one clean pass owed after
repair.** The [r1] erratum check (charge item on the header) is **CLEAN**:
see §6.

Machine leg: **REPRODUCED BIT-IDENTICALLY** (§7). Fresh arithmetic route:
**7 independent legs, all EXACT** (§8).

---

## 1. CHARGE 1 — the event grammar (GENIND-1(i)): NO SIXTH EVENT FOUND

I re-derived the classification from the read's own definition rather than
from the note's list. Fix a non-DRAIN state of the cluster system (m, d, N).
Every side of the exact lower hull has strictly negative slope (all a_j ≡ 0
mod π, so every point sits at height ≥ 1 and (m, 0) is the unique lowest
rightmost point); per side of denominator e and residual degree g = ℓ/e the
residual over F_Q factors as Π ψ_i^{μ_i}. Partition the state space by:

* **A.** every μ_i = 1 on every side → **DEC**.
* **B.** some μ_i ≥ 2. Then **exactly one** of
  * **B2.** some repeated factor has e·deg ψ ≥ 2 → **CS**;
  * **B1.** every repeated factor has e·deg ψ = 1 (⟺ ¬B2 inside B) →
    α or β, split by whether the fracture partition is trivial.

B1/B2 is a complemented pair inside B, A/B is a complemented pair, DRAIN
fires first: the five classes are exhaustive and pairwise disjoint. **The
partition claim is correct.**

I then hunted the trivial-partition boundary, which is where a sixth event
would hide, since α is characterized as "the unique case in which the
fracture partition is the trivial partition (m)":

| candidate | e | residual | verdict | class |
|---|---|---|---|---|
| one side, e = 1, (y−z)^m | 1 | (y−z)^m | trivial partition | α ✓ |
| one side, e ≥ 2, (y−z)^{m/e}, m/e ≥ 2 | ≥2 | repeated linear | e·deg ψ = e ≥ 2 | CS ✓ |
| one side, e ≥ 2, m/e = 1 | ≥2 | linear | separable | DEC ✓ |
| one side, e = 1, ψ^μ, deg ψ ≥ 2, μ ≥ 2 | 1 | ψ^μ | e·deg ψ ≥ 2 | CS ✓ |
| one side, e = 1, ψ, μ = 1 | 1 | irreducible | separable | DEC ✓ |
| a₁ = … = a_{m−1} = 0, m ∤ v(a₀) | – | ≥ 2 sides | some repeated / not | β/DEC/CS ✓ |

No case escapes. **No sixth event exists at the stated granularity.**

Two sub-claims inside the proof that I checked and that HOLD, both of which a
hostile reader should expect to break and which do not:

**(a) small-characteristic pin degeneration (the note's "degenerating but
never merging", J-D0's blindness).** The α pins are
digit_{(m−j)k}(a_j) = C(m,j)(−z)^{m−j}. Some of these are ≡ 0 mod p, so the
corresponding lattice point leaves the polygon — but the digit is still
DETERMINED (to 0), so the slot count Q^{Σ_j (N−1−(m−j)k)} is unchanged, and
the residual is still exactly (y−z)^m. The letter map remains injective:
with S := {i ∈ [1,m] : C(m,i) ≢ 0 mod p}, the pin tuple determines
(z^i)_{i∈S}, and the smallest element of S is p^{t₀} (t₀ = lowest nonzero
base-p digit position of m, by Lucas), so gcd(S) is a power of p, hence
coprime to Q−1 and z ↦ (z^i)_{i∈S} is injective on F_Q^×. **The (Q−1)
letter factor is right in every characteristic.** Machine corroboration is
strong here: at (q, N, m) = (2, 6, 4), char 2 kills ALL THREE interior pins
(C(4,1) = C(4,3) = 4 ≡ 0, C(4,2) = 6 ≡ 0) and the measured ALPHA(1) = 1,024
= (q−1)q^{4(N−1)−10k} exactly (§8 leg 5).

**(b) the ghost-zone / consulted-height pairing ([r1 F1] generalized).** The
displayed identity m(N−jk) − (m−j)(N−1) = j(N−1−mk) + m ≥ m > 0 is correct
as written. The consulted-height side is also correct and I checked the one
place it could be tight: the reader never needs a digit strictly above the
chord height, because a point above the chord from (0, v(a₀)) to (m, 0)
cannot affect the lower hull, so reading a_j up to ⌊(m−j)v(a₀)/m⌋ suffices.
The slack is (N−jk) − (m−j)(N−1)/m = [j(N−1−mk)+m]/m ≥ 1, with equality only
at mk = N−1 — and that case is vacuous (the whole α(k) slice has
v(a₀) ≥ mk+1 = N along the chain, i.e. drains at the next step; I verified
#D_k = Q^{k·c(m)} = the ghost fiber exactly there, so the reduced system is
the single window-1 state). **No leak.**

Also checked and coherent: the triangular recentering update is
window-compatible — a′_i = Σ_{j≥i} C(j,i)(−s)^{j−i}a_j + C(m,i)(−s)^{m−i}
needs a_j only mod π^{N−ik−(j−i)(k+1)}, and
N−ik−(j−i)(k+1) ≤ N−jk ⟺ 0 ≤ j−i. Ghost digits provably cannot contaminate
consulted windows.

## 2. CHARGE 2 — α-transport and the general bracket: CORRECT

**Exponent coefficient c(m)+1 = m(m−1)/2 + 1 at m = 2, 3, 4, 5 = 2, 4, 7, 11.**
Committed table (S3 "Instances", GENIND.A(II), S11 P-7): 2/4/7/11.
**MATCH.**

**The bracket, re-derived.** A₁(x) = Σ_{k≥1}(Q−1)Q^{ck}x^k =
(Q−1)Q^c x/(1−Q^c x); 1 − A₁ = (1 − Q^{c+1}x)/(1−Q^c x); hence
A₁/(1−A₁) = (Q−1)Q^c x/(1 − Q^{c+1}x), whose x^μ coefficient is
(Q−1)Q^{c+(c+1)(μ−1)} = (Q−1)Q^{(c+1)μ−1}. **MATCH.** Spot-checked by hand
at μ = 1 ((Q−1)Q^c) and μ = 2 (compositions (2) and (1,1):
(Q−1)Q^{2c}(1+Q−1) = (Q−1)Q^{2c+1}). **MATCH.**

**The counting spine of GENIND-2(a) closes exactly.** Σ_{j<m}(N−1−(m−j)k) =
m(N−1) − k·m(m+1)/2 (α-locus exponent, and #D_k); ghost slots
Σ_{j<m} jk = k·m(m−1)/2 = k·c(m); and
m(N−mk−1) + k·c(m) = m(N−1) − k·m(m+1)/2, i.e.
(window-(N−mk) state count) × (ghost fiber) = #D_k **identically**. So
GENIND-1(ii)'s bijection and GENIND-2(a)'s fiber size are mutually forced,
not independently guessed. The ghost zone {≥ N − jk} at abscissa j is
exactly right (a_j/π^{(m−j)k} is known mod π^{N−(m−j)k}, truncated to
mod π^{N−mk}, losing jk digits, i.e. a_j's digits at heights N−jk .. N−1).

**MINOR PE1-M1 (unstated side condition on the bracket).** GENIND.A(II) and
GENIND-2(b) display b_{m,d}(μ) as a sum "over all finite sequences
(k₁,…,k_r), k_i ≥ 1, Σk_i = μ" with no window condition. The step
admissibility is m·k_i ≤ (window at that step) − 1, whose conjunction over
the chain is exactly mμ ≤ N−1; so the unrestricted sum is the correct
aggregate **iff mμ ≤ N−1**, which the note never says. Harmless (the
constraint is implied by the α-prefix being realized) but the display is
under-hypothesized. Class: MINOR.

## 3. CHARGE 3 — the composite criterion: CORRECT, AND THE GRAMMAR IS COMPLETE

**Necessity, re-derived.** CS ⟹ ∃ repeated (ψ, μ) with μ ≥ 2 and
e·deg ψ ≥ 2 ⟹ e·μ·deg ψ ≥ 2·2 = 4 (the note's case split into
(e ≥ 2, deg ψ = 1) and (e = 1, deg ψ ≥ 2) is exhaustive but the one-line
"product of two factors each ≥ 2" argument covers it, including
e ≥ 2 ∧ deg ψ ≥ 2 where the bound is 8). The side's abscissa length is
e·g ≥ e·μ·deg ψ, and the polygon spans [0, m], so m ≥ 4; with mD ≤ n,
n ≥ 4D ≥ 4. Multiplicity monotonicity (α preserves m; β gives μ_l < m; CS
gives μ ≤ m/(e·deg ψ) ≤ m/2) closes n ≤ 3. **MATCH.**

**The n = 5 example.** I re-derived CS5-V1E2(h) from scratch: side
(1, 2h)–(5, 0), length 4, drop 2h, slope h/2 with h odd so e = 2, lattice
points at j odd ∈ {1, 3, 5}, residual quadratic (y−z)² with
digit_{2h}(a₁) = z², digit_h(a₃) = −2z; off-lattice budgets
v(a₂) ≥ (3h+1)/2, v(a₄) ≥ (h+1)/2; convexity at the abscissa-1 vertex forces
v(a₀) > 5h/2 i.e. ≥ (5h+1)/2, and non-DRAIN forces a₀ ≠ 0. Free-digit total
(N−(h+1)/2) + (N−1−h) + (N−(3h+1)/2) + (N−1−2h) = 4N − 5h − 3, and the a₀
headroom contributes q^{N−(5h+1)/2} − 1. Hence

    CS5-V1E2(h) = (q−1)·q^{4N−5h−3}·(q^{N−(5h+1)/2} − 1)

**MATCH** with S5.3 (including the intermediate display
4N − 2 − 3h − (4h+2)/2). Since e = 2, deg ψ = 1, μ = 2 gives
e·μ·deg ψ = 4 ≤ 5 = m, n = 5 (prime) genuinely bears a composite stage,
with the fifth root splitting off on the length-1 side (residual degree 1,
always separable). **The "d·e-factorization" criterion is indeed refuted.**

**CS5-V4E2 re-derived independently** (this law is derivation-only in
GENIND — no roster window reaches it — so it deserved the harder look):
left side (0, v₄+2h)–(4, v₄), e = 2, lattice points j even ∈ {0, 2, 4},
right side (4, v₄)–(5, 0) of length 1; two letters (the vertex unit c₂ ∈ F_q^×
and z ∈ F_q^×, with z ≠ 0 forced because (0, v₄+2h) is a hull vertex);
budgets v(a₃) ≥ v₄+(h+1)/2, v(a₁) ≥ v₄+(3h+1)/2, pins at heights v₄, v₄+h,
v₄+2h. Free-digit total
(N−1−v₄) + (N−v₄−(h+1)/2) + (N−1−v₄−h) + (N−v₄−(3h+1)/2) + (N−1−v₄−2h)
= 5N − 5v₄ − 5h − 4. Hence **(q−1)²q^{5N−5v₄−5h−4}** — **MATCH**. Vertex
condition: lower-hull convexity at (4, v₄) needs left slope magnitude
h/2 > right magnitude v₄, i.e. h > 2v₄, i.e. h ≥ 2v₄+1 (h odd) — **MATCH**,
and visibility v₄+2h ≤ N−1 with v₄ ≥ 1, h ≥ 3 gives N ≥ 8 — **MATCH**
("first visible at N = 8"). The smoke-run RED that produced this condition
was a genuine math-side correction, correctly folded.

**Grammar completeness at depth 0, n = 4 and n = 5 — re-enumerated
independently.** A CS side needs length ≥ 4 and e | length.

* m = 4: only length 4 = the full side; e ∈ {1, 2, 4}; e = 4 ⟹ g = 1,
  μ = 1, not CS; e = 2 ⟹ g = 2 ⟹ CS iff residual = (y−z)² = **CS4-E**;
  e = 1 ⟹ g = 4 ⟹ CS iff the repeated factor has deg ψ ≥ 2, i.e.
  residual = ψ², deg ψ = 2 = **CS4-F**. **Exactly the note's two genres.**
* m = 5: CS side of length 4 spanning [1,5] gives {e = 2, (y−z)²} =
  **V1E2** and {e = 1, ψ²} = **V1E1-(2²)**; length 4 spanning [0,4] gives
  **V4E2** and **V4E1-(2²)**; length 5 (e ∈ {1,5}; e = 5 ⟹ μ = 1) gives
  e = 1, g = 5, deg ψ·μ ≤ 5 with deg ψ ≥ 2, μ ≥ 2 ⟹ (2,2) with a leftover
  linear = **FULL-(2²1)**. At most two sides are possible (4+1 or 5).
  **Exactly the note's five genres, no sixth.**

Visibility floors also re-derived and matching: V1E1-(2²) at
(1,4k)–(5,0) needs v(a₀) ≥ 5k+1 ≤ N−1, first visible **N = 7** (note: N = 7
✓); FULL-(2²1) needs 5k ≤ N−1, **N ≥ 6** (note: N ≥ 6 ✓); V4E1-(2²) needs
k > v₄ ≥ 1 so k ≥ 2 and v₄+4k ≤ N−1, first visible N = 10 (note gives no
floor, consistent with "beyond this roster's windows").

**MINOR PE1-M2 (the sufficiency padding is false as written at small q).**
S5.1 *Sufficiency*: "at n > 4 pad with n−4 distinct simple roots at level 0
(Hensel product, W12-S2.1)". Over F_2 the only monic linears are x and x+1,
and x is taken by the cluster, so there is no such padding for n−4 ≥ 2
(first failure n = 6, q = 2). The claim survives verbatim by padding with a
SINGLE irreducible of degree n−4 (which exists over every F_q), or with the
S5.3 embedded genres as the same sentence offers; only the displayed
realization is wrong. Class: MINOR.

**MINOR PE1-M3 (CS4-E displayed without its visibility floor).** S5.1's
sufficiency and S5.3's CS4-E line display "(q−1)·q^{4N−5h−3}" with no
condition, while every sibling law in the same subsection displays its floor
(V1E2's headroom, V4E2's vertex condition + N ≥ 8). At (N, h) = (2, 1) the
displayed law returns q−1 whereas the true locus is 0 (v(a₀) = 2h = 2 ≥ N,
so DRAIN fires first). The runner is correct (`while 2*h <= N-1`), so this is
display-only. Class: MINOR.

## 4. CHARGE 4 — GENIND.B's IH package: **NOT** exactly (hMenu-k)+(hExhaust-k)

Quoted, S1:

> Define the package P(k) := {history-resolved exact menu (HM3.A-form) +
> finite (A1)-admissible aggregate menu + (A0) + exact-complement (A2)} for
> the degree-k problem.

and, S0:

> **W-12.D** … Its per-degree hypothesis package {(A0), (A1), (A2)} is what
> (hMenu-n)+(hExhaust-n) abbreviate throughout.

So P(k) = (hMenu-k)+(hExhaust-k) **plus two extra strengths**:
(i) history-resolution of the menu, and (ii) exact-complement rather than
merely vanishing (A2). Strength (i) is DISCLOSED (S0's third bullet:
"aggregate menus do not suffice: β-children enter at their own refine loci")
and is re-established by Step 2 ("This is (hMenu-n) = (A1) + the
history-resolved form of P(n)"), so it is honest extra strength, not hidden.
Strength (ii) is where the induction leaks:

### **PE1-G1 [GAP] — Step 4 does not re-establish P(n)'s exact-complement member, and [GENIND-H] does not ask for it.**

Quoted, S6 Step 4:

> Summing: r(N)/q^{nN} → 0, with the same exact-complement sharpening
> HM3.C S5.3 achieved at n = 3 **wherever the stage laws are exact**.

and [GENIND-H(n)]'s three members ((CS-1) transport, (CS-2) bracket,
(CS-3) = (H-e)) contain **no exactness clause anywhere**. Therefore the
displayed implication "(IH) + [GENIND-H(n)] ⟹ P(n)" is not established for
P(n)'s fourth member at n ≥ 4: the antecedent as written admits stage laws
that give only a bound, and then P(n) fails while [GENIND-H(n)] holds.

This is load-bearing, not pedantic, because the induction CONSUMES the
exactness at the next degree. S5.2's drainage bullet:

> Σ_{β-genres} (route prefactor)·[children: at least one drains,
> inclusion–exclusion over the child systems' u's and totals]

is an identity only if the children's u's are exact; and it is exactly this
mechanism that the battery certifies (S11 P-4 / GT-BDRAIN: "the n = 4
FULL-side beta drain laws confirmed in closed form CONSUMING the proved
n ≤ 3 drains"). Failure scenario: let [GENIND-H(4)] hold with the (2,2)
stage drain given as an asymptotic bound rather than a closed form. Then
P(4)'s exact-complement member fails; the n = 8 instance of Step 2/Step 4,
which fractures into a degree-4 child, loses the exact first-step recursion
and can only assert a bound — so P(8) fails too, and the strong induction
does not propagate the member it assumed. Repair options (verifier does not
choose): add a fourth box member (stage drainage is an exact q-power family
per stratum), or weaken P(k)'s member 4 to plain (A2) and delete the exact
β-drain composition from the inductive step.

De facto the downstream discharger already supplies exactness (GENH4
THEOREM GENH4.B / Q22-L3: "UND = … one exact q-power per stratum"), so this
is a statement-level hole in GENIND's own box, not a live mathematical
error. Class: **GAP**.

Two further IH checks that came out CLEAN: (a) Step 1's extraction of a
cluster system (m_i, d_i) with m_i d_i = k < n from P(k) is legitimate
because P(k) is history-resolved and level-0 configuration is part of the
history; (b) the base cases are genuinely needed only for bookkeeping —
Step 2 at n = 2 consumes no IH (children of a (2, 1) fracture have μ_l = 1).

## 5. CHARGE 5 — the [GENIND-H(n)] box vs the dischargers: TWO DRIFTS

Dischargers read at HEAD: **GENH4** (`GENH4_PROOF_2026-08-08.md`,
"[GENIND-H(4)] DISCHARGED AT BOTH QUARTIC GENRES … OB-a/OB-b/OB-c/OB-d all
closed"; COROLLARY GENH4.D: "CS-1 = GENIND-4 + GENH4-1F + GENH4-2/-3/-4;
CS-2 = the stage bracket, proved in S6.2 …; CS-3 = THEOREM GENH4.C") and
**GENHN** (`GENHN_PROOF_2026-08-08.md`, THEOREM GENHN.B: "(CS-1) and (CS-2)
hold … and (CS-3) holds at every μ = 2 genre … The ONLY unproved clause
anywhere in [GENIND-H(n)], for every n, is [GENHN-HE(μ)], μ ≥ 3").
**Member NAMES and COUNT match exactly — no renaming drift, no silent
member addition or deletion.** HE6/HE7/HE6R1 do not consume [GENIND-H]'s
members (they consume GENHN-2 and HE3-0; see R9's own consumption check),
so they cannot drift against GENIND. Two content drifts remain:

### **PE1-G2 [GAP] — (CS-1) is stated in a form GENIND's own §S7.3 says is unachievable, and Step 4 charges the ragged residue to it.**

(CS-1), S7.1:

> the stage read (polygon, residuals over K, refine events) is
> count-isomorphic to a degree-m′ cluster-system read over K at an explicit
> stage window.

GENIND-5, S7.3, about the very first instance of that stage:

> the PARITY-RAGGED window (even slots end at dv = 2N−2, odd at 2N+h−2;
> uniform statements hold below dv = 2N−2, **the ragged band routes through
> (A2) as a boundary family**)

and (OB-a) names the un-written ledger. The discharger agrees the
qualification is needed: GENHN.A(v) says "the stage read IS the (μ, K)-cluster
read in dv-units at the S-node, **ragged-window-corrected**". So (CS-1) as a
box member is stated WITHOUT the correction its own note says is required,
and — the consequential half — GENIND.B Step 4 accounts for the residue by
assumption:

> the CS-internal part: (CS-1)+(CS-2) resolve each stage into its own
> decided menu + drain

with no ragged/boundary family in the list. Failure scenario: a stage genre
whose ragged band carries non-vanishing normalized mass satisfies
(CS-1)+(CS-2)+(CS-3) under the "count-isomorphic below the ragged threshold"
reading that GENHN actually proves, while breaking P(n)'s (A2) at degree n —
because nothing in the box or in Step 4 obliges anyone to bound that band.
Repair: state (CS-1) with the ragged correction and add the band explicitly
to Step 4's (A2) inventory (where the tail families already live). Class:
**GAP**.

### **PE1-G3 [GAP] — (CS-2) carries no declared normalization; the discharger's genre-F bracket differs from GENIND's F-instantiation by (q²)^μ.**

(CS-2), S7.1: b_{m′,K}(μ″) = (|K|−1)·|K|^{(c(m′)+1)μ″−1}. Instantiating at
the f-first quartic genre (m′ = 2, e₁ = 1, f₁ = 2, |K| = q²) gives
**(q²−1)(q²)^{2μ−1}**. GENH4 §S6.2, the cited discharge of (CS-2), proves

> genre F: (q²−1)(q²)^{μ−1}

— smaller by exactly (q²)^μ. The reconciliation exists but lives in a THIRD
note, GENHN §S6.2:

> GENIND's bracket is mass-normalized (it includes the ghost fiber
> |K|^{c(μ)κ} of the α-transport), GENH4's ladder telescoping (q−1)q^{δ−1}
> is the letter-sum with per-node laws carrying the floors; they compose as
> (|K|−1)|K|^{2κ−1} = |K|^{κ} · (|K|−1)|K|^{κ−1} (ghost × letters)

I verified the two are consistent under that split (at genre E, e₁ = 2, the
ladder has δ = 2μ integer dv-points so GENH4's (q−1)q^{δ−1} coincides
numerically with GENIND's display, which is why the mismatch is INVISIBLE at
the E genre and only surfaces at F). But GENIND itself never declares the
normalization, and its own justification —

> the (CS-2) instance — same exponent coefficient c(2)+1 = 2 as the order-1
> quadratic cluster, because W-9's dim = E already flattened the stage
> lattice to one slot per unit height

— reads as a letter-aggregation statement. Failure scenario: a discharger
proves the letters-only law at genre F (exactly what GENH4 §S6.2 displays),
cites it as "(CS-2)", and Step 2's aggregation then consumes the
mass-normalized value — a (q²)^μ over-count of the CS-stage menu mass at
every f-first genre. No mathematical contradiction was found; the defect is
that the box member is not pinned tightly enough to make its discharge
checkable from GENIND alone. Class: **GAP** (drift, resolvable by one
declared sentence).

Non-drifts I checked and clear: (CS-1)'s slot claim "ONE K-digit slot per
(abscissa, v′-height)" is f₁-correct at all (e, f) — A_j has D′ = e·d·deg ψ
coefficients over [K : F_q] = d·deg ψ, i.e. e K-digits per window unit
against a v′-height range of e·N, so one K-digit per v′-unit; GENHN-T's
tower criterion (μ ≥ 4 ⟺ n ≥ 8) is GENIND.A(IV) applied inside a stage with
outer key degree e₁f₁ ≥ 2 (4·2 = 8) — consistent; (CS-3)'s discharge status
(μ = 2 proved by GENHN.C, μ ≥ 3 boxed as [GENHN-HE]) is consistent with
GENIND's box being declared OPEN.

## 6. THE [r1] ERRATUM (HE6R1's R9, GENHN-adjacent): LANDED COHERENTLY

R9 (HE6R1_RECON §S1) corrects GENHN-1's stage-initial node to
**{dv(A_j) ≥ (μ−j)·D′h + 1}, D′h = f₁S**, applied to GENHN as a dated `[r1]`
annex (GENHN §S6/line 387). Consumption check against GENIND:

* GENIND's ONLY node display is LEMMA GENIND-4's
  **{dv(A₀) ≥ 2S+1, dv(A₁) ≥ S+1}, S := 2h** at the (2,2)-E stage, where
  f₁ = 1 and hence D′h = S. The corrected general form at μ = 2, f₁ = 1 is
  {dv(A_j) ≥ (2−j)S+1} = {dv(A₀) ≥ 2S+1, dv(A₁) ≥ S+1}. **IDENTICAL.**
* I re-derived GENIND-4's node from its own budgets rather than accepting it:
  with dv(ax+b) = min(2v(a)+h, 2v(b)), dv(A₁) ≥ min((h+1)+h, 2h+2) = 2h+1 =
  S+1 and dv(A₀) ≥ min((3h+1)+h, 4h+2) = 4h+1 = 2S+1. **MATCH.**
* GENIND's general work order (S7.4) displays NO node height (it says only
  "expected budgets = the entry law's exponent, the E parities/residues mod E
  separating slots"), and GENIND has no f₁ ≥ 2 node display anywhere, so R9's
  named residue GENHN-ERR-1 (f₁ ≥ 2 count-side displays substituting S for
  f₁S) has **no GENIND-side counterpart**.

**No GENIND erratum is owed from R9.** Clean.

## 7. MACHINE LEG — REPRODUCED BIT-IDENTICALLY

* **Runner md5 vs seal:** `verification/openmath/genind_checks.py` =
  `e7ca150b1b5cb13ad4f3350ac776aca2` at the worktree, at HEAD `b49e111`,
  and at the seal `c3212cc` — all three identical. S11's "runner
  byte-identical to the sealed commit c3212cc" **CONFIRMED**.
* **Supplier pins at my read time (charge 6):** all five GT-PIN files match
  their pinned md5 (`w11_checks.py` 500aae15…, `w12_checks.py` 7dc040d9…,
  `hex3_checks.py` 83faf7ed…, `hmenu3_checks.py` 65326f85…,
  `hex3_checks_results.json` ce6f4116…), and all are clean in `git status`.
  All 18 commit-hash pins named in §S9.3 (+ the ledger pin 66057f4) resolve
  to real commits. **0/5 pin violations, 18/18 hashes live.**
* **Fresh run** in an isolated sandbox (`/tmp/genind_pe1_run`, runner +
  the five pinned suppliers copied, so the committed artifacts were never
  touched), system python3.10 with `~/.local/lib/python3.10/site-packages`
  supplying cypari2 2.2.0:

      VERDICT: GREEN — 163536 checks, 0 violations, 164.6 s
      GT-PIN 5/0  GT-PART 33/0  GT-DEPTH0 108/0  GT-BDRAIN 4/0
      GT-ALPHA 2474/0  GT-BETA 87156/0  GT-RECUR 8/0  GT-BRACKETID 24/0
      GT-CRIT 22/0  GT-N3TIE 16/0  GT-CONS 10/0  GT-ORACLE 73676/0
      GT-T-ALPHA 12/12  GT-T-CS 12/12  GT-T-CRIT 4/4  GT-T-BRACKET 24/24

  Counts, per-family split, and all four teeth agree with §S11 exactly
  (163,536 / 0 / 12-12-4-24). `genind_checks_results.json` from my run is
  **equal to the committed JSON key-for-key modulo the single `elapsed_s`
  field** (164.6 vs 164.5); the output text differs on **6 lines, all
  timing** (two per-row seconds, one total). Verdict GREEN ⟹ exit 0.
* **Instrument audit (not just re-run).** The three checks a hostile pass
  should suspect of vacuity are real: `depth0_pred` gates every law by its
  own visibility (`m*k <= N-1` for α; `2*h <= N-1` for E4/V1E2 with the
  extra `head >= 1`; `4*k <= N-1` for F4/B*; `h >= 2*v4+1` and
  `v4+2h <= N-1` for V4E2), the both-directions loop flags an unpredicted
  key of any predicted class as a GT-DEPTH0 violation and an unlisted CS
  genre (`CSOTHER`) as a GT-CRIT violation, and GT-CRIT tests
  `mu >= 2 and e*gam >= 2 and 4 <= e*mu*gam <= fm` on every recorded CS
  event at every depth (so a single e·μ·γ < 4 event would kill the
  criterion). **Disclosed limitation I confirmed:** multi-side β genres are
  tallied under a catch-all `BOTHER` key that is NOT law-checked in
  GT-DEPTH0 (only the four n = 4 FULL-side genres have laws); their
  compensating instrument is GT-BETA's pointwise Hensel leg
  (87,156 reconstructions, 0 bad). This matches GENIND-BOX-2's own framing
  and is not a hidden claim.

## 8. FRESH ARITHMETIC ROUTE — MY OWN NUMBERS, 7 LEGS, ALL EXACT

Every number below was computed from my own re-derivation (§2, §3), then
compared against the committed prediction/verdict; none was read off the
note first.

| leg | quantity | my value | committed |
|---|---|---|---|
| 1 | CS5-V1E2(1) at (q,N,m) = (2,5,5): 1·2^{20−5−3}(2^{5−3}−1) | 4096·3 = **12,288** | 12,288 (P-3/S11) |
| 2 | **β-drain closed form** B2Q(1) at (2,6,4): locus (q−1)(q(q−1)/2)q^{4N−10k−4} = 2^{10}; drained c·q^{6k}·q^{2(M−1)}·R(M), M = 2, R(2) = q^{M−1} = 2 → 1·64·4·2 | **512 of 1,024** | 512/1,024 (P-4) |
| 3 | E4(1) at (2,6,4) = 1·2^{24−5−3}; F4(1) = 1·2^{24−10−4}; row CS total | **65,536; 1,024; 66,560** | 65,536; 1,024; 66,560 |
| 4 | DRAIN₀ = q^{(m−1)(N−1)} at (2,6,4) / (3,4,4) / (2,5,5) / (3,3,5) | **32,768; 19,683; 65,536; 6,561** | same (P-3) |
| 5 | ALPHA(1) at (2,6,4) = (q−1)q^{4(N−1)−10} — the char-2 all-pins-degenerate case | **1,024** | 1,024 (P-3) |
| 6 | E4(1) at (3,4,4) = 2·3^{16−5−3}; at (5,3,4) = 4·5^{12−5−3} | **13,122; 2,500** | 13,122; 2,500 |
| 7 | (3,3,5): V1E2 headroom N−(5h+1)/2 = 0 at h = 1, all other n = 5 genres first visible at N ≥ 6 ⟹ CS locus | **0** | "ZERO CS keys" (P-3) |

Two more legs done symbolically rather than numerically, both matching:
the **BOTHER genre at (2,4,4)** — polygon (0,3)–(2,1)–(4,0), char-2 residual
(y+1)² forcing v(a₁) ≥ 3, giving 1·2·4·8 = **64** against the committed
`depth0` entry 64 (and all 64 drain, consistent with a child window M = 1) —
and the **B22/B31/B211/B2Q mass identity** c·q^{6k}·q^{4(M−1)} =
c·q^{4N−10k−4}, which forces the ghost exponent 6k = k·c(4) and hence ties
the four drain closed forms to GENIND-2(a)'s ghost count. Also verified
independently: the four B-genre letter prefactors ((q−1)(q−2)/2,
(q−1)(q−2), (q−1)(q−2)(q−3)/2, (q−1)·q(q−1)/2) are exactly the counts of
monic degree-4 residuals with nonzero constant term of shapes (2²), (31),
(21²), (2·Q).

## 9. FINDINGS TABLE

| id | class | site | one line |
|---|---|---|---|
| PE1-G1 | GAP | S1 P(k) def / S6 Step 4 / S7.1 box | P(n)'s exact-complement (A2) member is consumed by the induction but re-established only "wherever the stage laws are exact"; [GENIND-H] has no exactness clause |
| PE1-G2 | GAP | S7.1 (CS-1) / S6 Step 4 / S7.3 OB-a | (CS-1) is stated without the ragged-window correction its own OB-a and the discharger GENHN.A(v) require, and Step 4's (A2) inventory omits the ragged band |
| PE1-G3 | GAP | S7.1 (CS-2) | no normalization declared; GENIND's genre-F instantiation (q²−1)(q²)^{2μ−1} vs the discharger GENH4 §S6.2's (q²−1)(q²)^{μ−1} — a (q²)^μ gap resolved only in a third note |
| PE1-M1 | MINOR | GENIND.A(II), GENIND-2(b) | bracket displayed with no window condition; the sum is the correct aggregate only for mμ ≤ N−1 |
| PE1-M2 | MINOR | S5.1 Sufficiency | "pad with n−4 distinct simple roots" is impossible over F_2 for n ≥ 6; repairable by one degree-(n−4) irreducible |
| PE1-M3 | MINOR | S5.1 / S5.3 CS4-E | CS4-E's locus displayed without its visibility floor 2h ≤ N−1, unlike every sibling law (runner is correct) |
| PE1-M4 | MINOR | S7.2 GENIND-4 | editing scar in a load-bearing proof line: "= 2h+1 = S+... = 2h+1"; and the preamble's "(q−1)q^{4N−5h−3} members" mis-scopes the (h,z)-slice count by (q−1) |

## 10. WHAT SURVIVED (for the repair round's benefit)

Unrefuted and independently re-derived: GENIND-1(i) (the partition, both
characteristics, including the small-p pin degeneration and the letter-map
injectivity), GENIND-1(ii) (the D_k bijection, forced by the slot identity),
GENIND-2(a) (ghost zone {≥ N−jk}, fiber Q^{k·c(m)}, the triangular update's
window compatibility, the [r1 F1] pairing including its one tight case,
which is vacuous), GENIND-2(b) (the bracket and its 2/4/7/11 exponents),
GENIND.A(IV) both directions, S5.3's five n = 5 and two n = 4 depth-0 CS
genres AND their completeness AND their visibility floors, GENIND-4 in full
(the four development identities, the four budgets, the free-digit total =
the entry law's exponent, the ℤ/2 dv-parity slot separation, the node), and
the four β-drain closed forms with their mass identity. GENIND.C's statement
is untouched by the findings; GENIND.B's REDUCTION survives with PE1-G1's
member excised or the box extended.

---
*Verifier: fresh-context hostile pass PE1, 2026-08-08. Fixed nothing.
Machine leg re-run in an isolated sandbox; committed artifacts untouched.*
