# W11 passPE1 report — hostile verification of W11_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W11_PROOF_2026-08-08.md` at HEAD (seal 7020ceb,
verdict cb05127). **Role:** hostile verifier, fresh context, fix nothing.
**Verdict: NOT CLEAN — 2 CRITICAL ERRORS + 2 JUSTIFICATION GAPS + 2 MINOR.**
Both critical errors are LOCALIZED display/side-claim errors whose surrounding
conclusions I re-derived true independently; **the theorem's clauses (i)–(iii)
themselves survive this pass intact** (all counts, the drainage law q^N, the
σ-symmetry, the limit sum = 1, and the capstone tie were re-derived from
scratch and confirmed by an independent machine route). Findings trigger
repair per protocol.

---

## 1. FINDINGS

### F1 — CRITICAL ERROR (S2.4): the displayed per-node exhaustiveness identity is false as written (every leg off by a factor of q)

Offending passage (S2.4, verbatim):

>     RAM leg      Σ_{k≥s+1} (1−1/q)·q^(−(3k−1))       = q²·X
>     2SIDED leg   Σ_{w≥s+1} Σ_{u≥2w+1} (1−1/q)²q^(−u−w) = X
>     e=1 leg      Σ_{k≥s+1} q(q−1)·q^(−3k−2)           = q·X
>       (all q(q−1) residual pairs: split + irreducible + refine)
>
> with X = (1−1/q)·q^(−3(s+1))/(1−q^(−3)); total (q² + q + 1)·X =
> q^(−3s−2) = μ_s exactly. ∎(nothing leaks at any node)

With the note's own X (which evaluates to q^(−3s−1)/(q²+q+1)), the three
displayed sums evaluate to **qX, X/q, X** — each displayed value is exactly
q times the true one — and the displayed total equality is false:
(q²+q+1)·X = q^(−3s−1) = **q·μ_s ≠ μ_s**. Numerical check at q = 2, s = 0:
μ₀ = 1/4; true legs 1/7 + 1/28 + 1/14 = 1/4 ✓; displayed legs 2/7 + 1/14 +
1/7 = 1/2 = 2μ₀ ✗. The summands themselves are correct; only the three
evaluated leg values and the final total-vs-μ_s equation carry the spurious q.

**Classification: CRITICAL ERROR** (a chain of false equations inside the
proof of the identity that feeds clause (iii)'s Σ = 1). **Conclusion status:
TRUE.** I re-derived the identity independently: corrected legs qX + X/q + X
= (q²+q+1)X/q = q^(−3s−2) = μ_s exactly. The finite-window version (which is
what the machine census checks) is unaffected — I verified the exact
finite-N per-key counts by an independent route (§3). Repair = divide the
three displayed leg values by q and fix the total line.

### F2 — CRITICAL ERROR (S2.2): the degenerate disc = 0 bullet is false in equal characteristic 2, and its displayed mechanism is wrong even where the conclusion holds

Offending passage (S2.2, verbatim):

> * Degenerate perfect squares (disc = 0): never decided at any window
>   (v(disc) = ∞ forces u = w = ∞ in-window) — measure zero, part of the
>   undecided residue at every N.

(a) **Equal char 2 counterexample:** disc = a₁² there, so disc = 0 ⇎ perfect
square. f = x² + t over F_q[[t]] has disc = 0 identically and is **DECIDED
RAM(1) at every window N ≥ 2** (u = 1 odd, w = ∞; irreducible, e = 2 in the
value-group sense — inseparable). Machine-confirmed with my fresh classifier:
`f=x²+t: leaf = ('RAM', (1,), ())`, disc ≡ 0 at every position. So "never
decided at any window" is FALSE as stated (the bullet carries no
characteristic fence in a note whose banner is "both characteristics").
(b) **Wrong mechanism even in mixed char:** for a true perfect square the
read does NOT see u = w = ∞ in-window; it runs the refine chain with finite
visible u, w and exits at the undecided tail cell (u ≥ N, w > (N−1)/2), with
w = v(2) + u/2 possibly < N and visible. Verified: (x+2)² over Z₂ at N = 8
classifies UNDECIDED with realized refine history (1,2,3), intermediate
reads all at finite (u, w). The correct statement is: a perfect square's
final read lands in the undecided cell because w = v(2) + v(root-offset) >
(N−1)/2 whenever u ≥ N — not because u = w = ∞.

**Blast radius: zero on clauses (i)–(iii).** No count or density consumes
this bullet (x² + t is correctly counted in RAM(1) by note, runner, and my
fresh census alike; the count laws never reference disc). The machine bracket
"W11-ORACLE … checks disc = 0 ⟹ window-undecided" is PARI-side and therefore
mixed-characteristic only (runner computes poldisc of the exact canonical
lift, so "disc = 0" there = exact perfect square, where the claim is true —
0 violations is the correct outcome). W11-BOX-4 discloses the oracle
coverage limit, but the S2.2 bullet itself is stated as unfenced mathematics.

### F3 — JUSTIFICATION GAP (S4.2): deep-inert tail display double-applies the center factor

Offending passage (S4.2, verbatim):

> THIS note's deep-inert tail: Σ_k (q−1)/(2q^(2k+1))·q = 1/(2q(q+1)) = 1/12
> at q = 2.

The summand (q−1)/(2q^(2k+1)) is already the WHOLE-SPACE density (table (i)'s
INERTDEEP(k) row); with the displayed extra "·q" the left side evaluates to
1/(2(q+1)) = 1/6 at q = 2, not 1/12. The intended summand is the per-center
density (q−1)/(2q^(2k+2)). **The right-hand value 1/(2q(q+1)) = 1/12 is
correct** (Σ_k (q−1)/(2q^(2k+1)) = 1/(2q(q+1)) — re-derived), and the
capstone tie 1/4 + 1/12 = 1/3 = q/(2(q+1)) at q = 2 is correct (§2 below).
Display-level slip only.

### F4 — JUSTIFICATION GAP (S5, fencing/honesty): the "p = 2 mixed" qualifier of S2.2's disc spectrum is dropped

Offending passage (S5, verbatim):

> The wild rows are genuinely wild (S2.2: at p = 2 every RAM member has
> v(disc) ∈ {h+1, h+2}, never tame; …)

S2.2 proves the {h+1, h+2} spectrum for **p = 2 mixed** and labels it so; S5
re-states it for blanket "p = 2". In equal characteristic 2, disc = A₁² on a
RAM(h) member gives v(disc) = 2w ∈ {h+1, h+3, h+5, …} ∪ {∞} (x² + t realizes
∞). The "never tame" half survives everywhere (all values ≥ 2 > e−1 = 1),
the displayed spectrum does not. The TAMEDISC tooth is oracle-side (mixed
only), so the machine claim is unaffected. One-word repair ("mixed").

### F5 — MINOR (S1 table): SPLIT-TAIL "absorbed into 2SIDED/SPLITEQ as N → ∞"

Tail members have w < N/2 ≤ u/2, so all their lifts have roots at strictly
distinct valuations: the absorption target is 2SIDED rows only (plus the
measure-zero exact x(x+A₁) locus). SPLITEQ (equal-valuation roots) is
unreachable from the tail. Zero downstream weight (σ-totals unaffected).

### F6 — MINOR (S2.4): "genuinely ambiguous (contains split, inert AND ram lifts)"

True of the undecided residue as a set; per MEMBER, split and inert lifts
always both exist (verified — so σ-undecidedness itself is airtight member by
member), but ram lifts need not: a char-2 member with exact w = N/2 has only
split and inert lifts (residual c₁ ≠ 0 blocks the refine that a ram lift
would need). The parenthetical invites a false per-member reading; the
drainage law's meaning is unaffected.

**Honesty grade:** no overclaim-type defects found. Boxes S6/BOX-1..7,
the conditionality stack S9, the smoke disclosure, and the Lean-side
non-claims (BOX-2/3/5) all check out as stated; F4 is the only fencing slip,
and it is commentary (S5), not the theorem.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

### Charge 1 — completeness of the seven-family menu (re-derived, both characteristics)

Re-derived the full case analysis from the S1 read definition alone. Level 0
partitions q^(2N) exactly into SEP-SPLIT (q(q−1)/2 residue classes), SEP-INERT
(q(q−1)/2), and q double-root centers. At a node C(2s+1, s+1) with u = v(A₀),
w = v(A₁): for u ≤ N−1 the trichotomy {u odd ∧ 2w > u → RAM(u)} ⊔
{2w < u → 2SIDED(w, u−w)} ⊔ {u = 2k ∧ w ≥ k → residual read} is exhaustive
and mutually exclusive (parity + comparison; 2w = u impossible at odd u);
the residual quadratic over F_q is split/irreducible/double-root-z̄≠0
exhaustively in both characteristics (char ≠ 2: discriminant square class;
char 2: c₁ ≠ 0 Artin–Schreier by Tr(c₀/c₁²), c₁ = 0 the Frobenius square —
z̄ = 0 impossible since c₀ ≠ 0). For u ≥ N the tail dichotomy 2w < N →
SPLIT-TAIL(w) (σ certified split for EVERY lift, incl. A₀ = 0 exactly) vs
undecided is exact, and every undecided member genuinely has both split and
inert lifts (F6 refines the "AND ram" parenthetical). Decidedness of each
leaf against all lifts checked (RAM decidable in-window whenever u ≤ N−1
since A₁ ≡ 0 ⟹ w ≥ N ≥ (u+1)/2). The refinement isomorphism S2.3 re-checked
in both characteristics (char ≠ 2: digit cancellations z̄²−2z̄²+z̄² = 0 and
−2z̄+2z̄ = 0; mixed char 2: v(2s) ≥ k+1 and 2z̄² ≡ 0; equal char 2: A₁
unchanged), affine unit-Jacobian map, compact-open equal-measure ⟹ onto.
**No eighth family; no overlap** (the read is a deterministic function, so
the leaves partition by construction; key-SET equality with the closed-form
list confirmed on 7 census rows incl. F₄/F₈/F₉ and the depth-3 (Zp,2,8) row).
The wild p = 2 branch holds no hidden family: the AS/Kummer loci differ, the
three census constants (q−1)(q−2)/2, q(q−1)/2, q−1 re-derived equal in both
characteristics (row sums q(q−1) ✓).

### Charge 2 — exact counts re-derived from scratch (> 3 rows, incl. RAM(h ≥ 3) and both deep families)

Per node instance at state s, per leaf, with the bracket Σ_{s<k}
instances(s) = 1 + Σ(q−1)q^(s−1) = q^(k−1) (re-derived; instances(s) =
Σ_t C(s−1,t−1)(q−1)^t = (q−1)q^(s−1)):

* RAM(h = 2k−1): (q−1)q^(N−1−h) · q^(N−k) per instance × q^(k−1) =
  (q−1)q^(2N−2k−1) per center ✓ (h = 3, 5, 7 window-checked at (2,6)/(2,8));
* INERTDEEP(k): (q(q−1)/2)·q^(N−k−1)·q^(N−2k−1) × q^(k−1) = ((q−1)/2)
  q^(2N−2k−2) ✓; SPLITEQ(k): same with (q−1)(q−2)/2 ✓ (uniform A₁-count
  q^(N−k−1) for c₁ = 0 and c₁ ≠ 0 checked);
* 2SIDED(w₁,w₂): (q−1)²q^(2N−w₁−(w₁+w₂)−2) × q^(w₁−1) = (q−1)²q^(2N−3−w₁−w₂)
  ✓; SPLIT-TAIL(w): (q−1)q^(N−w−1)·1 × q^(w−1) = (q−1)q^(N−2), w-independent ✓;
* SEP rows ((q²−q)/2)q^(2N−2), no center factor ✓.

**σ-undecided = q^N derivation checked exactly:** per instance the undecided
cell is A₀ ≡ 0 (one class) × v(A₁) ≥ ⌈N/2⌉ (q^(⌊N/2⌋) = q^(⌈(N−1)/2⌉)
classes), INDEPENDENT of s because reachable states have s + 1 ≤ ⌈N/2⌉
(s ≤ ⌊(N−1)/2⌋ from the 2k ≤ N−1 refine-visibility bound); bracket sum
q^(⌊(N−1)/2⌋), so per center q^(⌈(N−1)/2⌉+⌊(N−1)/2⌋) = q^(N−1), × q centers
= **q^N exactly** ✓. Window split = inert EXACT verified structurally:
per node per depth k, (q−1) [2SIDED+TAIL A₀-mass q^(N−2w−1) leg] +
(q−1)(q−2)/2 [SPLITEQ] = q(q−1)/2 [INERTDEEP], same k-range (2w < N ⟺
w ≤ ⌊(N−1)/2⌋ = the SPLITEQ/INERTDEEP range) ✓. The note's preregistered
spot tables ((Zp,2,4), (Fqt,9,3), (Zp,2,8), (Fqt,8,3)) all re-computed by
hand from my own forms — every number matches, sums q^(2N) exact.

### Charge 3 — limit densities and the capstone tie

Σ re-derived: ram = Σ_{h odd}(q−1)q^(−h−1) = 1/(q+1) ✓; 2SIDED total
1/(q²(q+1)), SPLITEQ total (q−2)/(2q²(q+1)), deep-split = deep-inert =
1/(2q(q+1)) ✓; split = inert = (q−1)/(2q) + 1/(2q(q+1)) = q/(2(q+1)) ✓;
2·q/(2(q+1)) + 1/(q+1) = 1 ✓. Per-node deep-inert fraction q/(2(q²+q+1)) of
μ_s ✓ (S2.5's parenthetical is right; S2.4's leg display is F1). At q = 2:
1/4 + 1/12 = 1/3 = q/(2(q+1)) ✓ (modulo the F3 display slip). Lean side:
`gate3_inert_q2 : omCount (sepShape 2 lam2) 2 = 1 / 4` at
`lean/LeanUrat/OM/OMCountV2.lean:646` ✓ (the certified order-0 inert value);
`montes_unconditional_exhaustive` hypothesis is
`Tendsto (fun N => (realM2 n hn).undecidedCount N / realP^(n*N)) atTop (nhds 0)`
(`OM/RealInstanceV2.lean:439-442`), quoted faithfully in the note's intro;
`undecidedCount` is the box residual (box − Σ decided over `omMenu` =
order-0 slice at HEAD), so the note's BOX-3/BOX-5 convention caveat is
apt and honestly displayed. `omMenu_order0 … = sepShapesOf … := rfl`
(`OMCountV2.lean:315`) ✓. No overclaim of the Lean side anywhere.

### Charge 4 — blueprint §S0 box

`docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §S3.1 row W-11 reads
byte-identically to the note's quote (modulo hard line-wrapping): "menu tie:
decided order-r shapes ↔ grown omMenu entries (typeOf-keyed), hExhaust
program stated as mathematics | J-D | **M** | W-10 | omMenu order-0 slice
(Lean, capstone); L5fix menu finiteness (math)". The reconciliation is
faithful: instance-first execution of the row, "EXCEEDED at n = 2" is
accurate (hExhaust proved, not merely stated, at the slice), the divergence
box correctly separates the two alternative readings and claims neither.
`WELD_SYNTHESIS_2026-08-05` §4(ii) step (3) = "W-11 menu tie" ✓.

### Charge 5 — DULEMMA / (DMULT-s) at e_m = 1

`DULEMMA_PROOF_2026-08-08.md` confirms the perimeter: (DMULT-s) PROVED-
conditional on the scored stratum at **e_m ≥ 2** (seal 048cf6d/f819f26 ✓ in
history). Audit of S2 for smuggled value-layer multiplicativity: the only
multiplicative steps are (a) counting disjoint letter-branch instances
((q−1)^t per history — S2.3's measure-space bijection, not a value law),
(b) Hensel factorization at separable residuals (degree-1 / separable-
residual factor lifting — classical, cited), (c) digit-counting products of
independent coordinate constraints. The e = 1 rows (SPLITEQ/INERTDEEP) are
pure count statements off the residual census; no (DMULT)-shaped identity
(no product of stage values/densities across levels) appears anywhere in
S2.1–S2.5. **DULEMMA is genuinely not consumed; no e_m = 1 stretch found.**

### Charge 6 — n = 2 fencing at consuming surfaces

Checked every claim surface: title, intro ("answers all three AT n = 2"),
S0 ("stated as mathematics at general n"), S1 GRADE box ("GENERAL W-11 …
NOT proved — BOX-1"), S4.3 ("None of (P1)–(P3) is proved here beyond
n = 2"), S6 BOX-1 ("Nothing at n ≥ 3 is claimed"), S8 (consumers get "a
PROVED exhaustiveness INSTANCE" / "the template"), S10 ("the general W-11
remains the S4.3 program"). Airtight except the F4 characteristic-fence slip
in S5 (an n = 2-internal issue, not an n-fencing one). The R_τ ∈ ℚ(q)
corollary is correctly fenced as an n = 2 display, not the general-r theorem.

---

## 3. MACHINE LEG

**Seal verification:** `w11_checks.py` md5 `500aae152bb5b5e9df3712904a6d73a6`
at HEAD == `git show 7020ceb:…` ✓ byte-identical. Committed artifacts match
cb05127: output.txt `c0b6b10b…`, results.json `72ad1567…` ✓.

**Re-run (this pass):** exit **0**, verdict **GREEN**, elapsed 50.8 s (note:
49.9 s). Every number matches §S10 exactly: 30/30 census rows; checks
**1,250,280**; violations W11-PIN=0 W11-CENSUS=0 W11-W10TIE=0 W11-EXHAUST=0
W11-TOWER=0 W11-ORACLE=0; teeth MISSING=SHADOW=DRAIN=**30**, SIGMA=**3,020**,
TAMEDISC=**1,440**; towers 12 levels (wild 7, beyond-211 1); oracle
(2,3):64/0 (2,4):256/0 (2,6):4096/0 (3,2):81/0 (3,3):729/0 (5,2):625/0
(7,2):2401/0. **Artifact byte-diff vs committed: timing-only** (the
`elapsed:` line in output.txt; four `elapsed_s` fields in results.json);
artifacts restored to committed state after diffing. Frozen-import md5s on
disk match the note's four pins (a9c34244 / cae45db2 / 03811b69 / d3a5e13d).

**Fresh route (verifier's own, no imports from the runner):**
`/tmp/w11_fresh_census.py` — an independent implementation of the S1/S2 read
(own F₄ = F₂[x]/(x²+x+1), F₈ = F₂[x]/(x³+x+1), F₉ = F₃[x]/(x²+1) arithmetic;
own window rings; own residual-type routine; own closed forms re-derived in
§2 above). Brute-force census of ALL monic quadratics on 7 rows the runner
samples: Zp (2,4),(2,6),(2,8),(3,3); Fqt (4,2),(8,3),(9,3) — ≈ 345k
polynomials. Result: **0 mismatches against my own closed forms on every
(leaf, params) key; exhaustiveness sum q^(2N), drainage exactly q^N,
split-decided = inert-decided, max refine depth = ⌊(N−1)/2⌋ on every row**
(depth 3 realized at (2,8)); and the per-key tallies are **identical to the
runner's committed JSON on all 7 rows** (programmatic key-for-key diff).
Independent teeth arithmetic: SIGMA 3,020 = 20+80+1344+27+270+250+1029 and
TAMEDISC 1,440 = 16+80+1344 re-derived from the closed forms; double-lift
1,070 = 56+240+72+702 = Σ(q^(2N)−q^N) over its four rows; total 1,235,872
polynomials re-summed from the 30-row list. All ✓.

**Counterexample probes (for F2):** eq-char-2 x²+t → RAM(1) decided with
disc ≡ 0 (falsifies the S2.2 bullet as stated); mixed (x+2)² at (2,8) →
UNDECIDED via realized history (1,2,3) with finite intermediate (u,w)
(falsifies the "u = w = ∞" mechanism); mixed x²+2 at (2,3) → decided RAM(1)
with disc ≡ 0 mod 2^N but disc ≠ 0 exactly (confirms the runner's exact-lift
disc convention is the right reading of the machine bracket).

---

## 4. SUMMARY FOR THE RECORD

The theorem's substance — the seven-family menu, its completeness, every
exact count law, undecided = q^N, split = inert at every window, the limit
sum 1, and the 1/4 + 1/12 = 1/3 capstone tie — survived a full independent
re-derivation plus an independent machine census. The four findings are:
one false displayed identity-evaluation chain in S2.4 (F1, factor-q slips;
true conclusion), one false unfenced side claim in S2.2 with an equal-char-2
counterexample (F2, zero blast radius on (i)–(iii)), one display slip in
S4.2's tail sum (F3), and one dropped "mixed" qualifier in S5 (F4). All four
are cheaply repairable without touching any count, box, or the machine leg.
Pass verdict: NOT CLEAN; repair then re-pass.

*Verifier: fresh-context hostile pass PE1, 2026-08-07/08. Machine artifacts
of this pass: `/tmp/w11_fresh_census.py`, `/tmp/w11_fresh_census_results.json`
(scratch, not committed).*
