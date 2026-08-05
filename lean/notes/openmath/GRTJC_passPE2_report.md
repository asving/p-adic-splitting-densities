# GRTJC pass PE2 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**, i.e. after
the r1 STRUCTURAL repair (commits `85d5811`, `54904cc`, `f45b63c`, `66263ce`).
Runners `verification/openmath/grt_jc_checks.py` (r0, sealed `6ad01d1` → `8f07904`)
and `verification/openmath/grt_jc_r1_checks.py` (r1 mini-seal `f45b63c` → `66263ce`).
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Scope fences and honest boxes are graded as part of the statement.
**Pass date:** 2026-08-05 wallclock (campaign 2026-08-08). Second acceptance attempt.

## VERDICT

**0 CRITICAL · 9 GAPS — NOT CLEAN.** Counter stays 0/2.

**The structural repair itself survives a full hostile re-derivation.** I
re-derived JC-LOC, JC-PIINV, JC-BSURJ, (COORD-B)(1)(2), (MULT-B), JC-COB,
JC-PSIKER(ii)(iii) and all five PE1 consumers from scratch and found **no false
statement**: the localization really is the graded algebra of the valuation on the
FULL polynomial ring `K[x]` (not of a subring — see §A1 for the m = 0 hand
computation that decides this), the constant `c_π` is absorbed EXACTLY with no
leak (§A2 exhibits the cancellation `a_{kE}·a_{n+k′E} = a_{n+(k+k′)E}` that makes
(COORD-B)(2)'s algebra map unital and multiplicative on the nose), REALIZE-(m) is
quoted **inside** its accepted scope (its descent invariant `(I_m): β ≥
e_{m−1}g_{m−1}γ_m` *is* JC-BSURJ's displayed inequality `β_d ≥ wΦ_m`, verbatim —
§A3), and the corrected PSIKER range holds in both directions (hand-checked on two
rows, §M(d)). PE1's two CRITICALs are genuinely repaired, not re-labelled.

What the nine gaps are about: **the repair moved the literature footprint onto one
identity, (DMULT), and that identity's *exact* (multiplier-1) form is stronger than
what §0's own transport statement can cite** (G-1); the new machine leg that is
supposed to carry it never tests its bilinear content (G-2); one machine figure is
a pre-seal smoke value presented as the roster (G-3); and the `[r1]` bracket system
left seven live call sites naming the struck `(COORD)`/`(MULT)`, one of them inside
a THEOREM statement box and asserting the opposite of r1's own headline (G-4).
Four smaller gaps: two unwritten transport steps the repair needs (G-5, G-9), the
JC-LOC↔literature identification (G-6), and two bookkeeping/arithmetic defects
(G-7, G-8).

**Machine leg: BOTH batteries fully reproduced, exit 0, artifacts byte-identical**
(one wallclock digit aside), seals verified, R1-DMULT audited as an *independent*
test, two PSIKER rows hand-derived. Details in §M.

---

## §A WHAT I RE-DERIVED (the load-bearing repair, checked to the bottom)

These are not concessions; they are the hostile re-derivations the charge asked
for, and they are what makes the verdict 0 CRITICAL. Each is reported because the
gaps below must be read against it.

### A1. JC-LOC — is `B` the associated graded of the FULL valuation ring? YES.

The charge's suspicion (that `B = gr(w)[in(π)^{-1}]` might be the graded algebra of
a *subring*, or that the localization introduces torsion) does not land.

* **Torsion/flatness.** `in(π)` is homogeneous of degree `E` and a nonzerodivisor
  in the domain `gr^O(w)` ((IN-3)(a)(b) + `w(π) = E`), so the graded localization
  is flat, `gr^O(w) ↪ B` is injective, and `B_n = ∪_k in(π)^{-k}gr_{n+kE}` is a
  filtered colimit of injections. No torsion, no collapse. JC-DOM is clean.
* **The degreewise map is an isomorphism.** I re-ran the four legs. Well-defined:
  `in(π)^{-k}in(g) = in(π)^{-k′}in(g′)` in `B` ⟺ `in(π^{k′}g) = in(π^{k}g′)` (`in(π)`
  a nonzerodivisor) ⟺ `w(π^{k′}g − π^{k}g′) > w(π^{k′}g)`, and dividing by
  `π^{k+k′}` gives `w(π^{-k}g − π^{-k′}g′) > w(π^{-k}g)` — the same statement in
  `gr^K`. Surjective in degree `n`: `π^kf ∈ O[x]` for large `k`, weight `n+kE`.
  Injective: `w(π^{-k}g) = n` exactly.
* **Is `B_0` the polynomial ring `Δ = K_m[y]` and not a LAURENT ring?** This is the
  question that decides "FGMN's object". Hand computation at `m = 0`
  (`Φ_0 = x`, `w(π) = e_0`, `w(x) = h_0`, `gcd = 1`): a monomial `c·x^aπ^b` has
  `gr`-degree `0` iff `e_0(v(c)+b) + ah_0 = 0`, which forces `a = e_0t`,
  `b + v(c) = −h_0t`. Because the ambient ring is `K[x]` (**not** `K[x,x^{-1}]`)
  one has `a ≥ 0`, hence `t ≥ 0`, hence `B_0 = K_0[u]` with
  `u = in(x^{e_0}/π^{h_0})` — a POLYNOMIAL ring, matching `Δ = K_m[y]` with
  `y ↔ u`. Cross-check in the note's own coordinates: at `λ = ke_0`, `s_NR = 0`,
  on-line abscissas `a = e_0j` need `v(A) = k − jh_0 ≥ 0`, so
  `deg 𝑅_{ke_0} ≤ ⌊k/h_0⌋` — bounded at each `k`, unbounded in the colimit.
  Both computations agree, and they agree with the note. The slot index is `≥ 0`
  always (`a ≥ 0`, `a ≡ s_NR`, `s_NR ∈ [0,e_m)`), so no negative powers of `y` can
  appear — which is exactly why the colimit is `K_m[y]` and not `K_m[y,y^{-1}]`.
* **Consistency of `(DMULT)` with JC-PIINV, checked for a leak.** `(DMULT)` with
  `f = π` forces `c_π = 𝑅_E(π) = a_E` (since `δ(E,λ) = 0`), and JC-PER gives
  `φ_E = π`, so `c_π = a_E` is not an extra constant but the anchor constant at
  line `E`. `𝑅_{2E}(π²) = c_π²` both ways. No inconsistency.

### A2. JC-PIINV + (COORD-B) — does `c_π` leak? NO, and here is the cancellation.

`c_π ≠ 1` on **20 of 29** rows (reproduced this pass; see G-3 for the note's own
misquote of the value set), so this is a real hazard.

* `ρ_λ := 𝑅_λ/a_λ` with `a_{λ+E} = c_π a_λ` (JC-PIINV(b) + `φ_{λ+E} = πφ_λ`
  byte-for-byte, JC-PER) gives `ρ_{λ+E}(πf) = ρ_λ(f)` **exactly**, so the colimit
  `ρ^B_n := colim_k ρ_{n+kE}` is well defined; in the un-normalized `𝑅` it would
  not be. Injectivity is the colimit of injections (`𝑅_λ(f) = 0 ⟺ w(f) > λ`).
  `ρ^B_n(in φ_n) = 1`.
* **The ISO statement absorbs `c_π` correctly.** (COORD-B)(2)'s proof needs
  `a_{kE}·a_{n+k′E} = a_{n+(k+k′)E}` for the division by anchor constants to turn
  `𝑅(tβ) = 𝑅(t)𝑅(β)` into `ρ^B_0(tβ) = ρ^B_0(t)ρ^B_n(β)`. That holds on the nose:
  `a_0 = 𝑅_0(φ_0) = 1` (`φ_0 = 1`, `0 ∈ W`), `a_{kE} = c_π^k`,
  `a_{n+k′E} = c_π^{k′}a_n`, and `a_{n+(k+k′)E} = c_π^{k+k′}a_n`. So the map is
  unital (`ρ^B_0(1) = 1`) and multiplicative with **no residual constant**. The
  step is not written in the note but it is true and forced.
* Machine bracket, reproduced: R1-PER 841/0 with `c_π` one constant per row and
  `k = 1,2` consistent (`c_π²` exact); tooth T5 (the `y`-shift mutation) fires
  406/406.

### A3. JC-BSURJ — proved, and REALIZE-(m) is quoted IN scope.

Re-derived: `β_j := (λ − a_jγ_{m+1})/e_m` with `a_j = s + je_m` is an integer
because `γ_{m+1} ≡ h_m` and `λ ≡ s·h_m (mod e_m)` (eq-(12)), so
`λ − a_jγ_{m+1} ≡ −je_mh_m ≡ 0`; `β_j` decreases in `j`, so the single displayed
inequality `(n+kE) − (s_NR(n)+d·e_m)γ_{m+1} ≥ e_m·wΦ_m` (i.e. `β_d ≥ wΦ_m`)
gives `β_j ≥ wΦ_m` for all `j ≤ d`; `deg A_j < deg Φ_m` makes `Σ_j A_jΦ_m^{a_j}`
the actual `Φ_m`-development, so every digit is on the line and `w(f) = λ`, and
the slot-`j` digit is `ε_m(β_j)·read_m(β_j,A_j) = c_j`. `β_j` grows by `E/e_m` per
`k`-step, so only finitely many `k` are excluded.

**Scope check (charge item 3).** `ITERLAWN_PROOF_2026-08-08.md` §S4.1 states
REALIZE-(m) under the DESCENT INVARIANT `(I_m): β ≥ e_{m−1}g_{m−1}γ_m`. Since
`wΦ_j = e_{j−1}g_{j−1}γ_j`, `(I_m)` **is** `β ≥ wΦ_m` — exactly JC-BSURJ's
hypothesis, and exactly the runner's guard (`num // em < T.wPhi[NR-1] → reject`).
The zero-coefficient slots are skipped, so R2's `τ ≠ 0` hypothesis is respected.
`REALIZE-(m)` is "PROVED, generic" in [ILN]† with its m = 1 base on [IL3]
WELL-DEF, and [IL3] is ACCEPTED. **No scope violation.**

### A4. The five PE1 consumers — each re-derived; all THROUGH.

1. **§3.1 / `A_ν` a K-line.** `A_ν ≅ B_n` (JC-GAUGE(iii)) and
   `B_n/(𝔦^B ∩ B_n) ≅ Δ/(ψ_m) = K`. Holds — but the transport of the *ideal*
   along JC-GAUGE(iii) is an unwritten step; see G-9.
2. **OB-4 / JC-IND.** `Σ_ν c_ν[φ_{γ_ν}] = 0` with `c_ν ∈ K = 𝒜_0` splits by the
   ℤ/E-grading (the TC-3 ideal is generated by ONE homogeneous element, so the
   quotient stays graded); `𝒜_ν = K·[φ_{γ_ν}]` and `[φ_{γ_ν}] ≠ 0` because
   `ρ^B(in φ_{γ_ν}) = 1 ∉ (ψ_m)`. Hence `c_ν = 0`. Clean, and the base-changed
   module now exists ((COORD-B)(2): `B_{γ_ν}` free of rank one over `Δ`).
3. **W-7 bijectivity via `dim_K 𝒜 = E`.** Each of the `E` graded pieces is a
   K-line, so the anchor span is the whole ring; injectivity is JC-IND. The
   strengthening ("spanning is a theorem, not a definition") is real.
4. **JC-F1's count.** `v^k = β_k[φ_{γ_k}]`, `β_k = ∏_{i<k}c(1,i) ∈ K^*`, the `v^k`
   sit in pairwise distinct ℤ/E-degrees hence are independent, `dim = E` so
   `{1,…,v^{E−1}}` is a basis, `v^E = ζ_T·[φ_0] = ζ_T` (`φ_0 = 1`), and
   `K[v]/(v^E − ζ_T) → 𝒜` is surjective and injective by `E = E`. Clean.
5. **(MULT-B) and the Δ-bilinearity step.** The r1 text is right that this is the
   step r0 skipped: a K_m-linear iso `gr_λ ≅ Δ` transports multiplication to
   *some* K_m-bilinear map, and only compatibility with the degree-0 action makes
   it "multiply and scale by `A(λ,μ)`". (COORD-B)(2) supplies exactly that.
   Uniqueness of `A(λ,μ)` follows from injectivity of `ρ^B` and `Δ` a domain.
   **No re-derivation silently reuses the old per-piece (COORD) form** — but seven
   of them still *name* it (G-4), and §4.1/§4.2/§5 apply the identity at gr-level
   without recording that this is the restriction of (MULT-B) to `gr_λ ⊂ B_λ`.

### A5. JC-PSIKER's corrected range — both directions confirmed.

`𝔦 := in(Φ_{m+1})·gr(w)` is principal homogeneous of generator degree `wΦ_NR`, so
`𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR}`. **Zero below:** `w ≥ 0` on `O[x]`
(`w_0 ≥ 0`, `γ_{j+1} > 0`), so `gr_j = 0` for `j < 0`, hence the intersection is 0
for `λ < wΦ_NR`. **Nonzero on the shifted window:** `in(Φ_{m+1})·in(φ_{λ−wΦ_NR}) ≠ 0`
because `gr(w)` is a domain. **Nonzero on every `B_n`:** `in(π)` is a unit of degree
`E`, so `B_j ≅ B_{j+E}`, and each residue class contains a window representative
with `gr_n ∋ in(φ_n) ≠ 0`, so no `B_j` vanishes and
`𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR} ≅ ψ_m(y)·Δ ≠ 0` for every `n ∈ ℤ`. All three
clauses (i)(ii)(iii) hold as written. Hand-verified numerically on C2A and C2I in
§M(d).

---

## GAP 1 — `(DMULT)`'s EXACT form is labelled CITED, but §0's own transport statement can only cite it UP TO A LINE-WISE UNIT (the repair's single literature leg is over-claimed)

**Offending passage (verbatim), §2.10:**

> **(DMULT) [r1 — the one cited input of the coordinate calculus].** For f,g ∈ O[x]
> with λ := w(f), μ := w(g):
>
>     𝑅_{λ+μ}(fg) = y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g),
>     δ(λ,μ) := (s_NR(λ) + s_NR(μ) − s_NR(λ+μ))/e_m ∈ {0,1}.
>
> This is the composite-stage form of (IN-2)'s (W-MULT) — stated there at the
> last-read layer — and of Montes/FGMN residual-polynomial multiplicativity; via
> JC-LOC it is the content of (IN-3)(c) on the object (IN-3)(c) is about. It is
> **CITED, not proved here**

and the note's own §0 (IN-3), which fixes what the citation delivers:

> Their transport to the HARNESS objects (w = v_{m+1} in the sheared frame;
> R_{m,λ} = c·R_λ^{GMN} with c a line-wise unit) is **W-1 (J-A), ATTEMPT GRADE**.

**Why this is a gap.** `𝑅` is §1's **ε-corrected harness** digit polynomial, and
§0 states that it differs from FGMN's `R^{GMN}` by a **line-wise unit** `c_λ`.
Transporting FGMN's residual multiplicativity through that rescaling gives

    𝑅_{λ+μ}(fg) = (c_{λ+μ}/(c_λ c_μ))·y^{δ}·𝑅_λ(f)·𝑅_μ(g),

i.e. the cited identity holds **up to the unit cocycle `c_{λ+μ}/(c_λc_μ)`**. The
displayed `(DMULT)` asserts that cocycle is identically **1** — a nontrivial
multiplicative-normalization property of the ε-kit that the note nowhere states,
nowhere proves, and cannot get from the citation *as §0 itself describes the
transport*. The note's own §9.3 finding 1 states the exactness as a **battery
result** ("**(DMULT) holds with multiplier exactly 1**, not merely up to a
line-wise unit"), which is the honest status: **measured on 29 rows, not cited.**
That the note simultaneously calls the exact form "CITED, not proved here" and
"a finding of the r1 battery" is the defect. It also sits directly on this repo's
standing memory item (*extraction corruption decorrelation*: verbatim pins against
shared extractions need a non-textual leg per load-bearing formula) — the
non-textual leg exists (R1-DMULT), so the fix is a label, not new work.

**What rides on the EXACT form vs the up-to-unit form** (checked, so the blast
radius is small): with only the up-to-unit form, `(COORD-B)(2)` still goes through
after rescaling (`ρ^B_0(1) = 1` forces the degree-0 factor to be 1), `(MULT-B)`
still goes through (`A(λ,μ)` absorbs the unit), and JC-BOX-4[r1]'s corner closure
still goes through (`κ·y^δa_γa_{γ′}` is still a monomial of degree exactly `δ`).
What loses its proof is **COROLLARY JC-COB's sharp form `u = a_γ·a_{γ′}`** (it
degrades to JC-SPAN's already-known `u ∈ K_m^*`), hence also §4.1's r1 replacement
remark ("the a's do not merely cancel, they ARE the inner factor"), JC-COB's second
half (`∏z_j^{D_j} = a_γa_{γ′}/a_{γ+γ′}`), and R1-COB's exact predicate. No clause
GRADE changes. **Classification: JUSTIFICATION GAP** (assume `(DMULT)` exact and
continue), with an honesty component: the citation is stronger than the source
§0 declares.

## GAP 2 — R1-DMULT, the leg that carries GAP 1, never tests `(DMULT)`'s bilinear content: 6 of its 7 sample elements have MONOMIAL digit polynomials and the one non-monomial × non-monomial pair is silently skipped

**Offending passages (verbatim), §9.3 prereg and verdict:**

> | **R1-DMULT** | (DMULT): 𝑅_{λ+μ}(fg) == y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g) EXACTLY (not
> merely up to a unit) on sampled pairs — the Δ-module half of (COORD-B), the leg
> neither prior runner had | **0** |

> | **R1-DMULT** | (DMULT), the cited input | 2,784 | **0** | GREEN —
> 𝑅_{λ+μ}(fg) == y^{δ}𝑅_λ(f)𝑅_μ(g) **EXACTLY** (multiplier 1, not merely
> proportional) **on every sampled pair of every row** …

**The code (`grt_jc_r1_checks.py`, audited this pass).** The sample set is a fixed
7-element list per row:

```python
def samples(S):
    """assorted INTEGRAL f with their exact weights (deterministic)."""
    cands = [S.ph[r] for r in range(min(S.E, 3))]   # anchors  -> R is a MONOMIAL
    cands.append(S.X)                               # X_N      -> R == 1
    cands.append(P.mul(S.ph[0], S.ph[1 % S.E]))     # anchor product -> MONOMIAL
    cands.append(P.add(S.ph[0], P.mul(S.pi1, S.ph[0])))  # (1+pi)*phi_0 -> MONOMIAL
    cands.append(S.PhiTop)                          # the ONLY non-monomial R
```

and the DMULT loop explicitly excludes the only pair with a non-monomial factor on
**both** sides:

```python
    for (f, lf) in smp:
        for (g, lg) in smp:
            if f == S.PhiTop and g == S.PhiTop:
                continue
```

**Consequence.** `2,784 = 29 rows × 48 ordered pairs × 2 predicates`, and in every
one of those 48 pairs at least one factor has a **single-slot** digit polynomial.
For a single-slot factor, `y^δ𝑅_λ(f)𝑅_μ(g)` is just a shift-and-scale — the
identity's genuinely *bilinear* content (cross-term formation, `Σ_k` convolution of
two multi-slot digit polynomials) is **never exercised**, and the one pair that
would exercise it is dropped without disclosure. Neither the prereg row ("on
sampled pairs") nor the verdict cell ("on every sampled pair of every row")
discloses the sample composition or the skip. This is the **same species of defect
r1 was repairing** in G3 (a filter before the predicate) and G6 (an undisclosed
606-skip), reintroduced in the new leg — and it is the leg the note points to as
the answer to PE1's "the instrument did not measure Δ-freeness". R1-PSIK-HI
partially compensates (it tests `Φ_{m+1}·φ_ν`, i.e. non-monomial × monomial, with
the exact `a_ν·y^δ·ψ_m(y)` form, 1,182/0), but that is still one-sided.
**Classification: JUSTIFICATION GAP** (evidence resolution, undisclosed skip).

## GAP 3 — STALE MACHINE QUOTE: §2.10 reports the PRE-SEAL 6-ROW SMOKE's `c_π` value set as the roster measurement, and the note's own artifacts contradict it

**Offending passage (verbatim), §2.10 after JC-PIINV:**

> *Machine (r1 §9.3):* family **R1-PER** — 𝑅_{λ+kE}(π^kf) = c_π^k·𝑅_λ(f) with one
> c_π per row and ρ exactly invariant, k = 1,2, on every row (measured
> **c_π ∈ {1, z̄, z̄²} across the roster**: a nontrivial constant, which is exactly
> why the ρ-normalization is the one that makes the colimit well defined).

`{1, z̄, z̄²}` is the value set of the **pre-seal 6-row mechanism probe**, and the
note discloses it as such two sections later ("a 6-row mechanism probe
(C2A/C2I/C3A/C3I/C4H/C4I) which found … that c_π is a single row constant taking
values in {1, z̄, z̄²}"). The **roster** value set, from the committed artifact and
reproduced this pass (R1-CEN column `c_pi`), is `{1, z̄, z̄², z̄³, z̄⁴, z̄⁶, z̄⁸}` —
`z̄³` on C2G, `z̄⁴` on C3H, `z̄⁶` on C2H, `z̄⁸` on I4C — which is what §9.3's own
verdict cell says ("measured c_π = 1 on 9 rows and z̄^a with a ∈ {1,2,3,4,6,8} on
the other 20"). So §2.10 quotes a 6-row smoke figure with the words "across the
roster", contradicted by the note's own §9.3. It **understates** (a larger value
set strengthens the point being made), so nothing mathematical moves.
**Classification: JUSTIFICATION GAP** (stale machine quote / mislabelled
provenance).

## GAP 4 — the `[r1]` bracket system leaks: seven live sites still consume the STRUCK `(COORD)`/`(MULT)`, and one of them — inside a THEOREM statement box — asserts the exact opposite of r1's headline

`(COORD)` and `(MULT)` are struck (`~~…~~`) and declared REPLACED by (COORD-B) /
(MULT-B). The following sites are un-bracketed and live.

**(a) The worst one — inside the W-7 THEOREM statement box (§3, verbatim):**

> * **OB-4 (independence): PROVED, general m** — degree separation +
>   **(COORD)/(IN-3)(c)** base change (§3.4); the Δ-rank input is
>   literature-carried, **NOT measured** (JC-BOX-3).

Both halves are superseded. `(COORD)/(IN-3)(c)`-on-`gr_λ` is the statement PE1
**refuted** and r1 struck; and "the Δ-rank input is … NOT measured" is exactly what
r1's rewritten §3.4 rider denies — "**r1 measures its equivalent digit form**:
family R1-DMULT … plus its sharp corollary R1-COB". So a THEOREM statement box at
HEAD still grades OB-4 on a refuted input and denies the round's own machine leg.
Note the same box's `𝒜(T)` definition WAS given a `[r1, G2]` bracket, so the pass
touched this box and left the grade line behind.

**(b) Five proof bodies apply the struck `(MULT)` by name:**

> §3.2: "divide by a_{γ+γ′} to pass to ρ, which is the definition of A(γ,γ′) in **(MULT)**."
> §4.1: "Apply ρ_{λ+N} and **(MULT)** to both sides."
> §4.2: "Apply **(MULT)** with ρ_N(in X_N) = 1/a_N ∈ K_m^*."
> §5(i): "expanding both with **(MULT)**"; §5(iv): "iterating **(MULT)** along the orbit".

These are *recoverable*: for `α ∈ gr_λ ⊆ B_λ`, `ρ^B_λ|_{gr_λ} = ρ_λ` and
`αβ ∈ gr_{λ+μ}` ((IN-3)(b)), so the gr-level identity is the restriction of
(MULT-B). But the note never records that restriction, so as written W-8, §4.2 and
W-9 are proved by invoking a statement the note struck three sections earlier.

**(c) §4.1 remark (b), which contradicts r1's footprint claim (verbatim):**

> (b) C15's separation stands: nothing above uses N-1's operator-level commuting
> diagram; what is used is **(COORD)+(MULT)**, i.e. the carrier-level content,
> which is precisely what C15 said was missing. This note supplies it from
> **FGMN Thm 4.2** + the corpus's read definition, at the cost of riding W-1's
> dictionary for the transport of Thm 4.2 to the harness w.

Against §2.10's r1 headline — "the surjectivity half becomes a theorem of this note
(JC-BSURJ, from REALIZE-(m)), and the only cited input left in the coordinate
calculus is the multiplicativity (DMULT)" — and JC-BOX-3[r1]'s "it uses it **only**
through the single statement (DMULT)". Two incompatible footprint statements at
HEAD.

**(d) Lower-weight:** §10.1's r0 grade table still reads "W-8 … **PROVED at general
m on (COORD)+(MULT)**+JC-SPAN+JC-SCAL+R3" (arguably fenced: the `[r1]` block above
it says the r0 table "stands except where this block supersedes it", and its W-8 row
does re-list the inputs); and W-8's own `[r1]`-updated grade line still ends
"(i.e. FGMN (b)**(c)**(e) via W-1, ATTEMPT)", where (c) is the Thm-4.2-on-`gr`
input that §3.5 says "enters only through (DMULT), on B".

**Classification: JUSTIFICATION GAP** for (b)(d) (recoverable renames);
**(a) and (c) are honesty defects** — un-superseded text that states the negation
of the round's own findings inside a theorem box and a remark.

## GAP 5 — `(MULT-B)` and §2.10's TC-3 display quantify over ALL `λ, n ∈ ℤ`, but `ρ^B` and the anchors are only defined ON the window; the transport step is gestured at, never written

**Offending passages (verbatim), §2.10:**

> **(COORD-B) [r1 — REPLACES (COORD)].** Fix ν ∈ ℤ/E and **n ∈ W** with n ≡ ν (mod E) …

> **(MULT-B)** … for α ∈ B_λ, β ∈ B_μ and **all λ,μ ∈ ℤ** (window representatives
> are used only to name the anchors; by (COORD-B)(1) every class mod E has one).

> Hence for **every n ∈ ℤ** ⟹ B_n/(𝔦^B ∩ B_n) ≅ Δ/(ψ_m) = K_{m+1} = K

`ρ^B_n` is defined only for `n ∈ W`, because `a_n := 𝑅_n(φ_n)` needs the anchor, and
JC-BOX-7 records "outside, gr_γ = 0 and **no anchor exists**". Making the
all-of-ℤ statements meaningful requires (i) the *virtual* anchor
`in φ_λ := in(π)^{-k}in(φ_{λ+kE}) ∈ B_λ` and (ii) `ρ^B_λ := ρ^B_{λ+kE} ∘ (in π)^k`,
both `k`-independent by JC-PIINV(c). This is a two-line step and it is true, but the
note replaces it with a parenthesis. Same omission at the display
`ρ^B(in Φ_{m+1}) = ψ_m(y)/a_{wΦ_NR}`, which presumes `wΦ_NR ∈ W` (true under
JC-BOX-7's convention, since `wΦ_NR` is attained by `Φ_{m+1}`, but unstated).
**Classification: JUSTIFICATION GAP.**

## GAP 6 — JC-LOC proves `B ≅ gr` of the NOTE'S OWN extension of `w` to `K[x]`; the identification of that extension with the literature's valuation — the step that licenses "B IS FGMN's object" — is asserted by phrasing

**Offending passage (verbatim), §2.10:**

> **LEMMA JC-LOC [r1] (B *is* the object FGMN's theorems speak about).** Write
> gr^O(w) for §1's graded ring (built on O[x]) and gr^K(w) for **the same
> construction on K[x] = O[x][π^{-1}], with w extended by
> w(π^{-k}g) := w(g) − kE.**

and its closing gloss:

> Thm 4.2 is a statement about gr^K. By JC-LOC the note HAS gr^K — it is TC-1's
> output — so the citation is now APPLIED to the object it is about

The lemma is correct as stated, and the extension **is** the MacLane valuation on
`K[x]` (the min-formula is `w_0`-homogeneous under scaling by `π^{-k}`, since
`w_j(π^{-k}A) = w_j(A) − k·e_0⋯e_{j−1}`). But the note never checks that: it
*defines* `gr^K` by the extension and then asserts that this is the object FGMN's
theorems are about. Since PE1's CRITICAL 1 was precisely a mis-identification of
the ambient object, the second identification deserves the same scrutiny as the
first, not a parenthetical "the same construction on". Also, JC-LOC's proof checks
well-definedness, multiplicativity, gradedness, surjectivity and injectivity, but
**not additivity** of the degreewise map (needed because homogeneous elements are
`in(f)` or `0`, and sums can drop degree). **Classification: JUSTIFICATION GAP.**

## GAP 7 — JC-BOX-4 is described as "unchanged" in two places while it in fact gained an `[r1]` conditional closure, and three r1 edits describe the same top-flat corner three different ways

**Offending passages (verbatim).** W-6's `[r1]` grade block:

> Boxes: **JC-BOX-4 (unchanged)** and JC-BOX-3 **re-cut to box APPLICABILITY, not
> literature truth**.

§10.1's r1 grade table, W-6 row:

> (ii) re-keyed to B_n (G1); (v) re-quantified (F2); **box JC-BOX-4 unchanged**

But JC-BOX-4 at HEAD carries:

> **[r1 — CONDITIONALLY CLOSED, on (DMULT).]** … **So: the corner is CLOSED for a
> reader who grants (DMULT) (JC-BOX-3), and stays OPEN for one who wants it
> independent of the FGMN input**

while §2.8(c)`[r1, G5]` fences the set identity as "theorem where proved (28 rows),
measured where measured (C4H)" and §7 case 5 still reads "sharp form **MEASURED not
proved** — JC-BOX-4".

**On the charge's question about G5's honesty: G5's fence IS honest.** It matches
JC-LOAD's own written hypothesis (`e_m ≥ 2`), the roster geography is right (C4H is
the unique `e_m = 1` row — reproduced this pass from R1-CEN), and it *understates*
relative to JC-BOX-4[r1]. And JC-BOX-4[r1]'s argument is **correct**: at `e_m = 1`,
`s_NR ∈ [0,1) = {0}` so `δ ≡ 0`, and `(DMULT)` on two anchors gives the constant
`a_γa_{γ′}`, so the slot set is `{0}` with no `e_m` hypothesis, and `0 = δ < g_m`
makes RAW always solvable. The defect is purely bookkeeping: two places assert
"unchanged" about a box that changed, and the note never reconciles
"conditionally closed on (DMULT)" (JC-BOX-4) with "MEASURED not proved" (§7 case 5,
§2.8(c)) even though every clause of §§2.10–5 already rides (DMULT).
**Classification: JUSTIFICATION GAP** (bookkeeping; no false statement).

## GAP 8 — §9.3's headline sample total double-counts: "10 FAMILIES … 10,475 scored samples" over an 11-row table; the ten families sum to 10,330

**Offending passage (verbatim), §9.3 verdict:**

> **ALL 10 FAMILIES GREEN — 10,475 scored samples, 0 violations, 29 rows,
> elapsed 2.6 s, exit 0; ALL FIVE TEETH FIRED (1,885 firings, no silent tooth,
> every per-row obligation met: TOOTH-ROW 145/145).**

Reproduced this pass, family by family: EXT-GATE 1, R1-BND 29, R1-PER 841,
R1-INJ 585, R1-SURJ 841, R1-DMULT 2,784, R1-COB 2,607, R1-PSIK-LO 591,
R1-PSIK-HI 1,182, R1-UNIT 869 — **ten families, total 10,330**. The quoted 10,475
adds TOOTH-ROW's 145, and TOOTH-ROW is itself a family by §9.1's own disclosure
("per-row tooth obligations are scored as their own family (TOOTH-ROW)"). So the
correct pair is either "10 families / 10,330" or "11 families / 10,475"; the table
under the headline has **eleven** rows. r0's §9.2 got this right (its ten families
sum to exactly 8,566, the MJ teeth counted separately), so r1 broke the note's own
convention. Nothing else moves: `0` violations, `29` rows, exit `0`, `1,885` tooth
firings (`29+29+1,392+29+406`) all reproduce exactly.
**Classification: JUSTIFICATION GAP** (machine-quote arithmetic).

## GAP 9 (low) — JC-GAUGE(iii) is stated as an isomorphism of ADDITIVE GROUPS, and §3.1/§2.10 use it to transport a quotient by an IDEAL

**Offending passages (verbatim).** JC-GAUGE(iii):

> (iii) for each ν and EACH n ≡ ν (mod E) the composite B_n → A_ν is an
> **isomorphism of additive groups**; in particular A_0 ≅ B_0 as rings.

§3.1's r1 re-derivation:

> By JC-GAUGE(iii) the gauged piece is A_ν ≅ **B_n** … and by §2.10's repaired
> display B_n/(𝔦^B ∩ B_n) ≅ Δ/(ψ_m) = K with basis the image of in(φ_n). So after
> TC-3 each 𝒜_ν is a 1-dimensional K-space with basis [φ_{γ_ν}]

`𝒜_ν = A_ν/(image(𝔦^B) ∩ A_ν)`, so the conclusion needs `σ` to carry
`image(𝔦^B) ∩ A_ν` onto `𝔦^B ∩ B_n` — which an additive-groups-only isomorphism
does not give for free. It **is** true: `σ(𝔦^B ∩ B^{(ν)}) = Σ_k ϑ^{-k}(𝔦^B ∩
B_{n+kE}) ⊆ 𝔦^B ∩ B_n` because `𝔦^B` is an ideal and `ϑ^{-k} ∈ B`, and the reverse
inclusion is the `k = 0` term. Unwritten, one line, load-bearing for both §3.1 and
§2.10's "for every n ∈ ℤ" display. **Classification: JUSTIFICATION GAP.**

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. Both runners
overwrite their own `*_results.json` on execution; `git diff` after both reruns is
**empty on `verification/openmath/`**, i.e. both runs reproduced the committed JSON
artifacts **byte-for-byte**. (The only working-tree modification at the time of this
pass is `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, another agent's work —
untouched and unstaged by me.)

### (a) The sealed r0 battery — reproduced exactly, exit 0

`python3 grt_jc_checks.py` → exit **0**, elapsed 2.0 s, 29 rows,
`total violations 0; silent teeth NONE`. `diff` against the committed
`grt_jc_checks_output.txt` differs in **one character**: row I4C's per-row wallclock
(`0.9s` committed vs `1.0s` here). All content identical. Every §9.2 cell:

| family | §9.2 | re-run | match |
|---|---|---|---|
| EXT-GATE | 1 / 0 | 1 / 0 | ✓ |
| JC1 | 2,594 / 0 | 2594 / 0 | ✓ |
| JC2 | 570 / 0 | 570 / 0 | ✓ |
| JC3 | 2,484 / 0 | 2484 / 0 | ✓ |
| JC3-FLAT | 24 / 0 | 24 / 0 | ✓ (printed `JC3-FLAT-census`) |
| JC4 | 443 / 0 | 443 / 0 | ✓ |
| JC5 | 855 / 0 | 855 / 0 | ✓ |
| JC6 | 116 / 0 | 116 / 0 | ✓ |
| JC7 | 581 / 0 | 581 / 0 | ✓ |
| JC8 | 898 / 0 | 898 / 0 | ✓ |
| MJ1 | 103 firings / 333 tested | 103 / 333 | ✓ |
| MJ2 | 285 / 285 | 285 / 285 | ✓ |
| MJ3 | 4 / 6 | 4 / 6 | ✓ |
| MJ4 | 29 / 29 | 29 / 29 | ✓ |
| MJ5 | 633 / 633 | 633 / 633 | ✓ |

Ten families sum to **8,566** exactly as the note says (r0's arithmetic is clean —
contrast GAP 8). Tooth firings 1,054 = 103+285+4+29+633 ✓. Cyclic split
CYCLIC 6 / NOT-CYCLIC 14 / UNDECIDED 9 with C2A/C2E/C2G/C2J/C3A/C4A ✓.
**Seal:** runner md5 `adb555e1134d3ae0b0174d62e8b3446c` identical at `6ad01d1`,
`8f07904` and HEAD — the sealed runner is the run runner.

### (b) The r1 battery — reproduced exactly, exit 0

`python3 grt_jc_r1_checks.py` → exit **0**, elapsed 2.6 s, 29 rows,
`total violations 0; silent teeth NONE`. `diff` against the committed
`grt_jc_r1_output.txt` differs in **two per-row wallclock digits** (C3A, C3G);
all content identical, including the full R1-CEN census table.

| family | re-run samples / viol |
|---|---|
| EXT-GATE | 1 / 0 |
| R1-BND | 29 / 0 |
| R1-PER | 841 / 0 |
| R1-INJ | 585 / 0 |
| R1-SURJ | 841 / 0 |
| R1-DMULT | 2,784 / 0 |
| R1-COB | 2,607 / 0 |
| R1-PSIK-LO | 591 / 0 |
| R1-PSIK-HI | 1,182 / 0 |
| R1-UNIT | 869 / 0 |
| TOOTH-ROW | 145 / 0 |

Teeth: T1 29/29, T2 29/29, T3 1,392/1,392, T4 29/29, T5 406/406 — **1,885 firings,
no silent tooth**, matching the note. Census lines reproduce exactly:
`R1-COB: 869 anchor pairs scored (0 out-of-window skipped)`,
`R1-UNIT census: 869 unit / 0 zero / 0 undefined-denominator / 0 out-of-window, over 869 grid pairs`,
`R1-PSIK: 197 window lines below wPhi_NR with kernel 0; 197 residue classes with a certified nonzero kernel witness`.

**Charge-item checks against the note:** 10 families → see **GAP 8** (the ten
families total 10,330, not 10,475). 10,475 / 0 violations → the *total including
TOOTH-ROW* is 10,475 ✓ and violations are 0 ✓. R1-DMULT multiplier exactly 1 → ✓
(the predicate is literal equality of dicts, so "multiplier 1" is what 0 violations
means; and tooth T3, the `y^{δ+1}` mutation, fires on all 1,392 opportunities, so
the predicate is live). R1-COB 869/869 ✓. R1-UNIT 869/0 ✓.

**Mini-seal.** `f45b63c` touches **only** `verification/openmath/grt_jc_r1_checks.py`
(688 insertions, one file) — script only, as claimed. `66263ce` touches only the
note (83 lines) + `grt_jc_r1_output.txt` + `grt_jc_r1_results.json` — artifacts +
verdict, no script. Runner md5 `7f896bfa27d06158f95c5987c7299770` identical at
`f45b63c` and HEAD. The r0 runner and instrument are byte-frozen as claimed.

### (c) R1-DMULT code audit — does it TEST `(DMULT)` or ASSUME it? It TESTS it.

```python
            fg = P.mul(f, g)
            if T.wlev(NR, fg) != lf + lg: viol(...)
            d = delta_of(S, lf, lg)
            lhs = Rpoly(S, lf + lg, fg)                                  # read of the PRODUCT
            rhs = pshift(pmul(Km, Rpoly(S, lf, f), Rpoly(S, lg, g)), d)  # product of the READS
            if lhs != rhs: viol('R1-DMULT', ...)
```

`lhs` comes from `T.read_coeffs` applied to the schoolbook product polynomial;
`rhs` is built from the two factors' reads and `δ` computed from **split data only**
(`delta_of` reads `T.split(...)['s'][NR]`, never `T.constants`); the comparison is
exact dict equality, so no proportionality slack. `w(fg) = w(f)+w(g)` is scored as
a separate predicate rather than assumed. **This is a genuinely independent test of
the identity** — it does not presuppose (DMULT) anywhere. Its weakness is the
sample set, not the predicate: see **GAP 2**.

Same audit on the two sharp legs: R1-COB compares `Rpoly(S, lam, φ_rφ_s)` to
`{δ: a_r·a_s}` built from separately-read anchor constants (independent);
R1-UNIT builds the FULL grid, classifies every in-window pair
(`unit`/`zero`/`den0`), and only then applies the violating predicate
(`score_table`) — **no pre-filter**, which is precisely G3's repair, and tooth T4
plants a `zero` into a copy of the table and requires the *same* predicate to
report it (`len(probe) > len(sink)`). G3 is repaired correctly and falsifiably.

### (d) Hand-check of one R1-PSIK-LO row and one R1-PSIK-HI row

Read-only probe `/tmp/pe2/spot.py` (outside the repo; imports `grt_jc_probe` and
`grt_jc_r1_checks`, computes nothing new, prints the quantities).

**C2A (m = 1, NR = 2, E = 4, e_m = 2, g_m = 1).** Machine prints
`γ_{m+1} = 5, wΦ_m = 2, wΦ_NR = 10, G0 = 4`, window reps `[4,5,6,7]`,
`ψ_m` coefficients `(z̄-basis) [(0,1),(1,0)]`.

* Hand: `wΦ_NR = e_mg_mγ_{m+1} = 2·1·5 = 10` ✓ matches.
  `w Φ_1 = e_0g_0γ_1 = 2·1·1 = 2` ✓ (E = 4 = e_0e_1 forces e_0 = 2).
* **LO, `λ = G0 = 4`:** `λ − wΦ_NR = −6 < 0`, so `𝔦 ∩ gr_4 = in(Φ_2)·gr_{−6} = 0`
  since `w ≥ 0` on `O[x]`. `maxslot(4) = ⌊(⌊4/5⌋ − s_NR(4))/2⌋ = ⌊(0−0)/2⌋ = 0`
  (`s_NR(4) = l_1·4 mod 2 = 0`) — machine `maxslot = 0` ✓, and
  `𝑅_4(φ_4) = {slot 0}` ✓ (JC-ANCHMON(c)). `zero_cert(φ_4, 4) = False` ✓ — nothing
  certified dead at a line below `wΦ_NR`, exactly JC-PSIKER(ii)'s zero half and the
  R1-PSIK-LO predicate. All four window reps `4,5,6,7 < 10` ✓ (4 lines, matching the
  per-row print `psik lo 4`).
* **HI, `ν = 0`:** machine picks `λ = 12`, `ν = λ − 10 = 2 ∈ W`. Hand: `δ(10,2)`:
  `s_NR(10) = 0`, `s_NR(2) = 0`, `s_NR(12) = 0` ⟹ `δ = 0`. `a_ν = 𝑅_2(φ_2) = 1`.
  Predicted digit polynomial `a_ν·y^0·ψ_m(y) = {0:(0,1), 1:(1,0)}`; machine
  `R = [(0,(0,1)), (1,(1,0))]` ✓ **on the nose**. `w(Φ_2·φ_2) = 12 = 10+2` ✓
  (multiplicativity), `read = 0` ✓ (`ψ_m(z̄) = 0`), death CERTIFIED ✓.

**C2I (m = 1, E = 4, g_m = 2 — the row PE1's counter-instance sat on).**
`wΦ_NR = 2·2·5 = 20` ✓; LO reps `4,5,6,7` all `< 20` with
`λ − wΦ_NR ∈ {−16,−15,−14,−13}` ✓ (PE1's "C2I 4 < 20" reproduced);
HI at `λ = 20`, `ν = 0`, `a_0 = 1`, `δ = 0`, `R = {0:1, 1:1, 2:1} = ψ_m(y)`
(`g_m = 2` ⟹ `deg ψ_m = 2`) ✓, `read = 0` ✓, certified ✓.

**Both directions of JC-PSIKER's corrected range are confirmed numerically**, and
the R1-PSIK-HI predicate is additionally a live test of `(DMULT)` with a
non-monomial factor.

### (e) Cross-checks of other machine figures the note quotes at HEAD

Reproduced from R1-CEN this pass: `maxslot(G0) = 0` on **29/29** rows ✓;
C4H is the **unique** `e_m = 1` row (so §2.8(c)`[r1,G5]`'s "28 rows" is right) ✓;
C2I and C4I are the **only** `g_m = 2` rows and C2B/C3I are `g_m = 1` (so
§7 row 1's `[r1,G4]` correction is right, and "29 − 2 = 27 g_m = 1 stages" is
consistent) ✓; `c_π = 1` on exactly **9** rows, `≠ 1` on **20** ✓ (but see GAP 3
for the value set); R1-SURJ minimal-`k` ranges — degree 0 at `k = 0` on 28 rows and
`k = 2` on C4H, degree 1 `k ∈ [2,16]`, degree 2 `k ∈ [5,34]` ✓ exactly as §9.3
states; `197 = Σ_rows min(E,8)` ✓ (so R1-PSIK-HI's "all E classes per row, capped
at 8" is the honest description, and the §9.3 *prereg* row's "for EVERY residue
ν ∈ ℤ/E" is the un-capped wording — the cap is disclosed in the runner docstring
and the verdict cell).

**G6's restored parenthesis is verbatim-faithful:** the instrument's own row reads
`**328 certified / 0 zero-class / 0 FAILED** (606 skipped for non-integrality)`
(`GRTJC_PROBE_2026-08-08.md` line 223), which is exactly what §3.4 row 2 now
quotes. **And the note does NOT claim the r1 battery covers the 606** — it says the
opposite in three places ("have **no machine leg**", JC-BOX-8(i), and §9.3's "it
does NOT touch the one place r1 leaves a measurement owed"). The charge's premise
here does not land: G6 is applied honestly, and the previously-skipped stratum
remains a disclosed, unmeasured residue.

---

## §C WHAT SURVIVED THE PASS (beyond §A: re-checked, no defect found)

1. **JC-DOM, JC-GAUGE, JC-PER, JC-FIB, JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD** —
   spot-re-derived; PE1 had already cleared them and nothing r1 did disturbs them.
   JC-LOAD's `⟸` still rides §4.2's offset transport, now on (COORD-B)/(DMULT).
2. **G1 (W-6(ii) → `A_ν ≅ B_n`)** — correctly applied, with the strictness witness
   (`maxslot` growing along the `λ+kE` ladder) restated inside the clause and
   scored as R1-BND's census. The ladder columns reproduce (C2A `[0,0,1,1]`,
   C2D `[0,1,1,1]`, I4C `[0,0,0,0]` at `k ≤ 3` — the note correctly calls the last
   "slower but unbounded" rather than claiming growth within the printed window).
3. **G2 / FINDING JC-F2** — the `𝒜(T)` "degree-0 component" definition is struck in
   BOTH places PE1 found (§1 and W-7), replaced by the across-all-degrees reading,
   and escalated to a REVIEW-OWED finding with the upstream sources named
   (`GRW2_TIE_DESIGN` §S2.2, blueprint §S2.3, the brief). Correct, and the
   promotion of spanning from definition to theorem is real.
4. **G7 (§4.1 remark (a))** — the two unproved identifications are struck verbatim
   and replaced by exactly what is provable (same-line cancellation is definitional;
   the sharper `u = a_γa_{γ′}` is fenced on (DMULT)). J-B's authority is no longer
   imported. Clean, modulo GAP 1's status question for the sharper half.
5. **G8 (fence hygiene)** — the battery's own `T.constants`/`T.read` call sites are
   disclosed with the non-circularity argument, and I confirmed in code that
   `delta_of`/`constants()['delta']` is pure split data and that the gr-side
   quantities come from `read_coeffs`. The r1 runner obeys the same rule.
6. **JC-BOX-3's re-cut** — it now boxes the right risk (WHICH OBJECT / citation
   precision / what dies), and correctly notes that a numbering error would not by
   itself refute (DMULT). The standing printed-source Codex leg is still owed and is
   honestly still owed.
7. **The 22/28 byte-frozen record, the 14/6/9 instrument split, §6's one-directional
   cyclic law, and §9.2's two battery-driven findings** — unamended, no row
   re-scored, converse still declared FALSE with the 13 rows named. No gate fires or
   retires; no `.lean` touched by any r1 commit (verified: `85d5811`/`54904cc`/
   `f45b63c`/`66263ce` touch only `.md`, the r1 `.py`, and the r1 artifacts).

---

## §R RECOMMENDATION

**Not clean; 0 CRITICAL, 9 gaps, counter stays 0/2.** The r1 repair is a genuine
structural fix — every load-bearing new lemma survived independent re-derivation and
the two PE1 CRITICALs are gone — so the next round should be a *labelling and
footprint* round, not another restatement:

1. **GAP 1 is the one with content.** Either (i) re-label `(DMULT)`-exact as
   PROVED-IN-NOTE (by proving the ε-kit's unit system is multiplicative — the
   `a_{λ+μ} = a_λa_μ` fact JC-COB already asserts is the same statement), or
   (ii) cite only the up-to-a-line-wise-unit form and demote JC-COB's sharp `u =
   a_γa_{γ′}` and §4.1's replacement remark to MEASURED. Do not leave "CITED, not
   proved here" next to "a finding of the r1 battery".
2. **GAP 2** needs one added sample class with a genuinely multi-slot digit
   polynomial on both sides (the skipped `(Φ_{m+1}, Φ_{m+1})` pair, or
   `Φ_{m+1}·φ_γ` × `Φ_{m+1}·φ_{γ′}`), plus disclosure of the sample composition.
   Any new leg needs its own mini-seal.
3. **GAP 4(a)(c)** are two-sentence edits but they are the kind PE1 called
   "display defect that contradicts the note's own proof" — a THEOREM box grading
   OB-4 on a refuted input, and a remark asserting the pre-repair footprint.
4. **GAPs 3, 8** are one-number fixes (roster `c_π` value set; 10 families/10,330 or
   11/10,475). **GAPs 5, 6, 9** are three short unwritten steps (off-window
   transport of `ρ^B`/virtual anchors; the extension-is-the-literature's-valuation
   check plus additivity in JC-LOC; ideal transport along JC-GAUGE(iii)).
   **GAP 7** is bookkeeping (JC-BOX-4 is not "unchanged").
5. PE3 should re-open **GAP 1** first (it is the only remaining literature leg and
   everything coordinate-based still dies with it), then audit the added DMULT
   samples of GAP 2, then confirm the GAP 4 edits did not create new dangling
   references.

— GRTJC pass PE2, hostile verifier unit (fresh context), fixes nothing.
