# Blueprint — piece 4: the changing-field growing tower (2026-07-18)

**Status: DESIGN, for Asvin's steer (blueprint-first rule). No Lean written off this yet.**

Wave 5 so far (builds #70/#71/#72, all green + guardian-clean) proved the order-≥2 reduce-stability *at a
single fixed extension base* `g`, reduced to exactly one input (the per-digit read cutoffs = the CITE).
Piece 4 is the remaining architectural step: the OM tower whose residue field GROWS at each descent.

## The obstacle (the wave-4 wall, precisely)

`classifyGenuineExtAux` (build #69) threads a SINGLE fixed `g : (ZMod(p^N))[X]`: at a node the child's
residual factor `ch.P` is fed back over the **same** `resField p N g hN`. This is deliberate — it keeps
the residue-field TYPE out of the `Nat.strongRecOn` motive:
```
motive := fun _ : ℕ => (r : ℕ) → (Ψ : (resField p N g hN)[X]) → (μ : ℕ) → ClusterShape
```
so the field type is a closure CONSTANT, never transported ⇒ no `eqRec`-on-motive. The genuine Montes
tower breaks this: level `r`'s residual factor `ψ_r` is irreducible over `resField(g_r)`, and descending
adjoins its root, so level `r+1` lives over a STRICTLY LARGER field `resField(g_{r+1}) ⊋ resField(g_r)`.
Put a growing field type into the recursion argument and the motive's type varies with the recursion
variable ⇒ the `eqRec`-on-motive pathology wave 4 was built to avoid.

Key facts constraining the design:
- The accumulated residue field after `r` descents has degree `f_0·f_1·…·f_{r-1}`, which **divides `n`**
  (since `∏ e_i f_i = n`). So every level's residue field is an unramified extension of `Q_p` of degree
  `≤ n` — all embeddable in ONE fixed unramified extension of bounded degree.
- The tower DEPTH is finite and bounded: `≤ ind(f) ≤ v_p(disc f) < N` under `hbulk` (GMN Cor 4.19 /
  theorem of the index). So the tower is a finite structure, depth known to be `< N`.
- My #70/#71/#72 machinery is parameterized by an ARBITRARY monic `g` with `ḡ` irreducible — so it
  already applies at EACH level's `g_r` unchanged. Whatever represents "the level-`r` base" as a single
  `g_r : (ZMod(p^N))[X]`, the reduce-stability is already proved there.

## The design space (three options)

### Option A — FLATTEN: changing `g_r` over the fixed base `ZMod(p^N)`
Represent level `r`'s base by a single `g_r : (ZMod(p^N))[X]` (defining the accumulated degree-`f_0…f_{r-1}`
unramified extension). The child's `g_{r+1}` is the defining poly of `resField(g_r)[X]/(ψ_r)` re-expressed
over `ZMod(p^N)`.
- **Pro:** reuses #70/#71/#72 verbatim at each `g_r`; single base ring `ZMod(p^N)`.
- **Con:** the incoming factor `Ψ_r : resField(g_r)[X]` still has a type varying with `g_r` ⇒ the
  motive pathology is NOT solved, only relocated. Needs the "re-express `resField(g_r)[X]/(ψ)` over
  `ZMod(p^N)`" construction (a resultant/tower-collapse), itself nontrivial.
- **Verdict:** maximizes reuse but does not by itself defeat the wall.

### Option C — FIXED AMBIENT FIELD (recommended)
Fix ONE ambient unramified extension `F := F_{p^{D}}` with `D` a common multiple of every possible
residue degree `≤ n` (e.g. `D = n!` or `lcm(1..n)`; `D` depends only on `n`, NOT on `p` or the tower).
Every level's residue field is a SUBFIELD `resField(g_r) ↪ F`, and every residual factor is carried in
`F[X]`. The recursion motive becomes **field-CONSTANT**:
```
motive := fun _ : ℕ => (r : ℕ) → (Ψ : F[X]) → (μ : ℕ) → ClusterShape
```
exactly the type-uniformity wave 4 wanted but couldn't get with a growing field. Tower "growth" = the
relevant subfield of the fixed `F` grows; the AMBIENT type never changes ⇒ no `eqRec`.
- **Pro:** kills the motive pathology at the root (single fixed type); the recursion is then structurally
  the wave-4 recursion with `F` in place of `resField(g)`. Depth bound `< N` gives termination.
- **Con:** must (i) construct `F` + the degree bound `f_0…f_{r-1} ∣ n ⟹ ≤ D`; (ii) thread the embeddings
  `resField(g_r) ↪ F` and prove the residual factors genuinely land in the correct subfield (faithfulness:
  the `F[X]`-representation must equal the true Montes residual, not just "some poly over `F`"). (ii) is
  the real work — it is the faithfulness crux, and it is where the order-≥2 CITE + the `f↔h` discriminant
  threading attach (the reads are bounded in `F` because they are bounded in each `resField(g_r) ⊆ F`).
- **Verdict:** cleanest for Lean's type theory; recommended. The embedding-faithfulness is new math but
  bounded and honest (not a citation).

### Option B — FINITE EXPLICIT TOWER (fallback)
Make the tower explicit DATA of bounded length `D`: a `Fin D`-indexed family `(g_r, ψ_r, μ_r)` with
propositional coherence (`g_{r+1}` extends `resField(g_r)` by `ψ_r`) and a terminal marker. Classification
reads this finite structure directly — no recursion whose motive carries a varying type.
- **Pro:** sidesteps motive issues entirely (no recursion over a growing type — it's a fixed-length fold);
  depth bound `< N` supplies `D`; mirrors how the order-≤1 classifier already bounds depth by budget.
- **Con:** the coherence conditions are dependent (each `g_{r+1}`'s type/field depends on `g_r`), so the
  family is a Σ-telescope — awkward to build and to prove `#print axioms`-clean; still faces per-level
  varying types, just as data rather than in a motive.
- **Verdict:** viable fallback if Option C's embeddings prove too heavy.

## Recommendation

**Option C (fixed ambient field `F = F_{p^{n!}}`).** It is the only option that removes the varying-type
motive obstacle at the root rather than relocating it, and it reduces piece 4 to the wave-4 recursion over
a fixed `F` plus ONE new-math obligation: the subfield-embedding faithfulness (each level's residual genuinely
lives in `resField(g_r) ⊆ F`). That obligation is exactly where:
- the **order-≥2 CITE (2b)** attaches — the reads are `< N` because bounded in each `resField(g_r) ⊆ F`
  (GMN index bound, arising-key scope, resolved 2026-07-17);
- the **`f↔h` discriminant threading** attaches — `hbulk : v_p(disc f) < N` bounds the reads at every
  level uniformly (one disc bound for all orders, per Thm 4.18).

## Open questions for Asvin (the steer)

1. **Ambient-field choice:** `F = F_{p^{n!}}` (simple, wasteful degree) vs `F_{p^{lcm(1..n)}}` (tighter) vs
   building `F` lazily as the actual accumulated field. Recommend `n!` for simplicity — the degree only
   affects an intermediate type, not the final rational-function output. Agree?
2. **Is Option C's embedding-faithfulness the right new-math target, or do you see a way to keep Option A's
   reuse while defeating the motive wall (e.g. a tower-collapse resultant that is cleaner than I think)?**
3. **Scope for THIS push:** build the Option-C skeleton (fixed `F`, field-constant recursion, CITE declared)
   and leave embedding-faithfulness as a scoped obligation; OR do the full thing including embeddings?

Until steered, I will NOT write tower Lean — the ambient-field + embedding decision is architural and
expensive to redo, exactly the kind of choice to fix before formalizing.
