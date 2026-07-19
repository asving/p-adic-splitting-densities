# Determination — the faithful scope of the order-≥2 `ind≤disc` CITE (2026-07-17)

**Prompt (Asvin, 2026-07-16):** "There should be only one interpretation that makes sense with the
rest of the paper … read through the paper with all the interpretations carefully and see which one
makes ALL the arguments go through. Feel free to work out small examples." This note resolves the scope
of the order-≥2 Montes CITE **myself** from GMN (arXiv:0807.2620v2) + worked examples, rather than asking.

## The question

The reduce-stability of the OM classifier rests on a Montes CITE of the form: *the develop-reads the
classifier performs on `g` are `< N` whenever `v_p(disc g) < N`* (Lean root form
`omReadValuation_lt_of_certLevel_fkeyed`, hyp `hbulk : zmodValuation p (N+1) g.discr < N`, conclusion
`GuardSuppR ∧ GuardSideR` = the hull-dot / on-side reads are `< N`). The **order-≥2** analogue reads
`g`'s φ_r-adic development coefficients as elements of the **unramified extension base** `O''`
(`childResidualExt` / `resUnitResidue`). Two candidate scopes:

- **(a) UNIVERSAL** — for *every* key ψ, the develop-reads of `g` against `liftKey ψ` are `< N`.
- **(b) ARISING-KEY-RESTRICTED** — only for keys ψ that **arise** in `g`'s OM tree (a repeated residual
  factor, `2 ≤ μ ∧ P^μ ∣ R_r`). This is what the Lean `ch.P`/`ch.μ` satisfy by construction.

## Determination: **(b)** is the unique interpretation consistent with GMN. Five reasons.

**1. The theorem's object IS the tree.** GMN's theorem of the index (Thm 4.18, line 4364, monic
separable `f`): `ind(f) = Σ_r ind_r`, with `ind_r` = the number of lattice points under the order-`r`
Newton polygon `N_r` **at the arising types** `t ∈ t_r(f)`. `N_r` is *defined only relative to an
order-`r` type* (an arising key φ_r; GMN §2.5, line 2174) — there is no "Newton polygon against an
arbitrary polynomial." So the theorem bounds reads **on arising keys** and is silent on non-arising ones.
The disc bound follows: `ind(f) ≤ ½ v_p(disc f)` via the Ore–Montes relation
`v_p(disc f) = 2·ind(f) + v_p(disc of the maximal order)` (disc-conductor); hence `ind(f) ≤ v_p(disc f)`.

**2. The universal reading is provably FALSE** (Example A, exact-arithmetic verified). `g = X²+X+p⁵` is
separable mod `p` (roots `0, −1` distinct) ⇒ its OM tree is trivial, both linear factors lift by Hensel,
**no order-1 key arises** (`t_1(g)=∅`), and `v_p(disc g)=0`. But developing `g` against the *non-arising*
key φ=X gives digit `p⁵`, valuation `5`. A universal CITE would assert `5 < N` under `0 < N` — false.
A non-arising key has no Newton-polygon interpretation, hence no index bound. This is exactly the
recurring **over-generalization** failure mode (same shape as the two earlier false-axiom catches).

**3. The arising-key reading HOLDS at every order, with margin** (Examples B, C verified).
- **B** `g = X²+2` /Q₂: `g mod 2 = X²` (repeated ⇒ arising key φ=X, order 1); read val `1 ≤ v_2(disc)=3`.
- **C** `g = X⁴+4` /Q₂ `= (X²+2X+2)(X²−2X+2)`, two ramified quadratics. Tree descends: order-1 polygon
  against φ₀=X has slope −1/2, residual `(y+1)²` **repeated** ⇒ **order-2** key φ₁=X²+2. φ₁-adic
  development `g = φ₁² − 4φ₁ + 8`: order-2 reads `{v(8),v(−4),v(1)} = {3,2,0}`, `max = 3 ≤ v_2(disc)=14`.

  The reads on the lower hull / on the side (the ones the reader reads, and the ones that determine the
  residual polynomials) have valuation `≤ v_p(disc g)`. Coefficients **above** the hull (val `> v_p(disc)`)
  are **inert**: they touch no Newton polygon or residual, so truncating `g mod p^N` (any `N > v_p(disc)`)
  leaves the whole tree unchanged. (Sanity probe: perturbing C by `2^k·junk`, `k ≥ v_2(disc)=14`, does not
  move `v_2(disc)` — the boundary is exactly `v_p(disc)+1`, matching "reads to precision `v_p(disc)+1`.")

**4. Scope over `O''` is INSIDE GMN's frame — no new content.** GMN fixes `K` = a finite extension of
`Q_p` (finite residue field, mixed char 0; line 482, abstract line 9). The order-≥2 tower lives over
`O''` = the unramified extension of the base by the residue-degree-`f₁` residual factor — itself a finite
**unramified** extension of `Z_p`, i.e. a p-adic field in GMN's *exact* scope. The theorem of the index
applies verbatim over `O''`. The order-≥2 CITE is therefore the **same** GMN theorem re-instantiated at
the next base, NOT a stronger claim.

**5. This matches the Lean guard structure exactly.** The root CITE quantifies over `hullDots`
(`GuardSuppR`) and on-side coefficients (`GuardSideR`) — precisely the lower-hull / on-side reads of (3) —
under `hbulk : v_p(disc g) < N`. The `_fkeyed` suffix + the `ch.P`/`ch.μ` arising-key restriction
(`2 ≤ μ ∧ P^μ ∣ R_r`, an `OMCell.Child` invariant) encode (1)–(2)'s scope. The order-≥2 CITE is the
identical statement with the coefficients read in `O''[X]` via `childResidualExt` / `resUnitResidue`.

## Conclusion (what to declare)

Declare the order-≥2 CITE as the **hull-dots / on-side, arising-key-restricted, `hbulk`-guarded
(`v_p(disc g) < N`)** statement over the unramified extension base `O''` — the verbatim order-≥2 instance
of GMN's theorem of the index. **NOT** the universal-∀-key form (Example A refutes it). No confirm needed
from Asvin: this is forced by the paper's index theory + the three worked examples, not a judgment call.

**Faithfulness triple-check (for the guardian + the axiom ledger):**
- *statement-map NOT-MORE*: asserts only "arising-key hull/on-side reads `< N` under `v_p(disc)<N`" — no
  rationality/uniformity/all-prime/closed-form smuggled; the disc bound is GMN Thm 4.18 + Ore relation.
- *statement-map NOT-LESS*: non-vacuous — Examples B, C exhibit arising keys with genuine reads the CITE
  governs (it is not trivially true on an empty read-set for wild `g`).
- *mutation*: dropping the arising-key restriction (→ universal) BREAKS on Example A (`X²+X+p⁵`); dropping
  `hbulk` or widening past hull dots BREAKS on the inert-coefficient probe (C perturbed at `2^{≥14}`).

## The Lean shape (for wave 5 — NOT declared yet, and WHY not)

A subtlety that fixes the Lean form (found while scoping the declaration, 2026-07-17; **corrected**
after building the level-drop hom, build #70). Naively one might guard "reads `< N`", but note that over
`Oring p M g = ZMod(p^M)[X]/(g)` **every nonzero element already has `pval < M`** (`p^M = 0`;
`ChildResidualExt.pval_lt_N_of_ne_zero`). The subtlety is that the reads and the drop live at **two
different levels**: the `developExt` reads happen at the **source** level `M = N+1` (where a nonzero digit
CAN have `pval = N`), and reduce-stability drops to the **target** level `N`. The genuine guard is
therefore "`pval` (at level `N+1`) `< N`" = "the read survives the drop to level `N`" — **non-vacuous**
(it excludes exactly the boundary `pval = N` nonzero digits, which `θ` would send to `0`). This is the
per-digit `resUnitResidue`-compatibility `hcompat` that `ChildResidualExt.childResidualExt_transport`
(wave 2) abstracts, instantiated at the **concrete level-drop hom** `θ : Oring(p,N+1,g') → Oring(p,N,g)`
(now built, `LevelDrop.levelDropHom`, #70). `hcompat` splits into: **(2a)** a CITE-FREE core lemma
`resUnitResidue_N(θ x) = φ(resUnitResidue_{N+1} x)` GIVEN `pval_{N+1} x < N` (analogue of
`zmodUnitResidue_reduce_stable`; provable via `resHom_natural_levelDrop` #70 + `pval(θx)=pval(x)` below
cutoff + witness-independence); and **(2b)** the CITE proper — for ARISING keys, `∀ t, pval_{N+1}(digit_t)
< N` under `hbulk : v_p(disc f) < N` (the GMN index bound). Only **(2b)** is imported.

Faithful CITE shape (to declare in wave 5, once `θ` and the box↔`h` discriminant threading exist):
```
-- [CITE] GMN Thm 4.18 / theorem of the index — ORDER-≥2 instance over the unramified base O''.
-- For an ARISING extension key Φ = liftKeyExt ψ (ψ a REPEATED residual factor of the parent, μ ≥ 2)
-- and the concrete level-drop hom θ, the extension child residual is level-drop-stable, PROVIDED
-- hbulk : v_p(disc f) < N   (f = the ORIGINAL box being classified — the SAME disc that bounds ALL
-- orders, since ind(f) = Σ_r ind_r ≤ v_p(disc f) is one total bound over every order r).
axiom childResidualExt_reduce_stable_fkeyed … (hΦarise : Φ = liftKeyExt … ψ) (hμ : 2 ≤ μ)
    (hbulk : «v_p(disc f)» < N) :
    childResidualExt (θ-image, level N) = (childResidualExt (level N+1)).map φ
-- ≡ discharges `childResidualExt_transport`'s `hcompat` for the concrete θ.
```
**Why not declared now:** the statement must reference (i) the level-drop hom `θ` (`Oring(N+1,g')→Oring(N,g)`,
does not exist in-repo yet — wave-5 engineering, flagged in `childResidualExt_transport`'s doc) and (ii)
how the original box `f`'s discriminant threads to the ext reader's `h`. Declaring against **guessed**
plumbing is precisely the mis-port failure mode this whole exercise fights. The interpretation is FIXED
(arising-key, `hbulk`-guarded, `θ`-stability); wave 5 declares it against real objects — a mechanical
step then, not a re-litigation. An atomic "reads `< N`" CITE is NOT an option: it is vacuous over `O''`.
