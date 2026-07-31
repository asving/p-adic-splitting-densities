# M08-cl6-general — problem brief: the CL-6 count-law package (`PolyGeomLaws`) at general n

**Status of this file.** Neutral, self-contained problem statement. It contains no
approach material. Sources: `lean/LeanUrat/MovesS/Defs.lean` (the structure),
`lean/LeanUrat/MovesU/BridgeKernels.lean` (the obligation row),
`lean/LeanUrat/MovesS/N2PolyGeom.lean` + `lean/LeanUrat/MovesU/SynK2_cl6N2.lean`
(the n = 2 record), `lean/LeanUrat/MovesV/V7_pgLaws.lean` (the corpus supply
theorem), and the project note `lean/notes/MOVES_2026-07-24.md` (the ledger row
CL-6 this formalizes).

## 0. Setting

The project formalizes a uniformity theorem: for each degree n and each *splitting
type* σ (a multiset of pairs (e, f) of positive integers with Σ e·f = n), there is
ONE rational function R_σ ∈ ℚ(q) such that for every prime p, the Haar density of
monic degree-n polynomials over ℤ_p whose irreducible factors over ℚ_p have
ramification indices and residue degrees given by σ equals R_σ(p). The proof
organizes p-adic factorization as a finite-state transition system per "block"
(the blocks come from the residual factorization; states are partial
Newton-polygon / Okutsu–Montes data), and solves each block by a Neumann/Cramer
matrix solve over ℚ(q). Every matrix entry is carried in a normal form

    (count polynomial T) · (count polynomial S) · (geometric factor G),

and the present obligation — ledger row CL-6, "CTS-M(iv)-POLY" — is the package of
laws pinning the two count polynomials to actual counts, with degree bounds. The
n = 2 instance is discharged modulo a one-line repair executing concurrently
(see §4); the obligation here is the package **at every n**.

## 1. The Lean statement

The obligation is the `cl6` field of the kernel ledger
(`MovesU/BridgeKernels.lean:254`), stated over the abstract carrier pack
`C : UCarriers n` (which binds a table `C.T : MovesS.TableShape n`, a measured
side `C.MS : MovesS.MeasuredSide C.T`, and rational burdens
`C.RB : MovesS.RatBurdens C.T C.MS`):

```lean
cl6 : Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)
```

with (`MovesS/Defs.lean:411`):

```lean
structure PolyGeomLaws (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) where
  tCount : ∀ e (τ : T.State e), T.Out e τ → ℚ → ℕ
  tcount_val : ∀ e (τ : T.State e) (o : T.Out e τ), ∀ q₀ ∈ M.Pools,
    (RB.tgP e τ o).countT.eval q₀ = (tCount e τ o q₀ : ℚ)
  scount_val : ∀ e (τ : T.State e) (o : T.Out e τ), ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ →
    (RB.tgP e τ o).countS.eval q₀
      = ∑ c ∈ M.cells e τ o, ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)
  tcount_deg : ∀ e (τ : T.State e) (o : T.Out e τ),
    (RB.tgP e τ o).countT.natDegree ≤ T.Wloc e τ o
  scount_deg : ∀ e (τ : T.State e) (o : T.Out e τ),
    (RB.tgP e τ o).countS.natDegree ≤ T.Wstate e τ
```

The presentation type it constrains (`MovesS/Defs.lean:322`; `Qq := RatFunc ℚ`):

```lean
structure PolyGeom where
  countT : Polynomial ℚ
  degBoundT : ℕ
  degT_le : countT.natDegree ≤ degBoundT
  countS : Polynomial ℚ
  degBoundS : ℕ
  degS_le : countS.natDegree ≤ degBoundS
  geom : Qq
  qpow : ℕ
  geomDenoms : Finset ℕ+
  geom_denom_dvd : geom.denom ∣
    Polynomial.X ^ qpow * ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a : ℕ))

noncomputable def PolyGeom.val (P : PolyGeom) : Qq :=
  algebraMap (Polynomial ℚ) Qq (P.countT * P.countS) * P.geom
```

## 2. Unfolded to standard mathematics

Fix n. A *pack* consists of three layers of data (all of which the obligation
takes as given — at general n the pack itself is a concurrent construction
obligation of the project; see §5).

**(a) Table** T: for every "block size" e ∈ ℕ (all of ℕ, not just 1..n), a finite
set State_e of states; for each state τ a finite set Out_{e,τ} of outcomes; each
outcome carries combinatorial data (a nonempty list of members, each with a size,
a base-change index, and either a *verdict* — a pair (e′, f′) with e′·f′ ≤ n — or
a continuing state); and two weight functions fixed with the table,
W_loc : (e, τ, o) ↦ ℕ and W_state : (e, τ) ↦ ℕ.

**(b) Measured side** M: a set Pools ⊆ ℚ, every element of the form p^δ (p prime,
δ ≥ 1), closed under q₀ ↦ q₀^δ, infinite; for each q₀ ∈ Pools and level N ∈ ℕ a
finite nonempty set Box(q₀, N) ("level-N residue boxes"); for each (e, τ) a
finite set Cell(e, τ) with a map cellOut : Cell(e, τ) → Out_{e,τ} (write
cells(o) := cellOut⁻¹(o) for the fiber), a level ℓ(c) ∈ ℕ per cell, and an
instance set Inst(c, q₀, N) ⊆ Box(q₀, N); an activity predicate Act(q₀, e, τ);
and measured row values ρ(e, τ, o, q₀) ∈ ℝ.

**(c) Rational burdens** RB: for every row (e, τ, o) a presentation
P = (A, B, G) with A, B ∈ ℚ[X], recorded degree bounds pinned by RB's own laws to
deg A ≤ W_loc(e, τ, o) and deg B ≤ W_state(e, τ), and G ∈ ℚ(X) whose (reduced)
denominator divides X^b · ∏_{a ∈ 𝒜}(1 − X^a) for some b ∈ ℕ and finite
𝒜 ⊆ ℕ_{≥1}; the value val := A·B·G is defined at every q₀ ∈ Pools (its reduced
denominator does not vanish there), and — RB's interpolation law — for
non-split-routed outcomes, val(q₀) = ρ(e, τ, o, q₀) at every pool point.

**The obligation** is to produce, for the pack at each n:

* (data) a function t : (e, τ, o, q₀) ↦ ℕ, and
* **(1) T-value law** — for ALL e ∈ ℕ, all τ, o, and every q₀ ∈ Pools:
  A_{e,τ,o}(q₀) = t(e, τ, o, q₀). Since t is otherwise unconstrained, (1) says
  exactly: **A takes values in ℤ_{≥0} at every pool point** — with no activity
  guard and no restriction of e to the operative range 1..n.
* **(2) S-census law** — for all e, τ, o and every q₀ ∈ Pools at which
  Act(q₀, e, τ) holds:
  B_{e,τ,o}(q₀) = Σ_{c ∈ cells(o)} #Inst(c, q₀, ℓ(c)) — **the countS factor
  evaluates to the outcome's cell-fiber census, each cell counted at its own
  level**.
* **(3)/(4) degree laws** — deg A ≤ W_loc(e, τ, o), deg B ≤ W_state(e, τ). These
  two follow immediately from RB's recorded bounds and pins (the structure's own
  docstring records this: "Derivable from `degT_le` + `tg_degT` … so
  instantiation is free").

Note what is NOT constrained: only the product A·B·G is interpolated by RB, so
(1) and (2) are genuine additional laws on how the product is factored.

## 3. The intended instance (what the counts mean)

At general n the pack is not yet constructed in Lean; the intended instantiation,
fixed by the project's design notes (`MOVES_2026-07-24.md` §V, §S.3), is:

* Pools = all prime powers q₀ = p^δ. Box(q₀, N) = the level-N coefficient boxes:
  residue classes mod π^N of (tuples of coefficients of) monic polynomials over
  the ring of integers O of the unramified extension of ℚ_p of degree δ (residue
  field F_{q₀}), π = p.
* A state τ at block e is a partial Okutsu–Montes datum for a degree-e block: an
  order-r type in the sense of Guàrdia–Montes–Nart ("Newton polygons of higher
  order in algebraic number theory", Trans. AMS 364 (2012); the project's pinned
  external reference, see `docs/GMN_citations.md`) together with pending
  refinement data — Newton-polygon sides and residual-polynomial factorization
  information along the tower with invariants (e_i, f_i, h_i).
* A cell c of τ is a residue-digit configuration realizing τ at level ℓ(c);
  Inst(c, q₀, ℓ(c)) is the set of level-ℓ(c) boxes satisfying it. So the law-(2)
  right-hand side is a **count of residue configurations of
  Newton-polygon/Okutsu–Montes strata of degree-n p-adic polynomials**.
* The T-count of a row is the number of fresh digit assignments (one transition
  window) from a fixed representative of τ realizing outcome o; ρ is the
  height-resummed measured mass of the row.

The governing ledger row, verbatim (MOVES note, lines 12129–12132): "K_e/b_e^{term,fin}
entries: T is one polynomial of degree ≤ W_loc(m) and each cell size one
polynomial of degree ≤ W_state(s), valued correctly at every prime power —
CTS-M(iv)-POLY (CL-6, with V.2's EXPONENT-MAP AUDIT)". The audit clause
(MOVES 8378–8384): "Every norm/trace/ratio/collision exponent map in every
table's evaluation chain is audited for congruence factors (e.g. the image size
of t ↦ t^a on F_{q^g}ˣ is (q^g − 1)/gcd(a, q^g − 1)); 'triangular/monomial
shape' alone is NOT accepted as a polynomiality argument — each such factor
either cancels against a displayed cell-size factor or splits the cell into
displayed congruence sub-cells with their own labels."

The note's own status for this row (V.3(iv)): the T-half mechanism is displayed
("twisted-cell constancy makes each (m, o, β) count a product of cell sizes and
fiber counts over the displayed strata, polynomial after the EXPONENT-MAP
AUDIT"), but "per-entry closed forms are the table-build deliverable,
gate-sealed at V.6" — i.e. open at general n, with numeric gates executed at
n = 3 only.

## 4. What is already proved in the corpus

* **General-n supply theorem** (`MovesV/V7_pgLaws.lean:91`,
  `polygeom_count_laws`, proved): for ANY pack, IF
  (hTCount) ∀ e τ o, ∀ q₀ ∈ Pools, ∃ k ∈ ℕ, A(q₀) = k, AND
  (hSCount) the law-(2) equality holds at all active pools,
  THEN `Nonempty (PolyGeomLaws T M RB)` (with t := the evaluated counts and the
  degree legs from RB). Its docstring records the adjudication ADJ-4: at
  arbitrary-pack generality the two value laws are NOT derivable — rescaling
  countS ↦ 2·countS, geom ↦ geom/2 preserves every RatBurdens law and breaks
  (2), and nothing pins countT's values.
* **n = 2 record**: the n = 2 pack exists and is sorry-free
  (`MovesS/N2Carriers.lean`, `MovesS/N2PolyGeom.lean`).
  `n2_countLaws_block2` (`MovesU/SynK2_cl6N2.lean`, proved): both count laws
  hold at the operative block-2 layer (all counts ≡ 1 there).
  `n2_polyGeomLaws_isEmpty` (same file, proved): the as-built n = 2 pack
  REFUTES the package — at a padding row (block e = 1, a duplicate outcome
  carrying no mass) the padding presentation carries countS = 1 against an
  empty cell fiber, so (2) demands 1 = 0. The failure is value-law-invisible
  (that presentation's val is 0 either way). The val-preserving repair
  (padding countS := 0) is executing concurrently (sign-off queue item 10);
  after it the n = 2 instance discharges. Caveat: the n = 2 measured side is
  degenerate (every cellInst a singleton at level 0, Act ≡ True), so n = 2
  exercises no genuine counting content.
* Degree legs (3)/(4): free from RB's fields, at any pack (structure docstring;
  used by both the n = 2 probe and `polygeom_count_laws`).

## 5. What a proof must deliver

For each n, either:

**(I)** the laws (1) and (2) for the general-n pack once its carriers are fixed
(the pack construction is a concurrent project obligation; `cl6` is carried as a
named hypothesis row until then), or

**(II)** — the standalone form usable by the pack builder — the two counting
theorems over the intended carriers of §3: (i) each row's T-count function
q₀ ↦ (one-window digit count from a representative) agrees on the pool with ONE
polynomial in q₀, ℕ-valued there, of degree ≤ W_loc; (ii) each outcome's
cell-fiber census q₀ ↦ Σ_{c ∈ cells(o)} #Inst(c, q₀, ℓ(c)) agrees at active
pools with ONE polynomial of degree ≤ W_state; together with the compatibility
that the measured row value factors as (T-count poly)·(census poly)·G with G in
the stated geometric denominator class (so that the pack can be BUILT with these
count factors while keeping RB's interpolation law).

Cautions for faithfulness: the quantifiers run over ALL e ∈ ℕ (padding/junk
rows included — this is exactly where the n = 2 as-built pack failed); law (1)
has no activity guard (rows whose defining strata are empty at q₀ must still
evaluate to a nonnegative integer — the intended semantics is count 0 there);
Pools includes the wild primes p ≤ n and all base-change legs q₀ = p^δ, so "one
polynomial, valued correctly at every prime power" is a p-uniform claim with no
excluded primes.
