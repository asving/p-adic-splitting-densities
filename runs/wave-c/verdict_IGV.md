# UNIT IGV — VERDICT: THE IGUSA AXIS OPENS — the MASTER LAW for the per-depth
census is DERIVED in closed form (`Z_m(t) = ∏_{j=1}^m (1−s^jt^{j−1})/(1−s^jt^j)`,
depending ONLY on `m = min(n₁,n₂)`) and verified INTEGER-EXACTLY on 17 box
configurations through `m = 4`; in LEAN the MIN-REDUCTION lands pure Lean-core
(every box value = the diagonal reduced census at `min(n₁,n₂)` × an exact cylinder
factor, via `Res(f,g) = Res(f, g mod f)` over the truncation ring) and the
`min = 1` law closes COMPLETELY at every degree, every level, with its depth-density
`ZcURLim` fired outright — while the `m ≥ 2` diagonal values and the vis-restriction
honestly do NOT land in Lean (the exact named remainder) (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG61.lean` (665 lines, ZERO sorries,
zero errors, zero warnings; 17 AxCheck footer rows) + the numeric instrument
`runs/wave-c/igv_battery.py` with `igv_battery_heavy.log`.
**Axiom fence, machine-exact: ALL SEVENTEEN rows PURE Lean core
`{propext, Classical.choice, Quot.sound}`** — no B.42, no C.33, no
`AX_cellRecursion` anywhere in the file.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG61.lean` (final run: exactly the 17
footprint infos, nothing else); targeted `lake build Uniformity.ChapI.IFCG61` GREEN
(8967 jobs); sanctioned aggregator import appended after IFCG60's line, aggregator
`lake env lean Uniformity/ChapI.lean` GREEN (exit 0).  `I10RungLift3W.lean`
untouched.  NO git operations.

## ★★★ THE MASTER LAW (mathematics of record — the answer to charge item 1)

For random monic pairs `(f, g)` of degrees `(n₁, n₂)` over ANY DVR `O` with residue
cardinality `q`, with `m := min(n₁,n₂)`, `s := 1/q`:

    Σ_v P[v(Res(f,g)) = v]·t^v  =  Z_m(t)  =  ∏_{j=1}^{m} (1 − s^j t^{j−1})/(1 − s^j t^j)

— **the depth distribution depends ONLY on `m`** (and `q`); box form:
`#depthPairSet(n₁,n₂,L,v) = [t^v]Z_m(t)·q^{(n₁+n₂)L}` exactly for `v < L`; each
`P_v` is a polynomial in `s`; the tail generating identity
`Σ_m Z_m(t) w^m = ∏_{k≥0}(1−sw(st)^k)/(1−w(st)^k)` (so `Z_m = (s;st)_m/(st;st)_m`,
a `q`-Pochhammer ratio); mean `E[v(Res)] = Σ_{j=1}^m 1/(q^j−1)`.  Instances:
`m = 1`: `P_v = (1−s)s^v` (the (1,1) law at EVERY degree pair); `m = 2`:
`P₁ = s(1−s)²`, `P₂ = (1−s)s²(2−s)`, `P₃ = 2(1−s)²s³`, `P₄ = (1−s)s⁴(3−2s)`, GE-form
`P[π^v ∣ Res] = s^v(1 + ⌊v/2⌋(1−s))`.

**Derivation** (elementary, finite-level, DVR-agnostic — full chain in the file
docstring): (1) THE MIN-REDUCTION: for monic `f`, `Res(f,g) = ∏_{f(α)=0} g(α)`
depends on `g` only through `g mod f`, and `g ↦ (quot, rem)` is a level-wise measure
bijection ⇒ min-only dependence; (2) NORM FORM: `∏ g(αᵢ) = N_{O[x]/(f)}(g mod f)`
with `g mod f` uniform on `A = O[x]/(f)`; (3) LOCALIZATION: `A` splits by
coprime-factor Hensel along `f̄`'s residual factorization, the local pieces
independent-uniform, the norm multiplicative; (4) THE LOCAL PEEL: `r`-adic
Weierstrass preparation — proved at finite level as a coprime-Hensel counting
bijection `{ρ : v_r(ρ̄) = c} ≅ {P monic, P̄ = r^c} × {U : gcd(Ū,r) = 1}`, no power
series — gives the recursion `B_e(1−(st)^{δe}) = Σ_{c<e}(s^δ)^c(1−s^δ)(t^δ)^c B_c`,
solved `B_e = (s;st)_e/(st;st)_e`; (5) ASSEMBLY: the multiplicative statistic of a
random monic `f̄` over the irreducibles of `F_q[x]` Euler-factorizes; the `F_q[x]`
zeta `∏_δ(1−y^δ)^{−I_δ} = (1−qy)^{−1}` collapses the product; the `q`-binomial
theorem extracts `Z_m`.  **Literature status: derived independently here; the result
is plausibly classical (Igusa zeta of the resultant genre) — novelty NOT claimed,
flagged for lookup** (the repo's FoCM reference pdf is the OM-factorization paper,
not this).

**★★ THE BATTERY — 17/17 INTEGER-EXACT PASS** (`igv_battery.py`; exhaustive box
enumeration, exact Sylvester determinants over ℤ, predictions as exact `Fraction`s):
m=1: (1,1,p3,L3), (1,2,p2,L3), (1,2,p3,L2), (1,3,p2,L2) · m=2: (2,2,p2,L4),
(2,2,p2,L5) [v ≤ 4], (2,2,p3,L2), (2,3,p3,L2), (2,3,p2,L4) [v ≤ 3], (2,4,p2,L2) ·
m=3: (3,3,p2,L3), (3,3,p2,L4) [16.7M pairs, v ≤ 3], (3,3,p3,L2), (3,4,p2,L2),
(3,4,p2,L3) · m=4: (4,4,p2,L2), (4,5,p2,L2).  Every exact-`v` count AND every
GE-tail matched as an exact integer.  Min-only dependence confirmed at m = 2, 3, 4.

## ★★★ THE LEAN HEADLINES (`IFCG61.lean`, all pure Lean core)

    theorem card_depthPairSet_reduce :          -- ★★ THE MIN-REDUCTION COUNT
      0 < n₁ → n₁ ≤ n₂ → v < N →
      #depthPairSet(n₁,n₂,N,v) = #redDepthPairSet(n₁,N,v) · q^{(n₂−n₁)N}
                                                -- NO irreducibility hypothesis
    theorem card_depthPairSet_swap :            -- ★ the (n₁,n₂) symmetry
      #depthPairSet(n₁,n₂,N,v) = #depthPairSet(n₂,n₁,N,v)
    theorem card_depthPairSet_one_right/_left : -- ★★ THE min = 1 LAW, EVERY DEGREE
      #depthPairSet(1,n₂,N,v) = (q−1)·q^{(1+n₂)N−v−1}    (1 ≤ n₂, v < N)
    theorem zcURLim_depthDensity_one_right/_left : -- ★★ the density ZcURLim OUTRIGHT
      ZcURLim (fun O π M => #depthPairSet(1,n₂,M,v)/q^{(1+n₂)M})   -- (X−1)/X^{v+1}
    theorem zcURLim_depthDensity_of_reduced :   -- ★ general (n₁,n₂) ⟸ diagonal
      ZcURLim (reduced diagonal density at n₁) → ZcURLim (depth density at (n₁,n₂))

Supporting cast: `mixDepth_eq_iff` (the class-level exact-depth reader — no lifts,
no irreducibility), `classRes_eq_redRes` (★★ `Res(f,g) = Res(f, g mod f)` at pinned
sizes over the truncation ring — mathlib's `resultant_add_mul_right` + the monic
size-drop `resultant_add_right_deg`), `divSplit` (the explicit division bijection,
roundtrips by `monicPoly_coeff_self_ring` + `div_modByMonic_unique`),
`mixDepth_swap` (`resultant_comm`, sign a unit), `redRes_one` (`redRes` at size 1 IS
the second coordinate), `card_redDepthPairSet_one`, and the `polyOf` tail-box kit.
Lean-internal cross-check: RCD's landed `card_depthPairSet_one_one` re-derived as an
instance (`example`, exponent-exact).

## The three charge items, disposition

1. **The stratification / general per-v value: DERIVED, closed form, only-`m`
   dependence proved** (mathematics of record above; battery-verified).  The charge's
   suggested gcd-degree route matured into the sharper division route: conditioning
   on the reduction gcd does NOT Hensel-split (gcd and cofactors need not be
   coprime); the honest elementary mechanism is `g mod f` + norm + localization +
   `r`-adic Weierstrass, and the "geometric at the gcd's scale — recursion!" instinct
   is exactly the `B_e` recursion (whose base IS the (1,1) law at scale `s^δ`).
2. **Per-v values proved exactly at every level in LEAN: at `min = 1`, COMPLETELY**
   (`card_depthPairSet_one_right/_left`, all levels via the statement's free `N` —
   RCD's `card_depthPairSet_levels` composes for the cylinder form), and the
   URLim forms landed: the `min = 1` families fire `ZcURLim` OUTRIGHT;
   at general `(n₁,n₂)` the box values are REDUCED (Lean-core, hypothesis-light) to
   the diagonal reduced census at `min(n₁,n₂)`, with the `ZcURLim` transport
   packaged.  **`zcURLim_visDepth_of_clusters`'s premise is NOT fired outright** —
   as VCL's own fence records, the premise needs the box values AND which visible
   cells the clusters land on; this unit closes the value axis at `min = 1` and
   confines its general-`m` content to the diagonal; the vis-landing is the named
   remainder (axis 3 overlap).  Nothing weakened.
3. **What remains of VCL's three axes** — see the fence below.

## THE HONEST FENCE (what remains of VCL's three axes, exactly)

1. **Axis 1 (this unit) — value side**: the diagonal reduced census values at
   `m ≥ 2` in LEAN (`#redDepthPairSet(n, N, v)` for `n ≥ 2`) — the mathematics is
   the derived `Z_m` (verified numerically, exact), but the Lean transcription
   needs the localization/Weierstrass engine (finite-level coprime-Hensel
   factorization bijections + the norm-multiplicativity census — CSL's
   `IFCG42` Newton kit is the natural substrate).  After this file the entire
   general-`(n₁,n₂)` box question IS this diagonal question.
   **Axis 1 — consumer side**: the bridge premise's sum runs over `visGenreSet`;
   which visible cells carry the clusters (B.42's block-grouping genre) is untouched
   here — this is where axis 1 meets axis 3.
2. **Axis 2 (summed rationality across depths)**: untouched.  Note the master law
   sharpens its target: the per-depth values are `[t^v]Z_m`, geometric-with-period-`j`
   mixtures, so the `Σ_v`-interchange has an explicit dominating structure
   (IFCG60's `sum_card_depthPairSet_eq` partition + `GE_v ≤ s^v·(1+⌊v/2⌋)`-genre
   envelopes now have exact closed forms to aim at).
3. **Axis 3 (collision structure / per-cell cluster multiplicities)**: untouched.

NOT attempted (out of charge): `PowerFullSpanLaw`, `LeafSubfaceLaw`, TBT's
decidedness-transport converse.  Zero new axioms; every consumed statement
byte-untouched; no statements weakened (the `0 < n₁`/`1 ≤ n₂` hypotheses are the
honest degenerate-degree fences — at `n₁ = 0` the frame polynomial is `1` and the
stratum is depth-0-trivial).

## File map (`leanfinal/Uniformity/ChapI/IFCG61.lean`, 665 lines)

§0 kit: ★ `mixDepth_eq_iff`, `mk_pow_dvd_iff_le_resOrd`, `polyOf` +
`polyOf_coeff_lt`/`polyOf_degree_lt`/`polyOf_eq_self` ·
§1 ★★ THE MIN-REDUCTION: `redRes`, `redDepthPairSet`, `remCoeff`/`quotCoeff`/
`buildCoeff`, `rem_natDegree_lt`/`quot_natDegree`/`quot_monic` (private),
`polyOf_remCoeff`, `monicPoly_quotCoeff`, ★★ `classRes_eq_redRes`,
`mem_depthPairSet_iff_red`, `build_roundtrip`/`monicPoly_buildCoeff`/
`rem_quot_build`/`divSplit`/`natCard_prod_set` (private),
★★ `card_depthPairSet_reduce`, `mixDepth_swap`, ★ `card_depthPairSet_swap` ·
§2 ★ `redRes_one`, ★ `card_redDepthPairSet_one`, ★★ `card_depthPairSet_one_right`,
★★ `card_depthPairSet_one_left`, the (1,1) cross-check `example` ·
§3 ★ `zcURLim_depthDensity_of_reduced`, ★★ `zcURLim_depthDensity_one_right`,
★ `zcURLim_depthDensity_one_left` · AxCheck footer (17 rows).
Imports: Mathlib + `Uniformity.ChapI.IFCG56` + `Uniformity.ChapH.H116b4a` (the
ring-level `monicPoly` kit — `monicPoly_monic_ring`/`_natDegree_ring`/`_coeff_lt_ring`/
`_coeff_self_ring`, all previously landed Lean-core).  Aggregator: one import line
after IFCG60's (the sanctioned touch).

## Design decisions (recorded)

* **The reduced carrier is monic × FREE box** (`redRes c b` with `polyOf b`
  non-monic): the division remainder is degree-unconstrained below `n₁`, so the
  diagonal carrier at `min` is the (monic frame) × (tail box) resultant — this is
  ALSO exactly the `V_m` carrier the master-law derivation runs on, so the Lean
  fence and the math recursion meet at the same named object.
* **Everything at the class level**: `classRes` is computed over `Res O N`
  (IFCG41's design), so the min-reduction never consults lifts — mathlib's
  resultant lemmas run directly over the truncation ring, with `nontrivial_res`
  (H102) supplying the one instance monic bookkeeping needs.
* **`mixDepth_eq_iff` needs no irreducibility** — `Nat.findGreatest` reading plus
  power-divisibility only; hence `card_depthPairSet_reduce`/`_swap` are
  irreducibility-free (only the resOrd-valued counting at `min = 1` consumes `hπ`).
* **The URLim families at plain level `M`** (`#/q^{(n₁+n₂)M}`), eventual-constancy
  via `Tendsto.congr'` — matches IFCG24's `(X−1)/X^w` packaging pattern; consumers
  needing the `M + (n₁+n₂)` frame recompose through `card_depthPairSet_levels`.
* **The battery is the decorrelation leg** for the hand-derived `Z_m` (extraction-
  corruption discipline): predictions computed as exact `Fraction`s from the
  `q`-Pochhammer form, counts as exhaustive integer enumeration with Bareiss
  determinants — an integer-exact match at 17 configurations including a 16.7M-pair
  box.

## Repair log (5 compile rounds, all mechanical; every theorem landed as designed)

1. Dependent-rewrite motive failures (KDN #3 genre): rewriting `n₂`/`n₁` where they
   index `Coeff` types (`quot_monic` ×2, `classRes_eq_redRes`) — the
   rewrite-at-hypothesis idiom (`rwa [hgd] at h'`).
2. This pin's `Resultant/Basic.lean` declares `(f g p : R[X]) (m n k : ℕ)` EXPLICIT:
   `resultant_add_mul_right` needed all args positionally (a by-block hypothesis
   left `?p` as a delayed metavariable that blocked keyed matching);
   `resultant_comm` needed its four explicit args (stuck `CommRing ?m`).
3. `simp only [Prod.mk.injEq]` normalized `c₁ = c₁` to `True`, breaking `⟨rfl, _⟩` —
   replaced by direct `Prod.ext` terms.
4. `Nat.card_coe_set_eq` grabbed the wrong `Nat.card` occurrence — pinned the
   `Set.univ` argument.
5. `Tendsto.congr'` obligations arrive as beta-redexes (`(fun O _ .. => ..) O ..`):
   `simp only []` reduces them; the `ZcURLim.congr` obligation arrives already
   reduced (a third `simp only []` errored "no progress" and was removed).
   Unused binders `h1` in two private build lemmas removed (zero-warning bar).

## Cross-checks

* RCD's `card_depthPairSet_one_one` re-derived inside Lean from the new law
  (`example`, `N = v+1`, exponent identity by `omega`) — the two independent proofs
  of the (1,1) value agree.
* The min-reduction is battery-visible: (1,2),(1,3) match (1,1); (2,3),(2,4) match
  (2,2); (3,4) matches (3,3); (4,5) matches (4,4) — the Lean theorem and the
  numeric law point at the same invariance.
* `Z_m` self-consistency: `Z_m(1) = 1` for all `m` (telescoping), and the m=2
  GE-form recursion `γ_v = (1−s)s^v + s²γ_{v−2}` reproduces the assembled values.
