# UNIT DPN — VERDICT: THE DEPTH PIN IS MACHINE-CHECKED — `v(Res(g, R)) = h·d·(m − e'·d)`
lands as a Lean-core theorem on the lift-free depth instrument (`mixDepth_eq_of_cones`),
via the weighted-Leibniz Sylvester route (no splitting fields, no norm, no ceilings);
LSF's discharge pointer 1 (the keystone of `SubfaceFrameLaw`) is CLOSED; the two CSL
firing pins are FIRED at the known depth (the exact `q^{h·d·(m−e'·d)}` cluster law on
every sub-face cell + the decidedness transfer at the shifted level, drainage premises
carried honestly); witness-frame regression kernel-decided (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG67.lean` (931 lines, ZERO sorries,
zero errors, ZERO warnings; 10 AxCheck footer lines — 10 public theorems, 20 privates).
**Axiom fence, machine-exact at landing:** `pow_dvd_resultant_of_cones`,
`not_pow_succ_dvd_resultant_of_cones`, `mixDepth_eq_of_cones`, `cone_data_of_isPure`,
`natCard_pairNbhd_of_cones`, `decidedAt_mulClass_of_cones`, `witness_frame_depths` are
PURE Lean core `{propext, Classical.choice, Quot.sound}`; the three leaf forms
(`subface_depth_pin`, `subface_cluster_law`, `subface_depth_pin_witness`) are Lean core
+ EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through LSF's
`subface_transport_pinned` — never re-consumed).  The C.33 cites, `AX_cellRecursion`,
and `sorryAx` do NOT occur.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG67.lean` (6 increments, each GREEN;
final: exactly the 10 expected axiom prints); targeted
`lake build Uniformity.ChapI.IFCG67` GREEN (9042 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN (exit 0) with the IFCG67 line appended
after IFCG66's (the one sanctioned touch).  NO git operations.  IFCG68.lean untouched.

## ★★★ THE HEADLINES

    theorem mixDepth_eq_of_cones :                 -- ★★★ THE DEPTH PIN (class form)
      (purity  h·(e'd − j) ≤ e'·resOrd(c₁ j),  exact corner  resOrd(c₁ 0) = h·d,
       steepness  h·(r − j) < e'·resOrd(c₂ j),  window  h·d·r < N) →
      mixDepth π c₁ c₂ = h·d·r                   -- TBT's ladder constant, PROVED;
                                                 -- Lean-core, uniform in q AND frame
    theorem subface_depth_pin :                   -- ★★★ THE LEAF PIN
      (sub-face leaf cell, min face (h,e'), any lift) → LSF's full pinned transport
      outputs AND: below the window, the factor classes' mixing depth
      = h·d·(m − e'·d) EXACTLY
    theorem subface_cluster_law :                 -- ★★★ CSL PIN 1 FIRED
      … ∧ (2v+1 ≤ N → #pairNbhd(v-clusters) = q^v)  at v := h·d·(m − e'·d) — every
      sub-face cell pair carries clusters of size EXACTLY q^{h·d·(m−e'·d)}
    theorem decidedAt_mulClass_of_cones :         -- ★★ CSL PIN 2 FIRED (premises honest)
      cones + factors decided at level N − h·d·r → product class decided at N
    theorem pow_dvd_resultant_of_cones /          -- ★★ THE TWO DETERMINANT HALVES
      not_pow_succ_dvd_resultant_of_cones :       -- (lift side, splitting-field-free)
      weak cones ⟹ π^{u·r} ∣ Res  (ANY CommRing+domain, ANY π);
      strict steep + exact corner + Prime π ⟹ ¬ π^{u·r+1} ∣ Res     (h·n = e'·u)

## The route (charge item 1) — and why THIS route

The charge suggested "norm/polygon first".  Inspected: DGT's `resultant_eq_norm` lands
the ring identity `Res = N_{O[X]/(g)}(R)`, but NO landed instrument reads the norm's
valuation over a pure-but-possibly-REDUCIBLE block (`O[X]/(g)` need not be a domain at
`d ≥ 2`), so the norm route would have required new structure theory.  What landed is
LSF's machine-check candidate (a) — THE WEIGHTED-LEIBNIZ SYLVESTER BOUND — which is
polygon-level in the honest sense: it consumes ONLY the coefficient valuations (the
polygon data), no root splitting, through mathlib's column-blocked `sylvester`:

1. **The column telescope** (`sum_slack_blocks`): for ANY in-band permutation σ,
   `Σ_c (offset(c) + band(c) − σ(c)) = n·r` — trade `Σ σ(c)` for `Σ c` (σ is a
   bijection: `Equiv.sum_comp`), then both structured sums collapse BLOCKWISE
   (left block contributes `r` per column, right block `0`).  All ℕ, no ceilings:
   the `e'`-cleared weights make every denominator disappear.
2. **The weak bound**: purity + steepness give each in-band entry `e'`-weight
   `≥ h·(slack)`; the telescope forces every Leibniz term's weight `≥ h·n·r = e'·(u·r)`;
   out-of-band terms vanish (zero entry).  Divisibility only — `Finset.dvd_sum`,
   `prod_dvd_prod_of_dvd`, `prod_pow_eq_pow_sum`; works over ANY commutative domain.
3. **The strict half**: with the steep bounds STRICT, a term dodges the `+1` excess only
   if EVERY steep column sits at its monic point — and then the face columns form an
   injective self-map of `Fin r` above the diagonal, which the equal-sum argument
   (`Finset.sum_eq_sum_iff_of_le`) forces to the identity: σ IS the block-flip
   permutation `sylFlip = finAddFlip ∘ finCongr`.  Its term is `sign · (a₁ 0)^r` — the
   corner power — and the exact corner (`π^{h·d} ∥ g₀`, `π` prime) kills `π^{u·r+1}`.
4. **The class assembly**: `classRes_proj` + `mk_pow_dvd_mk_iff` (IFCG41) push both
   halves through the truncation ring; `mixDepth_eq_iff` (IFCG61) reads the exact depth.
   The windowed valuations `resOrd` are themselves the lift weights
   (`le_classCoeffVal_iff_dvd`), so the class-side hypotheses ARE the proof's weights.
5. **The frame conversion** (`cone_data_of_isPure`): B.34's `IsPure` = on-side at BOTH
   endpoints, so B.17's two-point ℕ-equation (`onSide_nat_eq`) pins the corner height to
   `h·d` FOR FREE (no extra "exact corner" hypothesis anywhere in the leaf chain), and
   the `suppVal` inf gives the coefficientwise purity cone; window saturation is escaped
   by `h·(n−j) ≤ e'·(h·d) ≤ e'·N`.

## Charge disposition

**(1) THE PIN: PROVED**, in all three grades — lift-side determinant halves (§1,
CommRing+domain generality; the weak half needs neither primality nor positivity of the
corner), class-side `mixDepth` pin (§2, THE consumer key), leaf-side composite (§3:
LSF's transport re-run with the pin appended; the steep cone comes verbatim from LSF's
`class_strict_cone_of_side_singleton`, the face cone from `IsPure` via B.17).  Uniform
in `q` and in the frame `(h, e', d, r)`; the ONLY size condition is the honest window
`h·d·(m − e'·d) < M + m` (stated as an implication inside the leaf theorems, since the
frame is transport-produced).

**(2) THE COUPLINGS: FIRED where they close; the count identity honestly NOT.**
* FIRED: `natCard_pairNbhd_of_cones` (IFCG42's `natCard_pairNbhd_of_mixDepth` at the
  now-KNOWN `v = h·d·r`) and its leaf composite `subface_cluster_law` — the per-frame
  count's cluster granularity is now a theorem: every realized sub-face pair sits in a
  `q^{h·d·(m−e'·d)}`-cluster of pairs with the SAME product class, below half the
  window.  `decidedAt_mulClass_of_cones` fires the transfer socket at the shifted level
  `N − h·d·r` with the two factor-decidedness premises CARRIED EXPLICITLY (they are the
  drainage remainder, not discharged here).
* NOT closed (exactly as LSF forecast): the per-frame count identity
  `#subfaceCell · q^{adjust} = #(face box) × #(steep census)` — it needs the three
  remaining engines listed below, none of which is the pin.
* Regression at the witness frames: `witness_frame_depths` (kernel-decided) — at
  `m = 5`, `σ = {(4,1),(1,1)}`, the two admissible frames `(1,4,1)/(3,4,1)` carry
  pinned depths `{1, 3}`; and `subface_depth_pin_witness` — at minimal face `(h, 4)`
  the block is forced to `d = 1` and `mixDepth = h` EXACTLY, end-to-end through the
  transport.  (`SubfaceFrameLaw` itself is untouched — statement byte-identical,
  still open; the witness feed is these two theorems, its first two frames' cluster
  data.)

**(3) WHAT REMAINS of `SubfaceFrameLaw m h e' d σ` after the pin** (LSF's pointers 2–4,
unchanged in content, now with the keystone removed):
1. **THE STEEP CENSUS** (`SteepLaw r τ h e'`-to-be): the count of decided-`τ` classes in
   the strict cone at mass `r = m − e'·d`.  At `r = 1` it is trivial (the X-stratum;
   count `q^{N−1}`) — the witness frames need ONLY this member, so the first
   `SubfaceFrameLaw` instances are one census lemma + the drainage away.
2. **THE DRAINAGE** (CSL fence 2): shifted-level decidedness of the canonical factor
   classes — consumed here as `decidedAt_mulClass_of_cones`'s two explicit premises.
   (LSF's dead end — the depth-`v` Newton-correction route — was NOT retried.)
3. **The image characterization**: which (face box) × (steep decided) products land in
   `subfaceCell` (the converse wiring; SDL-§1 genre, routine per LSF given B.39a §7).
   With 1–3, the assembly is IFCG60 §5's cluster-bridge pattern through this file's
   `subface_cluster_law` + `decidedAt_mulClass_of_cones`.

## New definitions (trust boundary)

**NONE public.**  The unit adds 10 theorems; the only new `def`s are three PRIVATE
proof instruments (`sylFlip`, `wtL`, `wtR` — the flip permutation and the per-column
weight tables), invisible outside the file.  Every consumed statement
(`subface_transport_pinned`, `class_strict_cone_of_side_singleton`, `mixDepth`,
`pairNbhd`, `DecidedAt`, `SubfaceFrameLaw`, `IsPure`, `OnSide`, …) is byte-untouched.

## File map (`leanfinal/Uniformity/ChapI/IFCG67.lean`, 931 lines)

§0 kit: `monicPoly_coeff_deg`, `dvd_sign_zsmul`, `syl_left`/`syl_right` (the entry
readers), `sylFlip` + val lemmas, `wtL`/`wtR`, `dvd_entry_L/R`,
`slack_bound_L`/`_L_strict`/`_R`, ★ `sum_slack_blocks` (THE TELESCOPE) ·
§1 `term_dvd`, ★★ `pow_dvd_resultant_of_cones`, `term_dvd_strict` (the flip forcing),
`prod_sylFlip`, ★★ `not_pow_succ_dvd_resultant_of_cones` ·
§2 ★★★ `mixDepth_eq_of_cones` ·
§3 `npHgt_monic_top`/`suppVal_ne_top_of_monic` (private replicas),
★ `cone_data_of_isPure`, ★★★ `subface_depth_pin` ·
§4 ★★ `natCard_pairNbhd_of_cones`, ★★ `decidedAt_mulClass_of_cones`,
★★★ `subface_cluster_law`, `witness_frame_depths` (decide),
`subface_depth_pin_witness` · AxCheck footer (10 lines).
Imports: Mathlib + IFCG61 (the depth instruments, through IFCG56/42/41) + IFCG66
(LSF's transport; everything else transitive).  Aggregator: one import line appended
after IFCG66's.

## Repair log (4 error rounds + 1 lint round; every theorem landed as designed — no mathematical failures)

1. `congr 1` after `Fin.sum_univ_add` closed the castAdd block DEFINITIONALLY (castAdd
   val is rfl), leaving one goal — the second bullet found "no goals".  Replaced by
   `simp`.  Also the flip val lemma needs the `add_comm` leftover closed explicitly.
2. Binder shadowing: the obtained zero-entry witness `j` collided with the `∏ j`
   binder, deranging `rw [Finset.prod_eq_zero …]` — route through a named `have`.
   `push_neg` deprecated → replaced by a direct `fun j hj => hzero ⟨j, hj⟩`.
3. The `Fin r`-vs-`Fin (n+r)` val mismatch: `congrArg Fin.val hxy` elaborates its
   implicit type OUTSIDE-IN, unifying `Fin.val` at the WRONG Fin type — route the
   ψ-injectivity through `simp only [Fin.mk.injEq] at hxy` instead.  Also `prod_sylFlip`
   call sites: section variables are implicit here (unlike §0's explicit ones).
4. **THE B09 TRAP, re-confirmed**: `WithTop.ne_top_iff_exists` produces `WithTop.some`,
   which is defeq-but-not-syntactic against `Nat.cast` — the post-`rw` rfl fails.  Use
   `ENat.ne_top_iff_exists` (exactly B09's recorded warning; consult it before ANY ℕ∞
   finiteness extraction).
5. Lint: `term_dvd_strict` needs no `0 < e'` (strict-mul cancellation
   `Nat.lt_of_mul_lt_mul_left` is positivity-free) — binder dropped.

Increments 4 (§2), 5 (§3, post-ENat fix), and 6 (§4) compiled FIRST-SHOT — the §0/§1
scaffolding absorbed all the friction.

## Cross-checks

* The telescope constant reproduces the classical root computation: `e'd·r` root pairs
  at pairwise valuation `h/e'` each ⟹ `v(Res) = e'd·r·(h/e') = h·d·r` — the Lean
  telescope `Σ slack = n·r` is its `e'`-cleared shadow, term by term.
* `witness_frame_depths` matches TBT's derived table exactly: frame `(1,4,1)` ⟹
  `v = 1·1·(5−4) = 1`; frame `(3,4,1)` ⟹ `v = 3` — kernel-decided.
* The abstract couplings preserve IFCG42's socket signatures verbatim (`pairNbhd`,
  `DecidedAt`, `mulClass` untouched); the pin enters ONLY through the `hd : mixDepth = v`
  slot those sockets were designed around.
* The weak half's generality (any CommRing+domain, any π, no corner) is the "`≥` half
  gives the fiber lower bounds" form LSF requested for future census units.
