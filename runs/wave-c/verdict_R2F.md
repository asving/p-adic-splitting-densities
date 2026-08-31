# UNIT R2F — VERDICT: THE r ≥ 2 SEPARATION IS CLOSED (the general fiber = one
pairNbhd cluster, Lean-core), THE DRAINAGE DISSOLVES (typeOf-additivity kills LSF's
fence 2 pointwise), the naive census value is REFUTED and the frame laws are RE-BASED
onto the named `SteepDecCensusLaw` family via an exact count squeeze; ★★★ AT THE
SPECIAL FRAMES `r·(e'−h) ≤ e'` THE CENSUS FIRES from one smaller-mass value law
(Lean-core!) and `SubfaceFrameLaw 6 3 4 1 {(4,1),(1,1),(1,1)}` — THE FIRST r ≥ 2
FRAME LAW — is UNCONDITIONAL (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG72.lean` (2888 lines, ZERO sorries,
zero errors, ZERO warnings; 15 AxCheck footer lines — 16 public theorems + 1
regression example + 4 public defs, ~36 privates).  **Axiom fence, machine-exact at
landing:** `tSteep_le_iff`, `exact_factorization_unique`, `fiber_eq_pairNbhd_gen`,
`mul_mem_subfaceCell_gen`, `steepDecCensusLaw_one`, and — the fire —
`steepDecCensusLaw_of_special` are PURE Lean core `{propext, Classical.choice,
Quot.sound}`; everything consuming LSF's transport (`subfaceCell_factors_gen`,
`subfaceCell_gen_empty`, `subfaceFrameLaw_of_steepCensus`,
`subfaceFrameLaws_of_censusLaws`, `subfaceFrameLaw_of_special`,
`subfaceFrameLaw_r_two_witness`, the two census masters) is Lean core + EXACTLY the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, inherited through IFCG66/67/69 — never re-consumed); the capstone master
additionally inherits exactly `Uniformity.Density.Tower.agnprw_termination` (ID12's,
previously declared).  The C.33 cites, `AX_cellRecursion`, and `sorryAx` do NOT
occur.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG72.lean` (12 increments, each GREEN;
final: exactly the 15 expected axiom prints); targeted
`lake build Uniformity.ChapI.IFCG72` GREEN (9044 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN (exit 0) with the IFCG72 line appended
after IFCG71's (the one sanctioned touch; IFCG73's line appeared concurrently from
its own unit — no conflict).  NO git operations.  IFCG71.lean untouched.

## ★★★ THE HEADLINES

    theorem fiber_eq_pairNbhd_gen :               -- ★★★ THE GENERAL FIBER (item 1)
      (pinnedBox ×ˢ steepCone) ∩ mulClass⁻¹{base product}
        = pairNbhd π K (h·d·r) a₁ a₂             -- BOTH directions, Lean-core;
                                                  -- size q^{hdr} via DPN's count
    theorem exact_factorization_unique :          -- ★★ THE NEW EXACT ENGINE
      W₁W₂ = B₁B₂, monic, deg-matched, Res(W₁,B₂) ≠ 0 ⟹ W₁ = B₁ ∧ W₂ = B₂
      -- any commutative domain; Bezout row + degree collapse; splitting-field-free
    theorem subfaceFrameLaw_of_steepCensus :      -- ★★★ THE CONDITIONAL LAW
      SteepDecCensusLaw (m−e'd) h e' ⟨σ.data.erase (e',d)⟩ → SubfaceFrameLaw m h e' d σ
      -- EVERY frame r ≥ 1; value nz_d(q)·L_τ(q)/q^{wLeaf + h·d·r}
    theorem steepDecCensusLaw_of_special :        -- ★★★ THE SPECIAL-FRAME FIRE
      r·(e'−h) ≤ e' → DecidedValueLaw r τ → SteepDecCensusLaw r h e' τ  -- LEAN CORE
    theorem subfaceFrameLaw_r_two_witness :       -- ★★★ FIRST CLOSED r ≥ 2 MEMBER
      SubfaceFrameLaw 6 3 4 1 ⟨{(4,1),(1,1),(1,1)}⟩   -- UNCONDITIONAL (B.42 only):
      -- frame (3,4,1), cofactor mass 2, census fed by the LANDED DecidedSliceAt 2
    theorem decidedSliceAt_all_of_MASTER_CENSUS / _visCensus_census /
      capstoneHypotheses_of_MASTER_CENSUS :       -- ★★★ MASTERS: leaf row's r ≥ 2
      -- premise re-based onto the census family (guards unchanged)

## The charge, disposition

**(1) THE GENERAL FIBER — CLOSED, Lean-core (charge item 1).**  Over every carrier
product, the `mulClass` fiber inside (pinned box) ×ˢ (steep cone) is EXACTLY one
`pairNbhd` cluster at DPN's pinned depth `v = h·d·r`.  Separation (⊆): the Hensel
leg `liftsFactor_of_not_dvd_resultant` (IFCG42) at the Bezout depth pinned by DPN's
strict determinant half refactors the exact product `W₁·W₂` through the base pair
mod `π^{v+1}`; then the NEW `exact_factorization_unique` at the MIXED pair
`(W₁, B₂)` — whose resultant is nonvanishing by the SAME strict half, since the
perturbed steep side keeps its strict cone (reads ≤ r ≤ v) — collapses the two exact
factorizations, so the carrier pair IS the Hensel pair.  Stability (⊇): every
box/steep read lives at digit levels ≤ h·d resp. ≤ r, both < v + 1.  (The charge's
"evaluate at THE root" gap at r ≥ 2 is closed without any evaluation: the mixed-pair
Bezout + degree-collapse replaces it.)

**(2) THE STEEP CENSUS — the honest verdict is a REFUTATION plus a re-base plus a
partial fire.**
* **Finding A (refutation, recorded for successors).**  The anticipated consumption
  "census value = q^{−wSteep}·decidedDensity(r,τ)" is FALSE at r ≥ 2.  Hand witness:
  `h/e' = 1/2`, `r = 3`, `τ = {(3,1)}`: the strict cone is the box (v₀,v₁,v₂) ≥
  (2,2,1), wSteep = 5, and the boxed decided density is at least
  `(1−q⁻¹)(q^{−5}+q^{−9})/(1−q^{−6})` — at q = 2 this is 0.0332 > 2^{−5} =
  q^{−wSteep} ≥ q^{−wSteep}·decidedDensity.  The steep box correlates with the
  polygon and hence with the type; the census does NOT factor off the < e value laws
  at genuinely fractional boxes.  Charge item 3's "conditional on the < e laws only"
  is therefore unattainable AS STATED; the honest carrier is the new named family
    `SteepDecCensusLaw r h e' τ` := ZcURLim of #(strict cone ∩ decided-τ)/q^{rK},
  and the masters are re-based onto it (LSF §4's sanctioned discharge-path genre).
* **Finding B (THE DRAINAGE DISSOLUTION).**  LSF's fence 2 (shifted-level cofactor
  decidedness) is NOWHERE needed: for any factorization of a CELL point with the box
  factor's type forced (`box_decided_shifted_gen` at shift h·d), `typeOf_mul`
  (TypeOfAlgebra, Monic+Monic) + multiset cons-cancellation make the steep factor
  decided at the FULL window, pointwise (`census_of_mem_cell`,
  `subfaceCell_factors_gen`'s last output).  The count is then a SQUEEZE, exact at
  every `M ≥ 2hdr` (`card_cell_bounds`):
    #box·(#census(K−v)·q^{rv}) ≤ #cell·q^v = #P ≤ #box·#census(K),
  P := (box ×ˢ steepCone) ∩ mulClass⁻¹(cell), the middle identity via the fiber
  theorem; the shifted-census term is the same census sequence at index K−v (the
  q^{rv} truncation fibers via IFCG46's `card_preimage_coeffFactor_eq`), so both
  ends converge to the SAME limit and ★★★ `subfaceFrameLaw_of_steepCensus` closes
  with value `nz_d(q)·(n_τ/d_τ)(q)/q^{wLeaf + h·d·r}`.  Regression: at r = 1 the
  value reduces to SFW's `nz_d(q)/q^{wLeaf + hd + 1}` — machine-checked by the
  `example` reproducing SFW's witness frame (3,4,1) at m = 5 through
  `steepDecCensusLaw_one` (the census family's first member, closed outright,
  value 1/q).
* **Finding C (THE SPECIAL-FRAME FIRE — item 3 delivered on a subfamily).**  At the
  frames with `r·(e'−h) ≤ e'` the strict cone IS the integer slope-1 box
  (`special_box_read`), and the coordinate scaling `u_j ↦ π^{r−j}·u_j` (IFCG51's
  `scaledHom` kit, replicated) preserves types in BOTH directions
  (`typeOf_scaleVecN`): every scaling preimage of a census member is decided at the
  full window, and every truncation-decided class scales INTO the census.  With
  `card_ker_scaledHom` (#ker = q^{bigTLoop r}) and `card_preimage_of_subset_range`,
  the exact squeeze `#dec(M)·q^{r²} ≤ #census(M+r)·q^{bigT} ≤ #dec(M+r)` closes the
  census law from `decidedSeq_tendsto` + `DecidedValueLaw r τ`:
  ★ `steepDecCensusLaw_of_special` is PURE LEAN CORE, value
  `(n_τ/d_τ)(q)/q^{bigTLoop r}`.  Composite `subfaceFrameLaw_of_special`: the frame
  law from ONE smaller-mass value law (exactly the master guard's shape).  The
  special family includes r ≥ 2 frames — every `(h,e') = (e'−1,e')` with `r ≤ e'` —
  and at `DecidedValueLaw 2` (= the LANDED `DecidedSliceAt 2`, I02/I03w) the first
  r = 2 member closes UNCONDITIONALLY (`subfaceFrameLaw_r_two_witness`).

**(3) THE MASTERS (charge item 3, honest form):** all three spines restated with the
leaf row's r ≥ 2 premise = `SteepDecCensusLaw (e − e'd) h e' ⟨σ.data.erase (e',d)⟩`
at the admissible frames with `e ≠ e'd + 1` (same guards as IFCG69's) —
`subfaceFrameLaws_of_censusLaws` + `decidedSliceAt_all_of_visCensus_census` /
`decidedSliceAt_all_of_MASTER_CENSUS` / `capstoneHypotheses_of_MASTER_CENSUS`.
This is strictly finer content than the SubfaceFrameLaw premise (the frame laws
follow); the r = 1 members remain SFW's theorems.  **Exact remainder after R2F:**
`SteepDecCensusLaw r h e' τ` at the NON-special r ≥ 2 frames (`r·(e'−h) > e'`) —
one census family at mass r < e, no products, no boxes, no drainage; Finding A
pins what its value is NOT; the realizable-slope stratification between `h/e'`
and 1 (a leaf-row-one-level-down recursion) is the anticipated mechanism.

## Supporting cast (all general-r, replacing SFW's r = 1 specials)

§4 `prod_coeff_dvd` (the antidiagonal convolution engine) + `prod_class_data_gen`
(cone; EXACT `h·d` at abscissa r — the corner term `g₀·R_r` exact, every competitor
at `tLeaf(i) + tSteep(r−i) = hd + 1`; strictly-raised corner in the cleared form
`e'hd + hr < e'·resOrd`) · §5 `face_package_gen` (minimal face/¬attain-0/stratum/
shallow/¬pure-face at `m = e'd + r`; the pure-face contradiction is tight exactly at
abscissa r) · §6 `steep_class_side` (the strict cone collapses the class side to
{r}) + `prod_residual_gen` (steep residual a UNIT via B.39a §7's product side laws;
degrees pinned to d) · §7 `box_decided_shifted_gen` (SFW's box decision at ANY shift
v ≥ h·d) + ★★ `mul_mem_subfaceCell_gen` (THE IMAGE, Lean-core) · §8 ★★
`subfaceCell_factors_gen` (THE SURJECTION; type forced `σ = (e',d) ::ₘ τ`;
`subfaceCell_gen_empty` off-type) · §9–10 the memberships and ★★ `card_cell_bounds`.

## New definitions (trust boundary — flag for review)

`tSteep` (the strict-cone digit floor, `⌊h(r−j)/e'⌋ + 1`, with its defining iff) ·
`steepCone` (the mass-r strict cone, byte-matching DPN's coupling hypotheses) ·
`steepDecCensus` (cone ∩ decided-τ at ONE window) · **`SteepDecCensusLaw`** (THE new
named premise family; NOTE it is π-independent — the ZcURLim π-slot is ignored).
All four are one-liners over landed corpus objects.  Every consumed statement
(`SubfaceFrameLaw`, `subfaceCell`, `subFrames`, `pairNbhd`, `LiftsFactor`,
`DecidedAt`, `pinnedBox`, the IFCG69 masters, `decidedSeq`/`decidedDensity`) is
byte-untouched.

## File map (`leanfinal/Uniformity/ChapI/IFCG72.lean`, 2888 lines)

§0 kit (replicas: fiber-partition counters, `digAt_congr`, `box_lift_divs`) ·
§1 carriers + `SteepDecCensusLaw` · §2 ★★ `exact_factorization_unique` ·
§3 ★★★ `fiber_eq_pairNbhd_gen` (+ `steepCone_stable`, `pinnedBox_stable`,
`steep_lift_divs`) · §4–§6 the product package · §7 THE IMAGE · §8 THE SURJECTION ·
§9 memberships · §10 ★★ `card_cell_bounds` · §11 ★★★ `subfaceFrameLaw_of_steepCensus`
· §12 the bridge + the three masters · §13 `steepDecCensusLaw_one` + the SFW-witness
regression `example` · §14 the special fire (`scaledHom` kit replicas,
`special_box_read`, the two transports, `card_census_special_bounds`,
★★★ `steepDecCensusLaw_of_special`, `subfaceFrameLaw_of_special`,
★★★ `subfaceFrameLaw_r_two_witness`) · AxCheck footer (15 lines).
Imports: Mathlib + IFCG69 (LSF/DPN/SFW and the spine transitive).  Aggregator: one
import line appended after IFCG71's.

## Repair log (10 error rounds over 12 increments; every theorem landed as designed — no mathematical failures)

1. omega mul-atom traps, repeatedly: `t*e'` vs `e'*t`, `h*(e'd−0)` vs `h*(e'd)`,
   Fin-coercion atoms `↑⟨x.1,hi⟩` — fix with explicit `Nat.mul_comm` bridges,
   `simp only [Nat.sub_zero]`, and `show`-defeq renormalization before omega.
2. `add_le_add_left` at this pin has the (a+c ≤ b+c) shape — use
   `le_add_of_nonneg_right` for `a ≤ a + b` on `WithBot ℕ`.
3. `coeff_eq_zero_of_natDegree_lt` inside `rw` unifies with the FIRST coeff subterm
   (the wrong factor) — pin p and n via a type-ascribed `have`.
4. **`set K := M + (m)` is a trap in this corpus**: the abstraction splits the
   type-level `M + m` inside `Coeff`/`subfaceCell`/`DecidedAt`, deranging the
   transport applications — write the literal window everywhere (SFW did too).
5. A `have : 1 ≤ tSteep … := by unfold tSteep; omega` leaks the division atom into
   LATER omega calls — use the term proof `Nat.succ_le_succ (Nat.zero_le _)`.
6. `div_le_div_iff` is `div_le_div_iff₀` at this pin; `div_eq_div_iff` is unprimed.
7. `← pow_add` needs `mul_assoc` first when the power pair is left-nested under a
   third factor; count the matches (a three-factor merge needs two rewrites, the
   two-factor one exactly one).
8. `ỹ` (y-tilde) is not a valid Lean identifier; `push_neg` deprecated at this pin.
9. `decidedSeq_tendsto` takes O implicitly while `decidedSeq`/`decidedCount` take it
   explicitly.
10. subfaceCell membership destructures at depth FIVE `.1`s to the decidedSet leg
    (remainderCarrier's nested inters + leafSubSector + subfaceCell).

## Cross-checks

* The conditional law at r = 1 + `steepDecCensusLaw_one` (value 1/q) reproduce SFW's
  closed witness frame `(3,4,1)` at m = 5 — machine-checked (`example`, §13); the
  value formula `nz_d·L/q^{wLeaf+hdr}` degenerates to SFW's `nz_d/q^{wLeaf+hd+1}`.
* `not_pow_succ_dvd_resultant_of_cones` enters THREE times (base Bezout, mixed-pair
  nonvanishing, DPN's count via `natCard_pairNbhd_of_cones`) — always through the
  same resOrd-weight instantiation, never re-proved.
* `steepDecCensusLaw_of_special` Lean-core confirms the fire never consults the
  transport; the exponent bookkeeping `r² − bigT = kappa`, `Σ_{j<r}(r−j) = bigT r`
  is discharged against IFCG3's loop constants.
* Finding A's refutation witness is a hand computation recorded here and in the
  design record — NOT formalized; its role is purely to stop successors from
  chasing the false product value.  (The boxed-decided lower bound alone beats
  q^{−wSteep}, so no undercounting subtlety can rescue the product formula.)
