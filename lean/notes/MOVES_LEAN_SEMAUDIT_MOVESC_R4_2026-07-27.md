No tool calls were made. Round 4 fixes nearly every round-3 item, including (SAE) exactly, but the fresh-species permutation loophole remains. That is blocking.

1. **R3 F8 — (SAE): GENUINE.**

   Encoding:

   > `∀ j : ℕ, ν.s0 ≤ j → j ≤ ν.s0 + ν.wSide → j < νp.μ →`
   > `  νp.line.at (j * νp.childWidth) < ν.line.at (j * νp.childWidth)`

   and

   > `ν.s0 + ν.wSide = νp.μ →`
   > `  ν.line.at (νp.μ * νp.childWidth) = νp.line.at (νp.μ * νp.childWidth)`

   This matches rev 14 symbol-for-symbol:

   - `ν.s0 ≤ j`
   - `j ≤ j* = ν.s0 + ν.wSide`
   - `j < μ_i = νp.μ`
   - `old(j) < new(j)`, equivalent to `new(j) > old(j)`
   - equality exactly when `j* = μ_i`
   - equality evaluated at `μ_i`, not merely at the recorded endpoint
   - base indices use `j·D_{i+1} = j·νp.childWidth`

   In particular, at a non-adjacent endpoint `j* < μ_i`, the strict clause applies at `j = j*`. At an adjacent endpoint, strictness stops at `j < μ_i` and the separate equality applies at `μ_i`. The F-EMPTY equality at a non-adjacent endpoint is excluded.

   The accompanying (NA) direction is also correct:

   > `ν.line.at (...) < νp.line.at (...)`

   i.e. `new(μ_i) < old(μ_i)`.

2. **R3 F9 — full realizability: GENUINE.**

   > `def Realizable (H : History p F) : Prop :=`
   > `  ∀ ... , TransitionAdmissible ...`

   Since `TransitionAdmissible` contains (NA), (HV), and both lines of (SAE), this is the required ∀-step three-condition class.

3. **R3 F10 — named per-step interface: GENUINE.**

   > `def TransitionAdmissible (νp ν : Node p F) : Prop := ...`

   The pairwise predicate is present, `Realizable` is its whole-history closure, `JetSetup` carries it through

   > `realizable : Realizable H`

   and `C3.lineDom` now receives

   > `(hreal : Realizable H)`.

   The elementary `C2_EInh_implied` theorem itself needs only the already-established `(ZC)` downset, so its not mentioning the predicate separately is not a semantic defect.

4. **R3 F11 — side height `u*`: GENUINE.**

   The relevant encoding is:

   > `ustar : ℚ`

   > `hLineU : line.at ((s0 + wSide) * Dwidth) = ustar`

   and

   > `gam : ℤ`

   > `((ν.gam : ℤ) : ℚ) = ν.e * (H.strFrame i * ν.ustar) + (ν.s0 + ν.wSide) * ν.h`

   `hLineU` pins the affine line through the right endpoint. The slope law in `HistoryCoherent` pins its slope, so the intercept cannot translate independently.

   The extra `STR` is correct because Lean records `ustar` in absolute \(v_p\)-scale while `gam` is the augmented/stage-scale weight. In the adjacent case, (SAE)’s endpoint equality plus `hLineU` identifies `ustar` with the standing vertex height.

5. **R3 F12 — canonical Bézout pair: GENUINE.**

   > `hbez : (e : ℤ) * s + (h : ℤ) * t = 1`

   > `hbezCanon : 0 ≤ t ∧ t < (e : ℤ)`

   With `gcd(e,h)=1`, multiplication by `h` is invertible modulo `e`, so exactly one `t ∈ [0,e)` satisfies `h·t ≡ 1 mod e`; then `s = (1-h·t)/e` is uniquely determined.

   At `e = 1`, `0 ≤ t < 1` forces `t = 0`; the Bézout equation then forces `s = 1`. Thus the claimed recentering value `(s,t)=(1,0)` and `mhat=0` are correct.

6. **R3 F13 — irreducibility: GENUINE.**

   > `hψirr : Irreducible ψ`

   Together with `hψmonic` and `hψdeg`, this encodes “monic irreducible over \(F_i\)” at the polynomial level.

7. **R3 F14 — anchor provenance: GENUINE at the node-data boundary.**

   > `hAnchor : (e : ℤ) * a = (s0 : ℤ) - t * gam`

   This is precisely the division-free form of

   \[
   a=p_{s_0}(\gamma)=\frac{s_0-t\gamma}{e}.
   \]

   With the side slots advancing by `e`, the stride positions advance by one; `hpat0` makes the first position occupied. Consequently the normalized exponents in `hRanch` start at zero and `a` can no longer move independently.

   The connection to an actual polynomial’s residual on a realized locus remains part of the declared presentation/existence bridge, but the round-3 free-anchor defect itself is repaired.

8. **R3 F15 — final residue extension: PARTIAL.**

   Round 4 adds:

   > `hψirr : Irreducible ψ`

   but retains only:

   > `hzbarRoot : ... = 0`

   plus `LandingKey`. There is no quotient equivalence or generation statement identifying the final residue field with `F_i[z]/(ψ_i)`. This is accurately declared as R4.B.7 and is not disguised as completed.

9. **R3 F16 — `C3.lineDom` hypothesis boundary: GENUINE.**

   Its statement now includes:

   > `(hreal : Realizable H)`

   The former weak endpoint clauses have been removed from `HistoryCoherent`. Thus DOM consumes the strict span entry or adjacent equality from (SAE), while coherence supplies slopes, widths, and tower provenance.

10. **R3 F17 — exact fresh species: NOT FIXED — BLOCKING.**

   The new laws are:

   > `fresh_band`: every clause support is contained in `inFreshBand`

   > `fresh_cover`: every band coordinate belongs to some support

   > `FreshData.disj`: supports are pairwise disjoint

   and the value branch has:

   > `cl.codim = cl.support.card`

   These force the supports to form a partition of the band and force the total codimension to equal the band cardinality. They do **not** force the geometric clause species.

   A direct countermodel remains:

   - For every band coordinate `c`, create one singleton strip clause with
     `support = {c}`, `codim = 1`, and `sat x ↔ x c = 0`.
   - These supports are disjoint.
   - Their union is the complete band.
   - Every support is contained in the band.
   - Every clause satisfies the first branch of `fresh_assembled`.
   - `mstar = band.card`, so `mstar_eq` holds.

   This replaces every prescribed nonzero/value digit by unrelated literal-zero clauses while satisfying all four new fields.

   There is a second permutation: value-clause supports need only have constant `htH`; they need not be contained in one coefficient block, equal the complete level set of that block, or correspond to the node’s specified pattern digit. Coordinates from distinct blocks at the same height can be grouped or repartitioned arbitrarily.

   Thus `fresh_cover + codim = support.card` fixes inventory cardinality, not the geometric species or the actual transported system.

11. **R3 F18 — zero cutoff: GENUINE for the stated blocker.**

   > `hN : 1 ≤ N`

   This makes `N=0` and the specific vacuous presentation from round 3 impossible.

   The stronger assertion `N ≥ N(H,Z)` is not internalized. It is explicitly left as the existence-side gap R4.B.4. Therefore the zero-cutoff defect is fixed, while the uniform sufficiently-large-\(N\) existence theorem remains deferred.

12. **R3 F19 — root cluster geometry: GENUINE.**

   > `root_height : ∀ ... b,`
   > `  b < μ₀ * childWidth₀ → 1 ≤ line₀.at b`

   This is the rev-14 DOM base inequality on the entire root factor interior, not merely an intercept shadow. It is at least as strong as the block-left-edge form used by `lineStep`.

   Combined with `floorH 0 = ⊥`, `fresh_cover`, `mstar_eq`, and the subsequent `(ZC)` downset, it places level-zero root coordinates below the root line and ensures they enter the root inventory. The property sits on `JetSetup` rather than bare `Realizable H`, but every counting consumer receives it through `J`.

13. **Fresh sweep — new independent unfaithfulness: none found beyond finding 10.**

   The major new round-4 overclaim is precisely the assertion that support partitioning identifies the clause species. It does not. I found no separate sign, endpoint, Bézout, γ-scale, or root-height error in the newly added fields.

14. **R4.B.1 — JetSetup existence: GAP.**

   This is openly a missing existence theorem for the presentation interface. It does not silently weaken a proved existence statement.

15. **R4.B.2 — the two `htH`/alphabet identifications: GAP.**

   The K1 interpretation and the level-set/alphabet cardinality theorem are assumed through the presentation interface rather than proved. That is an honest graded-ring obligation. It does not, however, repair finding 10: even granting the cardinality identity, Lean does not say that a support is the appropriate complete block level set.

16. **R4.B.3 — `TypObject` existence: GAP.**

   The interface accurately states the additive-surjection object; construction from the real graded piece is deferred.

17. **R4.B.4 — sufficiently large `N`: GAP.**

   `hN` handles positivity only. Existence of a corresponding setup for every `N ≥ N(H,Z)` is still absent and is correctly described as an existence-side theorem rather than encoded in the current conditional units.

18. **R4.B.5 — DIG level-set grouping: GAP.**

   `ZCData` records only the interior zero downset and rim location of other leads. Recovering the finer per-rim-block level-set grouping is genuinely unformalized.

19. **R4.B.6 — `vtx ≠ 0` and residue bridge: GAP.**

   `C3.vtxPolyNe` proves polynomial nonvanishing, not nonvanishing after evaluation at `zbar`. The missing quotient/injective-evaluation bridge is explicitly acknowledged. In adjacent transitions, (HV) plus the nonzero pattern lead forces the particular parent vertex value to be nonzero, but no global node theorem does so.

20. **R4.B.7 — final quotient identification: GAP.**

   This is exactly the remaining part of R3 F15. It is openly declared and currently unused by the counting interface.

21. **R4.B.8 — stratum semantics off the state locus: GAP.**

   `inh_implied` characterizes `stratum` only on `Sigma i`. That is enough for the recursion and counting arguments, but identification with the actual classifier stratum outside the locus remains presentation provenance.

22. **R4.B.9 — recentering center nonzero: not actually a remaining gap.**

   For a recentering,

   > `((zbar : Fˣ) : F) = ((center : σ.K) : F)`

   while `zbar` is a unit. The field embedding of `σ.K` into `F` is injective, so `center = 0` would force the unit `zbar` to have value zero. Thus `center ≠ 0` is derivable. This item is conservatively listed, but it is already forced rather than a hidden weakening.

23. **R4.B.10 — non-adjacent `u*` attainability: GAP.**

   The integer `gam` supplies the node-level on-lattice condition. Realizing the endpoint grade by an actual coordinate in the finite jet presentation is additional graded/presentation content and is not falsely claimed by the Lean fields.

**Verdict: REJECT.**

Blocking list:

1. `fresh_band + fresh_cover + disj + mstar_eq` determine only a partition and its total cardinality.
2. `fresh_assembled` does not label strip versus value coordinates from node geometry.
3. A complete value level set of one slot is not required; arbitrary constant-height subsets, including cross-block subsets, remain legal.
4. The all-singleton-zero construction satisfies every new fresh law while replacing the required value clauses and hence changing the locus in Theorem C(a).

The (SAE), realizability, per-step interface, `u*`, canonical Bézout, irreducibility, anchor, cutoff positivity, and root-height retypes are semantically sound. The 13 units should nevertheless not be released to provers until exact geometric fresh-clause identification is encoded.
