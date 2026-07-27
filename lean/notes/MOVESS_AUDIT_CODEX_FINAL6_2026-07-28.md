# MovesS Lean blueprint — Codex final-confirmation pass 6 (REV 9), 2026-07-27
Prompt: /tmp/leanaudit/movess_final6_prompt.txt · Raw transcript: /tmp/leanaudit/movess_final6_verdict.txt

1. **CRITICAL — the new “typed” packages remain vacuously instantiable registries.**

   Offending specs:

   > `structure XRBPackage where xhd_w : Prop ; ... ; ns_null : Prop`

   > `structure RS1GivenPackage where tree_exp_fin : Prop ; ...`

   > `structure Wsh17Package where c15_volumes : Prop ...`

   These fields neither contain proofs nor refer to `T`, `M`, the ledger, trees, events, or owner interfaces. All may be instantiated as `False`; then `W2_xrb` and `W17ii` are trivially provable. Owner tags exist only in comments. This fails the requested typed-field and non-vacuity rules.

2. **CRITICAL — `W3_recursion` does not actually assume XRB.**

   > `W2_xrb Π B₀ → ... recursion`

   `W2_xrb Π B₀` is only the implication “all thirteen XRB premises imply height invariance.” `W3_recursion` assumes neither those thirteen premises nor the resulting invariance equality. Thus it can derive recursion when an XRB package field is false and XRB is unavailable. The note requires **GIVEN XRB (S.1)**.

3. **CRITICAL — `allActive_cofinite` weakens the displayed cofinite-prime claim.**

   > `{p : ℕ | p.Prime ∧ (p:ℚ) ∈ M.Pools ∧ (p:ℚ) ∉ allActivePools M}.Finite ∧ (allActivePools M).Infinite`

   This only bounds bad primes already lying in `M.Pools`; every prime omitted from `M.Pools` disappears from the exceptional set. Its second conjunct may be witnessed entirely by higher prime powers. The unit has no `RS4Chain.prime_sub` premise, despite its sketch relying on it. The note says cofinitely many **base primes** are all-active.

4. **CRITICAL — activity is determined by unconstrained data on split outcomes.**

   > `act_iff : ... ↔ ∀ o, (tgP e τ o).countS.eval q₀ ≠ 0`

   For split outcomes, `tgP` has no interpolation law; `jP` supplies the actual branching-cell mass. Hence `tgP.countS` on a split outcome can be chosen independently of the measured cells and can arbitrarily change activity. Moreover, the note quantifies over every cell-size polynomial, while the field quantifies only one outcome-level polynomial. This does not faithfully type CTS-M(ii).

5. **CRITICAL — the typed no-reclassification fence says the wrong thing.**

   > `(∀ t (ν : TI.Node t), TI.isDeepSplit t ν → ¬ TI.isEntrance t ν)`

   The note requires a deep split not to be classified as **shallow**. A deep split normally is not itself an entrance, so this implication does not establish the fence. It must place the split strictly in an entered block subtree, equivalently give it a first-entrance ancestor.

6. **GAP — the separate `(BDY)` pin is not connected to CUT-WD.**

   > `def W8_bdy (RL : ReadLedger) : Prop := ...`

   `ReadLedger.fe`, its charges, and its totals have no relation to a `TreeIface` tree, its first entrance, `shapeOf`, `WshVal`, or `βmeas`. Consequently a proof about an unrelated numeric sequence can discharge `W8_bdy`; the boundary ownership clause is not consumed by `W7_cutWD`.

7. **CRITICAL — W17ii remains vacuous for an empty shape menu.**

   > `structure ShapeFam ... where Sh : Finset (Shape T)`

   > `∀ Ŝ ∈ F.Sh, ...`

   Neither `shDom_ne` nor `sh_realized` prevents `F.Sh = ∅`; both are then vacuous, as is `W17ii`. `W17ii` does not premise `W7_cutWD`, whose nonempty tree could otherwise force a listed shape. This fails the explicitly requested empty-menu edge case.

8. **GAP — W17ii drops the displayed XHD-s hypothesis face.**

   > `structure Wsh17Package where c15_volumes : Prop; cts_counts : Prop; sib_count : Prop`

   CL-17(ii) explicitly names “XHD-s shallow height sums” alongside C.1.5, CTS counts, and the `(SIB)` count face. No `xhd_s` field or real XHD-s interface appears in this package. The `HasSum` conclusion states the desired consequence but does not supply the hypothesis from which the note derives it.

9. **CRITICAL — `W10_convergence` is satisfiable by empty, semantically unrelated fibers.**

   > `Fib : ∀ e, ... → Type`

   > `HasSum (fun f : FI.Fib ... => FI.fibMass ...) (B.βmeas ...)`

   `Fib` may be empty and has no map to canonical trees, events, or disjoint tree fibers. Taking `βmeas = 0` makes the statement immediate. The note’s claim concerns the countable disjoint union of actual complete finite canonical-tree fibers, not an arbitrary countable carrier.

10. **CRITICAL — `SCSData.resFactors` loses factor multiplicity.**

    > `resFactors : ... → Finset (ℕ × ℕ)`

    The note’s residual shape is an indexed family/multiset of factors, as witnessed by `Σᵢ g⁽ⁱ⁾μ⁽ⁱ⁾`. A `Finset` collapses repeated equal pairs. Two identical residual factors can therefore masquerade as one, invalidating U-4’s inference from `m = 1` to a singleton residual shape and corrupting `res_sum`.

11. **CRITICAL — the n=2 gate asserts data not displayed in the frozen note.**

    > “THREE outcomes … rowVal = `q₀⁻³`, `1 − q₀⁻¹`, `q₀⁻¹ − q₀⁻³`”

    > “the reduced solve: `β_(1,2) = (q+1)/(q²+q+1)` and `β_(1,1)² = q²/(q²+q+1)`”

    The frozen note displays only the 1×1 character, denominator `q² + q + 1`, and the `p = 2` inequality shadow. It does not display this three-outcome roster or the two numerators. Calling these “the NOTE’s instance” is a stronger, unsupported assertion rather than merely an arbitrary consistency witness.

12. **CRITICAL — the advertised schema-consistency instance omits substantial structure fields.**

    > “`consistency_n2` inhabits EVERY §2 structure simultaneously”

    The S5 units do not specify constructions for most `RS4Chain` shallow machinery (`WshP`, `WshVal`, all shallow event/height carriers and laws, `shDom_ne`, `sh_realized`, and their card laws), nor for `FiberIface`, `ReadLedger`, or the three new package structures. Thus the claimed explicit inhabitation story is absent.

13. **GAP — the REV-9 decomposition is still materially bundled.**

    Offending examples include:

    > `n2_boxes` — “Box/Cell/Rep carriers + boxpos/rep_ne + the cell events”

    > `n2_heights_ent` — “Hgt/HDom/gwt + entrance carriers ... + kstep/activeState/markedVal”

    > `n2_degpins_act` — “six per-piece degree pins + cellsize_nonzero + act_iff”

    > `n2_x3_rs1` — “x3_total/rs1_equates”

    These are multiple independent fields or displays, not one-obligation units. Their sketches conceal substantial construction and proof work.

**Counts:** 10 CRITICAL / 3 GAP

**REJECT (10 crit / 3 gap)**
