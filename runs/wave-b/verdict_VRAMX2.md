# Adversarial re-verification VRAMX2 — ramified level-1 norm exactness

1. **The original normalized-residue gap is disposed.** The repaired passage is:

   > `[c]_i := digAt π i c ∈ k.`

   B21 defines `digAt` as a total scalar digit (`B21.lean:43-47`); B22 proves witness-independence, exact vanishing, and common-height additivity (`B22.lean:77-102`). The displayed product law is also supported: B35a's `resMk_mul` (`B35a.lean:148-159`), specialized to constant polynomials and read through B59a's `digPoly_C` and `resFieldXEquiv_coe` (`B59a.lean:99-104,157-161`), gives precisely the claimed scalar multiplication rule. The old ill-typed use of `res(c·π^{-i})` is gone.

2. **The original critical `Nat`-subtraction error is disposed.** The repaired definition says verbatim:

   > `h*a ≤ γ AND e₁ ∣ (γ - h*a)`

   and the same inequality guard precedes every later interpretation of `(γ-h*a)/e₁`. In particular, for the predecessor's counterexample `P=X, γ=0, h≥1`, the `a=1` term is excluded. The convolution proof also handles failed output guards rather than reading truncated heights, and the band formula is genuinely piecewise at `s≤γ`. I followed the dependent chain after assuming I1 and found no renewed truncation defect in SPREAD 2, NC, the filtration product law, the band count, or the final telescope.

3. **I1 is now discharged; the document's OPEN labels are stale, not erroneous mathematics.** The document still says:

   > `INTERFACE I1 (resPoly/scalar-digit identification; OPEN, real proof node).`

   and later:

   > `This node is OPEN.`

   At current HEAD `d08ebafa`, `B59c.lean` proves all required pieces: `frameKey_sideGeometry` (`92-118`), the non-`rfl` `frameKey_hpin` (`125-134`), the coefficientwise/map identity `frameKey_resPoly_eq_map` (`187-214`), and the final irreducibility/degree transport `frameKey_scalarResidual_irreducible` (`223-241`). The scalar polynomial in `frameResidualPoly` (`141-145`) is literally the document's guarded `ψ`. `lake env lean Uniformity/ChapB/B59c.lean` exits 0 with only `[propext, Classical.choice, Quot.sound]`, and `Uniformity/ChapB.lean:71-74` imports B59c. Thus the document's conditional arrows may now be specialized unconditionally; the unchanged “T1 PARTIAL” status prose merely predates this landed input.

4. **The original degenerate-case citation gap is disposed.** The repaired passage says:

   > `Apply B53b span_mk_eq_span_algebraMap_pow to the arbitrary A₀ (using degree A₀ < degree Φ′)`

   and explicitly disclaims `addVal_norm_key_eval`. This now matches B53b's actual quantifiers (`B53b.lean:102-109`): an arbitrary nonzero polynomial below the key degree with finite Gauss value. With `h=0`, coprimality forces `e₁=1`, I1 identifies the residual read with ordinary reduction, and the scalar-power quotient plus the generic B53c dictionary yields the claimed `f₁·c`. No completeness hypothesis is imported into this route.

5. **No new break was found in the rewritten guarded chain.** The potentially fragile steps check out:

   - the division induction has `D′=e₁f₁>0`, so the zero-polynomial/natDegree case cannot obstruct strict descent;
   - NC applies additive extraction only after establishing all three weights are at least `w`, and nonzero extraction forces equality before SPREAD decomposition;
   - the graded basis has at most one `i` for each `a`, while coprimality gives exactly `f₁` admissible abscissae in `[0,e₁f₁)` above the stable threshold;
   - the band intersection is split at `γ<s` versus `s≤γ`; when `s=0`, the final telescoping range is empty and gives length zero;
   - for `Γ=e₁(λ.toNat+1)+h(D′-1)+s`, one has `N(Γ+1)>λ.toNat`, so the asserted terminal filtration quotient really vanishes;
   - T2 is independent of NC: the domain argument gives norm nonvanishing, and Cayley--Hamilton gives the scalar principal-ideal membership with the correct sign.

6. **Current-HEAD citation spot-check (no additional finding).** I checked more than the required five anchors against the files themselves:

   - `C01.lean:80-100` has exactly the positive `e₁,f₁`, coprimality, monicity, degree, irreducibility, purity, nonempty-side, and pinned residual hypotheses claimed for `KeyFrame`.
   - `C131p.lean:112-117` is exactly the coefficient-infimum formula for `stageHeight`.
   - `C27.lean:164-171` proves the constant-coefficient purity equation used as P2.
   - `B33.lean:84-88` proves the product superadditivity used for the easy half; its extra hypotheses are all present.
   - `B53c.lean:121-140` is the generic determinant--length dictionary and lies outside the later complete/residue-finite section.
   - `Leanspec/ChapC.lean:883-889` confirms that signed C.27 has no `IsAdicComplete` binder.
   - `C27x.lean:241-242` supplies `dv2Hgt_key` as claimed.
   - the transfer theorems cited historically from `scratch/DEC4_check.lean` are now landed at `B53d.lean:43-124`; the scratch citation is harmless staleness.

7. **Amendment audit (no additional finding).** A-C.17--A-C.19 concern the previous-grade fence, `chainNormBelow`, and `shadow_persistence`; A-C.20 degree-pins the separate C.34/C.35 block candidates; A-I.4 reconciles the I.01 termination carrier. None changes the KeyFrame hypotheses or the level-1 exactness argument here. The document's statement that a later general-`C` consumer needs extra heredity remains a fence, not an attempt to consume a pre-amendment signature.

8. **Certificate rerun.** `python3 verification/ramx_cert.py` exits 0 at current HEAD: all 4,443 positive cases are exact and the reducible-residual control has the stated 10 violations.

**ACCEPT**
