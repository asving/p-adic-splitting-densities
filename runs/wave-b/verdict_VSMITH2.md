# Verdict VSMITH2 — H.116b4 restricted Smith identification after MSFIX

Current HEAD: `62a85329b10c3a764799aefc8f81834d821c7a68`.

## Re-verification of the original findings

1. **Original CRITICAL (wrong sign): disposed.**  The amended Step 2 now says

   > “`w'_i := Σλ^{(i)}g_{p,j} + c_i·Φ̃`.”

   This has the same sign as the residue identity in Step 1, so
   `w'_i ≡ Y^i (mod π)`.  The insertion of the `Y^j Φ̃` term through the
   original cofactor generator has multiplier
   `π^(ε-δ_j)c_(i,j)`, and for `j < d` the displayed estimate
   `ε-δ_j = β-kj ≥ k` makes it integral.  Top-down clearing is also integral:
   if `δ_j>ε`, then `j>d`, the `c_i Φ̃` contribution is absent, and the
   `g`-part has the required extra divisibility; if `δ_j≤ε`, no denominator is
   present.  Together with `w'_i≡Y^i (mod π)`, the clearing preserves the
   residue normal form.  Thus the generator change has diagonal blocks
   `Λ,I`, with `Λ mod π` invertible, and really is in `GL_m(O)`.

   I independently checked the Step-3 minors.  On the minor indexed by the
   cheapest slots, the child columns cannot occupy cofactor rows, the selected
   cofactor staircase forces its diagonal matching, and every moved child
   matching gains at least one valuation while preserving the sum of its row
   indices.  Conversely, arbitrary child columns occupy distinct rows below
   `s_μ`, and every cofactor entry is divisible by `π`.  These give both
   determinantal-ideal inclusions.  No new counterexample to Theorem E was
   found.

2. **Original GAP (finite certificate universalized): disposed.**  The amended
   text says “CERTIFIED AT THE FOLLOWING FINITE INSTANCES,” explicitly labels
   B1--B11 sampled, and disclaims a universal quantifier and non-prime residue
   fields.  I reran
   `python3 verification/openmath/h116b4_smith_cert.py` at current HEAD.  It
   exited 0 in 8.2 seconds and reported exactly 91,945 exhaustive anchor bases,
   970 sampled Block-B matrices, and 16 reported genre instances.  Those are
   the scopes now claimed in the document.

3. **Original GAP (cofactor/V inheritance hidden): disposed.**  U2 now stops at
   the integral cofactor split, U3 is unconditional only for `r=0`, and the
   cofactor-inclusive V-bound and residue-span compatibility are expressly
   named **OPEN GR-7b-0**.  Theorem U is explicitly conditional on GR-7b-0,
   GR-7b-I, and GR-7b-II.  The honesty ledger no longer says that only two
   lemmas are missing.

4. **Original GAP (U4 called proved despite open inputs): disposed.**  U4 is now
   marked `OPEN/CONDITIONAL`, and its dependencies are separately named OPEN
   GR-4a, GR-4b, GR-4c, and GR-5.  It is absent from the paper-proved ledger and
   is not used to upgrade Theorem U.

5. **Original citation audit: still current.**  No amendment-staleness problem
   appeared at this HEAD; details are below.

## New findings in the amended text

1. **GAP — Step 2 contains a false summand-wise divisibility sentence, although
   the immediately available case split repairs the argument.**  The amended
   proof says:

   > “from the `c_iΦ̃`-part, nonzero only for `j ≤ d−1` where
   > `δ_j − ε ... ≤ −k < 0`. In both cases the coefficient is divisible by
   > `π^{max(0, δ_j−ε)}·π^{min(k,1)}`”

   Read literally, “both cases” asserts that the `c_iΦ̃` summand is divisible
   by `π` when it is present.  That is false: `Φ̃` is monic, so if the top
   coefficient of `c_i` is a unit, the corresponding coefficient of
   `c_iΦ̃` is a unit.  The same phenomenon occurs in the predecessor's
   `F_3` example where the correction has `c̄_i=1`.

   What is divisible by `π` is the **total** high coefficient of `w'_i`, by
   `w'_i≡Y^i (mod π)`.  For the stronger bound when `δ_j>ε`, the cofactor
   summand is absent and the `g`-part bound applies.  These two facts, both
   already present in the proof, suffice for the clearing and its recursive
   divisibility invariant.  Hence this is a false local assertion and an
   exposition/proof gap, not a break of Theorem E.

2. **GAP — U2's written justification proves the split-off `π` factors but not
   the word “exactly.”**  U2 says:

   > “every child column has valuation ≥ 1 everywhere (S0). So ... [this]
   > splits off exactly `r` Smith exponents equal to `1`”

   From `A ~ diag(πI_r,S)` and only `S∈πM`, one gets at least the displayed `r`
   exponent-1 factors; one has not excluded additional exponent-1 factors in
   `S`.  The missing strengthening is available from the setup but is not
   stated in the U2 argument: since `j<μ`, `k≥1`, and a restricted child basis
   vector contains the global `π` times `π^{k(μ-j)}`, every initial child
   column is in `π²`; during the Schur elimination the correction
   `C(πU)^{-1}D` remains in `π²`.  Therefore `S∈π²M`, which does establish that
   no additional exponent is 1.  Until that observation is supplied, the
   advertised exact-count conclusion of the paper-proved U2 is under-justified.
   This does not close or further break Theorem U, which remains explicitly
   open for the three GR-7b lemmas.

## Current-HEAD citation spot-check

The cited line pins and scopes remain accurate at
`62a85329b10c3a764799aefc8f81834d821c7a68`:

- `leanspec/Leanspec/ChapH.lean:2963` is the signed
  `planted_presentation_card` axiom.
- `leanfinal/Uniformity/ChapH/H115b.lean:111` is
  `alphaParent_coeff`.
- `leanfinal/Uniformity/ChapH/H115c.lean:95` is
  `comp_recentre_injective`.
- `leanfinal/Uniformity/ChapH/H116b2.lean:448` is
  `plantedPoly_frame_profile`.
- `leanfinal/Uniformity/ChapH/H116.lean:212` is
  `monicPoly_map_residue`.
- `leanfinal/Uniformity/ChapH/H115.lean:101` is
  `proj_classSect`.
- `leanfinal/Uniformity/Density/LocalData.lean:221,228` are
  `resFactor_surjective` and `card_res`.
- `leanfinal/Uniformity/ChapB/B50.lean:97` is
  `exists_smith_of_norm`, with the narrow determinant-length/Smith-template
  scope now stated in the document.

A repository search still finds no landed Lean declaration named
`addVal_resultant_alphaParent_eq_slope`,
`addVal_resultant_alphaParent_ne_slope`, or `det_multiSylvester`; their only
substantive declarations remain OPEN sketches in
`leanfinal/notes/H116B4_OUTLINE_2026-08-18.md`.  The amended document now records
that status correctly.

The repairs therefore dispose every original rejection ground.  The amended
equal-slope theorem survives adversarial re-check, the unequal-slope theorem is
honestly OPEN, and the two new defects above are locally fillable gaps rather
than critical failures.

ACCEPT-WITH-GAPS
