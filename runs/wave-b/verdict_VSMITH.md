# Verdict VSMITH — H.116b4 restricted Smith identification

Current HEAD: `d08ebafa`.

1. **CRITICAL ERROR — the residue-normal-form sign is reversed, so Theorem E's claimed column normalization does not follow.**  Step 1 says, verbatim:

   > “Hence for each i < s_μ there are unique
   > λ̄^{(i)} and c̄_i with  Y^i = Σ λ̄^{(i)}_{p,j}·ḡ_{p,j} + c̄_i·Φ̄,  deg c̄_i ≤ d−1”

   Step 2 then says, verbatim:

   > “set w'_i := Σλ^{(i)}g_{p,j} − c_i·Φ̃, so w'_i ≡ Y^i mod π.”

   The unit verdict correspondingly overstates, verbatim:

   > “- PROVED — THEOREM E (equal-slope regime, cofactor included; = GR-7a/b4.15):
   >   the list is {1+D−k·i : i < s_μ} ∪ {1}^r, for every admissible base, every DVR.
   >   Complete determinantal-ideal proof (doc §6)”

   Reducing the second display and using the first gives instead
   `w̄'_i = Y^i − 2c̄_i Φ̄`.  There is no characteristic-two hypothesis and no proof that `c̄_i = 0`.  This is a real case, not a formal possibility: over `κ = F₃`, take one block with `f=(Y−1)^2`, `g=Y`, `r=1`.  Then
   `1 = Y + 2(Y−1)Y + f`, so the unique cofactor correction for `i=0` has `c̄_0=1`, while the document's subtraction reduces to `1−2f ≠ 1`.  This residue data occurs in the stated admissible shape (one `μ=2`, `k=1`, `z=1` child and a degree-one cofactor with `β=1`, `Q̄=Y`).  Thus the asserted `w'_i ≡ Y^i`, the `GL_m(O)` change at lines 249–251, and hence the Step 3 minor calculation are not established.  Per the charge, I stop checking claims dependent on this normalization, including the claim that Theorem E is proved and its GR-6/GR-8 consequences.  The numerical evidence may support the theorem's truth, but it does not repair this proof.

2. **JUSTIFICATION GAP — the certificate summary makes a universal quantifier claim that the actual certificate does not test.**  The offending passage is:

   > “CERTIFIED (exit 0, ~5s, exact arithmetic in Z/q^N): true SNF == assignment
   > spectrum of V (C1) == C2 closed form, at EVERY base of every genre:”

   The unit verdict repeats and sharpens the overclaim, verbatim:

   > “- CERTIFIED — C1/C2 verified true-SNF == assignment-spectrum == closed-form at
   >   every base: exhaustive CELL-1/2/4 (91,945 bases, battery lists reproduced
   >   byte-equal) + 11 new cells (slope-2/3 blocks, three children, μ=3 char-2,
   >   deg-2 cofactors, TWO-genre cells, 6×6 and 7×7 mixes, q=5), ~700 sampled bases,
   >   16 genres, exact arithmetic, exit 0.”

   The following bullets themselves call B1–B11 “sampled cells.”  At current HEAD, `verification/openmath/h116b4_smith_cert.py` exhausts only CELL-1, CELL-2, and CELL-4; its B-block uses `structured_lifts` plus pseudorandom samples and sampled admissible cofactors.  A fresh run exits 0, but it reports 970 sampled B-base matrices, not every base of those genres.  Only the finite-instance conclusions are supported.  The later caveat “instances, not proof” is correct but does not make “EVERY base of every genre” true.

3. **JUSTIFICATION GAP — the cofactor-to-block reduction needs an additional unstated lemma, so U3 is not proved in the advertised cofactor-inclusive generality and the two-item OPEN ledger is incomplete.**  U2 says, verbatim:

   > “which is ≥ V[i'][c] pointwise in every certified cell (checked numerically; a
   > general proof of this comparison belongs to OPEN-I's polygon arithmetic).”

   U3 nevertheless says, verbatim:

   > “(U3) Per-block pivots at C2's rows (r = 0 or after U2, stated for r = 0).”

   and later:

   > “Moreover the
   > normalized columns inherit the V-bound”

   while the honesty ledger claims, verbatim:

   > “U3 (per-block pivots at exactly the C2 rows/exponents)”

   as proved and concludes:

   > “Nothing else is
   > missing for GR-7.”

   The unit verdict makes the same offending status claim, verbatim:

   > “U3 (each block normalizes to pivots at precisely C2's
   >   rows/exponents), U4 (t = m slot exact via det = ∏Res·det(D)). Remaining gap =
   >   two named OPEN lemmas”

   The displayed Schur-complement comparison is only numerically observed.  More importantly, named OPEN GR-7b-I is stated solely as `β_t(V) =` the C2 partial sums; it neither states nor implies that U2's integral clearing preserves the entrywise `V` bound.  GR-7b-II then assumes the U3 `V`-inheritance bound.  Therefore a separate uniform Schur-complement/V-inheritance lemma is missing (or OPEN-I must be strengthened explicitly).  Assuming that lemma, the later unequal-slope discussion can still be read conditionally.

4. **JUSTIFICATION GAP — U4 is listed among “PROVED PIECES” but invokes inputs that are still OPEN and not landed.**  The offending passage is:

   > “(U4) Top slot exact (t = m). v(det A) = Σ_{cols}(1+k(μ−j)) + r
   > + Σ_{p<p'}μ_pμ_{p'}min(k_p,k_{p'}) + Σ_pμ_p·β_{k_p}: A = Syl(P_1..P_s,Q)·D with
   > D the triangular basis matrix (det exact from S0/S1) and det Syl = ±∏ pairwise
   > resultants (outline GR-5); the resultant valuations are the outline's GR-4a/b
   > plus v(Res(P_p,Q)) = μ_p·β_{k_p}”

   The unit verdict likewise calls, verbatim, “U4 (t = m slot exact via det = ∏Res·det(D))” proved.

   At current HEAD there are no landed declarations named `addVal_resultant_alphaParent_eq_slope`, `addVal_resultant_alphaParent_ne_slope`, or `det_multiSylvester`.  The cited `leanfinal/notes/H116B4_OUTLINE_2026-08-18.md:319`, `:329`, and `:374` labels GR-4a, GR-4b, and GR-5 **OPEN**.  The document gives only a short scaling/resultant sketch, not proofs of the multi-Sylvester determinant identity or all exact scaling identities.  This is partly admitted later by “modulo the outline's independent GR-4/GR-5 nodes,” but that admission contradicts the unconditional “PROVED PIECES” label and the unit verdict's “proved U4.”  Assume those open identities to continue.

5. **Current-HEAD citation audit (no staleness defect found in the checked H/B inputs).**  I spot-checked more than the required five pins: `leanspec/Leanspec/ChapH.lean:2963` is still the unchanged `planted_presentation_card` axiom; `leanfinal/Uniformity/ChapH/H115b.lean:111` is `alphaParent_coeff`; `ChapH/H115c.lean:95` is `comp_recentre_injective`; `ChapH/H116b2.lean:448` is `plantedPoly_frame_profile`; `Uniformity/Density/LocalData.lean:221` and `:228` are `resFactor_surjective` and `card_res`; `ChapB/B50.lean:97` is `exists_smith_of_norm`; `ChapH/H116.lean:212` is `monicPoly_map_residue`; and `ChapH/H115.lean:101` is `proj_classSect`.  The line pins are live at HEAD.  Their scopes are narrower than a full restricted-Smith proof—especially B50, which is a determinant-length/elementary-divisor template, not GR-7—but the map describes it as a template.  Amendments A-C.17–A-C.20 touch Chapter C and A-I.4 touches Chapter I; none changes these audited Chapter H/B inputs.  Thus the defects above are current mathematical/proof-status defects, not amendment staleness.

REJECT
