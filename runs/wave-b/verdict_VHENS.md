# Adversarial verdict — VHENS

1. **CRITICAL ERROR — the purported counterexample does not satisfy the current signed C.34 hypotheses.**  The document says, verbatim:

   > **Signed C.34's uniqueness clause** (`hsep`, and hence the signed
   > `exists_dv_residual_dissection` conclusion): the two labelled splits
   > `g = fS · q` (with `HasLabel fS`, `q` monic, `R(q)` a nonzero constant — the landed
   > constant law gives the complement clause) and `g = g · 1` (with `HasLabel g` — §7.1
   > — and complement `1`, again the landed constant law) have `fS ≠ g` (degrees 2 ≠ 3).
   > Every hypothesis of the signed statement holds at this instance (`hg` ✓ `hpure` ✓
   > `hne` ✓ `hp: M₀ = 3` ✓ `hdvd: r ∣ r` ✓).

   This is false against the landed source being verified.  In `leanfinal/Uniformity/ChapC/C34.lean:285-295`, both block candidates in `hsep` must satisfy
   `HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree`; the same pins occur in the packaged conclusion at lines 296-305.  Here `D′ = 2` and the second proposed candidate is `g` of degree `3`, so it fails the signed hypothesis.  The cited `leanfinal/Uniformity/ChapC/C34_BLOCKED_2026-08-18.md:69-82` is a historical pre-A-C.20 record, not the current signature.  The numerical example does refute the historical unpinned statement, but not the current signed C.34 clause.  Consequently the headline and the unit verdict's “STOP-THE-LINE STATEMENT-DEFECT” conclusion are stale.

2. **CRITICAL ERROR — the same stale-signature mistake invalidates the claimed C.35 refutations.**  The document says, verbatim:

   > * **The degree-pinned frontier `BlockFrontier′ L f` from `BlockContext L f`** (the
   >   honest F1.H3): §8, consuming the C.33 cite pair + M + H0 + A + B + C.  The UNPINNED
   >   `BlockFrontier` (`C35.lean:246-249`, whose maximality clause quantifies over unpinned
   >   `HasLabel`) is **REFUTABLE from `BlockContext`** — §7 — so F1.H3 as planned is a false
   >   target; the repair (pin the label in the quantifier, matching the classical
   >   `D″ ∣ deg f_S` of LEMMA HE7-6, `spec/EFF-HE7.md:1653-1663`) is an owner statement-gate
   >   item.  All eight `_of_frontier` rows survive unchanged as conditionals; what changes
   >   is what their `hfr` can ever be discharged FROM.

   and later:

   > **Signed C.35 `blockFactor_spec`** (clause 3): at this `f`, the maximal UNPINNED
   > labelled divisor EXISTS and is `f` itself (both labelled divisors divide it), so
   > `blockFactor L f = f` (the landed `blockFactor_eq_of_frontier` argument shape), and
   > clause 3 reads `3 = keyDeg₂ · mult₂ = 2 · (3 / 2) = 2` — FALSE.

   Current `leanfinal/Uniformity/ChapC/C35.lean:163-172` defines `blockFactor` using degree-pinned labels, and current `BlockFrontier` at lines 278-282 also pins every competitor by `D′ ∣ natDegree`.  The unpinned object survives only under the explicitly historical names `blockFactorLeaky`/`mult₂Leaky` at lines 132-175.  Thus the degree-3 polynomial can refute the leaky historical selector, but it cannot be the current `blockFactor`; the asserted current clause-3 contradiction `3 = 2` does not follow.  The cited line range `C35.lean:246-249` is not `BlockFrontier` at all in the landed file.  Likewise the document's proposed `BlockFrontier′` is, in substance, already the landed `BlockFrontier`, not a still-pending repair.

3. **CRITICAL ERROR — Lemma M1(2), the root read law, is false with the landed `slotRes` normalization.**  The offending statement is:

   > (read form)  for the finite heights `ka, kb` pinned by `dv(a) = ka`, `dv(b) = kb`:
   > `slotRes (ka+kb) ((a*b) %ₘ F.key) = slotRes ka a * slotRes kb b` in `K`
   > (hence `twistRead` multiplies up to the explicit unit
   > `stageLetter ^ (twistExp ka + twistExp kb − twistExp (ka+kb))`).

   The landed definitions exhibit a carry unit that this equality omits.  Use the `(e₁,f₁,h)=(2,2,3)` frame recorded in `leanfinal/Uniformity/ChapC/C22.lean:80-90`, and take `a=b=X`.  Then `deg a,deg b < D′=4`, `stageHeight X=3`, and `(X*X) %ₘ F.key=X²`.  From the formula for `slotRes` in `C21.lean:134-142`, `slotRes 3 X=1`, while `slotRes 6 X²=η` (the live band is `t=1`).  The same C.22 witness has `K=F₉` and `η²=2`, so `η≠1`.  M1(2) therefore asserts `η=1`.  The landed `twistRead` factor `η^{-twistExp(k)}` is precisely what cancels this slot-normalizer carry; it does not follow from an exact multiplicativity law for bare `slotRes`.  This breaks M1 and hence the proof of Theorem M.  Per the verifier charge, Theorems A, B, C, and the §8 assembly, all of which consume M, are not certified downstream.

4. **CRITICAL ERROR — Theorem M is stated under a weaker floor hypothesis than its proof uses.**  Its hypothesis is quoted verbatim:

   > direction `(u, ℓ)` with `hℓ : 0 < ℓ`, `hcop : Nat.Coprime u ℓ`, and admissibility
   > `ℓ * (D′ * F.h) ≤ u` (the engine's consumers all have the strict floor, which implies
   > this); `g z : Polynomial O` **nonzero** (no monicity, no purity, no degree fence).

   but §3.2 says:

   > By the C130nv3 mechanism (its "generic half", stated there with `hsurv` as a
   > hypothesis): that digit is `(dev g jg · dev z jz) %ₘ key + (strictly-above terms)`
   > (landed `dev_mul_pow` at carry 0, `dev_zero_pin`, and `lt_line_dev_term` for every other
   > convolution/carry term, using the strict floor).

   and §3.2 again invokes `lt_line_dev_term`.  The actual generic endpoint theorem `stageHeight_dev_endpoint_le_of_surv` requires strict admissibility `ℓ * V < u` (`leanfinal/Uniformity/ChapC/C130nv3.lean:170-185`), as does the strict pricing step at lines 236-249.  The landed weak inequality only supplies the superadditive half (`C130nv2.lean:645-674`).  No argument is given for the equality boundary.  Thus the proof does not establish Theorem M at its stated quantifiers, even apart from Finding 3.

5. **JUSTIFICATION GAP — the document calls several explicitly missing, load-bearing lemmas non-load-bearing.**  The headline says, verbatim:

   > **The engine is designed and its mathematics is proved below** at the stated grade
   > (every step justified; the four items that are NOT fully proved are named OPEN with
   > exact statements — none is load-bearing for the eight C.35 `_of_frontier` rows).

   But the proof of M1 uses OPEN-1/M1a at §3.1(c) and (d); clause M(3), initialization, solve, and monic normalization use the OPEN-3 C.22/TW computations; and §8 step 3 uses OPEN-4/X1 to prove the complement has point side.  These are load-bearing for the claimed engine and for `blockFrontier_of_context`, even if the already-landed conditional `_of_frontier` wrappers themselves remain valid.  Assuming the missing conclusions permits downstream discussion, but “the mathematics is proved” is not justified.

6. **JUSTIFICATION GAP — the side-lift construction claims more public landed API than the cited files provide.**  The offending passage is:

   > For monic `P ∈ K[Z]` of degree `d` with `P.coeff 0 ≠ 0`, the **side lift**
   > `Λ(P) := F.key ^ (d·ℓ) + Σ_{t < d} stageLiftO(u·(d−t))(P.coeff t) · F.key ^ (t·ℓ)`,
   > with `stageLiftO M κ` the landed digit lift with exact stage height `M` and prescribed
   > slot read `κ` (C.43/C.46/C.47's pins), built THROUGH the inverse twist so its
   > `twistRead` is exactly `κ` (the `k2DigitLift` trick, C56a).

   In the landed sources, `natDegree_stageLiftO_lt` and `slotRes_stageLiftO` are private in `C46.lean:217-230`, and `stageHeight_stageLiftO` is private in `C47.lean:401-405`.  The public theorem with the needed exact-height/exact-`twistRead` conclusion is instead the existential `KeyFrame.exists_twistRead_preimage` in `C14.lean:421-425`; it produces some `B`, not the displayed `stageLiftO` term.  Reproving the private facts or redefining `Λ` using the public existential may be possible, but the stated formula is not supplied by the cited landed declarations.

7. **JUSTIFICATION GAP — the limit conversion uses an inequality in the wrong logical direction and cites a private helper as consumable.**  The passage is:

   > Proof = B.40's shape verbatim with one conversion lemma
   > each way: `W`-floor ⟹ `gaussVal`-floor on windows (chain: `dvHgt ≥ e₁ • gaussVal(dev)`
   > — immediate from `stageHeight`'s formula — then B.40's own landed
   > `inf_npHgt_le_gaussVal` at `φ = F.key`, **Monic-fenced only**, `B40.lean:121`), and
   > back (`gaussVal q ≥ N ⟹ W(q) ≥ ℓ·e₁·N`, the `coeffIdeal` transport B.40 already
   > performs).

   From `dvHgt ≥ e₁·gaussVal` and a lower bound on `dvHgt`, no lower bound on `gaussVal` follows.  A bounded-degree upper comparison (with the finite `h·j` contribution explicitly controlled) is needed and is not stated.  Moreover `inf_npHgt_le_gaussVal` is declared `private` at `B40.lean:121-134`, so it is not a landed declaration that MH.8 can call.  This leaves the only completeness-consuming step of Theorem A unjustified even if M is assumed.

8. **JUSTIFICATION GAP — the inventory overstates the availability of a field instance.**  The document says, verbatim:

   > Throughout: `D′ := F.e₁ * F.f₁`, `K := F.stageField H₀ hpin` (a field —
   > `Field (F.stageField …)` is landed, `leanfinal/Uniformity/ChapC/C04.lean:151`),

   At `C04.lean:149-154`, `fieldStageField` is a **private** noncomputable definition, and the file explicitly says consumers must install such structure locally.  There is no exported global instance at that citation.  The field structure is reconstructible from `instFieldResField`, `F.hresirr`, and `AdjoinRoot.instField`, so this is repairable, but the cited landed input does not say what the document claims.

9. **JUSTIFICATION GAP — citation spot-check summary (ten citations checked).**  The inventory introduces its table as:

   > ### 1.1 The landed inventory the engine stands on (all Lean-core unless marked)

   Five cited inputs do match their advertised mathematical content: `stageHeight_mul` (`C130nv2.lean:203-207`) is universal; `dvSupp_add_le_dvSupp_mul` (`C130nv2.lean:645-674`) is the weak-admissibility superadditive half; `dvSupp_mul_eq_add_of_endpoint_le` (`C130nv2.lean:784-798`) requires the extra endpoint bound; `resPoly_mul_gen` (`B39a.lean:883-918`) is the general order-1 product law; and `natDegree_dvResPoly` (`C26.lean:394-400`) gives residual degree and nonzero constant coefficient.  Further correct spot-checks are the pure endpoint laws (`C35.lean:191-230`), the generic adic limit (`HenselFactorization.lean:306-310`), the monic-fenced graded limit (`B40.lean:203-210`), the strict pure×pure cite (`C66b.lean:90-112`), and the C.33 axioms (`C33Cite.lean:76-87`).  However, the inventory suppresses important distinctions exposed above: C.04's field construction and the named stage-lift lemmas are private; B.40's line-121 helper is private; C130nv3's generic strict endpoint theorem still assumes survival; and the current C.34/C.35 declarations have already been degree-pinned.  Therefore the landed-input audit does not support the document's global “proved” verdict.

Final verdict: **REJECT**
