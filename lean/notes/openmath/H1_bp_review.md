# H1_bp_review — Codex adversarial review of HDISCHARGE_H1.md (2026-08-05)

Fresh-context Codex (`codex exec`, detached; thread 019fbc59-140e-76f2-a4ec-6060d7589d6a;
prompt = the verifier charge + the FULL rev-1 blueprint pasted; Codex cannot read the repo).
Charge: quote-and-classify (CRITICAL vs GAP), five targeted questions, verdict line.
VERDICT: **BLUEPRINT-UNSOUND** (9 critical / 6 gap). ALL 15 findings FOLDED at blueprint
REV 2 (same file, same day) — disposition table in HDISCHARGE_H1.md §7. Verbatim report:

---

1. **CRITICAL ERROR — §0 / §2.2 use incompatible tower indices.**  
   Quotes: §0, “`(KP)_{j+1} feeds only (V1)_{j+2}`”; §2.2(s1), “`hom^m_{e,h} : K[z] → gr(w_{j+2})-candidates`”; §5.3, `kp_step ... (M : GenuineStageModel σ')`.  
   If `(KP)_{j+1}` is a claim in `gr(w_{j+2})`, then its proof already requires the graded-ring/valuation structure represented by `(V1)_{j+2}` and `GenuineStageModel σ'`, which the display says is obtained only afterward. If instead `(KP)_{j+1}` belongs to `gr(w_{j+1})`, then §2.2 targets the wrong graded ring. Calling the target “candidates” does not support `Prime`, divisibility, or `initialForm` in an actual graded ring.

2. **CRITICAL ERROR — §2.2(s6) explicitly offers a circular proof of `(KPb)`.**  
   Quote: “`Input: (GR-B)(3) at the NEXT state or the direct computation from (2′) — the unit picks whichever composes`.”  
   The next-state `(GR-B)` is available only after the present `(KP)` step in the displayed induction. That alternative is circular. The non-circular direct computation is merely named, not supplied, so the proof plan cannot defer choosing between them.

3. **JUSTIFICATION GAP — §0 misidentifies or leaves unpinned the theorem producing the next `(V1)`.**  
   Quote: “`GD23 §5: BRIDGE + MacLane Thm 4.2, ON FILE`.”  
   The trusted pins list FGMN Theorem 4.2 and MacLane Theorems 10.2 and 12.1, not “MacLane Thm 4.2.” Since this arrow is the step closing the induction, the exact theorem and its hypotheses must be identified.

4. **CRITICAL ERROR — §1.2 mis-prices clause (1)’s printed support.**  
   Quote: “`Thm 4.2 (H_µ, ϕ_r multiplicative...) + Lemma 5.13 (R(gh) = R(g)R(h), g µ-proper)`.”  
   The trusted pin for Theorem 4.2 is the two-form identity for `H_µ(g)`, not a blanket residual multiplicativity theorem. Lemma 5.13 has a properness hypothesis, while clause (1) is stated totally and TR-6 sends properness only to clauses (3)/(4). Thus the cited combination does not discharge clause (1) as stated unless an additional derivation removes the properness hypothesis.

5. **JUSTIFICATION GAP — §1.2 clause (3) is not a direct match to Corollary 5.6(2).**  
   Quote: “`Cor 5.6(2) ... R_i(φ_{i+1}) = ψ_i`” mapped to “`R^{gr}(ψ̂) ∼ ψ_i`.”  
   The printed statement applies a polynomial residual operator to `φ_{i+1}`; the package applies a graded operator to its initial form `ψ̂`. TR-4 might bridge this, but the table labels it merely “`(KPb) transported`” and never states the precise factorization/normalization lemma needed for this particular clause.

6. **JUSTIFICATION GAP — §1.3 has no established source for the carry-algebra clause.**  
   Quote: OP-A2, “`the 𝒟-realization clause has no printed home — it is OUR gloss`.”  
   This is a consumed part of member (a), not optional decoration. “Prove it in S5, else drop it” is not a closed discharge route because dropping it reopens the engine seam and no replacement obligation is scheduled.

7. **CRITICAL ERROR — §4.2’s `KEY1-SITE` implication omits data needed for (d3).**  
   Quote: “`KEY1-SITE: (GR-B)_{i+1} + KP-STEP at the site ⟹ (d1)–(d3)`.”  
   To get the asserted equality for the site’s input `f`, one also needs the node/run fact identifying its recorded `Ranch` with the anchored normalization of `ν.σ.R f`, plus `ν.hOrd`. Neither `Key1SiteBlock` nor the displayed implication contains `f`, `ReadsOf`/`SideReads`, or that identification. Hence the block alone cannot derive the site-specific `ord_ψ(R_i(f)) = μ`.

8. **CRITICAL ERROR — §5.1’s guarded `faithful` statement is not the exact claimed face without additional invariants.**  
   Quote: “`∀ f a Rf, ... HasAnchorK (ν.σ.R f) a Rf → ...`.”  
   This universally asserts faithfulness for every polynomial whose parent residual admits an anchor, not merely the one polynomial realized at the node. That is close to a total Corollary-5.15 assertion and can require properness and compatibility between `ν`, `σ'`, `M`, and `KB`; the structure declares none of those relations. Conversely, it says nothing for the realized `f` until `SideReads` supplies the required `HasAnchorK` witness. The latter may make it sufficient for WGEO, but that consumption lemma is missing.

9. **CRITICAL ERROR — §4.2–§4.3 underprices the refinement-site content.**  
   Quotes: “`no new mathematics beyond (a)+(b)`” and “`KP-STEP's proof pattern covers refinement reads`.”  
   At `e·g = 1`, the minimal-degree/degree-block argument is exactly the unresolved OP-B1 corner, and (d3) additionally needs the properness transcription and the run-to-anchor identification. Coverage by read order also requires a theorem connecting machine sites to the appropriate tower instance. These are genuine propositions, not formatting alone.

10. **CRITICAL ERROR — §5.3’s probed `kp_step` theorem does not express its mathematical hypotheses.**  
    Quote:
    ```lean
    theorem kp_step ... (hΦ : IsNodeLift ν σ'.Φ)
      (he : σ'.e = ν.e) (hh : σ'.h = ν.h) :
      Nonempty (KPBlock σ' M)
    ```
    The theorem omits the advertised induction state, `(GR-B)`, `DevBound`, and an explicit transition/model compatibility hypothesis. “Prover discretion” to enlarge it to `TransitionCoreL` is not content-preserving: it changes the theorem. As shown, it claims the block for any genuine model and matching lift parameters, substantially more than the proof plan supports.

11. **CRITICAL ERROR — §5.3/§5.5 allow an unresolved `DevBound` hypothesis to masquerade as discharge.**  
    Quotes: U8b “`carries a displayed DevBound hypothesis row until OP-B1's math lands`”; wave W2, “`U8b also OP-B1 or its DevBound row`.”  
    Proving U8b conditional on `DevBound` only renames OP-B1. The wave table treats the row as an alternative dependency, but retirement of member (b) requires an unconditional proof of that row or a theorem deriving it from already discharged inputs.

12. **CRITICAL ERROR — §0 and §6 incorrectly treat `sorry`-backed theorems as non-axiomatic hypotheses.**  
    Quotes: §5.3 U9 “`lands as a sorry-statement behind the row`”; §6 “``sorry`-backed rows stay hypothesis-grade by construction`.”  
    In Lean, a theorem proved with `sorry` contains `sorryAx` and can satisfy downstream theorem dependencies as if proved. It is not equivalent to a structure field required explicitly from consumers. This directly contradicts the “never an axiom” and retirement disciplines.

13. **JUSTIFICATION GAP — §3.2 suggests an invalid inversion.**  
    Quote: “`Lean pattern: keys_exist_of_run's extraction inverted, or direct induction`.”  
    A theorem extracting lawful keys from `ReadsOf` cannot be inverted to construct `ReadsOf` from lawful keys. Only the direct induction route could work, and its required facts about the wired emitter are not specified.

14. **JUSTIFICATION GAP — §2.2 does not yet justify primeness after localization.**  
    Quote: “`ψ irreducible ... ⟹ hom^m(ψ) prime ... in K[ȳ][anchors^{±1}]`.”  
    Irreducibility survives localization only after proving that the localization does not invert or meet the prime generated by `ψ`. The necessary nonzero-constant/anchor-disjointness invariant is not stated in `KPBlock` or the proof inputs.

15. **JUSTIFICATION GAP — §2.2(s7) asserts the full OL-1 normalization from a smaller block.**  
    Quote: “`The per-level blocks assemble into OL-1's joint statement ... clause (c)'s V-recursion is (s2)'s weight arithmetic`.”  
    `KPBlock` contains neither monicity, the exact degree formula, nor the value recursion. A separate theorem can prove these, but B-M2 presently has only a one-sentence derivation and no precise induction statement or inputs.

### Targeted answers

**Q1.** No. DEVID itself is consumed one level down from `(V1)_{≤j+1}+(KPa)_{≤j}`, so that particular dependency is non-circular. The blueprint becomes circular because KP-STEP targets `gr(w_{j+2})`/a `GenuineStageModel` before `(V1)_{j+2}`, and because s6 permits using next-state `(GR-B)(3)`.

**Q2.** Yes. Most seriously, clause (1) uses properness-dependent Lemma 5.13 for a total multiplicativity clause while TR-6 assigns properness only to (3)/(4). Clause (3) also needs an unshown polynomial-to-graded transport beyond the literal Corollary 5.6(2), and the carry-algebra part of (0′) has no printed home.

**Q3.** As a site-consumed law it can be sufficient only when `SideReads` proves `HasAnchorK (ν.σ.R f) a Ranch` for the particular WGEO input and supplies `hOrd`. As stated it over-quantifies truth by asserting the equivalence for every anchored `f` without compatibility/properness hypotheses, while simultaneously under-specifying sufficiency because the site block contains no `f` or run-to-anchor bridge.

**Q4.** No. Site coverage, the `SideReads`/anchor identification, properness at `e·g=1`, and the refinement-case degree block are genuine content. They may be assembly lemmas rather than new valuation theory, but they do not follow from the stated `(a)+(b)` payloads alone.

**Q5.** No. A-M2’s N-1 gate is consistent, assuming “green” explicitly permits failure only of the optional total strengthening. U8b is inconsistent: “OP-B1 or its DevBound row” substitutes an assumption for the required proof, and therefore cannot support retirement; the overall tower also lacks a non-circular gate ensuring the next-stage model before U8.

**BLUEPRINT-UNSOUND** — the KP induction is index-circular, the site-level `(d3)` assembly omits necessary run data, and unresolved assumptions/`sorry` rows are incorrectly allowed to count as discharge.