# MovesX rev-2 Codex re-audit (2026-07-27, gpt-5.6-sol via codex exec)
# Charge: lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md · Note: §X-EXHAUST (MOVES_2026-07-24.md ~10947-11556) · Blueprint: MOVESX_LEAN_BLUEPRINT_2026-07-28.md rev 2

1. **CRITICAL — `FourthPiece` omits one half of the note’s domain.**

   Offending spec:

   > `def FourthPiece ... := (∃ b', I.complete b' ∧ isPrefix I b b') ∧ NsFree I b`

   The note quantifies over an ns-free history that is “a finite branch **or** prefix of a complete τ-halted tree.” The definition retains only the second alternative. In particular, finite prefixes belonging to an infinite non-ns branch need not have a complete extension, even though the note includes them. This weakens `X2Aff`, `X2Progress`, and the intended bridge-to-envelope application.

2. **CRITICAL — `X2Cap` silently strengthens the kernel’s domain.**

   Offending spec:

   > `bound : ∀ b, I.capDetectable b → ...`

   The note’s cap-detectable quantifier is within the fourth-piece, intrinsically ns-free family: “(τ-ns) branches never enter it.” The structure requires the inequality for every `capDetectable` branch in an otherwise unconstrained interface, including possible ns-track branches. No field says `capDetectable b → FourthPiece I b`. This is a stronger hypothesis than `(X2-CAP)`.

3. **CRITICAL — the required n-only, p-uniform constants are not enforced.**

   Offending specs include:

   > `WeightChargeT4 (n p ...)` / `WeightChargeFull (n p ...)` with `s : ℕ`

   > `X2Tails (n p ...)` with `CT cT : ℝ`

   > `X2Progress (n) (I)` with `cd ch cd' ch' : ℚ`

   > `EnvKernels` chosen separately for each `M : XMassInterface n p ...`

   The note requires `s(n)`, `c₀(n)`, `c_cap(n)`, `c_d(n)`, `c_h(n)`, `C_T(n)`, and `c_T(n)` to be p-free. These structures permit new constants for every `p`, apparatus, mass interface, or p-dependent tree interface. “Enforced at instance time” is not part of the Lean statements, so the formal claims are weaker than the displays.

4. **CRITICAL — `X2Tails` is not tied to the displayed tall-read event.**

   Offending specs:

   > `tallFrac : ℕ → ℚ`

   > `bound : ∀ hstar, (M.tallFrac hstar : ℝ) ≤ CT * ...`

   The note bounds the mass of the concrete set
   `{f : some read of some branch has h_r ≥ h*}`. `tallFrac` is arbitrary and has no field identifying it with that event’s mass. It may be identically zero even when the actual event has positive mass. Thus `X2Tails` is vacuously satisfiable and does not state the note’s hypothesis.

5. **CRITICAL — `XMassInterface` is not normalized and admits the zero content.**

   Offending spec:

   > “a normalized monotone finitely-subadditive content”

   followed by fields for nonnegativity, monotonicity, unions, and null unions, but no field such as:

   > `frac Set.univ = 1`

   Taking `frac ≡ 0` satisfies every displayed content law, `discZero_le_tail`, `frac_inter_tendsto`, and all null conclusions. Consequently `XG.3` can prove “mass zero” over a completely degenerate mass model. This is precisely a non-vacuity failure relative to the note’s box probability measure.

6. **CRITICAL — the kernel-unit “inhabitation repair” is bookkeeping, not a semantic non-vacuity guard.**

   Offending unit specification:

   > “the guard is (i) contentful fields over data … and (ii) the recorded inhabitation obligations”

   The following remain vacuously inhabitable:

   - `XE.1a–c`: choose `F` empty, making every `∀ f` field vacuous.
   - `XE.1d` and `XE.1h`: choose an interface with `complete := False`, making `FourthPiece` empty.
   - `XE.1e`: choose `capDetectable := False`.
   - `XE.1f`: choose `Undec := ∅`, `link := False`, and zero content.
   - `XE.1g`: choose `tallFrac := 0`.

   Future-owner prose does not provide an actual instance or prevent these degeneracies. The rev-1 non-vacuity defect therefore remains.

7. **CRITICAL — `XE.2 envelopeStatement` does not state the note’s derived envelope theorem.**

   Offending spec:

   > `def EnvBound ... : Prop := ∀ N, ...`

   This merely defines what a bound would mean. It neither asserts existence of `K`, nor derives it from `X2Progress`, `X1aAlign`, `WeightChargeFull`, `X2Bridge`, `X2Cap`, and `X2Tails`. The note performs that conditional derivation in-section. The blueprint also has no unit for the displayed `p^{-c√N}` fallback. Deferring “the envelope’s SQ-side consumption” does not justify omitting these two note-derived displays.

8. **GAP — `XF.9 tailUnconditional` is not a frozen Lean statement and combines two displays.**

   Offending spec:

   > `theorem tailUnconditional … : same statements as XF.7 + XF.8`

   “Same statements” leaves the result type and quantifiers unspecified, and one unit combines the finite-level inequality with the separate limit display. This fails both statement fencing and the one-display-per-unit decomposition rule.

9. **CRITICAL — the supposedly unconditional discriminant corollary and X.3 theorem retain the proof-apparatus hypothesis.**

   Offending specs:

   > `XF.10 discZeroNull ... (V : ∀ aTail, ValExt ...) : M.frac A.discZero = 0`

   > `XG.3 x3Density ... (V : ∀ aTail, ValExt ...) : Tendsto ... 0`

   Both cited note displays are unconditional once `p` is prime and `n ≥ 2`. Although `XF.3` proposes constructing `ValExt`, neither unit discharges it, and no unconditional wrappers for `XF.10` or `XG.3` are specified. This silently strengthens the hypotheses and violates D8’s own requirement that `ValExt` never strengthen `(3b)` or X.3.

10. **CRITICAL — `XG.2 koenigFinite` is weaker than the quoted König display.**

    Offending spec:

    > `(hlen : ∀ b, (I.hist b).length ≤ B) : Finite I.Branch`

    The note’s displayed bridge is finite branching plus “every branch finite” implies the tree is finite. The unit instead assumes a uniform global depth bound. That stronger premise proves a weaker version of the cited statement. It may suffice after the numerical branch bound, but it is not the quoted König claim.

11. **CRITICAL — `XG.3` assumes the principal X.3(b)+(d) derived inclusion through `detectInter`.**

    Offending field:

    > `detectInter : (⋂ N, Undec N) ⊆ infBranch ∪ (⋃ i, nsFiber i) ∪ A.discZero`

    The note lists X.3(b) and X.3(d)’s assembly logic as derived in this section, using finite-tree detection, TB-CAP, the trichotomy, and König. `detectInter` already packages their decisive conclusion. `XG.3` consequently bypasses `XG.2`, has no tree interface argument, and proves the limit largely by assuming the intersection inclusion. This smuggles an in-section derivation into an owed interface field, contrary to the axiom policy.

12. **CRITICAL — `XG.4 x3Series` assumes the substantive set-level density identity.**

    Offending hypothesis:

    > `hσ : ∀ σ, M.frac {f | f ∈ ⋃ T ∈ {T | S.trueTypeOf T = σ}, S.fiber T} = S.densityσ σ`

    This already identifies the mass of all finite true-type fibers with the full density. That identification is what X.3’s zero-undecided/zero-ns assembly is needed to establish; it is not merely definitional. Moreover, `SeriesData` contains no finite-level decided sets or coverage relation through which `hx3` could establish it. Thus the series theorem assumes essentially the set-level form of its target.

13. **GAP — required Defs dependencies are not actually specified.**

    Offending unit references include:

    > `ValExt p (fTail n aTail)`

    > `Event p n D aTail a0`

    > `(hadd : CountableFiberAdditive M S)`

    `fTail` and `Event` are described as abbreviations but absent from the proposed skeleton. `CountableFiberAdditive` is only promised in a postscript; its fields and exact relationship to `M.frac`, disjoint families, and `HasSum` are not given. Consequently XF.6–XF.9 and XG.4 cannot yet be semantically or typingly audited as frozen statements.

Arithmetic recheck: the repaired tail inequality is algebraically equivalent to `(3b)`. It gives bounds `4` and `1/4` at `(n,p,D)=(2,2,0)` and `(2,2,4)`, and `2/3, 2/9, 2/27` at `(n,p,D)=(3,3,5),(3,3,7),(3,3,9)`. The branch bound is also correct on both routes:
`2I ≤ v`, `R ≤ sv`, and `T3 ≤ ⌊log₂n⌋` give
`2d_total ≤ (2s+1)v + 2⌊log₂n⌋`.

Counts: **11 CRITICAL / 2 GAP**

**REJECT (11 crit / 2 gap)**
