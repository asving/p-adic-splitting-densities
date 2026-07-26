Verdict: **REJECT.**

The redesign repairs the local combinatorics and the root indexing, but it still does not state Theorem C for the classifier history. The principal blocker is that `JetSetup` contains arbitrary loci, clauses, height data, and unitriangular maps without a formal relation saying they are the loci, fresh inventory, heights, and moves determined by `H`. Consequently trivial presentations remain possible, and `thmC_a/b` count a locus defined from the presentation itself.

## Round-1 objections

1. **Anchored residual — GENUINE.**

   Round 2 states:

   ```lean
   hRanch : Ranch = ∑ k ∈ Finset.range (wSide / e + 1),
     Polynomial.C (pat k) * Polynomial.X ^ k
   hpat0 : pat 0 ≠ 0
   hpatTop : pat (wSide / e) ≠ 0
   ```

   This genuinely makes `Ranch` pattern data with exact endpoints. It is faithful provided the blueprint’s claimed normalization from stride positions to consecutive powers is the intended normalized `z`-coordinate.

2. **Conditions on `ψ` — GENUINE.**

   ```lean
   hψmonic : ψ.Monic
   hψdeg : ψ.natDegree = g
   hOrd : OrdPsiPoly ψ Ranch μ
   ```

   These impose monicity, degree, and exact `ψ`-order, matching §C.0’s factorization requirement.

3. **Relations among `e,h,g,μ,Dwidth,line`, and stage data — PARTIAL.**

   Round 2 adds:

   ```lean
   he : 1 ≤ e
   hh : 1 ≤ h
   hcop : Nat.gcd e h = 1
   hg : 1 ≤ g
   hμ : 1 ≤ μ
   hDwidth : Dwidth = σ.Φ.natDegree
   ```

   and in coherence:

   ```lean
   line.slope * (e * strFrame i * Dwidth) = h
   ...
   child.Dwidth = parent.childWidth
   parent.line.slope < child.line.slope
   ```

   These are substantive. But the line intercept remains unrelated to the pinned vertex or D.8 box line. §C’s `old(j) := w(f)-j·w(Φ̂)` is not determined by its slope alone. The admitted gap R2.C.9 therefore leaves `line`, `floorH`, realizability comparisons, and freshness placement adjustable independently of the actual read geometry.

4. **Species constraints — GENUINE.**

   ```lean
   hspecInc : species = ReadSpecies.increment → 1 < e * g
   hspecRec : species = ReadSpecies.recentering → e = 1 ∧ g = 1
   ```

   These exclude the round-1 zero/degenerate increment and recentering data.

5. **Recentering lift tied to the node — GENUINE.**

   ```lean
   IsRecenteringCore parent.σ child.σ parent.center parent.lift
   ```

   The existential unrelated witness is gone.

6. **Increment transition uses recorded parent read data — GENUINE for nonterminal transitions, PARTIAL globally.**

   ```lean
   IsStandardLift parent.σ parent.ψ parent.g child.σ.Φ ∧
   TransitionCoreL parent.σ child.σ child.σ.Φ
     parent.e parent.h parent.zbar
   ```

   This fixes the parent/child-field mismatch for `i+1 < length`.

   However, the last read `ν_k` also has a move and landing frame in §C. No successor stage is stored for it, and `J.Theta k` is not related to a `TransitionCoreL` or `IsRecenteringCore`. Thus the recorded history still does not determine every `Θ_i`, especially the final one.

7. **Later root nodes — GENUINE.**

   ```lean
   root_iff : ∀ j hj, nodes[j].species = ReadSpecies.root ↔ j = 0
   ```

   Together with `nonempty`, this forces exactly the first node to be root.

8. **Coherence and realizability are theorem inputs — PARTIAL.**

   ```lean
   coherent : HistoryCoherent H
   realizable : Realizable H
   ```

   They are now fields of every `JetSetup`. This fixes the purely syntactic omission.

   It does not make `Sigma`, `fresh`, `Theta`, `ht`, or `Psi` presentations of that coherent history. Those fields remain arbitrary except for internal combinatorial laws. Thus the final theorems consume coherence and realizability only nominally.

9. **Vacuous `(HV)` — GENUINE locally.**

   ```lean
   child.pat (child.wSide / child.e) = parent.vtx
   ```

   with

   ```lean
   Node.vtx :=
     zbar ^ (a - μ * mhat) *
       eval₂ ... ((Ranch /ₘ ψ ^ μ) %ₘ ψ)
   ```

   This is a genuine identity of recorded data, not an existential tautology.

10. **Full transported vertex value — PARTIAL.**

   Scalar factors and evaluation at `zbar` are now present. But:

   ```lean
   def Node.mhat (ν) : ℤ := -ν.σ.t * (ν.σ.h : ℤ) * (ν.g : ℤ)
   ```

   uses `ν.σ.h`, whereas the redesign prose describes `−t·h·g` in terms of the read data and separately records `ν.h`. The pasted material does not establish that `σ.h = ν.h`. This needs semantic confirmation; otherwise the “full” vertex factor uses the wrong `h`.

11. **`(NA)` slot/base-index mismatch — GENUINE.**

   ```lean
   child.line.at (parent.μ * parent.childWidth) <
     parent.line.at (parent.μ * parent.childWidth)
   ```

   Both lines are evaluated at the base index `μ_iD_{i+1}`, as required by §C.

12. **`m = nN` — GENUINE.**

   ```lean
   hm : m = n * N
   ```

13. **Sorted coordinate chart — GENUINE.**

   ```lean
   coordOf_sorted :
     ∀ j j', j < j' ↔ CoordPrec (coordOf j) (coordOf j')
   coordOf_lt :
     ∀ j, (coordOf j).1 < N ∧ (coordOf j).2 < n
   ```

   This is much stronger than the old cardinal equivalence and supplies the required order interpretation.

14. **Sufficiently large `N` — NOT FIXED as a theorem statement.**

   No Lean predicate `N ≥ N(H,Z)` occurs. The redesign says that a suitable `JetSetup` is intended to exist only above the cutoff, but the present layer proves only a conditional theorem from an arbitrary setup. This is an openly declared existence gap, not a false internal arithmetic claim, but it does not yet formalize §C’s universal “for every `N ≥ N(H,Z)`.”

15. **Exact floor downset — GENUINE on the declared interior, PARTIAL as `(ZC)` as a whole.**

   ```lean
   downset_exact : ... index < rimIdx →
     (D.pinned j = true ↔ ht (coordOf j) ≤ floor index)
   interior_zero : ... → D.solve j f = 0
   ```

   This fixes the old one-way `pin_dichotomy` and enforces literal zeros.

   Outside the interior, `ZCData` says nothing except the tautological fact that an index not below `rimIdx` is in the rim. It does not encode the structure or history-constant right sides of `DIG_i`.

16. **Rim represented as a base-index region — GENUINE.**

   ```lean
   (coordOf j).2 < rimIdx
   ...
   rimIdx := μ_i * childWidth_i
   ```

   The erroneous global-order suffix and `rimStart := 0` escape are gone. `m = 0` is also harmless.

17. **DIG equations solving whole rim level sets — NOT FIXED.**

   There is no field corresponding to §C.1.5:

   > “each equation solving for the level set of one rim block.”

   R2.C.5 admits this. The current `ZCData` permits arbitrary independent base-digit pins and arbitrary solve functions at the rim.

18. **Address-based `FreshData` — GENUINE deletion.**

   The old `coords`/`pinTo` representation is gone. Fresh values are now general predicates supported on whole finite coordinate sets:

   ```lean
   support : Finset (Fin m)
   sat : (Fin m → ZMod p) → Prop
   dep : ...
   count : ...
   ```

   This is compatible with Route B.

19. **Fresh clauses tied to the geometric species inventory — NOT FIXED.**

   Nothing connects

   ```lean
   J.fresh i : FreshData p m
   ```

   to `H.nodes[i]`, its `(α)/(β)/(γ)` clauses, its line, side, crossing, pattern value, or a `TypObject`. The list may be empty for every node. This is the round-1 “unrelated to `H.nodes`” problem in a new form.

20. **`C0.pinWelldef` — GENUINE for count, with a genuine new status statement.**

   `C0.pinWelldef` still gives count equality, while the new:

   ```lean
   theorem C0_pinStatus ... :
     ∀ j, D.pinned j = D'.pinned j
   ```

   states the missing per-coordinate free/determined status.

21. **`C0.pinTransport` — GENUINE.**

   ```lean
   ∃ D', ... ∧ ∀ j, D'.pinned j = D.pinned j
   ```

   This now states exact status preservation, not merely equal cardinality.

22. **`C1.zcInit` / root initialization — PARTIAL.**

   The off-by-one aspect is genuinely fixed by:

   ```lean
   init : ∀ c, (Sigma 0).pinned c = false
   recursion : ... Sigma (i+1) ... fresh i ...
   ```

   But §C.1.5 initializes the post-root cylinder using D.8 and D.11. Here the root’s actual system is not represented; arbitrary `fresh 0` and `Theta 0` determine `Sigma 1`.

23. **Synthetic `valClauseDownset` — NOT FIXED semantically.**

   The fake theorem was deleted, which is preferable to asserting it. But the replacement is just:

   ```lean
   ht : HtMap
   ```

   plus assumed `zc` and `fresh_above`. No Lean proposition says `ht` is the K1-chain height or that the actual valuation clause equals the literal downset.

24. **Fake `rimLeads` persistence — PARTIAL.**

   The fake proof was removed, but persistence is now assumed wholesale:

   ```lean
   zc : ∀ i hi, ZCData (Sigma (i+1)) ...
   ```

   This is an explicit interface deferral, not a proof. Because `ZCData` itself omits rim level-set grouping and right-side semantics, it also defers a weaker property than §C’s full `(ZC-b)`.

25. **`LST_selection` / `LST_typing` — NOT FIXED as mathematical statements.**

   They were replaced by:

   ```lean
   fresh_above : ...
   ```

   This records only the conclusion that the chosen support is above `floorH`. It neither identifies the support as the entire weight-`γ′` level set nor states `ht = l + Σ innerSlot·κ` with current κ. The crucial LST typing content is absent rather than merely hypothesized.

26. **`EInh_implied` — GENUINE but much narrower than all of C.1(i).**

   ```lean
   ... hbelow ... →
     ∀ x, Sigma.IsSolution x → x j = 0
   ```

   This correctly derives a forced zero from exact downset data. It does not encode implication of inherited value clauses, adjacent hinge clauses, `(γ)` crossing clauses, or rim clauses. Those are said to be absorbed into `JetSetup.recursion`.

27. **`freshFree` — GENUINE relative to the interface.**

   ```lean
   (J.Sigma i).pinned c = false
   ```

   has no rim alternative and follows from `init`, `zc`, `fresh_above`, and `fresh_interior`. This repairs the old local statement.

28. **`conditionalMass` — GENUINE as an abstract combinatorial lemma.**

   ```lean
   ... hfree ... →
   card {x // Sigma.IsSolution x ∧ fd.sat x} * p ^ fd.mstar = Sigma.mass
   ```

   Together with support dependence, exact fiber counts, and disjoint supports, this is the correct Route-B conditional counting statement.

   It does not by itself establish that `fd` is the real fresh content of a node.

29. **`zcPersist` — NOT FIXED; explicitly deferred.**

   It was deleted and replaced by the field `J.zc` at every prefix. That is an honest assumption of persistence only if the setup is later proved to represent the real history. It is not currently a proved §C.1.5(2).

30. **`massRec` and the old `k=0` countermodel — GENUINE indexing repair.**

   ```lean
   (Sigma k).numPinned =
     ∑ i ∈ range k, (fresh i).mstar
   ```

   with `Sigma 0` full is correctly indexed. The exact round-1 countermodel no longer falsifies `massRec`: the root cut belongs between `Sigma 0` and `Sigma 1`.

31. **One fresh object consumed per step — PARTIAL.**

   The recursion references exactly `fresh i` once:

   ```lean
   Sigma (i+1) x ↔ Sigma i (Theta i x) ∧ fresh i .sat (Theta i x)
   ```

   But `fresh i` may have `clauses := []`, or contain only codimension-zero tautologies. Thus one field is consumed per step, but not one genuine fresh block or the D.11 inventory of that read.

32. **`psiBij` — GENUINE as composition of the recorded `Theta`s, PARTIAL as history semantics.**

   `J.Psi` is now an actual iterated composite. But the `Theta`s are not tied to the recorded node transitions. It is therefore a composite recorded by `J`, not yet the composite determined by `H` as required by §C.0.

33. **Unconstrained existential `Dfin` — GENUINE deletion.**

   `thmC_b` counts the explicit image of the final joint locus; no arbitrary existential locus remains.

34. **Final-state admissibility — GENUINE.**

   Both final theorems require:

   ```lean
   hZ : AdmissibleZ (J.Sigma H.nodes.length) Z
   ```

   This is the correct final state.

35. **`thmC_a` — PARTIAL and still substantially tautological.**

   It states:

   ```lean
   Function.Bijective (J.Psi len) ∧
   card {y // ∃ x, Sigma_final x ∧ Z x ∧ y = J.Psi len x}
     = card {x // Sigma_final x ∧ Z x}
   ```

   Once `Psi` is injective, the cardinal equality is a generic image-cardinality fact. The theorem defines its “`S(H,Z)`” subtype as that image; it does not identify an independently defined classifier locus with the image, nor state that it is the solution locus of `T(H,Z)`, nor state the equal pin count claimed in §C(a).

   `C6.transportedSystem` gives a useful separate expansion for `Sigma k`, but `thmC_a` does not include the terminal `Z` transport or an equality with a digit-system presentation of `T(H,Z)`.

36. **`thmC_b` — GENUINE arithmetic for a given presentation, NOT faithful as Theorem C.**

   Its arithmetic is sound for `J`:

   ```lean
   card (image of Sigma_final ∩ Z) *
     p ^ (Σ (J.fresh i).mstar + Z.numPinned) = p^m
   ```

   But the factors are the codimensions of arbitrary `J.fresh i`, not `vol(E_fresh(ν_i))` computed from node data. Therefore a trivial presentation proves a trivial box identity without proving §C(b).

## Fresh sweep

37. **`LevelClause.count` does pin the declared conditional mass.**

   Given `dep`, the set

   ```lean
   {y // sat y ∧ ∀ c ∉ support, y c = 0}
   ```

   is a canonical set of support assignments. Hence

   ```lean
   card ... * p^codim = p^support.card
   ```

   genuinely forces a fraction `p^{-codim}` on the support. Together with disjoint supports and freeness on the solved graph, this is sufficient for `C4.conditionalMass`.

38. **Nevertheless, degenerate clause data are allowed.**

   Examples include:

   ```text
   support = ∅, codim = 0, sat = True
   ```

   and, for any support,

   ```text
   codim = 0, sat = True.
   ```

   These satisfy `dep` and `count`. Such clauses are mathematically valid codimension-zero constraints, but nothing prevents every purported read from consisting only of these or from having an empty clause list. Thus the law self-polices exactness, not semantic provenance or nontriviality.

39. **A trivial `JetSetup` is not ruled out by the vocabulary.**

   Subject to choosing compatible arbitrary `ht`/floor data, one may take identity `Theta`, empty `fresh`, and full `Sigma` throughout. The fields `coherent` and `realizable` do not connect these choices to the node clauses or moves. This is the redesigned analogue of the round-1 artificial-history model.

40. **`fresh_interior` omits the root by design, but also supplies no root geometry.**

   It is quantified only as:

   ```lean
   i + 1 < length → support of fresh (i+1) is inside node i's interior
   ```

   Root freshness relies solely on `Sigma 0` being full. There is no statement that `fresh 0 = E(ν₀)` or that its codimension is D.11’s root count.

41. **`History.floorH` is not the full floor described in §C.1.5.**

   Each contribution is:

   ```lean
   if b < μ * childWidth then line at left block edge else ⊥
   ```

   But §C describes the maximum of line staircases over their clause regions, with surviving old zeros beyond a later factor interior carried into future rim data. The code discards every line outside its factor interior and leaves the rim entirely unconstrained. This may suffice for the narrow `freshFree` proof, but it is not a full formalization of `(ZC-a/b)`.

42. **`Theta_uni` is stronger than needed for bijectivity but weaker than provenance.**

   ```lean
   Theta_uni : ∀ i, IsUnitriangular (Theta i)
   ```

   includes indices beyond the history, though those are harmless junk. More importantly, it says only that a map is unitriangular, not that it is the D.8/D.10 move determined by node `i`.

43. **`recursion` absorbs the central geometric theorem without naming the actual stratum.**

   ```lean
   Sigma (i+1) x ↔ Sigma i (Theta i x) ∧ fresh i .sat (Theta i x)
   ```

   There is no `stratum(ν_i)` or statement equating its intersection with `fresh i`. Consequently C.1(i)’s inherited-clause implication cannot be audited from this interface; it is replaced by a presentation axiom about arbitrary predicates.

44. **`AdmissibleZ` is locally faithful.**

   ```lean
   Z.pinned c = true → Sigma.pinned c = false
   ```

   is exactly the final free-leading-coordinate condition, with unrestricted earlier arguments.

45. **The final theorem does not quantify over an independently defined `S(H,Z)`.**

   The “source locus” is manufactured inside the theorem as the image of the final joint locus. This makes the carriage part true by construction. §C instead begins with the classifier joint-history locus and proves its equality with that transported image and with the solution locus of `T(H,Z)`.

## Honest-gaps audit

46. **R2.C.1, existence of `JetSetup` — HIDDEN WEAKENING, not merely a gap.**

   Deferring existence would be honest if `JetSetup` asserted that its fields present the actual node strata and moves. It does not. Existence of some setup is much weaker and often trivial. The missing property is correctness/provenance, not merely construction.

47. **R2.C.2, `ht =` K1-chain weight — HIDDEN WEAKENING in the present interface.**

   `ht` is bare data, and no proposition records the intended equality even abstractly. `fresh_above` and `zc` can be satisfied by choosing `ht` conveniently. This is not an unproved hypothesis expressing LST(i); the LST(i) sentence is absent.

48. **R2.C.3, `TypObject` existence — GENUINE locally, HIDDEN WEAKENING globally.**

   `TypObject` itself faithfully states support dependence and additive surjectivity, so its existence for an actual value digit is a genuine graded-ring gap.

   But `JetSetup.fresh` is not required to be assembled from `TypObject`s. Thus the main theorem bypasses the claimed existence gap and accepts arbitrary exact-count predicates.

49. **R2.C.4, `N ≥ N(H,Z)` — GENUINE existence gap.**

   The current statements are conditional at a fixed presented cutoff. A later theorem supplying presentations for every sufficiently large `N` could close this without changing the internal combinatorics. The present layer simply does not yet state the full quantifier.

50. **R2.C.5, DIG level-set grouping — PARTIAL GAP, with a weakened `(ZC)` name.**

   If downstream counting truly consumes only rim status, deferring the finer grouping is legitimate for that counting lemma. But the structure and docstring call the result “the `(ZC)` invariant,” while it omits a stated component of §C’s `(ZC-b)`. It should not be treated as a formalization of full `(ZC)`.

51. **R2.C.6, `vtx ≠ 0` — GENUINE residue-field gap, subject to Finding 10.**

   Nonvanishing of polynomial evaluation at the residue root genuinely requires the irreducible quotient/residue-field bridge. Adjacent `(HV)` plus the child’s nonzero pattern lead forces nonzero in that case, but the node-level `vtx ∈ F_{i+1}ˣ` assertion remains deferred.

52. **R2.C.7, `DomData.vertex_entry` — GENUINE lemma-level hypothesis, but bypassed globally.**

   As an explicit input to `C2.DOM`, it is an honest hypothesis. However no final counting statement requires a `DomData`; `fresh_above` is assumed directly. Therefore this does not defer the proof path used by Theorem C—it permits the final theorem to avoid DOM altogether.

53. **R2.C.8, `mstar =` D.11 inventory — HIDDEN WEAKENING and a blocker.**

   This is not merely an existence proof left for later. The equality does not occur in `JetSetup` or the final theorem. Since `mstar` is defined from arbitrary clauses, `thmC_b` has a weaker and different right-hand side from §C(b).

54. **R2.C.9, line intercept tie — HIDDEN WEAKENING and a blocker.**

   A line with the correct slope but arbitrary intercept is not the read-side line of §C. It changes `(NA)`, the staircase floor, and which clauses are “above floor.” Because these quantities feed directly into `Realizable`, `zc`, and `fresh_above`, omitting the tie admits histories and presentations outside the mathematical quantifier.

## Blocking items

55. **No formal provenance relation ties `J.Theta`, `J.Sigma`, `J.fresh`, or `J.ht` to `H.nodes`.**

56. **The final read’s landing transition is not represented in `HistoryCoherent`.**

57. **`mstar` is not equated with the D.11 species inventory, so `thmC_b` has the wrong formal RHS.**

58. **`thmC_a` defines the target locus as an image and proves generic image cardinality; it does not state the classifier-locus or transported-system equalities of §C(a).**

59. **The line intercept and K1-height identifications are absent predicates, allowing degenerate presentations rather than merely deferring proofs of faithful ones.**

60. **Empty/codimension-zero fresh data remain legal at every read, so the redesign forces one indexed `FreshData` object per step but not one genuine fresh block or root system.**

**Final classification: REJECT. Prover fan-out should not proceed on `C5`/`C6` as statements of Theorem C.** The abstract `LevelClause` counting lemmas and several local C0–C4 combinatorial statements are sound, but the global vocabulary still permits trivial presentations disconnected from the accepted §C history.
