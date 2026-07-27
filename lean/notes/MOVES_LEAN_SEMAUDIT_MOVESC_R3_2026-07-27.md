Verdict: REJECT. The round-3 rebuild materially improves the interface, but rev 14 changed the realizability class in a way the Lean vocabulary does not encode. In addition, blockers 55, 57–60 are only partially repaired. The 13 RETYPE/NEW units should not go to provers yet.

## Round-2 blockers 55–60

1. **B55 — PARTIAL.**

   Relevant new text includes:

   > `pres_theta : ... pres (i+1) x f → pres i (Theta i x) f`

   > `recursion : ... (Sigma (i+1)).IsSolution x ↔ ((Sigma i).IsSolution (Theta i x) ∧ stratum i (Theta i x))`

   > `inh_implied : ... (Sigma i).IsSolution y → (stratum i y ↔ (fresh i).sat y)`

   > `fresh_assembled : ...`

   and the replacement of the free `ht` field by `History.htH`.

   These genuinely connect `Sigma` to `Theta`, `stratum`, and `fresh`. But `Theta` is still not uniquely characterized as the re-development map attached to `keys i`: `pres` is abstract, `pres_theta` is only a one-way preservation property, and arbitrary block-local unitriangular recodings can be absorbed into a suitable `pres`.

   More seriously, `fresh_assembled` specifies permitted clause shapes, not that the clauses are exactly the node’s D.11 species inventory. Supports need not cover the recorded fresh band or equal the appropriate per-slot level sets. Thus `fresh` is still only partially tied to the node history.

2. **B56 — GENUINE, for the specific round-2 omission.**

   The decisive text is:

   > `landing : ∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i)`

   Unlike `keys_mid`, this quantifies over every read, including `i = length − 1`. The final read’s landing key is now represented. The missing post-final valuation/residue-stage package is a separate rev-14 tuple issue, not the original B56 omission.

3. **B57 — PARTIAL.**

   The new equality is:

   > `(fresh i).mstar = Nat.card {c : Fin m // ... floorH ... < htH ... ∧ htH ... ≤ lineStep ...}`

   This prevents `mstar` from being arbitrary. It is not yet formally the D.11 inventory, however. Lean supplies no equivalence between:

   - clauses in `(fresh i).clauses`,
   - the individual `(α)/(β)/(γ)` and hinge species,
   - their complete level sets and attainable alphabets, and
   - the coordinates counted by this band.

   The problem is amplified by the missing recorded `u*`: `lineStep` is computed from a line with an inadequately constrained intercept. Consequently the displayed RHS is a node-dependent band count, but not yet the rev-14 D.11 species inventory.

4. **B58 — PARTIAL.**

   The improved equality is:

   > `J.SHZ Z = (J.Psi H.nodes.length) '' {x | (J.Sigma ...).IsSolution x ∧ Z.IsSolution x}`

   and `SHZ` does not mention `Sigma` or an image. That removes the round-2 image-cardinality tautology.

   Nevertheless, `SHZ` is defined to be the solution predicate of the transported fresh-chain itself:

   > `{x | ∃ y, ... (J.fresh i).sat (y i) ... ∧ Z.IsSolution ...}`

   Thus the rev-14 equality

   > “`S(H,Z)` is exactly the solution locus of `T(H,Z)`”

   remains definitional/absent: there is no independently classifier-defined `S(H,Z)` related to the transported system. Only the second equality, with the transported final joint locus, is genuinely proved.

5. **B59 — PARTIAL.**

   The height half is substantially repaired:

   > `History.htH ... := level + Σ innerslot·kappaH`

   and the adjustable `JetSetup.ht` field is gone.

   The intercept half is not faithful to rev 14. `HistoryCoherent` only contains comparisons between consecutive arbitrary `Line` fields:

   > `old.line.at (...) ≤ new.line.at (...)`

   and, in the adjacent case,

   > `old.line.at (...) = new.line.at (...)`.

   Rev 14 instead makes `u*_i` node data and defines the line as the line of slope `−h_i/e_i` through `(j*_i,u*_i)`, with `u*_i` on-lattice and tied to the standing vertex when adjacent. Lean has no `u*`, no on-lattice predicate, and no root intercept anchor. Simultaneously translating all line intercepts remains legal and changes floors and `mstar_eq`.

6. **B60 — PARTIAL.**

   The relevant repair is:

   > every clause is either a singleton codimension-one zero clause or a `TypObject` value clause,

   together with `mstar_eq`.

   This excludes an empty fresh list when the computed band cardinality is positive. It does not force the fresh list to be the recorded inventory. A value clause may use a proper subset of a level set, combine coordinates from unrelated blocks sharing a height, or be placed at a height/support unrelated to the read line, subject only to `fresh_above` and `fresh_interior`.

   Codimension-zero, always-satisfied value clauses also remain legal. More importantly, positive codimension may be moved to unrelated above-floor supports while preserving the same total `mstar`.

## F10 re-adjudication

7. **F10 — PARTIAL FIX, with the principal index correction GENUINE.**

   These changes are correct and necessary:

   > `Node.mhat (ν) := -ν.t * ν.h * ν.g`

   > `IsNodeLift` uses `ν.e` and `ν.h`

   > child-frame ties `σ'.s = ν.s` and `σ'.t = ν.t`

   This fixes the round-2 error of using the frame-creating read’s `σ.e, σ.h` for the node currently being read. Keeping `ν.σ.t` inside the Laurent realization condition is not by itself evidence of the old bug: that occurrence belongs to the current frame’s residual-map normalization, whereas `ν.t` supplies the read-side D.5 normalization exponent.

   The remaining defect is that rev 14 calls `(sᴮ,tᴮ)` a conventionally selected function of `(e,h)`. Lean records an arbitrary Bézout solution:

   > `hbez : e * s + h * t = 1`

   Apart from recenterings, nothing makes this pair canonical or determined by `(e,h)`. Since `mhat` and hence `vtx` change when another Bézout solution is chosen, this is semantically material. The field names `s` and `t` are harmless because the polynomial recentering lift is separately named `lift`; the missing canonicity is not harmless.

## Rev-14 delta

8. **(SAE) is absent — RETYPE-REQUIRED.**

   `Realizable` contains only `(NA)` and `(HV)`. The exact missing rev-14 sentence is:

   > “`new(j) > old(j)` for every span slot `j ∈ [s₀',j*]`, `j < μ_i`; and `new(μ_i) = old(μ_i)` when `j* = μ_i`.”

   Equivalently, the non-adjacent endpoint must satisfy `new(j*) > old(j*)`. Lean’s coherence field gives only `old(j*) ≤ new(j*)`, permitting equality in the certified F-EMPTY configuration.

9. **The actual realizability class is therefore not encoded — RETYPE-REQUIRED.**

   Rev 14 states:

   > “A lift-carrying history is REALIZABLE iff … `(NA)+(HV)+(SAE)`.”

   Lean’s docstring and definition still explicitly describe realizability as “the two data-side conditions.” This is not a documentation-only mismatch: histories violating SAE satisfy `JetSetup.realizable`.

10. **`TRANSITION-ADMISSIBLE` is absent — RETYPE-REQUIRED.**

   The exact required sentence is:

   > “A read `ν_{i+1}` appended to a prefix is TRANSITION-ADMISSIBLE iff the extended prefix through `ν_{i+1}` satisfies `(NA)+(HV)+(SAE)` at the appended read.”

   Rev 14 further requires:

   > “The per-step statements (C.1, C.1.0(b)(iii), C.1.5) HYPOTHESIZE this of their appended reads.”

   No such predicate or per-step argument exists. A corrected whole-history `Realizable H` could be used as a stronger hypothesis in global `JetSetup` theorems, but it would not repair `C3.lineDom`, which currently assumes only `HistoryCoherent H`. Moreover, the present global `Realizable` lacks SAE anyway.

11. **The side height `u*` is absent — RETYPE-REQUIRED.**

   The exact tuple sentence to encode is:

   > “the SIDE HEIGHT `u*_i :=` the right-endpoint height (on-lattice; at an ADJACENT read, `u*_i` is the standing window-vertex height). These determine the read-side LINE … slope `−h_i/e_i` through `(j*_i,u*_i)`.”

   `Node.line` plus an abstract intercept comparison does not encode this datum or its role.

12. **The finalized Bézout convention is only partially encoded — RETYPE-REQUIRED.**

   The sentence requiring encoding is:

   > “with `(sᴮ_i,tᴮ_i)` the read’s Bézout pair … a function of `(e_i,h_i)` only.”

   `hbez` records a solution, not the selected function. `hspecRecBez` correctly handles the rev-14 recentering base case.

## Fresh whole-file sweep

13. **`ψ` irreducibility is missing — blocking new unfaithfulness.**

   Rev 14 requires:

   > “`ψ_i` monic irreducible over `F_i`.”

   `Node` records `hψmonic` and `hψdeg`, but no irreducibility predicate. Reducible residual factors are legal Lean nodes and need not define the stated residue-field extension.

14. **The anchor is unconstrained — blocking new unfaithfulness.**

   Rev 14 says:

   > “the anchor `a_i` … `= ord_z R(f)` on the locus”

   and defines `R_anch` through the stride positions relative to that anchor. Lean’s `a : ℤ` occurs only in the scalar exponent of `vtx`; no field ties it to the side pattern, stride positions, or anchored residual. Changing `a` can change `(HV)` while leaving every other node law unchanged.

15. **The final residue-extension datum is incomplete — PARTIAL provenance.**

   Rev 14 derives:

   > `F_{i+1} = F_i[z]/(ψ_i)`.

   Interior transitions may obtain some of this from `TransitionCoreL`, but the final node has only `hzbarRoot` and `LandingKey`. A root of `ψ` in the ambient `F` is weaker than identifying the next residue field with the quotient, especially while irreducibility is absent.

16. **`C3.lineDom` has the wrong semantic hypothesis boundary — blocking moved quantifier.**

   Its statement assumes only:

   > `(hcoh : HistoryCoherent H)`.

   Rev 14’s DOM statement is:

   > “For every realizable prefix…”

   and its proof explicitly sources the span-entry inequality from `(SAE)`. Round 3 moved a weakened, non-strict shadow of SAE into `HistoryCoherent`, then claimed DOM from coherence alone. That admits histories outside the rev-14 realizability class and obscures the hypothesis consumed by the mathematics.

17. **The fresh inventory can be permuted away from the geometric species — blocking.**

   Neither `fresh_assembled` nor `mstar_eq` says that every counted fresh-band coordinate belongs to exactly the corresponding strip or complete value-level-set clause. Equal total codimension is insufficient: the same total can be realized on unrelated above-floor coordinates. This is a nontrivial satisfiability loophole, not merely the admitted codimension-zero junk.

18. **Zero-cutoff presentations remain legal — blocking degeneracy.**

   `JetSetup` has no `1 ≤ N` or `N ≥ N(H,Z)` field. With `N = 0`, `m = n*N = 0`; `pres_zero` becomes vacuous and the coordinate/fresh systems collapse even for positive `n`. Rev 14 explicitly has:

   > “for every `N ≥ N(H,Z)`,”

   with `N(H,Z) ≥ 1`.

   Deferring existence for sufficiently large `N` is legitimate, but permitting a `JetSetup` at `N=0` makes the current theorem quantify over degenerate presentations that are not instances of Theorem C.

19. **Root cluster geometry is not forced — blocking consequence of the missing intercept datum.**

   Rev 14’s DOM base requires the root line to dominate the cluster floor, with root side heights at least the cluster-zero level. Since the root line intercept is free and `floorH 0 = ⊥`, `mstar_eq` may omit root cluster zeros entirely. Neither `LandingKey` nor `HistoryCoherent` supplies the root-side height condition.

20. **Final disposition.**

   The blocking retypes are: full `(NA)+(HV)+(SAE)` realizability, an explicit transition-admissible/per-step interface, recorded `u*` with line/intercept/on-lattice ties, canonical read Bézout data, irreducible residual factors, anchored-residual provenance, exact fresh-species coverage, and a positive/sufficient cutoff condition. `C3.lineDom`, `C6.thmC_a`, and the fresh-counting spine depend directly on these defects.

**Final classification: REJECT.** The 23 frozen local units remain unaffected, but the 13 round-3 RETYPE/NEW units should not be released to provers as statements of rev-14 §C.
