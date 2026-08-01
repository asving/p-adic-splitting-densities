# H4_bp_review — adversarial Codex review of lean/blueprints/HDISCHARGE_H4.md

*(H4 discharge lead, 2026-08-05 swarm. ONE review per the directive. Runner:
`codex exec --skip-git-repo-check --json` on a self-contained prompt (verifier
charge + authoritative-context digest + the full blueprint pasted; Codex cannot
read the repo). Prompt/stream: `/tmp/openmath/H4_bp_prompt.txt`,
`H4_bp_review.jsonl`. VERDICT: **BLUEPRINT-REVISE — 10 CRITICAL, 4 GAP.** All
14 findings dispositioned at the blueprint's §X (same commit); the review text
below is verbatim.)*

---

1. **CRITICAL — The claimed countermodel to (UB-X)(b) is not established.**

> “whenever an interior residual splits … the O_δ classifier realizes positions whose matched letters CHANGED”

M14’s dictionary lemma concerns a position transported with the same keys. The worked \(p=3,\delta=2\) example is expressly “out of domain.” Neither fact proves that the independently reconstructed \(O_\delta\) classifier realizes an unstable position in the common `AD.Pos`, much less that (b) is “false at every composite interface.” Composite \(\delta\) alone also does not guarantee that a realized residue degree shares a factor with \(\delta\). A repair must address the missing realization argument behind the alleged countermodel.

2. **CRITICAL — Route A confuses intrinsic irreducibility with cross-base stability.**

> “the classifier constructs residuals irreducible over the fields where they are read — stability by construction”

Being irreducible in the newly reconstructed \(O_\delta\)-tower does not imply that the same-key \(O_1\) position remains unchanged after unramified extension. The authoritative criterion is the additional condition \(\gcd(m,\delta)=1\). In the described \(q^D\) continuation, merely reading an irreducible residual over the child field does not supply that condition. A repair must address the missing matched-prefix/gcd proof for every K3-c pool.

3. **CRITICAL — Route B does not discharge the stated (UB-X)(b) or (K3-δ).**

> “Under Route B, member (b) and (K3-δ) BOTH rescope to instances of the intrinsic law”

The intrinsic exponent identity does not imply that realized positions are `Stable`, while the authoritative rows explicitly require exhaustion by stable classes and its K3-c restriction. Route B is a replacement obligation requiring ledger-level authorization, not a proof of the current obligation. This also contradicts:

> “The Lean faces … are route-neutral”

`UBXbStmt` and `K3deltaStmt` explicitly assert `AlphabetData.Stable`, so they cannot type Route B’s stability-free law. A repair must address the statement change and the incompatible typed faces.

4. **CRITICAL — The base-alphabet realization argument is mathematically insufficient.**

> “𝔸₁(e₁v) = F₁ (single-slot realizers p^v·(Teichmüller unit) exist over W(F_q))”

A Teichmüller unit from \(W(F_q)\) realizes only a base-residue-field element. In general \(F_1\) has base degree \(d>1\), as the blueprint itself later records through \([F_1:\mathbf F_p]=d\). Thus these elements cannot realize all of \(F_1\). A repair must address realization of the full first residual field.

5. **CRITICAL — The proposed (R4) dictionary violates the governing re-base rule.**

> “residual polynomials transport along F_k ↪ F_k·F_q”

The authoritative REL.1 rule says residue-theoretic objects must be reconstructed over the new residue field and that the re-based tower is not the scalar extension of the old tower. The quoted construction instead describes scalar/compositum transport as the re-based read. A repair must address the distinction between a comparison dictionary and construction of the \(O_\delta\)-tower.

6. **CRITICAL — `H4aTypedFace` is not a typed refinement of (H4a).**

> “The typed candidate for `RootHyps.h4a_r1r4` field refinement … `EQ2law`”

(H4a) is the four stage-tower laws. `EQ2law` is only their downstream alphabet-law consequence. An implementation satisfying EQ-2 need not satisfy any of the stage axioms, digit recursion, weight recursion, or residual-stability conditions. Refining `h4a_r1r4` to this face would silently replace the hypothesis being discharged. A repair must address faithful typing of the actual four rows.

7. **CRITICAL — `LedgerSkel` assumes numerical conclusions instead of representing M14’s hypotheses.**

> “the typed face of what M14’s Theorem consumes from (R1)–(R4)”

Its fields already assert:

> `dim_conf`  
> `tree_stable`  
> `dbase_stable`

These are enough to make `eq2_dim_of_skel` a short arithmetic tautology, but the structure contains no stage axioms, residual fields, digit maps, alphabet product bijection, weight-set conformance, or R4 irreducibility data. In particular, `tree` is unrelated to `StageTuple`, `wSet`, `attainIdx`, or actual alphabets. The future instance therefore bears essentially all mathematical content without a type expressing it. A repair must address this conformance smuggling and missing structure.

8. **CRITICAL — The commutation proof invokes an unavailable and potentially circular transported chain.**

> “the per-entry value correctness over O_δ is Steps 14/16/17/18’s transported chain”

Authoritative Step 16 is currently missing exactly (UB-X)(a), (b), and (c). Therefore “the transported chain” cannot be consumed wholesale to prove (c) without first isolating a pre-commutation result that does not already depend on (c). Moreover:

> “H4-M1 step 8 supplies the walk for the slice this unit needs”

H4-M1 covers only (R1)–(R3); it does not establish the predicted `(EQ-1)` species-catalogue and aggregation-map base independence used in item (2). A repair must address both the circular dependency and the absent EQ-1 input.

9. **CRITICAL — H4-M3 permits (UB-X)(a) to remain unproved.**

> “LIT-4 row resolved or opened as a named lemma”

and

> “write the proof or open a named lemma”

Opening a new obligation does not discharge member (a). Yet later waves and H4-M6 consume “(a)’s audit” as if it were complete. A repair must address closure of every real-content residue before (a) is treated as available.

10. **CRITICAL — The wave plan violates its own dependencies.**

> “Wave 3 (after M1+M4): H4-M5, H4-M6 (parallel).”

H4-M6 expressly consumes “(b)’s law,” which is proved only by H4-M5, and it also consumes (a), whose M3 completion is not a stated Wave-3 gate. If Route B is selected, ledger authorization is deferred to the later ROOT sync, so M5 cannot yet discharge the authoritative row either. A repair must address these dependency and authorization ordering errors.

11. **GAP — `StageTuple` does not enforce the invariant used by `anchorSlot`.**

> “with Bézout companion `t` (`h·t ≡ 1 mod e`)”

The structure contains `e`, `h`, `t`, and `g`, but no proof of that congruence. Consequently `anchorSlot` accepts shapes that are not legal OM stage data. A repair must address enforcement of the Bézout invariant.

12. **GAP — The proposed `posLetter` hard-coding does not establish equivalence with (R4).**

> “prefix stability … HARD-CODED … so Lean `Stable` ⟺ (R4)”

`Stable` is only equality `posLetter δ x = posLetter 1 x`. A single designated off-domain letter does not by itself encode equality of every stage tuple, base degree, and residual degree, nor does it prevent collisions with ordinary letters. No injectivity or dictionary-conformance statement is specified. A repair must address the missing equivalence proof.

13. **GAP — The retyping checkpoint weakens the needed scalar structure.**

> “must RETYPE to additive on F_q-digit blocks”

Additivity supplies only prime-field linearity in general. M14 requires \(\mathbf F_{p^\delta}\)-linearity of the re-based slot map from (R1). Although a later section mentions \(L_0\)-linearity, the plan does not connect that structure to this retyped coordinate statement. A repair must address full \(F_q\)-linearity and its compatibility with the digit coordinates.

14. **GAP — `RealizedLedger` does not type the claimed K3-c semantics.**

> “`Pool` indexes Step-18 K3-c’s realized δ > 1 pools”

The fields record only an arbitrary type, an index, a position, and membership in an arbitrary set. They encode no beta-leg, accumulated residue degree, \(q^D\) continuation, classifier result, or relation to clause (R). Thus `k3delta_of_ubxb` proves only elementary set restriction, not conformance of K3-c pools to that restriction. A repair must address the missing value-side semantics.

**BLUEPRINT-REVISE — 10 CRITICAL, 4 GAP.**
