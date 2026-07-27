# MovesX-XE mini-audit — Codex (2026-07-27, via codex exec, detached run)

Charge: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` · Corpus: MovesX-XE · Note:
§X-EXHAUST (`MOVES_2026-07-24.md` ~11170-11470) · Blueprint:
`MOVESX_LEAN_BLUEPRINT_2026-07-28.md` (Layer E §XE.2/XE.3 + §7 REFUTATION RECORD only)
· Lean files audited: `lean/LeanUrat/MovesX/XE2.lean`, `lean/LeanUrat/MovesX/XE3.lean`.

SCOPE (per runner instructions): ONLY the two restated units XE.2/XE.3 + their §7
REFUTATION RECORD. History recap given to Codex: the originals were kernel-certified
FALSE (`∃c ∀p N` forced p-uniform decay at N=1; a point mass at X²+X refuted it); the
orchestrator adjudicated against the note's own display — the (N−1−c_cap) numerator
means the note is vacuous at small N by design — and the restatement binds
`∃N₀ c3 c4` (n,K-only) BEFORE `∀p`, `∀N ≥ N₀`.

Prompt assembled at `/tmp/leanaudit/movesx_xe_prompt.txt` (charge + SCOPE addendum +
note excerpt lines 11170-11470 of `MOVES_2026-07-24.md` + blueprint lines 405-488 and
661-752 of `MOVESX_LEAN_BLUEPRINT_2026-07-28.md` + the full XE2.lean/XE3.lean). Raw run
log: `/tmp/leanaudit/movesx_xe_codex_out.log` (pid 1944425, detached via `nohup ... &
disown`, ~90s wall).

---

## Codex's findings (verbatim)

1. **CRITICAL — XE.2 silently weakens the note to an eventual bound.**

   Offending spec:

   > `∃ N₀ : ℕ, ∃ c3 c4 : ℝ, ... ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N → ... ≤ c3 * p ^ (-(c4 * N))`

   The frozen display states

   > `env(N) ≤ c₃(n)·p^{−c₄(n)·N}`

   without an `N ≥ N₀` restriction. The fact that the intermediate numerator `N−1−c_cap`
   has no coercive content for small `N` does not make the final exponential inequality
   vacuous there: its right side still tends to zero as `p → ∞`. Thus the note's
   displayed assertion is false in the certified countermodel, while XE.2's restatement
   is true. Adding `N₀` changes the claim rather than faithfully formalizing it.

2. **CRITICAL — XE.2 does not enforce the claimed `(n,K)`-only dependence.**

   Offending quantifier order:

   > `(n) ... (X : XFamily n) (K : XConsts n) (PR ...) ... (R ...) : ∃ N₀ ... ∃ c3 c4 ...`

   Since `N₀`, `c3`, and `c4` are existentially bound after `X`, they may depend on `X`
   as well as on `n` and `K`. Merely placing them before `p` proves only
   `p`-uniformity. It does not express the spec's asserted "functions of `(n,K)` alone"
   discipline or the note's `c₃(n), c₄(n)` uniformity across admissible families.

3. **CRITICAL — XE.3 has the same unlicensed eventual weakening.**

   Offending spec:

   > `∃ N₀ : ℕ, ∃ c3' c4' : ℝ, ... ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N → ... ≤ c3' * p ^ (-(c4' * Real.sqrt N))`

   The note instead displays, without a threshold,

   > `env(N) ≤ c₃′(n)·p^{−c₄′(n)·√N}`

   The lack of useful coercivity at small `N` explains why the displayed derivation
   cannot prove a uniform small-level estimate; it does not insert an omitted
   quantifier into the mathematical statement. XE.3 is therefore strictly weaker than
   the frozen display.

4. **CRITICAL — XE.3 also permits `X`-dependent constants and cutoff.**

   Offending quantifier order:

   > `(X : XFamily n) (K : XConsts n) ... : ∃ N₀ ... ∃ c3' c4' ...`

   Again, binding the witnesses before `p` but after `X` does not make them
   `(n,K)`-only. The resulting theorem allows a different cutoff and decay constants
   for each family.

5. **CRITICAL — the §7 adjudication misclassifies a mathematical change as a
   transcription repair.**

   Offending record:

   > "The NOTE is intact: its `(N−1−c_cap)` numerator makes the envelope vacuous at
   > small `N` by design…"

   and

   > "The blueprint's `∃ c ∀ p N` rendering was unfaithfully STRONG…"

   The countermodel establishes the opposite comparison: the original all-`N`
   rendering matches the unqualified envelope display and refutes it; the new
   `N ≥ N₀` rendering escapes by weakening that display. If the intended mathematics
   is only asymptotic, the frozen note itself needs an explicit threshold or
   equivalent qualification.

**Checks that pass** (Codex's words):
- All displayed conditionality tags are present in both units; XE.3 correctly obtains
  `(X2-HYP)` through `AF ∧ CP`.
- The exponent forms are correct: linear `N` for XE.2 and `Real.sqrt N` for XE.3.
- The countermodel does escape the restated statements: choosing `N₀ = 2` makes every
  claimed `Undec N` empty, so either inequality holds for arbitrary positive constants.
- No additional missing hypothesis tag or implausible Lean typing is visible in the
  quoted statements.

**Counts: 5 CRITICAL, 0 GAP. Verdict: REJECT (5 crit / 0 gap).**

---

## Runner's read of the disagreement (not re-litigated, flagged for the orchestrator)

Codex's findings 1–4 all reduce to one structural objection, independent of finding 5:
adding `∃ N₀` before `∀ N` is not a faithfulness-preserving restatement of an
unconditional `∀ N` display — it is a strictly weaker claim (the note's own display, if
taken as `∀ N` verbatim, is simply false per the countermodel; restricting to `N ≥ N₀`
removes exactly the cases (`N ∈ {0,1}` here) where the display was false). Finding 5
is the orchestrator-level version of the same objection, aimed at the blueprint's
narrative ("unfaithfully STRONG" vs "the note is intact").
Finding 2/4 (constants bound after `X` rather than strictly before it) is a second,
independent structural objection about the D9 p-freeness discipline: `X` sits between
`K` and the `∃ N₀ c3 c4`, so nothing in the Lean binder order forces `N₀, c3, c4` to be
functions of `(n, K)` alone rather than of `(n, K, X)` — contradicting the blueprint's
own "(n,K)-only... bound BEFORE p, the D9 discipline" claim about these very units.
Both objection classes are FAITHFULNESS-class per the charge's own rubric (item 1),
not GAP.
