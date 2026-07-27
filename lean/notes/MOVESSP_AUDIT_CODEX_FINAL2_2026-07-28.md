# MovesSp REV 4 — SECOND final-confirmation Codex audit (2026-07-27)
Prompt: /tmp/leanaudit/movessp_final2_prompt.txt · full transcript: /tmp/leanaudit/movessp_final2_verdict.txt · verdict: REJECT (1 crit / 1 gap)

codex
1. CRITICAL — `CanTreeModel` / `Sp.compMember`

   Offending spec:

   > `len : Branch → ℕ∞`
   >
   > “`len η = 0` is ALSO a REAL case … a Hensel track has an empty catalogue word”

   together with:

   > `theorem SP_COMP ... (hr : (r : ℕ∞) < M.len η) : InCatalogue n (M.datum η r)`

   The quoted justification conflates “NO window read ever opened” with an empty catalogue word. The frozen note explicitly says that at `n = 1` the catalogue word is the single confirming ROOT letter, while only the τ-word is empty. Yet `CanTreeModel 1 p f` may have every branch satisfy `len η = 0`; then `hRoot`, `hStage`, `hCoh`, `hHalt`, and every SP-COMP conclusion are vacuous. `hTotal : Nonempty Branch` prevents an empty branch type but not this degenerate all-zero model. The independent `Sp.n1singleton`/`Sp.n1Word` units do not connect an actual `CanTreeModel` branch to a `CatalogueWord`.

2. GAP — `Sp.n3thresholdData`

   Offending spec:

   > `theorem threshold_data_pinned :`
   > field-size filter identities `∧`
   > the six literal species `∧`
   > group membership/Nodup `∧`
   > six `Nstar3six` values `∧`
   > total domain checks `∧`
   > exclusion cardinalities

   This combines distinct note displays: the two field-size exclusion catalogues, the six multi-side species, and the six threshold computations. It is a hidden multi-lemma unit rather than one short display, contrary to the required decomposition discipline.

The unbounded-read adjudication itself is otherwise correct: the note expressly leaves READ counts unbounded and bounds only collapsed prefixes by `6n²`; `Sp.compCollapsed` preserves that distinction. The VP rider is also visibly named and correctly recorded as `[3t]`-owned rather than promoted to a definition. The SUCC domains, global menu closure chain, Bool-routed decision targets, six literal species, exclusion rosters, `n = 1` literal, and the R6 entrance erratum all agree with the frozen displays.

Counts: 1 CRITICAL / 1 GAP

REJECT (1 crit / 1 gap)
