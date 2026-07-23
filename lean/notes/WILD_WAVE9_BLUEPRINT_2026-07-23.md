# WILD_WAVE9_BLUEPRINT — JOINT-D1 in Lean (the class-3 descend bijection + tower)
*(2026-07-23. Formalizes `JOINT_D1_2026-07-23.md` (ACCEPTED, 2 Codex passes) — the
deg-2-key class-3 joint ledger. Directive: Claude agents formalize, Codex audits, in
parallel with the remaining math (order-r ≥ 2 via a Case-G gate; D3/D5 at n = 3).)*

## W9a — `OM/DescendBijection.lean` (purely additive, general p; the W8a/RecenterBox pattern)
1. **Θ as a box equiv**: `descendMap (s t ĉ₁ ĉ₀ : R) (m : ℕ)` on 4-tuples by the four J1a
   formulas (in any CommRing R; the p^m enters as `(p:R)^m` — parametrize by `pm : R` to
   keep it ring-generic, instantiating pm := (p:ZMod (p^N))^m); explicit inverse by
   back-substitution; `descendEquiv p N m ĉ : fourBox p N ≃ fourBox p N`. Equiv laws by
   `ring`.
2. **The genuine identity**: for monic quartic f with φ-development (a₁, a₀) (from
   `DevBijection.dev_division_padic`), the φ'-development of f at φ' = φ − p^m·ĉ is
   given by the four formulas — prove `f = φ'^2 + A₁'·φ' + A₀'` by `ring` (self-contained,
   the DevBijection §B pattern), plus the box commutation with toZModPow.
3. **J1-step**: `descend_bijection`: the subtype bijection
   {a ∈ S_{m,c̃}-cylinder} ≃ {b ∈ B'-box} via `Equiv.subtypeEquiv (descendEquiv …)` with
   the membership iff (the J1b digit computations — the F_Q residue steps become
   ZMod (p^N)-digit lemmas in the CellCard.digit vocabulary; the center equations are
   digit-pair identities: digit_m(a₁) = −2c̃-pair, digit_{2m}(a₀) = c̃²-pair with the
   F_Q-multiplication written out as the 2-dimensional pair product (the `gr_mul` form:
   (x̄-part, const): c̃² = (2c̃₁c̃₀ − c̃₁²s, c̃₀² − c̃₁²t)-mod-p — derive from the residual
   convention used in ChainMenuU/mem_squareUnitPairs; MATCH the existing squareUnitPairs
   convention exactly so W9 composes with the W6q pools).
   Cardinality route (mirror J1-step's proof): inclusion + injectivity + equal card, or
   directly exhibit the inverse restricted (implementer's choice; the note's route is
   inclusion+count).
4. **The tower**: `descendTower_bijection` — finite composition over a history
   (M₁ < … < M_k, centers): the joint-stratum subtype ≃ the B_k box, by induction with
   `Equiv.trans` (the note §4's restriction argument: T_j ⊆ B_{j−1} is a `subset`-lemma;
   the restriction of an equiv to a preimage is `Equiv.subtypeEquiv` again). Then
   `joint_count`: #(joint ∩ leaf C) = #C for decidable C ⊆ B_k (Nat.card_congr).
5. **Gates**: p = 2, m = 1, N = 3: the S-cylinder and B'-box cards equal by decide; the
   depth-2 tower (M = (1,2)) card gate tying to the Case-F 144-number (level-5 too big
   for decide — use the closed-form card lemma + norm_num); p = 3 center-pair gate.
6. AxCheck core-only; no sorry; NO type/leaf claim (docstring: counting only; keying =
   the later class-3 faithfulness wave with axiom re-scope, guardian-audited).

## W9b (parallel, math): Case-G gate + order-r ≥ 2 ledger note; D3/D5 at n = 3 (censuses
first). Owner: orchestrator + Codex. NOT dispatched to Lean until their notes are ACCEPTED.

## Done criteria: module green, core-only; census extended; gates tie to Case F/F-odd
numbers; docs/log updated; Codex audit of any statement that cites the math note.
