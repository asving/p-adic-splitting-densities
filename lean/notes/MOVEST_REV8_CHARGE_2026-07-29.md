# MovesT REV-8 CHARGE (2026-07-29) — round-7 union, orchestrator-adjudicated

Blueprint: lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md (REV 7). Verdicts (READ BOTH):
MOVEST_AUDIT_CODEX7_2026-07-29.md (REJECT 5/1) + MOVEST_AUDIT_FABLE7_2026-07-29.md
(2 crit/2 gap). 15 of 19 rows verified REAL by both; the residue is five converged items.
Produce REV 8 in place; full disposition table. No git. Staged writes ≤4000 tokens.

## NEW STANDING RULE (this rev on): THE CLOSURE MANIFEST
Round after round, "closed" defs turn out to be prose (this killed rows in rounds 6 AND
7 on the sibling corpus). REV 8 adds a §CLOSURE-MANIFEST: a table listing EVERY
identifier consumed by displayed Lean in this blueprint → its own displayed decl (section
ref) or its built-source path:line. Verify each entry by grep before tabling it. An
identifier with neither is a defect you must fix before shipping the rev.

## The five items (both-leg convergences; rulings bind)
1. ChildCover INSTALLATION (Codex#1; Fable judged the content sound but Codex checked
   the wiring — Codex is right): ChildCover is a standalone predicate; the displayed
   CellAssign ends at child_cell_red and NO displayed consumer (T-E5, TreeExpFin,
   TreeNStmt, VPPinned, rs1GivenOfMovesT) takes hccov. FIX: make it a FIELD of
   CellAssign (child_cover : ChildCover …) — the W4-1 ruling says the INTERFACE itself
   rejects the constant-false-child model. Consequence: the toys must now instantiate it
   — verify they do (the per-track witness exists in both toys after the round-6 guard
   fix: check!) or re-fence the toy scope HONESTLY and disclose. Re-run all decide
   checks; census integers must stay unchanged.
2. NsBridgeStmt IS FALSE AS STATED (Codex#3 = Fable CRIT-1, with Fable's full in-corpus
   counter-model: childless-tower Tat + junk H with μ·Dwidth = 0 gives interior roster
   ∅, L ≡ univ, ratios ≡ 1, μcap ≡ 1, μclass = 1 — premises hold, conclusion demands
   1 = 0). The note's proof (7216–7233) is: (ii) C(b) pricing μ(Σ ∩ L_M) =
   μ(Σ)·p^{−|Z_M|}; (iii) |Z_M| → ∞; THEN continuity from above. FIX: restate as the
   note's conditional — premises gain the pricing equality field AND the growth field
   (|Z_M| → ∞, or directly Tendsto μcap atTop (nhds 0)), plus identification fields
   (μclass = the (τ-ns) class mass carrier; μcap M = the cap mass at level M). Then
   RE-RUN Fable's counter-model — it must die on the new premises (the μcap ≡ 1 instance
   must fail the decay leg). Display that check.
3. T-F4 belowHalt_decomp FALSE at the ∅ shape (Codex#5 = Fable CRIT-2): at reads = [],
   built mult ≡ 1 but PrefIdx = ∅, so 1 = 0 + 0. FIX: the same hne premise D11a took
   (Fable names it), + an explicit ∅-shape display via mult_empty_shape (the note-side
   1 = 1 through the option-level object — repair round 3 is adding the additive
   option-level incidence theorem D11a_opt to MovesD; you may cite it as in-flight with
   its exact name/type).
4. Toy roster lawfulness (Codex#4 + Fable GAP-2, complementary): (a) the e·g = 1 leaves
   CANNOT be .increment (built hspecInc : species = increment → 1 < e·g) — they are
   RECENTERINGS; re-pin species and re-check every law that dispatches on species.
   (b) the γ pins violate the γ-tie (built law: gam = e·(STR·ustar) + (s0+wSide)·h;
   Fable computed lawful values: heads γ = 3 (not 1), leaf a γ = 4 (not 2), leaf b γ = 6
   (not 3) — or adjust u* instead; pick ONE lawful assignment and re-verify no gate or
   census consumes gam (Fable checked: none does — keep it that way)). (c) pin the FULL
   line (intercept, not just slope). (d) display the realizability obligations for
   Ranch := 0 / ψ := X / μ > 0 against TreeModel.mem_realizable (the ψ-order and pat
   facts) — either show they hold or re-pin Ranch. Re-run ALL decide checks + census.
5. OmSat (Codex#2 + Fable GAP-1, two halves of one fix): (a) the realized-membership
   conjunct inside ClusterFactorOf cannot cure implication-vacuity (junk trackOf ⇒
   empty antecedent ⇒ OmSat trivially true). ADD the totality direction as its own typed
   law where the note asserts existence (re-read the note's OM-SAT display in §T-ASSEMBLY
   and type the existence quantifier: every realized saturated history HAS an fη with
   the ClusterFactorOf package). (b) RE-ATTRIBUTE record 19: the real protection against
   junk trackOf is ruling 2's SHARED trackOf (KBTotTower.root_total makes VPPinned
   uninhabitable under junk trackOf — Fable's analysis); the conjunct's genuine role is
   the wrong-reduction/over-strength direction. Fix the record and the row.

## Gap
6. hRes: the "exact on every nonempty history" claim exceeds the displayed support —
   scope the exactness claim to lawful histories (add the lawfulness hypothesis to the
   claim, or weaken the claim to what junk histories support; the accessor def itself
   stays closed).

Return {units, dispositions, summary}.
