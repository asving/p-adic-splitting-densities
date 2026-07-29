# MovesV REV-8 CHARGE (2026-07-29) — round-7 union, orchestrator-adjudicated

Blueprint: lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md (REV 7). Verdicts (READ BOTH):
MOVESV_AUDIT_CODEX7_2026-07-29.md (REJECT 8/2) + MOVESV_AUDIT_FABLE7_2026-07-29.md
(PASS 0 crit / 3 gaps — its HMC-closure sweep and load-bearing checks are CLEAN and
STAND; the Codex criticals are wiring/identity-level and were adjudicated individually).
Produce REV 8 in place; full disposition table. No git. Staged writes ≤4000 tokens.

## NEW STANDING RULE: THE CLOSURE MANIFEST
REV 8 adds a §CLOSURE-MANIFEST table: EVERY identifier consumed by displayed Lean →
its own displayed decl (section ref) or built-source path:line, each entry grep-verified.
This kills the recurring prose-as-def class (N6/N7 this round; C10/C11/C12 last round).

## Adjudicated rulings (bind)
1. N2 — RefEvents + the separation witness (REVISES the round-6 C4 ruling; orchestrator
   analysis): the h₁-split refinement is mathematically sound but INEXPRESSIBLE at the
   toy as built — the PUnit history carrier cannot retain h₁, and tevt_cover as typed
   (per refined state+history) forces each refined state to reproduce the whole coarse
   event. FIX, two coordinated parts: (a) the cover law becomes the FIBER-UNION form —
   coarse tevt at (α, x) = the union over ALL refined (α′, x′) lying above (α, x) —
   equivalently the per-compatible-pair form WITH a law making the refining statistic a
   function of the refined history; (b) the toy carrier is ENRICHED to retain h₁
   (Hist = the h₁ flag instead of PUnit). Then the separation (¬HMC ∧ HMCAug) holds at
   the enriched toy: re-derive it and DISPLAY the check (the h₁ = 0 state's tail domain
   excludes h₂ = 0; the h₁ ≠ 0 state's is full; each factors; the unrefined domain does
   not). Also fix Fable GAP-2 (V4-11(i) says "four TE ties," there are FIVE since
   marks_realize; the RefEvents comment likewise).
2. N1 — Tgam must EQUAL the note's chain count BY LAW, not bound it. The note (7921–23):
   T_γ(x,h) := #{fresh-assignment chains from x realizing (γ,h)}. Currently Tgam =
   (tinst …).card with only marks_chains : Tgam ≤ chainCount — an instance with two
   realizing chains and a singleton tinst passes everything. FIX: add the counting tie
   (an instance-chain bijection law, or Tgam defined as the direct chain-set card over
   the process carrier — you have chainCount table-side; the DIRECT count must come from
   the process side). CONSTRAINT (Fable's clean HMC sweep must survive): whatever law
   you add must NOT introduce a composite decomposition (no law tying tevt/tinst at
   .cons to the step layer). Re-run the HMC-closure sweep yourself and display it.
   Also Fable GAP-3: bracket-correct the two unbracketed historical T_γ lines (revision
   record lines ~29 and ~119 — "chainCount (the note's T_γ definition encoded as the
   recursion)" is the pre-C6 attribution ruled false).
3. N3 — entInst/entEvt are free fields; ent_sel's sibling-disjointness does not tie them
   to the cut. ADD the typed identification: each entInst member's prefix is accepted by
   a lands_sel-bounded EntranceCut (a field/law, not prose — e.g. entInst = the image of
   the cut's accepted set under the instance encoding, or a mem-level law entInst ∋ i →
   cut.lands (decode i) with SelMatches inherited).
4. N4 — the markReading law is promised but absent from the displayed conclusion surface
   (Meas_Stmt has only pairwise disjointness + EqualProjInstance). DISPLAY the reading
   function field + law in the marked carrier (mark ↦ its (m,o,β,height-class) reading)
   and show MarkDisj/MarkDisjT DERIVED from it on the displayed surface. MStep/mEvt get
   real displayed decls (closure manifest).
5. N5 — stepKey's dependent transport is ill-typed: with d.2 : W.toStepCells.symm d.src
   = αc and x : S.Hist q₀ αc, the call needs d.2.symm ▸ x (both branches). Fix; display
   castAssignKey/castAssignKeyT bodies.
6. N6 — close the Defs layer for real: ReadFits, ShapeWFOf, EntTiesAt, emptyPrefix get
   displayed decls (the closure manifest will catch any remainder).
7. N7 — jcellPG and μcellVal get closed displayed defs checked against the BUILT
   RatBurdens fields (lean/LeanUrat/MovesS/Defs.lean — jPCell/jcell_ok/jcell_interp/
   jcell_sum; cite current lines).
8. N8 — V7-9 redesign, card-side: tCount must be ℕ-valued and TOTAL over ℚ (built type
   ∀ … → ℚ → ℕ). Define tCount from the census-card carrier (a Finset.card — ℕ by
   construction), with ValA.tbl_count supplying the polynomial-eval equality AT POOLS;
   handle the empty-mdom outcome explicitly; supply the newer tcount_deg/scount_deg
   fields (built PolyGeomLaws — cite current lines). Outside M.Pools no valuation law is
   claimed (say so).
9. M1 — the E6/E7 bridge RealizedBranching → IsBranchSlot: a real displayed unit (or
   typed hypothesis row) + the Nat.card finiteness fact recorded where used.
10. M2 — XhdS_Stmt's hok binder: obtain it from GcellT_ok … hq (the original structure),
    not an arbitrary premise; drop the "verbatim" overclaim or make it true.
11. Fable GAP-1 — refresh the built-source cites against CURRENT HEAD (repair round 2
    landed in the same commit as REV 7 and shifted MovesD/Defs.lean by ~18 lines:
    EncTargetP now 547–549, encIdx 574–582, E7 comment 570–573; MovesS DetHyp 561–562).
    Verify each by grep at HEAD (the closure manifest covers this henceforth).

Return {units, dispositions, summary}.
