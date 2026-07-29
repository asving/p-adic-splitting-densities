# RATIFICATION REPAIR ROUND 2 (2026-07-29) — D2″/D4″/S5″ per the Codex confirm FLAG

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities. The consolidated Codex
confirm (lean/notes/RATIFY_REPAIR_CONFIRM_CODEX_2026-07-29.md — READ IT) ratified 7/10
round-1 repairs and flagged three. Execute the three follow-ups. Rules as before:
build green throughout (`cd lean && lake build <module>` per unit, full `lake build` at
the end), Lean-core footprints on new decls, no git, staged writes ≤4000 tokens/response.
This round CHANGES two existing definitions under the standing definition-change
authority — the exact changes are specified; everything else additive.

## D2″ — OffsetPPin under-typed (Realizes can be `t ≠ 0`)
Note display (MOVES 4646–4667, quote in docstrings): the (S6b) OFFSET-P-LIFT — "the sum
anchored at the forced slot class j₀ ≡ h⁻¹·(target) mod e, slots j₀, …, j₀+(g−1)e,
prescribed digits"; L1: "the offset-P formula returns a realizer t with w(t) = ν and the
prescribed class"; "the digits t_k are FUNCTIONS of the node data … the policy is
deterministic". Strengthen `OffsetPPin` (lean/LeanUrat/MovesD/PolPin.lean) with laws that
EXCLUDE the `Realizes ν t := t ≠ 0` instantiation:
  (a) SUPPORT LAW: Realizes ν t → t's monomial support ⊆ the arithmetic progression
      {j₀ + k·e : k < g} for a j₀ in the forced congruence class mod e (express the class
      via ν's own (e, h, g) node data and `bezT`/modular arithmetic — the exact form of
      h⁻¹·(target) mod e: derive the target from the node's prescribed residual class
      data as far as MovesD/MovesC vocabulary reaches; whatever needs §B2-DEF vocabulary
      (w(t) = ν itself) STAYS the named residue, documented).
  (b) DETERMINISM: ∀ ν, ∀ t t', Realizes ν t → Realizes ν t' → t = t' (the digits are
      functions of node data).
  (c) keep total/realizes_ne_zero/lift_ne_zero. Then re-verify non-vacuity: exhibit that
      Realizes := (t ≠ 0) now FAILS the laws (a witness comment or a small example lemma).
The confirm's exact objection: "any policy producing nonzero recentering lifts can obtain
an OffsetPPin". After (a)+(b) that must be false.

## D4″ — wire the ∅ dispatch INTO the note-designated objects (kill the parallel API)
The confirm: "A correct alternative API does not wire the empty case into the
note-designated objects and introduces two competing event/multiplicity semantics."
Execute (lean/LeanUrat/MovesD/Defs.lean + consumers):
  (a) REDEFINE (the definition change):
      def Presented.event (S) : Set (Box p m) :=
        if (P : ShapePrefix).reads = [] then Set.univ else ⋃ i, S.fiber i
      noncomputable def Presented.mult (S) (x) : ℕ :=
        if (P : ShapePrefix).reads = [] then 1
        else Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i}
      Docstring cites L5 (MOVES ~4788–4800: the EMPTY prefix INCLUDED, S(∅,⊤) = FULL BOX,
      base of L6) + the F3 deviation record.
  (b) Add the unfolding lemmas `event_of_ne`/`mult_of_ne` (reads ≠ [] → event = ⋃ fiber,
      mult = Nat.card …) and `event_empty_shape`/`mult_empty_shape` (reads = [] →
      univ/1), and patch every consumer proof (D3b, D11b, D12, D13, D14b — each already
      carries an hne or an emptiness hypothesis; rewrite via event_of_ne/mult_of_ne at
      the top of each proof). Statements of those theorems DO NOT change.
  (c) DELETE Presented.eventO/multO and rewrite D14c_emptyEvent.lean to state its laws
      directly on event/mult (eventO_empty_shape → event_empty_shape etc.). No competing
      semantics may remain.
  (d) Check downstream corpora for event/mult consumers outside MovesD (grep
      LeanUrat -rn "Presented.event\|Presented.mult\|\.eventO\|\.multO" excluding
      MovesD) — patch any (expected: none or MovesT-blueprint-only, which is notes).

## S5″ — make the count laws non-bypassable at the CL-6 consumer
The confirm: tCount is free data; both `_counted` variants accept hPGL but do not use it.
CL-6 display (MOVES 12126–12133, quote): "T is one polynomial of degree ≤ W_loc(m) and
each cell size one polynomial of degree ≤ W_state(s), valued correctly at every prime
power — CTS-M(iv)-POLY (CL-6, with V.2's EXPONENT-MAP AUDIT)". Execute
(lean/LeanUrat/MovesS/CountLaws.lean + Defs.lean):
  (a) Restate the `_counted` variants so their CONCLUSIONS consume the laws: each should
      conclude the count-factored form — the Kmat/bTerm entry VALUE at q₀ decomposed as
      (countT value = tCount q₀) ∧ (countS value = the cellInst/cellLvl aggregate) ∧ the
      existing rationality conclusion — i.e. the conclusion must be STRICTLY STRONGER
      than the uncounted form and derivable only through hPGL. Rename honestly if needed
      (`ksub_eval_countFactored`). The proofs consume hPGL's fields.
  (b) tCount stays interim data BUT: add to `PolyGeomLaws` a degree law
      (countT.natDegree ≤ the W_loc bound and countS.natDegree ≤ the W_state bound —
      find the corpus's W carriers; if absent take the bounds as fields of PolyGeomLaws,
      typed ℕ, with the CL-6 degree text quoted) so the laws pin more than values.
      The event-side identification of tCount stays the RECORDED MovesV seam duty
      (Defs.lean 407–409 note stands).
  (c) Report which theorem is the corpus's CL-6/RS.2 consumer and whether it now has a
      counted-premise variant that a MovesV instantiation MUST route through.

## Deliverables (final response ≤4000 tokens)
Per item: decls landed, build status, axiom check, consumers patched (list), deviations.
