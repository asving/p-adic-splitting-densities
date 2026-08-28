# UNIT AI6 — adjudicate the A-I.6 fork: is `IFC0.LadderField` refutable at the landed corpus?

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities (all paths below relative to it).

## Context

The capstone `UniformityStatement` reduces to inhabiting `CapstoneHypotheses n`; its signed
`ladder` field routes through E.24 `LadderSupply`, whose fourth conjunct demands
`Ladder.VarthetaRes` at EVERY external index `i ≥ 3` ("the unbounded demand").
`leanfinal/Uniformity/ChapI/IFC0.lean` decomposes this as `LadderField n` (four suppliers,
`ladderField_iff_suppliers`). The VAUD audit (certificates in
`leanfinal/scratch/VAUD_probe.lean`, adjudication in `runs/wave-b/verdict_VAUD.md` and
`docs/in-progress/LADDER_SUPPLY_2026-08-27.md` [VAUD] sections) proved:
- `gauge_view_offRange_kernel_replacement`: at every `¬ GaugeLive core.r i` index, the
  dependent `(v, ρ)` package and `q` can be replaced arbitrarily without changing
  `GaugeFamilyViewEq`;
- `vartheta_sitewise_negative`: a concrete false `HVarthetaRes`;
- `s2_three_not_gaugeLive`: the landed depth-two S2 socket's first demanded index 3 is
  outside the live range.
VAUD explicitly did NOT claim a closed countermodel to `LadderField` itself. The LVT unit
(2026-08-28, `runs/wave-b/verdict_LVT.md`, `leanfinal/Uniformity/ChapI/IFC5.lean`) enacted
the live-range supersession `LadderFieldLive` (restricted fourth supplier via
`CanonicalLadderLiveAt`) and proved OLD ⟹ NEW; the converse is deliberately absent.
The remaining fork, recorded as future amendment A-I.6: either the signed
`CapstoneHypotheses.ladder` must be REBOUND to the live shape (statement amendment at the
leanspec surface, recorded, honesty-preserving), or a GCW-1-style interpretive rider
suffices (capstone bytes frozen; precedent: `leanspec/Leanspec/ChapI.lean` A-I.5 block and
`leanfinal/Uniformity/ChapI/IFC3.lean`/`IFC4.lean` headers).

## Your charge (in order)

1. READ: `IFC0.lean`, `IFC5.lean`, `VAUD_probe.lean`, the [VAUD]+[LVT] sections of
   `docs/in-progress/LADDER_SUPPLY_2026-08-27.md`, `runs/wave-b/verdict_VAUD.md`,
   `runs/wave-b/verdict_LVT.md`, and the A-I.5 precedent block in
   `leanspec/Leanspec/ChapI.lean`.
2. DECIDE the mathematical question: can VAUD's three teeth be assembled INSIDE
   `LadderField`'s quantification — i.e., construct concrete
   `O, K, C, B, G, Kt, L, N, v, ρ, q` (and the socket antecedent data the suppliers
   guard on) such that the first three suppliers' antecedents hold while `VarthetaRes`
   FAILS at some demanded `i ≥ 3`, yielding `¬ LadderField n` for some concrete n (n = 2
   preferred)? Useful landed material: the q = 2 collapse witnesses (C80 territory:
   `|K₁| = 2` makes any degree-1 nonzero-endpoint polynomial `X+1`), the landed S2 socket
   (`s2_degree_four_socket`), and VAUD's replacement lemma as the engine.
3. If YES: land the refutation as a compiling probe
   `leanfinal/scratch/AI6_probe.lean` (verify:
   `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/AI6_probe.lean`;
   NEVER bare `lake build`), zero sorry, `#print axioms` footer, footprints exactly
   [propext, Classical.choice, Quot.sound]. Then the adjudication is FORCED: A-I.6
   rebinding is mandatory (an unfulfillable signed field is a fake-hypothesis honesty
   violation). Write the exact proposed rebinding diff (leanspec + IFC0 anti-drift pin +
   every `CapstoneHypotheses` consumer: grep `h.ladder` and `CapstoneHypotheses` across
   leanfinal/) — but DO NOT ENACT any edit to landed or signed files.
4. If NO (obstruction found): state exactly what blocks the countermodel (which
   antecedent cannot be satisfied simultaneously), and adjudicate rider-vs-rebind on the
   merits: can the capstone inhabitation campaign honestly proceed against the unbounded
   demand (someone must eventually PROVE VarthetaRes at off-range junk indices — is that
   possible-in-principle, e.g. vacuously or by a uniform argument?), or is rebinding
   still the only honest path even without a refutation?
5. UNDECIDED after real effort: name the exact missing ingredient as an open lemma.

## Deliverables

- `leanfinal/scratch/AI6_probe.lean` (if a probe exists) — new file only.
- A dated `[AI6 2026-08-28]` section APPENDED to
  `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` with the adjudication.
- `runs/wave-c/verdict_AI6.md`: verdict (REFUTED / NOT-CONSTRUCTIBLE-BECAUSE / UNDECIDED),
  the recommendation (REBIND per attached diff / RIDER with justification), and every
  claim labeled PROVED (with decl name) vs GAP vs BLOCKED-BECAUSE.

## Rules

No git commits. No edits to any landed .lean file, any leanspec file, or VAUD_probe.lean.
Statements never weakened. A pattern checked on examples is a conjecture, not a proof —
label it so. Quote exact declaration names and line numbers for every load-bearing claim.
