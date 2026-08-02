/-
`Scaffold/HDischarge/H7/H7Probe.lean` — **the (H7) FIRST PROBE** (synthesis-6 queue #7;
pass-6 F4 finding: "(H7) LIVE-BUT-NEVER-PROBED — the pair has no compiled or numeric
decision point of its own").  Countermodel-first entry per the [M]-row protocol: pin the
exact (I-τ) and K-LOC statements, then DECIDE each at the cheapest compiled instance in
the corpus bin (toyStage3, bStageP, td2V4, H₃rc — plus the walk's find, toyTreeA).
Record: `lean/notes/openmath/H7PROBE_2026-08-08.md`.

## The two statements, pinned (HDISCHARGE_H7.md REV 2; ROOT §3.1 (H7))

**(I-τ)** — at every realized site s of the canonical tree with continuing branch roster
{ν₁,…,ν_m}, m ≥ 2, and K-FACT tuple dec = f₀·∏f_j, the site's stratum presents as O-10's
ρ-separated adapted cell: Σ_c = μ_N(C₀ × ∏_j C_j), C₀ the pinned f₀ cell (τ(c)-keyed, no
event), C_j the K_j-keyed per-branch factor strata, K_j ≤ thr(c) + ρ(c) (§2.1 IT-1/IT-2).

**(K-LOC)** (= M07 OL-3) — given the frame kernel KL-0, there is a cell-constant
normalization ε_j(c) = (δ_{j,r}(c), u_{j,r}(c)) with, per continuation level r of branch
j on the polydisc: (i) the λ_{j,r}-side of N_r^−(F) in the t_j-frame = that of N_r^−(g_j)
translated by δ_{j,r}(c); (ii) R_{λ_{j,r}}(F) = u_{j,r}(c)·R_{λ_{j,r}}(g_j); (iii′) every
prescribed-finite-subtree event of branch j pulls back to residue classes E_j mod p^{K_j}
of the factor coordinate (§1.1).

## Verdict table (this probe; full walk in the note)

| face | toyStage3 | bStageP | H₃rc | td2V4 | toyTreeA/toyLedgerA (walk find) |
|---|---|---|---|---|---|
| (I-τ) | VACUOUS (type) | VACUOUS (type) | VACUOUS (type) | VACUOUS (type) | STATABLE-BUT-DEGENERATE (P-2) |
| (K-LOC) full | VACUOUS | VACUOUS | VACUOUS | VACUOUS | DEGENERATE (diagonal read, P-2) |
| KL-1a count face (order 1) | HOLDS (ℤ/3, §D) | HOLDS (F4, §D) | HOLDS (F4, §D) | HOLDS (ℤ/2, §D) | — |

VACUOUS (type): the instance's TYPE cannot carry the statement's subject — `Stage` is one
OM read of one branch (single key Φ; `reps` is the U-representative list, NOT a roster);
`History` is one chain (the sibling roster lives only at `VTree`/`CellData` level);
`LedgerStratumDataV4` is a digit-window carrier (slots = window positions on ONE line; no
factorization tuple anywhere in the type).  No countermodel is obtainable at any of the
four — nothing to refute a statement that cannot be instantiated — so NO restatement is
pinned; the REV-2 statements stand as drafted.

## Findings (P-1 … P-4)

**P-1 (the bin is roster-free).**  None of the four charter instances can express either
face; certificates §B.  The pair's first compiled decision point is NOT in the corpus
instance bin — confirming pass-6 F4 at compile level.

**P-2 (the only compiled m ≥ 2 site is triply degenerate).**  The walk found exactly one
compiled sibling object in the corpus: `toyTreeA` (G1_toyGate), chains {tA1, tA2a, tA2b},
with the branching cell roster `toyBranchA .splitC = {toyLeafA, toyLeafB}` of card 2
(certificates §C, Lean-core).  But the site CARRIER over it cannot non-degenerately
decide either face, for three source-pinned reasons kept OUT of this file's compiled
perimeter (each would import `sorryAx`; measured 2026-08-08, scratch `#print axioms`):
(a) the site read is the DIAGONAL — `branchCellOf := fun es _ν => toyCellA es`
(G1_toyGate:723): sibling reads are definitionally equal, so any K-LOC "check" there
compares a function to itself (ε_j trivial) — a degenerate HOLDS of no evidential value
(the review-finding-16 genre); (b) the ledger prices every site 1-sided — `sides := fun _
=> 1` (G1_toyGate:1496), `splitAt`/`hsplit_k`/`hsplit_exp` discharged vacuously by
`omega`-absurd: no compiled leg ever exercises an m ≥ 2 presentation; (c) the carrier
chain `toyModel`/`toyCA`/`toyLedgerA` itself depends on `sorryAx` (the two
`mem_realizable` sorries, G1_toyGate:561/:794 — one marked BLOCKED-FALSE at :2814).

**P-3 (the one decidable fragment HOLDS at every bin field).**  KL-1a's order-1 count
face (ω-blindness of ψ-coprime cofactors, unit H7-C2 `pow_dvd_mul_iff_of_coprime_cofactor`,
landed PROVED) is DECIDED HOLDS by explicit instantiation at each instance's own field:
ℤ/3 (toyStage3's residue field, card 3 = `toyStage3_card`), F4 = GF(4) (bStageP's and
H₃rc's ambient), ℤ/2 (the toys' ambient; td2V4's q₀ = 2 alphabet) — §D.  This is the ONLY
(H7) content with a compiled decision anywhere; KL-0, KL-1b/1c, KL-2, KL-3, KL-4, (iii′),
IT-2⊇, IT-4b have none.

**P-4 (route implication — cheapest non-degenerate extensions).**  Lean side: NONE cheap.
The named cheapest is H7-W3a's `gate_order0_semantic` (decide-small p = 2, n = 2, N = 2
box enumeration), blocked on OL-2 ledger inhabitation — which this probe SHARPENS: an
OL-2 inhabitant must break BOTH rfl-degeneracies of P-2 (register sides ≥ 2 at a branching
site AND supply a non-diagonal `branchCellOf`), on a sorry-free TreeModel.  Near-term
decision point is therefore the NUMERICS harness N-H7-1 (`h7_kloc_probe.py`, blueprint §5
— the read-conformance falsifier), exactly the pass-6 F4 charter artifact.

Fences: no existing statement touched; no Tier-S Prop shells added (deliberately — the
Tier-M rows stay §3.7-owned); `MovesT.SibJcRows`/`CellData` and parked items 22–29
untouched.  All declarations below are Lean-core (§E census).
-/
import LeanUrat.MovesT.G1_toyGate
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.B2D.HuniV4Probe
import LeanUrat.Scaffold.HDischarge.H1.RCWitness
import LeanUrat.Scaffold.HDischarge.H7.Rows
import LeanUrat.Scaffold.HDischarge.H7.ResTrans

namespace LeanUrat.Scaffold.HDischarge.H7.Probe

open LeanUrat.MovesT LeanUrat.MovesC

/-! ## §B — instance anchors (the four charter instances; verdict VACUOUS each)

Each anchor pins the instance's single-branch shape by `rfl`/`simp` on clean constants
only.  The vacuity itself is TYPE-level (see header); an anchor is a witness of WHAT the
instance is, not a proof of a negative. -/

/-- §B.1 [toyStage3 : `Stage 3 (ZMod 3)`, G1_toyGate]: one OM read — single key Φ = X,
empty U-representative list.  A `Stage` has no roster/site/product field: both faces
VACUOUS.  (KL-1a face at its field: `kl1a_decided_zmod3`.) -/
theorem toyStage3_anchor :
    toyStage3.Φ = Polynomial.X ∧ toyStage3.reps = [] :=
  ⟨rfl, rfl⟩

/-- §B.2 [bStageP : `Stage 2 F4`, HK13]: one OM read — single key Φ = X (its
`reps = [C 2]` is the U-list of DEF-3, p-and-previous-keys data, not a branch roster).
Both faces VACUOUS.  (KL-1a face at its field: `kl1a_decided_F4`.) -/
theorem bStageP_anchor : LeanUrat.MovesJ.bStageP.Φ = Polynomial.X := rfl

/-- §B.3 [H₃rc : `History 2 F4`, H1/RCWitness]: ONE chain of three nodes (root →
σ₁rec → the recentering-ended leaf).  `History` carries no sibling data — the roster
vocabulary starts at `VTree.chains`/`CellData.branchSetOf`, and no compiled `VTree`
contains H₃rc.  Both faces VACUOUS. -/
theorem h3rc_anchor : LeanUrat.Scaffold.HDischarge.H1.RCW.H₃rc.nodes.length = 3 := by
  simp [LeanUrat.Scaffold.HDischarge.H1.RCW.H₃rc]

/-- §B.4 [td2V4 : `LedgerStratumDataV4 tdD td2W td2P`, B2D/HuniV4Probe]: the d-leaf
digit-window carrier at N = 2, q₀ = 2 — window slots on one line (junction slot 0 +
free slot 1), no polynomial factorization in the type.  Its landed uniformity content
(`slotUniform_td2V4`) is (FRESH)/huni counting, NOT sibling-interface content.  Both
faces VACUOUS. -/
theorem td2V4_anchor : LeanUrat.B2D.td2V4.N = 2 ∧ LeanUrat.B2D.td2V4.q0 = 2 :=
  ⟨rfl, rfl⟩

/-! ## §C — the walk's find: the corpus's ONLY compiled sibling pair (finding P-2)

`toyTreeA` branches at tA1 into tA2a/tA2b, and the branching cell's roster has card 2.
These five certificates are Lean-core (they cite only the tree/roster layer, never
`toyModel`/`toyCA`/`toyLedgerA` — the `sorryAx`-tainted carrier chain of P-2(c)). -/

/-- §C.1: the two toy leaves are distinct reads (their slope numerators differ: h = 2
vs h = 3). -/
theorem toy_leaf_ne : toyLeafA ≠ toyLeafB := by
  intro hEq
  have hh : toyLeafA.h = toyLeafB.h := congrArg Node.h hEq
  simp [toyLeafA, toyLeafB] at hh

open Classical in
/-- §C.2: the branching cell's roster, by definitional reduction. -/
theorem toy_roster : toyBranchA ToyCell.splitC = {toyLeafA, toyLeafB} := rfl

open Classical in
/-- §C.3: roster card 2 — the (H7) subject's m ≥ 2 EXISTS in the corpus exactly here. -/
theorem toy_roster_card : (toyBranchA ToyCell.splitC).card = 2 := by
  rw [toy_roster, Finset.card_pair toy_leaf_ne]

/-- §C.4: both extensions of tA1 are chains of `toyTreeA`, and they are distinct —
the compiled sibling PAIR (tA1's two continuations). -/
theorem toy_sibling_pair :
    tA2a ∈ toyTreeA.chains ∧ tA2b ∈ toyTreeA.chains ∧ tA2a ≠ tA2b := by
  refine ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), ?_⟩
  intro hEq
  have hn : tA1.nodes ++ [toyLeafA] = tA1.nodes ++ [toyLeafB] :=
    congrArg History.nodes hEq
  have h1 : toyLeafA = toyLeafB := by simpa using hn
  exact toy_leaf_ne h1

/-- §C.5: both siblings continue the SAME parent chain tA1 (nodewise list prefix). -/
theorem toy_sibling_parent : tA1.IsPrefixOf tA2a ∧ tA1.IsPrefixOf tA2b :=
  ⟨⟨[toyLeafA], rfl⟩, ⟨[toyLeafB], rfl⟩⟩

/-! ## §D — the KL-1a order-1 count face, DECIDED at the bin's fields (finding P-3)

The one (H7) fragment with compiled decision content: unit H7-C2's ω-blindness law,
instantiated at ψ = X, cofactor g = X + 1 (ψ-coprime: constant coefficient 1 ≠ 0), at
each charter instance's own field.  Scope EXACTLY as H7-C2's docstring: this decides
none of KL-0/KL-1b/1c/KL-2/KL-3/KL-4. -/

/-- §D.1 [toyStage3's residue field ℤ/3]: ψ-power reads are blind to the coprime
cofactor — KL-1a count face HOLDS at the p = 3 instance's field. -/
theorem kl1a_decided_zmod3 (f : Polynomial (ZMod 3)) (k : ℕ) :
    (Polynomial.X : Polynomial (ZMod 3)) ^ k ∣ f * (Polynomial.X + 1) ↔
      Polynomial.X ^ k ∣ f :=
  pow_dvd_mul_iff_of_coprime_cofactor Polynomial.irreducible_X
    (by rw [Polynomial.X_dvd_iff]; simp) f k

/-- §D.2 [bStageP's and H₃rc's ambient F4 = GF(4)]: KL-1a count face HOLDS at the
p = 2 tower instances' field. -/
theorem kl1a_decided_F4 (f : Polynomial LeanUrat.MovesJ.F4) (k : ℕ) :
    (Polynomial.X : Polynomial LeanUrat.MovesJ.F4) ^ k ∣ f * (Polynomial.X + 1) ↔
      Polynomial.X ^ k ∣ f :=
  pow_dvd_mul_iff_of_coprime_cofactor Polynomial.irreducible_X
    (by rw [Polynomial.X_dvd_iff]; simp) f k

/-- §D.3 [the toys' ambient ℤ/2 = td2V4's q₀ = 2 alphabet field]: KL-1a count face
HOLDS. -/
theorem kl1a_decided_zmod2 (f : Polynomial (ZMod 2)) (k : ℕ) :
    (Polynomial.X : Polynomial (ZMod 2)) ^ k ∣ f * (Polynomial.X + 1) ↔
      Polynomial.X ^ k ∣ f :=
  pow_dvd_mul_iff_of_coprime_cofactor Polynomial.irreducible_X
    (by rw [Polynomial.X_dvd_iff]; simp) f k

end LeanUrat.Scaffold.HDischarge.H7.Probe

/-! ## §E — axiom census (acceptance bar: Lean core only; any `sorryAx` here is a
stop-the-line regression — in particular none of the P-2 tainted carriers may leak in). -/

#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.toyStage3_anchor
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.bStageP_anchor
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.h3rc_anchor
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.td2V4_anchor
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.toy_leaf_ne
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.toy_roster
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.toy_roster_card
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.toy_sibling_pair
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.toy_sibling_parent
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.kl1a_decided_zmod3
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.kl1a_decided_F4
#print axioms LeanUrat.Scaffold.HDischarge.H7.Probe.kl1a_decided_zmod2
