# AMENDMENT DRAFT — THE TOWER-INSTANTIATION FREEZE (A-C.9 / A-I.2, DRAFT v1)

**Author: the orchestrator (Fable 5), 2026-08-20, working the blueprint-finishing charge
directly.** STATUS: **DRAFT — nothing here is signed.** Adopting any part of §3–§5 is an
owner gate-(a) event (it fixes the meaning of the capstone's `ladder`/`deepTwist`
hypotheses). A Codex adversarial architecture pass is owed before the owner read (standing
plan-level-adversarial rule).

## §0 The charge, and what is owed to whom

Chapter I signed FOUR sockets/domains it could not type, all owed to "chapter C's
tower-instantiation freeze (the same GC-13/GC-14 pass that typed E.61/E.62)":

| debtor | creditor | what is owed |
|---|---|---|
| I.10a `CanonicalLadderConfig` | chapter C | a `Prop` body meaning "this `(C, B, G, Kt, L, N, v, ρ, q)` is the configuration chapter C's OM ladder produces for a degree-`n` input, at the canonical node-point residue read" |
| I.10b `CanonicalDeepTwistConfig` | chapters C+D | I.10a **∧** "the level-indexed arena family `(A, R, w)` is the tower's own" |
| I.05/I.06/I.07 bodies | chapters C+H | the quantification domain "the degree-`n` stage data, every stage of every genre" |
| E.61's socket consumer obligation | chapter C | "bind chapter C's canonical residue data" (OM-8's adjudication, append #73) |

The blocking fences, all of which this draft obeys:

* **the NON-SWALLOWING FENCE (A-I.1, binding):** the socket may NOT be typed at any condition
  that already implies its own carrier — it must constrain the CONFIGURATION, never the
  residue law. Operationally (§6 gate G-2): the socket's proof obligations must be
  *equations between data*, and inhabiting the socket at a witness must not produce
  `HVarthetaRes`/`VarthetaRes` as a by-product.
* **OM-8's pinning:** the ϑ-adjudication is YES exactly at DEF GENTOW5-1 instantiations with
  the CANONICAL node-point residue read, NO at arbitrary ambient `ρ`. So the socket must pin
  `ρ` to a canonical read constructed FROM the tower, not quantify over reads.
* **the transcription fence:** where the corpus prints no formula (the letter residue table
  at depth > 2), this draft cites the EFF source and marks the transcription as its own node
  rather than inventing content.

## §1 The gap, named precisely

Chapter C owns, LANDED: `KeyFrame` (C.01), `TowerDatum` (C.42), `DeepTower` (C.83, with
`ehat`, `Econst`, `towerNorm`, `towerSolve`), the development/height/residual battery
(`dev`, `dvHgt`, `dvSupp`, `dvResPoly`, `stageHeight`), the exact-height lift `stageLiftO`
(C.14a, pins at C.46), `slotIdx`/`twistExp` (C.15), `composedKey` (C.43). Witness values:
`s2Witness` (depth 3, C.97), `linTower` (depth 2, C53c — 2026-08-20).

Chapter C does NOT own, and the freeze must supply (these are the four genuinely new
objects; everything else is bridging):

* **(TIF-A)** a per-stage **`SlotCarrier` read** — the packaging of `(dvHgt, dvResPoly-digit)`
  at stage `i` as E.10's abstract carrier;
* **(TIF-B)** the **input block** — a degree-`n` monic input presented as E.11's `BlockData`
  over that carrier via its `Φ_i`-adic development;
* **(TIF-C)** the **letter lattice** — the group `G` with heights `v_j`, normalizer section
  `N`, use-heights `q`, and the **canonical node-point residue read** `ρ_j` (OM-8's object;
  D.07 says level 2's instance is "GENTOW2's letter group `⟨γ₁, γ₂⟩` … supplied by chapter
  C" — this is that supply, at general depth);
* **(TIF-D)** the **transport lemmas** — `SlotCarrier`/level-data transport along field
  equivalences, so the socket can equate the abstract `(C, B, …)` with the tower's own
  without demanding syntactic type equality.

## §2 Design decisions (each one flagged; the owner pass rules on all three)

* **D-TIF-1 (height normalization).** E-side heights are `WithTop ℤ`; C-side heights are
  `ℕ∞` in the `dv_i = ê_i·v`-cleared normalization. The freeze embeds `ℕ∞ ↪ WithTop ℤ`
  canonically and does NOT re-gauge: the T2 ladder's negative heights arise only after
  recentering moves, which are the LADDER's business (E-side), not the instantiation's.
  Consequence to verify at the gate (G-4): E.10's `hgt_ne_top`/`dig_ne_zero` hold for the
  embedded read on sub-`D_i` polynomials — this is B.22/C.26's nonvanishing at sub-key
  degrees, landed at levels ≤ 2.
* **D-TIF-2 (the letter group is the ABSTRACT lattice).** `G` is the free abelian lattice on
  the letter alphabet `{π, x, Φ_1, …, Φ_r}` — Lean-facing:
  `G := Multiplicative (Fin (r + 2) →₀ ℤ)` — with `v_j`, `N`, `ρ_j` defined by TABLES off
  the tower data. The rejected alternative (a subgroup of ambient units) is rejected
  *because of the non-swallowing fence*: ambient units carry relations, and relations are
  exactly what would let a socket silently discharge a residue-law conjunct. On the abstract
  lattice, `ρ_j` is data with no theorem content — the fence's operational form.
* **D-TIF-3 (the receiving fields).** `Kt := T.fld j` at the read level and `L := T.fld r`
  (the terminal level field), with `[Algebra Kt L]` the composite of C.83's `step`
  equivalences. The socket carries explicit `≃+*`s to the abstract `Kt, L` rather than
  demanding type equality (TIF-D transport).

## §3 The freeze nodes (chapter-C side; provisional IDs C.130a–C.130g, ENV-C1 unless noted)

Node granularity follows the formalization-trivial rule (≈30–60 min each). `T : DeepTower
F H₀ hpin r` throughout; `1 ≤ i ≤ r`.

* **C.130a [def] `DeepTower.stageDeg`** — `D_i := ∏_{j ≤ i} e_j f_j` plus positivity and the
  `i = 1` reconciliation `D_1 = e₁f₁ = F.key.natDegree`. Pure arithmetic off C.83's fields
  (`ehat`'s pattern). SOURCE: `EFF.GENTOW5.413`.
* **C.130b [def] `DeepTower.stageKey`** — the composed key chain `Φ_i`: `Φ_1 := F.key`,
  `Φ_{i+1} := composedKey (T.truncDatum i)` where `truncDatum i : TowerDatum … ` is the
  depth-`(i, i+1)` slice of `T` (the C.97 header already speaks of `DeepTower.trunc`;
  landing it IS this node's work). Clauses: monic, `natDegree = D_i` (C.47's
  `composedKey_monic`/`composedKey_natDegree_D₂` per stage). SOURCE: `EFF.HETOW.13` iterated;
  `EFF.GENTOW5.21`.
* **C.130c [def] `DeepTower.stageHgt`, `DeepTower.stageDig`** — the stage-`i` height and
  digit reads on `Polynomial O`:
  `stageHgt i A := dv_i-height of A` (the `dvHgt`-family at `Φ_i`, `ê_i`-cleared, valued in
  `ℕ∞`, embedded per D-TIF-1) and `stageDig i A ∈ T.fld i` (the leading residual coefficient
  of `A`'s stage read — B.21 `digAt`/B.29 `resPoly` iterated through `base`/`step`).
  ⚠ the ONLY node with real proof content beyond level 2: the ultrametric pair
  (`hgt_add_ge`, `hgt_add_eq`) and `dig_add` at general depth. At depth ≤ 2 these are landed
  (C.127's `stageHeight` battery; C.11); the general-depth statements are the `EFF.HE7`
  §height-calculus rows. If general depth stalls, the freeze still closes at `r ≤ 2` scope
  (covers every landed witness) with the depth index carried as a hypothesis — an honest
  narrowing, disclosed in I.10a's docstring at the freeze.
* **C.130d [def] `DeepTower.stageCarrier i : SlotCarrier O (T.fld i)`** — assembling
  C.130a–c: `D := stageDeg i`, `(eC, fC) := (∏ e_j, ∏ f_j)`, `hgt/dig := stageHgt/stageDig`,
  `Full k := ∃ A ≠ 0, deg A < D_i ∧ stageHgt i A = k`, `hlift` := C.46's `stageLiftO` pins
  (level 1 landed; the stage-`i` form rides C.130c's transport). Fields `hgt_zero`,
  `dig_zero`, `hgt_ne_top`, `dig_ne_zero` from the landed nonvanishing battery.
* **C.130e [def] `DeepTower.inputBlock`** — for `F₀` monic, `natDegree F₀ = μ·D_i`,
  key-free at `Φ_i`: `BlockData (stageCarrier i)` with `Φ := stageKey i`, `F := F₀`,
  `A j := dev (stageKey i) F₀ j`, `hdev` := the development identity (B.02-chain;
  C53b's `slotSum_grouped` pattern at depth 2), `hdegA` := `dev` degree bounds (landed),
  `hkeyfree` := the (KEY-FREE) hypothesis threaded, `hA0` := its polygon shadow.
* **C.130f [def] the letter lattice + tables** — `letterGroup r := Multiplicative
  (Fin (r + 2) →₀ ℤ)`; `letterHeight j : letterGroup r →* Multiplicative ℤ` by the height
  table `π ↦ ê_j`, `x ↦ (stage height of x)`, `Φ_k ↦ E_k`-values (the `ehat`/`Econst`
  arithmetic, LANDED in C.83); `normSection : NormSection (letterGroup r)` with
  `n k := the towerNorm word` (C.83's `towerNorm`, LANDED — `n_zero` is its slot-0
  normalization); `useHeight : ℕ → ℤ` from C.15's `twistExp` composed along the chain.
  SOURCE: `EFF.T1.01/.02`, `EFF.GENTOW2.42`.
* **C.130g [def] `canonicalRes` — THE OM-8 OBJECT** — for each `j`, the residue read
  `ρ_j : ker (letterHeight j) →* (T.fld r)ˣ` defined as the multiplicative extension of the
  LETTER RESIDUE TABLE: a height-0 word `π^a x^b ∏ Φ_k^{c_k}` is sent to the product of the
  letters' node-point residues at level `j`, each letter's residue being the landed stage
  data (`x ↦ the stage letter η_j` — C.19's `stageLetter`; `Φ_k ↦ its residual constant` —
  the `ψ`-data; `π ↦ 1` after the `ê_j`-clearing, by the exact-height normalization).
  ⚠ TRANSCRIPTION NODE: the table above is this draft's READING of `EFF.T1.03` +
  `EFF.GENTOW2.42` + OM-8's "letter-lattice factorization + residue multiplicativity +
  letters ∈ K_iˣ"; the freeze pass must transcribe the table AGAINST THOSE SOURCES, clause
  by clause, before signing. **This is the one node where a wrong guess poisons OM-8's
  adjudication, so it gets the D62w witness layer as its regression** (the general-depth
  `triangular_descent`/`dvd_stage` skeleton is already Lean-general, append #73).

## §4 The socket bodies (chapter-I side, typed at the freeze)

With §3 landed, I.10a's body (FROZEN binder block unchanged):

```
def CanonicalLadderConfig … (n : ℕ) : Prop :=
  ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (π : O) (_ : Irreducible π)
    (_ : IsAdicComplete (maximalIdeal O) O) (_ : Finite (ResidueField O))
    (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (r i : ℕ) (hi : 1 ≤ i ∧ i ≤ r)
    (T : DeepTower F H₀ hpin r) (F₀ : Polynomial O) (_ : F₀.Monic)
    (_ : F₀.natDegree = n) (hkf : KeyFree (T.stageKey i) F₀)
    (eK : K ≃+* T.fld i) (eKt : Kt ≃+* T.fld i) (eL : L ≃+* T.fld r)
    (eG : G ≃* letterGroup r),
    C = (T.stageCarrier i).transport eK ∧
    B = (T.inputBlock i F₀ …).transport eK ∧
    N = (T.normSection).transport eG ∧ (∀ j, v j = (T.letterHeight j).transport eG) ∧
    (∀ j, ρ j = (T.canonicalRes j).transport eG eL) ∧ (∀ j, q j = T.useHeight j)
```

— every conjunct an EQUATION between data (the non-swallowing fence's operational form);
no conjunct mentions `HVarthetaRes`, `VarthetaRes`, or any residue LAW. I.10b conjoins the
arena half the same way: `A j`, `R j`, `w j` equal the tower's own gauge-arena family (the
`(τ, ϑ, Θ)` letters at level `j` — D.07/D.08's instantiation off C.130f/g; its `True`
placeholder is replaced by three more transport equations).

I.05/I.06/I.07 then quantify over THE SAME data: e.g.
`WindowPinningAt n := ∀ (config arising at degree n per the ∃-block above), the
per-stage `StageInterface.hwin` clause at every live stage` — the domain is the freeze's,
the asserted clause is each node's own (H.89's at I.05, HE3.A's at I.06, C.93's census at
I.07), which keeps the three nodes independent of one another exactly as signed.

## §5 What the freeze does NOT do

* It does NOT discharge `ladder`/`deepTwist` — those still demand `LadderSupply` /
  `DeepTwistConjunct` AT the arising configurations (the open mathematics, HYP.41/42/57/63).
* It does NOT touch I.10's forbidden `jd0`/`genhnBox2` placeholders or the `w1` debt
  (A-I.1 rules them open; unchanged).
* It does NOT unfreeze I.10's field list (owner gate-(a); this draft only makes the two
  socket GUARDS typable).
* It does NOT claim the depth-general C.130c ultrametric — if that stalls, the freeze
  closes at `r ≤ 2` scope, disclosed.

## §6 The verification gate (all machine-checked before the freeze is signed)

* **G-1 (non-vacuity):** `CanonicalLadderConfig` is INHABITED at a real witness. Two are
  landed: `s2Witness` (depth 3, `ℤ₂`-class) and `linTower` (depth 2, any DVR; C53c). The
  gate instantiates at `s2Witness` with `F₀ := ` a concrete quartic from the §13 rows.
* **G-2 (non-swallowing probe):** from the socket's ∃-witness alone, `VarthetaRes … i` is
  NOT derivable without OM-8's mathematics: machine form — the G-1 inhabitation term is
  checked (by `#print axioms` and by construction) to consume only transport equations; no
  `hvarthetaRes_of_arena_agree` / `hvarthetaRes_of_tau_letters` appears in its proof term.
* **G-3 (refinement):** `CanonicalDeepTwistConfig → CanonicalLadderConfig` by construction
  (already the A-I.1 shape; re-checked at the typed bodies).
* **G-4 (the carrier laws):** `stageCarrier` satisfies E.10's field contracts at the landed
  witnesses (the depth-≤ 2 battery; the §13 numeric rows as regression).
* **G-5 (the equivalence-invariance sanity):** transported carriers satisfy the same laws —
  `SlotCarrier.transport` is lawful (TIF-D's lemma, one-time).

## §7 Owner items raised by this draft

1. gate-(a): adopting §4's socket bodies (they fix the capstone hypotheses' meaning);
2. D-TIF-1/2/3 (the three design decisions);
3. the §3 C.130g residue-table transcription (source read against `EFF.T1.03` /
   `EFF.GENTOW2.42`; OM-8's record is the adjudication authority);
4. whether the `r ≤ 2` fallback scope (§5) is acceptable for a first freeze.

## §8 DAG deltas (to be appended to `spec/DAG_BLUEPRINT_C.tsv` / `_I.tsv` on adoption)

`C.130a–g` new nodes as §3; edges: `I.10a → C.130{d,e,f,g}`, `I.10b → C.130{d,e,f,g} + D.07/D.08`,
`I.05/06/07 → C.130{d,f}`, `C.130d → C.130{a,b,c}`, `C.130e → C.130{b,d}`, `C.130g → C.130f + C.19 + C.83`,
`C.130b → C.43 + C.83`, `C.130c → C.11 + C.127 + B.21/B.29`. G-1's witness edge: `C.130-gate → C.97 + C53c`.
