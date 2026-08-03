/-
BP_IV §1.2 — Step 14, the (ADM)-FULL and level-1 census layers (`Census.lean`).
Units in this file: SKEL (module skeleton) · C3 (the `Decidable (ADMFull D)`
instance) · C2a (`r1Bound`) · C1 (`admFull_of_r_eq_zero` — statement verbatim,
PROVED over the REVISION-3 carrier; the pre-revision refutation artifacts are
retired to git history, see the C1 provenance block) · C4a (`Stratum1`, the
level-1 stratum carrier: Finset-of-boxes datum with per-coordinate windows
c_i = Δ(i)+1, + `count`, `padExp`) · C4b (`vertexChain_telescope` +
`vertexChain_telescope_units`, the M08 Lemma D vertex-chain telescope — the
carrier-free counting engine; see its provenance block for the honest scope)
· C4c (`censusW` + `canonicalStratum1` + `census_r0_law` — the M08 Theorem 2
r = 0 census law AT THE CONSTRUCTED carrier, junction-pinned and
type-aggregated; see the C4c provenance block) · C6 (`censusW_eval` +
`censusW_eval_nonneg`, p-freeness by type) · C7 (adjudicated at REVISION 3:
`Attained` + `attained_always` + the VACUOUS verbatim padding law — see the
C7 provenance block for the honesty record) · C2 (`admFull_r1_iff` —
statement verbatim, PROVED over the REVISION-3 carrier via the pointwise core
`attainDim_eq_d_iff_r1Bound_le`; pre-revision countermodels retired to git
history) · C5/C5′ statement layer (REVISION 3): the `StratumR` /
`JunctionStratum` counting carriers + the named row `CensusValueRows` with
the BP_III-owned (GR-B)/(FRESH) rows as OPAQUE PREDICATE PARAMETERS
(K3DeltaRow precedent); the C5 digit-cost proof kernels
(`digitCost_of_surjective_read` / `digitCost_of_surjective_linear_read`) are
landed and proved; the wave-4 constructor (the anchored march) is re-chartered
per REVISION 3 · **C5-ctor (wave 4, LANDED — end of file): the
`AnchoredMarch`/`AnchoredMarchProof` carriers (the anchored-march digit-read
ladder, O9 rev-5 §5.1/§6.3), `censusValueRows_of_anchoredMarch`, the
`censusW` re-key to the census field degree d = ∏ᵢ f_i, and the honest
vertex-granular padding layer superseding C7's vacuous verbatim law (with
the compiled carrier-degeneracy record).**
Import graph (BP_IV §1.0): `CensusCore → Hyps` and `{CensusCore, Hyps} →
Census`, never a cycle — this module imports both and is imported by the
repaired `SeriesTie.lean`/`DensityTie.lean` (REVISION 3).
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.CensusCore
import LeanUrat.Scaffold.ValueSide.Hyps

/-!
# The order-r census layers [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.2, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement layer) and §0
  (module map row `Census.lean` | step 14 | "imports `CensusCore.lean` and
  `Hyps.lean`; proves the (ADM)-FULL and level-1 census layers").
* Math source of record: `O9_phaseB_verifybrief_rev5.md` + M08
  (`M08-cl6-general_fable.md` §2), per BP_IV §0 step-14 row.
* Imports: `Mathlib` + the two value-side roots (`CensusCore`, `Hyps`).
-/

namespace LeanUrat.Scaffold

/-!
**PROVENANCE (unit C3; BP_IV §1.2, unit table §2 row C3).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement transcribed VERBATIM;
  unit-table row C3 "Finset.decidableBAll over onLineSlots").
* Math source of record: ROOT §3.1, the (ADM) row's "per-datum DECIDABLE"
  clause ("finite lattice check").
* Deps: C0 (the `CensusData` carriers, `CensusCore.lean`) and H1 (`ADMFull`,
  `CensusCore.lean`).
* Mechanism: `ADMFull D` is a one-field structure over the bounded-∀
  proposition `∀ β ∈ D.onLineSlots, D.attainDim β = D.d`; `decidable_of_iff`
  transports the `Finset.decidableBAll` instance on that proposition across
  the (constructor ↔ field) equivalence.  `noncomputable` because `wt` (hence
  `onLineSlots`/`attainDim`) is declared `noncomputable` upstream per the
  blueprint's verbatim signatures — the decidability is at type level, exactly
  as the C3 docstring states; no `Classical.dec` is used.
-/

/-- C3: (ADM)-FULL is per-datum decidable — the ROOT §3.1 row's "finite lattice
    check" clause, machine-checked at type level. -/
noncomputable instance : ∀ D : CensusData, Decidable (ADMFull D) := fun D =>
  decidable_of_iff (∀ β ∈ D.onLineSlots, D.attainDim β = D.d)
    ⟨fun h => ⟨h⟩, fun h => h.full_attained⟩

/-!
**PROVENANCE (unit C2a; BP_IV §1.2 C2 comment + §2 C-table row C2a).**

* Blueprint: `lean/blueprints/BP_IV.md` — the C-table row C2a
  ("`r1Bound` def (the displayed r = 1 RHS h₁((h₁⁻¹β mod e₁)+(f₁−1)e₁))",
  "needs h₁ invertible mod e₁") and the §1.2 C2 display, whose use site
  `r1Bound D β ≤ β` (with the comment "`r1Bound` uses `D.h_coprime`; no
  undefined auxiliary proposition occurs") fixes the verbatim application form
  `r1Bound D β : ℕ` at namespace level (NOT `CensusData` dot-notation — the C2
  display sits outside `namespace CensusData`).  The undefined `coprimeHyp`
  binder of the table row is removed per REV-2 finding 16: invertibility is
  supplied by the `CensusData.h_coprime` field.
* Math source of record: O9 r4 display (`O9_phaseB_verifybrief_rev5.md`, the
  r = 1 FULL-attainment criterion): β is FULLY attained iff
  β ≥ h₁·((h₁⁻¹β mod e₁) + (f₁ − 1)·e₁).
* Deps: C0 (the `CensusData` carrier, `CensusCore.lean`).
* Body is DERIVED (the blueprint displays no body) and hereby flagged for
  division-lead/Codex ratification per the trust boundary:
  - stage index 1 is `(1 : Fin (D.r + 1))` — the genuine stage 1 whenever
    D.r ≥ 1 (the only regime C2 consumes; at D.r = 0 the literal wraps to
    stage 0, and the def is total but unconsumed);
  - `(h₁⁻¹β mod e₁)` is realized as `ZMod.val` of
    `(ZMod.unitOfCoprime (D.h 1) (D.h_coprime 1))⁻¹ * β` in `ZMod (D.e 1)`:
    the canonical representative in `[0, e₁)` of h₁⁻¹·β mod e₁ (`ZMod.val` is
    reduction mod e₁ since e₁ ≥ 1 by `D.he`), with the unit inverse supplied
    EXACTLY by `D.h_coprime` — the C2-comment discharge of the removed
    `coprimeHyp`;
  - `(f₁ − 1)` is ℕ-truncated subtraction, exact since f₁ ≥ 1 by `D.hf`.
-/

/-- C2a: the r = 1 attainment bound — the displayed O9 r4 RHS
    `h₁·((h₁⁻¹β mod e₁) + (f₁ − 1)·e₁)`, with h₁⁻¹ the inverse of h₁ mod e₁
    furnished by `D.h_coprime` (via `ZMod.unitOfCoprime`).  Unit C2 states:
    FULL attainment at β ⟺ `r1Bound D β ≤ β` (for D.r = 1, over
    `D.onLineSlots`). -/
def r1Bound (D : CensusData) (β : ℕ) : ℕ :=
  D.h 1 *
    ((((ZMod.unitOfCoprime (D.h 1) (D.h_coprime 1))⁻¹ : (ZMod (D.e 1))ˣ) *
        (β : ZMod (D.e 1)) : ZMod (D.e 1)).val
      + (D.f 1 - 1) * D.e 1)

/-!
**PROVENANCE (unit C1; BP_IV §1.2, unit table §2 row C1; PROVED at
REVISION 3).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 ("C1: r = 0 automaticity — the
  ONLY automatic case"; statement transcribed VERBATIM below, per the
  statement fence — the statement is UNCHANGED by the revision).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` §1 + §2
  (automaticity, re-scoped to the FULL predicate): "r = 0: all ledger weights
  are 0 and **e = 1**, so dim G_β = #{wt ≤ β} = **m = f₀ = d**".
* **REVISION-3 adjudication record.**  Over the PRE-revision C0 carrier
  (stage 0 a full `Fin (e 0) × Fin (f 0)` pair in `J`, an `e 0` factor in
  `period`) this statement was REFUTED — compiled negation witness
  `C1Refutation.not_admFull_cmC1` (datum r = 0, e₀ = 2, h₀ = 1, f₀ = 1:
  `attainDim 0 = e₀·f₀ = 2 ≠ 1 = f₀ = d`), on file in git history (33656d2).
  The mop-up architect ruled the CARRIER wrong and the LAW right (the O9
  ledger has stage 0 at multiplicity f₀ and period e₁⋯e_r): `CensusCore.lean`
  now derives `J`/`period`/`wt` through `ledgerE` (= 1 at stage 0), and the
  statement is PROVED below — the blueprint's own sketch (all weights 0,
  `onLineSlots = {0}`, `Gset 0 = univ`, `|J| = ∏ ledgerEᵢfᵢ = ∏ fᵢ = d`).
  The retired countermodel datum satisfies the theorem on the repaired
  carrier (attainDim 0 = f₀ = 1 = d).
* Deps: C0 (`CensusCore.lean`, REVISION-3 form), H1 (`ADMFull`).
-/

/-- C1: r = 0 automaticity — the ONLY automatic case (ROOT (ADM) row, exact). -/
theorem admFull_of_r_eq_zero {D : CensusData} (hr : D.r = 0) : ADMFull D := by
  have hidx : ∀ i : Fin (D.r + 1), i.1 = 0 := by
    intro i
    have := i.2
    omega
  have hwphi : ∀ i, D.wphi i = 0 := by
    intro i
    unfold CensusData.wphi
    simp [hidx i]
  have hwt : ∀ j : D.J, D.wt j = 0 := by
    intro j
    unfold CensusData.wt
    exact Finset.sum_eq_zero fun i _ => by rw [hwphi i, mul_zero]
  constructor
  intro β hβ
  have hβ0 : β = 0 := by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hβ
    rw [← hj, hwt]
  subst hβ0
  have hgset : D.Gset 0 = Finset.univ := by
    unfold CensusData.Gset
    rw [Finset.filter_true_of_mem]
    intro j _
    exact ⟨by rw [hwt], (hwt j).le⟩
  have hcardJ : Fintype.card D.J = ∏ i, D.ledgerE i * D.f i := by
    have h1 : Fintype.card D.J
        = Fintype.card
            ((i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [h1]
    simp
  have hle : ∀ i : Fin (D.r + 1), D.ledgerE i = 1 := by
    intro i
    unfold CensusData.ledgerE
    simp [hidx i]
  unfold CensusData.attainDim CensusData.d
  rw [hgset, Finset.card_univ, hcardJ]
  exact Finset.prod_congr rfl fun i _ => by rw [hle i, one_mul]

/-!
**PROVENANCE (unit C4a; BP_IV §1.2 C4 annotation + §2 C-table row C4a).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2, the C4 display annotation
  ("stated for the level-1 stratum carrier `Stratum1` (a Finset-of-boxes
  datum, unit C4a)") and the §2 C-table row C4a ("`Stratum1` carrier
  (level-1 stratum as Finset of boxes with per-coordinate windows
  c_i = Δ(i)+1) | definition | C0 | MECH | M08 §2.1").
* Math source of record: M08 (`M08-cl6-general_fable.md`) §2.1 (the level-1
  stratum datum D = (Δ, (λ_S)_S) for the x^e block: lower-convex Δ from
  (0, y₀), y₀ ≥ 1, to (e, 0), negative increasing slopes; lattice slots =
  integer points of Δ) and §2.2 (the per-coordinate factorization
  C_{D,N} = q^{E(D,N)} · Z_D(q), E(D,N) = Σ_{i<e} (N − c_i)).
* VERBATIM constraints honored exactly (the blueprint displays no Lean body
  for C4a; these two fragments are all it fixes):
  `Stratum1 : CensusData → Type` — from the §1.2 signature
  `noncomputable def canonicalStratum1 (D : CensusData) : Stratum1 D` —
  and a `count : ℕ → ℕ` interface in `q` ONLY (no level `N`) — from the
  §1.2 use site `(canonicalStratum1 D).count q = (censusW D).eval q` with
  `censusW D : Polynomial ℕ`.
* Body is DERIVED from M08 §2.1/§2.2 and hereby FLAGGED for
  division-lead/Codex ratification per the trust boundary:
  - a **box** is a per-coordinate digit pin `Fin e → Option (Fin q)`
    (`some z` = the single digit at the window floor `c_i − 1` is pinned to
    `z` — a lattice slot of Δ; `none` = the coordinate is free above its
    window — a non-lattice slot).  The digit alphabet is the BARE `Fin q`:
    at this carrier layer only counts matter; the F_q field structure
    (residual polynomials, types λ_S) enters at the canonical instance
    (unit C4c) and the telescope (unit C4b).
  - the window normalization c_i = Δ(i)+1 at lattice slots (⌈Δ(i)⌉
    otherwise) is exactly what makes every box contribute q^(N − c_i)
    points in EVERY coordinate (M08 Lemma A: pinned digit at depth Δ(i)
    costs one q; free coordinate has floor ⌈Δ(i)⌉), so box size is the
    box-independent q^(E(D,N)) — recorded here as `padExp`.
  - `count q` := the number of boxes = M08 §2.2's digit census Z_D(q); the
    q^E per-box padding is NOT part of `count`, matching the N-free verbatim
    use site above (the level-N point count is `count q * q^(padExp N)`,
    assembled by C4b/C4c).
  - the parameter `D` is a keying seam, not a constraint: BP_IV §5 FIXED
    row 11 ("`census_r0_law` applies to the constructed `canonicalStratum1
    D`, not every arbitrary carrier"), so no field ties the polygon data to
    `D`; the tie is made by the C4c construction.
  - carrier laws kept minimal-faithful: `1 ≤ e` (nonempty block),
    `1 ≤ window i` (the x^e-block clause v(a_i) ≥ 1 of M08 §2.1), and
    `boxes_lattice` (every box pins exactly the lattice slots — Δ fixes the
    pinned coordinate set uniformly across the stratum).
* Deps: C0 (`CensusData`, `CensusCore.lean`).  Consumers: C4b (vertex-chain
  telescope), C4c (`canonicalStratum1`, `censusW`, `census_r0_law`).
-/

/-- C4a (box shape): one level-1 box over the digit alphabet `Fin q` on `e`
    coordinates — coordinate `i` either pins the digit at its window floor
    (`some z`, a lattice slot of Δ) or is free above its window (`none`).
    Named `Box1` because the corpus `Box p n N` is used AS IS and must not
    be shadowed (BP_IV §0). -/
abbrev Box1 (e q : ℕ) : Type := Fin e → Option (Fin q)

/-- C4a: the level-1 stratum carrier — M08 §2.1's stratum datum reduced to
    its counting skeleton: block degree `e`, per-coordinate windows
    `window i` (= Δ(i)+1 at lattice slots, ⌈Δ(i)⌉ otherwise — M08
    Theorem 2's c_i), the lattice-slot set, and the Finset of boxes at each
    digit-alphabet size `q` (M08 §2.2's admissible digit tuples (z_i)).
    The parameter `D` keys the carrier to its census datum; the tie is made
    by the constructed `canonicalStratum1 D` (unit C4c; BP_IV FIXED
    row 11). -/
structure Stratum1 (D : CensusData) where
  /-- The block degree: the horizontal length of Δ (the census ranges over
      the `e` coefficients a_0, …, a_{e−1} of the x^e block). -/
  e : ℕ
  he : 1 ≤ e
  /-- The per-coordinate window c_i: Δ(i)+1 at lattice slots, ⌈Δ(i)⌉ at
      non-lattice slots (M08 Theorem 2). -/
  window : Fin e → ℕ
  /-- The x^e-block clause of M08 §2.1: v(a_i) ≥ 1, i.e. every window is at
      least 1. -/
  hwindow : ∀ i, 1 ≤ window i
  /-- The lattice slots of Δ (the coordinates carrying a pinned digit;
      determined by Δ, hence shared by every box of the stratum). -/
  latticeSlots : Finset (Fin e)
  /-- The Finset of boxes at digit-alphabet size `q` — the level-1 stratum
      IS this Finset-of-boxes datum (unit C4a's title clause). -/
  boxes : (q : ℕ) → Finset (Box1 e q)
  /-- Every box pins exactly the lattice slots. -/
  boxes_lattice : ∀ q, ∀ b ∈ boxes q, ∀ i, (b i).isSome ↔ i ∈ latticeSlots

namespace Stratum1

variable {D : CensusData}

/-- C4a: the box census — the number of boxes at digit-alphabet size `q`
    (M08 §2.2's Z_D(q)).  The level-N point count of the stratum is
    `count q * q ^ padExp N` (q^E per-box padding; assembled by units
    C4b/C4c), which is why `count` is N-free, matching the verbatim
    `census_r0_law` use site. -/
def count (S : Stratum1 D) (q : ℕ) : ℕ := (S.boxes q).card

@[simp] theorem count_def (S : Stratum1 D) (q : ℕ) :
    S.count q = (S.boxes q).card := rfl

/-- C4a: the per-level padding exponent E(D,N) = Σ_{i<e} (N − c_i) of M08
    Theorem 2 (ℕ-truncated subtraction; exact in the M08 level regime
    N > max_i Δ(i), where N ≥ c_i for every i). -/
def padExp (S : Stratum1 D) (N : ℕ) : ℕ := ∑ i, (N - S.window i)

@[simp] theorem padExp_def (S : Stratum1 D) (N : ℕ) :
    S.padExp N = ∑ i, (N - S.window i) := rfl

end Stratum1

/-!
**PROVENANCE (unit C4b; BP_IV §2 C-table row C4b).**

* Blueprint: `lean/blueprints/BP_IV.md` §2, C-table row C4b — "vertex-chain
  telescope (M08 Lemma D): the chain-aggregated count factors ∏ M_{λ_S}(q) |
  telescoping product over the chain; each factor a geometric window count |
  deps C4a | MED | M08 §2.6".  **The §1.2 statement layer displays NO Lean
  signature for C4b** (its code block passes from C2 directly to the C4c-level
  declarations `censusW`/`canonicalStratum1`/`census_r0_law`), so — per the
  C0d/C2a/C4a precedent — the statement below is DERIVED from the math source
  of record and hereby FLAGGED for division-lead/Codex ratification (trust
  boundary: statements are where errors hide).
* Math source of record: `lean/notes/openmath/M08-cl6-general_fable.md` §2.6,
  Lemma D (vertex-chain telescope).  Vertices v₀ … v_k of Δ, sides S = 1..k
  (side S: left vertex v_{S−1}, right vertex v_S), z_{v_k} = 1 pinned by
  monicity; the displayed telescope identity is

      Σ_{z_{v₀},…,z_{v_{k−1}} ∈ F_q^×} ∏_{S=1}^{k} ν_{λ_S}(z_{v_{S−1}} / z_{v_S})
        = ∏_{S=1}^{k} Σ_{t ∈ F_q^×} ν_{λ_S}(t).

* Lean transcription (the derivation being flagged): the k free vertex values
  are `z : Fin k → G`; the pinned right end z_{v_k} = 1 is supplied by
  `Fin.snoc z 1 : Fin (k+1) → G`; side `S : Fin k` reads its left vertex at
  `S.castSucc` and its right vertex at `S.succ`.  The per-side ratio class
  functions ν_{λ_S} enter as ARBITRARY `ν S : G → R`: M08 Lemma C supplies the
  intended instances ν_λ : F_q^× → ℕ with Σ_t ν_λ(t) = M_λ(q) — so each RHS
  factor is exactly the "geometric window count" M_{λ_S}(q) of the C-table
  row, and that identification is the C4c seam.  Stated over any finite group
  `G` with values in any commutative semiring `R` (the counting instance is
  R := ℕ, G := F_q^×): M08's proof uses only the group structure of F_q^×,
  and `vertexChain_telescope_units` pins the literal F_q^× form.
* SCOPE (honest): Lemma D's FIRST equality — Z_D(q) = the chain sum, i.e. the
  aggregation of the box census over sides via Lemma C — is a property of the
  CANONICAL boxes (an abstract `Stratum1.boxes` is an unconstrained Finset),
  so it belongs to C4c's `canonicalStratum1`/`census_r0_law` assembly, per
  C4a's own provenance ("the F_q field structure ... enters at the canonical
  instance (unit C4c) and the telescope (unit C4b)").  This unit lands the
  telescope engine: the second and third displayed equalities of Lemma D.
* Deps: C4a (`Stratum1`, landed above) for the seam design; the engine itself
  is carrier-free by construction.
* Proof (M08 §2.6, mechanism verbatim): the substitution
  t_S := z_{v_{S−1}}/z_{v_S} is a bijection (F_q^×)^k → (F_q^×)^k because
  z_{v_k} = 1 is pinned ("invert backwards from z_{v_k}") — here: injectivity
  by downward induction along the chain (`Fin.reverseInduction`), upgraded by
  `Finite.injective_iff_bijective`; then the summand splits as ∏_S ν_S(t_S)
  and `Finset.prod_univ_sum` factorizes the aggregated sum.
-/

/-- C4b (M08 §2.6 Lemma D, the vertex-chain telescope — the carrier-free
    counting engine): for a chain of `k` sides over a finite group `G` — free
    vertex values `z : Fin k → G`, right end pinned to `1` via `Fin.snoc z 1`,
    side `S` reading the ratio of its left (`S.castSucc`) and right (`S.succ`)
    vertex values — the chain-aggregated sum of per-side ratio class functions
    telescopes into the product of their plain sums:

        Σ_z ∏_S ν S (z_{v_{S−1}} / z_{v_S})  =  ∏_S Σ_t ν S t.

    With ν S := ν_{λ_S} of M08 Lemma C (so Σ_t ν_{λ_S}(t) = M_{λ_S}(q), each
    factor a geometric window count) this is the chain-aggregated census
    factorization Z_D(q) = ∏_S M_{λ_S}(q); unit C4c instantiates it through
    the canonical `Stratum1` boxes.  The telescope is load-bearing (M08 §2.5):
    the individual end-pinned factors are NOT polynomial in q — only the
    chain-aggregated sum factorizes. -/
theorem vertexChain_telescope {G R : Type*} [Group G] [Fintype G]
    [CommSemiring R] {k : ℕ} (ν : Fin k → G → R) :
    (∑ z : Fin k → G, ∏ S : Fin k,
        ν S ((Fin.snoc z 1 : Fin (k + 1) → G) S.castSucc /
          (Fin.snoc z 1 : Fin (k + 1) → G) S.succ))
      = ∏ S : Fin k, ∑ t : G, ν S t := by
  -- M08's substitution (z_{v₀},…,z_{v_{k−1}}) ↦ (t_1,…,t_k), t_S = z_{v_{S−1}}/z_{v_S}
  have hinj : Function.Injective
      (fun (z : Fin k → G) (S : Fin k) =>
        (Fin.snoc z 1 : Fin (k + 1) → G) S.castSucc /
          (Fin.snoc z 1 : Fin (k + 1) → G) S.succ) := by
    intro z z' hzz
    -- "invert backwards from z_{v_k}": downward induction along the chain
    have hext : ∀ i : Fin (k + 1),
        (Fin.snoc z 1 : Fin (k + 1) → G) i = (Fin.snoc z' 1 : Fin (k + 1) → G) i := by
      intro i
      induction i using Fin.reverseInduction with
      | last => simp
      | cast i ih =>
        have hfac : (Fin.snoc z 1 : Fin (k + 1) → G) i.castSucc /
              (Fin.snoc z 1 : Fin (k + 1) → G) i.succ
            = (Fin.snoc z' 1 : Fin (k + 1) → G) i.castSucc /
              (Fin.snoc z' 1 : Fin (k + 1) → G) i.succ :=
          congrFun hzz i
        rw [ih] at hfac
        exact div_left_injective hfac
    funext i
    simpa using hext i.castSucc
  have hbij : Function.Bijective
      (fun (z : Fin k → G) (S : Fin k) =>
        (Fin.snoc z 1 : Fin (k + 1) → G) S.castSucc /
          (Fin.snoc z 1 : Fin (k + 1) → G) S.succ) :=
    Finite.injective_iff_bijective.mp hinj
  calc
    (∑ z : Fin k → G, ∏ S : Fin k,
        ν S ((Fin.snoc z 1 : Fin (k + 1) → G) S.castSucc /
          (Fin.snoc z 1 : Fin (k + 1) → G) S.succ))
        = ∑ w : Fin k → G, ∏ S : Fin k, ν S (w S) :=
      hbij.sum_comp fun w => ∏ S : Fin k, ν S (w S)
    _ = ∏ S : Fin k, ∑ t : G, ν S t := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- C4b at the source group (M08 §2.6 display, literal): the F_q^×
    instantiation of `vertexChain_telescope` for a finite field `F`. -/
theorem vertexChain_telescope_units {F R : Type*} [Field F] [Fintype F]
    [DecidableEq F] [CommSemiring R] {k : ℕ} (ν : Fin k → Fˣ → R) :
    (∑ z : Fin k → Fˣ, ∏ S : Fin k,
        ν S ((Fin.snoc z 1 : Fin (k + 1) → Fˣ) S.castSucc /
          (Fin.snoc z 1 : Fin (k + 1) → Fˣ) S.succ))
      = ∏ S : Fin k, ∑ t : Fˣ, ν S t :=
  vertexChain_telescope ν

/-!
**PROVENANCE (unit C4c; BP_IV §1.2 + §2 C-table row C4c; REV-2 finding 11).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 — the three signatures below
  (`censusW`, `canonicalStratum1`, `census_r0_law`) are transcribed VERBATIM;
  the law applies to the CONSTRUCTED `canonicalStratum1 D` (REV-2 finding 11).
* Math source of record: M08 (`M08-cl6-general_fable.md`) §2.6 Theorem 2 (the
  r = 0 / level-1 census law; PROVED on paper, 46-strata machine check), read
  through the landed C4a carrier: `Stratum1.count` is the N-FREE digit census
  Z_D(q) (the q^{E(D,N)} padding lives in `Stratum1.padExp`, per C4a's
  provenance), so `censusW` is the Z_D-side polynomial — M08 §2.2's
  ∏_S M_{λ_S}-slot of Theorem 2, in the junction-pinned type-aggregated
  reading forced below.
* Deps: C4a (`Stratum1`, above), C4b (`vertexChain_telescope`, above).  At
  r = 0 the canonical polygon has ONE side, so the C4b chain telescope
  degenerates to a one-factor product; the assembly consumed here is the
  per-coordinate factorization (`Fintype.card_piFinset` — M08 Lemma A's
  per-slot independence).  The C4b engine stands ready for the r ≥ 1 laws.
* Bodies are DERIVED (the blueprint displays none) and hereby FLAGGED for
  division-lead/Codex ratification per the trust boundary.  THE FORCING
  ARGUMENT pinning the canonical construction:
  - `censusW : Polynomial ℕ` is blueprint-verbatim (C6's p-freeness BY TYPE).
    An ℕ-coefficient polynomial cannot take the value (q−1)·q^{f₀−1} at every
    prime power (the unique interpolating polynomial X^{f₀} − X^{f₀−1} has a
    negative coefficient), so the free-unit-vertex digit census — M08 §2.2's
    Z_D aggregated over residual types — admits NO `censusW`.  The canonical
    stratum is therefore JUNCTION-PINNED: the left-vertex digit is pinned to
    the unit 1 (encoded `1 % q`: the field unit at every q = p^N ≥ 2, the
    unique digit at q = 1) — O9 rev5 §6.4's ε = 0 branch ("the right-end read
    is the constant 1 — the window-internal instance of the junction pin"),
    giving the pure-power digit census q^{f₀−1}.
  - type-AGGREGATION (the `CensusData` carrier holds NO λ-datum) is what
    keeps a pinned-end count polynomial: M08 §2.5's warning (λ-refined
    pinned-end counts are genuinely non-polynomial in q) applies per type;
    the aggregate Σ_λ ν_λ(1) = q^{f₀−1} is exact.
  - the canonical polygon reads stage-0 data (e₀, h₀, f₀): the single side
    (0, h₀f₀) → (e₀f₀, 0) of slope −h₀/e₀ (gcd(h₀,e₀) = 1 = `D.h_coprime 0`),
    block degree `m1` = e₀·f₀, lattice slots e₀ ∣ i, windows
    `c1 i` = ⌊h₀(m1−i)/e₀⌋ + 1 — ONE ℕ-division formula giving both M08
    clauses: Δ(i)+1 at lattice slots (exact division) and ⌈Δ(i)⌉ = ⌊Δ(i)⌋+1
    off the lattice (non-exact division).
  - canonical boxes: pinned unit digit at the vertex i = 0, free digit
    (`isSome`) at the f₀ − 1 interior lattice slots (e₀ ∣ i, i ≠ 0), `none`
    off the lattice — M08 §2.2's admissible digit tuples, junction-pinned and
    type-aggregated.
* Consumption seams RECORDED (division-lead items, not discharged here):
  (a) C7's `Attained` predicate is undefined corpus-wide; `censusW` below is
  the UNGUARDED canonical monomial — C7's owner must key `Attained` to match
  or escalate a `censusW` re-key.  (b) CEN-W's r ≥ 1 value (E′/s(β_k)
  thresholds) is NOT expressible from `CensusData` alone; at r ≥ 1 `censusW`
  reads the same stage-0 shadow and MUST be re-keyed by C5's wave-4
  constructor (recorded to prevent silent consumption) — **EXECUTED at unit
  C5-ctor: `censusW` now reads the census field degree d = ∏ᵢ f_i (see its
  re-key docstring); the E′/s(β_k) bookkeeping lives in the march carrier's
  `Balanced` clause (end of this file)**.  (c) `hr` and the
  prime-power binders are not consumed by the proof: over the landed carrier
  the identity is polynomial in q, needing only q ≥ 1 (supplied by `hq`); the
  DVR content of M08 Thm 2 (Lemma A's residue counts over O/π^N) lives above
  the scaffold carrier.  Statements kept verbatim.
* Machine gate (`C4cGate` below): the worked shape (e₀,h₀,f₀) = (2,1,2) —
  `count 3 = 3 = q^{f₀−1}` decide-checked, plus the law instance at q = 3¹.
-/

namespace CensusData

/-- C4c (canonical polygon, block degree): `m1` = e₀·f₀ — the horizontal
    length of the canonical one-sided r = 0 polygon (M08 §2.1, stage-0
    data). -/
def m1 (D : CensusData) : ℕ := D.e 0 * D.f 0

/-- C4c (canonical windows): M08 Theorem 2's c_i in one ℕ-division formula,
    `c1 i` = ⌊h₀(m1−i)/e₀⌋ + 1: this is Δ(i)+1 at lattice slots (where the
    division is exact — gcd(h₀,e₀) = 1 makes e₀ ∣ h₀(m1−i) ⟺ e₀ ∣ i) and
    ⌈Δ(i)⌉ = ⌊Δ(i)⌋+1 off the lattice (division non-exact). -/
def c1 (D : CensusData) (i : ℕ) : ℕ := D.h 0 * (D.m1 - i) / D.e 0 + 1

end CensusData

/-- C4c (canonical slot choices): coordinate `i`'s admissible digit entries at
    alphabet size `q` — the vertex `i = 0` pins the unit digit (value `1 % q`),
    interior lattice slots (`e₀ ∣ i`, `i ≠ 0`) carry a free digit, off-lattice
    coordinates carry `none` (M08 §2.2 digit tuples, junction-pinned and
    type-aggregated per the C4c provenance). -/
def canonicalSlotChoice (e₀ q i : ℕ) : Finset (Option (Fin q)) :=
  if i = 0 then Finset.univ.filter (fun o => o.map Fin.val = some (1 % q))
  else if e₀ ∣ i then Finset.univ.filter (fun o => o.isSome)
  else {none}

/-- C4c (slot-choice card law, M08 Lemma A shadow): at every q ≥ 1 the slot
    choices count 1 (pinned vertex), q (interior free digit) or 1 (`none`),
    uniformly `q ^ [e₀ ∣ i ∧ i ≠ 0]`. -/
lemma canonicalSlotChoice_card {q : ℕ} (hq : 0 < q) (e₀ i : ℕ) :
    (canonicalSlotChoice e₀ q i).card
      = q ^ (if e₀ ∣ i ∧ i ≠ 0 then 1 else 0) := by
  unfold canonicalSlotChoice
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, if_neg (by simp), pow_zero, Finset.card_eq_one]
    refine ⟨some ⟨1 % q, Nat.mod_lt 1 hq⟩, ?_⟩
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    cases o with
    | none => simp
    | some z => simp [Fin.ext_iff]
  · rw [if_neg h0]
    by_cases hdvd : e₀ ∣ i
    · rw [if_pos hdvd, if_pos ⟨hdvd, h0⟩, pow_one]
      have himg : (Finset.univ.filter fun o : Option (Fin q) => o.isSome)
          = Finset.univ.image some := by
        ext o
        cases o <;> simp
      rw [himg, Finset.card_image_of_injective _ (Option.some_injective _),
        Finset.card_univ, Fintype.card_fin]
    · rw [if_neg hdvd, if_neg (fun h => hdvd h.1), pow_zero,
        Finset.card_singleton]

/-- C5-ctor re-key support: at r = 0 the census field degree collapses to the
    stage-0 residue degree, d = ∏_{i : Fin 1} f i = f₀ — the bridge that keeps
    `census_r0_law` (statement verbatim) proved across the REVISION-3 R3.5
    `censusW` re-key. -/
theorem CensusData.d_eq_f0_of_r_eq_zero {D : CensusData} (hr : D.r = 0) :
    D.d = D.f 0 := by
  have hidx : ∀ i : Fin (D.r + 1), i = 0 := by
    intro i
    have h2 := i.2
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have h1 : D.d = ∏ _i : Fin (D.r + 1), D.f 0 :=
    Finset.prod_congr rfl fun i _ => by rw [hidx i]
  rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- `D.f 0`'s index type depends on `D.r`, so generalize it before using `hr`
  generalize D.f 0 = c
  rw [hr, zero_add, pow_one]

/-- C6+C7: the census value CEN-W as data: a ℕ-coefficient polynomial in q per
    stratum (p-freeness is BY TYPE), with the padding law census = 0 at
    unattained vertices.

    **RE-KEYED at unit C5-ctor (BP_IV REVISION 3 R3.5, executing the C4c
    provenance seam note): the exponent reads the CENSUS FIELD DEGREE
    d = ∏ᵢ f_i (O-9's DELTA-3 index fix), not the stage-0 shadow f₀.**
    Design (DERIVED, flagged for division-lead/Codex ratification): the
    canonical junction-pinned window census — the fully attained graded piece
    carries d F_q-digit lines (LED(iii) at FULL attainment: dim_{F_q} G = d),
    the anchored march pins ONE read (the junction pin, O9 rev5 (FRESH)(c) /
    the monic-top ε = 0 branch of CEN-W), the d − 1 free reads cost q each
    (proof kernel (b) below at target F_q) — census q^{d−1}.  At r = 0,
    d = f₀ (`CensusData.d_eq_f0_of_r_eq_zero`) and this IS the previous
    stage-0 form q^{f₀−1} = M08 Theorem 2's digit census: `census_r0_law`
    and both `C4cGate` gates are UNCHANGED and still proved. -/
noncomputable def censusW (D : CensusData) : Polynomial ℕ                -- unit C4c
  := Polynomial.X ^ (D.d - 1)

/-- C4 (M08 Theorem 2, the r = 0 / level-1 census law): census = q^E · ∏ M_{λ_S}(q)
    with c_i = Δ(i) + 1 at lattice slots — stated for the level-1 stratum carrier
    `Stratum1` (a Finset-of-boxes datum, unit C4a), as an exact ℕ-count identity
    at every prime power: count = (censusW D).eval q. -/
noncomputable def canonicalStratum1 (D : CensusData) : Stratum1 D where
  e := D.m1
  he := by
    unfold CensusData.m1
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp (D.he 0))
        (Nat.one_le_iff_ne_zero.mp (D.hf 0)))
  window := fun i => D.c1 i.1
  hwindow := fun i => Nat.le_add_left 1 _
  latticeSlots := Finset.univ.filter (fun i => D.e 0 ∣ i.1)
  boxes := fun q =>
    Fintype.piFinset (fun i => canonicalSlotChoice (D.e 0) q i.1)
  boxes_lattice := by
    intro q b hb i
    have hbi : b i ∈ canonicalSlotChoice (D.e 0) q i.1 :=
      Fintype.mem_piFinset.mp hb i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold canonicalSlotChoice at hbi
    by_cases h0 : i.1 = 0
    · rw [if_pos h0, Finset.mem_filter] at hbi
      obtain ⟨-, hmap⟩ := hbi
      have hsome : (b i).isSome = true := by
        cases hbv : b i with
        | none => rw [hbv] at hmap; simp at hmap
        | some z => rfl
      simp [hsome, h0]
    · rw [if_neg h0] at hbi
      by_cases hdvd : D.e 0 ∣ i.1
      · rw [if_pos hdvd, Finset.mem_filter] at hbi
        simp [hbi.2, hdvd]
      · rw [if_neg hdvd, Finset.mem_singleton] at hbi
        simp [hbi, hdvd]

set_option linter.unusedVariables false in
theorem census_r0_law {D : CensusData} (hr : D.r = 0)
    {p N : ℕ} [Fact p.Prime] (q : ℕ) (hq : q = p ^ N) :
    (canonicalStratum1 D).count q = (censusW D).eval q := by
  have hq0 : 0 < q := by
    rw [hq]
    exact pow_pos (Fact.out (p := p.Prime)).pos N
  have he0 : 0 < D.e 0 := D.he 0
  have hf0 : 0 < D.f 0 := D.hf 0
  -- per-coordinate factorization (M08 Lemma A / `Fintype.card_piFinset`)
  simp only [Stratum1.count_def, canonicalStratum1]
  rw [Fintype.card_piFinset]
  -- each factor is a q-power with the interior-slot indicator exponent
  rw [Finset.prod_congr rfl fun i _ =>
      canonicalSlotChoice_card hq0 (D.e 0) i.1,
    Finset.prod_pow_eq_pow_sum]
  -- the indicator sums to the f₀ − 1 interior lattice slots
  have hsum : (∑ i : Fin D.m1, if D.e 0 ∣ i.1 ∧ i.1 ≠ 0 then 1 else 0)
      = D.f 0 - 1 := by
    rw [Fin.sum_univ_eq_sum_range fun j => if D.e 0 ∣ j ∧ j ≠ 0 then 1 else 0,
      ← Finset.card_filter]
    have himg : (Finset.range D.m1).filter (fun j => D.e 0 ∣ j ∧ j ≠ 0)
        = ((Finset.range (D.f 0)).filter fun j => j ≠ 0).image (D.e 0 * ·) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image,
        CensusData.m1]
      constructor
      · rintro ⟨hk, ⟨c, rfl⟩, hne⟩
        exact ⟨c, ⟨lt_of_mul_lt_mul_left hk (Nat.zero_le _),
          fun hc => hne (by simp [hc])⟩, rfl⟩
      · rintro ⟨c, ⟨hc, hc0⟩, rfl⟩
        exact ⟨mul_lt_mul_of_pos_left hc he0, ⟨c, rfl⟩,
          Nat.mul_ne_zero he0.ne' hc0⟩
    rw [himg, Finset.card_image_of_injective _
        (fun a b hab => Nat.eq_of_mul_eq_mul_left he0 hab),
      Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_range.mpr hf0),
      Finset.card_range]
  rw [hsum]
  simp [censusW, CensusData.d_eq_f0_of_r_eq_zero hr]

namespace C4cGate

/-- The C4c machine-gate datum: the worked M08 shape (e₀, h₀, f₀) = (2, 1, 2)
    (polygon (0,2) → (4,0), lattice slots {0, 2}, one interior slot).  NOT a
    blueprint unit — a C4c gate artifact (RealInstanceV2Gates precedent). -/
def gateData : CensusData where
  r := 0
  e := fun _ => 2
  h := fun _ => 1
  f := fun _ => 2
  he := fun _ => one_le_two
  hf := fun _ => one_le_two
  h_coprime := fun _ => Nat.coprime_one_left 2

/-- Gate 1: the canonical digit census at q = 3 is 3 = q^{f₀−1} (one pinned
    vertex · one free interior digit · two `none` slots). -/
example : (canonicalStratum1 gateData).count 3 = 3 := by decide

/-- Gate 2: the law instance at the gate datum, q = 3 = 3¹. -/
example : (canonicalStratum1 gateData).count 3 = (censusW gateData).eval 3 :=
  @census_r0_law gateData rfl 3 1 ⟨Nat.prime_three⟩ 3 (by norm_num)

end C4cGate

/-!
**PROVENANCE (units C6 + C7; BP_IV §1.2 + §2 C-table rows C6/C7; ADJUDICATED
at REVISION 3).**

* Blueprint: §2 C-table row C6 ("p-freeness by type: `censusW : Polynomial ℕ`
  + eval nonneg | by construction; one `simp` lemma") — landed below
  (`censusW_eval`, `censusW_eval_nonneg`).  C7's statement
  `censusW_eq_zero_of_unattained` is transcribed VERBATIM; §2 C-table row C7
  ("padding value 0 by definition of censusW at unattained vertices").
* Math source of record: O9 rev5 §4 padding clause — "a value-UNATTAINED
  VERTEX β_k empties the graded piece → the §8 padding value" (census 0).
* **REVISION-3 adjudication record (C7).**  Two compiled facts force the
  ruling: (i) the landed `censusW D = X^(f₀−1)` is a monomial in ℕ[X], hence
  NEVER 0 (`censusW_ne_zero` below); (ii) EVERY faithful per-datum `Attained`
  key over this carrier is provably ALWAYS TRUE — the all-zero φ-monomial
  index has weight 0, so the graded piece at the base slot β = 0 is nonempty
  at every datum (`attained_always` below).  Consequently the verbatim C7
  law holds VACUOUSLY (its hypothesis `¬ Attained D` is unsatisfiable), and
  NO non-vacuous per-datum padding law is expressible over `CensusData`: the
  carrier holds no polygon datum, so no expressible vertex can be unattained
  (C0d's provenance already recorded this).  The verbatim statement is landed
  below WITH ITS VACUITY ON DISPLAY (honesty invariant: `sorry`-free ≠
  non-vacuous — this theorem is machine-checked AND empty); the OPERATIVE
  padding clause re-keys to the r ≥ 1 stratum layer, where vertex data
  exists — recorded in BP_IV REVISION 3 as part of the re-chartered C5
  constructor design.  DO NOT cite `censusW_eq_zero_of_unattained` as
  content; cite `attained_always` when the void hypothesis must be shown.
  **SUPERSESSION (unit C5-ctor): the honest padding layer is now landed at
  the end of this file** — vertex-granular, count-valued (the O9 §2 (ADM)
  bullet's "census = 0, the §8 padding value" attaches to the STRATUM COUNT,
  never to the polynomial, which C7's verbatim shape mis-keyed): see
  `AnchoredMarchProof.paddingW`/`paddingJ`,
  `stratumR_count_eq_zero_of_unattained_vertex`, and the carrier-degeneracy
  record beside them.
-/

/-- C6 (p-freeness by type, the one `simp` lemma): the census value at every
    alphabet size is the pure power `q^(d−1)`, `d = ∏ᵢ f_i` the census field
    degree — a ℕ-polynomial evaluation, p-free BY TYPE.  (REVISION-3 R3.5
    re-key, executed at unit C5-ctor: previously `q^(f₀−1)`, the stage-0
    shadow; at r = 0 the two agree via `CensusData.d_eq_f0_of_r_eq_zero`.
    This statement was DERIVED, never blueprint-displayed — the C6 unit row
    fixes only "censusW : Polynomial ℕ + eval nonneg".) -/
@[simp] theorem censusW_eval (D : CensusData) (q : ℕ) :
    (censusW D).eval q = q ^ (D.d - 1) := by
  simp [censusW]

/-- C6 (the nonneg clause — trivial over ℕ, displayed for the C-table row). -/
theorem censusW_eval_nonneg (D : CensusData) (q : ℕ) :
    0 ≤ (censusW D).eval q :=
  Nat.zero_le _

/-- C7 adjudication fact (i): the landed census polynomial is never zero. -/
theorem censusW_ne_zero (D : CensusData) : censusW D ≠ 0 := by
  unfold censusW
  exact pow_ne_zero _ Polynomial.X_ne_zero

/-- C7: value-attainment of the census datum's base vertex — the graded piece
    at β = 0 is nonempty (O9 rev5 §4: a value-attained vertex carries
    `0 < attainDim`; a value-UNATTAINED vertex empties the piece and takes the
    §8 padding value 0). NAMED per BP_IV §1.2 C7's `Attained`; supplied by C7's
    owner (undefined upstream). -/
def Attained (D : CensusData) : Prop := 0 < D.attainDim 0

/-- C7 adjudication fact (ii): over the `CensusData` carrier the base slot is
    attained at EVERY datum — the all-zero φ-monomial index (every stage digit
    0) has weight 0 and lies in `Gset 0`.  This is the compiled witness that
    C7's hypothesis is void at this carrier (REVISION-3 record above). -/
theorem attained_always (D : CensusData) : Attained D := by
  have hj : ∀ i : Fin (D.r + 1),
      Nonempty (Fin (D.ledgerE i) × Fin (D.f i)) := fun i =>
    ⟨(⟨0, D.ledgerE_pos i⟩, ⟨0, D.hf i⟩)⟩
  refine Finset.card_pos.mpr ⟨fun i => (⟨0, D.ledgerE_pos i⟩, ⟨0, D.hf i⟩), ?_⟩
  have hwt0 : D.wt (fun i => (⟨0, D.ledgerE_pos i⟩, ⟨0, D.hf i⟩)) = 0 := by
    unfold CensusData.wt
    exact Finset.sum_eq_zero fun i _ => by simp
  unfold CensusData.Gset
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [hwt0], by rw [hwt0]⟩

/-- C6+C7: the census value CEN-W as data: a ℕ-coefficient polynomial in q per
    stratum (p-freeness is BY TYPE), with the padding law census = 0 at
    unattained vertices.

    **VACUOUS at this carrier** (REVISION-3 adjudication, provenance block
    above): the hypothesis `¬ Attained D` is unsatisfiable
    (`attained_always`), so this theorem carries NO content — the operative
    padding clause lives in the r ≥ 1 stratum layer (re-chartered C5).
    Statement kept verbatim per the statement fence. -/
theorem censusW_eq_zero_of_unattained {D : CensusData} (h : ¬ Attained D) :
    censusW D = 0 :=
  absurd (attained_always D) h

/-!
**PROVENANCE (unit C2; BP_IV §1.2, unit table §2 row C2; PROVED at
REVISION 3).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 ("C2: the r = 1 displayed
  criterion (O-9 r4, collapsing to the r3 form at f₁ = 1)"; statement
  transcribed VERBATIM below — UNCHANGED by the revision).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` §2, the rev-4 FULL
  form: "(ADM) at r = 1 ⟺ every on-line β_k ≥ h₁·((h₁⁻¹β_k mod e₁)
  + (f₁ − 1)·e₁)" (K7 verifies it numerically at seven (e₁, h₁, f₁, f₀)
  tuples, β ≤ 40).  The O9 r = 1 ledger has period e = e₁ and class
  decomposition {j₁ = j₁* + t·e₁ : 0 ≤ t < f₁} — NO stage-0 e₀ factor.
* **REVISION-3 adjudication record.**  Over the PRE-revision C0 carrier this
  statement was REFUTED in BOTH directions (compiled countermodels
  `C2Refutation.forward_refuted`/`reverse_refuted` at e₀ = 2 data — C1's
  carrier defect, live at r = 1; on file in git history at 33656d2).  The
  REVISION-3 carrier fix (`ledgerE` in `J`/`period`/`wt` — see
  `CensusCore.lean`) makes the stage-0 contribution the weight-0 factor f₀
  and the period e₁, exactly the O9 ledger; the statement is PROVED below
  from the pointwise core `attainDim_eq_d_iff_r1Bound_le`, which now holds
  at EVERY β with NO extra hypothesis (the pre-revision salvage's `e 0 = 1`
  hypothesis is structural on the repaired carrier).
* Deps: C2a (`r1Bound`, this file), C0/H1 (`CensusCore.lean`, REVISION-3
  form).  Proof = O9 §2's class decomposition, formalized:
  (i) the stage-0 pair contributes a weight-0 multiplicative factor
      1·f₀ = f₀ to every graded count (`card_filter_pi_two`);
  (ii) the mod-e₁ congruence pins the stage-1 class digit to
      j₁* = (h₁⁻¹β) mod e₁ (`weight_mod_iff`, via `ZMod.unitOfCoprime` — h₁ a
      unit mod e₁ by `h_coprime`, matching `r1Bound`'s inverse exactly), and
      pinning the first coordinate costs nothing (`card_filter_prod_fst_eq`);
  (iii) the residual f₁-window {h₁·(j₁* + t·e₁) : t < f₁} is monotone in t, so
      it is FULL iff its top member t = f₁ − 1 clears β (`card_filter_window`)
      — and that top-member inequality IS `r1Bound D β ≤ β`;
  (iv) the h₁ = 0 corner: coprimality forces e₁ = 1, every slot weight is 0,
      and both sides of the criterion hold trivially.
-/

namespace C2R1Salvage

/-- Counting helper 1: over the two-stage pi carrier, a predicate reading only
    stage 1 counts with multiplicity `card (G 0)`. -/
theorem card_filter_pi_two {G : Fin 2 → Type} [∀ i, Fintype (G i)]
    (Q : G 1 → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun j : (i : Fin 2) → G i => Q (j 1))).card
      = Fintype.card (G 0) * (Finset.univ.filter Q).card := by
  classical
  calc (Finset.univ.filter (fun j : (i : Fin 2) → G i => Q (j 1))).card
      = ∑ j : (i : Fin 2) → G i, if Q (j 1) then 1 else 0 :=
        Finset.card_filter _ _
    _ = ∑ p : G 0 × G 1, if Q p.2 then 1 else 0 :=
        Fintype.sum_equiv (piFinTwoEquiv G) _ _ (fun _ => rfl)
    _ = ∑ _x : G 0, ∑ y : G 1, if Q y then 1 else 0 := Fintype.sum_prod_type _
    _ = Fintype.card (G 0) * ∑ y : G 1, if Q y then 1 else 0 := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    _ = Fintype.card (G 0) * (Finset.univ.filter Q).card := by
        rw [Finset.card_filter]

/-- Counting helper 2: pinning the first coordinate of a product to a fixed
    value costs nothing. -/
theorem card_filter_prod_fst_eq {α β' : Type} [Fintype α] [Fintype β']
    [DecidableEq α] (a0 : α) (R : β' → Prop) [DecidablePred R] :
    (Finset.univ.filter (fun p : α × β' => p.1 = a0 ∧ R p.2)).card
      = (Finset.univ.filter R).card := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.card_filter]
  simp [ite_and]

/-- Counting helper 3: a monotone window over `Fin F1` is full iff its top
    element clears. -/
theorem card_filter_window {F1 : ℕ} (hF1 : 1 ≤ F1) (g : ℕ → ℕ) (hg : Monotone g)
    (β : ℕ) :
    (Finset.univ.filter (fun b : Fin F1 => g b.1 ≤ β)).card = F1
      ↔ g (F1 - 1) ≤ β := by
  constructor
  · intro hcard
    have huniv : (Finset.univ.filter (fun b : Fin F1 => g b.1 ≤ β))
        = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Fintype.card_fin]
    have hmem : (⟨F1 - 1, by omega⟩ : Fin F1)
        ∈ Finset.univ.filter (fun b : Fin F1 => g b.1 ≤ β) := by
      rw [huniv]; exact Finset.mem_univ _
    simpa using (Finset.mem_filter.mp hmem).2
  · intro htop
    have hall : ∀ b : Fin F1, g b.1 ≤ β := fun b =>
      le_trans (hg (by have := b.2; omega : b.1 ≤ F1 - 1)) htop
    rw [Finset.filter_true_of_mem (fun b _ => hall b), Finset.card_univ,
      Fintype.card_fin]

/-- Congruence helper: for `a < e₁` and `h₁` a unit mod `e₁`, the slot weight
    `(a + e₁·b)·h₁` is `≡ β (mod e₁)` iff `a` is the canonical class digit
    `(h₁⁻¹·β mod e₁)` — the exact inverse `r1Bound` reads. -/
theorem weight_mod_iff {E1 H1 : ℕ} [NeZero E1] (hcop : Nat.Coprime H1 E1)
    (β aa bb : ℕ) (ha : aa < E1) :
    ((aa + E1 * bb) * H1) % E1 = β % E1
      ↔ aa = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
          * (β : ZMod E1) : ZMod E1).val := by
  have hu : ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
      = (H1 : ZMod E1) := ZMod.coe_unitOfCoprime H1 hcop
  have hcast : (((aa + E1 * bb) * H1 : ℕ) : ZMod E1)
      = (aa : ZMod E1) * (H1 : ZMod E1) := by
    push_cast
    rw [ZMod.natCast_self]
    ring
  constructor
  · intro hmod
    have h1 : (((aa + E1 * bb) * H1 : ℕ) : ZMod E1) = ((β : ℕ) : ZMod E1) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [hcast, ← hu] at h1
    have h3 : (aa : ZMod E1)
        = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (β : ZMod E1) : ZMod E1) := by
      calc (aa : ZMod E1)
          = (aa : ZMod E1) * (ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ)
            * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) :=
            (Units.mul_inv_cancel_right _ _).symm
        _ = (β : ZMod E1) * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) := by
            rw [h1]
        _ = _ := mul_comm _ _
    calc aa = ((aa : ℕ) : ZMod E1).val := (ZMod.val_cast_of_lt ha).symm
      _ = _ := by rw [h3]
  · intro haa
    have h3 : (aa : ZMod E1)
        = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (β : ZMod E1) : ZMod E1) := by
      rw [haa]
      exact ZMod.natCast_zmod_val _
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [hcast, h3, ← hu]
    calc (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) * (β : ZMod E1))
          * ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
        = (β : ZMod E1) * ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
          * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) := by ring
      _ = (β : ZMod E1) := Units.mul_inv_cancel_right _ _

end C2R1Salvage

/-- The C2 pointwise core (REVISION 3 — the pre-revision salvage's `e 0 = 1`
    hypothesis is now STRUCTURAL on the repaired carrier): at r = 1, a slot β
    is FULLY attained iff it clears `r1Bound` — at EVERY β : ℕ, not only the
    on-line slots. -/
theorem attainDim_eq_d_iff_r1Bound_le {D : CensusData} (hr : D.r = 1)
    (β : ℕ) :
    D.attainDim β = D.d ↔ r1Bound D β ≤ β := by
  obtain ⟨r, e, h, f, he, hf, hcop⟩ := D
  dsimp only at hr
  subst hr
  set Dm : CensusData := ⟨1, e, h, f, he, hf, hcop⟩ with hDm
  haveI : NeZero (e 1) := ⟨by have := he 1; omega⟩
  set A : ℕ := (((ZMod.unitOfCoprime (h 1) (hcop 1))⁻¹ : (ZMod (e 1))ˣ)
      * (β : ZMod (e 1)) : ZMod (e 1)).val with hA
  -- the displayed RHS, unfolded
  have hrb : r1Bound Dm β = h 1 * (A + (f 1 - 1) * e 1) := by
    simp only [hA]
    rfl
  -- the degree and the LEDGER period (`ledgerE 0 = 1`, `ledgerE 1 = e 1`,
  -- both definitional at the concrete stages)
  have hd : Dm.d = f 0 * f 1 := Fin.prod_univ_two f
  have hperiod : Dm.period = e 1 :=
    (Fin.prod_univ_two Dm.ledgerE).trans (one_mul _)
  -- the stage weights: wphi 0 = 0, wphi 1 = E₁·(e₁·V₁ + h₁) = h₁ (V₁ = 0,
  -- E₁ = 1 at the top stage — F-ADM-3 re-key: at r = 1 the top-normalized
  -- and birth weights agree)
  have hwphi0 : Dm.wphi 0 = 0 := rfl
  have hwphi1 : Dm.wphi 1 = h 1 := by
    have hE : Dm.Emul 1 = 1 := Dm.Emul_last
    have h2 : Dm.wphi 1 = Dm.Emul 1 * (e 1 * 0 + h 1) := rfl
    rw [h2, hE, one_mul]
    omega
  -- the slot weight at r = 1: wt 𝐣 = (a₁ + e₁·b₁)·h₁ (the stage-1 ledger
  -- radix is e₁; the stage-0 term rides at weight 0)
  have hwt : ∀ j : Dm.J, Dm.wt j = ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 := by
    intro j
    have h2 : Dm.wt j
        = ((j 0).1.1 + Dm.ledgerE 0 * (j 0).2.1) * Dm.wphi 0
          + ((j 1).1.1 + e 1 * (j 1).2.1) * Dm.wphi 1 :=
      Fin.sum_univ_two _
    rw [h2, hwphi0, hwphi1, mul_zero, zero_add]
  -- reduce the census count to a stage-1 count (helper 1)
  have hattain : Dm.attainDim β
      = (Finset.univ.filter (fun j : Dm.J =>
          (((j 1).1.1 + e 1 * (j 1).2.1) * h 1) % e 1 = β % e 1
            ∧ ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 ≤ β)).card := by
    unfold CensusData.attainDim CensusData.Gset
    congr 1
    refine Finset.filter_congr ?_
    intro j _
    rw [hwt j, hperiod]
  have hstep : (Finset.univ.filter (fun j : Dm.J =>
        (((j 1).1.1 + e 1 * (j 1).2.1) * h 1) % e 1 = β % e 1
          ∧ ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 ≤ β)).card
      = Fintype.card (Fin 1 × Fin (f 0))
        * (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
            ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
              ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)).card :=
    C2R1Salvage.card_filter_pi_two
      (G := fun i => Fin (Dm.ledgerE i) × Fin (f i))
      (fun y => ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
        ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)
  rw [hattain, hstep, hd, hrb, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, one_mul]
  by_cases hzero : h 1 = 0
  · -- the h₁ = 0 corner: coprimality forces e₁ = 1; both sides hold
    have he1 : e 1 = 1 := by
      have hc := hcop 1
      rw [hzero] at hc
      exact (Nat.coprime_zero_left _).mp hc
    have hQtrue : ∀ y : Fin (e 1) × Fin (f 1),
        (((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
          ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β) := by
      intro y
      rw [hzero, mul_zero, he1]
      omega
    apply iff_of_true
    · rw [Finset.filter_true_of_mem (fun y _ => hQtrue y), Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, he1, one_mul]
    · rw [hzero, zero_mul]
      exact Nat.zero_le β
  · -- the live stage: pin the class digit (helper 4 + 2), count the window
    -- (helper 3)
    have hAlt : A < e 1 := by
      rw [hA]
      exact ZMod.val_lt _
    have hQiff : ∀ y : Fin (e 1) × Fin (f 1),
        ((((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
            ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)
          ↔ (y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ (A + e 1 * y.2.1) * h 1 ≤ β)) := by
      intro y
      constructor
      · rintro ⟨hc, hle⟩
        have h1y : y.1.1 = A := by
          rw [hA]
          exact (C2R1Salvage.weight_mod_iff (hcop 1) β y.1.1 y.2.1 y.1.2).mp hc
        refine ⟨Fin.ext h1y, ?_⟩
        rw [← h1y]
        exact hle
      · rintro ⟨hfst, hle⟩
        have h1y : y.1.1 = A := by rw [hfst]
        refine ⟨(C2R1Salvage.weight_mod_iff (hcop 1) β y.1.1 y.2.1 y.1.2).mpr
            (by rw [h1y, hA]), ?_⟩
        rw [h1y]
        exact hle
    have hcard2 : (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
          ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
            ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)).card
        = (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
            y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ (A + e 1 * y.2.1) * h 1 ≤ β)).card :=
      congrArg Finset.card (Finset.filter_congr (fun y _ => hQiff y))
    have hcard3 : (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
          y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ (A + e 1 * y.2.1) * h 1 ≤ β)).card
        = (Finset.univ.filter (fun b : Fin (f 1) =>
            (A + e 1 * b.1) * h 1 ≤ β)).card :=
      C2R1Salvage.card_filter_prod_fst_eq (⟨A, hAlt⟩ : Fin (e 1))
        (fun b : Fin (f 1) => (A + e 1 * b.1) * h 1 ≤ β)
    rw [hcard2, hcard3]
    have hmono : Monotone (fun t => (A + e 1 * t) * h 1) := by
      intro x y hxy
      change (A + e 1 * x) * h 1 ≤ (A + e 1 * y) * h 1
      gcongr
    have hf0 : 0 < f 0 := by have := hf 0; omega
    calc f 0 * (Finset.univ.filter (fun b : Fin (f 1) =>
            (A + e 1 * b.1) * h 1 ≤ β)).card = f 0 * f 1
        ↔ (Finset.univ.filter (fun b : Fin (f 1) =>
            (A + e 1 * b.1) * h 1 ≤ β)).card = f 1 := by
          constructor
          · exact Nat.eq_of_mul_eq_mul_left hf0
          · intro hh
            rw [hh]
      _ ↔ (A + e 1 * (f 1 - 1)) * h 1 ≤ β :=
          C2R1Salvage.card_filter_window (hf 1)
            (fun t => (A + e 1 * t) * h 1) hmono β
      _ ↔ h 1 * (A + (f 1 - 1) * e 1) ≤ β := by
          rw [show (A + e 1 * (f 1 - 1)) * h 1
              = h 1 * (A + (f 1 - 1) * e 1) from by ring]

/-- C2: the r = 1 displayed criterion (O-9 r4, collapsing to the r3 form at
    f₁ = 1): FULL attainment at β ⟺ β ≥ h₁·((h₁⁻¹β mod e₁) + (f₁ − 1)·e₁). -/
theorem admFull_r1_iff {D : CensusData} (hr : D.r = 1) :
    ADMFull D ↔ ∀ β ∈ D.onLineSlots,
      r1Bound D β ≤ β :=
  ⟨fun hFull β hβ => (attainDim_eq_d_iff_r1Bound_le hr β).mp
      (hFull.full_attained β hβ),
   fun hB => ⟨fun β hβ => (attainDim_eq_d_iff_r1Bound_le hr β).mpr (hB β hβ)⟩⟩

/-!
## Units C5/C5′ — the CEN-W/CEN-J statement layer (LANDED at REVISION 3)

**PROVENANCE (units C5/C5′ statement layer; BP_IV §1.2 + REVISION 3
adjudication).**  The pre-revision §1.2 display was BLOCKED at compile: FIVE
of its types (`GRBRow D`, `FreshRow D`, `StratumR D`, `JunctionStratum D`,
`AnchoredMarchProof D`) were declared nowhere in the corpus, and BP_III/BP_V
never chartered the owner rows at any signature (grep of `blueprints/BP_III.md`
and `BP_V.md`, 2026-08-01: zero hits) — a cross-blueprint seam failure, full
record in the pre-revision BLOCKED blocks (git history 33656d2) and BP_IV
REVISION 3.  The mop-up adjudication:

* **`GRBRow`/`FreshRow` become OPAQUE PREDICATE PARAMETERS** of
  `CensusValueRows` — the sanctioned `K3DeltaRow` pattern ("consumed as an
  opaque predicate parameter so this row compiles before Movement V lands").
  BP_IV declares NO alias and invents NO foreign content (§5 rule preserved);
  when BP_III lands its census-keyed (GR-B)/(FRESH) rows, they instantiate
  the parameters with NO re-key of this structure.
* **`StratumR`/`JunctionStratum` are BP_IV-OWNED counting carriers** (they
  appear only in BP_IV's display, so BP_IV owns them): landed below as
  order-guarded counting skeletons (`count : ℕ → ℕ` in the alphabet size q,
  the same N-free convention as `Stratum1.count`).  The geometric fields
  (polygon, vertex, march data) enter with the re-chartered wave-4
  constructor design — DERIVED, flagged for ratification.
* **The strata enter as PARAMETERS `SW`/`SJ`, not as an internal ∀** — over
  skeletal carriers an internal `∀ S : StratumR D` would make the row
  UNSATISFIABLE (an arbitrary `count` falsifies any value law), killing every
  consumer vacuously; the parametric form asserts the law AT the engine's
  constructed strata (the `canonicalStratum1` precedent, REV-2 finding 11).
* **`censusValueRows_of_anchoredMarch` is RE-CHARTERED** (REVISION 3): its
  hypothesis type `AnchoredMarchProof` had no spec anywhere; the wave-4 HARD
  unit now includes designing that carrier (the anchored-march digit-read
  ladder, O9 rev-5 §5.1) + proving the constructor, and ALSO re-keys
  `censusW` beyond the stage-0 shadow (C4c provenance note (c)) and carries
  the O9 §4 padding clause (C7's re-key, this file's C7 block).
  **EXECUTED — unit C5-ctor, end of this file (all four charges).**

**What IS landed and proved (C5 PROOF KERNEL — statement-fence-safe):** the
counting engine of the §2 C5 proof-sketch clause "(GR-B) digit read =
surjective F_q-linear map on graded piece ⇒ each digit costs q^d"
(O9 rev-5 §5.1: the read is fiber-uniform onto its image; onto F_{q^d} ⟺
FULL attainment).  Counting form: a surjective additive read has all fibers
of one size, card(fiber) · card(target) = card(source) — so at target
F_{q^d} each digit costs exactly q^d.  The wave-4 constructor applies this
once per march step.
-/

/-- C5 proof kernel (a): the digit-cost law, additive form.  A surjective
additive read `φ` off a finite source has all fibers of equal size
`card(source)/card(target)`: `card(fiber) · card(target) = card(source)`.
Fiber ≃ ker by translation through any anchor preimage; source ≃ quotient ×
ker by Lagrange; quotient ≃ target by first isomorphism. -/
theorem digitCost_of_surjective_read {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Finite V] (φ : V →+ W) (hφ : Function.Surjective φ) (w : W) :
    Nat.card {v : V // φ v = w} * Nat.card W = Nat.card V := by
  obtain ⟨v₀, hv₀⟩ := hφ w
  have efib : {v : V // φ v = w} ≃ φ.ker :=
    { toFun := fun v => ⟨v.1 - v₀, by
        simp [AddMonoidHom.mem_ker, map_sub, v.2, hv₀]⟩
      invFun := fun k => ⟨k.1 + v₀, by
        have hk : φ k.1 = 0 := AddMonoidHom.mem_ker.mp k.2
        simp [map_add, hk, hv₀]⟩
      left_inv := fun v => by ext; simp
      right_inv := fun k => by ext; simp }
  have equot : Nat.card (V ⧸ φ.ker) = Nat.card W :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  calc Nat.card {v : V // φ v = w} * Nat.card W
      = Nat.card (V ⧸ φ.ker) * Nat.card φ.ker := by
        rw [Nat.card_congr efib, equot, Nat.mul_comm]
    _ = Nat.card V :=
        (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm

/-- C5 proof kernel (b): the digit-cost law in the sketch's own register — a
surjective `F`-LINEAR digit read on a (finite) graded piece costs exactly
`card(target)` per digit (`= q^d` at target `F_{q^d}`).  Thin wrapper of
kernel (a) at `φ.toAddMonoidHom`. -/
theorem digitCost_of_surjective_linear_read {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [Finite V]
    (φ : V →ₗ[F] W) (hφ : Function.Surjective φ) (w : W) :
    Nat.card {v : V // φ v = w} * Nat.card W = Nat.card V :=
  digitCost_of_surjective_read φ.toAddMonoidHom hφ w

/-- C5 carrier (REVISION 3, BP_IV-owned): the order-r (r ≥ 1) stratum
    counting skeleton — the CEN-W quantifier type of `CensusValueRows.cenW`.
    `count q` is the stratum's digit census at alphabet size q (the N-free
    convention of `Stratum1.count`).  Geometric fields (polygon, vertices,
    march ladder) enter with the re-chartered wave-4 constructor design;
    DERIVED, flagged for division-lead/Codex ratification. -/
structure StratumR (D : CensusData) where
  hr : 1 ≤ D.r
  count : ℕ → ℕ

/-- C5′ carrier (REVISION 3, BP_IV-owned): the junction-stratum counting
    skeleton — the CEN-J quantifier type of `CensusValueRows.cenJ` (O9 CEN-J:
    the junction pin kills the (q^d−1)^ε factor).  Same skeletal discipline
    and ratification flag as `StratumR`. -/
structure JunctionStratum (D : CensusData) where
  hr : 1 ≤ D.r
  count : ℕ → ℕ

/-- C5/C5′: the queued r ≥ 1 mathematics as a named hypothesis row
    (REVISION-3 form; pre-revision display in git history).  The lower scope
    `1 ≤ D.r` and both conclusions are visible fields.  `GRBRow`/`FreshRow`
    are the BP_III-owned (GR-B)/(FRESH) rows, consumed as OPAQUE PREDICATE
    PARAMETERS (`K3DeltaRow` precedent) until the owner lands census-keyed
    forms; `SW`/`SJ` are the engine's constructed strata (see the provenance
    block: an internal ∀ over the skeletal carriers would be unsatisfiable).
    NOTE (C4c seam, recorded): at r ≥ 1 the pre-R3.5 `censusW` read the
    stage-0 shadow only — the re-key is EXECUTED at unit C5-ctor (below):
    this row's RHS now reads `q^(d−1)`, d = ∏ᵢ f_i, shape unchanged. -/
structure CensusValueRows (D : CensusData)
    (GRBRow FreshRow : CensusData → Prop)
    (SW : StratumR D) (SJ : JunctionStratum D) : Prop where
  cenW : 1 ≤ D.r → GRBRow D → ADMFull D →
    ∀ {p N : ℕ}, Fact p.Prime → ∀ q : ℕ, q = p ^ N →
      SW.count q = (censusW D).eval q
  cenJ : 1 ≤ D.r → GRBRow D → FreshRow D → ADMFull D →
    ∀ {p N : ℕ}, Fact p.Prime → ∀ q : ℕ, q = p ^ N →
      SJ.count q = (censusW D).eval q

/-!
## Unit C5-ctor — the anchored-march constructor (wave 4)

**PROVENANCE (units C5/C5′-ctor; BP_IV §1.2 + REVISION 3 §§R3.5/R3.7).**

* Blueprint: `lean/blueprints/BP_IV.md` REVISION 3 §R3.5 ("C5/C5′ constructor
  RE-CHARTERED (wave 4)").  The four charges, all landed below: (i) DESIGN
  the `AnchoredMarchProof` carrier (no spec existed anywhere); (ii) prove
  `censusValueRows_of_anchoredMarch` (§1.2 display, re-keyed to the landed
  opaque-parameter `CensusValueRows` per the §R3.1 C5/C5′ adjudication row);
  (iii) RE-KEY `censusW` beyond the stage-0 shadow (executed above, see the
  `censusW` docstring); (iv) land the honest O9 padding clause (C7's re-land,
  the padding layer below).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` — §5.1 (the digit
  read: F_q-linear, fiber-uniform onto its image, onto F_{q^d} ⟺ FULL
  attainment; "only then does the per-digit count take the value the census
  consumes"), §6.3 (CEN-W: per-abscissa factorization; on-line slots charge
  q^{mN−s(β_k)−d} per prescribed digit; E′ bookkeeping), §6.4 step 3 (the
  anchored/ρ-pinned reads, charged to the parent), §6.1 (TYPE-MARCH: the
  ANCHORED march — never slot-fresh — is the mechanism making the census
  polynomial), §2 (the (ADM) bullet's padding clause).
* Design (DERIVED — the blueprint displays no carrier body; hereby FLAGGED
  for division-lead/Codex ratification per the trust boundary):
  - `AnchoredMarch d q` is the ladder at ONE alphabet size: per step the
    §5.1 read as a surjective additive map `Win k →+ Tgt k` with the
    anchor-transported prescribed digit, plus the q-power card pins
    (`Win k` the level window of the graded piece, q^{winExp k}; `Tgt k`
    the digit target F_{q^d}) and the aggregated non-read padding `padExp`.
    The per-step engine is EXACTLY the proved kernel
    `digitCost_of_surjective_read`: `AnchoredMarch.cost_mul_pow` chains it
    down the ladder (each prescribed digit costs q^{winExp k − d}, in
    division-free form), and `cost_eq_of_balanced` closes the value against
    the `Balanced` E′-bookkeeping clause.
  - `AnchoredMarchProof` is the per-datum proof object at the engine's
    constructed strata `SW`/`SJ`: a march per prime-power alphabet under
    the row's own hypotheses ((GR-B) resp. (GR-B)+(FRESH) as the OPAQUE
    parameters, + (ADM)-FULL), the §6.3 factorization law (`countW`/`countJ`:
    the stratum digit census IS the march cost), the E′ balance, and the
    vertex-granular padding clause.  Fields quantify over the working
    alphabet, so the carrier lives in `Type` (`TreeRecursion` precedent —
    a Prop structure cannot carry the march data).
  - the constructor `censusValueRows_of_anchoredMarch` then produces the
    landed row: count = cost (factorization field) = q^{d−1} (kernel chain +
    balance) = `(censusW D).eval q` (the re-keyed C6 law).  The kernels do
    the counting work; the carrier fields are the honest [M]-row display of
    what the O9 engine instance must eventually supply.
-/

/-- C5-ctor (the march ladder at one alphabet size): the anchored-march
    digit-read ladder of O9 rev-5 §5.1/§6.3 reduced to its counting
    skeleton.  `steps` is L′ — the on-line lattice reads NOT charged to the
    anchor (§6.4 step 3: the chain's right-end read is the anchored/junction
    pin, ρ-determined, charged to the parent).  Step `k` carries the §5.1
    digit read `read k` (the graded-piece read r_{β_k} at working level:
    source the window piece `Win k` of card q^{winExp k} = q^{mN−s(β_k)},
    target `Tgt k` = the digit field F_{q^d}) and the anchor-transported
    prescribed digit `digit k` (§6.1 TYPE-MARCH: the march normalizers are
    anchored — "one fixed step, affine in the slot index" — never
    slot-fresh); `read_surj` is onto-ness, which at the engine instance is
    §5.1's ⟺: FULL attainment ((ADM) + the (GR-B) line clause).  `padExp`
    aggregates the q-power charges of every non-read slot (§6.3's
    strictly-above/left-tail/right-tail factors).  DERIVED design, flagged
    for ratification (provenance block above). -/
structure AnchoredMarch (d q : ℕ) where
  steps : ℕ
  padExp : ℕ
  Win : Fin steps → Type
  Tgt : Fin steps → Type
  [winGroup : ∀ k, AddCommGroup (Win k)]
  [tgtGroup : ∀ k, AddCommGroup (Tgt k)]
  [winFinite : ∀ k, Finite (Win k)]
  read : ∀ k, Win k →+ Tgt k
  digit : ∀ k, Tgt k
  read_surj : ∀ k, Function.Surjective (read k)
  winExp : Fin steps → ℕ
  card_win : ∀ k, Nat.card (Win k) = q ^ winExp k
  card_tgt : ∀ k, Nat.card (Tgt k) = q ^ d

attribute [instance] AnchoredMarch.winGroup AnchoredMarch.tgtGroup
  AnchoredMarch.winFinite

namespace AnchoredMarch

variable {d q : ℕ}

/-- The march cost: the q-power padding times the product of the per-step
    read-fiber counts at the anchored digits — §6.3's per-abscissa
    factorization with the digits prescribed. -/
noncomputable def cost (M : AnchoredMarch d q) : ℕ :=
  q ^ M.padExp * ∏ k, Nat.card {v : M.Win k // M.read k v = M.digit k}

/-- The E′ bookkeeping clause (§6.3), in ℕ-subtraction-free additive form:
    the ladder's exponents balance against the census exponent d − 1,
    `padExp + Σ_k winExp k = (d − 1) + d·L′`.  (Equivalently
    `padExp + Σ (winExp k − d) = d − 1` — E′(D,N) = Σ(mN − s(β_k)) − d·L′
    folded with the census value's exponent.) -/
def Balanced (M : AnchoredMarch d q) : Prop :=
  M.padExp + ∑ k, M.winExp k = (d - 1) + d * M.steps

/-- THE MARCH ENGINE (C5 proof kernel (a) chained down the ladder): each
    step's prescribed-digit fiber costs exactly q^{winExp k − d} — stated
    division-free: cost · q^{d·L′} = q^{padExp + Σ winExp}.  Per step,
    `digitCost_of_surjective_read` gives fiber · card(Tgt) = card(Win); the
    card pins evaluate both sides as q-powers. -/
theorem cost_mul_pow (M : AnchoredMarch d q) :
    M.cost * q ^ (d * M.steps) = q ^ (M.padExp + ∑ k, M.winExp k) := by
  have hstep : ∀ k : Fin M.steps,
      Nat.card {v : M.Win k // M.read k v = M.digit k} * Nat.card (M.Tgt k)
        = Nat.card (M.Win k) := fun k =>
    digitCost_of_surjective_read (M.read k) (M.read_surj k) (M.digit k)
  have hfib : ∀ k : Fin M.steps,
      Nat.card {v : M.Win k // M.read k v = M.digit k} * Nat.card (M.Tgt k)
        = q ^ M.winExp k := fun k => (hstep k).trans (M.card_win k)
  have htgt : (∏ k : Fin M.steps, Nat.card (M.Tgt k)) = q ^ (d * M.steps) := by
    calc (∏ k : Fin M.steps, Nat.card (M.Tgt k))
        = ∏ _k : Fin M.steps, q ^ d :=
          Finset.prod_congr rfl fun k _ => M.card_tgt k
      _ = (q ^ d) ^ M.steps := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = q ^ (d * M.steps) := (pow_mul q d M.steps).symm
  calc M.cost * q ^ (d * M.steps)
      = q ^ M.padExp
        * ((∏ k, Nat.card {v : M.Win k // M.read k v = M.digit k})
            * ∏ k, Nat.card (M.Tgt k)) := by
        simp only [cost]
        rw [htgt, mul_assoc]
    _ = q ^ M.padExp
        * ∏ k, (Nat.card {v : M.Win k // M.read k v = M.digit k}
            * Nat.card (M.Tgt k)) := by
        rw [Finset.prod_mul_distrib]
    _ = q ^ M.padExp * ∏ k, q ^ M.winExp k :=
        congrArg (q ^ M.padExp * ·)
          (Finset.prod_congr rfl fun k _ => hfib k)
    _ = q ^ (M.padExp + ∑ k, M.winExp k) := by
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add]

/-- The census value of a balanced anchored march: cost = q^{d−1} — the
    per-stratum value law the constructor consumes (q > 0 cancels the
    division-free engine identity). -/
theorem cost_eq_of_balanced (M : AnchoredMarch d q) (hq : 0 < q)
    (hb : M.Balanced) : M.cost = q ^ (d - 1) := by
  have hb' : M.padExp + ∑ k, M.winExp k = (d - 1) + d * M.steps := hb
  have h1 := M.cost_mul_pow
  rw [hb', pow_add] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hq _) h1

end AnchoredMarch

/-- C5-ctor carrier (the REVISION-3 R3.5 design): the anchored-march PROOF
    object for one census datum at the engine's constructed strata `SW`/`SJ`,
    with the BP_III-owned (GR-B)/(FRESH) rows as OPAQUE PREDICATE PARAMETERS
    (exactly `CensusValueRows`'s own seam).  Fields:
    * `marchW`/`marchJ` — at every prime-power alphabet q = p^N, under the
      row's hypotheses, the anchored-march ladder of the window resp.
      junction stratum (CEN-J's march differs by the ρ-pinned right end —
      §6.4 step 3 — which is why the two ladders are separate fields);
    * `countW`/`countJ` — the §6.3 per-abscissa factorization: the stratum's
      digit census IS the march cost;
    * `balanceW`/`balanceJ` — the E′ exponent bookkeeping;
    * `vertexSlots` + `paddingW`/`paddingJ` — the honest O9 §2 (ADM)-bullet
      padding clause at VERTEX granularity: a value-UNATTAINED vertex
      threshold (`attainDim β = 0`, i.e. G_β = 0) empties the stratum and
      the census takes the §8 padding value 0 — attached to the COUNT, the
      correct shape C7's verbatim law mis-keyed (see the padding layer's
      provenance below for the satisfiability record).
    DERIVED design, flagged for division-lead/Codex ratification. -/
structure AnchoredMarchProof (D : CensusData)
    (GRBRow FreshRow : CensusData → Prop)
    (SW : StratumR D) (SJ : JunctionStratum D) where
  vertexSlots : Finset ℕ
  marchW : ∀ {p N : ℕ}, Fact p.Prime → GRBRow D → ADMFull D →
    ∀ q : ℕ, q = p ^ N → AnchoredMarch D.d q
  countW : ∀ {p N : ℕ} (hp : Fact p.Prime) (hg : GRBRow D) (ha : ADMFull D)
    (q : ℕ) (hq : q = p ^ N), SW.count q = (marchW hp hg ha q hq).cost
  balanceW : ∀ {p N : ℕ} (hp : Fact p.Prime) (hg : GRBRow D) (ha : ADMFull D)
    (q : ℕ) (hq : q = p ^ N), (marchW hp hg ha q hq).Balanced
  marchJ : ∀ {p N : ℕ}, Fact p.Prime → GRBRow D → FreshRow D → ADMFull D →
    ∀ q : ℕ, q = p ^ N → AnchoredMarch D.d q
  countJ : ∀ {p N : ℕ} (hp : Fact p.Prime) (hg : GRBRow D) (hf : FreshRow D)
    (ha : ADMFull D) (q : ℕ) (hq : q = p ^ N),
    SJ.count q = (marchJ hp hg hf ha q hq).cost
  balanceJ : ∀ {p N : ℕ} (hp : Fact p.Prime) (hg : GRBRow D) (hf : FreshRow D)
    (ha : ADMFull D) (q : ℕ) (hq : q = p ^ N),
    (marchJ hp hg hf ha q hq).Balanced
  paddingW : ∀ β ∈ vertexSlots, D.attainDim β = 0 → ∀ q : ℕ, SW.count q = 0
  paddingJ : ∀ β ∈ vertexSlots, D.attainDim β = 0 → ∀ q : ℕ, SJ.count q = 0

/-- C5/C5′-ctor (BP_IV §1.2 display, re-keyed to the landed opaque-parameter
    `CensusValueRows` per REVISION 3 §R3.1): the anchored march produces the
    census value rows.  Per clause: count = cost (the factorization field)
    = q^{d−1} (the kernel chain + the E′ balance) = `(censusW D).eval q`
    (the re-keyed C6 law). -/
theorem censusValueRows_of_anchoredMarch (D : CensusData)
    {GRBRow FreshRow : CensusData → Prop}
    {SW : StratumR D} {SJ : JunctionStratum D}
    (hproof : AnchoredMarchProof D GRBRow FreshRow SW SJ) :
    CensusValueRows D GRBRow FreshRow SW SJ := by
  refine ⟨?_, ?_⟩
  · intro _hr hg ha p N hp q hq
    have hq0 : 0 < q := by
      rw [hq]
      exact pow_pos hp.out.pos N
    rw [hproof.countW hp hg ha q hq,
      (hproof.marchW hp hg ha q hq).cost_eq_of_balanced hq0
        (hproof.balanceW hp hg ha q hq),
      censusW_eval]
  · intro _hr hg hf ha p N hp q hq
    have hq0 : 0 < q := by
      rw [hq]
      exact pow_pos hp.out.pos N
    rw [hproof.countJ hp hg hf ha q hq,
      (hproof.marchJ hp hg hf ha q hq).cost_eq_of_balanced hq0
        (hproof.balanceJ hp hg hf ha q hq),
      censusW_eval]

/-!
## The honest padding layer (C7's re-land) + the carrier-degeneracy record

**PROVENANCE (unit C5-ctor charge (iv); O9 rev5 §2, the (ADM) bullet).**
The operative padding clause — "a value-UNATTAINED VERTEX β_k empties the
stratum (a nonzero vertex digit needs w(a_k) = β_k): census = 0, the §8
padding value" — lands here at VERTEX granularity, attached to the STRATUM
COUNT (`SW.count q = 0`), superseding C7's verbatim law (whose shape
`censusW D = 0` is impossible for the monomial — `censusW_ne_zero` — and
whose `Attained` key is always true — `attained_always`).  The clause is a
FIELD of `AnchoredMarchProof` (the [M]-row discipline: the emptiness
mechanism is TRI + the vertex digit-read, supplied by the eventual engine
instance; the skeletal `StratumR` cannot derive it) with the two operative
projection theorems below.

**SATISFIABILITY RECORD — RESOLVED at ADM-U0 (HDISCHARGE_H3 §1.3(b),
finding (F-ADM-1); definition-change authority).**  The escalation this
record originally carried is DISCHARGED.  Pre-repair, the carrier's
`triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i` row JOINTLY with `h_coprime`
forced e_i = 1 at every stage i ≥ 1, hence period = 1, hence EVERY β
value-attained by the zero ledger index — the padding hypothesis
`D.attainDim β = 0` was UNSATISFIABLE at the then-HEAD, machine-checked
by three compiled degeneracy witnesses (`e_eq_one_of_ne_zero` /
`period_eq_one` / `attainDim_pos`, RETIRED with the row they witnessed
against — see git history at this file).  The adjudication: the row was a
statement-level transcription defect of the blueprint's §1.2 display
against the math source of record — O9's r = 1 ledger (rev5 §§1–2) has
gcd(h₁, e₁) = 1 with e₁ > 1 allowed (warning display 1: e₁ = 3, h₁ = 2,
where 3 ∤ 2) — the C1/C2 precedent exactly (carrier wrong, law right: the
`ledgerE` fix of REVISION 3 §R3.3).  The repair DROPS the row
(`CensusCore.lean`, the ADM-U0 repair record on `CensusData`).  As this
record predicted, the padding law below was keyed to the post-repair
carrier and needed NO re-key; on the repaired carrier warning display 1
is representable, gives `attainDim 1 = 0` at period 3, and the clause is
LIVE (the K6 machine gate is unit ADM-U4's charge).
-/

/-- The census field degree is positive (each f_i ≥ 1). -/
theorem CensusData.d_pos (D : CensusData) : 0 < D.d :=
  Finset.prod_pos fun i _ => by have := D.hf i; omega

/-- Padding/value complementarity: an on-line value-unattained slot refutes
    (ADM)-FULL — the value rows (under `ADMFull`) and the padding clause
    (at an unattained vertex) can never both fire on one datum. -/
theorem not_admFull_of_unattained_onLineSlot {D : CensusData} {β : ℕ}
    (hβ : β ∈ D.onLineSlots) (h0 : D.attainDim β = 0) : ¬ ADMFull D := by
  intro h
  have h1 := h.full_attained β hβ
  have h2 := D.d_pos
  omega

/-- THE OPERATIVE PADDING LAW (window stratum): at a value-unattained vertex
    threshold the census takes the §8 padding value 0 — O9 rev5 §2's (ADM)
    bullet at the correct granularity and shape (count-valued), superseding
    the vacuous verbatim C7 law.  Satisfiability at HEAD: see the
    carrier-degeneracy record above. -/
theorem stratumR_count_eq_zero_of_unattained_vertex
    {D : CensusData} {GRBRow FreshRow : CensusData → Prop}
    {SW : StratumR D} {SJ : JunctionStratum D}
    (hproof : AnchoredMarchProof D GRBRow FreshRow SW SJ)
    {β : ℕ} (hβ : β ∈ hproof.vertexSlots) (h0 : D.attainDim β = 0)
    (q : ℕ) : SW.count q = 0 :=
  hproof.paddingW β hβ h0 q

/-- THE OPERATIVE PADDING LAW (junction stratum): the CEN-J twin. -/
theorem junctionStratum_count_eq_zero_of_unattained_vertex
    {D : CensusData} {GRBRow FreshRow : CensusData → Prop}
    {SW : StratumR D} {SJ : JunctionStratum D}
    (hproof : AnchoredMarchProof D GRBRow FreshRow SW SJ)
    {β : ℕ} (hβ : β ∈ hproof.vertexSlots) (h0 : D.attainDim β = 0)
    (q : ℕ) : SJ.count q = 0 :=
  hproof.paddingJ β hβ h0 q

namespace C5CtorGate

/-- The C5-ctor machine-gate datum: r = 1, e ≡ 1, h ≡ 1, f = (2, 1)
    (d = 2, all slot weights 0 — the deep-stratum regime, so (ADM)-FULL is
    genuinely PROVABLE below, not assumed).  NOT a blueprint unit — a
    positive-control gate (C4cGate/K9Gate precedent) confirming every
    `AnchoredMarchProof` field is satisfiable and the constructor fires
    end-to-end on the re-keyed `censusW`. -/
def gateData : CensusData where
  r := 1
  e := fun _ => 1
  h := fun _ => 1
  f := fun i => if i.1 = 0 then 2 else 1
  he := fun _ => le_refl 1
  hf := by intro i; split_ifs <;> omega
  h_coprime := fun _ => Nat.coprime_one_left 1

theorem gate_d : gateData.d = 2 := by decide

/-- Every gate slot weight is 0 (stage 0 carries weight 0; stage 1's digits
    are forced to 0 by `ledgerE = 1` and `f 1 = 1`). -/
theorem gate_wt (j : gateData.J) : gateData.wt j = 0 := by
  unfold CensusData.wt
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h0 : i.1 = 0
  · have hw : gateData.wphi i = 0 := by
      unfold CensusData.wphi
      simp [h0]
    rw [hw, mul_zero]
  · have he1 : gateData.e i = 1 := rfl
    have hL : gateData.ledgerE i = 1 := by
      unfold CensusData.ledgerE
      rw [if_neg h0, he1]
    have h1 : (j i).1.1 = 0 := by
      have hb := (j i).1.2
      omega
    have h2 : (j i).2.1 = 0 := by
      have hF : gateData.f i = 1 := by
        show (if i.1 = 0 then 2 else 1) = 1
        simp [h0]
      have hb := (j i).2.2
      omega
    rw [h1, h2, mul_zero, add_zero, zero_mul]

/-- (ADM)-FULL holds at the gate datum (every weight 0 ⇒ the single on-line
    slot 0 has `Gset 0 = univ` of card 2 = d). -/
theorem gate_admFull : ADMFull gateData := by
  constructor
  intro β hβ
  have hβ0 : β = 0 := by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hβ
    rw [← hj, gate_wt]
  subst hβ0
  have hgset : gateData.Gset 0 = Finset.univ := by
    unfold CensusData.Gset
    rw [Finset.filter_true_of_mem]
    intro j _
    exact ⟨by rw [gate_wt], (gate_wt j).le⟩
  have hcardJ : Fintype.card gateData.J = gateData.d := by decide
  unfold CensusData.attainDim
  rw [hgset, Finset.card_univ, hcardJ]

/-- The gate window stratum: digit census q^{d−1} = q. -/
def gateSW : StratumR gateData := ⟨le_refl 1, fun q => q⟩

/-- The gate junction stratum (same census — the empty-ladder shape). -/
def gateSJ : JunctionStratum gateData := ⟨le_refl 1, fun q => q⟩

/-- The gate march: the EMPTY ladder (L′ = 0), all census value in the
    padding exponent d − 1 = 1. -/
def gateMarch (q : ℕ) : AnchoredMarch gateData.d q where
  steps := 0
  padExp := 1
  Win := fun k => k.elim0
  Tgt := fun k => k.elim0
  winGroup := fun k => k.elim0
  tgtGroup := fun k => k.elim0
  winFinite := fun k => k.elim0
  read := fun k => k.elim0
  digit := fun k => k.elim0
  read_surj := fun k => k.elim0
  winExp := fun k => k.elim0
  card_win := fun k => k.elim0
  card_tgt := fun k => k.elim0

/-- The gate proof object: every `AnchoredMarchProof` field is satisfiable
    (opaque rows instantiated at `fun _ => True`, the O9-instance slot). -/
noncomputable def gateProof :
    AnchoredMarchProof gateData (fun _ => True) (fun _ => True)
      gateSW gateSJ where
  vertexSlots := ∅
  marchW := fun _ _ _ q _ => gateMarch q
  countW := fun _ _ _ q _ => by
    simp [gateSW, gateMarch, AnchoredMarch.cost]
  balanceW := fun _ _ _ q _ => by
    simp [AnchoredMarch.Balanced, gateMarch, gate_d]
  marchJ := fun _ _ _ _ q _ => gateMarch q
  countJ := fun _ _ _ _ q _ => by
    simp [gateSJ, gateMarch, AnchoredMarch.cost]
  balanceJ := fun _ _ _ _ q _ => by
    simp [AnchoredMarch.Balanced, gateMarch, gate_d]
  paddingW := fun β hβ => absurd hβ (Finset.notMem_empty β)
  paddingJ := fun β hβ => absurd hβ (Finset.notMem_empty β)

/-- THE GATE: the constructor fires end-to-end — the CEN-W row instance at
    q = 5 = 5¹, against the re-keyed `censusW` (eval = 5^{d−1} = 5). -/
example : gateSW.count 5 = (censusW gateData).eval 5 :=
  (censusValueRows_of_anchoredMarch gateData gateProof).cenW
    (le_refl 1) trivial gate_admFull (p := 5) (N := 1)
    ⟨by norm_num⟩ 5 (by norm_num)

end C5CtorGate

end LeanUrat.Scaffold
