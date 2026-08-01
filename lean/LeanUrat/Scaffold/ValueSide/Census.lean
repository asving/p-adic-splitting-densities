/-
BP_IV §1.2 — Step 14, the (ADM)-FULL and level-1 census layers (`Census.lean`).
Units in this file: SKEL (module skeleton) · C3 (the `Decidable (ADMFull D)`
instance) · C2a (`r1Bound`) · C1 (`admFull_of_r_eq_zero` — statement landed
verbatim, REFUTED over the landed C0 definitions: honest `sorry` + compiled
negation witness `C1Refutation.not_admFull_cmC1` + the e₀ = 1 salvage; see the
C1 provenance block) · C4a (`Stratum1`, the level-1 stratum carrier:
Finset-of-boxes datum with per-coordinate windows c_i = Δ(i)+1, + `count`,
`padExp`) · C4b (`vertexChain_telescope` + `vertexChain_telescope_units`, the
M08 Lemma D vertex-chain telescope — the carrier-free counting engine; see its
provenance block for the honest scope).  Later waves add C2 (`admFull_r1_iff`),
C4c (`canonicalStratum1` / `censusW` + `census_r0_law`),
C6, C7, and the wave-4 HARD units C5/C5′ (CEN-W r ≥ 1 / CEN-J).
Import graph (BP_IV §1.0): `CensusCore → Hyps` and `{CensusCore, Hyps} →
Census`, never a cycle — this module imports both and is imported by no
value-side module.
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
**PROVENANCE (unit C1; BP_IV §1.2, unit table §2 row C1) — BLOCKED: statement
REFUTED over the landed C0 definitions.**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 ("C1: r = 0 automaticity — the
  ONLY automatic case"; statement transcribed VERBATIM below, per the
  statement fence).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` §1 + §2
  (automaticity, re-scoped to the FULL predicate): "r = 0: all ledger weights
  are 0 and **e = 1**, so dim G_β = #{wt ≤ β} = **m = f₀ = d**".  Note the
  scope: the O9 ledger has `e := e₁⋯e_r` (**e = 1 at r = 0** — no e₀ factor)
  and m = f₀ ledger indices at r = 0.
* **The refutation (machine-checked below, `C1Refutation`).**  The landed C0
  carrier gives stage 0 a full `Fin (D.e 0) × Fin (D.f 0)` pair in `J` (and
  an `e 0` factor in `period`), while `wphi 0 = 0`; so at r = 0 the whole
  `J` (all `e₀·f₀` indices) sits at weight 0, `onLineSlots = {0}`,
  `attainDim 0 = e₀·f₀`, but `d = f₀`.  Hence `ADMFull D ↔ e₀ = 1`, and the
  unconditional statement fails at the datum `cmC1` (r = 0, e₀ = 2, h₀ = 1,
  f₀ = 1, all structure fields satisfied): `attainDim 0 = 2 ≠ 1 = d`.
* **Localization (salvage, proved below).**  Adding `∀ i, D.e i = 1` (at
  r = 0 this is exactly the O9 convention e₀ = 1; stage 0's pair collapses to
  `Fin 1 × Fin f₀ ≅ Fin f₀`, the f₀-element ledger) makes the statement true:
  `admFull_of_r_eq_zero_of_e_eq_one`.  So the defect is EXACTLY the spurious
  stage-0 `Fin (e 0)` factor of the landed `J`/`period` (C0's derived bodies,
  flagged DERIVED in their own provenance) against the blueprint-verbatim
  carrier that leaves `e 0` a free parameter ≥ 1.  Repair options for the
  division lead: (i) constrain the carrier (`e 0 = 1` field — statement
  change, escalation required), or (ii) re-derive `J`/`period` with stage 0
  contributing `Fin (f 0)` only — a C0-body change, also adjudication-level.
* Deps: C0 (`CensusCore.lean`), H1 (`ADMFull`).
-/

/-- C1: r = 0 automaticity — the ONLY automatic case (ROOT (ADM) row, exact). -/
theorem admFull_of_r_eq_zero {D : CensusData} (hr : D.r = 0) : ADMFull D := by
  sorry
-- BLOCKED(C1): statement FALSE as written over the landed C0 definitions —
-- refuted by the compiled negation witness `C1Refutation.not_admFull_cmC1`
-- below (datum r = 0, e₀ = 2, h₀ = 1, f₀ = 1: attainDim 0 = e₀·f₀ = 2 but
-- d = f₀ = 1).  True exactly on the O9 scope e₀ = 1 (`e = 1 at r = 0`,
-- O9 rev5 §1) — see `admFull_of_r_eq_zero_of_e_eq_one`.  Statement fence:
-- not weakened here; escalated to the division lead.

namespace C1Refutation

/-- The C1 negation witness datum: r = 0, e₀ = 2, h₀ = 1, f₀ = 1 (every
    `CensusData` field satisfied: `triangular` is vacuous at r = 0 and
    gcd(1, 2) = 1).  NOT a blueprint unit — a C1 adjudication artifact. -/
noncomputable def cmC1 : CensusData where
  r := 0
  e := fun _ => 2
  h := fun _ => 1
  f := fun _ => 1
  he := fun _ => one_le_two
  hf := fun _ => le_rfl
  triangular := fun i hi => absurd (Fin.val_eq_zero i) hi
  h_coprime := fun _ => Nat.coprime_one_left 2

/-- All `cmC1` slot weights vanish (`wphi 0 = 0`: stage 0 rides at weight 0). -/
lemma cm_wt (j : cmC1.J) : cmC1.wt j = 0 := by
  unfold CensusData.wt
  apply Finset.sum_eq_zero
  intro i _
  simp [CensusData.wphi]

/-- Every index of `cmC1.J` is on-line at β = 0. -/
lemma cm_gset : cmC1.Gset 0 = Finset.univ := by
  unfold CensusData.Gset
  rw [Finset.filter_true_of_mem]
  intro j _
  exact ⟨by rw [cm_wt], by rw [cm_wt]⟩

/-- **The compiled C1 refutation**: `cmC1` has r = 0 but is NOT (ADM)-FULL —
    `attainDim 0 = |J| = e₀·f₀ = 2` while `d = f₀ = 1`. -/
theorem not_admFull_cmC1 : ¬ ADMFull cmC1 := by
  intro h
  have h0mem : (0 : ℕ) ∈ cmC1.onLineSlots := by
    unfold CensusData.onLineSlots
    exact Finset.mem_image.mpr
      ⟨fun _ => (⟨0, two_pos⟩, ⟨0, one_pos⟩), Finset.mem_univ _, cm_wt _⟩
  have heq := h.full_attained 0 h0mem
  have hd : cmC1.d = 1 := by
    unfold CensusData.d
    simp [cmC1]
  have hcard : cmC1.attainDim 0 = 2 := by
    unfold CensusData.attainDim
    rw [cm_gset, Finset.card_univ]
    rw [show Fintype.card cmC1.J = 2 from rfl]
  rw [hcard, hd] at heq
  exact absurd heq (by norm_num)

theorem cmC1_r_eq_zero : cmC1.r = 0 := rfl

end C1Refutation

/-- The C1 SALVAGE (NOT a blueprint unit — a C1 adjudication artifact): the
    r = 0 automaticity IS true on the O9 scope `e = 1 at r = 0` (rev5 §1),
    i.e. with the spurious stage-0 `Fin (e 0)` factor collapsed.  Proof =
    the blueprint's sketch: all weights are 0, `onLineSlots = {0}`,
    `Gset 0 = univ`, and `|J| = ∏ eᵢfᵢ = ∏ fᵢ = d` under `e ≡ 1`. -/
theorem admFull_of_r_eq_zero_of_e_eq_one {D : CensusData} (hr : D.r = 0)
    (he1 : ∀ i, D.e i = 1) : ADMFull D := by
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
  have hcardJ : Fintype.card D.J = ∏ i, D.e i * D.f i := by
    have h1 : Fintype.card D.J
        = Fintype.card ((i : Fin (D.r + 1)) → Fin (D.e i) × Fin (D.f i)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [h1]
    simp
  unfold CensusData.attainDim CensusData.d
  rw [hgset, Finset.card_univ, hcardJ]
  exact Finset.prod_congr rfl fun i _ => by rw [he1 i, one_mul]

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

end LeanUrat.Scaffold
