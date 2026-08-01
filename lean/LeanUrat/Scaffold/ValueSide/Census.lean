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
provenance block for the honest scope) · C4c (`censusW` + `canonicalStratum1`
+ `census_r0_law` — the M08 Theorem 2 r = 0 census law AT THE CONSTRUCTED
carrier, junction-pinned and type-aggregated; see the C4c provenance block).
C2 (`admFull_r1_iff` — statement landed verbatim, REFUTED over the landed C0
definitions in BOTH directions: honest `sorry` + compiled countermodels
`C2Refutation.forward_refuted`/`reverse_refuted` + the e₀ = 1 salvage
`admFull_r1_iff_of_e0_eq_one`; see the C2 provenance block) lands at the END
of this file.  C5/C5′ (CEN-W r ≥ 1 / CEN-J): statements BLOCKED at compile —
owner rows/carriers/hypothesis types absent (see the two BLOCKED blocks at
the end of this file); the C5 digit-cost proof kernels
(`digitCost_of_surjective_read` / `digitCost_of_surjective_linear_read`) ARE
landed and proved.  Later waves add C6.
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
  constructor (recorded to prevent silent consumption).  (c) `hr` and the
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

/-- C6+C7: the census value CEN-W as data: a ℕ-coefficient polynomial in q per
    stratum (p-freeness is BY TYPE), with the padding law census = 0 at
    unattained vertices. -/
noncomputable def censusW (D : CensusData) : Polynomial ℕ                -- unit C4c
  := Polynomial.X ^ (D.f 0 - 1)

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
  simp [censusW]

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
  triangular := fun i hi => absurd (Fin.val_eq_zero i) hi
  h_coprime := fun _ => Nat.coprime_one_left 2

/-- Gate 1: the canonical digit census at q = 3 is 3 = q^{f₀−1} (one pinned
    vertex · one free interior digit · two `none` slots). -/
example : (canonicalStratum1 gateData).count 3 = 3 := by decide

/-- Gate 2: the law instance at the gate datum, q = 3 = 3¹. -/
example : (canonicalStratum1 gateData).count 3 = (censusW gateData).eval 3 :=
  @census_r0_law gateData rfl 3 1 ⟨Nat.prime_three⟩ 3 (by norm_num)

end C4cGate

/-!
**PROVENANCE (unit C7; BP_IV §1.2 + §2 C-table row C7).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 — the C7 statement
  `censusW_eq_zero_of_unattained {D : CensusData} (h : ¬ Attained D) :
  censusW D = 0` is transcribed VERBATIM; §2 C-table row C7 ("padding value 0
  by definition of censusW at unattained vertices | C4c | EASY | ROOT (ADM)
  row, padding clause").
* Math source of record: O9 rev5 §4 padding clause — "a value-UNATTAINED
  VERTEX β_k empties the graded piece → the §8 padding value" (census 0).
* `Attained` is UNDEFINED corpus-wide (BP_IV names it only in this C7 row); as
  C7's owner I supply the faithful named predicate below — the base vertex
  β = 0 carries value (its graded piece is nonempty). NAMED, non-fiat, flagged
  for division-lead/Codex ratification (trust boundary: statements/defs are
  where errors hide).

* **BLOCKED(C7) — the padding law is FALSE against the LANDED `censusW`.**
  C4c landed `censusW D := Polynomial.X ^ (D.f 0 - 1)`, the UNGUARDED canonical
  monomial (its own provenance, this file: "C7's owner must key `Attained` to
  match or escalate a `censusW` re-key"). In ℕ[X] (a domain) `X ^ k ≠ 0` for
  every k, so `censusW D = 0` is UNCONDITIONALLY FALSE — no faithful `Attained`
  (one that can be false on some datum) makes it provable, and forcing it true
  would need `Attained ≡ True` (discharge by fiat: forbidden; also vacuous).
  The blueprint's "0 BY DEFINITION of censusW" presumes a GUARDED censusW
  (`if Attained D then X^(f₀−1) else 0`); the landed C4c is unguarded. The fix
  is a `censusW` re-key (C4c's declaration), which also ripples into the
  just-landed `census_r0_law` (its closing `simp [censusW]` would then need
  `Attained` at the r = 0 canonical datum, i.e. C1 `admFull_of_r_eq_zero`,
  not yet landed) — an ESCALATION outside unit C7's EASY scope. Honest `sorry`
  stands per the honesty invariant; statement kept verbatim, not weakened.
-/

/-- C7: value-attainment of the census datum's base vertex — the graded piece
    at β = 0 is nonempty (O9 rev5 §4: a value-attained vertex carries
    `0 < attainDim`; a value-UNATTAINED vertex empties the piece and takes the
    §8 padding value 0). NAMED per BP_IV §1.2 C7's `Attained`; supplied by C7's
    owner (undefined upstream) and FLAGGED for ratification. -/
def Attained (D : CensusData) : Prop := 0 < D.attainDim 0

/-- C6+C7: the census value CEN-W as data: a ℕ-coefficient polynomial in q per
    stratum (p-freeness is BY TYPE), with the padding law census = 0 at
    unattained vertices. -/
theorem censusW_eq_zero_of_unattained {D : CensusData} (h : ¬ Attained D) :
    censusW D = 0 := by
  -- BLOCKED(C7): the landed `censusW D = Polynomial.X ^ (D.f 0 - 1)` is a
  -- monic monomial in the domain ℕ[X], hence NEVER 0; the goal is false for
  -- every D regardless of `h`. Requires a GUARDED `censusW` re-key (C4c
  -- declaration + `census_r0_law` ripple via C1) — escalation, out of C7 scope.
  sorry

/-!
**PROVENANCE (unit C2; BP_IV §1.2, unit table §2 row C2) — BLOCKED: statement
REFUTED over the landed C0 definitions in BOTH directions; compiled
countermodels + the e₀ = 1 salvage below.**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 ("C2: the r = 1 displayed
  criterion (O-9 r4, collapsing to the r3 form at f₁ = 1)"; statement
  transcribed VERBATIM below, per the statement fence).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` §2, the rev-4 FULL
  form: "(ADM) at r = 1 ⟺ every on-line β_k ≥ h₁·((h₁⁻¹β_k mod e₁)
  + (f₁ − 1)·e₁)" (K7 verifies it numerically at seven (e₁, h₁, f₁, f₀)
  tuples, β ≤ 40).  Note the scope: as at C1, the O9 r = 1 ledger has period
  e = e₁ and class decomposition {j₁ = j₁* + t·e₁ : 0 ≤ t < f₁} — NO stage-0
  e₀ factor (the O9 convention is e₀ = 1).
* **The refutation (machine-checked below, `C2Refutation`).**  Over the landed
  C0 carrier (stage 0 a full `Fin (e 0) × Fin (f 0)` pair in `J` at weight 0,
  an `e 0` factor in `period`), BOTH directions fail at e₀ = 2 — C1's defect,
  live at r = 1:
  - ⟹ fails (`cmForward`: e = (2,1), h = (1,1), f = (1,2)): every on-line
    slot IS fully attained (weights {0, 1}, each carried by the d = 2 stage-0
    copies, and period e₀e₁ = 2 splits the two classes), yet at the on-line
    slot β = 0 the bound reads r1Bound = h₁·(0 + (f₁−1)·e₁) = 1 > 0.
  - ⟸ fails (`cmReverse`: e = (2,1), h = (1,1), f = (1,1)): the bound clears
    every on-line slot (`onLineSlots = {0}`, r1Bound 0 = h₁·(0 + 0) = 0),
    yet `attainDim 0 = e₀·f₀·f₁ = 2 ≠ 1 = f₀·f₁ = d`.
* **Localization (salvage, proved below — NOT a blueprint unit, a C2
  adjudication artifact).**  Adding `D.e 0 = 1` (the O9 stage-0 scope — the
  SAME single hypothesis as C1's salvage, with e₁ left free) makes the
  criterion TRUE: `admFull_r1_iff_of_e0_eq_one`, from the pointwise core
  `attainDim_eq_d_iff_r1Bound_le` (which holds at EVERY β, not just on-line
  slots).  So the C1 repair adjudication (pin `e 0 = 1` carrier-side or
  hypothesis-side; division lead) cures C2 as well; nothing beyond the e₀
  defect obstructs the r ≤ 1 layer.
* Deps: C2a (`r1Bound`, this file), C0/H1 (`CensusCore.lean`).  C1 is listed
  as a dep in the unit table but its theorem is not consumed by either
  direction; its REFUTED status is shared (same defect, same salvage scope).
-/

/-- C2: the r = 1 displayed criterion (O-9 r4, collapsing to the r3 form at
    f₁ = 1): FULL attainment at β ⟺ β ≥ h₁·((h₁⁻¹β mod e₁) + (f₁ − 1)·e₁). -/
theorem admFull_r1_iff {D : CensusData} (hr : D.r = 1) :
    ADMFull D ↔ ∀ β ∈ D.onLineSlots,
      r1Bound D β ≤ β := by
  sorry
-- BLOCKED(C2): statement FALSE as written over the landed C0 definitions, in
-- BOTH directions — compiled countermodels `C2Refutation.forward_refuted` and
-- `C2Refutation.reverse_refuted` below (e₀ = 2 data: the stage-0 digits
-- multiply `attainDim` by e₀ while `d` and `r1Bound` are e₀-blind).  True
-- exactly on the O9 scope e₀ = 1 — proved as `admFull_r1_iff_of_e0_eq_one`.
-- Statement fence: not weakened here; escalated to the division lead (same
-- adjudication as C1).

namespace C2Refutation

/-- The ⟹-direction countermodel: r = 1, e = (2,1), h = (1,1), f = (1,2).
    (ADM)-FULL HOLDS — the ledger weights are {0, 1} (j₁ = b₁, weight h₁·b₁),
    each on-line slot catches its full d = 2 indices via the two weight-0
    stage-0 digits, and period e₀e₁ = 2 separates the two classes — but the
    displayed bound FAILS at the on-line slot β = 0:
    r1Bound = h₁·((h₁⁻¹·0 mod e₁) + (f₁ − 1)·e₁) = 1·(0 + 1·1) = 1 > 0.
    NOT a blueprint unit — a C2 adjudication artifact. -/
def cmForward : CensusData where
  r := 1
  e := ![2, 1]
  h := ![1, 1]
  f := ![1, 2]
  he := by decide
  hf := by decide
  triangular := by decide
  h_coprime := by decide

theorem cmForward_admFull : ADMFull cmForward := ⟨by decide⟩

theorem cmForward_bound_fails :
    ¬ ∀ β ∈ cmForward.onLineSlots, r1Bound cmForward β ≤ β := by decide

/-- **The compiled C2 ⟹ refutation**: over the landed carrier, FULL
    attainment does NOT imply the displayed r = 1 inequality. -/
theorem forward_refuted :
    ¬ ∀ (D : CensusData), D.r = 1 →
      (ADMFull D → ∀ β ∈ D.onLineSlots, r1Bound D β ≤ β) :=
  fun H => cmForward_bound_fails (H cmForward rfl cmForward_admFull)

/-- The ⟸-direction countermodel: r = 1, e = (2,1), h = (1,1), f = (1,1).
    The displayed bound clears every on-line slot (`onLineSlots = {0}` — all
    weights vanish — and r1Bound 0 = h₁·(0 + 0·e₁) = 0 ≤ 0), but FULL
    attainment FAILS: `attainDim 0 = e₀·f₀·e₁·f₁ = 2` while `d = f₀·f₁ = 1`.
    NOT a blueprint unit — a C2 adjudication artifact. -/
def cmReverse : CensusData where
  r := 1
  e := ![2, 1]
  h := ![1, 1]
  f := ![1, 1]
  he := by decide
  hf := by decide
  triangular := by decide
  h_coprime := by decide

theorem cmReverse_bound_clears :
    ∀ β ∈ cmReverse.onLineSlots, r1Bound cmReverse β ≤ β := by decide

theorem cmReverse_not_admFull : ¬ ADMFull cmReverse :=
  fun hFull => absurd hFull.full_attained (by decide)

/-- **The compiled C2 ⟸ refutation**: over the landed carrier, clearing the
    displayed r = 1 inequality does NOT imply FULL attainment. -/
theorem reverse_refuted :
    ¬ ∀ (D : CensusData), D.r = 1 →
      ((∀ β ∈ D.onLineSlots, r1Bound D β ≤ β) → ADMFull D) :=
  fun H => cmReverse_not_admFull (H cmReverse rfl cmReverse_bound_clears)

/-- **The compiled refutation of the C2 statement itself** (via the ⟹ leg):
    the ∀-closure of `admFull_r1_iff` is false. -/
theorem admFull_r1_iff_refuted :
    ¬ ∀ (D : CensusData), D.r = 1 →
      (ADMFull D ↔ ∀ β ∈ D.onLineSlots, r1Bound D β ≤ β) :=
  fun H => cmForward_bound_fails ((H cmForward rfl).mp cmForward_admFull)

end C2Refutation

/-!
**The C2 SALVAGE (NOT a blueprint unit — a C2 adjudication artifact).**
`C2R1Salvage` holds four generic counting/congruence helpers; the payoff pair
is `attainDim_eq_d_iff_r1Bound_le` (the pointwise criterion, at every β) and
`admFull_r1_iff_of_e0_eq_one` (the C2 statement under the O9 scope `e 0 = 1`,
e₁ free).  Proof = O9 §2's class decomposition, formalized:
(i) the stage-0 pair contributes a weight-0 multiplicative factor
    e₀·f₀ = f₀ to every graded count (`card_filter_pi_two`);
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

/-- The C2 SALVAGE core (pointwise form; NOT a blueprint unit — a C2
    adjudication artifact): at r = 1 with the O9 stage-0 scope e₀ = 1 (e₁
    free), a slot β is FULLY attained iff it clears `r1Bound` — at EVERY
    β : ℕ, not only the on-line slots. -/
theorem attainDim_eq_d_iff_r1Bound_le {D : CensusData} (hr : D.r = 1)
    (he0 : D.e 0 = 1) (β : ℕ) :
    D.attainDim β = D.d ↔ r1Bound D β ≤ β := by
  obtain ⟨r, e, h, f, he, hf, htri, hcop⟩ := D
  dsimp only at hr he0
  subst hr
  set Dm : CensusData := ⟨1, e, h, f, he, hf, htri, hcop⟩ with hDm
  haveI : NeZero (e 1) := ⟨by have := he 1; omega⟩
  set A : ℕ := (((ZMod.unitOfCoprime (h 1) (hcop 1))⁻¹ : (ZMod (e 1))ˣ)
      * (β : ZMod (e 1)) : ZMod (e 1)).val with hA
  -- the displayed RHS, unfolded
  have hrb : r1Bound Dm β = h 1 * (A + (f 1 - 1) * e 1) := by
    simp only [hA]
    rfl
  -- the degree and the period
  have hd : Dm.d = f 0 * f 1 := Fin.prod_univ_two f
  have hperiod : Dm.period = e 1 := by
    have h2 : Dm.period = e 0 * e 1 := Fin.prod_univ_two e
    rw [h2, he0, one_mul]
  -- the stage weights: wphi 0 = 0, wphi 1 = e₁·V₁ + h₁ = h₁ (V₁ = 0)
  have hwphi0 : Dm.wphi 0 = 0 := rfl
  have hwphi1 : Dm.wphi 1 = h 1 := by
    have h2 : Dm.wphi 1 = e 1 * 0 + h 1 := rfl
    omega
  -- the slot weight at r = 1: wt 𝐣 = (a₁ + e₁·b₁)·h₁
  have hwt : ∀ j : Dm.J, Dm.wt j = ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 := by
    intro j
    have h2 : Dm.wt j
        = ((j 0).1.1 + e 0 * (j 0).2.1) * Dm.wphi 0
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
      = Fintype.card (Fin (e 0) × Fin (f 0))
        * (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
            ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
              ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)).card :=
    C2R1Salvage.card_filter_pi_two (G := fun i => Fin (e i) × Fin (f i))
      (fun y => ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
        ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)
  rw [hattain, hstep, hd, hrb, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, he0, one_mul]
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

/-- The C2 SALVAGE (NOT a blueprint unit — a C2 adjudication artifact): the
    r = 1 displayed criterion IS true on the O9 stage-0 scope `e 0 = 1`
    (e₁ free) — the exact scope of C1's salvage
    `admFull_of_r_eq_zero_of_e_eq_one`, restricted to stage 0. -/
theorem admFull_r1_iff_of_e0_eq_one {D : CensusData} (hr : D.r = 1)
    (he0 : D.e 0 = 1) :
    ADMFull D ↔ ∀ β ∈ D.onLineSlots, r1Bound D β ≤ β :=
  ⟨fun hFull β hβ => (attainDim_eq_d_iff_r1Bound_le hr he0 β).mp
      (hFull.full_attained β hβ),
   fun hB => ⟨fun β hβ => (attainDim_eq_d_iff_r1Bound_le hr he0 β).mpr (hB β hβ)⟩⟩

/-!
## Unit C5 — `censusValueRows_of_anchoredMarch` (CEN-W r ≥ 1): BLOCKED
(statement-level; owner rows, stratum carriers, AND the hypothesis type absent)

**BLOCKED(C5)** (checked at compile, 2026-08-01; probe = the BP_IV
§1.2-VERBATIM `CensusValueRows` structure PLUS this unit's constructor
theorem `censusValueRows_of_anchoredMarch (D : CensusData)
(hproof : AnchoredMarchProof D) : CensusValueRows D` with `sorry` body, over
the import set `Census + ValueSide.CensusCore + ValueSide.Hyps +
DictIII.Hyps`).  FIVE of the statement's types are declared NOWHERE in the
corpus; each fails as a hard "unknown identifier" elaboration error (NOT a
`sorry`-able goal), verbatim shape: "error: Function expected at\n  GRBRow\n
but this term has type\n  ?m.1 … The identifier `GRBRow` is unknown":
 · `GRBRow D` (probe 15:19) / `FreshRow D` (18:30) — owner BP_III (§1.0
   owner table; dep H4).  The LANDED `DictIII.GRB p F` / `DictIII.FRESH p F`
   rows carry a DIFFERENT signature (prime + finite field, NOT
   `CensusData`-indexed); per BP_IV §1.0 ("blocked rather than compiled
   against a weaker signature") + §5 ("BP_IV defines no aliases") no
   prover-side bridge is declared.
 · `StratumR D` (16:11) / `JunctionStratum D` (19:11) — the r ≥ 1 stratum
   carriers appear ONLY inside the §1.2 display itself; no unit-table row
   owns them and no blueprint defines them.
 · `AnchoredMarchProof D` (23:14) — the constructor's OWN hypothesis type:
   its single corpus-wide occurrence is the §1.2 display line; the wave-4
   unit cannot even bind its hypothesis.  Signature fix must come from the
   blueprint owner (BP_IV §4 failure protocol) — escalated to the division
   lead with this compiled obstruction.
Same blockage as the S5b (`SeriesTie.lean`), D4 (`DensityTie.lean`), and C5′
(block below) probes.  Deps at check time: C0/C4c/H1 landed; H4 landed only
under the BP_III `(p, F)` key.  Verifier charge honored: neither the REFUTED
r2-class nor the r3-value (ADM) form appears anywhere in this unit's text.
Nothing weakened, no alias, no `sorry`.

**What IS landed (C5 PROOF KERNEL — statement-fence-safe NEW lemmas, not the
unit):** the counting engine of the §2 C5 proof-sketch clause "(GR-B) digit
read = surjective F_q-linear map on graded piece ⇒ each digit costs q^d"
(O9 rev-5 §5.1: the read is fiber-uniform onto its image; onto F_{q^d} ⟺
FULL attainment).  Counting form: a surjective additive read has all fibers
of one size, card(fiber) · card(target) = card(source) — so at target
F_{q^d} each digit costs exactly q^d.  The wave-4 constructor applies this
once per march step, once the carriers exist.  The E′ strict-left-tail
(floor(line)+1) leg cannot even be STATED faithfully without the `StratumR`
carrier — queued with the unit.
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

/-!
## Unit C5′ — `CensusValueRows.cenJ` (CEN-J): BLOCKED (owner rows absent)

**BLOCKED(C5′)** (checked at compile, 2026-08-01; probe = the §1.2-VERBATIM
`CensusValueRows` structure — the C5 `cenW` shell + this unit's `cenJ` field
— over the import set `Census + ValueSide.CensusCore + ValueSide.Hyps +
DictIII.Hyps`).  The C5′ statement is a STRUCTURE FIELD, so it cannot exist
without the C5-owned shell; the probe elaborated the full §1.2 display and
FOUR of its row/carrier types are declared NOWHERE in the corpus, each an
"unknown identifier" hard error (not a `sorry`-able goal), e.g. verbatim:
"error: Function expected at\n  GRBRow\nbut this term has type\n  ?m.1 …
The identifier `GRBRow` is unknown" — likewise `FreshRow` (probe line for
`cenJ`), `StratumR`, `JunctionStratum`.  Per BP_IV §1.0 ("if an owner has
not landed, that consuming unit is blocked rather than compiled against a
weaker signature") no local alias or placeholder is declared:
 · `GRBRow D` / `FreshRow D` — owner BP_III (§1.0 owner table; FRESH = dep
   H4).  The LANDED `DictIII.GRB p F` / `DictIII.FRESH p F` rows carry a
   DIFFERENT signature (prime + finite field, not `CensusData`); the cenJ
   binder `hFresh : FreshRow D` needs the CensusData-indexed form, which
   does not exist anywhere.
 · `StratumR D` / `JunctionStratum D` — the r ≥ 1 stratum carriers: they
   appear ONLY inside the §1.2 display itself (BP_IV defines them nowhere
   and no unit table row owns them); `JunctionStratum` is the quantifier
   type of `cenJ` itself.
Everything ELSE in the §1.2 display elaborates (probe-verified):
`CensusData`, `ADMFull D`, `censusW D : Polynomial ℕ` with `.eval q`, and
the `{p N : ℕ}, Fact p.Prime → ∀ q : ℕ, q = p ^ N` prime-power binder
block.  Deps ledger at check time: C5 (the shell + `cenW`) NOT landed —
identical blockage; H4 (FRESH) landed BP_III-side under the wrong key.
The S5/D4 consumers already record the same blockage (`SeriesTie.lean`,
unit S5b block).  §3's E-phase note (re-key `CensusValueRows` over the
SlotsG15 `SiteData` carriers) is a STATEMENT change — escalates to the
division lead per the statement fence; nothing is declared here this
campaign, and no `sorry` is added.
-/

end LeanUrat.Scaffold
