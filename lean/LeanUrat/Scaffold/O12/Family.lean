/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Core
import LeanUrat.Scaffold.O12.Bookings
import LeanUrat.MovesU.U0b_splitTypeFintype

/-!
# Scaffold/O12/Family — GramOver, the 𝔅_n row families, Theorem 2 [BP_II units II-R1..R14]

Movement II row-family layer (blueprint `lean/blueprints/BP_II.md` §1.3; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.3, §5).

This file carries **unit II-R1**: the `GramOver` inductive (the grammar 𝒢 with leaves,
mirroring the landed `Gram` of `MovesU/O12PoleFree.lean`) plus the two induction walks
`GramOver.mono` and `Gram.gramOver`. Units II-R2..R14 extend this module.

**Unit II-R4** adds `lowerLegs` (the β-legs available to block e) and the
`BlockPresentation` structure (one block presented for the R-induction; this is the T-8
block structure, consumed as structure only).

**Unit II-R12** adds the concrete-family statement layer: `BnCoordinates`,
`BnCoordinates.Valid`, `BnMember`, `BnMember.booking`, together with the
§1.3-displayed definitions they consume — `massPatt` (definition half of II-R6),
`massPoly` (definition half of II-R7; the blueprint splits II-R7 into definition and
grammar proof), and `AllocDatum` (definition half of II-R9). The `gramOver_*`
theorems of those units land with II-R7/R9.

**Unit II-R5** adds `beta_memRcyc`, Theorem 2's R-induction engine: strong induction
on the block index e, base blocks from `hbase`, step blocks absorbed through
`GramOver.memRcyc` over the lower legs and the ℛ-unit division `hu`.

**Unit II-R6** adds `gram_massPatt` (family (ii) is 𝒢-generated: the (g1)·(g2)·(g2)
product).

**Unit II-R7** adds `gram_massPoly` (family (iii) is 𝒢-generated: a finite sum of
(g3)·(g4) terms times the (JC) shape factor, each a Gram composite).

**Unit II-R11** adds `weightSet` (family (v): the entrance/shape weight list of brief
§2.3(v)) and `gram_weightSet` (all weights 𝒢-generated: (g2) atoms plus the (g4)-shaped
(O3) exit scalings with A = 1).
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- The grammar 𝒢 with LEAVES: generated from a set S by (g1)–(g6) (brief §2.3).
Mirrors the landed `Gram` (O12PoleFree.lean) plus a leaf constructor — the leaves are
the lower blocks' solved entries in Theorem 2's induction. -/
inductive GramOver (S : Set Qq) : Qq → Prop
  | leaf {f : Qq} (h : f ∈ S) : GramOver S f
  | poly (P : Polynomial ℚ) : GramOver S (algebraMap (Polynomial ℚ) Qq P)
  | invS {s : Polynomial ℚ} (hs : s ∈ cycS) : GramOver S (algebraMap (Polynomial ℚ) Qq s)⁻¹
  | add {f g} : GramOver S f → GramOver S g → GramOver S (f + g)
  | mul {f g} : GramOver S f → GramOver S g → GramOver S (f * g)
  | neg {f} : GramOver S f → GramOver S (-f)
  | subst {f} (δ : ℕ+) : GramOver S f → GramOver S (MovesS.powSubst δ f)

/-- Leafless generation is generation over any leaf set: the landed grammar `Gram`
embeds into `GramOver S` constructor-for-constructor (induction walk, unit II-R1). -/
theorem Gram.gramOver {S : Set Qq} {f : Qq} (h : Gram f) : GramOver S f := by
  induction h with
  | poly P => exact GramOver.poly P
  | invS hs => exact GramOver.invS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.subst δ

/-- Monotonicity in the leaf set (induction walk, unit II-R1): enlarging S only
enlarges what 𝒢 generates. -/
theorem GramOver.mono {S T : Set Qq} (hST : S ⊆ T) {f} : GramOver S f → GramOver T f := by
  intro h
  induction h with
  | leaf hf => exact GramOver.leaf (hST hf)
  | poly P => exact GramOver.poly P
  | invS hs => exact GramOver.invS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.subst δ

/-- Theorem 2's absorption step (unit II-R2): if every leaf of S lies in ℛ_cyc, then
everything 𝒢-generated over S lies in ℛ_cyc. Leaf case from `hS`; the remaining cases
are verbatim the landed `Gram.memRcyc` walk (O12PoleFree.lean: L7(i)–(iii) closure). -/
theorem GramOver.memRcyc {S : Set Qq} (hS : ∀ g ∈ S, MemRcyc g) {f : Qq}
    (h : GramOver S f) : MemRcyc f := by
  induction h with
  | leaf hf => exact hS _ hf
  | poly P => exact MovesU.memRcyc_algebraMap P
  | invS hs => exact MovesU.memRcyc_inv_cycS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.powSubst δ

/-- Finite sums of 𝒢-generated elements are 𝒢-generated (unit II-R3; brief §2.3(iv):
the 0/1 aggregated verdict sums). Empty sum is the polynomial 0. -/
theorem GramOver.finsetSum {S} {ι : Type*} (t : Finset ι) (F : ι → Qq)
    (h : ∀ i ∈ t, GramOver S (F i)) : GramOver S (∑ i ∈ t, F i) := by
  refine Finset.sum_induction F (GramOver S) (fun a b ha hb => ha.add hb) ?_ h
  simpa using GramOver.poly (S := S) 0

/-- List products of 𝒢-generated elements are 𝒢-generated (unit II-R3). Empty
product is the polynomial 1. -/
theorem GramOver.listProd {S} (l : List Qq) (h : ∀ f ∈ l, GramOver S f) :
    GramOver S l.prod := by
  induction l with
  | nil => simpa using GramOver.poly (S := S) 1
  | cons a l ih =>
    rw [List.prod_cons]
    exact (h a List.mem_cons_self).mul
      (ih fun f hf => h f (List.mem_cons_of_mem _ hf))

/-- The β-legs available to block e: β_{e′}(σ′) for e′ < e (base changes are `subst`,
so δ needs no indexing here — brief §2.3(vi)). -/
def lowerLegs {n : ℕ} (β : ℕ → MovesU.SplittingType n → Qq) (e : ℕ) : Set Qq :=
  {g | ∃ e' < e, ∃ σ, g = β e' σ}

/-- One block of a 𝔅_n member, presented for the R-induction (brief §2.3(iv)+(vii)):
the aggregated verdict rows t_σ are 𝒢-generated over the lower solved entries, and the
block solves by division by the booking's ℛ-unit denominator. This structure IS the
T-8 block structure consumed "as structure only" (ROOT Step 5 consumes-list). -/
structure BlockPresentation (n : ℕ) (β : ℕ → MovesU.SplittingType n → Qq) (e : ℕ) where
  trow    : MovesU.SplittingType n → Qq
  htrow   : ∀ σ, GramOver (lowerLegs β e) (trow σ)
  u       : Qq
  hu      : u ≠ 0 ∧ MemRcyc u ∧ MemRcyc u⁻¹
  hsolve  : ∀ σ, β e σ = u⁻¹ * trow σ

/-- **Theorem 2's R-induction engine**: base blocks in ℛ + every block presented over
its lower legs ⟹ every solved entry lies in ℛ. Strong induction on e. [BP_II unit
II-R5; brief §5 Thm2 proof, (vii)] At e ≤ 1 `hbase` fires; at 2 ≤ e the block's rows
are 𝒢-generated over the lower legs — all in ℛ by the induction hypothesis, absorbed
by `GramOver.memRcyc` — and β e σ = u⁻¹·t_σ lands in ℛ since u⁻¹ ∈ ℛ (`hu`). -/
theorem beta_memRcyc {n : ℕ} {β : ℕ → MovesU.SplittingType n → Qq}
    (hbase : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ))
    (hstep : ∀ e, 2 ≤ e → BlockPresentation n β e) :
    ∀ e σ, MemRcyc (β e σ) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro σ
    rcases Nat.lt_or_ge e 2 with he | he
    · exact hbase e (Nat.lt_succ_iff.mp he) σ
    · have B := hstep e he
      have ht : MemRcyc (B.trow σ) := by
        refine GramOver.memRcyc ?_ (B.htrow σ)
        rintro g ⟨e', he', σ', rfl⟩
        exact ih e' he' σ'
      rw [B.hsolve σ]
      exact B.hu.2.2.mul ht

/-- Family (ii): divisor-pattern mass m(π) = q^{−(E−e)}·N_π(q)·q^{−e}.
(Definition half of unit II-R6.) -/
noncomputable def massPatt (e : ℕ) (Nπ : Polynomial ℚ) : Qq :=
  (qX ^ (blockE e - e))⁻¹ * algebraMap (Polynomial ℚ) Qq Nπ * (qX ^ e)⁻¹

/-- The divisor-pattern mass is 𝒢-generated (unit II-R6, brief §2.3(ii)): the
(g1)·(g2)·(g2) product — `q^{−(E−e)}` and `q^{−e}` are `Gram.invS` atoms via
`Xpow_mem_cycS`, and `N_π` is a `Gram.poly` atom. -/
theorem gram_massPatt (e : ℕ) (Nπ : Polynomial ℚ) : Gram (massPatt e Nπ) := by
  rw [massPatt, qX_pow_eq_algebraMap (blockE e - e), qX_pow_eq_algebraMap e]
  exact ((Gram.invS (LeanUrat.MovesU.Xpow_mem_cycS _)).mul (Gram.poly Nπ)).mul
    (Gram.invS (LeanUrat.MovesU.Xpow_mem_cycS _))

/-- Family (iii): polygon-family mass m(κ, ρ⃗) — a finite sum over L6b(ii)'s
enumeration of (g3)-volumes times (g4)-closures (exponents c_j ≥ 1, from
`PolygonData`), times the (JC) shape factor ∏ P_{ρ_j}(q)·(q^{d_j}−q^{d_j−1})⁻¹. The
DEFINITION takes the enumeration data as finite lists; L6′ (unit II-M11) ties it to
the polygon cells. (Definition half of unit II-R7; `gram_massPoly` lands with II-R7.) -/
noncomputable def massPoly (e : ℕ) (enum : Finset (ℕ × ℕ))
    (cs : List ℕ+) (shape : List (Polynomial ℚ × ℕ+)) : Qq :=
  (∑ z ∈ enum, (qX ^ z.2)⁻¹) *
  (cs.map (fun c => (1 - (qX ^ (c : ℕ))⁻¹)⁻¹)).prod *
  (shape.map (fun z =>
    algebraMap (Polynomial ℚ) Qq z.1 *
      (qX ^ (z.2 : ℕ) - qX ^ ((z.2 : ℕ) - 1))⁻¹)).prod

/-- The polygon-family mass is 𝒢-generated (unit II-R7, brief §2.3(iii)): a finite
sum of (g3)-volume atoms `q^{−h}` (each a `Gram.invS` atom via `Xpow_mem_cycS`),
times the (g4)-closures `(1 − q^{−c})⁻¹ = (q^c − 1)⁻¹·q^c` (c ≥ 1 from `ℕ+`, so
`X^c − 1 ∈ 𝒮`), times the (JC) shape factor `P_ρ(q)·(q^d − q^{d−1})⁻¹` with
`q^d − q^{d−1} = q^{d−1}(q − 1) ∈ 𝒮` (d ≥ 1 from `ℕ+`) — each a Gram composite. -/
theorem gram_massPoly (e : ℕ) (enum : Finset (ℕ × ℕ))
    (cs : List ℕ+) (shape : List (Polynomial ℚ × ℕ+)) :
    Gram (massPoly e enum cs shape) := by
  rw [massPoly]
  refine Gram.mul (Gram.mul ?_ ?_) ?_
  · -- (g3) volumes: ∑_h q^{−h}, termwise `invS`
    refine Finset.sum_induction _ Gram (fun a b ha hb => ha.add hb)
      (by simpa using Gram.poly 0) fun z _ => ?_
    rw [qX_pow_eq_algebraMap]
    exact Gram.invS (MovesU.Xpow_mem_cycS z.2)
  · -- (g4) closures: ∏_j (1 − q^{−c_j})⁻¹ = ∏_j (q^{c_j} − 1)⁻¹·q^{c_j}
    refine List.prod_induction Gram (fun a b ha hb => ha.mul hb)
      (by simpa using Gram.poly 1) fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have hcpos : 1 ≤ c := by
      obtain ⟨a, -, rfl⟩ : ∃ a : ℕ+, a ∈ cs ∧ c = (a : ℕ) := by simpa using hc
      exact a.pos
    show Gram (1 - (qX ^ (c : ℕ))⁻¹)⁻¹
    have h1 : (1 : Qq) - (qX ^ (c : ℕ))⁻¹
        = (qX ^ (c : ℕ) - 1) * (qX ^ (c : ℕ))⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ (qX_pow_ne_zero _), one_mul]
    have h2 : qX ^ (c : ℕ) - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ (c : ℕ) - 1) := by
      rw [map_sub, map_one, qX_pow_eq_algebraMap]
    rw [h1, mul_inv, inv_inv, h2, qX_pow_eq_algebraMap]
    exact (Gram.invS (MovesU.Xpow_sub_one_mem_cycS hcpos)).mul (Gram.poly _)
  · -- (JC) shape factor: ∏_j P_{ρ_j}(q)·(q^{d_j} − q^{d_j−1})⁻¹
    refine List.prod_induction Gram (fun a b ha hb => ha.mul hb)
      (by simpa using Gram.poly 1) fun x hx => ?_
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx
    show Gram (algebraMap (Polynomial ℚ) Qq z.1 *
      (qX ^ (z.2 : ℕ) - qX ^ ((z.2 : ℕ) - 1))⁻¹)
    obtain ⟨d', hd⟩ : ∃ d', (z.2 : ℕ) = d' + 1 :=
      ⟨(z.2 : ℕ) - 1, (Nat.succ_pred_eq_of_pos z.2.pos).symm⟩
    have hmem : (Polynomial.X ^ (d' + 1) - Polynomial.X ^ d' : Polynomial ℚ) ∈ cycS := by
      have hX1 : (Polynomial.X - 1 : Polynomial ℚ) ∈ cycS := by
        simpa using MovesU.Xpow_sub_one_mem_cycS le_rfl
      have hfac : (Polynomial.X ^ (d' + 1) - Polynomial.X ^ d' : Polynomial ℚ)
          = Polynomial.X ^ d' * (Polynomial.X - 1) := by ring
      rw [hfac]
      exact mul_mem (MovesU.Xpow_mem_cycS d') hX1
    have heq : qX ^ (d' + 1) - qX ^ (d' + 1 - 1)
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ (d' + 1) - Polynomial.X ^ d') := by
      rw [map_sub, Nat.add_sub_cancel, qX_pow_eq_algebraMap, qX_pow_eq_algebraMap]
    rw [hd, heq]
    exact (Gram.poly z.1).mul (Gram.invS hmem)

open scoped Classical in
/-- Family (iv): the verdict row of a family F with hand-off list H(F) and composition
datum comp — a 0/1-coefficient finite sum of products of m(F) with base-changed lower
β-legs (brief §2.3(iv) display). μ < e per L4 (units II-B12/II-P8 supply the bound).
[BP_II unit II-R8] -/
noncomputable def rowOf {n : ℕ} (β : ℕ → MovesU.SplittingType n → Qq)
    (m : Qq) (H : List (ℕ × ℕ+))
    (comp : (∀ i : Fin H.length, MovesU.SplittingType n) → MovesU.SplittingType n)
    (σ : MovesU.SplittingType n) : Qq :=
  ∑ τ ∈ Finset.univ.filter (fun τ => comp τ = σ),
    m * ∏ i, MovesS.powSubst (H.get i).2 (β (H.get i).1 (τ i))

/-- The verdict row is 𝒢-generated over the lower legs (unit II-R8; brief §2.3(iv)):
outer sum by `finsetSum` (II-R3), each summand `m · ∏ᵢ powSubst δᵢ (β μᵢ τᵢ)` by
`.mul` of the leafless mass (`Gram.gramOver`) with a product of `subst`-wrapped
`leaf`s — each leg `β μᵢ τᵢ` lands in `lowerLegs β e` since `hH` gives μᵢ < e. -/
theorem gramOver_rowOf {n : ℕ} {β : ℕ → MovesU.SplittingType n → Qq} {e : ℕ}
    {m : Qq} (hm : Gram m) (H : List (ℕ × ℕ+)) (hH : ∀ x ∈ H, x.1 < e)
    (comp : (∀ i : Fin H.length, MovesU.SplittingType n) → MovesU.SplittingType n)
    (σ : MovesU.SplittingType n) :
    GramOver (lowerLegs β e) (rowOf β m H comp σ) := by
  refine GramOver.finsetSum _ _ fun τ _ => (Gram.gramOver hm).mul ?_
  refine Finset.prod_induction _ (GramOver (lowerLegs β e))
    (fun a b ha hb => ha.mul hb)
    (by simpa using GramOver.poly (S := lowerLegs β e) 1) fun i _ => ?_
  exact GramOver.subst _
    (GramOver.leaf ⟨(H.get i).1, hH _ (H.get_mem i), τ i, rfl⟩)

/-- Family (iv), (O2) allocation adjustment datum: an allocation α : verdicts → ℚ[q]
with the mass identity Σ_σ α(σ) = q−1 as the value-side datum (Theorem 2 needs only
α(σ) ∈ ℚ[q]). (Definition half of unit II-R9; `gramOver_allocAdjust` lands with
II-R9.) -/
def AllocDatum (n : ℕ) : Type :=
  {α : MovesU.SplittingType n → Polynomial ℚ //
    ∑ σ, α σ = Polynomial.X - 1}   -- Σ_σ α_e(σ) = q − 1 (brief §2.3(iv))

/-- Family (iv), (O2) allocation adjustment (unit II-R9; brief §2.3(iv) O2 row, rev-4
repair V13-1): for EVERY α ∈ ℚ[q] the adjusted row t + α·q^{−E} stays 𝒢-generated —
quantified over all polynomials α, so robust to allocation-datum display changes (§5).
Witness: `.add` of `h` with `.mul (poly α) (invS (q^E ∈ 𝒮))`. -/
theorem gramOver_allocAdjust {n : ℕ} {β : ℕ → MovesU.SplittingType n → Qq} {e : ℕ}
    {S : Set Qq} {t : Qq} (h : GramOver S t) (α : Polynomial ℚ) :
    GramOver S (t + algebraMap (Polynomial ℚ) Qq α * (qX ^ blockE e)⁻¹) := by
  refine h.add ((GramOver.poly α).mul ?_)
  rw [qX, ← map_pow]
  exact GramOver.invS (MovesU.Xpow_mem_cycS (blockE e))

/-- Family (iv)/(v), (O3) exit scaling q^E/(q^E − 1) = Σ_{L≥0} κ₀^L (closed form).
[BP_II unit II-R10] The scaling factor is `.mul`-absorbed: `q^E` is a `poly` atom and
`(q^E − 1)⁻¹` is an `invS` atom via `Xpow_sub_one_mem_cycS` (the (g4) shape) once
`blockE e ≥ 1`; the degenerate `blockE e = 0` corner collapses the whole term to the
`poly` atom 0. -/
theorem gramOver_o3scale {e : ℕ} {S : Set Qq} {t : Qq} (h : GramOver S t) :
    GramOver S ((qX ^ blockE e) * (qX ^ blockE e - 1)⁻¹ * t) := by
  rcases Nat.eq_zero_or_pos (blockE e) with hE | hE
  · -- degenerate corner: q^0 − 1 = 0, so the scalar is 1 * 0⁻¹ = 0
    have hz : (qX ^ blockE e) * (qX ^ blockE e - 1)⁻¹ * t
        = algebraMap (Polynomial ℚ) Qq 0 := by
      rw [hE]; simp
    rw [hz]
    exact GramOver.poly 0
  · -- (g4) shape: q^E is `poly`, (q^E − 1)⁻¹ is `invS` (X^E − 1 ∈ 𝒮 since E ≥ 1)
    have h1 : qX ^ blockE e - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      rw [map_sub, map_one, qX_pow_eq_algebraMap]
    rw [h1, qX_pow_eq_algebraMap]
    exact ((GramOver.poly _).mul
      (GramOver.invS (LeanUrat.MovesU.Xpow_sub_one_mem_cycS hE))).mul h

open scoped Classical in
/-- Family (v): the entrance/shape weight list (brief §2.3(v)), all Gram.
Concretely (brief §2.3(v) display): `{q^{−b} : 0 ≤ b ≤ E_n}` ∪
`{(q^d − q^{d−1})⁻¹ : 1 ≤ d ≤ n}` ∪ `{(q−1)/(q^{n+1}−1)}` ∪
`{q^{E_m}/(q^{E_m}−1) : 2 ≤ m ≤ n}` (the last are the (O3) exit-row scalings
Σ_{L≥0} κ₀^L, (g4) with A = 1). [BP_II unit II-R11] -/
noncomputable def weightSet (n : ℕ) : Finset Qq :=
  ((Finset.range (blockE n + 1)).image fun b => (qX ^ b)⁻¹) ∪
    ((Finset.Icc 1 n).image fun d => (qX ^ d - qX ^ (d - 1))⁻¹) ∪
    {(qX - 1) * (qX ^ (n + 1) - 1)⁻¹} ∪
    ((Finset.Icc 2 n).image fun m => qX ^ blockE m * (qX ^ blockE m - 1)⁻¹)

/-- Every entrance/shape weight is 𝒢-generated: the first two families are (g2)
`Gram.invS` atoms (`q^b ∈ 𝒮`; `q^d − q^{d−1} = q^{d−1}(q−1) ∈ 𝒮`), the last two are
`Gram.poly · Gram.invS` products with `q^c − 1 ∈ 𝒮`. [BP_II unit II-R11] -/
theorem gram_weightSet {n g} (hg : g ∈ weightSet n) : Gram g := by
  have hsub : ∀ c : ℕ,
      qX ^ c - 1 = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ c - 1) := by
    intro c
    rw [map_sub, map_one, qX_pow_eq_algebraMap]
  simp only [weightSet, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
    Finset.mem_range, Finset.mem_Icc] at hg
  rcases hg with ((⟨b, _, rfl⟩ | ⟨d, ⟨hd1, _⟩, rfl⟩) | rfl) | ⟨m, ⟨hm2, _⟩, rfl⟩
  · -- (g2): q^{−b}
    rw [qX_pow_eq_algebraMap]
    exact Gram.invS (MovesU.Xpow_mem_cycS b)
  · -- (g2): (q^d − q^{d−1})⁻¹, via q^d − q^{d−1} = q^{d−1}·(q − 1) ∈ 𝒮
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos hd1).symm⟩
    have hmem : (Polynomial.X ^ (d' + 1) - Polynomial.X ^ d' : Polynomial ℚ) ∈ cycS := by
      have hX1 : (Polynomial.X - 1 : Polynomial ℚ) ∈ cycS := by
        simpa using MovesU.Xpow_sub_one_mem_cycS le_rfl
      have hfac : (Polynomial.X ^ (d' + 1) - Polynomial.X ^ d' : Polynomial ℚ)
          = Polynomial.X ^ d' * (Polynomial.X - 1) := by ring
      rw [hfac]
      exact mul_mem (MovesU.Xpow_mem_cycS d') hX1
    have heq : qX ^ (d' + 1) - qX ^ (d' + 1 - 1)
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ (d' + 1) - Polynomial.X ^ d') := by
      rw [map_sub, Nat.add_sub_cancel, qX_pow_eq_algebraMap, qX_pow_eq_algebraMap]
    rw [heq]
    exact Gram.invS hmem
  · -- (g2)·(g2): (q−1)·(q^{n+1}−1)⁻¹
    have h1 : qX - 1 = algebraMap (Polynomial ℚ) Qq (Polynomial.X - 1) := by
      rw [map_sub, map_one, qX]
    rw [h1, hsub (n + 1)]
    exact Gram.mul (Gram.poly _)
      (Gram.invS (MovesU.Xpow_sub_one_mem_cycS (Nat.succ_le_succ (Nat.zero_le n))))
  · -- (g4) with A = 1: q^{E_m}·(q^{E_m}−1)⁻¹
    have hE : 1 ≤ blockE m := le_trans (by norm_num) (blockE_ge_three hm2)
    rw [hsub (blockE m), qX_pow_eq_algebraMap]
    exact Gram.mul (Gram.poly _)
      (Gram.invS (MovesU.Xpow_sub_one_mem_cycS hE))

/-- Raw §2.3 member coordinates: divisor masses, polygon masses, composition maps,
allocation data, weights, transitions, and the recursively specified rows.

**Honest scope (unit II-R12, from the blueprint's binding §1 scope declaration):**
the Movement II claim is about zeros/poles of the §2-defined family 𝔅_n; VALUE
correctness is OUTSIDE this movement (D-11/O-11, Movements IV–V). The composition
and allocation data below are MEMBER COORDINATES — data carried by the presented
family member, not conclusions or hypotheses about the project's realized tables.
The identification of realized tables with 𝔅_n is the named hypothesis row
`InstancePin` ((B-INST), §1.10), never an axiom. -/
structure BnCoordinates (n : ℕ) where
  system       : BookingSystem n
  pattData     : ℕ → Finset (Polynomial ℚ)
  polygonData  : ℕ → Finset (Finset (ℕ × ℕ) × List ℕ+ ×
    List (Polynomial ℚ × ℕ+))
  handoffs     : ℕ → List (ℕ × ℕ+)
  composition  : ∀ e, (∀ i : Fin (handoffs e).length,
    MovesU.SplittingType n) → MovesU.SplittingType n
  allocation   : ℕ → AllocDatum n
  weights      : ℕ → Finset Qq
  entries      : ℕ → Finset Qq

open scoped Classical in
/-- Intrinsic membership conditions for the concrete coordinates. These are
equations and support conditions defining §2.3 membership, not conclusions of
Theorem 2. The e = 1 corner is established from the concrete transition support and
hand-off descent carried here (via `BookingSystem`), not inferred merely from a
guarded kernel definition. -/
structure BnCoordinates.Valid {n : ℕ} (C : BnCoordinates n) : Prop where
  weight_gram : ∀ e g, g ∈ C.weights e → Gram g
  handoff_step :
    ∀ e x, x ∈ C.handoffs e →
      ∃ σ σ', C.system.step e σ x.1 σ'
  entries_eq :
    ∀ e, C.entries e =
      (C.weights e ∪
        (C.pattData e).image (massPatt e) ∪
        (C.polygonData e).image
          (fun z => massPoly e z.1 z.2.1 z.2.2))

/-- A proved presentation produced from the concrete coordinates.

**Honest scope (unit II-R12, from the blueprint's binding §1 scope declaration):**
T-8's block structure and T-3/T-6's event structure enter "as structure only" —
they are this structure's DATA (`blocks`, `coords.system`), not hypotheses about
realized tables. The composition/allocation data are member coordinates carried by
`coords`. The Movement II claim scoped by this structure is about zeros/poles of
the family 𝔅_n; VALUE correctness is outside (Movements IV–V), and realized-table
claims stay conditional on the named hypothesis row `InstancePin` ((B-INST)). -/
structure BnMember (n : ℕ) where
  coords   : BnCoordinates n
  valid    : coords.Valid
  β        : ℕ → MovesU.SplittingType n → Qq
  hbase    : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ)
  blocks   : ∀ e, 2 ≤ e → BlockPresentation n β e
  hblockU  : ∀ e (he : 2 ≤ e),
    (blocks e he).u = coords.system.booking.solveU e
  entries  : ℕ → Finset Qq
  entries_eq : entries = coords.entries
  hentries : ∀ e, ∀ g ∈ entries e,
    GramOver {f | ∃ e' ≤ e, ∃ σ, f = β e' σ} g

abbrev BnMember.booking {n : ℕ} (T : BnMember n) : Booking :=
  T.coords.system.booking

/-- **THEOREM 2 (master denominator theorem)**: for concrete §2.3 coordinates
`C` satisfying the intrinsic membership predicate `C.Valid`, apply
`bnMember_of_coordinates C hC`; every generated entry and solved leg lies in ℛ.
The following closure form is the induction lemma consumed by that theorem.
[BP_II unit II-R13; brief §5 Thm2] Proof: II-R5 (`beta_memRcyc`, fired from
`T.hbase` + `T.blocks`) puts every solved leg β_{e′}(σ) in ℛ_cyc; `T.hentries`
presents each entry as 𝒢-generated over those legs, and `GramOver.memRcyc`
(II-R2) absorbs the generation walk. -/
theorem BnMember.entries_memRcyc {n : ℕ} (T : BnMember n) :
    ∀ e, ∀ g ∈ T.entries e, MemRcyc g := by
  intro e g hg
  refine GramOver.memRcyc ?_ (T.hentries e g hg)
  rintro f ⟨e', -, σ, rfl⟩
  exact beta_memRcyc T.hbase T.blocks e' σ

/-- Every solved leg stays in ℛ_cyc at every substitution depth δ ≥ 1 (brief
§2.3(vi): the depth-δ legs are x ↦ x^δ substitutions of the depth-1 solve).
[BP_II unit II-R14] Proof: II-R5 (`beta_memRcyc`, fired from `T.hbase` +
`T.blocks`) puts β_e(σ) in ℛ_cyc; `MemRcyc.powSubst` (ℛ_cyc is closed under
x ↦ x^δ, since cyclotomic-supported denominators expand to cyclotomic-supported
denominators) transports it to depth δ. -/
theorem BnMember.beta_leg_memRcyc {n : ℕ} (T : BnMember n) (e : ℕ)
    (σ : MovesU.SplittingType n) (δ : ℕ+) : MemRcyc (MovesS.powSubst δ (T.β e σ)) :=
  (beta_memRcyc T.hbase T.blocks e σ).powSubst δ

end LeanUrat.Scaffold
