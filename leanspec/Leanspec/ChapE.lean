import Uniformity

/-!
# Chapter E — THE σ-LADDER: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-E_sigma_ladder.md` (68 nodes E.01–E.68), landed in the
isolated `leanspec` environment **before** the chapter-E fleet fires, in the blueprint's node
order.

**WORK IN PROGRESS — this header is completed by the stub gate's closing pass.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace LeanspecE

open Finset

-- The three universes E.12's `RungInterface` carries: `uO` (the bundle), `uK` (the label
-- field) and `uW` — the `(SEC-RANK)` carrier's universe, which every declaration that
-- QUANTIFIES over a `RungInterface` must bind explicitly (defect E-D6: the signed
-- E.39/E.40/E.24 signatures leave it an uninferable universe metavariable).
universe uO uK uW

/-! ## §3 — THE RUNG/LADDER SCHEMA (E.01–E.09) -/

/-- **E.01** [def] A **rung datum**: the arithmetic core of one σ-ladder level
(`EFF.HE7.47`/`.107`). -/
structure RungDatum where
  ℓ : ℕ
  g : ℕ
  u : ℕ
  T : ℕ
  hℓ : 1 ≤ ℓ
  hg : 1 ≤ g
  hcop : Nat.Coprime u ℓ
  hnode : ℓ * T < u

/-- **E.02** [def] `L = ℓg`, the number of slots the rung's key-development occupies. -/
def RungDatum.slotCount (R : RungDatum) : ℕ := R.ℓ * R.g

/-- **E.02** [def] `T' = L·u`, the next level's disk threshold (`EFF.HE7.47`). -/
def RungDatum.nextT (R : RungDatum) : ℕ := R.slotCount * R.u

/-- **E.02** [def] One step of the (LIFT) threshold recursion (`EFF.HE7.23`). -/
def RungDatum.nextBound (R : RungDatum) (b : ℕ) : ℕ :=
  (R.slotCount - 1) * R.u + R.ℓ * b

/-- **E.03** [lemma] The normalizer exponents exist and are unique (Bézout at the rung). -/
axiom normExp_exists_unique (R : RungDatum) (k : ℤ) :
    ∃! p : ℤ × ℕ, p.2 < R.ℓ ∧ (R.ℓ : ℤ) * p.1 + (p.2 : ℤ) * (R.u : ℤ) = k

/-- **E.03** [def] The slot exponent `s(k)`. -/
noncomputable def RungDatum.sExp (R : RungDatum) (k : ℤ) : ℕ :=
  (normExp_exists_unique R k).choose.2

/-- **E.03** [def] The carry exponent `m(k)`. -/
noncomputable def RungDatum.mExp (R : RungDatum) (k : ℤ) : ℤ :=
  (normExp_exists_unique R k).choose.1

/-- **E.04** [lemma] The cocycle exponent is `0` or `ℓ`. -/
axiom cocycle_exp_mem (R : RungDatum) (a b : ℤ)
    (sa sb sab : ℕ) (ma mb mab : ℤ)
    (ha : sa < R.ℓ ∧ (R.ℓ : ℤ) * ma + sa * R.u = a)
    (hb : sb < R.ℓ ∧ (R.ℓ : ℤ) * mb + sb * R.u = b)
    (hab : sab < R.ℓ ∧ (R.ℓ : ℤ) * mab + sab * R.u = a + b) :
    (sa + sb - sab : ℤ) = 0 ∨ (sa + sb - sab : ℤ) = R.ℓ

/-- **E.04** [lemma] The carry identity. -/
axiom cocycle_carry (R : RungDatum) {a b : ℤ} {sa sb sab : ℕ} {ma mb mab : ℤ}
    (ha : sa < R.ℓ ∧ (R.ℓ : ℤ) * ma + sa * R.u = a)
    (hb : sb < R.ℓ ∧ (R.ℓ : ℤ) * mb + sb * R.u = b)
    (hab : sab < R.ℓ ∧ (R.ℓ : ℤ) * mab + sab * R.u = a + b)
    {c : ℤ} (hc : (sa + sb - sab : ℤ) = c * R.ℓ) :
    ma + mb = mab - c * R.u

/-- **E.05** [def] The threshold chain: rung `r'` follows `r` when `r'.T = r.nextT`. -/
def rungFollows (r r' : RungDatum) : Prop := r'.T = r.nextT

/-- **E.05** [def] A **ladder**: base rung (threshold 0) + chained higher rungs. -/
structure LadderData where
  base : RungDatum
  rungs : List RungDatum
  hbase : base.T = 0
  hchain : List.Chain rungFollows base rungs

/-- **E.05** [def] The key degree at level `i+1` (`D₀` the seed; `D_{i+1} = D_i·L_i`). -/
def LadderData.degAt (Λ : LadderData) (D₀ : ℕ) : ℕ → ℕ
  | 0 => D₀ * Λ.base.slotCount
  | (i + 1) => Λ.degAt D₀ i * ((Λ.rungs[i]?).map RungDatum.slotCount |>.getD 1)

/-- **E.05** [def] The (LIFT) threshold at level `i+1` (`EFF.HE7.23`). -/
def LadderData.boundAt (Λ : LadderData) : ℕ → ℕ
  | 0 => Λ.base.nextBound 0
  | (i + 1) => ((Λ.rungs[i]?).getD Λ.base).nextBound (Λ.boundAt i)

/-- **E.06** [lemma] Ladder telescoping (degree conservation along levels). -/
axiom LadderData.degAt_eq_prod (Λ : LadderData) (D₀ : ℕ) (i : ℕ)
    (hi : i ≤ Λ.rungs.length) :
    Λ.degAt D₀ i = D₀ * ((Λ.base :: Λ.rungs.take i).map RungDatum.slotCount).prod

/-- **E.07** [lemma] (i) the jump floor. -/
axiom jump_floor {m p : ℕ} (hm : 2 ≤ m) (hp : 2 ≤ p) : 4 ≤ m * p

/-- **E.07** [lemma] (ii) the halving. -/
axiom jump_halving {μ μ₂ p : ℕ} (hp : 2 ≤ p) (h : μ₂ * p ≤ μ) : 2 * μ₂ ≤ μ

/-- **E.07** [lemma] (iii) the jump count. -/
axiom jump_count_bound (μ : ℕ → ℕ) (J : ℕ)
    (h4 : ∀ i ≤ J, 4 ≤ μ i) (hh : ∀ i < J, 2 * μ (i + 1) ≤ μ i) :
    2 ^ (J + 1) ≤ μ 0

/-- **E.08** [lemma] The lift-threshold implication `(‡) ⟹ (†)` at a rung. -/
axiom lift_threshold_step (R : RungDatum) {b k m₀ s₀ : ℕ}
    (hs : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hcrit : (R.slotCount - 1) * R.u + R.ℓ * b ≤ k) :
    (R.g - 1) * R.u + b ≤ m₀

/-- **E.09** [lemma] The use-site margin. -/
axiom useSite_margin (R : RungDatum) {k m₀ s₀ t : ℕ}
    (hs : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (huse : R.nextT < k) (ht : t < R.g) :
    R.ℓ * (m₀ - t * R.u) > R.u ∧ m₀ - t * R.u > R.T

/-! ## §4 — THE MASTER HE7.A SUITE (E.10–E.24; E.24 is placed after §9, see there) -/

/-- **E.10** [def] A **σ-ladder slot carrier** (T2 S1.2–S1.4, `EFF.T2.04`–`.10`): the
ξ-independent height/digit data with the ultrametric, lift, and additivity laws as fields. -/
structure SlotCarrier (O : Type*) [CommRing O] (K : Type*) [Field K] where
  /-- The current key degree `D > 0`. -/
  D : ℕ
  hD : 0 < D
  /-- Carrier invariants with `(DEG-EF)`: `D = e_𝒞 f_𝒞` (a hypothesis, never inferred). -/
  eC : ℕ
  fC : ℕ
  hef : D = eC * fC
  heC : 1 ≤ eC
  hfC : 1 ≤ fC
  /-- `h(A)`: the exact slot height (`SLOT-V`'s ξ-independent value); `h(0) = ⊤`. -/
  hgt : Polynomial O → WithTop ℤ
  /-- `dig(A)`: the exact slot digit (`SLOT-R`'s ξ-independent value); `dig 0 = 0`. -/
  dig : Polynomial O → K
  hgt_zero : hgt 0 = ⊤
  dig_zero : dig 0 = 0
  /-- nonzero sub-`D` polynomials have finite height and nonzero digit (`EFF.T2.05`). -/
  hgt_ne_top : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < D → hgt A ≠ ⊤
  dig_ne_zero : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < D → dig A ≠ 0
  /-- the ultrametric laws (`EFF.T2.04`, r12's valuation disclosure). -/
  hgt_add_ge : ∀ A B, min (hgt A) (hgt B) ≤ hgt (A + B)
  hgt_add_eq : ∀ A B, hgt A ≠ hgt B → hgt (A + B) = min (hgt A) (hgt B)
  /-- digit additivity at a shared height (`EFF.HE7.96`(c)'s mechanism). -/
  dig_add : ∀ A B : Polynomial O, ∀ k : ℤ,
      hgt A = (k : WithTop ℤ) → hgt B = (k : WithTop ℤ) → dig A + dig B ≠ 0 →
      hgt (A + B) = (k : WithTop ℤ) ∧ dig (A + B) = dig A + dig B
  /-- the full heights (`OCC`'s finite-domain obligation is the instances'). -/
  Full : ℤ → Prop
  /-- `(LIFT)`: at a full height every nonzero digit is realised (`EFF.T2.09`). -/
  hlift : ∀ k : ℤ, Full k → ∀ c : K, c ≠ 0 →
      ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < D ∧
        hgt A = (k : WithTop ℤ) ∧ dig A = c

/-- **E.11** [def] The cleared support value of a ladder development (D-1's shape on abstract
heights): `inf over j ≤ μ of (ℓ·hgt j + j·u)`. -/
noncomputable def ladderSuppVal (hgt : ℕ → WithTop ℤ) (u ℓ μ : ℕ) : WithTop ℤ :=
  (Finset.range (μ + 1)).inf fun j => ℓ • hgt j + ((j * u : ℕ) : WithTop ℤ)

/-- **E.11** [def] Abscissa `j` lies on the `(u, ℓ)`-side of the ladder polygon. -/
def onLadderSide (hgt : ℕ → WithTop ℤ) (u ℓ μ : ℕ) (j : ℕ) : Prop :=
  j ≤ μ ∧ ℓ • hgt j + ((j * u : ℕ) : WithTop ℤ) = ladderSuppVal hgt u ℓ μ

/-- **E.11** [def] A **σ-block** over a slot carrier (T2 S1.5–S1.6). -/
structure BlockData {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) where
  Φ : Polynomial O
  F : Polynomial O
  μ : ℕ
  hμ : 1 ≤ μ
  hΦ : Φ.Monic
  hΦdeg : Φ.natDegree = C.D
  /-- the development coefficients; `A j = 0` for `j ≥ μ` by convention. -/
  A : ℕ → Polynomial O
  hdev : F = Φ ^ μ + ∑ j ∈ Finset.range μ, A j * Φ ^ j          -- (DEV)
  hdegA : ∀ j < μ, (A j).natDegree < C.D
  /-- `(KEY-FREE)`, in its two consumed shadows. -/
  hkeyfree : IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Φ.map (algebraMap O (FractionRing O)))
  hA0 : A 0 ≠ 0
  /-- the inherited threshold. -/
  T : ℕ

/-- **E.11** [def] The block's development heights. -/
noncomputable def BlockData.devHgt {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} (B : BlockData C) : ℕ → WithTop ℤ :=
  fun j => if j = B.μ then (0 : WithTop ℤ) else if j < B.μ then C.hgt (B.A j) else ⊤

/-- **E.12** [def] The **rung interface**: T2's carrier hypothesis suite as fields
(`EFF.T2.39`'s five quantitative families + the side/residual numerical shadow). -/
structure RungInterface {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) where
  sides : Finset (ℕ × ℕ)
  hside_cop : ∀ p ∈ sides, Nat.Coprime p.1 p.2 ∧ 1 ≤ p.2
  hside_node : ∀ p ∈ sides, p.2 * B.T < p.1                     -- λ > T (clause 1 half)
  len : ℕ × ℕ → ℕ
  hlen_pos : ∀ p ∈ sides, 1 ≤ len p
  hlen_sum : ∑ p ∈ sides, len p = B.μ                           -- (HULL-LENGTH)
  linFac : ℕ × ℕ → Multiset (K × ℕ)                             -- (root s, mult m)
  hiFac : ℕ × ℕ → Multiset (ℕ × ℕ)                              -- (deg ≥ 2 …, mult)
  hresdeg : ∀ p ∈ sides,                                        -- (RES-DEG)
      p.2 * (Multiset.sum ((linFac p).map Prod.snd)
        + Multiset.sum ((hiFac p).map fun q => q.1 * q.2)) = len p
  rootCount : ℕ × ℕ → ℕ
  haccount : ∀ p ∈ sides, rootCount p = C.D * len p             -- (SIDE-COUNT) form
  classCount : ℕ × ℕ → K × ℕ → ℕ                                -- per linear factor
  classCountHi : ℕ × ℕ → ℕ × ℕ → ℕ                              -- per higher factor
  hnonempty : ∀ p ∈ sides, (∀ q ∈ linFac p, 1 ≤ classCount p q) ∧
      (∀ q ∈ hiFac p, 1 ≤ classCountHi p q)                     -- nonemptiness
  hforce : ∀ p ∈ sides, (∀ q ∈ linFac p, C.D * p.2 ≤ classCount p q) ∧
      (∀ q ∈ hiFac p, C.D * p.2 * q.1 ≤ classCountHi p q)       -- local forcing
  hexhaust : ∀ p ∈ sides,                                       -- exhaustion
      Multiset.sum ((linFac p).map (classCount p))
        + Multiset.sum ((hiFac p).map (classCountHi p)) = rootCount p
  /-- root-preserving continuation: the `(SEC-RANK)` carrier (`EFF.T2.26`). -/
  W : Type*
  wf : WellFoundedRelation W
  σRank : W                                                     -- the state's rank

/-- **E.13** [lemma] Degree bookkeeping of the block, clause (i). -/
axiom BlockData.natDegree_F {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K]
    {C : SlotCarrier O K} (B : BlockData C) : B.F.natDegree = B.μ * C.D ∧ B.F.Monic

/-- **E.13** [lemma] Degree bookkeeping of the block, clause (iii). -/
axiom BlockData.suppVal_ne_top {O : Type*} [CommRing O] [IsDomain O] {K : Type*}
    [Field K] {C : SlotCarrier O K} (B : BlockData C) (u ℓ : ℕ) :
    ladderSuppVal B.devHgt u ℓ B.μ ≠ ⊤

/-- **E.14** [def] A side is **separable** in the numerical shadow. -/
def RungInterface.SepSide {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B) (p : ℕ × ℕ) : Prop :=
  (∀ q ∈ I.linFac p, q.2 = 1) ∧ (∀ q ∈ I.hiFac p, q.2 = 1)

/-- **E.14** [lemma] The separable-side degree sum `(DEG-SUM)` and the count match. -/
axiom RungInterface.forced_sum_eq {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    {p : ℕ × ℕ} (hp : p ∈ I.sides) (hsep : I.SepSide p) :
    Multiset.sum ((I.linFac p).map fun _ => C.D * p.2)
      + Multiset.sum ((I.hiFac p).map fun q => C.D * p.2 * q.1) = I.rootCount p

/-- **E.15** [theorem] The multiset sandwich. -/
axiom multiset_sandwich {α : Type*} (s : Multiset α) (count lower : α → ℕ)
    (hle : ∀ q ∈ s, lower q ≤ count q)
    (hsum : (s.map count).sum = (s.map lower).sum) :
    ∀ q ∈ s, count q = lower q

/-- **E.15** [theorem] The `(e,f)` forcing chain. -/
axiom ef_forcing {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hae : a ∣ e) (hbf : b ∣ f) (hprod : e * f = a * b) : e = a ∧ f = b

/-- **E.16** [theorem] THEOREM HE7.A, clauses (1)–(2), schema form. -/
axiom he7a_clause12 {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B) :
    ((∀ p ∈ I.sides, p.2 * B.T < p.1) ∧ ∑ p ∈ I.sides, I.len p = B.μ) ∧
    (∀ p ∈ I.sides, I.SepSide p →
      (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1))

/-- **E.17** [def] The three continuation cases of HE7.A(3)–(4), on the numerical shadow. -/
inductive ContCase | terminal | refine | child
  deriving DecidableEq

/-- **E.17** [def] The continuation case of a factor. -/
def contCaseOf (ℓ d k : ℕ) : ContCase :=
  if k = 1 then .terminal else if ℓ * d = 1 then .refine else .child

/-- **E.17** [theorem] The continuation trichotomy is complete. -/
axiom contCase_complete (ℓ d k : ℕ) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (contCaseOf ℓ d k = .terminal ∧ k = 1) ∨
    (contCaseOf ℓ d k = .refine ∧ 2 ≤ k ∧ ℓ * d = 1) ∨
    (contCaseOf ℓ d k = .child ∧ 2 ≤ k ∧ 2 ≤ ℓ * d)

/-- **E.17** [theorem] `(MASS)` at a child. -/
axiom child_mass {μ μc ℓ d : ℕ} (h2 : 2 ≤ ℓ * d) (h : μc * (ℓ * d) ≤ μ) :
    2 * μc ≤ μ

/-- **E.18** [theorem] The mid-chain peel `(MID-PEEL)`/`(MID-MASS)`. -/
axiom midPeel {O : Type*} [CommRing O] [IsDomain O] {G Φ : Polynomial O} {D ν : ℕ}
    (hΦ : Φ.Monic) (hΦd : Φ.natDegree = D) (hG : G.Monic) (hGd : G.natDegree = D * ν)
    (hν : 1 ≤ ν) (hD : 0 < D)
    (hsq : Squarefree (G.map (algebraMap O (FractionRing O)))) (hdvd : Φ ∣ G) :
    ∃ G' : Polynomial O, G = Φ * G' ∧ G'.Monic ∧ G'.natDegree = D * (ν - 1) ∧
      IsCoprime (G'.map (algebraMap O (FractionRing O)))
        (Φ.map (algebraMap O (FractionRing O)))

/-- **E.19** [def] The `(RANK)` state: `(deg, μ, σ)` ordered lexicographically. -/
def LadderState (W : Type*) := ℕ ×ₗ (ℕ ×ₗ W)

/-- **E.19** [def-class row, landed as an `axiom`: the SIGNATURE has no body — see defect
E-D5] The lexicographic well-founded relation on `LadderState W`. -/
axiom ladderState_wf {W : Type*} (r : WellFoundedRelation W) :
    WellFoundedRelation (LadderState W)

/-- **E.19** [lemma] Rank descent, first component. -/
axiom rank_decreases_of_deg_lt {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h : s'.1 < s.1) : (ladderState_wf r).rel s' s

/-- **E.19** [lemma] Rank descent, second component. -/
axiom rank_decreases_of_mass_lt {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h1 : s'.1 = s.1) (h2 : s'.2.1 < s.2.1) :
    (ladderState_wf r).rel s' s

/-- **E.19** [lemma] Rank descent, third component. -/
axiom rank_decreases_of_sec {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h3 : r.rel s'.2.2 s.2.2) : (ladderState_wf r).rel s' s

/-- **E.20** [theorem] Termination and exhaustion of the recursive read. -/
axiom read_terminates_exhausts {W : Type*} (r : WellFoundedRelation W)
    (step : LadderState W → Finset (LadderState W))
    (terminal : LadderState W → Prop) [DecidablePred terminal]
    (wt : LadderState W → ℕ)
    (hdec : ∀ s, ¬ terminal s → ∀ s' ∈ step s, (ladderState_wf r).rel s' s)
    (hcons : ∀ s, ¬ terminal s → ∑ s' ∈ step s, wt s' = wt s) :
    ∀ s₀, ∃ leaves : Multiset (LadderState W),
      (∀ l ∈ leaves, terminal l) ∧ (leaves.map wt).sum = wt s₀

/-- **E.21** [theorem] THEOREM T2.KEY-BOUNDARY, schema form. -/
axiom key_boundary {O : Type*} [CommRing O] [IsDomain O]
    (F : Polynomial O) (hF : F.Monic)
    (boundary : List (Polynomial O)) (blocks : List (Polynomial O))
    (hprod : F = boundary.prod * blocks.prod)
    (hbmon : ∀ P ∈ boundary, Polynomial.Monic P)
    (hkmon : ∀ B ∈ blocks, Polynomial.Monic B)
    (emit : Polynomial O → Multiset ℕ)
    (hemit : ∀ B ∈ blocks, (emit B).sum = B.natDegree) :
    (boundary.map Polynomial.natDegree).sum
      + (blocks.map (fun B => (emit B).sum)).sum = F.natDegree

-- **E.22** [instance-record] level-one instance record: NO SIGNATURE (obligation table).
-- **E.23** [instance-record] level-two/tower instance records: NO SIGNATURE (obligation table).

/-! ## §5 — THE SLOT-SEAM EVALUATION LAYER (E.25–E.38) -/

/-- **E.25** [lemma] Seam exponent integrality. -/
axiom seam_exp_dvd {e h i k t : ℕ} (hcop : Nat.Coprime h e) (hi : i < e)
    (hk : k % e = (i * h) % e) (ht : (i + e * t) * h ≤ k) :
    e ∣ k - (i + e * t) * h

/-- **E.25** [lemma] The seam exponent drops by `h` per unit `t`. -/
axiom seam_exp_step {e h i k t : ℕ} (hi : i < e)
    (ht : (i + e * (t + 1)) * h ≤ k) :
    (k - (i + e * t) * h) / e = (k - (i + e * (t + 1)) * h) / e + h

/-- **E.26** [def] The seam sum `Σ_t γ_t η^t` (the `(GAMMA)`/`(SLOT₂)` residue assembly). -/
def seamSum {F K : Type*} [Field F] [Field K] [Algebra F K]
    {g : ℕ} (γ : Fin g → F) (η : K) : K :=
  ∑ t : Fin g, algebraMap F K (γ t) * η ^ (t : ℕ)

/-- **E.26** [def] The twisted seam sum `Σ_t γ_t·ϑ_t·η^t` (R1-b's display). -/
def seamSumT {F K : Type*} [Field F] [Field K] [Algebra F K]
    {g : ℕ} (γ ϑ : Fin g → F) (η : K) : K :=
  ∑ t : Fin g, algebraMap F K (γ t * ϑ t) * η ^ (t : ℕ)

/-- **E.27** [lemma] The twisted seam kill (no cancellation). -/
axiom seamSumT_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {g : ℕ} (hg : g = Module.finrank F K) (γ ϑ : Fin g → F)
    (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    seamSumT γ ϑ η ≠ 0

/-- **E.28** [lemma] Rung class separation. -/
axiom rung_class_sep (R : RungDatum) {s s' v v' : ℕ}
    (hs : s < R.slotCount) (hs' : s' < R.slotCount)
    (hmod : s % R.ℓ ≠ s' % R.ℓ) :
    R.ℓ * v + s * R.u ≠ R.ℓ * v' + s' * R.u

/-- **E.28** [lemma] The single-class minimum criterion. -/
axiom rung_min_class (R : RungDatum) {s k m₀ s₀ t : ℕ}
    (hks : R.ℓ * m₀ + s₀ * R.u = k) (hs₀ : s₀ < R.ℓ)
    (hattain : s = s₀ + R.ℓ * t) (w : ℕ → ℕ)
    (hval : R.ℓ * w s + s * R.u = k) :
    w s = m₀ - t * R.u ∧ t * R.u ≤ m₀

section E29
open scoped Classical

/-- **E.29** [theorem] The twisted slot specification (R1-b); `(SLOT₂)` is its `ϑ ≡ 1`
instance. The `if`-guard spells §12(a)4's elided in-class guard. -/
axiom twisted_slot_spec {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).natDegree < C.D) (hsupp : ∀ s, R.slotCount ≤ s → c s = 0)
    (hocc : ∃ s < R.slotCount, c s ≠ 0)
    (ϑ : Fin R.g → K) (hϑ : ∀ t, ϑ t ≠ 0)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hmin : ∀ s < R.slotCount, c s ≠ 0 → ∀ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) →
      (k : ℤ) ≤ R.ℓ * v + s * R.u)
    (hatt : ∃ s < R.slotCount, c s ≠ 0 ∧
      C.hgt (c s) = (((m₀ : ℤ) - (((s - s₀) / R.ℓ : ℕ) : ℤ) * (R.u : ℤ)) : WithTop ℤ)) :
    seamSumT (fun t : Fin R.g =>
        if s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0
          then C.dig (c (s₀ + R.ℓ * (t : ℕ))) else 0) ϑ η ≠ 0

end E29

/-- **E.30** [def] The realized-reach set `T(k)` of LEMMA HE7-L1. -/
def reachSet (e h f₁ i₀ k : ℕ) : Finset (Fin f₁) :=
  Finset.univ.filter fun t => (i₀ + e * (t : ℕ)) * h ≤ k

/-- **E.30** [lemma] Fullness iff the deepest slot reaches. -/
axiom reachSet_full_iff {e h f₁ i₀ k : ℕ} (hf : 1 ≤ f₁) :
    reachSet e h f₁ i₀ k = Finset.univ ↔ (i₀ + e * (f₁ - 1)) * h ≤ k

/-- **E.30** [lemma] The k-uniform sufficient bound. -/
axiom reachSet_full_of_uniform {e h f₁ i₀ k : ℕ} (hi : i₀ < e) (hf : 1 ≤ f₁)
    (hk : (e * f₁ - 1) * h ≤ k) : reachSet e h f₁ i₀ k = Finset.univ

/-- **E.30** [lemma] Emptiness iff the shallowest slot fails. -/
axiom reachSet_empty_iff {e h f₁ i₀ k : ℕ} (hf : 1 ≤ f₁) :
    reachSet e h f₁ i₀ k = ∅ ↔ k < i₀ * h

/-- **E.31** [theorem] The twisted lift at a rung (R1-c); `(LIFT₂)` is its `ϑ ≡ 1` instance. -/
axiom twisted_lift {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    {b : ℕ} (hfull : ∀ m : ℕ, b ≤ m → C.Full m)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hthr : (R.g - 1) * R.u + b ≤ m₀)
    (γ ϑ : Fin R.g → K) (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    ∃ c : ℕ → Polynomial O,
      (∀ s, R.slotCount ≤ s → c s = 0) ∧ (∀ s, (c s).natDegree < C.D) ∧
      (∀ t : Fin R.g, γ t ≠ 0 →
        C.hgt (c (s₀ + R.ℓ * (t : ℕ))) = ((m₀ - (t : ℕ) * R.u : ℕ) : WithTop ℤ) ∧
        C.dig (c (s₀ + R.ℓ * (t : ℕ))) = γ t * (ϑ t)⁻¹) ∧
      (∀ t : Fin R.g, γ t = 0 → c (s₀ + R.ℓ * (t : ℕ)) = 0)

/-- **E.32** [def] The realized set at a height (corrected, punctured-subspace-coset form). -/
def realizedSet {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    {f₁ : ℕ} (η : K') (w : K'ˣ) (T : Finset (Fin f₁)) : Set K' :=
  { x | ∃ γ : Fin f₁ → F, (∀ t ∉ T, γ t = 0) ∧ (∃ t, γ t ≠ 0) ∧
        x = (w : K') * seamSum γ η }

/-- **E.32** [lemma] At full reach the realized set is all of `K'ˣ`. -/
axiom realizedSet_full {F K' : Type*} [Field F] [Field K'] [Algebra F K'] {f₁ : ℕ}
    {η : K'} (hgen : (minpoly F η).natDegree = Module.finrank F K')
    (hint : IsIntegral F η) (hf : f₁ = Module.finrank F K') (w : K'ˣ) :
    realizedSet (F := F) η w (Finset.univ : Finset (Fin f₁)) = {x : K' | x ≠ 0}

/-- **E.33** [def] The cocycle `τ(a,b) = n(a)n(b)n(a+b)⁻¹`. -/
def coc {G : Type*} [CommGroup G] (n : ℤ → G) (a b : ℤ) : G :=
  n a * n b * (n (a + b))⁻¹

/-- **E.33** [lemma] The `(COC)` identity. -/
axiom coc_cocycle {G : Type*} [CommGroup G] (n : ℤ → G) (a b c : ℤ) :
    coc n a b * coc n (a + b) c = coc n b c * coc n a (b + c)

/-- **E.33** [lemma] Twist-unit telescoping (R1-a(iii)'s exponent engine). -/
axiom theta_telescope {G : Type*} [CommGroup G] (n : ℤ → G) (m₀ u : ℤ) (t : ℕ) :
    n (m₀ - t * u) * (n u) ^ t * (n m₀)⁻¹
      = ∏ j ∈ Finset.range t, coc n (m₀ - (j + 1) * u) u

/-- **E.33** [lemma] At a homomorphism the cocycle is trivial (`τ₁ ≡ 1`). -/
axiom coc_of_hom {G : Type*} [CommGroup G] (n : ℤ → G)
    (hn : ∀ a b, n (a + b) = n a * n b) (a b : ℤ) : coc n a b = 1

/-- **E.34** [lemma] `(IDX-TWIST)`'s bijection layer. -/
axiom unit_mul_bijOn {K : Type*} [Field K] (w : Kˣ) :
    Set.BijOn (fun x : K => (w : K) * x) {x | x ≠ 0} {x | x ≠ 0}

/-- **E.34** [lemma] The relabelling fixes `0`. -/
axiom unit_mul_zero {K : Type*} [Field K] (w : Kˣ) : (w : K) * 0 = 0

/-- **E.35** [theorem] `(REF-HT)`: the refinement height AND digit are forced by `(RISE)`. -/
axiom refht_forced {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)  -- see SIGNATURE NOTE
    {a b : Polynomial O} {lam k : ℤ}
    (ha : C.hgt a = (lam : WithTop ℤ)) (hb : C.hgt b = (k : WithTop ℤ))
    (hrise : (lam : WithTop ℤ) < C.hgt (a - b)) :
    k = lam ∧ C.dig b = C.dig a

/-- **E.36** [theorem] The gcd dichotomy (ANNEX-LEMMA R2-a, schema form). -/
axiom gcd_dichotomy {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree) :
    ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree = 0 ∨ g₀ = Ψ

/-- **E.36** [theorem] Coprimality from non-divisibility. -/
axiom coprime_of_not_dvd {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree)
    (hndvd : ¬ Ψ ∣ F) :
    IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Ψ.map (algebraMap O (FractionRing O)))

/-- **E.37** [theorem] The standing-convention peel: the peel fires at most once. -/
axiom peel_once {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (hdvd : Ψ ∣ F) :
    ∃ F' : Polynomial O, F = Ψ * F' ∧ F'.Monic ∧
      F'.natDegree = F.natDegree - D ∧ ¬ Ψ ∣ F'

/-- **E.38** [theorem] Slot domination, the fold (d). -/
axiom slot_fold {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {T : ℤ} (ws : List (Polynomial O)) (hne : ws ≠ [])
    (hdeg : ∀ w ∈ ws, w.natDegree < C.D)
    (hval : ∀ w ∈ ws, ∃ v : ℤ, C.hgt w = (v : WithTop ℤ) ∧ T < v)
    (hdist : ws.Pairwise fun w w' => C.hgt w ≠ C.hgt w') :
    ws.sum ≠ 0 ∧ (∃ v : ℤ, C.hgt ws.sum = (v : WithTop ℤ) ∧ T < v) ∧
      C.hgt ws.sum = (ws.map C.hgt).foldr min ⊤

/-- **E.38** [theorem] The off-disk positivity arithmetic of clause (a). -/
axiom offdisk_positivity {ν T₂ ℓ D' h lam ε₀ ε₁ : ℤ}
    (hν : T₂ < ν) (hlam : D' * h < lam) (hℓ : 1 ≤ ℓ) (hD : 1 ≤ D')
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hcase : (0 < ε₀ ∧ ε₁ = ℓ * (lam - D' * h) + ℓ * D' * ε₀) ∨ ε₀ = 0) :
    0 < (ν - T₂) + ε₁ - ℓ * (D' - 1) * ε₀

/-! ## §6 — `(LB1)` AND `(MP1)`: THE TWO OPEN OBLIGATIONS (E.39–E.44) -/

/-- **E.39** [def] `(LB1)` (`EFF.T2.18`): the level-one clause-4 block suite exists. OPEN — a
named capstone hypothesis; no chapter-E node proves it. -/
def LB1Carrier {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ I : RungInterface.{uO, uK, uW} C B,
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    ∃ blocks : List (Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B'),
      B.F = (blocks.map fun x => x.1.F).prod ∧
      (blocks.map fun x => x.1.F.natDegree).sum = B.F.natDegree
      -- + the per-block pure-residual and length clauses; see the node's SIGNATURE NOTE

/-- **E.40** [def] `(MP1)` (`EFF.T2.23`): the level-one mid-chain-peel input suite at a
RECENTERED key. OPEN — a named capstone hypothesis; carried to chapter I. -/
def MP1Carrier {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ (Λ : Polynomial O),                        -- the recentering increment
    Λ ≠ 0 → Λ.natDegree < C.D →
    ∀ (B' : BlockData C),                      -- the quotient block at key Φ − Λ
      B'.Φ = B.Φ - Λ → B'.Φ ∣ B.F →
      Nonempty (RungInterface.{uO, uK, uW} C B') ∧
      -- item 5: the peeled key's certified (e,f) emission
      ∃ e f : ℕ, e * f = C.D ∧ C.eC ∣ e ∧ C.fC ∣ f

/-- **E.41** [lemma] The scope theorem: clauses 1–2 fire without `(LB1)`. -/
axiom clause12_lb1_free {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    (hone : I.sides.card = 1) (hsep : ∀ p ∈ I.sides, I.SepSide p) :
    ∀ p ∈ I.sides, (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1)

/-- **E.42** [theorem] The level-two discharge S1.8B (the composed-key entry). -/
axiom s18b_fold {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {T : ℤ}
    (w : Polynomial O) (ws : List (Polynomial O))
    (hw : w = 0 ∨ (w.natDegree < C.D ∧ ∃ v : ℤ, C.hgt w = (v : WithTop ℤ) ∧ T < v))
    (hws : ∀ x ∈ ws, x.natDegree < C.D ∧ ∃ v : ℤ, C.hgt x = (v : WithTop ℤ) ∧ T < v)
    (hdist : (w :: ws).Pairwise fun a b => a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b) :
    (w + ws.sum = 0 ∧ ws = [] ∧ w = 0) ∨
    ((w + ws.sum).natDegree < C.D ∧
      ∃ v : ℤ, C.hgt (w + ws.sum) = (v : WithTop ℤ) ∧ T < v)

/-- **E.43** [lemma] S1.8C clause (i): the membership identity. -/
axiom recentered_is_member {O : Type*} [CommRing O] (Φ B₀ : Polynomial O) :
    Φ + B₀ = Φ - (-B₀)

/-- **E.43** [lemma] S1.8C clause (ii): the carrier's read mentions no key (frame stability
is enforced by TYPE; the content is that this elaborates). -/
axiom frame_key_free {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (A : Polynomial O) :
    C.hgt A = C.hgt A ∧ C.dig A = C.dig A

/-- **E.44** [def] The chapter-E obligations record: what chapter I receives from the
σ-ladder. `(MP1′)` is RETIRED and deliberately has NO carrier. -/
structure LadderObligations {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop where
  lb1 : LB1Carrier.{uO, uK, uW} C B
  mp1 : MP1Carrier.{uO, uK, uW} C B

/-! ## §7 — THE σ DICTIONARY AND THE TRANSPORT LAWS (E.45–E.54; TERMINAL SUPPLY) -/

/-- **E.45** [def] One terminal emission of the σ-ladder read (numerical shadow, D-E2). -/
structure LadderLeaf where
  path : List (ℕ × ℕ)
  term : ℕ × ℕ
  deriving DecidableEq

/-- **E.45** [def] The composed `(e, f)` of a leaf at base `(e₀, f₀)` (`EFF.HE7.48`). -/
def LadderLeaf.ef (l : LadderLeaf) (e₀ f₀ : ℕ) : ℕ × ℕ :=
  (e₀ * (l.path.map Prod.fst).prod * l.term.1,
   f₀ * (l.path.map Prod.snd).prod * l.term.2)

/-- **E.45** [def] **The σ dictionary** (GC-4): ladder leaves → the landed factorization
type. Carrier is the LANDED `Uniformity.FactorizationType` (see defect E-D8 on the
blueprint's `Uniformity.Density.FactorizationType` spelling). -/
def ladderSigma (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) :
    Uniformity.FactorizationType :=
  ⟨leaves.map fun l => l.ef e₀ f₀⟩

/-- **E.46** [lemma] Degree conservation (GC-4's mandatory invariant). -/
axiom ladderSigma_degree (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) :
    (ladderSigma e₀ f₀ leaves).degree
      = (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum

/-- **E.46** [lemma] Degree conservation, block-degree form. -/
axiom ladderSigma_degree_eq_deg {O : Type*} [CommRing O]
    (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) (F : Polynomial O)
    (hwt : (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum = F.natDegree) :
    (ladderSigma e₀ f₀ leaves).degree = F.natDegree

/-- **E.47** [def] Prepending a rung to a leaf's path. -/
def LadderLeaf.prepend (r : ℕ × ℕ) (l : LadderLeaf) : LadderLeaf :=
  ⟨r :: l.path, l.term⟩

/-- **E.47** [lemma] Rung composition of leaves (associativity of the ladder product). -/
axiom ladderSigma_prepend (e₀ f₀ : ℕ) (r : ℕ × ℕ) (leaves : Multiset LadderLeaf) :
    ladderSigma e₀ f₀ (leaves.map (LadderLeaf.prepend r))
      = ladderSigma (e₀ * r.1) (f₀ * r.2) leaves

/-- **E.48** [theorem] The rung σ-transport law (σ is multiplicative over the block split),
stated at the LANDED `typeOf_mul`'s strength: on `.data`, monicity only. The signed
`typeOf l.prod = (l.map typeOf).sum` does NOT elaborate — see defect E-D9. -/
axiom typeOf_list_prod {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (l : List (Polynomial O))
    (hm : ∀ g ∈ l, Polynomial.Monic g) :
    (Uniformity.Density.typeOf l.prod).data
      = (l.map fun g => (Uniformity.Density.typeOf g).data).sum

/-- **E.49** [def] The μ₂ = 2 dictionary rows (`EFF.HE7.58`'s table; rows 5/6 route onward). -/
inductive Mu2Row
  | oneSideHalf      -- row 1: λ₂ ∉ ℤ (ℓ₂ = 2)
  | oneSideInert     -- row 2: λ₂ ∈ ℤ, R₂ irreducible quadratic
  | oneSideSplit     -- row 3: λ₂ ∈ ℤ, R₂ split
  | twoSides         -- row 4
  | refineRow        -- row 5: R₂ = (Z−s₂)² — α-refine, re-read
  | peelRow          -- row 6: Ψ ∣ f — peel
  deriving DecidableEq

/-- **E.49** [def] The decided-row σ values at the n = 8 frame. -/
def mu2Sigma : Mu2Row → Option Uniformity.FactorizationType
  | .oneSideHalf  => some ⟨{(8, 1)}⟩
  | .oneSideInert => some ⟨{(4, 2)}⟩
  | .oneSideSplit => some ⟨{(4, 1), (4, 1)}⟩
  | .twoSides     => some ⟨{(4, 1), (4, 1)}⟩
  | .refineRow    => none        -- re-read at the refined key (E.52)
  | .peelRow      => some ⟨{(4, 1), (4, 1)}⟩

/-- **E.49** [lemma] Every decided row has degree 8. -/
axiom mu2Sigma_degree : ∀ r v, mu2Sigma r = some v → v.degree = 8

/-- **E.50** [lemma] The three-letter alphabet ("no fourth value possible"). -/
axiom mu2Sigma_alphabet :
    ∀ r v, mu2Sigma r = some v →
      v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩

-- BLOCKED: GC-13 resolution (§12 BLOCKED-UNTIL-RESOLUTION; `hpeel : True` placeholder —
-- the orchestrator types it against chapter C's HE6R1-3 emission record at freeze. A fleet
-- agent must NOT prove E.51 while the placeholder is `True`: it would be vacuous.)
/-- **E.51** [theorem] The peel-row law (row 6, given the peel supplier). -/
axiom peel_row_law
    (hpeel : True)   -- placeholder anchoring the HE6R1-3 emission supplier
                     -- [supplied-by: chapter C]
    {e f : ℕ} (hforce4 : 4 ∣ e * f) (hef : e * f = 4)
    (he : 4 ∣ e ∨ (e = 4 ∧ f = 1)) :   -- the forcing shadow at μ₂′ = 1
    e = 4 ∧ f = 1

/-- **E.52** [theorem] THEOREM HE7.A′ schema (the n = 8 bite decided, refine loop included).
NOT blocked (§12: it consumes E.51's row only through `mu2Sigma`). -/
axiom he7a_prime_schema
    (read : ℕ → Mu2Row)                  -- the row at refine-step i
    (hterm : ∃ i, read i ≠ .refineRow)   -- termination supply (E.55/E.56 at μ₂ = 2)
    : ∃ i v, mu2Sigma (read i) = some v ∧
        (v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩)

/-- **E.53** [lemma] The GC-3 bridge fence: the dictionary's `(e,f)` is NEVER identified with
the ideal-theoretic pair (`HYP.01` + `HYP.12`, CORE-SET). -/
axiom leaf_ef_finrank {e f n : ℕ} (hef : e * f = n)
    (hrank : n = n) :  -- anchor: instances substitute `finrank K₀ L` here via the
                       -- quarry identity; the fence forbids more
    e * f = n

/-- **E.54** [lemma] Frame/origin invariance of σ at the dictionary. -/
axiom ladderSigma_frame_invariant (e₀ f₀ : ℕ) (leaves leaves' : Multiset LadderLeaf)
    (h : leaves = leaves') :  -- the shadow equality the frame change induces
    ladderSigma e₀ f₀ leaves = ladderSigma e₀ f₀ leaves'

/-! ## §8 — ROOT-CONTINUATION AND EXHAUST (E.55–E.60) -/

/-- **E.55** [theorem, HARD] α-refine chains are finite (LEMMA HE7-8, `(REF-TERM)`).
The three stub-stage spelling calls of the SIGNATURE NOTE are executed here:
(a) `hOcoeff` is the landed DVR valuation `IsDiscreteValuationRing.addVal` pushed into
`WithTop ℤ` by `WithTop.map`; (b) the increment degree bound is against the CURRENT key degree
`C.D` (the NOTE's own resolution of its display's `C.D * μ₂`); (c) `hfloor`'s right side is
the cleared `WithTop ℤ` inequality. None changes the theorem's strength. -/
axiom refine_chain_finite {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {K : Type*} [Field K] (C : SlotCarrier O K)
    (hcoeff : ∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
      (v : WithTop ℤ) ≤ C.hgt A → ∀ i,
        (v : WithTop ℤ) ≤ (IsDiscreteValuationRing.addVal O (A.coeff i)).map
          (fun n : ℕ => (n : ℤ)))
    {F Ψ : Polynomial O} {μ₂ : ℕ} (hμ : 2 ≤ μ₂)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hdeg : ∀ j, (w j).natDegree < C.D)          -- deg < the current key degree; NOTE (b)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hmono : StrictMono lam)
    (A : ℕ → ℕ → Polynomial O)
    (hdev : ∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
      + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m)
    (hfloor : ∀ j, ∀ m < μ₂,
      (((((μ₂ - m : ℕ) : ℤ) * lam j : ℤ)) : WithTop ℤ) ≤ C.hgt (A j m)) :
    False

/-- **E.56** [theorem] The per-step jump: the same-residue kill. -/
axiom same_digit_rises {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    {a b : Polynomial O} {k : ℤ} (ha : C.hgt a = (k : WithTop ℤ))
    (hb : C.hgt b = (k : WithTop ℤ)) (hd : C.dig a = C.dig b) :
    (k : WithTop ℤ) < C.hgt (a - b)

/-- **E.56** [theorem] The chain invariant (HE7-12(d)/HE7-13's mutual induction, packaged). -/
axiom chain_invariant {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hstep : ∀ j, lam j < lam (j + 1))   -- supplied per step by the refined read
    : StrictMono lam ∧ ∀ i j, i < j → C.hgt (w i) ≠ C.hgt (w j)

-- BLOCKED: GC-13 resolution (§12 BLOCKED-UNTIL-RESOLUTION; `hpart : True` placeholder —
-- the product/disjointness carrier leg, typed against chapter C's partition record at freeze.
-- The fleet must NOT fire on E.57 before that pass.)
/-- **E.57** [theorem, HARD] The mixed-node block split (ANNEX-LEMMA HE7-13′(a), schema
form) — the PROVED level-≥2 counterpart of `(LB1)`. -/
axiom block_split {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    -- carrier legs (C-supplied at instances; the schema's explicit hypotheses):
    (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCount p q)
    (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCountHi p q)
    (hpart : True)  -- the product/disjointness leg; typed at GC-13 resolution
    : ∃ blocks : List (Polynomial O),
        B.F = blocks.prod ∧
        (blocks.map Polynomial.natDegree).sum = B.F.natDegree

/-- **E.58** [lemma] The per-class refine quartet (HE7-13′(b)–(e)). -/
axiom refine_quartet {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (hhigh : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      (k : WithTop ℤ) < C.hgt b → C.hgt (a + b) = (k : WithTop ℤ) ∧
        C.dig (a + b) = C.dig a)
    {w : Polynomial O} {lam : ℤ} (hw : C.hgt w = (lam : WithTop ℤ)) :
    (∀ a, C.hgt a = (lam : WithTop ℤ) → C.dig a = C.dig w →
      (lam : WithTop ℤ) < C.hgt (a - w)) ∧
    (∀ a, C.hgt a = (lam : WithTop ℤ) → C.dig a ≠ C.dig w →
      C.hgt (a - w) = (lam : WithTop ℤ) ∧ C.dig (a - w) = C.dig a - C.dig w) ∧
    (∀ a (μ : ℤ), μ < lam → C.hgt a = (μ : WithTop ℤ) →
      C.hgt (a - w) = (μ : WithTop ℤ) ∧ C.dig (a - w) = C.dig a) ∧
    (∀ a (ν : ℤ), lam < ν → C.hgt a = (ν : WithTop ℤ) →
      C.hgt (a - w) = (lam : WithTop ℤ) ∧ C.dig (a - w) = - C.dig w)

/-- **E.59** [lemma] The per-block level-jump gate (`μ ≥ 4` at any jump). -/
axiom block_jump_gate {k ℓ d L : ℕ} (hk : 2 ≤ k) (hld : 2 ≤ ℓ * d)
    (hL : L = k * (ℓ * d)) : 4 ≤ L

/-- **E.59** [lemma] Non-propagation at `μ ≤ 3`. -/
axiom no_jump_of_mu_le_three {μ L : ℕ} (hμ : μ ≤ 3) (hLμ : L ≤ μ) : ¬ 4 ≤ L

/-- **E.60** [theorem] THEOREM HE7.C, schema form (the ladder is finite at every degree). -/
axiom ladder_finite_bounds (μ : ℕ → ℕ) (J : ℕ)
    (h4 : ∀ i ≤ J, 4 ≤ μ i) (hh : ∀ i < J, 2 * μ (i + 1) ≤ μ i) :
    2 ^ (J + 1) ≤ μ 0 ∧ (μ 0 = 4 → J ≤ 1) ∧ (μ 0 ≤ 7 → ∀ i, 1 ≤ i → i ≤ J → μ i ≤ 3)
    ∧ (2 ≤ J → 8 ≤ μ 0)

/-! ## §9 — THE `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` INDEXED CARRIERS (E.61–E.64) -/

-- BLOCKED: GC-13/GC-14 resolution (§12 BLOCKED-UNTIL-RESOLUTION; the `supplied : True`
-- placeholder is typed when chapter C's letter layer and chapter D's ϑ table freeze).
/-- **E.61** [def] `(H-VARTHETA-RES)_i` (Display A, ∀ i ≥ 3): the level-i deep-twist units are
the letter-monomial residues, correctly oriented per chapter D's canonical ϑ table
[GC-14 anchor: EFF.GENTOW2 orientation records, supplied-by chapter D]. -/
structure VarthetaRes (i : ℕ) : Prop where
  supplied : True   -- typed at GC-13/GC-14 resolution; see the node's SIGNATURE NOTE

-- BLOCKED: GC-13 resolution (content is chapter D's T5 w-frame layer).
/-- **E.62** [def] `𝒲_(≤i)` (Display A, ∀ i ≥ 3): the w-frame holds through level `i`.
Content [supplied-by: chapter D (T5)]; E declares the socket. -/
structure WFrame (i : ℕ) : Prop where
  supplied : True   -- typed at GC-13 resolution against chapter D's T5 layer

/-- **E.63** [def] The Display-A `∀ i ≥ 3` conjunct, packaged. -/
def DeepTwistConjunct : Prop := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i

/-- **E.63** [lemma] The conjunct constrains nothing at ladder depth ≤ 2. -/
axiom deepTwist_vacuous_shallow (Λ : LadderData) (h : Λ.rungs.length ≤ 1) :
    ∀ i, 3 ≤ i → Λ.rungs.length + 1 < i ∨ True

/-- **E.64** [lemma] Depth ≥ 3 is unreachable below `n = 16` (necessary direction, R3-rider). -/
axiom depth3_needs_16 {D₀ μ₀ J : ℕ} (hD : 2 ≤ D₀) (hJ8 : 2 ≤ J → 8 ≤ μ₀)
    (hJ : 2 ≤ J) : 16 ≤ D₀ * μ₀

/-! ### NODE E.24 — the chapter-I package (placed here per §12: forward references to
§6's obligation carriers and §9's indexed carriers). -/

/-- **E.24** [def] Display A's `HE7A[…]` conjunct: the σ-ladder carrier suite holds for the
block — packaged for chapter I's hypothesis structure. -/
def HE7APackage {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  Nonempty (RungInterface.{uO, uK, uW} C B)

/-- **E.24** [def] The full chapter-E supply to chapter I: the package at every rung of a
ladder, plus the carried obligations. -/
structure LadderSupply {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop where
  package : HE7APackage.{uO, uK, uW} C B
  lb1 : LB1Carrier.{uO, uK, uW} C B           -- E.39
  mp1 : MP1Carrier.{uO, uK, uW} C B           -- E.40
  vartheta : ∀ i ≥ 3, VarthetaRes i           -- E.61 (with E.62's 𝒲 conjunct at I)

end LeanspecE
