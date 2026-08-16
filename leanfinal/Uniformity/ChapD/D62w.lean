/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D05
import Uniformity.ChapD.D17
import Uniformity.ChapD.D62

/-!
# Uniformity.ChapD.D62w — the deep-twist witness layer (unit OM-8)

**D.62-adjacent appendix file** (the H09w/H73w/H89w precedent), landed by unit OM-8
(`docs/openmath-campaign/OM-8_deep-twist_2026-08-16.md`; ledger rows HYP.57/HYP.63 — Display
A's `∀ i ≥ 3 ((H-VARTHETA-RES)_i ∧ 𝒲_{≤i})` conjunct, consumed at the A-D.2 sitewise form
per CHAP-I I.10's dated note). Five layers (1, 2, 3, 3′, 4), all PROVED, Lean-core only:

1. **The ϑ→τ reduction** (`hvarthetaRes_of_tau_letters`): the sitewise carrier at ANY datum
   `(N, v, ρ, q)` follows from the τ-letter law — every cocycle value `τ(sq, q)` has value
   zero and `ρ`-image in (the embedded) `K`. This is the Lean shadow of `EFF.T1.10`'s
   `(C2-recursion)` consumption: the corpus's per-depth content is EXACTLY the τ-law, and the
   telescope adds nothing (D.05's recursion + induction). Arena-free by design (DECISION D-2:
   the datum is `(N, v, ρ)`, no arena assumed).
2. **The `i = 1` discharge** (`hvarthetaRes_levelOne`): `EFF.T1.09`'s "at `i = 1` by direct
   evaluation ((C2-level-1): `ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}`, a power of `η ∈ K₁ˣ`)",
   transcribed through D.17's `levelOneArena` (whose `res` IS the η-power read) +
   `hvarthetaRes_of_arena_agree` at `L = K`. The corpus's level-1 proof survives verbatim:
   the arena's `res` is a genuine hom on the value-zero subgroup, so the sitewise clause
   holds for the canonical `ρ = res` at EVERY height `q` — the `i = 1` slice of the ledger
   display, machine-checked.
3. **The depth-3 letter-lattice model** (`deep3Section`/`deep3Height` + `deep3_tau_descent` +
   `hvarthetaRes_deep3`): the `i = 3` instance of GENTOW5_PROOF S2.1's monomial-quotient
   computation at the exponent level, on the F-LW3/F-P5/F-EC3 exponent chain
   (`(e, h, u) = ((2,2,2,1), 1, (1,5,21,43))`; `dv₃`-coefficients `(8,4,10,21)` on
   `(π, x, Φ₁, Φ₂)`). The greedy normalizer `n̂₃` is DEFINED (Euclidean `%`/`/` chains), its
   exact-height law is PROVED (`deep3_exact_height`), and the LATTICE FACTORIZATION is PROVED
   (`deep3_tau_descent`): every cocycle value `τ(a,b)` — for ALL heights `a, b`, not just the
   consumed ones — is an EXACT `ℤ`-monomial `γ₁^{c₁}γ₂^{c₂}γ₃^{c₃}` in the letter generators
   `γ₁ = x^{e₁}/π^h`, `γ₂ = Φ₁^{e₂}/n̂₁(u₂)`, `γ₃ = Φ₂^{e₃}/n̂₂(u₃)`. Consequence
   (`hvarthetaRes_deep3`): ANY residue datum `ρ` sending the three letters into `K` discharges
   the sitewise carrier at EVERY height `q` — the `(H-VARTHETA-RES)₃` law, reduced to exactly
   the three letter-memberships that the corpus's node-point read supplies (`β_j` a
   `ψ_{j+1}`-root ∈ `K_{j+1}ˣ ⊆ K₃ˣ`; numerically certified at both characteristics,
   `verification/om8_vartheta_deep.py` LEGs B/C).
3′. **The depth-2 model** (`deep2Section` + `deep2_tau_descent` + `hvarthetaRes_deep2`): the
   `i = 2` transcription — `EFF.GENTOW2.42`'s γ-calculus ("the value-0 Laurent monomials
   `x^i π^a Φ′^b` form exactly the group `⟨γ₁, γ₂⟩`") at exponent level, same descent, two
   letters.
4. **The `𝒲` interleaved-induction skeleton** (`Wle`, `wle_two`, `wle_of_interleaved`): the
   HYP.63 closure argument, abstractly. `Wle W n := ∀ q ∈ [3, n], W q` (byte-matching the
   leanspec D.55 carrier); `wle_two` is PROVED (the empty base — an `axiom` in leanspec);
   `wle_of_interleaved` PROVES: given the base `B 2` (the landed GENTOW2 clause (b) at
   index 2), the step `∀ i ≥ 3, Wle W (i−1) → B (i−1) → W i` (the WI companion's lemma, whose
   S3 census consumes clause (b) at index `i−1` = its C-5), and the chain
   `∀ i ≥ 3, Wle W i → B i` (frozen GENTOW5's `𝒲_{≤n} ⟹ (a)@n ⟹ Cor 6.4 ⟹ (b)@n`,
   T5 §4's (WF-chain)), the cumulative `Wle W n` holds for EVERY `n` — T5 S12.1's "induction
   closing the conjuncts from the empty base", as a machine-checked skeleton. What this does
   NOT do: discharge the three suppliers (they stay at their own grades — see the unit note
   §3.2's footprint walk).

## Faithfulness

* The deep3 model is the EXPONENT-LEVEL shadow of the tower — the faithful bridge to the
  p-adic/Laurent field is the corpus's evaluation leg (GENTOW5_PROOF S2.3 step (3), accepted;
  node points give each monomial factor its exact value, so residues multiply), machine-
  covered by the OM-8 instrument's PARI/equal-char oracles at the same exponent chain.
* Nothing here claims the ABSTRACT carrier for arbitrary `ρ`: it is genuinely `ρ`-dependent
  (`om4_resign_nontriviality.lean`; the OM-8 LEG-D2 twist at these very exponents), and the
  chapter-C instantiation obligation is exactly "supply the CANONICAL residue read".
* `deep3_tau_descent` quantifies over ALL `(a, b)` — strictly more than the ϑ-consumption
  needs — because the descent is forced by the height identity alone; this is the honest
  content of "standard MacLane residual specialization" (R9-2) at this depth.

DEPENDS: D.01/D.02/D.04/D.05 (section/cocycle/telescope + recursion), D.07/D.17 (arena,
level-1 instance), D.62 (the A-D.2 carrier).

## Status

Sorry-free, axiom-free (Lean core only). All theorems PROVED.
-/

namespace Uniformity.Density.Gauge

/-! ## 1. The ϑ→τ reduction -/

/-- **OM-8, the reduction.** The sitewise `(H-VARTHETA-RES)` carrier follows from the
τ-letter law at the datum: every cocycle value `τ(sq, q)` lies in `ker v` with `ρ`-image an
embedded `K`-unit. Proof: D.05's recursion + induction on `s` (the telescope endpoints are
`1`). Arena-free (DECISION D-2's datum discipline). -/
theorem hvarthetaRes_of_tau_letters {G : Type*} [CommGroup G] {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] {N : NormSection G}
    (v : G →* Multiplicative ℤ) (ρ : MonoidHom.ker v →* Lˣ) (q : ℤ)
    (hτker : ∀ s : ℕ, N.tau ((s : ℤ) * q) q ∈ MonoidHom.ker v)
    (hτK : ∀ s : ℕ, ∃ u : Kˣ,
      ((ρ ⟨N.tau ((s : ℤ) * q) q, hτker s⟩ : Lˣ) : L) = algebraMap K L (u : K)) :
    HVarthetaRes G K L N v ρ q := by
  intro s
  induction s with
  | zero =>
    have hker : N.varthetaEl q 0 ∈ MonoidHom.ker v := by
      rw [N.varthetaEl_zero]; exact one_mem _
    refine ⟨hker, 1, ?_⟩
    have h1 : (⟨N.varthetaEl q 0, hker⟩ : MonoidHom.ker v) = 1 := by
      ext; simp [N.varthetaEl_zero]
    rw [h1, map_one]
    simp
  | succ s ih =>
    obtain ⟨hker, u, hu⟩ := ih
    have hker' : N.varthetaEl q (s + 1) ∈ MonoidHom.ker v := by
      rw [N.varthetaEl_succ]; exact mul_mem hker (hτker s)
    obtain ⟨w, hw⟩ := hτK s
    refine ⟨hker', u * w, ?_⟩
    have hsplit : (⟨N.varthetaEl q (s + 1), hker'⟩ : MonoidHom.ker v)
        = ⟨N.varthetaEl q s, hker⟩ * ⟨N.tau ((s : ℤ) * q) q, hτker s⟩ := by
      ext; simp [N.varthetaEl_succ]
    rw [hsplit, map_mul, Units.val_mul, hu, hw, Units.val_mul, ← map_mul]

/-! ## 2. The `i = 1` discharge (the corpus's level-1 proof, transcribed) -/

/-- **The `i = 1` slice of `EFF.T1.09`, machine-checked**: at D.17's level-1 arena the
canonical residue datum (`ρ := res`, the η-power read) discharges the sitewise carrier at
every height. This is "(C2-level-1): `ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}` ... a power of
`η ∈ K₁ˣ`" — the proved membership, without the exponent formula (which is D.18's). -/
theorem hvarthetaRes_levelOne {K : Type*} [Field K] (e₁ h : ℕ) (he : 0 < e₁)
    (hcop : Nat.Coprime h e₁) (η : Kˣ) (q : ℤ) :
    HVarthetaRes (Multiplicative (ℤ × ℤ)) K K (levelOneSection e₁ h)
      (levelOneArena e₁ h he hcop η).v (levelOneArena e₁ h he hcop η).res q :=
  hvarthetaRes_of_arena_agree (levelOneArena e₁ h he hcop η) _ (fun x => by simp) q

/-! ## 3. The depth-3 letter-lattice model (the `i = 3` instance, exponent level)

The F-LW3/F-P5/F-EC3 exponent chain: stage data `e = (2,2,2,1)`, `h = 1`,
heights `u = (1, 5, 21, 43)`; `dv₃`-coefficients on `(π, x, Φ₁, Φ₂)` are `(8, 4, 10, 21)`.
Exponent vectors live in `Multiplicative (ℤ × ℤ × ℤ × ℤ)`. -/

/-- The depth-3 exponent group: `(a, i₀, b₁, b₂)` = the exponents of `(π, x, Φ₁, Φ₂)`. -/
abbrev Deep3 := Multiplicative (ℤ × ℤ × ℤ × ℤ)

/-- The `dv₃` height homomorphism: `8a + 4i₀ + 10b₁ + 21b₂`
(= `ê₃·a + (ê₃/ê₁)h·i₀ + (ê₃/ê₂)u₂·b₁ + u₃·b₂`). -/
def deep3Height : Deep3 →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd
    (8 * (Multiplicative.toAdd g).1 + 4 * (Multiplicative.toAdd g).2.1
      + 10 * (Multiplicative.toAdd g).2.2.1 + 21 * (Multiplicative.toAdd g).2.2.2)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ← ofAdd_add]
    ring_nf

/- The greedy normalizer exponents (DEF GENTOW5-1's ladder recursion at this chain;
Euclidean `%`/`/`, defined for ALL `k : ℤ` — Laurent at negative heights). -/

/-- `b₂(k)`: the `Φ₂`-exponent (level-3 peel; `u₃ = 21` odd, `e₃ = 2`). -/
def d3b2 (k : ℤ) : ℤ := k % 2
/-- the level-2 residual height. -/
def d3m2 (k : ℤ) : ℤ := (k - 21 * d3b2 k) / 2
/-- `b₁(k)`: the `Φ₁`-exponent (level-2 peel; `u₂ = 5` odd, `e₂ = 2`). -/
def d3b1 (k : ℤ) : ℤ := d3m2 k % 2
/-- the level-1 residual height. -/
def d3m1 (k : ℤ) : ℤ := (d3m2 k - 5 * d3b1 k) / 2
/-- `i₀(k)`: the `x`-exponent (`h = 1`, `e₁ = 2`). -/
def d3i0 (k : ℤ) : ℤ := d3m1 k % 2
/-- `a(k)`: the `π`-exponent. -/
def d3a (k : ℤ) : ℤ := (d3m1 k - d3i0 k) / 2

/-- The exact-height identity of the greedy solve: `8a(k) + 4i₀(k) + 10b₁(k) + 21b₂(k) = k`
(`EFF.T1.01`'s identity, at depth 3). -/
theorem d3_height_id (k : ℤ) :
    8 * d3a k + 4 * d3i0 k + 10 * d3b1 k + 21 * d3b2 k = k := by
  simp only [d3a, d3i0, d3m1, d3b1, d3m2, d3b2]
  omega

/-- The depth-3 tower normalizer section (`n̂₃`, greedy exponents). -/
def deep3Section : NormSection Deep3 where
  n k := Multiplicative.ofAdd (d3a k, d3i0 k, d3b1 k, d3b2 k)
  n_zero := by
    have : d3a 0 = 0 ∧ d3i0 0 = 0 ∧ d3b1 0 = 0 ∧ d3b2 0 = 0 := by
      simp only [d3a, d3i0, d3m1, d3b1, d3m2, d3b2]; omega
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2]

/-- `n̂₃` sits at exact height: `deep3Height (n̂₃ k) = k`. -/
theorem deep3_exact_height (k : ℤ) :
    deep3Height (deep3Section.n k) = Multiplicative.ofAdd k := by
  simp only [deep3Section, deep3Height, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  exact congrArg Multiplicative.ofAdd (d3_height_id k)

/-- Letter `γ₁ = x^{e₁}/π^h = x²/π` (the wrap; residue `η = z₁`). -/
def d3g1 : Deep3 := Multiplicative.ofAdd (-1, 2, 0, 0)
/-- Letter `γ₂ = Φ₁^{e₂}/n̂₁(u₂) = Φ₁²/(π²x)` (residue `z₂`). -/
def d3g2 : Deep3 := Multiplicative.ofAdd (-2, -1, 2, 0)
/-- Letter `γ₃ = Φ₂^{e₃}/n̂₂(u₃) = Φ₂²/(π⁴Φ₁)` (residue `z₃`). -/
def d3g3 : Deep3 := Multiplicative.ofAdd (-4, 0, -1, 2)

theorem d3g1_mem : d3g1 ∈ MonoidHom.ker deep3Height := by
  rw [MonoidHom.mem_ker]; rfl
theorem d3g2_mem : d3g2 ∈ MonoidHom.ker deep3Height := by
  rw [MonoidHom.mem_ker]; rfl
theorem d3g3_mem : d3g3 ∈ MonoidHom.ker deep3Height := by
  rw [MonoidHom.mem_ker]; rfl

/-- **THE LATTICE FACTORIZATION at depth 3** (GENTOW5_PROOF S2.3 step (3)'s letter
computation, exponent level, PROVED): every cocycle value `τ₃(a, b)` is an exact
`ℤ`-monomial in the three letters. The exponents are forced by the height identity and the
gcd chain (here: parity descent `b₂ → b₁ → i₀`, each pivot `e_{j+1} = 2`). -/
theorem deep3_tau_descent (a b : ℤ) :
    ∃ c1 c2 c3 : ℤ, deep3Section.tau a b = d3g1 ^ c1 * d3g2 ^ c2 * d3g3 ^ c3 := by
  have ha := d3_height_id a
  have hb := d3_height_id b
  have hab := d3_height_id (a + b)
  -- the τ exponent vector
  set w1 := d3a a + d3a b - d3a (a + b) with hw1
  set w2 := d3i0 a + d3i0 b - d3i0 (a + b) with hw2
  set w3 := d3b1 a + d3b1 b - d3b1 (a + b) with hw3
  set w4 := d3b2 a + d3b2 b - d3b2 (a + b) with hw4
  refine ⟨(w2 + (w3 + w4 / 2) / 2) / 2, (w3 + w4 / 2) / 2, w4 / 2, ?_⟩
  have hzero : 8 * w1 + 4 * w2 + 10 * w3 + 21 * w4 = 0 := by
    simp only [hw1, hw2, hw3, hw4]; omega
  apply Multiplicative.toAdd.injective
  simp only [NormSection.tau, deep3Section, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd,
    d3g1, d3g2, d3g3, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- τ₃-values have height zero (corollary of the descent + the letters' memberships). -/
theorem deep3_tau_mem_ker (a b : ℤ) :
    deep3Section.tau a b ∈ MonoidHom.ker deep3Height := by
  obtain ⟨c1, c2, c3, hc⟩ := deep3_tau_descent a b
  rw [hc]
  exact mul_mem (mul_mem (zpow_mem d3g1_mem c1) (zpow_mem d3g2_mem c2)) (zpow_mem d3g3_mem c3)

/-- **`(H-VARTHETA-RES)₃`, REDUCED TO THE THREE LETTER-MEMBERSHIPS** (the `i = 3` instance of
the ledger row, exponent level): any ambient residue datum sending `γ₁, γ₂, γ₃` into the
embedded `K` discharges the sitewise carrier at EVERY use-height `q`. The corpus's canonical
read supplies exactly these three memberships (`η, z₂, z₃` — `ψ`-roots in `K₃`); an
adversarial `ρ` genuinely fails them (`om8_vartheta_deep.py` LEG D2), which is why they are
hypotheses and not theorems here. -/
theorem hvarthetaRes_deep3 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ρ : MonoidHom.ker deep3Height →* Lˣ)
    (h1 : ∃ u : Kˣ, ((ρ ⟨d3g1, d3g1_mem⟩ : Lˣ) : L) = algebraMap K L (u : K))
    (h2 : ∃ u : Kˣ, ((ρ ⟨d3g2, d3g2_mem⟩ : Lˣ) : L) = algebraMap K L (u : K))
    (h3 : ∃ u : Kˣ, ((ρ ⟨d3g3, d3g3_mem⟩ : Lˣ) : L) = algebraMap K L (u : K))
    (q : ℤ) :
    HVarthetaRes Deep3 K L deep3Section deep3Height ρ q := by
  obtain ⟨u1, hu1⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  obtain ⟨u3, hu3⟩ := h3
  refine hvarthetaRes_of_tau_letters deep3Height ρ q
    (fun s => deep3_tau_mem_ker ((s : ℤ) * q) q) (fun s => ?_)
  obtain ⟨c1, c2, c3, hc⟩ := deep3_tau_descent ((s : ℤ) * q) q
  refine ⟨u1 ^ c1 * u2 ^ c2 * u3 ^ c3, ?_⟩
  have hsub : (⟨deep3Section.tau ((s : ℤ) * q) q,
        deep3_tau_mem_ker ((s : ℤ) * q) q⟩ : MonoidHom.ker deep3Height)
      = ⟨d3g1, d3g1_mem⟩ ^ c1 * ⟨d3g2, d3g2_mem⟩ ^ c2 * ⟨d3g3, d3g3_mem⟩ ^ c3 := by
    apply Subtype.ext
    push_cast
    exact hc
  rw [hsub, map_mul, map_mul, map_zpow, map_zpow, map_zpow, Units.val_mul, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
    hu1, hu2, hu3, Units.val_mul, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_mul, map_mul,
    map_zpow₀, map_zpow₀, map_zpow₀]

/-! ## 3′. The depth-2 letter-lattice model (the `i = 2` transcription)

`EFF.GENTOW2.42`'s γ-calculus, exponent level: "the value-0 Laurent monomials `x^i π^a Φ′^b`
form exactly the group `⟨γ₁, γ₂⟩`" — the depth-2 instance of the same descent, on the
GENTOW2/LW3 sub-chain (`e = (2,2)`, `h = 1`, `u = (1,5)`; `dv₂`-coefficients `(4, 2, 5)` on
`(π, x, Φ₁)`). This is the `i = 2` corpus proof's lattice core, transcribed. -/

/-- The depth-2 exponent group: `(a, i₀, b₁)` = the exponents of `(π, x, Φ₁)`. -/
abbrev Deep2 := Multiplicative (ℤ × ℤ × ℤ)

/-- The `dv₂` height homomorphism: `4a + 2i₀ + 5b₁`. -/
def deep2Height : Deep2 →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd
    (4 * (Multiplicative.toAdd g).1 + 2 * (Multiplicative.toAdd g).2.1
      + 5 * (Multiplicative.toAdd g).2.2)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ← ofAdd_add]
    ring_nf

/-- `b₁(k)` at depth 2 (`u₂ = 5` odd, `e₂ = 2`). -/
def d2b1 (k : ℤ) : ℤ := k % 2
/-- the level-1 residual height at depth 2. -/
def d2m1 (k : ℤ) : ℤ := (k - 5 * d2b1 k) / 2
/-- `i₀(k)` at depth 2. -/
def d2i0 (k : ℤ) : ℤ := d2m1 k % 2
/-- `a(k)` at depth 2. -/
def d2a (k : ℤ) : ℤ := (d2m1 k - d2i0 k) / 2

/-- The depth-2 exact-height identity `4a(k) + 2i₀(k) + 5b₁(k) = k`. -/
theorem d2_height_id (k : ℤ) : 4 * d2a k + 2 * d2i0 k + 5 * d2b1 k = k := by
  simp only [d2a, d2i0, d2m1, d2b1]
  omega

/-- The depth-2 tower normalizer section (`n̂₂`, greedy exponents — GENTOW-1 S3's `n̂₂`). -/
def deep2Section : NormSection Deep2 where
  n k := Multiplicative.ofAdd (d2a k, d2i0 k, d2b1 k)
  n_zero := by
    have : d2a 0 = 0 ∧ d2i0 0 = 0 ∧ d2b1 0 = 0 := by
      simp only [d2a, d2i0, d2m1, d2b1]; omega
    simp [this.1, this.2.1, this.2.2]

/-- Letter `γ₁ = x²/π` at depth 2. -/
def d2g1 : Deep2 := Multiplicative.ofAdd (-1, 2, 0)
/-- Letter `γ₂ = Φ₁²/(π²x)` at depth 2 (`EFF.GENTOW2.42`'s second generator). -/
def d2g2 : Deep2 := Multiplicative.ofAdd (-2, -1, 2)

theorem d2g1_mem : d2g1 ∈ MonoidHom.ker deep2Height := by
  rw [MonoidHom.mem_ker]; rfl
theorem d2g2_mem : d2g2 ∈ MonoidHom.ker deep2Height := by
  rw [MonoidHom.mem_ker]; rfl

/-- **The depth-2 lattice factorization** (GENTOW2-B″'s γ-calculus core, PROVED): every
`τ₂(a,b)` is an exact `ℤ`-monomial in `γ₁, γ₂`. -/
theorem deep2_tau_descent (a b : ℤ) :
    ∃ c1 c2 : ℤ, deep2Section.tau a b = d2g1 ^ c1 * d2g2 ^ c2 := by
  have ha := d2_height_id a
  have hb := d2_height_id b
  have hab := d2_height_id (a + b)
  set w1 := d2a a + d2a b - d2a (a + b) with hw1
  set w2 := d2i0 a + d2i0 b - d2i0 (a + b) with hw2
  set w3 := d2b1 a + d2b1 b - d2b1 (a + b) with hw3
  refine ⟨(w2 + w3 / 2) / 2, w3 / 2, ?_⟩
  have hzero : 4 * w1 + 2 * w2 + 5 * w3 = 0 := by
    simp only [hw1, hw2, hw3]; omega
  apply Multiplicative.toAdd.injective
  simp only [NormSection.tau, deep2Section, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd,
    d2g1, d2g2, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨by omega, by omega, by omega⟩

theorem deep2_tau_mem_ker (a b : ℤ) :
    deep2Section.tau a b ∈ MonoidHom.ker deep2Height := by
  obtain ⟨c1, c2, hc⟩ := deep2_tau_descent a b
  rw [hc]
  exact mul_mem (zpow_mem d2g1_mem c1) (zpow_mem d2g2_mem c2)

/-- **`(H-VARTHETA-RES)₂`, reduced to the two letter-memberships** — the `i = 2` slice of
`EFF.T1.09` at exponent level (the corpus's GENTOW2-B″ discharge supplies both letters as
`η, z₂ ∈ K₂ˣ`). -/
theorem hvarthetaRes_deep2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ρ : MonoidHom.ker deep2Height →* Lˣ)
    (h1 : ∃ u : Kˣ, ((ρ ⟨d2g1, d2g1_mem⟩ : Lˣ) : L) = algebraMap K L (u : K))
    (h2 : ∃ u : Kˣ, ((ρ ⟨d2g2, d2g2_mem⟩ : Lˣ) : L) = algebraMap K L (u : K))
    (q : ℤ) :
    HVarthetaRes Deep2 K L deep2Section deep2Height ρ q := by
  obtain ⟨u1, hu1⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  refine hvarthetaRes_of_tau_letters deep2Height ρ q
    (fun s => deep2_tau_mem_ker ((s : ℤ) * q) q) (fun s => ?_)
  obtain ⟨c1, c2, hc⟩ := deep2_tau_descent ((s : ℤ) * q) q
  refine ⟨u1 ^ c1 * u2 ^ c2, ?_⟩
  have hsub : (⟨deep2Section.tau ((s : ℤ) * q) q,
        deep2_tau_mem_ker ((s : ℤ) * q) q⟩ : MonoidHom.ker deep2Height)
      = ⟨d2g1, d2g1_mem⟩ ^ c1 * ⟨d2g2, d2g2_mem⟩ ^ c2 := by
    apply Subtype.ext
    push_cast
    exact hc
  rw [hsub, map_mul, map_zpow, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, hu1, hu2, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, map_zpow₀]

/-! ## 4. The `𝒲_{≤i}` interleaved-induction skeleton (HYP.63's closure shape) -/

/-- `𝒲_{≤i}`, abstract (byte-matching the leanspec D.55 carrier): `W q` for every
`q ∈ [3, i]`. -/
def Wle (W : ℕ → Prop) (i : ℕ) : Prop := ∀ q, 3 ≤ q → q ≤ i → W q

/-- The empty base `𝒲_{≤2}` — PROVED (an `axiom` stub in leanspec): no `q` satisfies
`3 ≤ q ≤ 2`. -/
theorem wle_two (W : ℕ → Prop) : Wle W 2 := fun _ h3 h2 => absurd (h3.trans h2) (by omega)

/-- **THE INTERLEAVED INDUCTION FROM THE EMPTY BASE** (T5 S12.1's named obligation, as a
machine-checked skeleton). Given
* `base`: clause (b) at index 2 — the landed GENTOW2 record (unconditional);
* `step`: the WI companion's lemma at level `i ≥ 3`, consuming `𝒲_{≤i−1}` material and
  clause (b) at index `i−1` ONLY (its consumption census C-5);
* `chain`: frozen GENTOW5's `𝒲_{≤n} ⟹ (a)@n ⟹ Cor 6.4 ⟹ (b)@n` (T5 §4, (WF-chain));

the cumulative `𝒲_{≤n}` holds for every `n`. The suppliers stay at their own grades — this
theorem contributes exactly the closure arithmetic that T5 S12.1 records as "NOT performed by
the companion as written". -/
theorem wle_of_interleaved (W B : ℕ → Prop) (base : B 2)
    (step : ∀ i, 3 ≤ i → Wle W (i - 1) → B (i - 1) → W i)
    (chain : ∀ i, 3 ≤ i → Wle W i → B i) :
    ∀ n, Wle W n := by
  have main : ∀ n, 2 ≤ n → Wle W n ∧ B n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨wle_two W, base⟩
    | succ n hn ih =>
      obtain ⟨hW, hB⟩ := ih
      have h3 : 3 ≤ n + 1 := by omega
      have hstep : W (n + 1) := by
        have hpred : n + 1 - 1 = n := by omega
        exact step (n + 1) h3 (by rw [hpred]; exact hW) (by rw [hpred]; exact hB)
      have hWle : Wle W (n + 1) := by
        intro q hq3 hqn
        rcases Nat.lt_or_ge q (n + 1) with hlt | hge
        · exact hW q hq3 (by omega)
        · have : q = n + 1 := by omega
          rw [this]; exact hstep
      exact ⟨hWle, chain (n + 1) h3 hWle⟩
  intro n
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exact fun q h3 hq => absurd (h3.trans hq) (by omega)
  · exact (main n hge).1

/-- Display A's `∀ i ≥ 3` conjunct, assembled (D.63's signature, byte-matching leanspec). -/
def VarthetaWConjunct (HVR W : ℕ → Prop) (i : ℕ) : Prop := HVR i ∧ Wle W i

/-! ## 5. The general-depth structural core (every `i`, abstract)

The `∀ i ≥ 3` law's arithmetic skeleton, PROVED at every depth: (a) `triangular_descent` —
a value-zero exponent vector against a triangular generator system with per-stage
divisibility factors EXACTLY over the generators (the depth-`d` letter-lattice
factorization, of which §3/§3′ are the `d = 3, 2` tower instances); (b) `dvd_stage` — the
per-stage divisibility IS the gcd chain (`gcd(u_{j+1}, e_{j+1}) = 1`), i.e. the number-
theoretic input at each rung of ANY DEF GENTOW5-1 datum. Together: for every depth, every
value-zero monomial in `(π, x, Φ₁, …, Φ_{i−1})` is an exact letter monomial — "standard
MacLane residual specialization" (`EFF.T1.09` R9-2's phrase), exponent level, all `i`.
Exponent vectors are `ℕ → ℤ` with bounded support (no `Fin`-casts); sums are `Finset.range`
sums. Instantiating the two lemmas at a concrete chain is routine (§3/§3′ show the shape);
the full chain-indexed instantiation (greedy `n̂` over stage lists + its exact-height law)
is left to the ChapD fleet — disclosed in the OM-8 unit note §3.3. -/

/-- Support bound: `w k = 0` above `n`. -/
def SuppLE (w : ℕ → ℤ) (n : ℕ) : Prop := ∀ k, n < k → w k = 0

/-- **The per-stage divisibility from the gcd chain** (the rung law): if every lower
coefficient is divisible by `M * e`, the pivot coefficient is `M * u` with `u` coprime to
`e`, and the vector is value-zero with support through the pivot, then `e` divides the pivot
exponent. In the tower: `M = ê_d/ê_{j+1}`, `e = e_{j+1}`, `u = u_{j+1}` — the divisibility
that drives the descent at rung `j`. -/
theorem dvd_stage (c : ℕ → ℤ) (j : ℕ) (M e u : ℤ) (hM : M ≠ 0)
    (hcop : IsCoprime u e)
    (hlow : ∀ k, k ≤ j → (M * e) ∣ c k) (hpivc : c (j + 1) = M * u)
    (w : ℕ → ℤ) (hsum : ∑ k ∈ Finset.range (j + 2), c k * w k = 0) :
    e ∣ w (j + 1) := by
  have hsplit : ∑ k ∈ Finset.range (j + 2), c k * w k
      = (∑ k ∈ Finset.range (j + 1), c k * w k) + c (j + 1) * w (j + 1) :=
    Finset.sum_range_succ _ _
  have hlowdvd : (M * e) ∣ ∑ k ∈ Finset.range (j + 1), c k * w k := by
    refine Finset.dvd_sum fun k hk => ?_
    exact Dvd.dvd.mul_right (hlow k (by
      have := Finset.mem_range.mp hk; omega)) _
  have hMe : (M * e) ∣ M * u * w (j + 1) := by
    have : M * u * w (j + 1) = -(∑ k ∈ Finset.range (j + 1), c k * w k) := by
      rw [← hpivc]; omega
    rw [this]
    exact hlowdvd.neg_right
  have he : e ∣ u * w (j + 1) := by
    rcases hMe with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have : M * (u * w (j + 1)) = M * (e * t) := by ring_nf; ring_nf at ht; linarith
    exact mul_left_cancel₀ hM this
  exact (hcop.symm.dvd_of_dvd_mul_left he)

/-- **The general-depth triangular descent** (the letter-lattice factorization, every
depth): given a height functional `c` with `c 0 ≠ 0`, and for each rung `j < d` a generator
`γ j` that is value-zero, supported through its pivot `j+1`, with pivot entry `e j`, and
given the per-stage divisibility (supplied by `dvd_stage` at tower instances), EVERY
value-zero vector supported in `[0, d]` factors over the generators. -/
theorem triangular_descent (c : ℕ → ℤ) (hc0 : c 0 ≠ 0) :
    ∀ (d : ℕ) (e : ℕ → ℤ) (γ : ℕ → ℕ → ℤ),
    (∀ j, j < d → γ j (j + 1) = e j) →
    (∀ j, j < d → SuppLE (γ j) (j + 1)) →
    (∀ j, j < d → ∑ k ∈ Finset.range (j + 2), c k * γ j k = 0) →
    (∀ j, j < d → ∀ w : ℕ → ℤ,
      (∑ k ∈ Finset.range (j + 2), c k * w k = 0) → e j ∣ w (j + 1)) →
    ∀ w : ℕ → ℤ, SuppLE w d → (∑ k ∈ Finset.range (d + 1), c k * w k = 0) →
    ∃ a : ℕ → ℤ, ∀ k, w k = ∑ j ∈ Finset.range d, a j * γ j k := by
  intro d
  induction d with
  | zero =>
    intro e γ _ _ _ _ w hsupp hval
    refine ⟨0, fun k => ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : c 0 * w 0 = 0 := by simpa using hval
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc0
      · exact h
    · exact hsupp k hk
  | succ d ih =>
    intro e γ hpiv htri hval hdvd w hsupp hwv
    -- top-rung divisibility
    have htop : e d ∣ w (d + 1) := by
      refine hdvd d (by omega) w ?_
      exact hwv
    obtain ⟨q, hq⟩ := htop
    -- peel the top generator
    set w' : ℕ → ℤ := fun k => w k - q * γ d k with hw'
    have hsupp' : SuppLE w' d := by
      intro k hk
      rcases Nat.lt_or_ge k (d + 2) with hk2 | hk2
      · have hkd : k = d + 1 := by omega
        subst hkd
        simp only [hw', hpiv d (by omega), hq]
        ring
      · simp only [hw', hsupp k (by omega), htri d (by omega) k (by omega)]
        ring
    have hval' : ∑ k ∈ Finset.range (d + 1), c k * w' k = 0 := by
      have hext : ∑ k ∈ Finset.range (d + 2), c k * w' k
          = ∑ k ∈ Finset.range (d + 1), c k * w' k := by
        rw [Finset.sum_range_succ, hsupp' (d + 1) (by omega)]
        ring
      rw [← hext]
      have : ∑ k ∈ Finset.range (d + 2), c k * w' k
          = (∑ k ∈ Finset.range (d + 2), c k * w k)
            - q * ∑ k ∈ Finset.range (d + 2), c k * γ d k := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [hw']; ring
      rw [this, hwv, hval d (by omega)]
      ring
    obtain ⟨a', ha'⟩ := ih e γ (fun j hj => hpiv j (by omega))
      (fun j hj => htri j (by omega)) (fun j hj => hval j (by omega))
      (fun j hj => hdvd j (by omega)) w' hsupp' hval'
    refine ⟨fun j => if j = d then q else a' j, fun k => ?_⟩
    rw [Finset.sum_range_succ]
    have hlow : ∑ j ∈ Finset.range d, (if j = d then q else a' j) * γ j k
        = ∑ j ∈ Finset.range d, a' j * γ j k :=
      Finset.sum_congr rfl fun j hj => by
        rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
    rw [hlow, ← ha' k]
    beta_reduce
    rw [if_pos rfl]
    simp only [hw']
    ring

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.hvarthetaRes_of_tau_letters
#print axioms Uniformity.Density.Gauge.hvarthetaRes_levelOne
#print axioms Uniformity.Density.Gauge.deep3_exact_height
#print axioms Uniformity.Density.Gauge.deep3_tau_descent
#print axioms Uniformity.Density.Gauge.hvarthetaRes_deep3
#print axioms Uniformity.Density.Gauge.deep2_tau_descent
#print axioms Uniformity.Density.Gauge.hvarthetaRes_deep2
#print axioms Uniformity.Density.Gauge.wle_of_interleaved
#print axioms Uniformity.Density.Gauge.dvd_stage
#print axioms Uniformity.Density.Gauge.triangular_descent

end AxCheck
