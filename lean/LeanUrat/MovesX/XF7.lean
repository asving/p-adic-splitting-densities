/-
Unit XF.7 tailCountBound — (3b-LEAN), UNCONDITIONAL (Ruling 2 — no V argument)
[PROVED: body complete and axiom-clean]
moves_ref: "(3b) μ{f monic deg n : v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}"
(auditor-confirmed arithmetic: 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at
(3,3,5/7/9)).
sketch: fiber over aTail ∈ (ZMod p^D)^{n−1} (XF.1); INSIDE the proof,
`valExtOf (fTail n p _ aTail)` (fTail ≠ 0: lead coeff n ≠ 0 in char 0) discharges
XF.6's V; ≤ (n−1)·p^{D−tailExp.toNat} residues per fiber; trivial-face check at
tailExp ≤ 0. deps: XF.1, XF.6, XF.3. difficulty: MEDIUM-HARD (carries XF.3's
stuck-risk — by ruling, a STUCK report, not a rider).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF1
import LeanUrat.MovesX.XF3
import LeanUrat.MovesX.XF6

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- Trivial upper bound: the number of discriminant-zero coefficient tuples is at most
the number of all coefficient tuples `(ZMod (p^D))^n = p^(n*D)`. -/
private lemma tailCount_le_pow (p n D : ℕ) [Fact p.Prime] :
    tailCount p n D ≤ p ^ (n * D) := by
  haveI : NeZero (p ^ D) := ⟨pow_ne_zero D (Nat.Prime.ne_zero (Fact.out))⟩
  have hle : tailCount p n D ≤ Nat.card (Fin n → ZMod (p ^ D)) := by
    unfold tailCount
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  calc tailCount p n D ≤ Nat.card (Fin n → ZMod (p ^ D)) := hle
    _ = p ^ (n * D) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card,
          Fintype.card_fin, ← pow_mul, Nat.mul_comm D n]

/-- `tailExp ≤ D` for `n ≥ 2`: the ceiling of `(D − n·v_p(n))/(n−1)` never exceeds `D`. -/
private lemma tailExp_le_D (p n D : ℕ) (h2 : 2 ≤ n) :
    tailExp p n D ≤ (D : ℤ) := by
  unfold tailExp
  rw [Int.ceil_le]
  rw [div_le_iff₀ (by
    have : (1 : ℚ) ≤ (n : ℚ) - 1 := by
      have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
      linarith
    linarith)]
  push_cast
  have hv : (0 : ℚ) ≤ (padicValNat p n : ℚ) := by positivity
  have hn2 : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
  nlinarith [hv, hn2, (by positivity : (0:ℚ) ≤ (D:ℚ))]

open Polynomial in
/-- The lower part `∑ aᵢ Xⁱ` of a `polyOfCoeffs` has degree `< n`. -/
private lemma polyOfCoeffs_lower_degree_lt {R : Type} [CommRing R] {n : ℕ} (hn : 1 ≤ n)
    (a : Fin n → R) :
    (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
  intro i _
  calc (Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      ≤ ((i : ℕ) : WithBot ℕ) := Polynomial.degree_C_mul_X_pow_le _ _
    _ < (n : WithBot ℕ) := by exact_mod_cast i.2

open Polynomial in
/-- `polyOfCoeffs R n a` is monic for `n ≥ 1`. -/
private lemma polyOfCoeffs_monic {R : Type} [CommRing R] {n : ℕ} (hn : 1 ≤ n)
    (a : Fin n → R) : (polyOfCoeffs R n a).Monic := by
  unfold polyOfCoeffs
  exact Polynomial.monic_X_pow_add (polyOfCoeffs_lower_degree_lt hn a)

open Polynomial in
/-- `polyOfCoeffs R n a` has `natDegree = n` for `n ≥ 1` over a nontrivial ring. -/
private lemma polyOfCoeffs_natDegree {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 1 ≤ n) (a : Fin n → R) : (polyOfCoeffs R n a).natDegree = n := by
  unfold polyOfCoeffs
  have hlt : (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      < (Polynomial.X ^ n : Polynomial R).degree := by
    rw [Polynomial.degree_X_pow]; exact polyOfCoeffs_lower_degree_lt hn a
  rw [Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt hlt),
    Polynomial.natDegree_X_pow]

open Polynomial in
/-- `fTail` (the mapped derivative of the tail-family member) is nonzero: its underlying
monic polynomial has degree `n ≥ 2`, and over the characteristic-zero field `ℚ_[p]` a
polynomial of positive degree has nonzero derivative. -/
private lemma fTail_ne_zero (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (h2 : 2 ≤ n)
    (aTail : Fin (n - 1) → ℤ_[p]) : fTail n p hn aTail ≠ 0 := by
  intro hz
  unfold fTail at hz
  have hmap_deg : ((polyOfCoeffs ℤ_[p] n ((Fin.cons 0 aTail) ∘
      Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom).natDegree = n := by
    rw [Polynomial.Monic.natDegree_map (polyOfCoeffs_monic hn _)]
    exact polyOfCoeffs_natDegree hn _
  have hd0 := Polynomial.derivative_eq_zero.mp hz
  rw [hmap_deg] at hd0
  omega

/-- A fiber of the reduction map `ZMod (p^D) → ZMod (p^k)` has at most `p^(D-k)` elements
(for `k ≤ D`). Proof: `x ↦ x.val / p^k` injects the fiber into `range (p^(D-k))`, since
within a fiber `x.val % p^k` is fixed. -/
private lemma cast_fiber_card_le (p k D : ℕ) [Fact p.Prime] (hkD : k ≤ D)
    (c : ZMod (p ^ k)) :
    (Finset.univ.filter (fun x : ZMod (p ^ D) => (x.cast : ZMod (p ^ k)) = c)).card
      ≤ p ^ (D - k) := by
  haveI : NeZero (p ^ D) := ⟨pow_ne_zero D (Nat.Prime.ne_zero Fact.out)⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Nat.Prime.ne_zero Fact.out)⟩
  have hp0 : 0 < p := Nat.Prime.pos Fact.out
  have hpk0 : 0 < p ^ k := pow_pos hp0 k
  have hval_cast : ∀ x : ZMod (p ^ D), (x.cast : ZMod (p ^ k)).val = x.val % p ^ k := by
    intro x
    rw [← ZMod.natCast_val x, ZMod.val_natCast]
  have hmaps : Set.MapsTo (fun x : ZMod (p ^ D) => x.val / p ^ k)
      ↑(Finset.univ.filter (fun x : ZMod (p ^ D) => (x.cast : ZMod (p ^ k)) = c))
      ↑(Finset.range (p ^ (D - k))) := by
    intro x _
    simp only [Finset.coe_range, Set.mem_Iio]
    rw [Nat.div_lt_iff_lt_mul hpk0]
    calc x.val < p ^ D := ZMod.val_lt x
      _ = p ^ (D - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hkD]
  have hinj : Set.InjOn (fun x : ZMod (p ^ D) => x.val / p ^ k)
      ↑(Finset.univ.filter (fun x : ZMod (p ^ D) => (x.cast : ZMod (p ^ k)) = c)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    apply ZMod.val_injective
    have hmod : x.val % p ^ k = y.val % p ^ k := by
      rw [← hval_cast x, ← hval_cast y, hx, hy]
    have hdiv : x.val / p ^ k = y.val / p ^ k := hxy
    calc x.val = p ^ k * (x.val / p ^ k) + x.val % p ^ k := (Nat.div_add_mod x.val (p ^ k)).symm
      _ = p ^ k * (y.val / p ^ k) + y.val % p ^ k := by rw [hdiv, hmod]
      _ = y.val := Nat.div_add_mod y.val (p ^ k)
  calc (Finset.univ.filter (fun x : ZMod (p ^ D) => (x.cast : ZMod (p ^ k)) = c)).card
      ≤ (Finset.range (p ^ (D - k))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = p ^ (D - k) := Finset.card_range _

/-- Reconstruct a tuple `a : Fin n → R` from its head `a₀` and tail via `Fin.cons`/`Fin.cast`
(the exact shape used by `Event`/`fTail`). -/
private lemma cons_cast_reconstruct {R : Type} {n : ℕ} (hcast : n = n - 1 + 1) (a : Fin n → R) :
    ((Fin.cons (a (Fin.cast hcast.symm 0)) (fun j => a (Fin.cast hcast.symm j.succ))
      : Fin (n - 1 + 1) → R)) ∘ Fin.cast hcast = a := by
  have hb : ((Fin.cons (a (Fin.cast hcast.symm 0)) (fun j => a (Fin.cast hcast.symm j.succ))
      : Fin (n - 1 + 1) → R)) = a ∘ Fin.cast hcast.symm :=
    Fin.cons_self_tail (a ∘ Fin.cast hcast.symm)
  rw [hb]
  funext i
  simp only [Function.comp_apply]
  congr 1

open Polynomial in
/-- Coefficient extraction: `(polyOfCoeffs R n c).coeff i = c i` for `i : Fin n`. -/
private lemma polyOfCoeffs_coeff {R : Type} [CommRing R] {n : ℕ} (c : Fin n → R) (i : Fin n) :
    (polyOfCoeffs R n c).coeff (i : ℕ) = c i := by
  unfold polyOfCoeffs
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (i : ℕ) = n), zero_add,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hji (Fin.ext h.symm)), mul_zero]
  · intro hcontra; exact absurd (Finset.mem_univ i) hcontra

/-- THE crux (fiber-count): for `tailExp > 0`, the number of discriminant-zero tuples is
at most `(n−1)·p^(n·D − tailExp.toNat)`. Proof plan: fiber over the tail coefficients
`aTail ∈ (ZMod p^D)^{n−1}`; for each fiber, lift residues to `ℤ_[p]`, use `discCylinder`
(XF.1) to convert the ZMod discriminant-zero condition to the level-`D` `Event`, feed
`valExtOf` (XF.3) into `ballCover` (XF.6) to split the surviving `a₀`-residues into
`≤ n−1` classes each pinned mod `p^tailExp.toNat`, hence `≤ p^(D − tailExp.toNat)` per
class. -/
private lemma fiber_count (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n)
    (hpos : 0 < tailExp p n D) :
    tailCount p n D ≤ (n - 1) * p ^ (n * D - (tailExp p n D).toNat) := by
  classical
  haveI : NeZero (p ^ D) := ⟨pow_ne_zero D (Nat.Prime.ne_zero Fact.out)⟩
  have hn1 : 1 ≤ n := by omega
  have hcast : n = n - 1 + 1 := by omega
  set k := (tailExp p n D).toNat with hk
  have hkD : k ≤ D := by have := tailExp_le_D p n D h2; omega
  -- decomposition maps: head coefficient and tail
  set cst : (Fin n → ZMod (p ^ D)) → ZMod (p ^ D) := fun a => a (Fin.cast hcast.symm 0) with hcst
  set tl : (Fin n → ZMod (p ^ D)) → (Fin (n - 1) → ZMod (p ^ D)) :=
    fun a j => a (Fin.cast hcast.symm j.succ) with htl
  have hrec : ∀ a : Fin n → ZMod (p ^ D),
      (Fin.cons (cst a) (tl a) : Fin (n - 1 + 1) → ZMod (p ^ D)) ∘ Fin.cast hcast = a :=
    fun a => cons_cast_reconstruct hcast a
  have hrec_inj : ∀ a b : Fin n → ZMod (p ^ D), cst a = cst b → tl a = tl b → a = b := by
    intro a b hc ht
    have ea : a = (Fin.cons (cst a) (tl a) : Fin (n - 1 + 1) → ZMod (p ^ D)) ∘ Fin.cast hcast :=
      (hrec a).symm
    have eb : b = (Fin.cons (cst b) (tl b) : Fin (n - 1 + 1) → ZMod (p ^ D)) ∘ Fin.cast hcast :=
      (hrec b).symm
    rw [ea, eb, hc, ht]
  -- the discriminant-zero count as a Finset
  have htc : tailCount p n D
      = (Finset.univ.filter
          (fun a : Fin n → ZMod (p ^ D) => (polyOfCoeffs (ZMod (p ^ D)) n a).discr = 0)).card := by
    unfold tailCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set S := Finset.univ.filter
    (fun a : Fin n → ZMod (p ^ D) => (polyOfCoeffs (ZMod (p ^ D)) n a).discr = 0) with hS
  -- per-tail-fiber bound
  have per_fiber : ∀ aTail : Fin (n - 1) → ZMod (p ^ D),
      (S.filter (fun a => tl a = aTail)).card ≤ (n - 1) * p ^ (D - k) := by
    intro aTail
    set aTailZ : Fin (n - 1) → ℤ_[p] := fun j => ((aTail j).val : ℤ_[p]) with haTZ
    have hg : fTail n p hn1 aTailZ ≠ 0 := fTail_ne_zero p n hn1 h2 aTailZ
    obtain ⟨idx, hidx⟩ := ballCover p n D h2 aTailZ (valExtOf p (fTail n p hn1 aTailZ) hg)
    -- Event bridge: discriminant-zero residues become level-D events
    have hevent : ∀ a ∈ S.filter (fun a => tl a = aTail),
        Event p n D hn1 aTailZ (((cst a).val : ℕ) : ℤ_[p]) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haS, haT⟩ := ha
      rw [hS, Finset.mem_filter] at haS
      have hdisc : (polyOfCoeffs (ZMod (p ^ D)) n a).discr = 0 := haS.2
      unfold Event
      have hpush : ∀ x : Fin (n - 1 + 1),
          PadicInt.toZModPow D
              ((Fin.cons (((cst a).val : ℕ) : ℤ_[p]) aTailZ : Fin (n - 1 + 1) → ℤ_[p]) x)
            = (Fin.cons (cst a) aTail : Fin (n - 1 + 1) → ZMod (p ^ D)) x := by
        intro x
        induction x using Fin.cases with
        | zero =>
          rw [Fin.cons_zero, Fin.cons_zero, map_natCast]
          simp [ZMod.natCast_val, ZMod.cast_id]
        | succ j =>
          rw [Fin.cons_succ, Fin.cons_succ]
          simp only [haTZ, map_natCast]
          simp [ZMod.natCast_val, ZMod.cast_id]
      rw [discCylinder p n D hn1 _ (polyOfCoeffs_monic hn1 _) (polyOfCoeffs_natDegree hn1 _)]
      have hcoeff_eq : (fun i : Fin n =>
          PadicInt.toZModPow D ((polyOfCoeffs ℤ_[p] n
            ((Fin.cons (((cst a).val : ℕ) : ℤ_[p]) aTailZ) ∘
              Fin.cast (by omega : n = n - 1 + 1))).coeff (i : ℕ))) = a := by
        funext i
        rw [polyOfCoeffs_coeff]
        simp only [Function.comp_apply]
        rw [hpush, ← haT]
        exact congrFun (hrec a) i
      rw [hcoeff_eq]
      exact hdisc
    -- cast equality from ballCover: same index ⟹ congruent mod p^k
    have hcasteq : ∀ a ∈ S.filter (fun a => tl a = aTail),
        ∀ b ∈ S.filter (fun a => tl a = aTail),
        idx (((cst a).val : ℕ) : ℤ_[p]) = idx (((cst b).val : ℕ) : ℤ_[p]) →
        ((cst a).cast : ZMod (p ^ k)) = (cst b).cast := by
      intro a ha b hb hidxeq
      have hdvd := hidx (((cst a).val : ℕ) : ℤ_[p]) (((cst b).val : ℕ) : ℤ_[p])
        (hevent a ha) (hevent b hb) hidxeq
      have hker : (PadicInt.toZModPow k)
          ((((cst a).val : ℕ) : ℤ_[p]) - (((cst b).val : ℕ) : ℤ_[p])) = 0 := by
        rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
        exact hdvd
      rw [map_sub, map_natCast, map_natCast, ZMod.natCast_val, ZMod.natCast_val,
        sub_eq_zero] at hker
      exact hker
    -- fiber over the index, bound each class by a reduction-fiber
    rw [Finset.card_eq_sum_card_fiberwise
        (f := fun a => idx (((cst a).val : ℕ) : ℤ_[p]))
        (t := (Finset.univ : Finset (Fin (n - 1))))
        (fun a _ => Finset.mem_univ _)]
    calc ∑ j : Fin (n - 1),
            ((S.filter (fun a => tl a = aTail)).filter
              (fun a => idx (((cst a).val : ℕ) : ℤ_[p]) = j)).card
        ≤ ∑ _j : Fin (n - 1), p ^ (D - k) := by
          apply Finset.sum_le_sum
          intro j _
          rcases (((S.filter (fun a => tl a = aTail)).filter
            (fun a => idx (((cst a).val : ℕ) : ℤ_[p]) = j))).eq_empty_or_nonempty with hE | ⟨a0, ha0⟩
          · rw [hE]; simp
          · have hmaps : ∀ a ∈ (S.filter (fun a => tl a = aTail)).filter
                (fun a => idx (((cst a).val : ℕ) : ℤ_[p]) = j),
                ((cst a).cast : ZMod (p ^ k)) = (cst a0).cast := by
              intro a ha
              rw [Finset.mem_filter] at ha ha0
              exact hcasteq a ha.1 a0 ha0.1 (by rw [ha.2, ha0.2])
            calc ((S.filter (fun a => tl a = aTail)).filter
                    (fun a => idx (((cst a).val : ℕ) : ℤ_[p]) = j)).card
                ≤ (Finset.univ.filter
                    (fun x : ZMod (p ^ D) => (x.cast : ZMod (p ^ k)) = (cst a0).cast)).card := by
                  apply Finset.card_le_card_of_injOn (fun a => cst a)
                  · intro a ha
                    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
                    exact hmaps a ha
                  · intro a ha b hb hab
                    simp only [Finset.coe_filter, Finset.mem_filter,
                      Set.mem_setOf_eq] at ha hb
                    exact hrec_inj a b hab (by rw [ha.1.2, hb.1.2])
              _ ≤ p ^ (D - k) := cast_fiber_card_le p k D hkD _
      _ = (n - 1) * p ^ (D - k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- assemble the tail-fiber sum
  rw [htc, Finset.card_eq_sum_card_fiberwise
      (f := tl) (t := (Finset.univ : Finset (Fin (n - 1) → ZMod (p ^ D))))
      (fun a _ => Finset.mem_univ _)]
  have hexp : D * (n - 1) + (D - k) = n * D - k := by
    have h1 : D * (n - 1) = n * D - D := by rw [Nat.mul_comm, Nat.sub_one_mul]
    have h2' : D ≤ n * D := Nat.le_mul_of_pos_left D (by omega)
    omega
  calc ∑ aTail : Fin (n - 1) → ZMod (p ^ D), (S.filter (fun a => tl a = aTail)).card
      ≤ ∑ _aTail : Fin (n - 1) → ZMod (p ^ D), (n - 1) * p ^ (D - k) :=
        Finset.sum_le_sum (fun aTail _ => per_fiber aTail)
    _ = (Fintype.card (Fin (n - 1) → ZMod (p ^ D))) * ((n - 1) * p ^ (D - k)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = (p ^ D) ^ (n - 1) * ((n - 1) * p ^ (D - k)) := by
        rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    _ = (n - 1) * p ^ (n * D - k) := by
        rw [← pow_mul,
          show (p ^ (D * (n - 1))) * ((n - 1) * p ^ (D - k))
            = (n - 1) * (p ^ (D * (n - 1)) * p ^ (D - k)) from by ring,
          ← pow_add, hexp]

theorem tailCountBound (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) :
    (tailCount p n D : ℚ) * (p : ℚ) ^ (tailExp p n D) ≤
      (n - 1 : ℚ) * (p : ℚ) ^ ((n * D : ℕ) : ℤ) := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
  have hn1 : (1 : ℚ) ≤ (n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
    linarith
  have htriv : tailCount p n D ≤ p ^ (n * D) := tailCount_le_pow p n D
  have htrivQ : (tailCount p n D : ℚ) ≤ (p : ℚ) ^ (n * D) := by exact_mod_cast htriv
  -- (p:ℚ)^((n*D:ℕ):ℤ) = (p:ℚ)^(n*D)
  have hpow : (p : ℚ) ^ ((n * D : ℕ) : ℤ) = (p : ℚ) ^ (n * D) := by
    rw [zpow_natCast]
  rw [hpow]
  set t := tailExp p n D with ht
  rcases le_or_gt t 0 with hle | hpos
  · -- Case t ≤ 0 : p^t ≤ 1
    have hpt : (p : ℚ) ^ t ≤ 1 := by
      calc (p : ℚ) ^ t ≤ (p : ℚ) ^ (0 : ℤ) := by
              apply zpow_le_zpow_right₀ hp1 hle
        _ = 1 := by simp
    calc (tailCount p n D : ℚ) * (p : ℚ) ^ t
          ≤ (tailCount p n D : ℚ) * 1 := by
            apply mul_le_mul_of_nonneg_left hpt (by positivity)
      _ = (tailCount p n D : ℚ) := by ring
      _ ≤ (p : ℚ) ^ (n * D) := htrivQ
      _ ≤ (n - 1 : ℚ) * (p : ℚ) ^ (n * D) := by
            nlinarith [pow_nonneg (le_of_lt hp0) (n * D), hn1]
  · -- Case t > 0 : the fiber count
    have hk_le_D : (t.toNat) ≤ D := by
      have := tailExp_le_D p n D h2
      rw [← ht] at this
      omega
    have hk_le_nD : (t.toNat) ≤ n * D := le_trans hk_le_D (Nat.le_mul_of_pos_left D (by omega))
    have hfiber : tailCount p n D ≤ (n - 1) * p ^ (n * D - t.toNat) := by
      have := fiber_count p n D h2 (by rw [← ht] at *; exact hpos)
      rw [← ht] at this
      exact this
    -- cast to ℚ
    have hn1nat : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hfiberQ : (tailCount p n D : ℚ) ≤ ((n : ℚ) - 1) * (p : ℚ) ^ (n * D - t.toNat) := by
      have := hfiber
      have h2' : (tailCount p n D : ℚ) ≤ ((n - 1 : ℕ) : ℚ) * (p : ℚ) ^ (n * D - t.toNat) := by
        exact_mod_cast this
      rwa [hn1nat] at h2'
    -- p^t = p^(t.toNat)
    have hpt_eq : (p : ℚ) ^ t = (p : ℚ) ^ (t.toNat) := by
      rw [← zpow_natCast (p : ℚ) t.toNat, Int.toNat_of_nonneg (le_of_lt hpos)]
    rw [hpt_eq]
    calc (tailCount p n D : ℚ) * (p : ℚ) ^ (t.toNat)
          ≤ (((n : ℚ) - 1) * (p : ℚ) ^ (n * D - t.toNat)) * (p : ℚ) ^ (t.toNat) := by
            apply mul_le_mul_of_nonneg_right hfiberQ (by positivity)
      _ = ((n : ℚ) - 1) * (p : ℚ) ^ (n * D) := by
            rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk_le_nD]

end LeanUrat.MovesX
