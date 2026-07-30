-- GOLF PASS 2 scratch: footprint capture (BEFORE) + candidate proof tests.
-- DELETE after use.
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.CellCard

#print axioms LeanUrat.OM.OMCountV2.omChildCount_rec
#print axioms LeanUrat.OM.OMCountV2.isRationalFn_compQpow
#print axioms LeanUrat.OM.OMCountV2.omCount_isRational
#print axioms LeanUrat.OM.CellCard.ceilSide_left
#print axioms LeanUrat.OM.CellCard.card_patFinset

namespace LeanUrat.OM.OMCountV2

open LeanUrat LeanUrat.MontesAxiom LeanUrat.RatFn Polynomial
open LeanUrat.OM LeanUrat.OM.Order0

-- candidate: omChildCount_rec
example (T : ClusterShape) (q : ℕ) :
    omChildCount T q
      = (((configsOf T).map (fun c =>
          mCell c q * ((q : ℚ) ^ (volExp c - M6.treeSize T))⁻¹
            * (c.children.map (fun ch =>
                omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum)
        / countPivot (M6.treeSize T) q := by
  rw [omChildCount]
  simp only [List.attach_map_val]

-- candidate: isRationalFn_compQpow (hcast via Nat.cast_pow)
example (k : ℕ) {f : ℕ → ℚ} (hf : IsRationalFn f) :
    IsRationalFn (fun q => f (q ^ k)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using isRationalFn_const (f 1)
  · obtain ⟨num, den, hden, h⟩ := hf
    have hcast : ∀ q : ℕ, ((q ^ k : ℕ) : ℚ) = ((q : ℚ)) ^ k := fun q => Nat.cast_pow q k
    refine ⟨num.comp (Polynomial.X ^ k), den.comp (Polynomial.X ^ k), ?_, fun q hq => ?_⟩
    · -- nonvanishing at 2^k > 1 forces the composed denominator to be nonzero
      intro h0
      have h2 : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega)
      apply (h (2 ^ k) h2).1
      have : (den.comp (Polynomial.X ^ k)).eval ((2 : ℕ) : ℚ) = 0 := by rw [h0]; simp
      rwa [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, ← hcast 2] at this
    · have hqk : 1 < q ^ k := Nat.one_lt_pow (by omega) (by omega)
      obtain ⟨hd, hv⟩ := h (q ^ k) hqk
      constructor
      · rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, ← hcast q]
        exact hd
      · show f (q ^ k) = (num.comp (Polynomial.X ^ k)).eval ((q : ℕ) : ℚ)
            / (den.comp (Polynomial.X ^ k)).eval ((q : ℕ) : ℚ)
        simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
        rw [hv, hcast q]

-- candidate: omCount_isRational (unfold instead of heq)
example (T : ClusterShape) : IsRationalFn (fun q => omCount T q) := by
  unfold omCount
  have hsum := isRationalFn_listSum ((configsOf T).map (fun c => fun q : ℕ =>
      mCell c q * ((q : ℚ) ^ volExp c)⁻¹
        * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)) ?_
  · simpa [List.map_map, Function.comp_def] using hsum
  · intro f hf
    rw [List.mem_map] at hf
    obtain ⟨c, _, rfl⟩ := hf
    refine isRationalFn_mul (isRationalFn_mul (mCell_isRational c) (isRationalFn_invQpow _)) ?_
    have hprod := isRationalFn_listProd (c.children.map (fun ch => fun q : ℕ =>
        omChildCount ch.shape (q ^ (ch.δ * ch.D)))) ?_
    · simpa [List.map_map, Function.comp_def] using hprod
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨ch, _, rfl⟩ := hg
      exact isRationalFn_compQpow _ (omChildCount_isRational ch.shape)

end LeanUrat.OM.OMCountV2

namespace LeanUrat.OM.CellCard

open LeanUrat LeanUrat.OM Polynomial
open LeanUrat.OM.CellMenu

-- candidate: ceilSide_left
example {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    ceilSide pr pr.1.1 = pr.1.2 := by
  simpa using ceilSide_pattern hw hh (t := 0) (Nat.zero_le _)

-- candidate: card_patFinset (reuse pat_pos_mem in the inverse-membership bullet)
example {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) :
    (patFinset s pr).card = sideDeg pr := by
  have he0 := sideE_pos hw hh
  have hde := sideDeg_mul_sideE hw hh
  rw [← Finset.card_range (sideDeg pr)]
  refine Finset.card_bij' (fun i _ => (i.1 - pr.1.1) / sideE pr)
    (fun t ht => ⟨pr.1.1 + t * sideE pr, by
      rw [Finset.mem_range] at ht
      have h1 := pat_pos_lt hw hh ht
      omega⟩) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_patFinset] at hi
    obtain ⟨h1, h2, h3⟩ := hi
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul he0]
    omega
  · intro t ht
    exact (pat_pos_mem hw hh hs (Finset.mem_range.mp ht)).choose_spec
  · intro i hi
    rw [mem_patFinset] at hi
    obtain ⟨h1, h2, h3⟩ := hi
    refine Fin.ext ?_
    show pr.1.1 + (i.1 - pr.1.1) / sideE pr * sideE pr = i.1
    rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h3)]
    omega
  · intro t ht
    rw [Finset.mem_range] at ht
    show (pr.1.1 + t * sideE pr - pr.1.1) / sideE pr = t
    rw [show pr.1.1 + t * sideE pr - pr.1.1 = t * sideE pr from by omega,
      Nat.mul_div_cancel _ he0]

end LeanUrat.OM.CellCard
