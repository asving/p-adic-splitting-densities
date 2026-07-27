/-
Unit Sp.encodeInj — moves_ref: "Every species tuple is determined by an integer
vector with all entries in {0, 1, …, n+1} … Total length ≤ 1 + 3 + 5 + (n+1) + n²
+ 2 + 2n = n² + 3n + 12, each entry taking ≤ n + 2 values".
deps: Sp.compEncode, Sp.lamEncode. sketch: field-by-field recovery: scalar entries
in range by (B5) (d ≤ n+1 the widened entry); λ via lamMatrix; sel via the
reserved (0,0) pair (WellTyped parts ≥ 1 keep it disjoint); flanks via compCuts +
spans s0 / W − s0 − w′ recovered from scalar entries; slots redundant ("kept for
crudeness"). difficulty: medium-hard (split candidate: scalar-block recovery vs
flank/λ blocks if > ~40 lines). Needs `hn : 1 ≤ n` ("n + 2 ≥ 3 for every n ≥ 1" —
the tag entry).

[P-PHASE NOTE] Self-contained: rather than cite the (still-open) deps `compCuts_inj`
and `lamMatrix_inj`, the flanks are encoded POSITIONALLY (part `j` at slot `j`; the
positive-part list is then recovered by an induction, no cut-set injectivity needed)
and `λ` by its `{1..n}²` multiplicity matrix (recovered inline by `Multiset.ext`).
Footprint is Lean-core only (no `sorry`, no `native_decide`, no extra axiom).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-! ### Generic helpers (Lean-core only) -/

/-- Total clamp of a natural into `Fin (n+2)` (reduction mod `n+2`). -/
private def fld (n v : ℕ) : Fin (n + 2) := ⟨v % (n + 2), Nat.mod_lt _ (by omega)⟩

/-- `fld` is injective on values `< n+2`. -/
private theorem fld_inj {n a b : ℕ} (ha : a < n + 2) (hb : b < n + 2)
    (h : fld n a = fld n b) : a = b := by
  simp only [fld, Fin.mk.injEq] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-- `tagord` lands in `{0,1,2}`. -/
private theorem tagord_le (t : Tag) : tagord t ≤ 2 := by cases t <;> simp [tagord]

/-- `tagord` is injective. -/
private theorem tagord_inj {t t' : Tag} (h : tagord t = tagord t') : t = t' := by
  cases t <;> cases t' <;> simp_all [tagord]

/-- first / second component of a selection, `0` on `none` (the reserved value:
`WellTyped` keeps real selections' parts `≥ 1`, so `0` is disjoint from any). -/
private def selFst : Option (ℕ × ℕ) → ℕ
  | none => 0
  | some p => p.1
private def selSnd : Option (ℕ × ℕ) → ℕ
  | none => 0
  | some p => p.2

/-- Two positive-part lists with equal `getD` at every index are equal. -/
private theorem list_pos_getD_ext :
    ∀ (l l' : List ℕ), (∀ x ∈ l, 1 ≤ x) → (∀ x ∈ l', 1 ≤ x) →
      (∀ j, l.getD j 0 = l'.getD j 0) → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' _ hl' h
    cases l' with
    | nil => rfl
    | cons b bs =>
      have h0 := h 0
      simp only [List.getD_cons_zero, List.getD_nil] at h0
      have hb := hl' b (by simp)
      omega
  | cons a as ih =>
    intro l' hl hl' h
    cases l' with
    | nil =>
      have h0 := h 0
      simp only [List.getD_cons_zero, List.getD_nil] at h0
      have ha := hl a (by simp)
      omega
    | cons b bs =>
      have h0 := h 0
      simp only [List.getD_cons_zero] at h0
      have htail : ∀ j, as.getD j 0 = bs.getD j 0 := by
        intro j; have := h (j + 1); simpa using this
      have := ih bs (fun x hx => hl x (by simp [hx])) (fun x hx => hl' x (by simp [hx])) htail
      subst h0; subst this; rfl

/-- Length of a positive-part list is at most its sum. -/
private theorem length_le_sum (l : List ℕ) (h : ∀ x ∈ l, 1 ≤ x) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Any `getD` entry is bounded by the sum of the (natural) list. -/
private theorem getD_le_sum (l : List ℕ) (j : ℕ) : l.getD j 0 ≤ l.sum := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem l 0 hj]
    exact List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getElem_mem hj)
  · rw [List.getD_eq_default l 0 (by omega)]; exact Nat.zero_le _

/-- The multiplicity count of any pair is bounded by the sum of the products. -/
private theorem count_bound (lam : Multiset (ℕ × ℕ)) (g μ : ℕ)
    (hpos : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2) :
    lam.count (g, μ) ≤ (lam.map (fun gm => gm.1 * gm.2)).sum := by
  refine le_trans (Multiset.count_le_card _ _) ?_
  have hcard : lam.card = (lam.map (fun _ => 1)).sum := by simp
  rw [hcard]
  apply Multiset.sum_map_le_sum_map
  intro gm hgm
  obtain ⟨h1, h2⟩ := hpos gm hgm
  calc 1 = 1 * 1 := by ring
    _ ≤ gm.1 * gm.2 := Nat.mul_le_mul h1 h2

/-- Multisets supported in `{1..n}²` with equal counts on the grid are equal. -/
private theorem multiset_grid_ext (n : ℕ) (lam lam' : Multiset (ℕ × ℕ))
    (hsup : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n)
    (hsup' : ∀ gm ∈ lam', 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n)
    (hgrid : ∀ g μ, 1 ≤ g → g ≤ n → 1 ≤ μ → μ ≤ n →
        lam.count (g, μ) = lam'.count (g, μ)) : lam = lam' := by
  apply Multiset.ext.mpr
  intro x
  by_cases hx : 1 ≤ x.1 ∧ x.1 ≤ n ∧ 1 ≤ x.2 ∧ x.2 ≤ n
  · obtain ⟨h1, h2, h3, h4⟩ := hx
    have := hgrid x.1 x.2 h1 h2 h3 h4
    simpa using this
  · rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
    · intro hmem; exact hx (hsup' x hmem)
    · intro hmem; exact hx (hsup x hmem)

/-- Every grid pair `(g,μ)` is hit by some flat index `k < n*n`. -/
private theorem grid_cover (n g μ : ℕ) (hg1 : 1 ≤ g) (hgn : g ≤ n) (hμ1 : 1 ≤ μ) (hμn : μ ≤ n) :
    ∃ k, k < n * n ∧ k / n + 1 = g ∧ k % n + 1 = μ := by
  have hn : 0 < n := by omega
  refine ⟨(g - 1) * n + (μ - 1), ?_, ?_, ?_⟩
  · calc (g - 1) * n + (μ - 1) < (g - 1) * n + n := by omega
      _ = (g - 1 + 1) * n := by ring
      _ ≤ n * n := by gcongr; omega
  · have hcomm : (g - 1) * n + (μ - 1) = (μ - 1) + (g - 1) * n := by ring
    rw [hcomm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt (by omega : μ - 1 < n)]
    omega
  · have hcomm : (g - 1) * n + (μ - 1) = (μ - 1) + (g - 1) * n := by ring
    rw [hcomm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : μ - 1 < n)]
    omega

/-- `Fin.append` is injective in each component. -/
private theorem append_inj {a b : ℕ} {X : Type*} {u u' : Fin a → X} {v v' : Fin b → X}
    (H : Fin.append u v = Fin.append u' v') : u = u' ∧ v = v' := by
  refine ⟨?_, ?_⟩
  · funext i; have := congrFun H (Fin.castAdd b i); simpa [Fin.append_left] using this
  · funext i; have := congrFun H (Fin.natAdd a i); simpa [Fin.append_right] using this

/-- Structure extensionality for `Species` (from all 14 field equalities). -/
private theorem species_ext {s s' : Species}
    (hTag : s.tag = s'.tag) (hD : s.D = s'.D) (hw : s.w = s'.w) (hW : s.W = s'.W)
    (he : s.e = s'.e) (hs0 : s.s0 = s'.s0) (hell : s.ell = s'.ell) (ha : s.a = s'.a)
    (hd : s.d = s'.d) (hslots : s.slots = s'.slots) (hlam : s.lam = s'.lam)
    (hsel : s.sel = s'.sel) (hlf : s.lflank = s'.lflank) (hrf : s.rflank = s'.rflank) :
    s = s' := by
  obtain ⟨t, D, w, W, e, s0, ell, a, d, slots, lam, sel, lf, rf⟩ := s
  obtain ⟨t', D', w', W', e', s0', ell', a', d', slots', lam', sel', lf', rf'⟩ := s'
  simp_all

/-! ### The encoding -/

/-- scalar block: tag; D w W; e s₀′ ℓ; selFst selSnd. -/
private def scalars (n : ℕ) (s : Species) : Fin 9 → Fin (n + 2) :=
  ![fld n (tagord s.tag), fld n s.D, fld n s.w, fld n s.W, fld n s.e,
    fld n s.s0, fld n s.ell, fld n (selFst s.sel), fld n (selSnd s.sel)]

/-- positional encoding of a flank composition (part `j` at slot `j`). -/
private def flankV (n : ℕ) (l : List ℕ) : Fin n → Fin (n + 2) :=
  fun j => fld n (l.getD j.val 0)

/-- `λ` as its `{1..n}²` multiplicity matrix, flattened. -/
private def lamV (n : ℕ) (lam : Multiset (ℕ × ℕ)) : Fin (n * n) → Fin (n + 2) :=
  fun k => fld n (lam.count (k.val / n + 1, k.val % n + 1))

/-- padding block (redundant slots). -/
private def padV (n : ℕ) : Fin (n + 3) → Fin (n + 2) := fun _ => fld n 0

/-- the concatenated raw vector, before the length cast. -/
private def bigAppend (n : ℕ) (s : Species) :
    Fin (9 + (n + (n + (n * n + (n + 3))))) → Fin (n + 2) :=
  Fin.append (scalars n s)
    (Fin.append (flankV n s.lflank)
      (Fin.append (flankV n s.rflank)
        (Fin.append (lamV n s.lam) (padV n))))

private theorem encode_dim (n : ℕ) :
    n ^ 2 + 3 * n + 12 = 9 + (n + (n + (n * n + (n + 3)))) := by ring

/-- the SP-FIN encoding. -/
def encode (n : ℕ) (hn : 1 ≤ n) (s : Species) : Code n :=
  bigAppend n s ∘ Fin.cast (encode_dim n)

theorem encode_inj {n hn} {s s' : Species} (hs : Coherent s ∧ Budget n s)
    (hs' : Coherent s' ∧ Budget n s') (h : encode n hn s = encode n hn s') :
    s = s' := by
  obtain ⟨hcoh, hbud⟩ := hs
  obtain ⟨hcoh', hbud'⟩ := hs'
  -- unpack coherence + budget for s
  obtain ⟨hWT, hG1, hG2, hG3, hG4, -⟩ := hcoh
  obtain ⟨-, -, -, -, -, hLamPos⟩ := hWT
  obtain ⟨⟨hLfPos, hLfSum⟩, hFlankSum, hRfPos⟩ := hG1
  obtain ⟨hSlots, hdEq⟩ := hG3
  obtain ⟨hLamSum, hSelMem⟩ := hG4
  obtain ⟨hDn, hwn, -, -, hB5⟩ := hbud
  obtain ⟨hEn, hElln, hS0n, -, hWn, hLamBd, -, -⟩ := hB5
  -- unpack coherence + budget for s'
  obtain ⟨hWT', hG1', hG2', hG3', hG4', -⟩ := hcoh'
  obtain ⟨-, -, -, -, -, hLamPos'⟩ := hWT'
  obtain ⟨⟨hLfPos', hLfSum'⟩, hFlankSum', hRfPos'⟩ := hG1'
  obtain ⟨hSlots', hdEq'⟩ := hG3'
  obtain ⟨hLamSum', hSelMem'⟩ := hG4'
  obtain ⟨hDn', hwn', -, -, hB5'⟩ := hbud'
  obtain ⟨hEn', hElln', hS0n', -, hWn', hLamBd', -, -⟩ := hB5'
  -- reduce the code equality to the raw-vector equality
  simp only [encode] at h
  have hba : bigAppend n s = bigAppend n s' := by
    funext i
    have := congrFun h (Fin.cast (encode_dim n).symm i)
    simpa [Fin.cast_cast] using this
  simp only [bigAppend] at hba
  -- peel off the five blocks
  obtain ⟨hsc, hr1⟩ := append_inj hba
  obtain ⟨hLf, hr2⟩ := append_inj hr1
  obtain ⟨hRf, hr3⟩ := append_inj hr2
  obtain ⟨hLam, -⟩ := append_inj hr3
  simp only [scalars] at hsc
  -- scalar recoveries
  have e0 : fld n (tagord s.tag) = fld n (tagord s'.tag) := by
    have := congrFun hsc 0; simpa using this
  have hTag : s.tag = s'.tag :=
    tagord_inj (fld_inj (by have := tagord_le s.tag; omega) (by have := tagord_le s'.tag; omega) e0)
  have eD : fld n s.D = fld n s'.D := by have := congrFun hsc 1; simpa using this
  have hD : s.D = s'.D := fld_inj (by omega) (by omega) eD
  have ew : fld n s.w = fld n s'.w := by have := congrFun hsc 2; simpa using this
  have hw : s.w = s'.w := fld_inj (by omega) (by omega) ew
  have eW : fld n s.W = fld n s'.W := by have := congrFun hsc 3; simpa using this
  have hW : s.W = s'.W := fld_inj (by omega) (by omega) eW
  have ee : fld n s.e = fld n s'.e := by have := congrFun hsc 4; simpa using this
  have he : s.e = s'.e := fld_inj (by omega) (by omega) ee
  have es0 : fld n s.s0 = fld n s'.s0 := by have := congrFun hsc 5; simpa using this
  have hs0 : s.s0 = s'.s0 := fld_inj (by omega) (by omega) es0
  have eell : fld n s.ell = fld n s'.ell := by have := congrFun hsc 6; simpa using this
  have hell : s.ell = s'.ell := fld_inj (by omega) (by omega) eell
  -- selection recovery
  have hSFn : selFst s.sel ≤ n := by
    cases hsel : s.sel with
    | none => simp [selFst]
    | some p => simp only [selFst]; exact (hLamBd p (hSelMem p hsel)).1
  have hSFn' : selFst s'.sel ≤ n := by
    cases hsel : s'.sel with
    | none => simp [selFst]
    | some p => simp only [selFst]; exact (hLamBd' p (hSelMem' p hsel)).1
  have hSSn : selSnd s.sel ≤ n := by
    cases hsel : s.sel with
    | none => simp [selSnd]
    | some p => simp only [selSnd]; exact (hLamBd p (hSelMem p hsel)).2
  have hSSn' : selSnd s'.sel ≤ n := by
    cases hsel : s'.sel with
    | none => simp [selSnd]
    | some p => simp only [selSnd]; exact (hLamBd' p (hSelMem' p hsel)).2
  have eSF : fld n (selFst s.sel) = fld n (selFst s'.sel) := by
    have := congrFun hsc 7; simpa using this
  have hSF : selFst s.sel = selFst s'.sel := fld_inj (by omega) (by omega) eSF
  have eSS : fld n (selSnd s.sel) = fld n (selSnd s'.sel) := by
    have := congrFun hsc 8; simpa using this
  have hSS : selSnd s.sel = selSnd s'.sel := fld_inj (by omega) (by omega) eSS
  have hSel : s.sel = s'.sel := by
    cases hsel : s.sel with
    | none =>
      cases hsel' : s'.sel with
      | none => rfl
      | some p' =>
        exfalso
        have hpos := (hLamPos' p' (hSelMem' p' hsel')).1
        rw [hsel, hsel'] at hSF; simp only [selFst] at hSF; omega
    | some p =>
      cases hsel' : s'.sel with
      | none =>
        exfalso
        have hpos := (hLamPos p (hSelMem p hsel)).1
        rw [hsel, hsel'] at hSF; simp only [selFst] at hSF; omega
      | some p' =>
        rw [hsel, hsel'] at hSF hSS
        simp only [selFst, selSnd] at hSF hSS
        exact congrArg some (Prod.ext hSF hSS)
  -- flank sums (needed for entry bounds)
  have hRfSum : s.rflank.sum ≤ n := by omega
  have hRfSum' : s'.rflank.sum ≤ n := by omega
  have hlenL : s.lflank.length ≤ n := by
    have := length_le_sum s.lflank hLfPos; rw [hLfSum] at this; omega
  have hlenL' : s'.lflank.length ≤ n := by
    have := length_le_sum s'.lflank hLfPos'; rw [hLfSum'] at this; omega
  have hlenR : s.rflank.length ≤ n := by
    have := length_le_sum s.rflank hRfPos; omega
  have hlenR' : s'.rflank.length ≤ n := by
    have := length_le_sum s'.rflank hRfPos'; omega
  -- left flank recovery
  have hLflank : s.lflank = s'.lflank := by
    refine list_pos_getD_ext s.lflank s'.lflank hLfPos hLfPos' (fun j => ?_)
    by_cases hj : j < n
    · have hfe : fld n (s.lflank.getD j 0) = fld n (s'.lflank.getD j 0) := by
        have := congrFun hLf ⟨j, hj⟩; simpa [flankV] using this
      have b1 : s.lflank.getD j 0 < n + 2 := by
        have := getD_le_sum s.lflank j; rw [hLfSum] at this; omega
      have b2 : s'.lflank.getD j 0 < n + 2 := by
        have := getD_le_sum s'.lflank j; rw [hLfSum'] at this; omega
      exact fld_inj b1 b2 hfe
    · rw [List.getD_eq_default s.lflank 0 (by omega), List.getD_eq_default s'.lflank 0 (by omega)]
  -- right flank recovery
  have hRflank : s.rflank = s'.rflank := by
    refine list_pos_getD_ext s.rflank s'.rflank hRfPos hRfPos' (fun j => ?_)
    by_cases hj : j < n
    · have hfe : fld n (s.rflank.getD j 0) = fld n (s'.rflank.getD j 0) := by
        have := congrFun hRf ⟨j, hj⟩; simpa [flankV] using this
      have b1 : s.rflank.getD j 0 < n + 2 := by
        have := getD_le_sum s.rflank j; omega
      have b2 : s'.rflank.getD j 0 < n + 2 := by
        have := getD_le_sum s'.rflank j; omega
      exact fld_inj b1 b2 hfe
    · rw [List.getD_eq_default s.rflank 0 (by omega), List.getD_eq_default s'.rflank 0 (by omega)]
  -- λ recovery
  have hLamSupp : ∀ gm ∈ s.lam, 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n := by
    intro gm hgm
    exact ⟨(hLamPos gm hgm).1, (hLamBd gm hgm).1, (hLamPos gm hgm).2, (hLamBd gm hgm).2⟩
  have hLamSupp' : ∀ gm ∈ s'.lam, 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n := by
    intro gm hgm
    exact ⟨(hLamPos' gm hgm).1, (hLamBd' gm hgm).1, (hLamPos' gm hgm).2, (hLamBd' gm hgm).2⟩
  have hLam' : s.lam = s'.lam := by
    refine multiset_grid_ext n s.lam s'.lam hLamSupp hLamSupp' (fun g μ hg1 hgn hμ1 hμn => ?_)
    obtain ⟨k, hk, hkg, hkμ⟩ := grid_cover n g μ hg1 hgn hμ1 hμn
    have hfe : fld n (s.lam.count (g, μ)) = fld n (s'.lam.count (g, μ)) := by
      have := congrFun hLam ⟨k, hk⟩
      simp only [lamV] at this
      rw [hkg, hkμ] at this; exact this
    have hb : s.lam.count (g, μ) ≤ n := by
      have := count_bound s.lam g μ hLamPos; rw [hLamSum] at this; omega
    have hb' : s'.lam.count (g, μ) ≤ n := by
      have := count_bound s'.lam g μ hLamPos'; rw [hLamSum'] at this; omega
    exact fld_inj (by omega) (by omega) hfe
  -- derived fields a, d, slots (from coherence)
  have ha : s.a = s'.a := by rw [hG2, hG2', hs0, he]
  have hd : s.d = s'.d := by rw [hdEq, hdEq', hell]
  have hslots : s.slots = s'.slots := by rw [hSlots, hSlots', ha, hell]
  exact species_ext hTag hD hw hW he hs0 hell ha hd hslots hLam' hSel hLflank hRflank

end LeanUrat.MovesSp
