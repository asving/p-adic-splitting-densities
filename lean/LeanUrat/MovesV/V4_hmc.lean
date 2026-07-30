/-  MovesV unit V4-11 `hmc_typing` (REWRITTEN REV 9: THE CENSUS-LEVEL
    COUPLING) — leg (i): the false-HMC toy (¬HMC at the coupled census);
    leg (ii) = V1-8b (HMC true there); leg (iii) WITHDRAWN (verdict (A),
    HMCAUG_ESCALATION_ADJUDICATION_2026-07-29: no separation obligation).
    The terminal-final signature check is the `example` below. -/
import LeanUrat.MovesV.V1_witnessB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-! ### The leg-(i) toy, built constructively (the writer's design note:
the domain-exactness legs quantify over the infinite `Hpt`, so the composite
domain is the FIRST-NONZERO-COORDINATE semilinear partition of `ℕ^D ∖ {0}`,
proved at all `D`).  Prover deviation from the REV-9 three-cell sketch,
mechanism preserved: ONE cell, every carrier `Fin 2`, `zc ≡ True`; census
`= cntraw` (full) at one-step templates, `1` off the zero height on every
composite and EMPTY at it; one-step domains full.  ¬HMC at `(0,0)` and the
`chainCount > 0 = Tgam` coupling signature are exactly the blueprint's. -/
namespace HmcToy

/-- the toy step system: one cell, one move, one terminal move; all
history/assignment carriers `Fin 2`, `zc ≡ True`, pool `{2}`. -/
def S : StepSys 1 where
  Cell := Fin 1
  finC := inferInstance
  cell_ne := ⟨0⟩
  Move _ _ := Fin 1
  MoveT _ _ := Fin 1
  finM _ _ := inferInstance
  finMT _ _ := inferInstance
  dim := fun _ => 1
  dimT := fun _ => 1
  Pools := {2}
  pools_ne := ⟨2, rfl⟩
  pools_pp := by
    rintro q₀ hq
    rw [Set.mem_singleton_iff] at hq
    exact ⟨2, 1, Nat.prime_two, one_pos, by rw [hq]; norm_num⟩
  pools_gt_one := by
    rintro q₀ hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq]; norm_num
  Hist _ _ := Fin 2
  hist_ne _ _ _ := ⟨0⟩
  zc := fun _ => True
  zc_ne _ _ _ := ⟨0, trivial⟩
  Assign := fun _ _ _ _ => Fin 2
  finA := fun _ _ _ _ => inferInstance
  AssignT := fun _ _ _ _ => Fin 2
  finAT := fun _ _ _ _ => inferInstance
  ext := fun _ _ _ _ a => a
  ext_zc := fun _ _ _ _ _ _ => trivial
  massOf := fun _ _ _ _ _ => 0
  massOfT := fun _ _ _ _ _ => 0
  out_ne := fun _ _ _ x _ => Or.inl ⟨0, 0, fun _ => 0, ⟨0⟩⟩

/-- the unique cell, named (numerals don't see through the projection). -/
def c0 : S.Cell := (0 : Fin 1)

/-- the unique move `c0 → c0`, named. -/
def mv : S.Move c0 c0 := (0 : Fin 1)

/-! #### The first-nonzero-coordinate domain build (all dimensions). -/

/-- the `i`-th unit vector of `ℕ^D`. -/
def uv (D : ℕ) (i : Fin D) : Hpt D := fun j => if j = i then 1 else 0

lemma uv_self {D : ℕ} (i : Fin D) : uv D i i = 1 := if_pos rfl

lemma uv_of_ne {D : ℕ} {a b : Fin D} (h : b ≠ a) : uv D a b = 0 := if_neg h

/-- the shifted index `i + j` living above the pivot `i`. -/
def nzp (D : ℕ) (i : Fin D) (j : Fin (D - (i : ℕ))) : Fin D :=
  ⟨(i : ℕ) + (j : ℕ), by have h1 := j.isLt; have h2 := i.isLt; omega⟩

@[simp] lemma nzp_val {D : ℕ} (i : Fin D) (j : Fin (D - (i : ℕ))) :
    (nzp D i j : ℕ) = (i : ℕ) + (j : ℕ) := rfl

/-- reindexing an `ofFn`-periods sum along `finCongr`. -/
private lemma sum_ofFn_mul {D n : ℕ} (f : Fin n → Hpt D)
    (c : Fin (List.ofFn f).length → ℕ) (k : Fin D) :
    (∑ j, c j * ((List.ofFn f).get j) k)
      = ∑ t : Fin n, c (Fin.cast (List.length_ofFn (f := f)).symm t) * f t k := by
  refine Fintype.sum_equiv (finCongr (List.length_ofFn (f := f))) _ _ fun j => ?_
  rw [List.get_ofFn]
  congr 1

/-- membership in an `ofFn`-presented linear set from a pointwise expansion. -/
private lemma mem_ofFn_linset {D n : ℕ} (base : Hpt D) (f : Fin n → Hpt D)
    (g : Fin n → ℕ) (h : Hpt D)
    (heq : ∀ k, h k = base k + ∑ t : Fin n, g t * f t k) :
    (⟨base, List.ofFn f⟩ : LinSet D).Mem h := by
  refine ⟨fun j => g (Fin.cast (List.length_ofFn (f := f)) j), funext fun k => ?_⟩
  change h k = base k
      + ∑ j, g (Fin.cast (List.length_ofFn (f := f)) j) * ((List.ofFn f).get j) k
  rw [heq k]
  congr 1
  rw [sum_ofFn_mul f (fun j => g (Fin.cast (List.length_ofFn (f := f)) j)) k]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1

/-- eliminating an `ofFn`-presented membership to a cast-free expansion. -/
private lemma linset_mem_elim {D n : ℕ} {base : Hpt D} {f : Fin n → Hpt D}
    {h : Hpt D} (hm : (⟨base, List.ofFn f⟩ : LinSet D).Mem h) :
    ∃ g : Fin n → ℕ, ∀ k, h k = base k + ∑ t : Fin n, g t * f t k := by
  obtain ⟨c, hc⟩ := hm
  refine ⟨fun t => c (Fin.cast (List.length_ofFn (f := f)).symm t), fun k => ?_⟩
  rw [congrFun hc k]
  change base k + ∑ j, c j * ((List.ofFn f).get j) k = _
  rw [sum_ofFn_mul f c k]

/-- the full box `ℕ^D` as one linear set: base `0`, unit periods. -/
def fullL (D : ℕ) : LinSet D := ⟨fun _ => 0, List.ofFn (uv D)⟩

lemma fullL_mem (D : ℕ) (h : Hpt D) : (fullL D).Mem h :=
  mem_ofFn_linset (fun _ => 0) (uv D) h h (fun k => by
    simp [uv, mul_ite, Finset.sum_ite_eq])

/-- the full box as a one-component partition. -/
def fullPart (D : ℕ) : SemilinPart D := ⟨[fullL D], by simp⟩

lemma fullPart_mem (D : ℕ) (h : Hpt D) : (fullPart D).Mem h :=
  ⟨fullL D, List.mem_singleton_self _, fullL_mem D h⟩

/-- the `i`-th component of the first-nonzero decomposition:
`h_j = 0` below the pivot `i`, `h i ≥ 1`, free above. -/
def nzComp (D : ℕ) (i : Fin D) : LinSet D :=
  ⟨uv D i, List.ofFn fun j => uv D (nzp D i j)⟩

lemma nzComp_mem_pos {D : ℕ} {i : Fin D} {h : Hpt D}
    (hm : (nzComp D i).Mem h) : 1 ≤ h i := by
  obtain ⟨g, hg⟩ := linset_mem_elim hm
  rw [hg i, uv_self]
  exact Nat.le_add_right 1 _

lemma nzComp_mem_zero {D : ℕ} {i : Fin D} {h : Hpt D}
    (hm : (nzComp D i).Mem h) {k : Fin D} (hk : (k : ℕ) < (i : ℕ)) : h k = 0 := by
  obtain ⟨g, hg⟩ := linset_mem_elim hm
  rw [hg k, uv_of_ne (fun he => by rw [Fin.ext_iff] at he; omega), zero_add]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : k ≠ nzp D i t := fun he => by
    rw [Fin.ext_iff, nzp_val] at he; omega
  rw [uv_of_ne hne, mul_zero]

lemma nzComp_mem_of {D : ℕ} {i : Fin D} {h : Hpt D} (h1 : 1 ≤ h i)
    (h0 : ∀ k : Fin D, (k : ℕ) < (i : ℕ) → h k = 0) : (nzComp D i).Mem h := by
  refine mem_ofFn_linset (uv D i) (fun j => uv D (nzp D i j))
    (fun t => if (t : ℕ) = 0 then h i - 1 else h (nzp D i t)) h (fun k => ?_)
  rcases Nat.lt_or_ge (k : ℕ) (i : ℕ) with hk | hk
  · have hbase : uv D i k = 0 :=
      uv_of_ne (fun he => by rw [Fin.ext_iff] at he; omega)
    rw [h0 k hk, hbase, zero_add]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    have hne : k ≠ nzp D i t := fun he => by
      rw [Fin.ext_iff, nzp_val] at he; omega
    rw [uv_of_ne hne, mul_zero]
  · have hd : (k : ℕ) - (i : ℕ) < D - (i : ℕ) := by have := k.isLt; omega
    set t₀ : Fin (D - (i : ℕ)) := ⟨(k : ℕ) - (i : ℕ), hd⟩ with ht₀def
    have ht₀v : (t₀ : ℕ) = (k : ℕ) - (i : ℕ) := rfl
    have hsum : (∑ t : Fin (D - (i : ℕ)),
        (if (t : ℕ) = 0 then h i - 1 else h (nzp D i t)) * uv D (nzp D i t) k)
        = if (t₀ : ℕ) = 0 then h i - 1 else h (nzp D i t₀) := by
      rw [Finset.sum_eq_single t₀]
      · have huv : uv D (nzp D i t₀) k = 1 :=
          if_pos (Fin.ext (by rw [nzp_val, ht₀v]; omega))
        rw [huv, mul_one]
      · intro t _ hne
        have hne' : k ≠ nzp D i t := fun he => hne (Fin.ext (by
          rw [Fin.ext_iff, nzp_val] at he
          rw [ht₀v]
          omega))
        rw [uv_of_ne hne', mul_zero]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    rw [hsum]
    rcases Nat.eq_or_lt_of_le hk with heq | hlt
    · have hki : k = i := Fin.ext heq.symm
      rw [hki, uv_self, if_pos (show (t₀ : ℕ) = 0 by rw [ht₀v]; omega)]
      omega
    · have hbase : uv D i k = 0 :=
        uv_of_ne (fun he => by rw [Fin.ext_iff] at he; omega)
      rw [hbase, zero_add, if_neg (show ¬((t₀ : ℕ) = 0) by rw [ht₀v]; omega)]
      have hnz : nzp D i t₀ = k := Fin.ext (by rw [nzp_val, ht₀v]; omega)
      rw [hnz]

/-- `ℕ^D ∖ {0}`, partitioned by the position of the first nonzero
coordinate — the constructive composite-domain build. -/
def nzPart (D : ℕ) : SemilinPart D :=
  ⟨List.ofFn (nzComp D), by
    rw [List.pairwise_ofFn]
    intro a b hab h hcon
    have hpos : 1 ≤ h a := nzComp_mem_pos hcon.1
    have hzero : h a = 0 := nzComp_mem_zero hcon.2 hab
    omega⟩

lemma nzPart_not_mem {D : ℕ} {h : Hpt D} (h0 : ∀ k, h k = 0) :
    ¬ (nzPart D).Mem h := by
  rintro ⟨L, hL, hmem⟩
  simp only [nzPart, List.mem_ofFn'] at hL
  obtain ⟨i, rfl⟩ := hL
  have := nzComp_mem_pos hmem
  rw [h0 i] at this
  omega

lemma nzPart_mem {D : ℕ} {h : Hpt D} (hne : h ≠ 0) : (nzPart D).Mem h := by
  classical
  have hex : ∃ m : ℕ, ∃ hm : m < D, h ⟨m, hm⟩ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (funext fun k => by simpa using hc (k : ℕ) k.isLt)
  obtain ⟨hlt, hne0⟩ := Nat.find_spec hex
  refine ⟨nzComp D ⟨Nat.find hex, hlt⟩, ?_, ?_⟩
  · exact (List.mem_ofFn' _ _).mpr ⟨⟨Nat.find hex, hlt⟩, rfl⟩
  · refine nzComp_mem_of (Nat.one_le_iff_ne_zero.mpr hne0) fun k hk => ?_
    by_contra hkne
    exact Nat.find_min hex hk ⟨k.isLt, by simpa using hkne⟩

/-! #### The coupled census, its event/mark carrier, and the domains. -/

/-- THE COUPLED CENSUS: full (= `cntraw`) at one-step templates; on every
composite, `1` off the zero height and EMPTY at it. -/
def census : ∀ {α} (γ : Template 1 S α) {q₀}, S.Hist q₀ α → Hpt γ.D → ℕ
  | _, .last m, _, x, h => S.cntraw m x h
  | _, .lastT m, _, x, h => S.cntrawT m x h
  | _, .cons _ _, _, _, h => if h = 0 then 0 else 1

/-- the one-step counts of the toy are everywhere `2`. -/
lemma cntraw_eq {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dim m)) : S.cntraw m x h = 2 := rfl

lemma cntrawT_eq {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dimT m)) : S.cntrawT m x h = 2 := rfl

lemma assign_card {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dim m)) : @Fintype.card (S.Assign m x h) (S.finA m x h) = 2 := rfl

/-- the census realized as a `Finset (Fin 2)` (the `tevt`/`tinst` value). -/
def tin {α} (γ : Template 1 S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) :
    Finset (Fin 2) :=
  Finset.univ.filter (fun b => (b : ℕ) < census γ x h)

lemma tin_card_pos {α} {γ : Template 1 S α} {q₀} {x : S.Hist q₀ α} {h : Hpt γ.D}
    (hc : 0 < census γ x h) : 0 < (tin γ x h).card :=
  Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩

/-- a default chain (all chain carriers of the toy are inhabited). -/
def chainDefault : ∀ {α} (γ : Template 1 S α) {q₀} (x : S.Hist q₀ α)
    (h : Hpt γ.D), Chains S γ x h
  | _, .last _, _, _, _ => (0 : Fin 2)
  | _, .lastT _, _, _, _ => (0 : Fin 2)
  | _, .cons m γ', _, x, h =>
      ⟨(0 : Fin 2), chainDefault γ' (S.ext m x (Hpt.take h) ((0 : Fin 2))) (Hpt.drop h)⟩

/-- the mark reading: the identity on one-step fibers, constant on
composites (whose census is ≤ 1). -/
def mark : ∀ {α} (γ : Template 1 S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    {b // b ∈ tin γ x h} → Chains S γ x h
  | _, .last _, _, _, _, b => b.1
  | _, .lastT _, _, _, _, b => b.1
  | _, .cons m γ', _, x, h, _ => chainDefault (Template.cons m γ') x h

lemma mark_inj {α} (γ : Template 1 S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) :
    Function.Injective (mark γ x h) := by
  cases γ with
  | last m => intro a b hab; exact Subtype.ext hab
  | lastT m => intro a b hab; exact Subtype.ext hab
  | cons m γ' =>
    intro a b _
    have ha : ((a.1 : Fin 2) : ℕ) < census (Template.cons m γ') x h :=
      (Finset.mem_filter.mp a.2).2
    have hb : ((b.1 : Fin 2) : ℕ) < census (Template.cons m γ') x h :=
      (Finset.mem_filter.mp b.2).2
    have hle : census (Template.cons m γ') x h ≤ 1 := by
      change (if h = 0 then 0 else 1) ≤ 1
      split <;> omega
    exact Subtype.ext (Fin.ext (by omega))

lemma mark_last_surj {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dim m)) : Function.Surjective (mark (.last m) x h) := fun a =>
  ⟨⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (a : Fin 2).isLt⟩⟩, rfl⟩

lemma mark_lastT_surj {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dimT m)) : Function.Surjective (mark (.lastT m) x h) := fun a =>
  ⟨⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (a : Fin 2).isLt⟩⟩, rfl⟩

/-- the toy's marked-event carrier: `tevt = tinst = tin`, level 0. -/
def TE : TmplEvents 1 S where
  Box _ _ := Fin 2
  finB _ _ := inferInstance
  tevt := fun γ _ x h _ => tin γ x h
  tinst := fun γ _ x h _ => tin γ x h
  tmplLvl := fun _ => 0
  tevt_last_iff := by
    intro α β m q₀ x h _ _
    constructor
    · exact fun _ => Nat.zero_lt_two
    · intro _
      exact ⟨0, fun N _ =>
        ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_lt_two⟩⟩⟩
  tevt_lastT_iff := by
    intro α v m q₀ x h _ _
    constructor
    · exact fun _ => Nat.zero_lt_two
    · intro _
      exact ⟨0, fun N _ =>
        ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_lt_two⟩⟩⟩
  real_marks := by
    intro α γ q₀ x h _ _ hR
    obtain ⟨N₀, hN⟩ := hR
    obtain ⟨b, hb⟩ := hN N₀ le_rfl
    exact Finset.card_pos.mpr ⟨b, hb⟩
  tmark := fun γ _ x h => mark γ x h
  tmark_inj := by
    intro α γ q₀ x h _ _
    exact mark_inj γ x h
  tmark_last_surj := by
    intro α β m q₀ x h _ _
    exact mark_last_surj m x h
  tmark_lastT_surj := by
    intro α v m q₀ x h _ _
    exact mark_lastT_surj m x h
  marks_realize := by
    intro α γ q₀ x h _ _ hpos
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    exact ⟨0, fun N _ => ⟨b, hb⟩⟩

/-- the toy domains: one-step full, composites = the first-nonzero build. -/
def domToy : ∀ {α} (γ : Template 1 S α), SemilinPart γ.D
  | _, .last _ => fullPart 1
  | _, .lastT _ => fullPart 1
  | _, .cons _ γ' => nzPart (1 + γ'.D)

/-- the toy XHD-d: `no_orphan`/`no_stray` against the coupled census. -/
def XD : XHDd 1 S TE where
  dom := domToy
  no_orphan := by
    intro α γ q₀ x h _ _ hpos
    have hpos' : 0 < (tin γ x h).card := hpos
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos'
    have hbc : (b : ℕ) < census γ x h := (Finset.mem_filter.mp hb).2
    cases γ with
    | last m => exact fullPart_mem 1 h
    | lastT m => exact fullPart_mem 1 h
    | cons m γ' =>
      have hne : h ≠ 0 := by
        intro h0
        rw [h0] at hbc
        rw [show census (Template.cons m γ') x 0 = 0 from if_pos rfl] at hbc
        omega
      exact nzPart_mem hne
  no_stray := by
    intro α γ h hm q₀ _ x _
    cases γ with
    | last m => exact tin_card_pos Nat.zero_lt_two
    | lastT m => exact tin_card_pos Nat.zero_lt_two
    | cons m γ' =>
      have hne : h ≠ 0 := fun h0 => nzPart_not_mem (fun _ => rfl) (h0 ▸ hm)
      refine tin_card_pos ?_
      rw [show census (Template.cons m γ') x h = 1 from if_neg hne]
      exact Nat.zero_lt_one

end HmcToy

/-- leg (i): THE COUPLED TOY — ¬HMC witnessed at carrier level (the §8
decide gate; the coupled composite census is empty at (0,0) while both
one-step factors are full). -/
theorem hmc_false_witness :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (D : XHDd 1 S TE), ¬ HMC TE D := by
  refine ⟨HmcToy.S, HmcToy.TE, HmcToy.XD, fun hH => ?_⟩
  have hmem := (hH HmcToy.mv (.last HmcToy.mv) (fun _ => 0) (fun _ => 0)).mpr
    ⟨HmcToy.fullPart_mem 1 _, HmcToy.fullPart_mem 1 _⟩
  refine HmcToy.nzPart_not_mem (fun k => ?_) hmem
  simp [Hpt.append, Fin.append, Fin.addCases]

/-- the coupling signature (marks_chains-consistent): at the coupled point
the combinatorial chains exist while the census is empty — recorded as the
∃-shaped check rider on leg (i). -/
theorem coupling_signature :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (α β : S.Cell)
      (m₁ : S.Move α β) (γ : Template 1 S β) (q₀ : ℚ) (x : S.Hist q₀ α)
      (h : Hpt (Template.cons m₁ γ).D),
      0 < chainCount S (.cons m₁ γ) x h ∧ Tgam TE (.cons m₁ γ) x h = 0 := by
  refine ⟨HmcToy.S, HmcToy.TE, HmcToy.c0, HmcToy.c0, HmcToy.mv,
    .last HmcToy.mv, 2, (0 : Fin 2), (fun _ => 0), ?_, ?_⟩
  · -- two combinatorial chains exist through the two first assignments
    have h4 : chainCount HmcToy.S
        (Template.cons HmcToy.mv (Template.last HmcToy.mv)) (q₀ := 2)
        ((0 : Fin 2)) (fun _ => 0) = 4 := by
      simp [chainCount, HmcToy.cntraw_eq, Finset.sum_const, Finset.card_univ,
        HmcToy.assign_card]
    exact lt_of_lt_of_eq (by norm_num) h4.symm
  · -- while the coupled census at the zero point is EMPTY
    change (HmcToy.tin (Template.cons HmcToy.mv (Template.last HmcToy.mv))
        (q₀ := 2) ((0 : Fin 2)) (fun _ => 0)).card = 0
    have hc : HmcToy.census (Template.cons HmcToy.mv (Template.last HmcToy.mv))
        (q₀ := 2) ((0 : Fin 2)) (fun _ => 0) = 0 := by
      simp only [HmcToy.census]
      exact if_pos rfl
    simp [HmcToy.tin, hc]

/-- the terminal-final signature check: `Template.lastT` instances TYPE
against HMC's quantifier (the probe's step 2 is a literal instance BY TYPE). -/
example {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) (D : XHDd n S TE)
    (hHMC : HMC TE D) {α β : S.Cell} {v : VLabel n} (m : S.Move α β)
    (mT : S.MoveT β v) (h₁ : Hpt (S.dim m)) (h₂ : Hpt (Template.lastT (n := n) (S := S) mT).D) :
    (D.dom (.cons m (.lastT mT))).Mem (Hpt.append h₁ h₂) ↔
      (D.dom (.last m)).Mem h₁ ∧ (D.dom (.lastT mT)).Mem h₂ :=
  hHMC m (.lastT mT) h₁ h₂

end LeanUrat.MovesV
