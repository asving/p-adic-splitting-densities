/-
Unit XE.2 envelopeExp — the note's exponential envelope, as the DERIVED ∃-theorem
(finding 7)  [RESTATED-POST-REFUTATION 2026-07-27: the previous ∀N conclusion was
kernel-certified FALSE (notes/XE2_refutation_witness.lean + _transcription_check.lean;
adjudication in blueprint §7). The conclusion now binds ∃ N₀ (an (n,K)-function, bound
BEFORE p) with the claim over N ≥ N₀ only — the note's honest domain of content (the
(N−1−c_cap) numerator; X.5(iii) no-teeth regime). The refutation countermodel (point
mass at X²+X, root-only tree, Undec N = ∅ for N ≥ 2) now SATISFIES the statement via
N₀ ≥ 2. Body sorry; fleet re-proves. D9 REBIND (audit, accepted findings 2/4): N₀, c3, c4 are
now bound BEFORE ∀ X — quantified over exactly (n, K); the tags move inside as
implications, so the constants cannot depend on any XFamily data. Disclosed: R is
redundant given AL ∧ WC (route a2) — kept, per the tag list.]
moves_ref: "Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF) … Given (X.2) with linear d*, h*
AND both legs …: env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n), c₀, C_T, c_T,
c_cap".
sketch: BR splits Undec(N) into the three null-tagged pieces (discZero via
XF.7/vdisc_le_tail; ns via NS; InfTree via XG.2d ⊆ discZero) + the witness-branch
piece. WITNESS FEED (rev 4, traced): BR's witness b carries `IsLeafB b ∧ NsFreeB b`,
hence `FourthPieceB b` by the FIRST disjunct of FourthPieceB — exactly PR's (and
XD.4's, in XE.3) hypothesis; PR on b gives deep-or-tall at d* = cd·N − cd',
h* = ch·N − ch'; DEEP LEG: DeepEvent d* ⊆ {vdisc ≥ (2(d*−log)/(2s+1))} pointwise
(XC.3 + gmnLink) → vdisc_le_tail + XF.7 give the (3b) bound with the note's displayed
exponent; TALL LEG: TL. Constants assembled n-only (c₄ from cd, s, n − 1; the
p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} absorption into c₃ — p-free).
deps: XC.3, XE.1*, XF.7, XG.2b–d. difficulty: HARD.
hyp_fields: the FULL tag set, verbatim the note's "CONSUMERS … inherit ALL tags above".
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XC3
import LeanUrat.MovesX.XE1a
import LeanUrat.MovesX.XE1b
import LeanUrat.MovesX.XE1c
import LeanUrat.MovesX.XE1d
import LeanUrat.MovesX.XE1e
import LeanUrat.MovesX.XE1f
import LeanUrat.MovesX.XE1g
import LeanUrat.MovesX.XE1h
import LeanUrat.MovesX.XF7
import LeanUrat.MovesX.XG2b
import LeanUrat.MovesX.XG2c
import LeanUrat.MovesX.XG2d

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ### Helper lemmas -/

/-- If `maxH H ≥ k ≥ 1`, some node of `H` has height `≥ k` (the seed `0` cannot
carry a positive `k`). -/
private lemma exists_node_of_le_maxH {n : ℕ} (H : XHistory n) (k : ℕ) (hk : 1 ≤ k)
    (hle : k ≤ maxH H) : ∃ ν ∈ H, k ≤ ν.h := by
  induction H with
  | nil => simp [maxH] at hle; omega
  | cons ν H' ih =>
      have hstep : maxH (ν :: H') = max ν.h (maxH H') := by
        simp only [maxH, List.map_cons, List.foldr_cons]
      rw [hstep] at hle
      rcases le_max_iff.mp hle with h | h
      · exact ⟨ν, List.mem_cons_self, h⟩
      · obtain ⟨μ, hμ, hμk⟩ := ih h
        exact ⟨μ, List.mem_cons_of_mem ν hμ, hμk⟩

/-- A crude p-free bound: `v_p(n) ≤ n` for `n ≥ 1`, `p` prime. -/
private lemma padicValNat_le_self (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) :
    padicValNat p n ≤ n := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hdvd : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
  have hpow_le : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hlt : padicValNat p n < 2 ^ padicValNat p n := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ padicValNat p n ≤ p ^ padicValNat p n :=
    Nat.pow_le_pow_left hp2 _
  omega

/-- The deep threshold `d*(N) = ⌈cd·N − cd'⌉`. -/
private def dstar (n : ℕ) (K : XConsts n) (N : ℕ) : ℕ := ⌈(K.cd * N - K.cd' : ℚ)⌉₊
/-- The tall threshold `h*(N) = ⌈ch·N − ch'⌉`. -/
private def hstarN (n : ℕ) (K : XConsts n) (N : ℕ) : ℕ := ⌈(K.ch * N - K.ch' : ℚ)⌉₊
/-- The discriminant-valuation threshold `D(N) = ⌊(2·d*(N) − 2·log₂ n)/(2s+1)⌋`. -/
private def Ddeep (n : ℕ) (K : XConsts n) (N : ℕ) : ℕ :=
  (2 * dstar n K N - 2 * Nat.log 2 n) / (2 * K.s + 1)

/-- The deep-leg exponent grows at least linearly in `N`: once `N` is large enough
(the `hN` premise), `cd·N ≤ (2s+1)·(n−1)·tailExp p n (D N)`.  Combined with
`c4 := cd/((2s+1)(n−1))` this gives `c4·N ≤ tailExp`, the p-uniform decay rate. -/
private lemma deep_exp (n : ℕ) (hn : 2 ≤ n) (K : XConsts n) (p : ℕ) [Fact p.Prime] (N : ℕ)
    (hN : 2 * K.cd' + 2 * (Nat.log 2 n : ℚ) + (2 * K.s + 1) * (1 + (n : ℚ) * n) ≤ K.cd * N) :
    (K.cd : ℚ) * N ≤ (2 * K.s + 1) * ((n : ℚ) - 1) * (tailExp p n (Ddeep n K N) : ℚ) := by
  set d := dstar n K N with hd
  set L := Nat.log 2 n with hLdef
  set w : ℕ := 2 * K.s + 1 with hw
  have hwpos : 0 < w := by omega
  have hwq : (0 : ℚ) < (w : ℚ) := by exact_mod_cast hwpos
  set D := Ddeep n K N with hDdef
  have hDeq : D = (2 * d - 2 * L) / w := rfl
  -- n ≥ 2 facts
  have hn2q : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1pos : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  -- F1: d ≥ cd*N - cd'
  have hF1 : (K.cd * N - K.cd' : ℚ) ≤ (d : ℚ) := by
    rw [hd, dstar]; exact Nat.le_ceil _
  -- cd*N ≥ 0
  have hcdN0 : (0 : ℚ) ≤ K.cd * N := mul_nonneg K.cdpos.le (Nat.cast_nonneg N)
  have hw1n2 : (0 : ℚ) ≤ (w : ℚ) * (1 + (n : ℚ) * n) := by positivity
  -- L ≤ d
  have hLd : L ≤ d := by
    have hq : (L : ℚ) ≤ (d : ℚ) := by
      have hwexp : ((w : ℚ)) = 2 * (K.s : ℚ) + 1 := by push_cast [hw]; ring
      -- from hN: cd*N ≥ 2cd' + 2L + w(1+n²); combine with hcdN0
      have hNq : 2 * K.cd' + 2 * (L : ℚ) + (w : ℚ) * (1 + (n : ℚ) * n) ≤ K.cd * N := by
        rw [hwexp, hLdef]; exact hN
      nlinarith [hF1, hcdN0, hw1n2, hNq]
    exact_mod_cast hq
  -- A := 2d - 2L, and A cast
  have hAcast : ((2 * d - 2 * L : ℕ) : ℚ) = 2 * (d : ℚ) - 2 * (L : ℚ) := by
    have : 2 * L ≤ 2 * d := by omega
    push_cast [Nat.cast_sub this]; ring
  -- D relation: (2d-2L) < w*(D+1)
  have hDrel : (2 * d - 2 * L : ℕ) < w * (D + 1) := by
    have hdm : w * D + (2 * d - 2 * L) % w = (2 * d - 2 * L) := by
      rw [hDeq]; exact Nat.div_add_mod _ _
    have hmod : (2 * d - 2 * L) % w < w := Nat.mod_lt _ hwpos
    calc (2 * d - 2 * L : ℕ) = w * D + (2 * d - 2 * L) % w := hdm.symm
      _ < w * D + w := by omega
      _ = w * (D + 1) := by ring
  have hDrelq : ((2 * d - 2 * L : ℕ) : ℚ) < (w : ℚ) * ((D : ℚ) + 1) := by
    exact_mod_cast hDrel
  -- vpn ≤ n
  have hvpn : padicValNat p n ≤ n := padicValNat_le_self p n (by omega)
  have hvpnq : (padicValNat p n : ℚ) ≤ (n : ℚ) := by exact_mod_cast hvpn
  -- F5: (D - n·vpn) ≤ (n-1)·tailExp
  have hF5 : ((D : ℚ) - (n : ℚ) * padicValNat p n) ≤ ((n : ℚ) - 1) * (tailExp p n D : ℚ) := by
    have hle : (((D : ℤ) - n * padicValNat p n : ℚ)) / ((n : ℚ) - 1)
        ≤ (tailExp p n D : ℚ) := by
      rw [tailExp]; exact_mod_cast Int.le_ceil _
    rw [div_le_iff₀ hn1pos] at hle
    push_cast at hle ⊢
    nlinarith [hle]
  -- assemble
  -- multiply F5 by w
  have hF5w : (w : ℚ) * ((D : ℚ) - (n : ℚ) * padicValNat p n)
      ≤ (w : ℚ) * (((n : ℚ) - 1) * (tailExp p n D : ℚ)) :=
    mul_le_mul_of_nonneg_left hF5 hwq.le
  -- D*w lower bound
  have hDw : 2 * (K.cd * N) - 2 * K.cd' - 2 * (L : ℚ) - (w : ℚ) < (D : ℚ) * (w : ℚ) := by
    rw [hAcast] at hDrelq
    nlinarith [hDrelq, hF1]
  -- w·n·vpn ≤ w·n·n
  have hRS : (w : ℚ) * ((n : ℚ) * padicValNat p n) ≤ (w : ℚ) * ((n : ℚ) * n) := by
    apply mul_le_mul_of_nonneg_left _ hwq.le
    exact mul_le_mul_of_nonneg_left hvpnq (by positivity)
  -- hN in the w·(1+n²) = w + w·n² form
  have hNexp : 2 * K.cd' + 2 * (L : ℚ) + ((w : ℚ) + (w : ℚ) * ((n : ℚ) * n)) ≤ K.cd * N := by
    have hwexp : ((w : ℚ)) = 2 * (K.s : ℚ) + 1 := by push_cast [hw]; ring
    have hNq : 2 * K.cd' + 2 * (L : ℚ) + (w : ℚ) * (1 + (n : ℚ) * n) ≤ K.cd * N := by
      rw [hwexp, hLdef]; exact hN
    nlinarith [hNq]
  -- final
  have hgoal : K.cd * N ≤ (w : ℚ) * (((n : ℚ) - 1) * (tailExp p n D : ℚ)) := by
    nlinarith [hF5w, hDw, hRS, hNexp]
  calc K.cd * N ≤ (w : ℚ) * (((n : ℚ) - 1) * (tailExp p n D : ℚ)) := hgoal
    _ = (2 * K.s + 1) * ((n : ℚ) - 1) * (tailExp p n (Ddeep n K N) : ℚ) := by
        rw [← hDdef, hw]; push_cast; ring

theorem envelopeExp (n : ℕ) (hn : 2 ≤ n) (K : XConsts n) :
    ∃ N₀ : ℕ, ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧
      ∀ (X : XFamily n), X2ProgressP n X K → X2BridgeP n X → X2AffP n X K → X2CapP n X K →
        X1aAlignP n X ⟨true, false⟩ → WeightChargeFullP n X K →
        X2TailsP n X K → NsNullP n X → X3aRouteP n X K →
        ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N →
          ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N)) := by
  -- n ≥ 2 facts
  have hn2q : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- constants
  set M : ℚ := (2 * K.s + 1) * ((n : ℚ) - 1) with hMdef
  have hMpos : (0 : ℚ) < M := by
    rw [hMdef]; exact mul_pos (by positivity) (by linarith)
  set c4d : ℚ := K.cd / M with hc4ddef
  have hc4dpos : (0 : ℚ) < c4d := div_pos K.cdpos hMpos
  set c4 : ℝ := min (c4d : ℝ) (K.cT * (K.ch : ℝ) / 2) with hc4def
  have hc4pos : (0 : ℝ) < c4 := by
    rw [hc4def]
    refine lt_min (by exact_mod_cast hc4dpos) ?_
    exact div_pos (mul_pos K.cTpos (by exact_mod_cast K.chpos)) (by norm_num)
  set c3 : ℝ := ((n : ℝ) - 1) + K.CT with hc3def
  have hc3pos : (0 : ℝ) < c3 := by rw [hc3def]; have := K.CTpos; linarith
  set Adeep : ℕ :=
    ⌈(2 * K.cd' + 2 * (Nat.log 2 n : ℚ) + (2 * K.s + 1) * (1 + (n : ℚ) * n)) / K.cd⌉₊
    with hAdeepdef
  set Btall : ℕ := ⌈(2 * K.ch' / K.ch : ℚ)⌉₊ with hBtalldef
  set N₀ : ℕ := Adeep + Btall + 1 with hN0def
  refine ⟨N₀, c3, c4, hc3pos, hc4pos, ?_⟩
  intro X PR BR AF CP AL WC TL NS R p _ N hN0
  set C := X.ctx p with hCdef
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  have hp0q : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hpp.pos
  have hp1r : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  -- N₀-derived numeric facts
  have hAdeepN : Adeep ≤ N := by omega
  have hBtallN : Btall ≤ N := by omega
  have hNge1 : 1 ≤ N := by omega
  -- deep numeric hypothesis
  have hN_deep : 2 * K.cd' + 2 * (Nat.log 2 n : ℚ) + (2 * K.s + 1) * (1 + (n : ℚ) * n)
      ≤ K.cd * N := by
    have hxle := Nat.ceil_le.mp (hAdeepdef ▸ hAdeepN)
    rw [div_le_iff₀ K.cdpos] at hxle
    nlinarith [hxle]
  -- tall numeric facts
  have h2ch' : 2 * K.ch' ≤ K.ch * N := by
    have hyle := Nat.ceil_le.mp (hBtalldef ▸ hBtallN)
    rw [div_le_iff₀ K.chpos] at hyle
    nlinarith [hyle]
  have hchN0 : (0 : ℚ) < K.ch * N := mul_pos K.chpos (by exact_mod_cast hNge1)
  have htallpos : (0 : ℚ) < K.ch * N - K.ch' := by nlinarith [h2ch', hchN0]
  have hstar_ge1 : 1 ≤ hstarN n K N := by
    unfold hstarN; exact Nat.one_le_ceil_iff.mpr htallpos
  -- hstarN lower bound (ℝ)
  have hhstarR : (K.ch : ℝ) * N - K.ch' ≤ (hstarN n K N : ℝ) := by
    have hq : (K.ch * N - K.ch' : ℚ) ≤ (hstarN n K N : ℚ) := by
      unfold hstarN; exact Nat.le_ceil _
    exact_mod_cast hq
  -- tall2: ch' ≤ (ch/2)·N in ℝ
  have hN_tall2 : (K.ch' : ℝ) ≤ (K.ch : ℝ) / 2 * N := by
    have hq : K.ch' ≤ K.ch / 2 * N := by nlinarith [h2ch']
    exact_mod_cast hq
  -- ============ core ℚ chain: Undec ⊆ Deep ∪ Tall ============
  have hchainQ : C.frac (C.Undec N)
      ≤ C.frac (DeepEvent C (dstar n K N)) + C.frac (TallEvent C (hstarN n K N)) := by
    obtain ⟨hcover, hnull⟩ := BR p N
    set Wpred : MonicBox n p → Prop :=
      fun f => ∃ b : C.Branch f, IsLeafB C b ∧ NsFreeB C b ∧ N < C.threshold b + capHB C b
      with hWpreddef
    have hUsub : C.Undec N ⊆ {f | f ∈ C.Undec N ∧ ¬ Wpred f} ∪ {f | Wpred f} := by
      intro f hf
      by_cases hw : Wpred f
      · exact Or.inr hw
      · exact Or.inl ⟨hf, hw⟩
    have hstep1 : C.frac (C.Undec N)
        ≤ C.frac {f | f ∈ C.Undec N ∧ ¬ Wpred f} + C.frac {f | Wpred f} :=
      le_trans (C.frac_mono _ _ hUsub) (C.frac_union_le _ _)
    have hnull' : C.frac {f | f ∈ C.Undec N ∧ ¬ Wpred f} = 0 := hnull
    rw [hnull'] at hstep1
    have hWsub : {f | Wpred f} ⊆ DeepEvent C (dstar n K N) ∪ TallEvent C (hstarN n K N) := by
      intro f hf
      obtain ⟨b, hleaf, hnsfree, hlt⟩ := hf
      have hFP : FourthPieceB C b := ⟨Or.inl hleaf, hnsfree⟩
      rcases PR p f b N hFP hlt with hdeep | htall
      · exact Or.inl ⟨b, by unfold dstar; exact Nat.ceil_le.mpr hdeep⟩
      · refine Or.inr ?_
        have hle : hstarN n K N ≤ maxH (C.hist b) := by
          unfold hstarN; exact Nat.ceil_le.mpr htall
        obtain ⟨ν, hν, hνh⟩ :=
          exists_node_of_le_maxH (C.hist b) (hstarN n K N) hstar_ge1 hle
        exact ⟨b, ν, hν, hνh⟩
    have hstep2 : C.frac {f | Wpred f}
        ≤ C.frac (DeepEvent C (dstar n K N)) + C.frac (TallEvent C (hstarN n K N)) :=
      le_trans (C.frac_mono _ _ hWsub) (C.frac_union_le _ _)
    linarith [hstep1, hstep2]
  -- ============ deep leg ℚ bound ============
  have hdeepQ : C.frac (DeepEvent C (dstar n K N))
      ≤ ((n : ℚ) - 1) * (p : ℚ) ^ (-(tailExp p n (Ddeep n K N))) := by
    have hincl : DeepEvent C (dstar n K N)
        ⊆ {f | Ddeep n K N ≤ vdisc f ∨ f ∈ discZero n p} := by
      rintro f ⟨b, hb⟩
      by_cases hdz : f ∈ discZero n p
      · exact Or.inr hdz
      · refine Or.inl ?_
        have hred := x1bReduction X K AL WC p f (C.hist b) (X.gmnLink p f b) hdz
          (C.wf b) (by omega)
        change Ddeep n K N ≤ vdisc f
        unfold Ddeep
        have hkey : 2 * dstar n K N - 2 * Nat.log 2 n ≤ (2 * K.s + 1) * vdisc f := by omega
        calc (2 * dstar n K N - 2 * Nat.log 2 n) / (2 * K.s + 1)
            ≤ ((2 * K.s + 1) * vdisc f) / (2 * K.s + 1) := Nat.div_le_div_right hkey
          _ = vdisc f := Nat.mul_div_cancel_left _ (by omega)
    have hmono := C.frac_mono _ _ hincl
    have hvt := C.vdisc_le_tail (Ddeep n K N)
    have hchain := le_trans hmono hvt
    have htcb := tailCountBound p n (Ddeep n K N) hn
    rw [zpow_natCast] at htcb
    have hzt : (0 : ℚ) < (p : ℚ) ^ (tailExp p n (Ddeep n K N)) := zpow_pos hp0q _
    have hnpD : (0 : ℚ) < (p : ℚ) ^ (n * Ddeep n K N) := pow_pos hp0q _
    have hrhs : ((n : ℚ) - 1) * (p : ℚ) ^ (-(tailExp p n (Ddeep n K N)))
        = ((n : ℚ) - 1) / (p : ℚ) ^ (tailExp p n (Ddeep n K N)) := by
      rw [zpow_neg]; ring
    rw [hrhs]
    refine le_trans hchain ?_
    rw [div_le_iff₀ hnpD, div_mul_eq_mul_div, le_div_iff₀ hzt]
    exact htcb
  -- ============ deep exponent domination: c4·N ≤ tailExp ============
  have hc4dQ : c4d * (N : ℚ) ≤ (tailExp p n (Ddeep n K N) : ℚ) := by
    have hde := deep_exp n hn K p N hN_deep
    rw [hc4ddef, div_mul_eq_mul_div, div_le_iff₀ hMpos, hMdef]
    nlinarith [hde]
  have hc4dR : (c4d : ℝ) * N ≤ (tailExp p n (Ddeep n K N) : ℝ) := by exact_mod_cast hc4dQ
  have hc4Nle : (c4 : ℝ) * N ≤ (tailExp p n (Ddeep n K N) : ℝ) := by
    have hle : (c4 : ℝ) ≤ (c4d : ℝ) := by rw [hc4def]; exact min_le_left _ _
    calc (c4 : ℝ) * N ≤ (c4d : ℝ) * N := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg N)
      _ ≤ _ := hc4dR
  -- ============ tall exponent domination: c4·N ≤ cT·h* ============
  have htallexp : (c4 : ℝ) * N ≤ K.cT * (hstarN n K N : ℝ) := by
    have h1 : (c4 : ℝ) ≤ K.cT * (K.ch : ℝ) / 2 := by rw [hc4def]; exact min_le_right _ _
    have hs1 : (K.cT * (K.ch : ℝ) / 2) * N ≤ K.cT * ((K.ch : ℝ) * N - K.ch') := by
      have hin : (K.ch : ℝ) / 2 * N ≤ (K.ch : ℝ) * N - K.ch' := by linarith [hN_tall2]
      calc (K.cT * (K.ch : ℝ) / 2) * N = K.cT * ((K.ch : ℝ) / 2 * N) := by ring
        _ ≤ K.cT * ((K.ch : ℝ) * N - K.ch') := mul_le_mul_of_nonneg_left hin K.cTpos.le
    have hs2 : K.cT * ((K.ch : ℝ) * N - K.ch') ≤ K.cT * (hstarN n K N : ℝ) :=
      mul_le_mul_of_nonneg_left hhstarR K.cTpos.le
    have hs3 : (c4 : ℝ) * N ≤ (K.cT * (K.ch : ℝ) / 2) * N :=
      mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg N)
    linarith [hs1, hs2, hs3]
  -- ============ deep leg ℝ bound ============
  have hdeepR : (C.frac (DeepEvent C (dstar n K N)) : ℝ)
      ≤ ((n : ℝ) - 1) * (p : ℝ) ^ (-(c4 * N)) := by
    have hzcast : (C.frac (DeepEvent C (dstar n K N)) : ℝ)
        ≤ ((n : ℝ) - 1) * (p : ℝ) ^ (-(tailExp p n (Ddeep n K N)) : ℤ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hdeepQ
      push_cast at h
      exact h
    refine le_trans hzcast ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)
    rw [← Real.rpow_intCast (p : ℝ) (-(tailExp p n (Ddeep n K N)))]
    apply Real.rpow_le_rpow_of_exponent_le hp1r
    push_cast
    linarith [hc4Nle]
  -- ============ tall leg ℝ bound ============
  have htallR : (C.frac (TallEvent C (hstarN n K N)) : ℝ)
      ≤ K.CT * (p : ℝ) ^ (-(c4 * N)) := by
    have hTL := TL p (hstarN n K N)
    refine le_trans hTL ?_
    apply mul_le_mul_of_nonneg_left _ K.CTpos.le
    apply Real.rpow_le_rpow_of_exponent_le hp1r
    linarith [htallexp]
  -- ============ assemble ============
  calc (C.frac (C.Undec N) : ℝ)
      ≤ (C.frac (DeepEvent C (dstar n K N)) : ℝ)
        + (C.frac (TallEvent C (hstarN n K N)) : ℝ) := by exact_mod_cast hchainQ
    _ ≤ ((n : ℝ) - 1) * (p : ℝ) ^ (-(c4 * N)) + K.CT * (p : ℝ) ^ (-(c4 * N)) :=
        add_le_add hdeepR htallR
    _ = (((n : ℝ) - 1) + K.CT) * (p : ℝ) ^ (-(c4 * N)) := by ring
    _ = c3 * (p : ℝ) ^ (-(c4 * N)) := by rw [hc3def]

end LeanUrat.MovesX
