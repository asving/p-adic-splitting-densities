/-
Unit SW1.ShapeWF_of_matches  (MovesD campaign, E-phase)  [REV 6 — the universe-loss
guard; REV 8, Codex#6 c.2 — MonicTie now DERIVED except its one genuinely encoding-level
clause; REV 9, Fable#7 G-1/G-2 — hw0 named + the wchain mechanism written in]
moves_ref: (the L3 dictionary: every note-η's shape is dictionary-image — so the subtype
loses NOTHING of the note's universe). THE MONICTIE DERIVATION [REV 8]: monicTop → r = 0
is DERIVED (`hmonicRoot` + `root_iff` via Matches); the RESIDUE — the root read's
monicTop ↔ (s0 + wSide = n) — is the named encoding gap ENC-MONIC, kept as the WEAKEST
SUFFICIENT hypothesis `hmt0` ("slot 3 = the monic lead, digit 1", §D4-R.6).
deps: E4, E5, E10.
sketch: transport each certificate clause from the matched history: species_iff from
`History.root_iff`; window/dchain from `HistoryCoherent`; gmu from E5 (hOrd) + E4; edvd
from `Node.hEdvd`; root_box from `InBox`; gamTie from coherence's γ-tie clause + Matches
+ D6a (strS); anchorTie from `Node.hAnchor` + `hbezCanon`-uniqueness against `bezT`;
w0 from `hw0` + Matches' pool-card clause (exponent-injectivity at p ≥ 2); wchain via
`TransitionData.child_field` + E10's field-tower card lemma (hψirr/hψmonic/hψdeg/
hzbarRoot), recenterings via `IsRecenteringCore` K-equality + `hspecRec`.
difficulty: medium-hard.
hypothesis_fields: `hmt0` (ENC-MONIC), `hw0` (ROOT-POOL) — both ledgered, §2.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.E5_gmuLe
import LeanUrat.MovesD.E10_towerCard

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- **The canonical Bézout coefficient is `bezT`**: any Bézout coefficient `t` of a side
`(e, h)` (lowest terms) lying in the window `[0, e)` is exactly `bezT e h` — the reduction
of `xgcd`'s coefficient modulo `e`. This is the `hbezCanon`-uniqueness the anchor read needs
(§D.3(c) stride anchor; rev 14's `t^B` is a function of `(e, h)` alone). -/
private lemma t_eq_bezT {e h : ℕ} (he : 1 ≤ e) (hcop : Nat.gcd e h = 1)
    {t s : ℤ} (htlo : 0 ≤ t) (hthi : t < (e : ℤ)) (hbez : (e : ℤ) * s + (h : ℤ) * t = 1) :
    t = bezT e h := by
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hbezT : bezT e h = ((Nat.xgcd e h).2) % (e : ℤ) := by
    unfold bezT
    rw [Int.add_emod_right, Int.emod_emod_of_dvd _ (dvd_refl (e : ℤ))]
  have hAB : (e : ℤ) * (Nat.gcdA e h) + (h : ℤ) * ((Nat.xgcd e h).2) = 1 := by
    have H := Nat.gcd_eq_gcd_ab e h
    rw [hcop] at H
    simpa [Nat.gcdB] using H.symm
  have hcopZ : IsCoprime (e : ℤ) (h : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa using hcop
  have hdvd : (e : ℤ) ∣ (t - (Nat.xgcd e h).2) := by
    have hh : (h : ℤ) * (t - (Nat.xgcd e h).2) = (e : ℤ) * ((Nat.gcdA e h) - s) := by
      linear_combination hbez - hAB
    have hdmul : (e : ℤ) ∣ (h : ℤ) * (t - (Nat.xgcd e h).2) := ⟨(Nat.gcdA e h) - s, hh⟩
    exact hcopZ.dvd_of_dvd_mul_left hdmul
  have hmodeq' : t % (e : ℤ) = (Nat.xgcd e h).2 % (e : ℤ) := by
    have : t ≡ (Nat.xgcd e h).2 [ZMOD (e : ℤ)] :=
      Int.modEq_iff_dvd.mpr (by rw [← neg_sub]; exact (dvd_neg).mpr hdvd)
    exact this
  rw [hbezT, ← hmodeq']
  exact (Int.emod_eq_of_lt htlo hthi).symm

/-- Every matched coherent in-box history's shape carries the certificate — the note's
universe is not lost to the subtype (ENC-MONIC = hmt0, ROOT-POOL = hw0; §2 ledger). -/
theorem ShapeWF_of_matches {Q : ShapePrefix} {H : History p F} (hM : Q.MatchesHist H)
    (hcoh : HistoryCoherent H) (hbox : InBox n H)
    (hmt0 : ∀ h0 : 0 < Q.reads.length,
      ((Q.reads[0]'h0).monicTop = true ↔ (Q.reads[0]'h0).s0 + (Q.reads[0]'h0).wSide = n))
    (hw0 : ∀ hj : 0 < H.nodes.length, Nat.card ↥((H.nodes[0]'hj).σ.K) = p) :
    ShapeWF n Q := by
  obtain ⟨hlen, hmatch⟩ := hM
  obtain ⟨hrootdeg, hslope, hgam, htrans⟩ := hcoh
  have hp2 : 2 ≤ p := Nat.Prime.two_le Fact.out
  -- STR is shape data: the `e`-product over the retained prefix matches nodewise.
  have hmape : ∀ i, (H.nodes.take i).map Node.e = (Q.reads.take i).map ShapeRead.e := by
    intro i
    apply List.ext_getElem
    · simp [hlen]
    · intro j hj1 _
      have hjn : j < H.nodes.length := by
        simp only [List.length_map, List.length_take] at hj1; omega
      simp only [List.getElem_map, List.getElem_take]
      exact (hmatch j hjn).2.1
  have hstr : ∀ i, H.strFrame i = Q.strS i := by
    intro i
    change ((H.nodes.take i).map Node.e).prod = ((Q.reads.take i).map ShapeRead.e).prod
    rw [hmape i]
  refine
    { species_iff := ?_
      root_box := ?_
      window := ?_
      gmu := ?_
      edvd := ?_
      dchain0 := ?_
      dchain := ?_
      monic := ?_
      w0 := ?_
      wchain := ?_
      gamTie := ?_
      anchorTie := ?_ }
  · -- species_iff
    intro r hr
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨hsp, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hmatch r hr0
    have hri := H.root_iff r hr0
    rw [hsp] at hri
    exact hri
  · -- root_box
    intro h0
    have h0' : 0 < H.nodes.length := by omega
    obtain ⟨_, _, _, _, _, _, hs0, hws, _, _, _, _, _⟩ := hmatch 0 h0'
    have hb := hbox h0'
    rw [hs0, hws] at hb
    exact hb
  · -- window
    intro r hr
    have hr1 : r + 1 < H.nodes.length := by omega
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, _, _, _, hmu_r, _, _, _, _, _, _, _, _⟩ := hmatch r hr0
    obtain ⟨_, _, _, _, _, _, hs0_1, hws_1, _, _, _, _, _⟩ := hmatch (r + 1) hr1
    obtain ⟨_, _, _, _, hwin, _, _⟩ := htrans r hr1
    rw [hs0_1, hws_1, hmu_r] at hwin
    exact hwin
  · -- gmu
    intro r hr
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, he, _, hg, hmu, _, _, hws, _, _, _, _, _⟩ := hmatch r hr0
    have hE := gmu_le_len (H.nodes[r]'hr0)
    rw [hg, hmu, hws, he] at hE
    exact hE
  · -- edvd
    intro r hr
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, he, _, _, _, _, _, hws, _, _, _, _, _⟩ := hmatch r hr0
    have hE := (H.nodes[r]'hr0).hEdvd
    rw [he, hws] at hE
    exact hE
  · -- dchain0
    intro h0
    have h0' : 0 < H.nodes.length := by omega
    obtain ⟨_, _, _, _, _, _, _, _, hDw, _, _, _, _⟩ := hmatch 0 h0'
    have hval : (H.nodes[0]'h0').Dwidth = 1 := by
      rw [(H.nodes[0]'h0').hDwidth]; exact hrootdeg h0'
    rw [hDw] at hval
    exact hval
  · -- dchain
    intro r hr
    have hr1 : r + 1 < H.nodes.length := by omega
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, he, _, hg, _, _, _, _, hDw_r, _, _, _, _⟩ := hmatch r hr0
    obtain ⟨_, _, _, _, _, _, _, _, hDw_1, _, _, _, _⟩ := hmatch (r + 1) hr1
    obtain ⟨_, _, _, _, _, hdw, _⟩ := htrans r hr1
    have hval : (H.nodes[r+1]'hr1).Dwidth
        = (H.nodes[r]'hr0).e * (H.nodes[r]'hr0).g * (H.nodes[r]'hr0).Dwidth := hdw
    rw [hDw_1, he, hg, hDw_r] at hval
    exact hval
  · -- monic (MonicTie)
    intro r hr
    rcases Nat.eq_zero_or_pos r with hr0eq | hrpos
    · subst hr0eq
      constructor
      · intro hmt
        exact ⟨rfl, (hmt0 hr).mp hmt⟩
      · rintro ⟨_, hn⟩
        exact (hmt0 hr).mpr hn
    · constructor
      · intro hmt
        exfalso
        have hsprc := (Q.reads[r]'hr).hmonicRoot hmt
        have hrH : r < H.nodes.length := by omega
        obtain ⟨hsp, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hmatch r hrH
        have hr0' : r = 0 := (H.root_iff r hrH).mp (hsp.trans hsprc)
        exact absurd hr0' (by omega)
      · rintro ⟨h0, _⟩
        exact absurd h0 (by omega)
  · -- w0
    intro h0
    have h0' : 0 < H.nodes.length := by omega
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcard, _⟩ := hmatch 0 h0'
    have hp := hw0 h0'
    have hpe : p ^ (Q.reads[0]'(by omega : 0 < Q.reads.length)).w = p := hcard.symm.trans hp
    have hpw : p ^ (Q.reads[0]'(by omega : 0 < Q.reads.length)).w = p ^ 1 := by
      rw [pow_one]; exact hpe
    exact Nat.pow_right_injective hp2 hpw
  · -- wchain
    intro r hr
    have hr1 : r + 1 < H.nodes.length := by omega
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, _, _, hg_r, _, _, _, _, _, _, _, hcard_r, _⟩ := hmatch r hr0
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcard_1, _⟩ := hmatch (r + 1) hr1
    obtain ⟨hrecC, hnrC, _, _, _, _, _⟩ := htrans r hr1
    by_cases hrec : (H.nodes[r]'hr0).species = ReadSpecies.recentering
    · -- recentering: K unchanged, g = 1
      have hRC := hrecC hrec
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hKeq, _, _, _⟩ := hRC.base
      have hg1 : (H.nodes[r]'hr0).g = 1 := ((H.nodes[r]'hr0).hspecRec hrec).2
      have hRg1 : (Q.reads[r]'(by omega : r < Q.reads.length)).g = 1 := by
        rw [← hg_r]; exact hg1
      have key0 : p ^ (Q.reads[r+1]'(by omega : r + 1 < Q.reads.length)).w
          = p ^ ((Q.reads[r]'(by omega : r < Q.reads.length)).w
              * (Q.reads[r]'(by omega : r < Q.reads.length)).g) := by
        calc p ^ (Q.reads[r+1]'(by omega : r + 1 < Q.reads.length)).w
            = Nat.card ↥(H.nodes[r+1]'hr1).σ.K := hcard_1.symm
          _ = Nat.card ↥(H.nodes[r]'hr0).σ.K := by rw [hKeq]
          _ = p ^ (Q.reads[r]'(by omega : r < Q.reads.length)).w := hcard_r
          _ = p ^ ((Q.reads[r]'(by omega : r < Q.reads.length)).w
                * (Q.reads[r]'(by omega : r < Q.reads.length)).g) := by rw [hRg1, Nat.mul_one]
      exact Nat.pow_right_injective hp2 key0
    · -- increment/root: residue tower, card raised to the g-th power
      have hnr := hnrC hrec
      have hcf : (H.nodes[r+1]'hr1).σ.K
          = (H.nodes[r]'hr0).σ.nextField (H.nodes[r]'hr0).zbar := hnr.2.base.child_field
      have hcardstep : Nat.card ↥(H.nodes[r+1]'hr1).σ.K
          = (Nat.card ↥(H.nodes[r]'hr0).σ.K) ^ (H.nodes[r]'hr0).g := by
        rw [hcf]
        exact fieldTower_card (H.nodes[r]'hr0).hψirr (H.nodes[r]'hr0).hψmonic
          (H.nodes[r]'hr0).hψdeg (H.nodes[r]'hr0).hzbarRoot
      have key0 : p ^ (Q.reads[r+1]'(by omega : r + 1 < Q.reads.length)).w
          = p ^ ((Q.reads[r]'(by omega : r < Q.reads.length)).w
              * (Q.reads[r]'(by omega : r < Q.reads.length)).g) := by
        calc p ^ (Q.reads[r+1]'(by omega : r + 1 < Q.reads.length)).w
            = Nat.card ↥(H.nodes[r+1]'hr1).σ.K := hcard_1.symm
          _ = (Nat.card ↥(H.nodes[r]'hr0).σ.K) ^ (H.nodes[r]'hr0).g := hcardstep
          _ = (p ^ (Q.reads[r]'(by omega : r < Q.reads.length)).w) ^ (H.nodes[r]'hr0).g := by
                rw [hcard_r]
          _ = p ^ ((Q.reads[r]'(by omega : r < Q.reads.length)).w * (H.nodes[r]'hr0).g) := by
                rw [← pow_mul]
          _ = p ^ ((Q.reads[r]'(by omega : r < Q.reads.length)).w
                * (Q.reads[r]'(by omega : r < Q.reads.length)).g) := by rw [hg_r]
      exact Nat.pow_right_injective hp2 key0
  · -- gamTie
    intro r hr
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, he, hh, _, _, _, hs0, hws, _, hus, hgm, _, _⟩ := hmatch r hr0
    have hg := hgam r hr0
    rw [hgm, he, hus, hs0, hws, hh, hstr r] at hg
    exact hg
  · -- anchorTie
    intro r hr
    have hr0 : r < H.nodes.length := by omega
    obtain ⟨_, he, hh, _, _, ha, hs0, _, _, _, hgm, _, _⟩ := hmatch r hr0
    have hanch := (H.nodes[r]'hr0).hAnchor
    have htb : (H.nodes[r]'hr0).t = bezT (H.nodes[r]'hr0).e (H.nodes[r]'hr0).h :=
      t_eq_bezT (H.nodes[r]'hr0).he (H.nodes[r]'hr0).hcop
        (H.nodes[r]'hr0).hbezCanon.1 (H.nodes[r]'hr0).hbezCanon.2 (H.nodes[r]'hr0).hbez
    rw [htb, he, ha, hs0, hh, hgm] at hanch
    exact hanch

end LeanUrat.MovesD
