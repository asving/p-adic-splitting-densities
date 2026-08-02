/-
HDISCHARGE_H1 — `H1/Conformance.lean`: B-M2's Lean face (wave 3) — the engine-lift
D8-DATA/(K0)-CONFORMANCE chain.  Unit note: `lean/notes/openmath/H1_BM2_2026-08-06.md`
(Theorem LIFT-CONF, REVISION 2 re-headline; scope split per the note's §S0 table
[REVISION 6 — the pass-4 CRITICAL-1 fold]: what is compiled is — at the
NON-RECENTERING carriers — (K0) at the recorded node's ACTUAL pair, and — at the
RECENTERING carriers — monicity + the SYNTHETIC `K0Conformant σ 1 1` IN THIS FILE
(the actual pair there follows by the sibling unit's compiled transport
`k0_actual_of_recentering`, `H1/RecParamE.lean` [REV 10] — `Node.hspecRec` forces
the pair (1, 1); the WIRING provenance REC-WIRE-G is DISCHARGED [REV 12] by
`recentering_natDegree_eq` + `recParam_eg_of_recentering` (`H1/RecParamE.lean`;
`hi1` and `hrec` are explicit hypotheses, the substantive width/recentering laws
come from `HistoryCoherent`, and `Node.hspecRec` is unused), which SUBSUMES the e-half
transition-hypothesis removal — see the unit note §S2 case (b)),
NOT KP-STEP class membership in either case; KP-STEP's
class is (K0)+(K1)+(K2), and (K1)+(K2) for the fired lifts ride, on [NR], the
OPEN graded (SL-dev) reading GRADED-READ, and on [RC] additionally the open
recentering legs REC-SL [REVISION 8 — the pass-6 finding-1 fold: the former
single-tag form left "the fired lifts" spanning both classes with only
GRADED-READ attached]); governing spec: blueprint §2.2 (s7) [REV 2, finding
15] + the VERIFIED KP-STEP note `H1_BM1_2026-08-06.md` §S7/§S8 (2-clean bar met;
corpus pins verified at pass 4).

WHAT IS COMPILED HERE (all sorry-free; no new axioms; no statement of any landed
unit touched):
* `K0Conformant` — the (K0) CLAUSE at a read: monic of the conformant degree
  e'·g·deg σ.Φ (KP-STEP §S1.3's degree-conformance hypothesis — ONE of the three
  clauses (K0)+(K1)+(K2) of the class KP-STEP quantifies over; (K1)+(K2) are not
  expressed in this file).
* `isReadLift_K0` — THE core: every D8-shaped read lift at a monic parent is
  (K0)-conformant.  This is Lemma PAR-MON's induction STEP (KP-STEP §S3.2,
  verified) compiled: the read-pair transport of the on-file `L3_liftMonic`
  (`Moves/L3_liftMonic.lean`, frame-pair stride σ.e) to the free read stride e'
  — same count, stride freed, `σ.he` replaced by the explicit `1 ≤ e'` binder
  (supplied by `Node.he` at every node).
* `isNodeLift_K0` / `landingKey_K0` / `landingKey_recentering_K0` /
  `historyCoherent_key_K0` / `historyCoherent_recentering_K0` /
  `readsOf_landing_K0` — the per-carrier (K0) read-offs at the three RECORDED
  carriers on which the wiring asserts a key, per class [REVISION 7 — the
  pass-5 CRITICAL-3 fold]: at the NON-RECENTERING ([NR]) carriers (K0) at the
  node's ACTUAL pair; at the RECENTERING ([RC]) carriers the SYNTHETIC
  `K0Conformant σ 1 1` IN THIS FILE ([REV 10]: transported to the node's actual
  pair by the sibling `k0_actual_of_recentering`, `H1/RecParamE.lean`; the unit
  note's §S0 table): coherent interior
  increments (`HistoryCoherent`'s non-recentering leg asserts
  `IsNodeLift νᵢ σᵢ₊₁.Φ`), interior recenterings (`IsRecenteringCore.base`:
  Φ' = Φ − lift, the e·g = 1 degree-preserving face), and the designated landing
  key of EVERY read of a `ReadsOf` run (SideReads clause (iv) — final read
  included, where e ≥ 2 strides are recordable).  That these three carriers
  exhaust the engine's key-firing sites is NOT proved — the unit note's open
  obligation SITE-EXH; these lemmas prove per-carrier implications, not the
  closed-world premise.

WHAT IS NOT CLAIMED (the unit note's §S4 residue — displayed, never consumed):
KP-STEP class membership of any fired lift (the (K1)+(K2) clauses ride the open
graded (SL-dev) READING, GRADED-READ: stage-law digit data → the initial-form
identity in gr(w'); rides the GenuineStageModel seam, A-M2's non-vacuity chain);
at recenterings additionally the (SL-top)/(SL-dev) legs (REC-SL, open — the
`*_recentering_K0` lemmas prove monic-degree-m ONLY); firing-site completeness
(SITE-EXH, open); the ABSTRACT-ENGINE identification (O-2a's pinned Lift_i vs
this corpus = the S-1 transcription audit, [T]); OL-1(b)'s verbatim GMN face
(TR-3-ORD-X, open).  The
(SL-top) stride shape and the marched (SL-dev) DATA (window/weight/twist-residual
laws) are DEFINITIONAL fields of `IsReadLift` (`HC2/Defs.lean:181–191`,
pass-4-verified verbatim) — no theorem restates them here; `isNodeLift_iff`
(`Iff.rfl`) is the on-file definitional tie.  Parent-key monicity is the carried
invariant `Stage.hmonic` (`Moves/Defs.lean:124`; base `Polynomial.monic_X` at
`HC1/T1_baseStage.lean:1547`; re-supplied per transition, e.g.
`MovesD/R7_ramifiedForge.lean:118`) — PAR-MON's corpus carrier.

RG-2 fence display (honesty; REV 4 — the retired location claim removed):
recorded interior non-recentering transitions carry
`νᵢ.e = 1` (the HK-06 recording fence, a DISCLOSED wiring-scope restriction with
its own ledger home) — so `historyCoherent_key_K0`'s recorded instances have
stride 1.  No existence or LOCATION claim is made for e ≥ 2 lifts: the compiled
coverage is per-declaration and conditional (`readsOf_landing_K0` covers the
reads of an ASSUMED `ReadsOf` run, final read included, where e ≥ 2 strides are
recordable; locating ALL fired e ≥ 2 lifts at final reads is the unit note's
open SITE-EXH, and no compiled e ≥ 2 `ReadsOf` existence lemma is on file).
An e ≥ 2 RECENTERING read is VACUOUS at the node level [REV 11 sync — the
pass-9 CRITICAL-4 fold]: `Node.hspecRec` (`MovesC/Defs.lean`, a structure field)
forces e = 1 ∧ g = 1 at every species-recentering node, so an e ≥ 2
species-recentering node cannot be constructed — and the compiled [RC]
conclusion transports to the actual (1, 1) pair anyway (the sibling
`k0_actual_of_recentering`, `H1/RecParamE.lean` [REV 10]).  e ≥ 2 lives only at
NON-RECENTERING reads: interior ones are fenced as above; final `ReadsOf` reads
are recordable.
The compiled declarations quantify over their carrier PREDICATES
(`IsNodeLift`/`IsRecenteringCore`/`LandingKey`/`HistoryCoherent`/`ReadsOf`
antecedents); whether every engine firing satisfies one of those predicates is
exactly the open obligation SITE-EXH [REVISION 6 — the pass-4 CRITICAL-2 fold:
the former "conformance quantifies over FIRED lifts" universal is retired].
-/
import LeanUrat.Scaffold.HDischarge.H1.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesJ

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **(K0) at a read** (KP-STEP §S1.3, the REV-2 degree-conformance hypothesis):
`Φhat` is monic of the conformant degree `e'·g·deg σ.Φ` — ONE clause of the class
the VERIFIED Theorem KP-STEP quantifies over (that class is (K0)+(K1)+(K2);
(K1)+(K2) ride the open GRADED-READ seam and are not expressed here), and — at
NON-RECENTERING sites, where the carrier corollaries conclude at the node's
actual `(e, g)` — OL-1(a)'s normalization `m_{i+1} = e_i·f_i·m_i` (with
`f_i = g` via `Node.hψdeg`) at the site.  At RECENTERING sites this file's
compiled conclusion is the SYNTHETIC pair `K0Conformant σ 1 1`; OL-1(a) at the
site's actual `(e_i, f_i)` follows [REV 10] by the sibling transport
`k0_actual_of_recentering` (`H1/RecParamE.lean`, via `Node.hspecRec`), and the
wiring provenance REC-WIRE-G is DISCHARGED [REV 12] via
`recParam_eg_of_recentering` (subsuming the e-half removal); REC-SL proper
alone stays open (unit note §S2 case (b)/§S4 (i-c)). -/
def K0Conformant (σ : Stage p F) (g e' : ℕ) (Φhat : Polynomial ℤ_[p]) : Prop :=
  Φhat.Monic ∧ Φhat.natDegree = e' * g * σ.Φ.natDegree

/-- **B-M2 core (Lemma PAR-MON's step, compiled)**: every D8-shaped read lift at a
monic parent key is (K0)-conformant.  The read-pair transport of `L3_liftMonic`
(same stride count; frame stride `σ.e` freed to the read's `e'`, `σ.he` replaced
by the explicit `1 ≤ e'`): the top stride `σ.Φ^{e'·g}` is monic of degree
`e'·g·deg σ.Φ` (parent invariant `Stage.hmonic`), and every present lower stride
`t_k·σ.Φ^{e'·k}` (`k < g`, digit in the coefficient window `deg t_k < deg σ.Φ`)
has strictly smaller degree.  No ψ-data beyond the window is consumed: the digit
weight/residual laws ride along untouched. -/
theorem isReadLift_K0 (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
    (he' : 1 ≤ e') (Φhat : Polynomial ℤ_[p])
    (hL : IsReadLift σ ψ g e' h' Φhat) :
    K0Conformant σ g e' Φhat := by
  obtain ⟨tt, htt0, httne, hΦhat⟩ := hL
  -- the leading stride is monic and nonzero
  have hpowg_mon : (σ.Φ ^ (e' * g)).Monic := σ.hmonic.pow _
  have hpowg_ne : σ.Φ ^ (e' * g) ≠ 0 := hpowg_mon.ne_zero
  have hbpos : (⊥ : WithBot ℕ) < (σ.Φ ^ (e' * g)).degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hpowg_ne (Polynomial.degree_eq_bot.mp h))
  -- each present stride has strictly smaller degree than the leading stride
  have hterm : ∀ k ∈ Finset.range g,
      (tt k * σ.Φ ^ (e' * k)).degree < (σ.Φ ^ (e' * g)).degree := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact hbpos
    · have hcoeff : ψ.coeff k ≠ 0 := fun h => htk (htt0 k h)
      have hlt : (tt k).degree < σ.Φ.degree := (httne k hk hcoeff).2.1
      have hpowk_ne : σ.Φ ^ (e' * k) ≠ 0 := (σ.hmonic.pow _).ne_zero
      have hprod_ne : tt k * σ.Φ ^ (e' * k) ≠ 0 := mul_ne_zero htk hpowk_ne
      have hA : (tt k).natDegree < σ.Φ.natDegree :=
        Polynomial.natDegree_lt_natDegree htk hlt
      have hmn : e' * k + 1 ≤ e' * g := by
        have h1 : e' * (k + 1) ≤ e' * g := Nat.mul_le_mul (le_refl e') (by omega)
        have h2 : e' * (k + 1) = e' * k + e' := by ring
        omega
      rw [Polynomial.degree_eq_natDegree hprod_ne, Polynomial.degree_eq_natDegree hpowg_ne,
        Polynomial.natDegree_mul htk hpowk_ne, Polynomial.natDegree_pow,
        Polynomial.natDegree_pow, Nat.cast_lt]
      have h1 : (e' * k + 1) * σ.Φ.natDegree ≤ e' * g * σ.Φ.natDegree :=
        Nat.mul_le_mul hmn (le_refl _)
      have h2 : (e' * k + 1) * σ.Φ.natDegree
          = e' * k * σ.Φ.natDegree + σ.Φ.natDegree := by ring
      omega
  -- the tail has strictly smaller degree than the leading stride
  have hSdeg : (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k)).degree
      < (σ.Φ ^ (e' * g)).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff hbpos]
    exact hterm
  refine ⟨?_, ?_⟩
  · rw [hΦhat]; exact hpowg_mon.add_of_left hSdeg
  · rw [hΦhat, Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_add_eq_left_of_degree_lt hSdeg), Polynomial.natDegree_pow]

/-- (K0) at the node's own read pair: `IsNodeLift` is definitionally `IsReadLift`
at `(ν.ψ, ν.g, ν.e, ν.h)` (`isNodeLift_iff`, `Iff.rfl`), and the read stride is a
genuine polygon side (`ν.he : 1 ≤ ν.e`). -/
theorem isNodeLift_K0 (ν : Node p F) (Φhat : Polynomial ℤ_[p])
    (hL : IsNodeLift ν Φhat) : K0Conformant ν.σ ν.g ν.e Φhat :=
  isReadLift_K0 ν.σ ν.ψ ν.g ν.e ν.h ν.he Φhat ((isNodeLift_iff ν Φhat).mp hL)

/-- **The e·g = 1 refinement face**: subtracting a coefficient-window element from
the monic frame key is degree-preserving monic — (K0) at `e = g = 1` (recenterings;
`1 * 1 * deg σ.Φ = deg σ.Φ`). -/
theorem sub_inC_K0 (σ : Stage p F) (tL : Polynomial ℤ_[p]) (hin : inC σ.Φ tL) :
    K0Conformant σ 1 1 (σ.Φ - tL) := by
  have hlt : (-tL).degree < σ.Φ.degree := by
    rw [Polynomial.degree_neg]; exact hin
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg]; exact σ.hmonic.add_of_left hlt
  · rw [sub_eq_add_neg, Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_add_eq_left_of_degree_lt hlt), one_mul, one_mul]

/-- The landing key fired by a NON-recentering read is (K0)-conformant at the
read's own `(e, g)` (`LandingKey`'s non-recentering leg is `IsNodeLift`). -/
theorem landingKey_K0 (ν : Node p F) (Φtop : Polynomial ℤ_[p])
    (hL : LandingKey ν Φtop) (hspec : ν.species ≠ ReadSpecies.recentering) :
    K0Conformant ν.σ ν.g ν.e Φtop :=
  isNodeLift_K0 ν Φtop (hL.2 hspec)

/-- The landing key fired by a RECENTERING read is (K0)-conformant at `e = g = 1`
(the recorded lift is a coefficient-window center realizer; `Φtop = σ.Φ − lift`). -/
theorem landingKey_recentering_K0 (ν : Node p F) (Φtop : Polynomial ℤ_[p])
    (hL : LandingKey ν Φtop) (hspec : ν.species = ReadSpecies.recentering) :
    K0Conformant ν.σ 1 1 Φtop := by
  obtain ⟨hin, -, -, -, hΦtop⟩ := hL.1 hspec
  rw [hΦtop]
  exact sub_inC_K0 ν.σ ν.lift hin

/-- **Wired interior increments are conformant**: along any coherent recorded
history, at every interior non-recentering transition `i → i+1` the CHILD frame
key is (K0)-conformant at node `i`'s read — monic of degree `νᵢ.e·νᵢ.g·deg σᵢ.Φ`,
OL-1(a)'s degree recursion at the wired sites.  (The child stage's own
`Stage.hmonic` is thereby CONSISTENT with, not independent of, the fired shape —
the re-supply is conformant.)  RG-2 fence: the same coherence leg records
`νᵢ.e = 1` at these sites (disclosed wiring scope; see the file header). -/
theorem historyCoherent_key_K0 (H : History p F) (hH : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hspec : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering) :
    K0Conformant (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).g
      (H.nodes[i]'(by omega)).e ((H.nodes[i+1]'hi1).σ.Φ) := by
  obtain ⟨-, -, -, hstep⟩ := hH
  obtain ⟨-, hnonrec, -, -, -, -, -⟩ := hstep i hi1
  obtain ⟨-, _σV, -, hlift, -⟩ := hnonrec hspec
  exact isNodeLift_K0 _ _ hlift

/-- **Wired interior recenterings are conformant**: at every interior recentering
transition the child frame key is the degree-preserving monic recentering of the
parent key — (K0) at `e = g = 1` (via `IsRecenteringCore.base`). -/
theorem historyCoherent_recentering_K0 (H : History p F) (hH : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hspec : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering) :
    K0Conformant (H.nodes[i]'(by omega)).σ 1 1 ((H.nodes[i+1]'hi1).σ.Φ) := by
  obtain ⟨-, -, -, hstep⟩ := hH
  obtain ⟨hrec, -, -, -, -, -, -⟩ := hstep i hi1
  obtain ⟨-, -, -, hin, -, -, -, hΦ', -⟩ := (hrec hspec).base
  rw [hΦ']
  exact sub_inC_K0 _ _ hin

/-- **Every read of a `ReadsOf` run lands a (K0)-conformant key** (`ReadsOf`, the
f-explicit run predicate): at EVERY read `i` of a run of `f` — the FINAL read
included — the designated landing key `Φnext` (SideReads clause (iv); pinned to
the child frame key at interior reads) is (K0)-conformant: at the read's own
`(e, g)` when the read is not a recentering, at `e = g = 1` when it is.  The
"every" quantifier is INTERNAL to `ReadsOf`: this is the widest compiled carrier
corollary of Theorem LIFT-CONF, and that every engine firing factors through a
recorded carrier is the unit note's open obligation SITE-EXH, not this lemma. -/
theorem readsOf_landing_K0 (n : ℕ) (f : Polynomial ℤ_[p]) (H : History p F)
    (hRO : ReadsOf p F n f H) (i : ℕ) (hi : i < H.nodes.length) :
    ∃ Φnext : Polynomial ℤ_[p],
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      ((H.nodes[i]'hi).species ≠ ReadSpecies.recentering →
        K0Conformant (H.nodes[i]'hi).σ (H.nodes[i]'hi).g (H.nodes[i]'hi).e Φnext) ∧
      ((H.nodes[i]'hi).species = ReadSpecies.recentering →
        K0Conformant (H.nodes[i]'hi).σ 1 1 Φnext) := by
  obtain ⟨-, -, -, hreads⟩ := hRO
  obtain ⟨B, Nd, Φnext, -, hpin, hside⟩ := hreads i hi
  obtain ⟨-, -, -, hland, -, -⟩ := hside
  exact ⟨Φnext, hpin,
    fun hs => landingKey_K0 _ _ hland hs,
    fun hs => landingKey_recentering_K0 _ _ hland hs⟩

end LeanUrat.Scaffold.HDischarge.H1
