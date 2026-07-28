/-
Unit U10.zc_step  (HC-2 campaign, E-phase — blueprint §5 Layer B: THE HARD CORE OF THE
HARD CORE; the pre-declared escalation-risk center)
moves_ref: §C C.1.5 (per-step conditional exactness): "(1) multiplies the mass by exactly
vol_nom(E_fresh(ν_{i+1})); (2) re-establishes (ZC)".
deps: U3–U7, S (zcSeed, Theta_uni, pres_block), C0.pinTransport, C2.freshFree, C3.lineDom,
hreal (per-step `TransitionAdmissible` via `Realizable`).  difficulty: HARD ×4.
PRE-SPLIT (mandatory, blueprint): U10a floor-monotone downset transport; U10b fresh-cut
downset exactness; U10c interior zeros; U10d rim-lead placement/confinement. The E-phase
renderings below are the elaborator's best-faith decomposition (flagged in MANIFEST;
prover refinement authorized). Whatever step resists derivation is a candidate zcSeed law
(D5's fence) — via the stuck rule, NEVER a silent axiom.
hypothesis_fields: S.zcSeed, hreal.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- U10a — floor-monotone downset TRANSPORT: pins standing before read `i+1` that stay
interior to the NEW rim sit at-or-below the NEW floor (at the new frame's heights). -/
theorem zc_step_transport {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      (mkSigma H n N S vOf (i+1)).pinned j = true →
      ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
        ≤ H.floorH (i+2) (boxChart n N j).2 := by
  -- STATUS (2026-07-28, DC-3 round): DC-3-UNLOCKED, PROVABLE, deferred to the fleet
  -- round.  Route (the general-step analogue of the PROVED U9a `zc_root_downset_mp`):
  -- the recursion supply is now available (`mkSigma_recursion_of_unpinned`, whose
  -- `hunpinned` leg is discharged from `ih` + U3 `mkFresh_band` + `hreal` per the K2
  -- diagnosis), so the pin of `mkSigma … (i+1)` reads off `pinTransportSystem_spec`
  -- clause (2) as (old pin of `Σ_i`) ∨ (fresh cut of read `i`); the new floor is the
  -- old max'd with `ν_{i+1}`'s staircase (`C2_floorH_succ`, PROVED), and the band's
  -- upper edge transports through the new staircase (the general-step floor bridge,
  -- replacing U9a's root-specific `STR₀ = 1`, `Dwidth = 1` collapse).  NOT blocked;
  -- left as a clean `sorry` (statement byte-unchanged, fence held) because the unit
  -- as a whole STOPs at U10c below, so landing this piece would not make U10 done.
  sorry

/-- U10b — fresh-cut downset EXACTNESS: an interior at-or-below-new-floor coordinate is
pinned after read `i+1` (old pin or fresh cut — the downset grows by exactly the strip
zeros + the sub-line levels). -/
theorem zc_step_freshExact {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
          ≤ H.floorH (i+2) (boxChart n N j).2 →
      (mkSigma H n N S vOf (i+2)).pinned j = true := by
  -- STATUS (2026-07-28, DC-3 round): DC-3-UNLOCKED, PROVABLE, deferred (the general-step
  -- analogue of U9b `zc_root_downset_mpr`, whose EXISTENCE obstruction DC-3 discharged —
  -- clauses (3)/(4) now Θ-composed, so `freshAttach_exists` supplies the witness for
  -- EVERY seed under `hunpinned`, itself derivable here from `ih` + U3 + `hreal`).  With
  -- the witness, `mkSigma … (i+2)` unfolds via `mkSigma_recursion_of_unpinned` and the
  -- ⊇ direction closes by the U10a band machinery run backwards (band membership from
  -- the floor-bridge identity).  Left as a clean `sorry`; the unit STOPs at U10c.
  sorry

/-- U10c — interior ZEROS: interior pins of the new state solve to the literal 0. -/
theorem zc_step_interiorZero {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      (mkSigma H n N S vOf (i+2)).pinned j = true →
      ∀ f : (j' : Fin (n * N)) → j' < j → ZMod p,
        (mkSigma H n N S vOf (i+2)).solve j f = 0 := by
  -- STOP-THE-LINE (2026-07-28, DC-3 round) — UNPROVABLE AS STATED; in fact REFUTABLE.
  -- The exact step-analogue of the recorded U9c STOP (`zc_root_interior_zero`), and the
  -- pre-declared stuck-rule firing site (blueprint §5/§6: "whatever step resists
  -- derivation is a candidate zcSeed law, D5's fence").  DC-3 did NOT and could not
  -- unlock this leg — it discharged only the existence/recursion supply (U10a/b/d).
  --
  -- THE OBSTRUCTION (definitional, not effort).  `ZCData.interior_zero` demands a
  -- LITERAL solve `(mkSigma … (i+2)).solve j f = 0`.  `mkSigma … (i+2)` is the choice
  -- `pinTransportSystem`, so its `solve` is `h.choose`'s, constrained ONLY through
  -- `IsFreshAttach`.  Post-DC-3 clauses (3)/(4) give Θ-IMAGE zeros — for `x` with
  -- `x c = solve`, only `S.Theta (i+1) x c = 0` — never `solve = 0`.  Concretely the
  -- witness `freshAttach_exists` builds has strip solve `= U c − corr c = − corr c`
  -- (`U c = 0`), literally `0` IFF the unitriangular correction `corr` of `S.Theta (i+1)`
  -- vanishes on that coordinate.  A raw lawful seed may carry a nonzero constant
  -- correction on a strip coordinate (respecting `Theta_uni`/`pres_theta`/`pres_block`
  -- /`downsets_literal`, which never constrain it) — the U9c `badSeed` — making this
  -- goal FALSE.  So no argument from the current `ZCSeedLaws` + `ih` + U3 + `hreal`
  -- reaches it (`ih.interior_zero` gives OLD literal zeros, which clause (4) only carries
  -- forward as Θ-image zeros).
  --
  -- Second, independent gap (the U9c(ii) analogue): interior VALUE coordinates are not
  -- excluded — nothing forces the read's span slots at/beyond the rim — so a value-pinned
  -- interior coordinate exists whose `solve` is the emitted `vOf`-digit, generically ≠ 0.
  --
  -- REPAIR (designer sign-off, N-queue; FORBIDDEN here by statement-fence / Defs-untouched
  -- / zero-axiom): the Θ-normalization zcSeed law (corrections vanish at read-`i` pinned
  -- coordinates — C.1.5(2)'s (ZC-a) normalized presentation, MOVES 3984–3988), plus the
  -- RootD4-class value-interior-exclusion law.  Statement kept byte-identical per the fence.
  --
  -- ESCALATION CONFIRMED (Fable, second prover, 2026-07-28) — STOP UPHELD after an
  -- independent source-level re-derivation: (a) `IsFreshAttach` clause (3) probes ALL
  -- digit vectors `x` (not just presentational ones), so with `IsUnitriangular`'s
  -- `Θ x c = x c + corr (x|₍<c₎)` EVERY spec witness has strip solve `= −corr` at every
  -- prefix — literal zero IFF `corr ≡ 0` as a total function; (b) no `PresentSeed` /
  -- `ZCSeedLaws` field mentions `Theta` beyond `Theta_uni` (bare existence of `corr`) /
  -- `pres_theta` / `pres_block`, and the in-tree machine-checked `badSeed`
  -- (`scratch_U7_recursion_false.lean`: U27's green gate + the constant shift, corr ≡ 1,
  -- every seed law discharged) lifts one read up (shift at read `i+1`, length `i+2`;
  -- `downsets_literal`/`pres_attain` never see the modified `pres (i+2)`); (c) U10c has
  -- NO `ih`, so even the no-witness fallback branch is unsupported.  SHARPENING for the
  -- designer round: the pending Θ-normalization law must assert `corr = 0` AT ALL RAW
  -- digit vectors (unconditional in `x`) — a law conditioned on `pres` leaves clause
  -- (3)'s arbitrary-`x` forcing (and this ∀-`f` goal) false unchanged.
  sorry

/-- U10d — rim-lead PLACEMENT/CONFINEMENT: every pin of the new state sits inside the
standing read's constraint region (base index < the OLD rim = `prevRim (i+2)`'s
predecessor region; no fresh pin escapes the factor interior — §C rim rule / DOM(3)). -/
theorem zc_step_confine {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N), (mkSigma H n N S vOf (i+2)).pinned j = true →
      (boxChart n N j).2 < H.prevRim n (i + 1) := by
  -- STATUS (2026-07-28, DC-3 round): DC-3-UNLOCKED, PROVABLE, deferred.  Reading the pin
  -- of `mkSigma … (i+2)` off `pinTransportSystem_spec` clause (2) (existence via DC-3's
  -- `freshAttach_exists`) splits it into (old pin of `Σ_{i+1}`, confined by `ih` via
  -- `ih.downset_exact`'s rim guard) ∨ (fresh cut of read `i+1`, confined by U3
  -- `mkFresh_band`'s `prevRim` clause).  Left as a clean `sorry`; the unit STOPs at U10c.
  sorry

/-- U10 assembled — the inductive step: (ZC) at prefix `i+1` re-establishes (ZC) at
prefix `i+2` (the `i+1` instance of `JetSetup.zc` from the `i` instance). -/
theorem zc_step {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (ih : ZCData (mkSigma H n N S vOf (i+1)) (boxChart n N) (H.htH (i+1)) (H.floorH (i+1))
      ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) :
    ZCData (mkSigma H n N S vOf (i+2)) (boxChart n N) (H.htH (i+2)) (H.floorH (i+2))
      ((H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth) := by
  -- STOP-THE-LINE (2026-07-28, DC-3 round): BLOCKED — this packages `downset_exact`
  -- (`fun j hj => ⟨U10a-derived →, zc_step_freshExact j hj⟩`) with `interior_zero :=
  -- zc_step_interiorZero`, and its `interior_zero` field IS U10c, refutable-as-stated
  -- above.  DC-3 unlocked the recursion/existence supply (U10a/b/d), but the assembled
  -- (ZC) re-establishment is FALSE for the U9c `badSeed` until the Θ-normalization zcSeed
  -- law (+ value-interior-exclusion law) are signed off — the pre-declared D5-fence
  -- residue.  Statement byte-unchanged per the fence.
  sorry

end LeanUrat.MovesJ
