/-  TV-H1b (BRIDGE BP3, cluster c2) — [GATE, countermodel-first, risk R2]
    COUNTERMODEL ASSEMBLY for the (then-)banked W17ii clause (ii): the §3.G
    infinite-shDom RS4Chain over TV-H1a's carriers.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.G + §4 (TV-H1b).
    deps: TV-H1a.

    ================= EXECUTION RECORD (gate prover, 2026-07-30) ============
    VERDICT: COUNTERMODEL-COMPILED.  The full ~30-field `negChain` was built
    GREEN per-module over TV-H1a's carriers (import closure = MovesS.Interfaces
    + TV_H1a only; V7_w17ii never in the closure, so no environment contained
    both the sorried universal and the compiled negation).  Axiom census on
    the deliverables (`#print axioms`): w17ii_false / negChain_shDom_infinite /
    negChain_weight_one / negShapeFam_ne all EXACTLY
    [propext, Classical.choice, Quot.sound] — zero sorryAx.
    THE FILLED, GREEN-BUILT TEXT IS ARCHIVED AT
      lean/quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt
    per the coexistence rule (the M1 lesson): a compiled `w17ii_false` may
    never share an environment with the sorried universal `w17ii_wave4`.
    Blocker inventory outcome — ALL CLEARED: RS1Bundle empty-indexed;
    pools_e0/legs_reg via a uniform empty-Act PoolHyp (EscapeE0's Tendsto =
    the constant map in the empty-indexed subsingleton Pi); legs_read VACUOUS
    (allActivePools = M.Pools at the empty-state carrier); rsh_interp
    discharged FOR REAL (k = 0 singleton shape, σ0 = {(1,1)}, Rsh ≡ 1).
    The refutation: clause (ii) at (Ŝ₀, q₀ = 2) demanded HasSum of the
    constant 1 over ↥(Set.univ : Set ℕ) — impossible at every value.
    =========================================================================

    ============ RETIREMENT RECORD (QUEUE ITEM 4 EXECUTED, 2026-07-31) ======
    Asvin sign-off 2026-07-31 (BRIDGE_ADJUDICATIONS_2026-07-30.md, item 4):
    the adjudicated repair (menu (b′) of §3.G REV 2 — the five census fields
    `shdom_fin`/`shdom_no_stray`/`vis_sub_shdom`/`shevt_off_vis`/`shevt_disj`
    on RS4Chain, MovesS/Interfaces.lean) landed IN THIS COMMIT, and
    `w17ii_wave4` clause (ii) is now PROVED for every chain by the counting
    squeeze (MovesV/V7_w17ii.lean, Lean-core; banked C14 sorry retired).

    M1-HYGIENE NOTE (which form the countermodel refutes): the quarantined
    fill refutes clause (ii) at the PRE-2026-07-31 RS4Chain ONLY — the form
    WITHOUT the census fields.  Against the repaired structure the fill does
    not typecheck: its `negChain` has `shDom ≡ Set.univ : Set ℕ` (infinite),
    which `shdom_fin` excludes — the repair cures EXACTLY the refuted law.

    THE E-PHASE SKELETON IS RETIRED (not re-fillable): after the repair,
    (a) `negChain` cannot be constructed with the pinned infinite shDom
    (`shdom_fin` is false there), and (b) `w17ii_false` is REFUTED for every
    possible chain (the proved `w17ii_wave4` applies to all of them) — a
    sorried false statement may not stand in-tree (the honesty invariant).
    The five sorried decls (negShapeFam, negShapeFam_ne, negChain,
    negChain_shDom_infinite, negChain_weight_one, w17ii_false) are DELETED;
    the compiled pre-repair record lives in the quarantine archive (with its
    own dated note) + this header.  What remains compiled below is the CURE
    SEAL at the countermodel's own carriers. -/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesV.TV_H1a

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV.W17iiNeg

/-- THE CURE SEAL (queue item 4, 2026-07-31; trivial BY DESIGN — the point is
that it now typechecks): at the exact TV-H1a carriers that hosted the compiled
countermodel, EVERY repaired chain has a finite height domain at every family
member — the quarantined `negChain` (shDom = Set.univ : Set ℕ, infinite) is
structurally excluded by the queue-item-4 `shdom_fin` field, which is precisely
the law its refutation exploited the absence of. -/
theorem negCarrier_shdom_finite (Fam : MovesS.ShapeFam negTable)
    (C : MovesS.RS4Chain negTable negMS negRB negDegCons negKmatHyp Fam) :
    ∀ Ŝ ∈ Fam.Sh, (C.shDom Ŝ).Finite :=
  fun Ŝ hŜ => C.shdom_fin Ŝ hŜ

end LeanUrat.MovesV.W17iiNeg
