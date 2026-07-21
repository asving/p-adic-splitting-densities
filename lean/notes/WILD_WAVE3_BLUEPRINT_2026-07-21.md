# WILD_WAVE3_BLUEPRINT — the H-window: deeper terminating wild strata per type

**Date: 2026-07-21. Authorized by Asvin ("go ahead with the H-window wave"). Successor to
`WILD_WAVE2_BLUEPRINT_2026-07-21.md` (complete: axiom accepted, flag 1 closed).**

## §0. Goal

Extend the σ-keyed menu from ONE canonical stratum per constant-e ramified type to a WINDOW of
them, certifying more of each wild type's density — the certified values grow monotonically in the
window bound toward the type's full (tower) density, which remains the honest wall.

## §1. The arithmetic of admissible heights

For constant-e σ (F := fSum σ = n/e): a single-slope side (0,H)–(n,0) has sideDeg gcd(H,n) and
slope denominator n/gcd(H,n). The stratum carries type σ iff gcd(H,n) = F, i.e. **H = F·k with
gcd(k, e) = 1** (proof: gcd(F·k, F·e) = F·gcd(k,e)). Wave 1 = k = 1. Each such stratum is
single-slope all-μ=1 with the SAME residual shape `wShape σ` (sideDeg = F unchanged), so the banked
counting legs (`hnode_selfloop_over_Bclassify_R`) apply verbatim with H = F·k, threshold
N₀ = H + 1, and the small-N-emptiness route (support-dot valuation < N) gives vanishing below H.
All H-strata share the head tree `[(0, n, F)]` — `typeOfW` (payload-blind beyond dS) already keys
every one to σ; they differ in the face payload (the side), so they are DISTINCT shapes with
disjoint fibers. Expected engine values (n=2): stratum H has density (p−1)·p^{−(H + 1 + ⌈H/2⌉)};
window K ∈ {1,3} at p=2: 1/8 + 1/64 = **9/64**, monotone toward the tower value
(p−1)p⁻³/(1−p⁻³) = **1/7** at p=2 — the wall value the windows approach but never claim.

## §2. Design (additive; K-parameterized)

1. **`OM/WildMenuW3.lean`**: `ramShapes3 n K σ : Finset ClusterShape` (the Tselfloop literals for
   1 ≤ k ≤ K, gcd(k,e) = 1; empty unless constERam), `omMenuW3 n K σ := sepShapesOf n σ ∪
   ramShapes3 n K σ`; **compatibility gate `omMenuW3 n 1 σ = omMenuW n σ`** (definitional or
   proved); injectivity in (σ, k) (σ via typeOfW, k via the payload side), cross-family/cross-σ
   disjointness, per-k `SelfLoopWitness` bundles (H = F·k; gcd(F·k, n) = F lemma), the windowed
   type/menu banks mirroring WildMenu/WildMenuPrep (box bound over the enlarged union; per-σ
   monotone staircase: legs join at N = F·k + 1; small-N vanishing per leg).
2. **`OM/RealInstanceW3.lean`**: `realMW3 n K hn` / `realDW3` / `realFW3` (density := windowed
   menu sum) + capstones `montes_unconditional_w3 (K)` (+`_exhaustive`), statements verbatim the
   Wave-1 ones with `omMenuW3 n K`; K = 1 must recover Wave 1's values.
3. **Gates (`OM/RealInstanceW3Gates.lean`)**: (G1) n=2, p=2, K=3: certified value = 9/64 through
   the real instance; (G2) window monotonicity: value(K=3) > value(K=1) = 1/8 (machine-checked
   strict growth — the "approaching the tower" narrative); (G3) census zero-regression, all
   core-only; (G4) mutation `C := 0` fails; (G5) Python brute force: the H=3 (n=2) and H=2 (n=3,
   e=3) strata, anchors (p−1)/p⁶ at p ∈ {2,3}.
4. **Axiom re-scope (guardian-gated, W3c)**: restate `om_leaf_faithful` over `T ∈ omMenuW3 n K σ`
   (∀ K) — a strict generalization whose K = 1 instance is the accepted Wave-2 form; same cite
   (Cor 1.20 applies verbatim to every all-μ=1 single-slope stratum with gcd(H,n) = F), same
   guard-soundness route (per-leg small-N emptiness). NEW axiom-free anchor for the probe: the
   n=2, H=3 stratum is ℚ_p-irreducible by the ELEMENTARY two-root valuation contradiction
   (roots a,b: v(a)+v(b) = 3, v(a) ≤ 1 ⟹ v(a+b) ≤ 1 < 2 ≤ v(a₁) — no Newton polygon needed);
   re-run both mutation probes (split-type and fine-swap) at the H=3 stratum. Full guardian
   re-audit BEFORE push (statement change to a declared axiom). Old axiom form retired in the
   same commit (the new one subsumes it at K = 1); consumers (`menuFiber_hasType` etc.) re-pointed.

## §3. Honest scope (docstrings)
Window-K certifies the K-truncated decided density of each constant-e type — a strictly larger
leading sum than Wave 1, still NOT the full type density (the geometric tail = the recursive
self-loop wall / Denef); mixed-e and order ≥ 2 unchanged. No exhaustiveness claim.
