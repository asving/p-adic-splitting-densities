# UNIT H2L — the slope-h≥2 recentring currency (IFCG75.lean) — VERDICT

STATUS: **LANDED GREEN** (2026-08-31). `leanfinal/Uniformity/ChapI/IFCG75.lean`,
2433 lines, ZERO sorries, ZERO new axioms/cites; every AxCheck footprint (35 rows)
is pure Lean core `{propext, Classical.choice, Quot.sound}`. Aggregator import added
(`Uniformity/ChapI.lean` line 115); `lake build Uniformity.ChapI.IFCG75` green
(8960 jobs); `lake env lean Uniformity/ChapI.lean` green. IFCG74 untouched.

Source design: `runs/codex/H2C_design.md` (sol-high). Transcribed per its §9 landing
order. The design's central verdict is ENFORCED: the naive ring `O[X]/(X^e − zπ^h)`
is never claimed to be a DVR/local/complete (FALSE for h ≥ 2 — not normal); the
correct object is the Bézout-normalized Eisenstein presentation.

## What landed (all Lean-core, machine-checked)

LAYER 1 (the design's normalization/coordinate/finite-transport layer):
- §1 Bézout arithmetic. Single pin `(B): a·h = b·e + 1` — positivity of a, h AND
  coprimality gcd(h,e)=1 are DERIVED from (B) (`bezout_pos`, `bezout_coprime`):
  smaller trusted surface than the design's redundant hypothesis list. Existence
  (`bezout_exists`, via ZMod inverse) and uniqueness of a ∈ {1..e−1}. The
  multiplication-by-h permutation i ↦ h·i % e with EXPLICIT inverse j ↦ a·j % e
  (`bezout_hmul_mod_injOn/surjOn` — no finiteness argument, the pin cancels
  directly). Carry arithmetic: `bezout_cceil_shift` (⌈(w−r)/e⌉⁺ − q = ⌈(w−s)/e⌉⁺ for
  s = eq+r) and `bezout_cceil_level` (level collapse at w = eN).
- §2 The presentation. O' := AdjoinRoot (eisKey π (−(u^a)) e) = O[Y]/(Y^e − u^a·π) —
  an IFCG39 Eisenstein key at unit parameter −u^a, so the ENTIRE landed h=1 cascade
  instantiates verbatim: `bez_recentring_stack` (complete DVR, finite residue field,
  residueCard UNCHANGED), `bez_root_irreducible`, `bez_map_pow_maximalIdeal`
  ((𝔪^K)O' = 𝔪'^{eK}). Pins (R): `bez_root_pow` γ^e = u^a·π; ξ := u^{−b}·γ^h with
  `bezXi_pow_e` ξ^e = u·π^h and `bezXi_pow_a` ξ^a = π^b·γ (the concrete
  fraction-field equality). Units handled in Oˣ (no inverse-choice plumbing).
- §3 The order embedding. `bezRawKey` κ = X^e − C(u·π^h) (monic, deg e; NO ring
  claims); `bezOrderMap` ι : A →+* O' via AdjoinRoot.lift at ξ (well-definedness IS
  (R2)); characterizations (mk/root/algebraMap); ★ `bezOrderMap_injective` via the
  coordinate permutation (a deg-<e relation among ξ-powers becomes one among the
  free power basis γ^0..γ^{e−1}). The design §3.3 obstruction (A/π^N → O'/γ^{eN} not
  injective; the (2,3) example) recorded in the docstring — the false h=1-style
  transport is structurally blocked.
- §4 The coordinate lattice. δ_i := u^{a·q_i}·u^{−b·i} ∈ Oˣ (`bezDelta`); (C1)
  `bezXi_pow` ξ^i = δ_i·π^{q_i}·γ^{r_i} for EVERY i; the permuted-sum lattice core;
  ★ (L-raw) `bez_root_pow_dvd_orderMk_iff`: γ^w ∣ ι(mk P) ⟺ π^{⌈(w−h·i)/e⌉⁺} ∣ P_i;
  Θ (C2) `bezTheta` (O-linear, deliberately NOT a ring map — carries removed) with
  inverse `bezThetaInv` (canonical rep, un-permute, strip units), round trips both
  ways, ★ (L-norm) `bez_root_pow_dvd_theta_iff`, ★ (L-level) `bez_theta_level_iff`
  γ^{eN} ∣ Θ(P) ⟺ π^N ∣ P_i — the exact reason Θ (not ι) supports the finite boxes.
- §5 The normalized development + transport. `bezDevT` (D) / `bezReassT` with
  coeff/monic/round-trip lemmas and TWO-WAY level exactness
  (`bezDevT_sub_root_pow_dvd`, `bezReassT_sub_pi_pow_dvd`); ★★★ `bezCellTransport` :
  Coeff O (e·k) N ≃ Coeff O' k (e·N) with the SAME three interface theorems as
  IFCG43 (`_apply`, `_symm_apply`, `_card_image` — count preservation UNCONDITIONAL)
  and the count pin `bez_card_coeff` #Coeff(O',k,eN) = q^{k·e·N}.

LAYER 2 (stated, NOT asserted — the cite surface):
- ★★★ `SlopeBezoutFactorCorrespondenceAt h k` — the named Prop in the
  IFCG48.FactorCorrespondenceAt genre (which is its h=1 instance): slope lattice +
  Bézout deep box (A) ⟹ Multiset.Rel matching monicFactors g ↔ monicFactors
  (bezDevT g) with (e,f) ↦ (e·e, f) legs. NEVER asserted, no axiom.
- `SlopeBezoutCellTypeScalingAt` (typeOf form); (TS)
  `slopeBezoutCellTypeScalingAt_of_correspondence` fires through IFCG48's
  `typeOf_eq_scaleType_of_rel` VERBATIM (the multiset/(e,f) engine is generic in the
  Eisenstein unit — only the correspondence itself is new mathematics).
- (DT) `bez_transport_decidedAt_iff` (+ `_of_correspondence` socket): DecidedAt O' k
  σ' (eN) (transport c) ⟺ DecidedAt O (e·k) (scaleType e σ') N c — IFCG47 §2's
  skeleton against the Bézout transport; ordinary DecidedAt, no weakened predicate.
  Lattice/box premises in ∀-lift form (the full-span side pins at slope h/e).

FIRED OUTRIGHT (design §5, recommended-proved-not-cited — and it proved):
- ★★★ (RB) `bez_transfer_digits_iff`: box (A) ⟺ digits read (X − ū)^k — the C110
  binomial replay with π^{h(s−t)} shifts; the carry q_i cancels between lattice
  supply and box line at every slot i ≥ 1 (new lemmas `bez_pure_exp`,
  `bez_lat_exp_pos`); the +1 at slot 0 is the digit pin paid by the binomial
  vanishing. `bez_xres_eq_pow_iff_box`: the sector-facing form, residual side from
  IFCG44's landed `xres_eq_pow_iff_digits_h`; the box side is BYTE-IDENTICAL to the
  Layer-2 Prop's hypothesis — the census residual objects and the cite surface meet.
- ★ `bez_box_exponent_identity`: Σ_{t<k}Σ_{i<e} λ_{t,i} = Σ_{j<ek}⌈h(ek−j)/e⌉ + k —
  the design's "hostile test of all +1 and carry conventions"; passed; aligns the
  box cost with IFCG64's `card_slopeBox` exponent (q^{ekN − Σ⌈⌉ − k}).

## Master rows: none recomputed (honest)

IFCG62's honesty fence named "the per-frame count/decision transports (the analogues
of cellTransport/transport_decidedAt_iff at h ≥ 2 and over the compositum)" as THE
named open set behind the MixedFaceLaw h≥2 axes. THIS unit supplies them at the
(h ≥ 2, d = 1) axis: count transport unconditional, decision transport conditional
on exactly the named correspondence — as the design mandates. No existing master
premise closes outright (the per-frame MixedFaceLaws still need the counting
campaign + the signed correspondence), so no master row changes. NOTE: everything in
IFCG75 is ∀-complete-DVR, so the (h ≥ 2, d ≥ 2) axis gets its coordinate currency by
instantiating O := AdjoinRoot φ (IFCG62's compositum stage) verbatim — that wiring
is a future unit's.

## Named remainders (exact, none load-bearing for the currency)

1. THE cite decision (design §9 item 7, OWNER-GATED by standing policy): whether to
   sign `SlopeBezoutFactorCorrespondenceAt` as a fourth FGMNCitePackage leg — only
   after the §8 dictionary audit (source normalizer must produce exactly
   (q_i, r_i, δ_i) incl. the unit z^{a·q_i − b·i}; transformed polynomial must be
   bezDevT (D), NOT the raw scalar extension; factors matched with multiplicity;
   FGMN Thm 6.4 is the plausible genre). CP2's legs E (h=1) and R (squarefree) do
   NOT certify it. If the audit fails to expose the exact normalized transform,
   keep it a hypothesis — never weaken (DT).
2. `bezoutAlphaBox` as a SUBSET of Coeff O' k (eN) + its cardinality (Count): the
   base-side box, criterion, and total exponent are landed; what remains is the
   Res O' (eN) ≅ (Res O N)^e coordinate read of the set (via bez_theta_level_iff)
   and the per-coordinate resOrd count — mechanical against LocalData's card kit.
3. `bezout_isIntegralClosure` (presentational; injectivity + (R3) + the DVR stack
   carry the operative content).
4. The resPoly-frame wrapper of (RB) (xres is the census currency per IFCG44; the
   resFieldXEquiv dance is IFCG43's, mechanical).

## Files touched
- NEW: leanfinal/Uniformity/ChapI/IFCG75.lean (2433 lines, green, Lean-core).
- leanfinal/Uniformity/ChapI.lean: +1 import line (IFCG75, after IFCG74).
- runs/wave-c/verdict_H2L.md (this file).
