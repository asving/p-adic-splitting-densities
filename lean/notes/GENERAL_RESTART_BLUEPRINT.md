# GENERAL_RESTART_BLUEPRINT — the restart lemma at all orders / all (e,h,f)

2026-07-06. Synthesis of the W6-frontier numeric exploration (workflow wf_082d7ea9-c8b: three
independent explorers, exact arithmetic + PARI, discover-and-refute). This is the MATH foundation
for the Lean waves W6a-residual / W6b / W6c — written per Asvin's directive "run the math and the
blueprint first, don't just push Lean." Everything below is gate-verified (0-mismatch) or a
precisely-named open point. Companion to RESTART_LEMMA.md (§8 w-table, §10/§13 the restart) and
PHASEB_CLASSIFIER_BLUEPRINT.md (§8 wave plan, W6a-corrected).

Status of what is ALREADY machine-checked (do not re-derive): the h=1, e-general, f=1 single-block
restart is `RestartEquiv.restartEquiv` (a genuine bijection, referee-gap heart). W6a
(`RphiRingGenH`) banked the general-(e,h) gapped filtration ring structure with the h=1 compat.
This blueprint fills the general-h / f≥2 / deeper-order gaps ON TOP of those.

--------------------------------------------------------------------------------
## §1 The unified fresh-cluster pattern (the one formula)

For a cluster refined by a key of ramification `e`, slope numerator `h` (gcd(e,h)=1), residual an
irreducible of degree `f` to multiplicity `μ ≥ 2`, over a base with residue field `F_q` (q = p^k):

Child ring:  `R = O''[X] / (X^e − c·p^h)`,  `O''` = unramified degree-f over the base (residue
`GaloisField p (k·f)`, i.e. F_{q^f}).  θ = X.  Valuation `vL(Σ a_i θ^i) = min_i (i·h + e·v(a_i))`.

**FRESH-CLUSTER PATTERN (gate-verified, 0 mismatches across all feasible cases):**
```
   FreshClusterPattern β  :=  ∀ j < μ,  vL(β_j) ≥ e·h·(μ − j) + 1
                              i.e.  β_j ∈ filtIdeal( e·h·(μ−j) + 1 )
```
* The floor scales by the FULL vL-slope `e·h` (the vL-avatar of the parent vphi-slope −h/e).
* STRICT (the `+1`), RESIDUE-FREE (verified at p=3: the leading digit at the floor ranges over
  all of F_p^*; vertex-exactness + binomial residues are carried by the cap φ^μ, not the digits —
  same mechanism as h=1).
* Collapses to the banked h=1 form `e(μ−j)+1` exactly (h=1 sanity + μ=3 h=1 controls reproduce it).
* f≥2: the SAME strict e-scaled floor, only the residue field enlarges p → q^f. No new pattern.

**FIBER CARDINALITY — the per-digit product count (NOT p^(Q·e·N − w)):** because the value
semigroup ⟨e,h⟩ is GAPPED for h≥2 (W6a), a filtration ideal's card is the per-digit product
```
   card( filtIdeal w )  =  Q^( Σ_{i<e} ( N − min(N, ⌈(w − i·h)/e⌉⁺) ) ),   Q = q^f = p^{kf}
```
(⌈·⌉⁺ = clamp to ≥0). The closed fiber card, valid in the readable regime N ≥ hμ+1, is
`Q^( μ·e·N − μ·C(e,h) − e·h·μ(μ+1)/2 )`, C(e,h)=Σ_{i<e}⌈(1−ih)/e⌉ (=1 at h=1, and negative for
larger h — see §5 caveat 1). USE THE PER-DIGIT PRODUCT in Lean, not the closed form (robust to
clamping).

**EMPTINESS / MARGIN:** the cell's left vertex is at height H = h·μ; vertex-exactness is
certifiable only at `N ≥ hμ + 1`. Below that the InCell fiber is UNINHABITED (gate R1: (2,3,2) is
0/65536 at N=5, N=6; nonempty first at N=7). Carry `h·μ < N` (with `h < N` so p^h ≠ 0) as a
hypothesis on every fiber/InCell lemma. This is the h-scaled version of the W0/W4d0 "F1"
left-endpoint-readability erratum.

--------------------------------------------------------------------------------
## §2 GUARDRAILS — the refuted naive forms (do NOT state these)

Each was tempting and each is FALSE (counterexamples from the gate, h≥2):
* `β_j ∈ (θ)^k` (θ-adic coset) — UNSOUND for h≥2 (no valuation-1 uniformizer; use `filtIdeal`).
* floor `e(μ−j)+1` (ignoring h) — (3,2,2) gives [5,3], true is [13,7].
* floor `h(μ−j)+1` — [5,3] ≠ [13,7]. floor `e(μ−j)+h` — [8,5] ≠ [13,7].
* floor = "next ⟨e,h⟩-semigroup value above h(μ−j)" — [7,4]/[5,3] ≠ [13,7].
  ONLY `e·h·(μ−j)+1` matches, uniquely, every h≥2 case.
* count `p^(Ne−w)` per slot — undercounts by exactly p per slot for h≥2 (the gap); use the
  per-digit product (W6a). Same refutation invariant under p → q^f.
* maximal ideal `span{θ}` — it is `span{θ, p}` for h≥2 (p ∉ (θ) when e<h) [W6a].

--------------------------------------------------------------------------------
## §3 The two-step descent (f≥2) — ARCHITECTURE, gate-verified

f≥2 reduces cleanly to `q → q^f` + the f=1 restart, via the paper's TWO-STEP descent
(RESTART_LEMMA §8), NOT the one-step lift:
1. **f-descent** to O'' (unramified degree f): the block factors as G = ∏_{i<f} G_i with
   G_{i+1} = Frob(G_i) (conjugate blocks), the tuple determined by G_1; G ↦ G_1 is a
   measure/count-preserving bijection up to the constant q-power (Weil restriction; cross-conjugate
   resultant valuation = the w-table lattice exponent). Gate: exact on the (y²+y+1)² p=2 f=2 μ=2
   cell + p=3 quadratic² + samples, 0 mismatches.
2. **e-descent** (now f=1, over O''): the general-h restart of §1 with residue field F_{q^f}.
   This is monogenic (Eisenstein), unlike the one-step f≥2 lift.
**MANDATORY:** the Lean W6b wave must implement the two-step split. The one-step f≥2 side lift is
NON-monogenic (index p² at (e,h,f)=(2,1,2), p^12 at (2,1,4) — RESTART_LEMMA §7 / Gate B) and must
never be used. The child census over F_{q^f} is a universal necklace polynomial evaluated at q^f
(the SAME polynomial at every prime power — 0-mismatch vs brute at Q ∈ {2,3,4,5,7,8,9}).

--------------------------------------------------------------------------------
## §4 Deeper orders — the tower recursion (gate-verified structure)

**Order-2 = "restart, then restart AGAIN over the child ring", the child ring being the
general-(e,h) W6a ring (GAPPED when h≥2)** — not the plain e=1 `RphiRing` (that is only the
ungapped Z/p^N special case, the banked `SelfLoopTower` base). For an order-1 cell of slope −h₁/e₁,
residual (y−c̃)^μ:
1. develop the cluster block f = φ₁^μ + Σ b_j φ₁^j over R₁ = base[X]/(X^{e₁} − c̃·p^{h₁});
   avatars β_j = b_j mod φ₁ ∈ R₁.
2. FRESH PATTERN over R₁: `β_j ∈ F_{e₁·h₁·(μ−j)+1}` (vL₁-filtration ideal of the gapped R₁), per
   §1 — VERIFIED (gapped case: min vL β_0 = 13 = 2·3·2+1, β_1 = 7 = 2·3·1+1).
3. per-slot count = the W6a per-digit product over R₁.
4. ORDER-2 READ: classify B(Y) = Y^μ + Σ β_j Y^j over R₁ by its vL₁-Newton polygon; order-2 side
   slope −h₂/e₂, residual over F_p, decided (mult-1) leaves + undecided (mult≥2) order-3 children.
5. **v_r COMPOUNDING (RESTART_LEMMA §10 made exact):** `v_p(φ_r(root)) = h_r / (e₁·e₂···e_r)`;
   verified on all 2556 decided boxes across four cases (PARI oracle, 0 contradictions).

**Lean W6c shape:** INDUCTION on order r; step = a single-order restart over a TOWER of gapped
child rings. childRing_r := RphiRingGenH(e_r, h_r, c_r) built OVER the order-(r−1) child ring
(a tower of finite local rings; residue = the GaloisField tower). freshClusterPattern_r reuses §1
with vL_r; the h_r=1 case must definitionally collapse to the banked `RestartEquiv.FreshClusterPattern`
(via W6a's `vL_eq_vphi_of_h_one`). The banked `SelfLoopTower.two_level_census` is the (e=1,h=1)
base case of this induction.

--------------------------------------------------------------------------------
## §5 Open points (honest — named, not assumed)

1. **C(e,h) is not 0/1 for h≥2** (it is negative for larger h: (2,5)→−1, (3,4)→−2, (7,9)→−23).
   So a Lean census lemma must NOT use a naive closed form — use the per-digit product count
   directly (robust to clamping). The closed form is valid only in the readable regime N ≥ hμ+1.
2. **Top-slot clamping:** for high h, per-coordinate floors h(μ−j)+c_i can go negative (c_i<0,
   i≥1) and clamp to 0, or exceed N. The per-digit product absorbs this; a Lean proof must handle
   the clamp explicitly, not the unclamped algebra. This is exactly W6a's named residual (the
   ⟨e,h⟩-graded strictness; e=2 tractable, e≥3 harder).
3. **The gap COMPOUNDS through orders — ✅ RESOLVED 2026-07-06 (W6c precondition gate).** The
   doubly-gapped tower (h₁≥2 AND h₂≥2, R₂ built as `R₁[t₂]/(t₂^{e₂} − c₂·Π^{h₂})` OVER an
   already-gapped R₁) was explicitly constructed and brute-verified: **COMPOUNDS CLEANLY, zero
   gap-interaction** (cases (2,3)/(2,3) at N=4 and N=5, plus (2,1)/(2,3), (2,3)/(2,1), and an
   adversarial "restart over the gap generator θ₁" — all 0-mismatch, dodging the box blowup via
   construct-then-verify). The compounded count is
   `card(filtIdeal₂ W) = ∏_{i<e₁,j<e₂} p^(N − ⌈(W − e₂h₁i − e₁h₂j)/(e₁e₂)⌉⁺)`, EQUAL to the
   "restart over R₁" form `∏_{j<e₂} card_{R₁}(filtIdeal₁ ⌈(W − e₁h₂j)/e₂⌉⁺)` (per-slot the lower
   ring's own W6a count). Load-bearing structural fact: the two tower generators occupy DISTINCT
   power-basis monomials, so they stay independent in each graded piece F_m/F_{m+1} — no
   cross-level cancellation, hence no new cancellation lemma needed for W6c. v_r compounding
   `v_p(φ_r(root)) = h_r/(e₁···e_r)` re-verified (PARI, incl. p=3). Level-2 fresh floor is
   `e₂·h₂·(μ₂−j)+1` in vL₂ units (§1 form at level 2). Emptiness compounds (N budget e₁e₂N must
   fit the level-2 top floor). **W6c Lean wave is UNBLOCKED — PROCEED** with the per-digit product
   count (never p^(E·N−w)); the only proof obligation per level is the already-W6a-shaped per-slot
   strictness. Artifacts /workspace-vast/asving/tmp/phaseb_w6c_gate/.
4. μ=3 h≥2 verified by SAMPLING (4000 surjectivity + 37k membership draws, 0 violations, floor
   attained), not exhaustively — exhaustive scan infeasible (prefilter > 1e8). The pattern is
   robust but the μ≥3 exhaustive check is a residual gate if one wants belt-and-suspenders.

--------------------------------------------------------------------------------
## §6 Lean wave plan (revised from the exploration; each gate-first)

Ordering unchanged (W6a-residual → W6b → W6c) but each shape now pinned by verified math:

* **W6a-residual** (the immediate next Lean wave — completes W6a): prove the reverse anchors
  `vL θ = h`, `vL p = e` (W6a banked only ≤) and the per-digit product count
  `card(filtIdeal w) = p^(Σ_i (N − min(N, ⌈(w−ih)/e⌉⁺)))` for the gapped ring — the ⟨e,h⟩-graded
  strictness. e=2 first (tractable), e≥3 named. This unblocks the general-h fiber card. GATE:
  gate_w6a.py / phaseb_w6h numbers.
* **W6b-h** (general-h single-block restart in Lean): `RestartEquivGenH` = `RestartEquiv` with the
  floor `e·h·(μ−j)+1` over `RphiRingGenH`'s filtIdeal + the per-digit count. Keep the RestartEquiv
  STATEMENT SHAPE verbatim (residue-free torsor); only the floor + count change. Carry `hμ < N`.
  GATE: phaseb_w6h fiber cards (0-mismatch).
* **W6b-f** (f≥2, the two-step descent): tower ring over `GaloisField p (kf)` = W6a with p→q^f
  (mechanical reindex); the Weil-restriction conjugate-block bijection; child census = necklace
  poly at q^f. Two-step split MANDATORY (never one-step). GATE: phaseb_w6f (0-mismatch, incl. wild
  gapped ⟨2,3⟩).
* **W6c** (deeper orders): the order-r induction of §4 over the gapped tower; base =
  `SelfLoopTower`. PRECONDITION: the §5.3 two-level-gapped numeric gate. Touches the classifier
  recursion (v_r reader) — enumerated-consumers discipline (the childCtxOfSize precedent).

Artifacts (all under /workspace-vast/asving/tmp/): phaseb_w6h/ (general-h), phaseb_w6f/ (f≥2),
phaseb_w6d/ (deeper-order), phaseb_w6a/ (the W6a gapped filtration gate). Each has scripts +
result tables + SUMMARY.md.

--------------------------------------------------------------------------------
## §7 The order-r≥3 tower closure — the `TowerBase` coefficient-ring abstraction (design)

2026-07-06. W6c-2 proved the order-2 general-(e,h) census; the ONLY remaining piece for the full
order-r tower recursion (hence the count-native restart at ALL orders) is a coefficient-ring
generalization. The math is DONE (W6c gate: the doubly-gapped tower compounds cleanly, distinct
power-basis monomials ⟹ no cross-level cancellation, no new cancellation lemma). This section is
the LEAN DESIGN, so the wave is math-and-blueprint-first, not exploratory.

**The problem.** `RphiRingGenH` is `AdjoinRoot (X^e − c·p^h)` over the CONCRETE base `ZMod (p^N)`,
and `RphiGenHCount.card_filtIdeal` counts via the base's ball-count `#{a : ZMod(p^N) | v_p(a) ≥ k}
= p^(N − min(N,k))`. For order r the child ring must be built over `R_{r−1}` (itself a gapped
tower ring), not `ZMod(p^N)`. So the count layer must be parameterized by the base's OWN
ball-count (which is recursive: R_{r−1}'s per-digit product).

**The abstraction (`TowerBase`).** A structure/typeclass on a finite commutative local ring `R`
bundling exactly what the construction + count need (NOT the full W(F)-tower — only the interface):
```
class TowerBase (R : Type*) [CommRing R] [Finite R] where
  ϖ        : R                    -- the base "uniformizer analogue" (p at level 0; π_{r−1} above)
  Q        : ℕ                    -- residue field size (p^k at level 0; q^{f·…} above)
  isLocal  : IsLocalRing R
  vB       : R → ℕ                -- the base valuation (v_p at level 0; vL_{r−1} above)
  ballCount : ℕ → ℕ               -- #{a : R | vB a ≥ k}  (p^(N−min N k) at level 0; the gapped
                                  --  per-digit product of R_{r−1} above) — the RECURSIVE input
  ball_count_spec : ∀ k, Nat.card {a : R // vB a ≥ k} = ballCount k
  -- + the minimal axioms card_filtIdeal's proof actually used (grep RphiGenHCount for the base
  --   facts: ZMod.card, the p^k-ideal card, digitEquiv's per-coordinate independence — abstract
  --   each to a TowerBase field/hypothesis; the filtIdeal_eq_phiIdeal θ-closure argument was
  --   base-agnostic already, so it ports).
```
Then:
1. `RphiGenH R [TowerBase R] (e h : ℕ) (c : Rˣ) := AdjoinRoot (X^e − C c · C (ϖ)^h)` over `R` —
   the general-base child ring. `card`, `digitEquiv`, `vL`, `filtIdeal` port from RphiRingGenH
   with `ZMod(p^N)` → `R`, `p` → `ϖ`, the per-coordinate count `p^(N−…)` → `R.ballCount`.
2. `card_filtIdeal_gen : card (filtIdeal w) = ∏_{i<e} R.ballCount (⌈(w − i·h)/e⌉⁺)` — the per-digit
   product with the base's own ball-count per coordinate (the concrete RphiGenHCount is this at
   `R = ZMod(p^N)`, `ballCount k = p^(N−min N k)`).
3. `instTowerBase_ZMod : TowerBase (ZMod (p^N))` (level-0 instance; `ballCount = p^(N−min N ·)`),
   proving `card_filtIdeal_gen` reduces to the banked `RphiGenHCount.card_filtIdeal`.
4. `instTowerBase_RphiGenH : TowerBase R → TowerBase (RphiGenH R e h c)` (the INDUCTIVE step: a
   tower ring is itself a TowerBase, with `vB := vL`, `ballCount := card_filtIdeal_gen`, `Q :=
   R.Q` unchanged f=1 / `Q^f` for the f-descent). THIS is the recursion that closes order-r: the
   tower is `Nat`-iterated `RphiGenH` starting from `ZMod(p^N)`, each level a TowerBase over the
   last. The W6c-gate's "compounds cleanly" is exactly `ball_count_spec` for the composed ring =
   the product of the per-level ball-counts (distinct-monomial independence ⟹ the composite ball
   is the product ball).
5. `restartEquivGenH` / `card_restartGenH_fiber` re-stated over `[TowerBase R]` (abstract base) —
   the h=1-shape proof is base-agnostic (grep RestartEquivGenH for `ZMod`-specific steps; the
   dictionary/cap-φ^μ argument uses only ring + the base ball-count). Then order-r restart =
   `restartEquivGenH` over the level-(r−1) tower base, and `two_level_census_genH` generalizes to
   `r_level_census` by `Nat`-recursion on tower height.

**Wave scope (partial banking expected):** (a) the `TowerBase` class + `instTowerBase_ZMod` +
`card_filtIdeal_gen` reducing to the concrete count = the tractable core; (b)
`instTowerBase_RphiGenH` (the inductive step) = the load-bearing generalization; (c) the abstract
`restartEquivGenH`/`r_level_census` = the closure. Bank (a); (b) is the crux; (c) may be named if
(b) is heavy. GATE: the concrete instance must reproduce EVERY banked W6a/W6b-h/W6c-2 number
(0-mismatch) — the abstraction is sound iff `R = ZMod(p^N)` recovers the banked results verbatim.
Owns NEW modules (TowerBase.lean + generalized layers); the concrete RphiRingGenH/RphiGenHCount/
RestartEquivGenH stay FROZEN (the abstract versions are additive, with the concrete = the level-0
instance). No new numeric gate needed (W6c gate already verified the compounding); the obligation
is purely the Lean abstraction + the reduction-to-concrete checks.
