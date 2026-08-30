# UNIT PSL3 — VERDICT: ALL FOUR NAMED LEGS LANDED AS THEOREMS, ALL PURE LEAN CORE — the compositum stack, the cell/count transport equivalence, the ZcURLim closure consumption, and THE HEART: C110's translate-residual criterion at e' ≥ 2, BOTH DIRECTIONS, digit form + sector-facing resPoly form (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG43.lean` (1208 lines, ZERO sorries,
zero errors, zero warnings; **all 15 AxCheck footer lines pure Lean core
`{propext, Classical.choice, Quot.sound}`** — the B.42/C.33 cites do not occur
anywhere in the file's footprint).  One-line aggregator import added to
`Uniformity/ChapI.lean` after IFCG41 (IFCG42's line left to its own unit — the file
does not yet exist; IFCG42.lean untouched per the fence).  No git ops.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG43.lean`
(9 increments, each GREEN before the next); final: targeted
`lake build Uniformity.ChapI.IFCG43` GREEN (8956 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the line wired.

## ★★★ THE HEADLINE — the four legs, in the landed order (4 → 2 → 3 → 1)

    LEG 4  compositum_recentring_stack : IsKey φ, π irr, c₁ residually ≠ 0, e' ≥ 2 ⟹
      O₂ := AdjoinRoot (eisKey (algebraMap π) c₁ e') over O₁ := AdjoinRoot φ is a
      COMPLETE DVR (∃-instance package), residueCard O₂ = q ^ deg φ, and FULL-TOWER
      ramification (𝔪^K).map(O→O₂ composite hom) = 𝔪₂^{e'·K} — the general-face
      (h, e', d) recentring ring, every complete DVR, every key, every centre.
    LEG 2  cellTransport : Coeff O (e'·k) N ≃ Coeff O' k (e'·N) — IFCG39's
      dev-transform bijection DESCENDS to the finite coefficient boxes, level
      scaling EXACTLY fScale = e'; computed on lifts (cellTransport_apply /
      _symm_apply via devVec/reassVec); count transport
      Nat.card (T '' S) = Nat.card S; box pin card_coeff_eis :
      Nat.card (Coeff O' k (e'N)) = q^(k·e'·N) at the SAME q.
    LEG 3  eis_recentring_stack : the ∃-instance package at EVERY (c, e'), c
      residually ≠ 0, e' ≥ 2 (generalizes IFCG39 §6's dd (2,2) point) +
      zcURLim_eis_value : ZcURLim F ⟹ ONE pair (n, d) serving simultaneously the
      base clause at every O AND the recentred clause — at every π, c, e' and every
      uniformizer π' of O', Tendsto (F O' π') atTop (nhds (n(q)/d(q))) with q the
      BASE residue cardinality (q' = q pays here; recentred limits stay in the
      same rational family).
    LEG 1  eis_transfer_digits_iff  (★★★ THE MATHEMATICAL HEART, both directions):
      G monic, natDegree = e'·k, raw-pure of slope 1/e'
      (π^{⌈(e'k−j)/e'⌉} ∣ G_j), z residually ≠ 0 ⟹
        [∀ t < k: α^{e'(k−t)+1} ∣ mk (dev (eisKey π (−z) e') G t)]   (DEEP BOX)
          ⟺ [∀ t < k: digAt π (k−t) (G_{e't}) = C(k,t)·(−z̄)^{k−t}]  (DIGITS)
      xres_eq_pow_iff_digits : under side pins (sideMin = 0, sideDeg = k, H₀ = k),
        xres = (X − C z̄)^k ⟺ the digit equations
      resPoly_eq_pow_iff_box (sector-facing composite) :
        resPoly π X G 1 e' hne k = (X − C (resFieldXEquiv z̄))^k ⟺ THE DEEP BOX
      — C110's translate-residual criterion at the recentred frame e' ≥ 2,
      x-frame (h, d) = (1, 1) sub-sector, uniform in q, e', k, z, every DVR.

## The mechanism of LEG 1 (the digit computation, no induction needed)

The predecessor's design note ("R(Y−c̄) = Y^k ⟺ k lower digit combinations vanish")
formalizes as a DIRECT two-way digit computation — the imagined downward induction
dissolves because the digit hypotheses arrive at all t simultaneously:
* the recentred key IS the constant shift `eisKey π (−z) e' = X^{e'} − C(zπ)`
  (`eisKey_neg`), so C110's binomial `shiftDev` rearrangement applies VERBATIM
  (replicated private stack `dev_sub_C` etc.), in BOTH directions
  (`dev_eisKey_eq` / `dev_X_pow_eq` — shift by `zπ` and by `−zπ`);
* the `X^{e'}`-adic development reads coefficient BLOCKS (`dev_X_pow_blk/_coeff`,
  via `dev_unique` against an explicit block sum — the `m = e'·t + i` regrouping);
* deep-box exponents through IFCG39's lattice: slot 0 reads `k−t+1`, slots
  `1 ≤ i < e'` read `k−t` (`lat_exp_zero/_pos`); purity supplies exactly `k−s` at
  every block slot (`pure_exp_eq/pure_dvd`);
* digits → box: slots `i ≥ 1` are paid by purity alone termwise; slot 0 needs the
  `+1`: the term digits sum to
  `Σ_s z̄^{s−t}·C(s,t)·C(k,s)·(−z̄)^{k−s} = C(k,t)·(z̄−z̄)^{k−t} = 0`
  (`binom_vanish`: `Nat.choose_mul` trinomial revision + `add_pow`), and
  `digAt_eq_zero_iff` converts the vanishing digit into the extra `π`;
* box → digits: the inverse shift expands `G_{e't}` as the top term
  `(−zπ)^{k−t}·C(k,t)` (whose digit is the target, `dev_top` pins the top digit 1)
  plus `π^{k−t+1}`-deep terms that fall out of the digit.

## What each section holds (file map)

§0 kit: `res_mk_eq_iff` (level-N class equality = ϖ^N-divisibility; serves BOTH O
and O' through `mem_pow_maximalIdeal_iff`), `monicPoly_coeff_lt/_coeff_self`
(C109a/C53b idioms, private copies), `pow_dvd_monicPoly_sub_coeff` ·
§1 ★ `compositum_recentring_stack` (IFCG29's `irreducible_algebraMap_adjoinRoot`
supplies uniformizer persistence; the two landed cascades compose by haveI
telescope; the tower clause via `Ideal.map_map`/`map_pow`) ·
§2 ★ `eis_root_irreducible` (α is a uniformizer of O'), `devVec`/`reassVec`,
`devVec_congr`/`reassVec_congr` (well-definedness = IFCG39's two-way level
exactness), `reassVec_devVec`/`devVec_reassVec` (exact round trips on canonical
lifts), ★★ `cellTransport`, ★ `cellTransport_apply/_symm_apply`,
★ `cellTransport_card_image`, ★ `card_coeff_eis` ·
§3 ★ `eis_recentring_stack`, ★★ `zcURLim_eis_value` ·
§4 `eisKey_neg` + the C110 shift stack (private) + the block reads (private) +
digit kit (`digAt_sum`, exponent lemmas, ★ `binom_vanish`) + `box_of_digits` /
`digits_of_box` (private directions) + ★★★ `eis_transfer_digits_iff`,
★★ `xres_eq_pow_iff_digits`, ★★★ `resPoly_eq_pow_iff_box` · AxCheck (15 lines).

## THE EXACT SURVIVING REMAINDER toward `PowerSectorLaw m σ` (the honest fence)

`PowerSectorLaw m σ` did NOT fire — the charge's conditional ("if the chain
closes") is NOT met.  The remainder, now all stated against landed apparatus:

1. **The face-indexed assembly** (bookkeeping, no new mathematics): partition
   `powerSector` by its unique minimal face `(h, e')` and residual centre;
   transport `classResidualPoly` to a lift's `resPoly` (IFCG39 §1's `resPoly_rep`
   idiom, private there — replicate); extract the side pins (`sideMin = 0`,
   `sideDeg = k`, `H₀ = k`) and the raw purity from `IsPure`/`MinFaceAt`
   (ℕ∞ bookkeeping mirroring IFCG39's `xKey_sideData`); then each face's cell set
   IS the deep recentred box via `resPoly_eq_pow_iff_box`, carried to `O'`-cells
   by `cellTransport` with its count transport.
2. **The general-`(h, d)` criterion** (the only remaining mathematics): LEG 1 is
   proved at the Eisenstein frame `(h, d) = (1, 1)`.  `h > 1` needs the key
   `X^{e'} + C(c·π^h)` (the `d = 1` xKey) and `d ≥ 2` the composed key over
   LEG 4's compositum ring: the RINGS are landed (`compositum_recentring_stack`),
   their coordinate lattices (the analogue of `eis_root_pow_dvd_mk_iff`) are not.
   The digit mechanism (binomial shift + vanishing) is frame-independent and
   should replay verbatim once those lattices land.
3. **The recentred-mass induction wiring**: consume the strictly-smaller-mass laws
   (mass `k ≤ m/2` by IFCG39's `powerSector_mass_drop`) at `O'` through
   `zcURLim_eis_value` + the count transport at level `e'·(M+m)` (a Tendsto
   reindexing), and sum the finitely many face/centre contributions into one
   `ZcURLim` family (`ZcURLim_sum`).

**Census position (exact):** with PSL3, the power sector's remainder is 1–3 above;
combined with the standing wrappers (`coneRemainderLaw_of_sectorLaws` at IFCG35,
IFCG40's `splitSectorLaw_of_mass_le_three` + the SSL equivalence), the cone census
still rests on {`PowerSectorLaw` (via 1–3), `LeafSectorLaw`'s cell count, the split
census laws (CSL's unit, IFCG42 — untouched), the mass-4 dd/E2 recursions}.  Any
claim that the power sector is CLOSED is false; what is closed is its second-order
instrument layer: every leg the PSL fence named now exists as a Lean-core theorem
at the stated frame.

## Repair log (5 error rounds over 9 compile passes; every statement landed as designed)

1. `omit [IsDomain R]` on the monicPoly kit — `monicPoly` itself requires
   `IsDomain` (LocalData section variable); omit only the DVR instance.
2. `subst h` with `h : m = n` eliminates the RIGHT variable — twice (kit's
   `monicPoly_coeff_self`, LEG 1's `s = k` branch); successors: prefer `rw [h]`
   or a pinned `have` over subst when the eliminated side is referenced later.
3. `Polynomial.monic_X_pow` wants its exponent explicit at binder-less use sites.
4. `eisKey_monic he''` under a bare `have h := degree_dev_lt …` leaves `π, c` as
   unsolved metavariables (⊢ O twice) — pin `(π := π) (c := -z)` when no expected
   type constrains them.
5. THE DEPENDENT-REWRITE TRAP at the resPoly wrapper: rewriting
   `Polynomial.map_X` inside `(X − C w)^k` over `resField X = AdjoinRoot X` —
   motive not type correct (the type index mentions `X`); route through
   `simp only [map_pow, map_sub, map_X, map_C, RingEquiv.coe_toRingHom]`
   (simp's congruence machinery handles the instance dependency).

Traps avoided by design: every `e'·s`-type product kept out of omega via
`generalize`/atom pins (IFCG39 log discipline); `Nat.div_eq_of_lt_le` fed bounds
in its native `k*n ≤ m < (k+1)*n` orientation via ℕ-`ring` calc steps; the
`Nat.div_add_mod` pin for all block-index arithmetic; `binom_vanish` stated in the
EXACT associativity its consumer's digit sum produces (no post-hoc reassociation).

## Consumption notes for the successor units

* `cellTransport`'s instance arguments (`IsDomain/IsDVR O'` + both `Finite`) are
  supplied by `eis_recentring_stack`/IFCG39's cascade via haveI at the use site.
* `zcURLim_eis_value`'s recentred clause takes the four O'-instances as
  ∀-instance-binders: intro them, `haveI`, then apply at any uniformizer of O'
  (e.g. `AdjoinRoot.root _` via `eis_root_irreducible`).
* `resPoly_eq_pow_iff_box`'s side pins are hypotheses BY DESIGN (C110's pattern):
  the face-assembly unit derives them once from `IsPure` and reuses everywhere.
* The centre convention: the criterion is stated at `eisKey π (−z) e'`
  (`= X^{e'} − C(zπ)` by `eisKey_neg`), residual root `z̄` — mind the sign when
  wiring `powerSector_data`'s `ψ = X − z̄` (constant coefficient `−z̄ ≠ 0`).
