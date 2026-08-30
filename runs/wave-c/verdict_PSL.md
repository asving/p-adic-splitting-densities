# UNIT PSL — VERDICT: THE POWER SECTOR'S SECOND-ORDER MONTES INSTRUMENTS LANDED, ALL PURE LEAN CORE — the canonical power data with the STRICT MASS DROP, the IRREDUCIBLE recentring key at EVERY face, the RAMIFIED (Eisenstein) complete-DVR cascade previously absent from the corpus, THE COORDINATE LATTICE (C27x's documented hole at h = 1), the dev-transform bijection with TWO-WAY level exactness, and the dd (2,2) instance stack (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG39.lean` (1351 lines, ZERO sorries,
zero warnings, zero errors; 22 AxCheck footer lines — **ALL pure Lean core
`{propext, Classical.choice, Quot.sound}`**, including §1's power data: the expected
B.42 inheritance through the `classResidualPoly` chain did NOT materialize (the
consumed RECUR/SSL slice is itself core); the C.33 cites do not occur).  One-line
aggregator import added to `Uniformity/ChapI.lean` between IFCG38 and IFCG40
(another unit's IFCG41 line observed appearing concurrently, untouched; the
orchestrator temporarily unwired my line mid-repair to unblock another unit's
aggregator check — RE-ADDED at finish per its note).  No git ops.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG39.lean`
(final: zero diagnostics beyond the 22 expected axiom prints), targeted
`lake build Uniformity.ChapI.IFCG39` GREEN (8955 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the line re-wired.

**Unit history:** the predecessor hung mid-proof; on takeover the inherited skeleton
verified with §2 (the xKey apparatus INCLUDING `xKey_irreducible`) already green —
the predecessor's capstone had landed.  This session closed §1, §3, §4, §5, §6.

## ★★★ THE HEADLINE (all Lean-core, all uniform in `q, m, σ, h, e', d, k`, every complete DVR)

    theorem powerSector_data      : power-sector class ⟹ unique face (h,e'), e' ≥ 2,
      MONIC irreducible ψ, ψ(0) ≠ 0, classResidualPoly = ψ^k EXACTLY, 2 ≤ k,
      1 ≤ deg ψ, e'·(k·deg ψ) ≤ m
    theorem powerSector_mass_drop : 2k ≤ m ∧ k < m          -- THE STRICT DESCENT
    theorem xKey_irreducible      : the slope-h/e' homogenization of any monic lift
      of ψ is IRREDUCIBLE                                    -- every (h, e', d)
    theorem eis_isDVR / eis_isAdicComplete / eis_finite_residueField /
      eis_residueCard / eis_map_pow_maximalIdeal :
      O' := AdjoinRoot (X^{e'} + cπ) is a COMPLETE DVR, maximalIdeal = (α),
      residueCard O' = residueCard O, 𝔪^K·O' = 𝔪'^{e'K}      -- THE RAMIFIED CASCADE
    theorem eis_root_pow_dvd_mk_iff :                        -- THE COORDINATE LATTICE
      α^w ∣ mk P  ↔  ∀ i < e', π^{(w+e'−1−i)/e'} ∣ P.coeff i   (deg P < e')
    theorems devT_monic/reassT_monic/devT_reassT/reassT_devT : the φ-adic
      dev-transform is a degree-graded bijection {monic deg D·k /O} ≃ {monic deg k /O'}
    theorems devT_sub_root_pow_dvd / reassT_sub_pi_pow_dvd : LEVEL EXACTNESS both
      ways — π^N-congruence over O ⟷ α^{e'N}-congruence over O' (fScale = e')
    theorem dd_recentring_stack : ER4's key X² − bπ (= eisKey π (−b) 2, pinned by
      eisKey_dd) generates a complete DVR, q UNCHANGED — the (2,2) instance point

## What each section delivers

* **§1** `powerSector_data` + `powerSector_mass_drop`.  `classResidualPoly_monic`
  is IMPORTED from IFCG38 (the landed SSL unit; byte-identical statement — the
  inherited sorry was deleted, not re-proved).  Private `resPoly_rep` (IFCG38's
  idiom replicated) + `classResidualPoly_natDegree_bound` (sideMax = m caps the
  face: `e'·deg ≤ m`).  Monic normalization via `eq_of_monic_of_associated`;
  `e' ≥ 2` is free from MinFaceAt's `1 ≤ h < e'`.
* **§2** (predecessor, found green): `xKey` = Σ ψt_i·π^{h(d−i)}·X^{e'i}; coeff
  lattice, monic of degree e'd, PURE of slope h/e', xres = ψ̄, IRREDUCIBLE via
  IFCG37's Step I.  (ChapC records composed-key irreducibility as generically
  absent; at the census x-frame it is a theorem.)
* **§3** the Eisenstein ring: `eisKey_irreducible` (via xKey at (h,d) = (1,1));
  `eisRes` (reduction-at-the-root O' →+* k, kernel EXACTLY (α) — first-iso route);
  locality via lying-over (module-finite ⟹ integral; every maximal contracts to 𝔪,
  hence contains α^{e'} = −cπ, hence α; Quarry's `of_unique_max_ideal` skeleton);
  DVR via `(IsDiscreteValuationRing.TFAE …).out 4 0` on the principal (α);
  completeness via the NEW generic `isAdicComplete_of_pow_eq` (cofinality transfer
  J^k = I) + IFCG27's `isPrecomplete_of_basis` + `IsAdicComplete.map_algebraMap_iff`;
  THE LATTICE by explicit monomial folds (`eis_mk_X_pow`: mk(X^n) =
  mk(C((−cπ)^{n/e'}))·α^{n%e'}) — forward: fold X^w·Q to the canonical rep R and
  read coefficients; backward: monomial-by-monomial with π = (−u⁻¹)α^{e'}.
* **§4** `devT`/`reassT` against B02–B13a's dev API (`sum_dev_eq`, `dev_unique`,
  `degree_dev_lt`, `dev_top`) + mathlib's `modByMonicHom_mk`/`mk_leftInverse`.
  The skeleton's `dev_sub_mem` (general-Ideal congruence) was DROPPED: B10's
  `dev_congr` is verbatim the needed π-power instrument (no consumer for the
  general form — the no-dead-Prop discipline).
* **§5** level exactness both directions (`dev_congr` + the lattice at w = e'N,
  where the ceiling collapses to N at every slot).
* **§6** the dd (2,2) test: `eisKey_dd` (anti-drift pin X² − bπ = eisKey π (−b) 2)
  + `dd_recentring_stack` (exists-instance shape; CN5 haveI telescope).

## THE EXACT SURVIVING OPEN SET toward `PowerSectorLaw m σ` (the honest fence)

No named Prop was declared (a hasty law-equivalent Prop with no in-file consumer
would violate the corpus' no-dead-Prop rule).  The law is the composite of four
legs, all now stated against LANDED apparatus:

1. **The residual-box transfer criterion** — C110's translate-residual criterion at
   `e' ≥ 2`: a pure slope-h/e' block has class residual `ψ^k` ⟺ its dev-transform
   lies in the deep recentred box over O' (the binomial-triangular digit
   computation; the lattice + `devT` are its ready coordinates; predecessor's
   design note: verified on paper, `R(Y−c̄) = Y^k ⟺ k lower digit combinations
   vanish`).
2. **The face-indexed cell decomposition + count identity** — `powerSectorCount` =
   Σ over faces of recentred cell counts over O', level-exact via §5 (level
   `M + m` over O ↦ level `e'(M+m)` over O'; the box side over O' is `𝔪'`-adic at
   the SAME q by `eis_residueCard`).  The `eScale (e,f) ↦ (e'e, f)` type-descent
   Prop rides with this leg.
3. **The ZcURLim closure** — the recentred families consume the strictly-smaller-
   mass laws (mass k ≤ m/2 by `powerSector_mass_drop`) INSTANTIATED AT O': legal
   exactly because §3 lands the complete-DVR instance stack with residueCard
   unchanged — the ∀-DVR uniformity of the law families pays here.  ER4's
   `ZcURLim (e1DdDecFam σ)` is the (2,2) instance of this leg, sitting on
   `dd_recentring_stack`.
4. **The general-face (d ≥ 2) compositum** — the unramified step (landed
   IFCG27/29 cascade at the residual key) composed with THIS file's Eisenstein
   step: the two-step tower under `xKey` (whose irreducibility at every (h,e',d)
   is already landed here).

## Repair log (7 error rounds over 9 compile passes; every statement landed as designed except the two noted reshapes)

1. `Polynomial.irreducible_X_add_C` absent at pin → `irreducible_X_sub_C` via
   `map_neg, sub_neg_eq_add`; `ring` cannot see through the `C` ring hom.
2. `Monic` dot-notation after `set` unfolds to `Eq` (`hψm.natDegree_eq_zero_iff…`
   resolves against `Eq`) → explicit `Polynomial.Monic.natDegree_eq_zero`.
3. `IsAdicComplete.mk`'s parents are INSTANCE fields — `⟨⟨…⟩,⟨…⟩⟩` fails; `haveI`
   both parents then `exact IsAdicComplete.mk`.
4. `Ideal.neg_mem` absent → root `neg_mem`.
5. Two inline `(by omega)` proof terms of the same Prop inside ONE term-mode def
   consumed by `.trans`-unification → "no goals to be solved"; hoist to a single
   named `have` (NOTE FOR SUCCESSORS — the flakiest error message of the unit).
6. DEPENDENT REWRITE: rewriting `c` under `(isUnit_of_residue_ne_zero hc).unit`
   (whose type mentions `c` through `hc`) — motive not type correct; generalize
   the unit to opaque binders `(u : Oˣ) (hu : ↑u = c)` + `subst`.
7. `map_pow` first-matches the ring hom `Polynomial.C` applied to a power
   (`C((−cπ)^t)`), starving the intended `mk (X^m)` — pin `map_pow` with explicit
   `(f) (a) (n)` arguments.  Also: `natDegree_X_pow` needs `Nontrivial
   (AdjoinRoot φ)` — route degree bounds through `natDegree_monomial_le` instead.
   Statement reshape (§6 only): the packaged instance stack needs its `IsDomain`/
   `IsLocalRing` as leading `∃`-witnesses (statement-time synthesis).

Traps avoided by design: every variable·variable product kept out of omega via
`generalize e' * N = A` or an atom-pinning `have` (the `Nat.div_add_mod` +
`Nat.mul_add_div` idiom for all ceiling arithmetic); `sideMin/sideMax` unfolded
before Finset lemmas (RECUR log 3); the Classical `sideSet` filter entered only
through the B83Kit `mem_sideSet_iff'` private copy; `mk∘C`-normal form kept
throughout the lattice (never the `↑`-coercion of `mk_C`, dodging CoeTC-vs-
algebraMap syntactic drift; `mk (C z) = algebraMap z` consumed as `rfl`).

## File map (`leanfinal/Uniformity/ChapI/IFCG39.lean`, 1351 lines)

§0 kit (`isKey_X`, `mem_sideSet_iff'` privates; `degree_modByMonicHom_lt`,
★ `isAdicComplete_of_pow_eq` — both generic, reusable) · §1 `resPoly_rep`,
`classResidualPoly_natDegree_bound` (privates), ★ `powerSector_data`,
★ `powerSector_mass_drop` · §2 `xKey`, `xKey_coeff/_mul/_off`, `xKey_monic`,
`xKey_isPure`, `xKey_sideData`, `xKey_xres`, ★★ `xKey_irreducible` · §3 `eisKey`,
`eisKey_monic/natDegree/eq_xKey`, ★ `eisKey_irreducible`, `eis_root_pow`,
`eisRes` + `eis_ker_eisRes` + `eis_span_root_isMaximal` (privates),
★ `eis_root_pow_dvd_mk_iff` (+ `eisKey_degree`, `eis_eq_zero_of_mk_eq_zero`,
`eis_mk_X_pow`, `eis_algebraMap_pi` privates), ★★ the cascade `eis_isDomain /
eis_isLocalRing / eis_maximalIdeal_eq / eis_isDVR / eis_map_pow_maximalIdeal /
eis_isAdicComplete / eis_finite_residueField / eis_residueCard`
(+ `eisResidueEquiv`, `eis_root_ne_zero` privates) · §4 `devT`, `reassT`,
`devT_coeff`, `devT_monic`, ★ `devT_reassT`, ★ `reassT_devT`, `reassT_monic`
(+ `adjoinRoot_one_ne_zero`, `devT_natDegree_le` privates) ·
§5 ★ `devT_sub_root_pow_dvd`, ★ `reassT_sub_pi_pow_dvd` · §6 `eisKey_dd`,
★ `dd_recentring_stack` · AxCheck footer (22 lines).
Imports beyond the predecessor's baseline: `ChapI.IFCG38` (classResidualPoly_monic);
opens added: IFCG38, IFCG26 (`onSide_monicPoly_of_npAttains`), IFCG27
(`isPrecomplete_of_basis`).
