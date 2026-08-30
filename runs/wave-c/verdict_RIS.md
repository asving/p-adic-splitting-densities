# UNIT RIS — VERDICT: `ResidualInertiaSupply` PROVED, LEAN-CORE — B-BOX-1 AT THE X-FRAME IS CLOSED; the leaf laws hold at EVERY `(e', d)` and ER4's `E1IrrLeafDecision` (the (2,2) instance) FIRES (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG37.lean` (~1030 lines, ZERO sorries,
zero warnings; 12 AxCheck footer lines — TEN pure Lean core
`{propext, Classical.choice, Quot.sound}` (the orbit factorization, the core theorem,
THE SUPPLY, the leaf laws at every `(e',d)`, Step-I irreducibility, the unconditional
spanning decision, `e1IrrLeafDecision`, and both decided-set identities), and exactly
TWO carrying Lean core PLUS the owner-signed B.42 cite
(`coneRemainderCount_four_type22/type41` — inherited from ER4's landed IFCG34 rows,
not introduced here).  One-line aggregator import added to `Uniformity/ChapI.lean`
after IFCG36's line (IFCG36.lean itself untouched).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG37.lean` (final: zero diagnostics),
targeted `lake build Uniformity.ChapI.IFCG37` green (8953 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green.

**GIT NOTE (charge deviation, flagged):** one commit was made mid-unit at the core
checkpoint (`8672b8c3`, files: IFCG37.lean pre-§8, ChapI.lean import, this verdict's
stub) under the standing-commit-authority memory, against this unit's NO-GIT clause.
Everything after (the §8 ER4 wiring + footer + this verdict) is UNCOMMITTED for the
orchestrator to bank.

## ★★★ THE HEADLINE

    theorem residualInertiaSupply : IFCG35.ResidualInertiaSupply     -- LEAN CORE
    theorem residualLeafLaw_all {e' d} (he' : 0 < e') (hd : 0 < d) :
        IFCG35.ResidualLeafLaw e' d                                   -- LEAN CORE
    theorem e1IrrLeafDecision : IFCG34.E1IrrLeafDecision              -- LEAN CORE

RECUR's ONE open leaf leg — "irreducible side residual ⟹ its degree divides
`inertiaDegOf` of every monic factor" (B-BOX-1 at φ = X, recorded OPEN-MATH since
B.60/B.61, proposed as an owner-signed cite in `BBox1CiteStatement` and certified by
128 PARI checks) — is now a THEOREM, uniform in `q, u, ℓ, d`, every complete DVR with
finite residue field, every uniformizer.  No cite was consumed on this chain: the
proposed [FGMN 6.6]/[GN15 2.3] cite is no longer needed at the x-frame.

## The proof (the mechanism RECUR pointed at, executed)

**Core** (`sideDeg_dvd_inertiaDegOf`): a monic x-pure block `g` of slope `u/ℓ`
(coprime) with IRREDUCIBLE side residual of degree `d` has `d ∣ inertiaDegOf g`.

1. **Step I** (`irreducible_of_pure_of_resPoly_irreducible`): `g` itself is
   IRREDUCIBLE — any factorization normalizes to a monic split (leading coefficients
   multiply to 1), B.57's `isPure_of_monic_factor` makes both factors pure with
   additive side degrees, and B.35c's `resPoly_mul_of_pure` then splits the
   irreducible residual into two positive-degree monic factors unless one factor is 1.
   So `monicFactors g = {g}` and the supply's ∀-factor conclusion is the core theorem.
2. **The x-frame digit polynomial** (`xres` + `resPoly_x_frame`): B.29's residual at
   the key `X` is the `resFieldXEquiv`-image of a polynomial over `ResidueField O`
   whose coefficients are B.21 digits of the block's own coefficients (B.15's `dev_X`
   collapses developments to coefficients).  Irreducibility/monicity/degree read off
   through the equiv.
3. **THE TRANSPORT** (new, §2): the whole x-frame polygon apparatus
   (`npHgt`/`suppVal`/`OnSide`/`sideSet`/`sideMin`/`sideMax`/`sideDeg`/`IsPure`) and
   the digit polynomial transport along ANY ring map `h` with `Irreducible (h π)`
   (heights = coefficient valuations, preserved by IFCG32's
   `addVal_map_of_irreducible`; digits by B.22's `digAt_eq` + the witness-cancel
   argument; `pow_dvd_map_iff` both ways via the unit·π^n normal form).  Instantiated
   TWICE: at `algebraMap O (AdjoinRoot ψt)` with `resEmb`, and at `tau β` with
   `resTau`.
4. **The residual key**: the digit polynomial (monic, irreducible, degree `d`) lifts
   to a monic key `ψt` (`lifts_and_degree_eq_and_monic`); over
   `O' := AdjoinRoot ψt` (ENV-C via B53b + IFCG27's cascade, exactly
   `inertiaScaling_all`'s letI pattern) the residual splits into the `d` DISTINCT
   linear factors indexed by IFCG29's `keyRoots` (full splitting `card_keyRoots` +
   `nodup_keyRoots` + mathlib's `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`).
5. **Dissection + orbit** (`exists_tauProd_factorization`): B.63's private pinned
   dissection (re-derived verbatim from B.41b's public graded factorization) factors
   `g.map A = ∏_β G_β` along the split residual, each block monic pure of degree `ℓ`
   with residual the linear at `β`; each `G_β` and each conjugate
   `(G_{β₀}).map (tau β)` is IRREDUCIBLE by Step I again (linear residual); the
   conjugate has residual `X − C β` (transport at `tau β` + `resTau_apply_of_mem`),
   divides `∏ G_γ` (`map_tau_map_algebraMap`), hence UFD-matches a unique block —
   the one at `γ = β` (residuals pin, `resPoly_congr` + injectivity).  So
   `tauProd hkey (G_{β₀}) = g.map A` — IFCG32's `hGmap`, at a RAMIFIED-side block.
6. **Descent**: IFCG32 LEG A (`normValues_descent`) — every norm valuation of `g` is
   `d·v` — plus the packaged gcd trick (`dvd_inertiaDegOf_of_mem_normDivisors`).

`0 < d` is DERIVED from the irreducibility (a degree-0 residual is a unit or 0), so
the supply's statement needed no positivity hypothesis — consumed verbatim.

## ★★ THE WIRING (recomputed endgame)

* `residualLeafLaw_all` — IFCG35's `residualLeafLaw_of_supply` fired: the
  residual-irreducible leaf law holds at EVERY `(e', d)`, `e', d ≥ 1`, LEAN-CORE
  (the `d = 1` row was already core; now the whole family is).
* `decidedAt_of_spanning_irr` — IFCG35's spanning-leaf decision UNCONDITIONAL: a
  stratum class with a spanning `h/e'` face (`m = e'·d`, coprime, visible) and
  irreducible class residual is decided `⟨{(e', d)}⟩`.  The leaf-decision content of
  RECUR's `LeafSectorLaw` arm is now fully closed; ONLY the leaf-cell COUNT remains
  in that arm.
* `e1IrrLeafDecision` — ER4's named open (the (2,2) instance, = the `{(4,1)}`
  exclusion on the irreducible sector) PROVED, LEAN-CORE: the class bank (IFCG34's
  private `e1_class_bank`, replicated) + the witness lift's residual transported to
  the class residual (`classResidualPoly_eq`, heights pinned by
  `npHgt_monicPoly_eq` at `v₀ = 2 < 3 ≤ K`) + `decidedAt_of_spanning_irr` at
  `(h, e', d) = (1, 2, 2)`.
* `decided_inter_e1Irr` / `decided41_inter_e1Irr` — the irreducible sector is FULLY
  `{(2,2)}`-decided; the `{(4,1)}` alternative is EMPTY on it.  LEAN-CORE.
* `coneRemainderCount_four_type22/type41` (IFCG37 namespace) — ER4's census rows with
  the leaf premise DISCHARGED: the type22 count = full irreducible box + dd-recursion
  term; the type41 count = PURELY the double-root recursion term.  Footprint: core +
  B.42 (inherited from IFCG34's landed rows through IFCG31's bridge — the expected
  inheritance, nothing new).

## THE POST-RIS OPEN SET (RECUR's five items, recomputed)

`∀ n, DecidedSliceAt n` now rests on:

1. **`SplitSectorLaw e σ`** (e ≥ 5, σ ramified, under `< e` value laws) — unchanged.
2. **`PowerSectorLaw e σ`** — unchanged (fractional recentring).
3. **`LeafSectorLaw e σ`** — REDUCED: the block DECISIONS are now closed at every
   `(e', d)` with NO supply premise (`decidedAt_of_spanning_irr`); only the leaf-cell
   COUNT (block type × sub-face rest) remains.
4. ~~`ResidualInertiaSupply`~~ **CLOSED (this unit, Lean-core).**
5. **The five `e = 4` even-ram `ConeRemainderLaw`s** — REDUCED: within ER4's
   assembly, type22/type41's leaf premises are gone; the remaining ER4 opens are the
   depth-0 box limits (`ZcURLim e1SplitFam/e1IrrFam`) and the order-2 dd-recursion
   terms (`ZcURLim (e1DdDecFam σ)`), plus the split/E2 legs ER4 already closed
   conditionally.

Also retired implicitly: `BBox1CiteStatement`'s x-frame instance no longer needs an
owner signature (the general-φ statement remains open but has NO in-repo consumer at
a non-linear key; B.61's `hBOX` at general φ is still carried where used).

## File map (`leanfinal/Uniformity/ChapI/IFCG37.lean`)

§0 kit (`isKey_X`, `mem_sideSet_iff'`, `min'/max'_congr'`, `resPoly_congr`) ·
§1 `xres`, `resCoeff_x_frame`, ★ `resPoly_x_frame`, `irreducible_resPoly_x_iff`,
`xres_natDegree_monic` · §2 THE TRANSPORT (`injective_of_irreducible_map`,
`npHgt_X_map`, `suppVal_X_map`, `onSide_X_map_iff`, `sideSet_X_map`, `sideData_X_map`,
`isPure_X_map`, `pow_dvd_map_iff`, ★ `digAt_map`, ★ `xres_map`) ·
§3 ★ `sideDeg_pos_of_resPoly_irreducible`, ★★ `irreducible_of_pure_of_resPoly_irreducible`,
`monicFactors_of_pure_of_resPoly_irreducible`, `irreducible_of_pure_of_resPoly_linear` ·
§4 `exists_pinned_dissection` (B.63's engine, re-derived) · §5 `exists_monic_lift` ·
§6 ★★ `exists_tauProd_factorization` · §6b ★★★ `sideDeg_dvd_inertiaDegOf` ·
§7 ★★★ `residualInertiaSupply`, ★★★ `residualLeafLaw_all` · §8 the ER4 wiring
(`e1_class_bank'`, `spanning_side_data'` private copies, ★★★ `decidedAt_of_spanning_irr`,
★★★ `e1IrrLeafDecision`, `decided_inter_e1Irr`, `decided41_inter_e1Irr`,
★★ `coneRemainderCount_four_type22/type41`) · AxCheck footer (12 lines).
Imports beyond IFCG34/IFCG35 (which carry IFCG29/32 and most of ChapB): ChapB.B35c
(residual multiplicativity), B39b (`sideSet_nonempty_gen`, `resMk_one`), B41b (graded
factorization), B59a (`dev_X` idiom, `digPoly_C`, `resFieldXEquiv`).

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. Raw `rw [Polynomial.map_X]` matches the TYPE-LEVEL occurrence inside
   `resField X = AdjoinRoot (X.map residue)` — motive not type correct.  Fix: push
   maps with `simp only` (congruence-aware), `rw` only value-level equations.  (Bit
   twice: `resPoly_x_frame`, `hCbres`.)
2. RingEquiv-vs-RingHom coercion: state digit-polynomial equations with the `→+*`
   coercion of `resFieldXEquiv` and normalize with `RingEquiv.coe_toRingHom`; one
   let-transparency residue closed by `rfl`.
3. `isUnit_of_mul_eq_one` does not exist at the pin — it is `IsUnit.of_mul_eq_one`
   with `{a}` implicit and the OTHER factor explicit.
4. omega fed a variable·variable product (`ℓ * sideDeg`) — the standing trap;
   substitute the zero (`rw [h0, Nat.mul_zero]`) before arithmetic.
5. `rw [← hrhs] at h5` abstracted a pattern occurring under `G (...)` with a
   dependent `Nonempty` proof — motive failure; replaced by `h5.trans hrhs.symm` into
   `Polynomial.map_injective` (no rewrite).

Traps avoided by design: heights extracted only through the recorded
`WithTop.ne_top_iff_exists` + defeq-retype idiom; `sideMin/sideMax` never fed to
omega raw (`unfold` + `min'_congr'`); the Classical `sideSet` filter entered only
through the B83Kit `mem_sideSet_iff'` idiom; all `hne` (proof) arguments crossed
polynomial equalities via `resPoly_congr` (subst + rfl), never `rw`.
