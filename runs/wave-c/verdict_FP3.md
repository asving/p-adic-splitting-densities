# UNIT FP3 — VERDICT: LANDED (2026-08-29)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG18.lean` (1111 lines, ZERO sorries,
axiom footprint Lean core `{propext, Classical.choice, Quot.sound}` on every footer
line; the C.33 cite does not occur; IFCG15/16/17 byte-untouched).

**★★ THE REDUCTION (proved, unconditional on the two kernels):**

    rationalNonloopCensusAt_of_kernels :
      SinglePointAggregateLaw → DeepLinearClusterLaw →
      ∀ {m}, 4 ≤ m → IFCG16.RationalNonloopCensusAt m

    decidedSliceAt_all_of_singlePoint :
      SinglePointAggregateLaw → DeepLinearClusterLaw →
      ∀ n, Uniformity.Density.DecidedSliceAt n

The full chain above: IFCG16.decidedSliceAt_all_of_census ← the census ← THIS reduction.
The campaign's remaining open content is now exactly TWO named statements (file §3).

**★ THE SINGLE-POINT KERNEL (the campaign's last named statement, stated EXACTLY):**

    def SinglePointAggregateLaw : Prop :=
      ∀ m : ℕ, 4 ≤ m →
        (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
        ∀ b : SBlock, 1 ≤ b.δ → b.E ≠ [] → (∀ e ∈ b.E, 1 ≤ e) → b.mass ≤ m →
          ¬(b.δ = 1 ∧ b.E = [m]) →
          ∀ s : Multiset (ℕ × ℕ), URLim (spFamily b s)

where `spFamily b s O N = ((SPAgg O N b ∅) s : ℝ) / q^(b.mass·N)` and `URLim F` means:
ONE `Polynomial ℚ` pair `(n, d)`, `d ≠ 0`, with `d.eval q ≠ 0` and
`Tendsto (F O) atTop (nhds (n.eval q / d.eval q))` at EVERY complete DVR `O` with finite
residue field. The self-referential pure deep-linear block `(1, [m])` is EXCLUDED (its
raw aggregate contains the full degree-m self-call); it enters only loop-corrected as

    def DeepLinearClusterLaw : Prop :=
      ∀ m, 4 ≤ m → (smaller value laws below m) →
      ∀ σ, σ.degree = m → Witnessed m σ →
        ∃ n d : Polynomial ℚ, d ≠ 0 ∧ ∀ O [complete DVR, finite residue],
          d.eval q ≠ 0 ∧ ∀ π, Irreducible π →
            Tendsto (fun M => (pcellCount O π m σ M {(1, m)} : ℝ) / q^(m·(M+m)))
              atTop (nhds (n.eval q / d.eval q))

with `pcellCount O π m σ M t = Nat.card (nonloopDecidedSet π m σ M ∩ {c |
patternOf (stratumPoly O m (M+m) c) = t})`. Both kernels are CONDITIONAL on the value
laws below m — neither is stronger than the remainder it refines (IFCG16 §3's audit
discipline).

**★★★ decidedSliceAt_all does NOT fire — the check was run, honestly:**
- e = 1 blocks reduce (via H124's irreducible-stratum-decided + H124b's
  `card_levelZeroStratum`) to the count of monic irreducibles of degree δ as a
  polynomial in q — Gauss's necklace count. The corpus has it ONLY at δ ≤ 3
  (IFCG4's degree-specific counts); the uniform-in-δ law is known math, unlanded.
- δ ≥ 2 blocks need the unramified base-change recentering (the census over the
  degree-δ unramified extension read at q^δ) — no landed theorem exports it.
- e ≥ 2 blocks (and all merged multi-exponent blocks) are the fractional-slope deep
  Okutsu–Montes cone censuses — the genuinely open heart.
- A cheap future sub-unit: discharge the kernel RESTRICTED to (δ ≤ 3, e = 1) blocks
  from IFCG4 + H124b; the general law needs the three items above.

---

## Original stub (stages, all closed)

Charge: finish the multi-point census stages against IFCG17's landed banks (S1–S5 + the
collision peel are LANDED there; remaining: §6b labelled/unlabelled exchange, §7 URseq +
the NAMED kernels, §8 assembly); land the multi-point per-genre clause; state and prove
the reduction `UniformRationalNonloopCensus ⟸ SinglePointAggregateLaw ∧
DeepLinearClusterLaw`; display the single-point kernel EXACTLY (the campaign's last named
statement). Fire ★★★ `decidedSliceAt_all` only if the kernel yields to landed machinery.

File: `leanfinal/Uniformity/ChapI/IFCG18.lean` (NEW; IFCG17 read-only).

## Planned stages (updated as they land)

- [x] S1 §1: `multPattern` (the labelling multiplicity ∏ (count)! with the cons law) +
      ★ `VAgg_eq_fiber` — on simple block systems the distinct-tuple aggregate is
      `multPattern π • Σ_{g ∈ fiber(π,A)} stratPoly g` (induction: `tuple_sum_succ` →
      `stratPoly_mul` on the fresh coprime head → §5b's `sum_sigma_fiber_eq`).
      LANDED (green 2026-08-29). Repair notes: (i) `set`-bound locals are opaque to the
      unifier — Fin.cons/SBlock projection reduction dies; spell literals. (ii) a `calc`
      restating the big post-peel sum re-elaborates + re-unifies it (heartbeat death);
      rewrite goal-side instead (`rw [VAgg, Finset.mul_sum]` then `sum_congr`).
      (iii) `congr 1` on `n • x = n • y` splits into HSMul junk; use `congrArg`.
- [x] S2 §2: the uniform-rational-limit calculus `URLim` (one O-independent `Polynomial ℚ`
      pair; limit at every complete DVR; closure under const/mul/add/sub/Finset-sum/congr).
      LANDED (green 2026-08-29, first attempt).
- [x] S3 §3: ★ THE NAMED KERNELS — `SinglePointAggregateLaw` (normalized SPAgg coefficient
      families of super-blocks, mass ≤ m, EXCLUDING the self-referential deep-linear block
      `(1,[m])`, conditional on the smaller value laws) + `DeepLinearClusterLaw` (the
      loop-corrected `{(1,m)}` pattern cell of `nonloopDecidedSet`, via `pcellCount`).
      STATED (definitions compile; the exact statements are in the file's §3).
- [x] S4 §4: `V_tendsto` = `vaggFamily_URLim` — the peel induction LANDED (green
      2026-08-29): `VAgg_cons_eq` + `mul_apply_powerset` + the URLim calculus;
      `sum_mass_update` does the merge mass accounting. Repair notes: AddMonoidAlgebra's
      add/nsmul instances aren't syntactically Finsupp's — coefficient extraction needs
      the local `typeAlg_sum_apply`/`typeAlg_nsmul_apply` rfl-helpers, and the peel
      coefficient identity is proved by rewriting BACKWARDS into `(X*Y) s` form.
- [x] S5 §5: `patternBank m` + `mem_patternBank_iff` + `patternOf_mass` (mass = degree via
      `natDegree_multiset_prod` + `sum_multiset_map_count`) + positivity + membership.
      LANDED (green 2026-08-29).
- [x] S6 §6: loop confinement (`patternOf_stratumPoly_loopClassN` via IFCG3's
      `map_residue_monicPoly_loopMapN`, pattern `{(1,m)}`), the exact pattern-cell
      partition `card_nonloopDecidedSet_eq_sum_pcellCount`, and
      `pcellCount_eq_fiber_sum` for non-deep cells. LANDED (green 2026-08-29).
      Also LANDED: `fiberFamily_URLim` (§7) — the exchange divides by `multPattern`.
- [x] S7 §7: ★★ the census assembly `rationalNonloopCensusAt_of_kernels` (bank = non-deep
      patterns of `patternBank m` + the deep genre, indexed `Fin (B'.card + 1)` via
      `Finset.equivFin` + `Fin.snoc`; children lists empty — the census's own smaller-laws
      input rationalizes everything; partition = §6's exact pattern-cell partition; limits
      read along `M ↦ M + m` via `tendsto_add_atTop_nat`) + the capstone reduction
      `decidedSliceAt_all_of_singlePoint`. LANDED (green 2026-08-29).
      Repair note: `Fin.snoc` needs its motive annotated (`(α := fun _ => Multiset (ℕ×ℕ))`)
      in witness lambdas.
- [x] S8: the ★★★ check — ran; does NOT fire; findings in the header block above.

## Notes so far

- IFCG17's landed span EXCEEDS its stub: §§1–5 AND §6's `VAgg_cons_eq` (exact collision
  peel) are all green; only §6b/§7/§8 remained — they are this unit.
- Design decision (recorded): the census bank uses EMPTY children lists — since
  `RationalNonloopCensusAt` is conditional on all smaller value laws, every child density
  is already one rational pair, so the URLim pairs absorb the children products. The
  kernels are therefore also stated conditional on the smaller laws (µ ≤ m window),
  keeping them no stronger than the remainder they refine.
- Kernel honesty fence: the pure deep-linear super-block `(1,[m])` is EXCLUDED from
  `SinglePointAggregateLaw` — its raw aggregate secretly contains the full degree-m
  density via the loop self-call; it enters only loop-corrected, as
  `DeepLinearClusterLaw`. Merged blocks `(1, E)` with `|E| ≥ 2` stay in scope (their
  components have mass < m).
