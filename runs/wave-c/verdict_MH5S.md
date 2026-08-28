# VERDICT — UNIT MH5S (nodes MH.5 + MH.7 stretch), 2026-08-28

**PROVED / LANDED.** New file `leanfinal/Uniformity/ChapC/C133mh5.lean` (895 lines),
**zero sorry, zero new axiom**; every declaration's `#print axioms` footprint is exactly
`[propext, Classical.choice, Quot.sound]` (AxCheck footer, 34 declarations).  Verified by
`lake env lean Uniformity/ChapC/C133mh5.lean` (exit 0, no warnings) AND scoped
`lake build Uniformity.ChapC.C133mh5` (olean produced, "Build completed successfully").
No existing file touched; C133mh14 untouched and not imported.

## MH.5 — the corrected side lift Λ: **CLOSED IN FULL**

Route decision (the §9 row's flagged choice): the **public C131f `stageLiftO` pins**, fed
the inverse-twisted target `η^{q(M)}·κ` (§4.1's `[MHDISP]` corrected supply) — so NO
`Finite (ResidueField O)` hypothesis anywhere (the C.14 `exists_twistRead_preimage`
alternative was not needed); the private C.46/C.47 helpers are not consumed.

Three layers, all clause lemmas proved:

1. **Digit** `twistLiftO F H₀ hpin M κ` (:= `stageLiftO` at target `η^{twistExp M}·κ`, `0` at `κ = 0`):
   `twistLiftO_zero` · `natDegree_twistLiftO_lt` (`< D′`, unconditional) ·
   `stageHeight_twistLiftO` (`= M` exactly, fullness `D′h < M`, `κ ≠ 0`) ·
   `twistRead_twistLiftO` (**ϖ-read `= κ` on the nose** — the cocycle cancels exactly) ·
   `twistRead_zero` (public copy of C131aa's private helper).
2. **Window lift** `dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ` (§4.2's "the §4.1 lift without the
   monic top": digit `t` at abscissa `j₀ + tℓ`, height `M₀ − ut`, grade `ℓM₀ + uj₀`):
   `dev_dvWindowLift` (slot digit, ∀ t) · `dev_dvWindowLift_off` (off-grid 0) ·
   `natDegree_dvWindowLift_lt` (`< (j₀ + degψ·ℓ + 1)·D′`) · `natDegree_dvWindowLift_lt'`
   (the Lemma-S window: `j₀ < ℓ`, `degψ < a` ⟹ `< ℓaD′` — §4.2's `deg U < deg p₁`) ·
   `le_dvSupp_dvWindowLift` (**pinned W-height ≥ grade**, hypothesis
   `D′h + u·degψ < M₀`) · `twistRead_dvWindowLift` (read identity `= ψ.coeff t`, ∀ t).
3. **Monic-top Λ(P)** `dvSideLift F H₀ hpin u ℓ P`
   (:= `key^(dℓ) + dvWindowLift u ℓ 0 (u·d) P.eraseLead`), §4.1's five clauses verbatim:
   * clause 1: `dvSideLift_monic`, `natDegree_dvSideLift` (`= d·ℓ·D′`);
   * clause 2: `dev_dvSideLift_top/slot/past/off` + `dvHgt_dvSideLift_top` (`= 0`),
     `dvHgt_dvSideLift_slot` (**exactly `u(d−t)`**), `dvHgt_dvSideLift_slot_top`
     (`⊤` where `P.coeff t = 0`);
   * clause 3: `isDvPure_dvSideLift` (left endpoint from `P.coeff 0 ≠ 0`, top from monicity);
   * clause 4: `dvSupp_dvSideLift` (**`W(Λ(P)) = ℓ·(u·d)` exactly**),
     `dvHgt_dvSideLift_sideMin` (**`M₀ = u·d`**, every side witness),
     `dvSideSet_dvSideLift_nonempty` (packaged witness);
   * clause 5: `dvResPoly_dvSideLift` — **`R(Λ(P)) = P` exactly**, every side witness and
     finite pin (C131aa's `dvResPoly_testKey`, generalized from `L.r` to arbitrary monic `P`
     with `P.coeff 0 ≠ 0`; the top coefficient closes through `C133mh0.twistRead_one`).

Statement-fence notes (deviations, all mild): (i) `dvSideLift_monic`/`natDegree_dvSideLift`
carry `hd : 0 < P.natDegree` (implicit in §4.1's use; `Λ` of a constant degenerates to `1`);
(ii) the window height clause is `≥ grade`, exactly the charge's "pinned W-height ≥ c" (the
monic variant gets exact `=`); (iii) hypotheses use the standing strict floor
`ℓ·(D′·F.h) < u` and per-lemma fullness, never weaker.

## MH.7 — Lemma S: **PREFIX LANDED; assembly recorded as the named open shape**

Proved:
* `le_dvSupp_succ_of_lineReads_eq_zero` — **window read-faithfulness** (MH.0b's window
  half, Lemma S's closing step): `W(f) ≥ c` ∧ all grade-`c` line reads `= 0` ⟹
  `W(f) ≥ c+1`.  Unconditional, via the landed `C133mh3.m1DigitFaithful` at the attained
  infimum slot.
* `exists_bezout_degree_lt` + `bezout_degree_lt_unique` (any `Field K`) — §4.2's
  Bézout-with-degree-control: for coprime monic `G, H`, every `E` with
  `deg E < deg G + deg H` decomposes uniquely as `H·Ū + G·V̄`, `deg Ū < deg G`,
  `deg V̄ < deg H` (the "injective hence bijective K-linear map", in solved existential +
  uniqueness form — no dimension count needed).
* `exists_stageField_bezout_degree_lt` + `stageField_bezout_degree_lt_unique` — the
  stage-field instantiation through the §9-row's "locally reconstruct `Field K`" (standing
  private D9 `localFieldStageField`); the exported statements are instance-free.

Named open (the MH.9 carried hypothesis, exact §4.2 statement in landed vocabulary):
* `LemmaSStatement : Prop` (statement shape, C133mh1 pattern, nothing asserted) — data:
  monic pure `p₁ p₂`, `D′ ∣ deg`, residual pins, `IsCoprime R(p₁) R(p₂)`, weights
  `w₁ w₂`, error `e` with `deg e < deg p₁ + deg p₂`, `W(e) ≥ c ≥ w₁ + w₂`; conclusion:
  `U V` in the degree windows, `W(U) ≥ c − w₂`, `W(V) ≥ c − w₁`,
  `W(e − (p₂U + p₁V)) ≥ c + 1`.

**The one open leg blocking the Lemma S assembly** (why the shape, not the theorem): the
grade-`c` MIXED product read law — `read_c(p·U) = R(p)·read(U)` at an arbitrary grade `c`
at/above the support line.  The landed `C133mh3.dvResPoly_mul_gen` reads at the support
line (`W`-pinned, `dvSideMin`-anchored) only.  This is Theorem-M-clause-3-at-grade-`c`,
an MH.3-scale node (250–450 lines by the doc's own pricing) — it, plus the corpus-level
grade-line read bookkeeping, is exactly what MH.9 must add before discharging
`LemmaSStatement`.  All OTHER ingredients of the §4.2 proof are now landed in this file.

## Notes for MH.9

* The general-offset window lift takes `j₀` (the abscissa residue of the grade mod the
  `(u,ℓ)`-lattice) explicitly; MH.9 must supply `j₀ < ℓ` with `u·j₀ ≡ c (mod ℓ)` when
  instantiating at grade `c` (the lattice can be empty for small `c`, so no total
  grade-read definition was introduced — deliberate).
* Fullness bookkeeping: the window lemmas need `D′h + u·degψ < M₀`; at the §4.4
  initialization this reduces to the standing strict floor (`slot_full` shows the pattern).
* `exists_testKey` (C.14) + `isTestKey_isDvPure`/`dvResPoly_testKey` (C131aa) are the
  `IsTestKey`-specialized ancestors of Part 3; nothing here duplicates their statements
  (this file's Λ is for arbitrary monic `P`, theirs is pinned to `L.r`, and this file is
  finiteness-free).

## Build discipline record

Skeleton-first (all statements elaborated with sorry, verified green), then 5 filled
increments, each compiled and on disk before the next: Part 1 digits → Part 2 window →
Part 3a Λ-dev/monic/degree → Part 3b heights/W/purity/residual → Parts 4–5.  Repairs hit:
3 (implicit-argument pinning on `have`, one omega atom-congruence needing a pre-`rw`, two
mathlib-pin name drifts: `Finset.nonempty_range_add_one`, `modByMonic_add_div` taking `q`
explicitly).  None required re-sketching.
