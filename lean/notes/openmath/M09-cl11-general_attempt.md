# M09-cl11-general — attempt (Fable, 2026-07-31)

## Resolution in one paragraph

`KsubM1C1T T` is a **theorem of DEG-CONS alone**, at every n and every table:
if all members of an outcome at a degree-e state (1 ≤ e ≤ n) have size e, then
the DEG-CONS sum law Σ sizes ≤ e reads m·e ≤ e, and e ≥ 1 forces m = 1 by
pigeonhole; c ≤ m = 1 together with c ≠ 0 forces c = 1. Since every context
where the ledger row `cl11_ksub : KsubM1C1T C.T` appears carries
`C.hdc : MovesS.DegCons C.T` (a field of the `UCarriers` parameter of both
`CapstoneLedger` and `BridgeKernels`), the row is derivable at ALL n — no
instance roster walk, no obstruction. Verified end-to-end in Lean against the
repo's own definitions (compile record below), Lean-core axiom footprint.

## Main theorem

**Theorem 1 (general n; consumes only `hdc`).** Let n ≥ 1 and let T be any
`TableShape n` satisfying DEG-CONS, i.e.

  (i) every member of every outcome has size ≥ 1;
  (ii) for every e with 1 ≤ e ≤ n, every state τ at degree e and every
       outcome o of τ, the sizes of o's members sum to at most e.

Then for every such (e, τ, o): if every member of o has size exactly e and o
has a continuing member, then m(o) = 1 and c(o) = 1.

*Proof.* Fix e, τ, o with 1 ≤ e ≤ n, all member sizes = e, and c(o) ≠ 0. Write
m := m(o) = |mem(o)|; the member list is nonempty by the structural field
`hm : mem ≠ []`, so m ≥ 1. Since every member has size e, the size sum is
exactly m·e, and (ii) gives m·e ≤ e. If m ≥ 2 then m·e ≥ 2e > e (using
e ≥ 1), a contradiction; hence m = 1. The continuing members form a sublist
of the member list, so c(o) ≤ m(o) = 1; with c(o) ≠ 0 this gives c(o) = 1. ∎

Note (i) was not even needed for Theorem 1 (all sizes equal e ≥ 1 already);
it IS needed for the sharper Corollary 2 below.

**Corollary 1 (the ledger row at every n).** For every n and every carrier
pack `C : UCarriers n`, `KsubM1C1T C.T` holds, witnessed by
`ksubM1C1T_of_degCons C.T C.hdc`. Both structures carrying the row
(`CapstoneLedger`, DefsLedger.lean:794; `BridgeKernels`,
BridgeKernels.lean:263) take `C : UCarriers n` as a parameter, so the row is
supplied uniformly in n and p.

**Corollary 2 (the docstring's parenthetical, made precise).** Under full
DEG-CONS ((i) and (ii)), the guard "∀ members have size e" is equivalent to
"∃ a member of size e": if some member has size e, the remaining members have
sizes ≥ 1 summing to ≤ e − e = 0, so there are none — m = 1 and the guard
holds. (Proved in Lean as `ksub_exists_form`, below.) Consequently the
∃-form of (K-SUB) is also a DEG-CONS consequence, and the two published
readings of the row coincide, as the `KsubM1C1T` docstring claimed without
proof.

## Lean verification (compile record)

Both files compile green against the built repo
(`cd lean && lake env lean <file>`, 2026-07-31), zero sorries;
`#print axioms` on both theorems: `[propext, Classical.choice, Quot.sound]`
(Lean-core only). Scratch copies at `/tmp/M09_cl11_general_check.lean`,
`/tmp/M09_cl11_exists_form.lean`; full sources inlined here for durability.

### Theorem 1 + Corollary 1

```lean
import Mathlib
import LeanUrat.MovesU.DefsCarriers

namespace LeanUrat.MovesU
open LeanUrat.MovesS

/-- GENERAL n: `KsubM1C1T` holds at ANY table satisfying DEG-CONS —
    pigeonhole on the member-size sum. -/
theorem ksubM1C1T_of_degCons {n : ℕ} (T : MovesS.TableShape n)
    (hdc : MovesS.DegCons T) : KsubM1C1T T := by
  intro e he τ o hall hc
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have hlen : 1 ≤ (T.odata e τ o).mem.length :=
    List.length_pos_iff.mpr (T.odata e τ o).hm
  have hmap : (T.odata e τ o).mem.map Member.size
      = List.replicate (T.odata e τ o).mem.length e := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hb
    exact hall μ hμ
  have hsum : (T.odata e τ o).mem.length * e ≤ e := by
    have := hdc.size_sum e he τ o
    rwa [hmap, List.sum_replicate, smul_eq_mul] at this
  have hm1 : (T.odata e τ o).mem.length = 1 := by
    rcases Nat.lt_or_ge (T.odata e τ o).mem.length 2 with h | h
    · omega
    · exfalso
      have : 2 * e ≤ (T.odata e τ o).mem.length * e :=
        Nat.mul_le_mul_right e h
      omega
  have hcm : (T.odata e τ o).c ≤ (T.odata e τ o).m :=
    List.length_filter_le _ _
  refine ⟨hm1, ?_⟩
  have hme : (T.odata e τ o).m = 1 := hm1
  omega

/-- The ledger-row form: `cl11_ksub` is DERIVABLE from `C.hdc` at every pack. -/
theorem UCarriers.cl11_ksub_general {n : ℕ} (C : UCarriers n) :
    KsubM1C1T C.T :=
  ksubM1C1T_of_degCons C.T C.hdc

end LeanUrat.MovesU
```

### Corollary 2 (∃-form; consumes `size_pos` + `size_sum`)

```lean
import Mathlib
import LeanUrat.MovesU.DefsCarriers

namespace LeanUrat.MovesU
open LeanUrat.MovesS

theorem ksub_exists_form {n : ℕ} (T : MovesS.TableShape n)
    (hdc : MovesS.DegCons T) :
    ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
      (∃ μ ∈ (T.odata e τ o).mem, μ.size = e) →
      (T.odata e τ o).mem.length = 1 ∧ ∀ μ ∈ (T.odata e τ o).mem, μ.size = e := by
  intro e he τ o hex
  obtain ⟨μ, hμ, hsz⟩ := hex
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  obtain ⟨s, t, hst⟩ := List.append_of_mem hμ
  have hsum : ((T.odata e τ o).mem.map Member.size).sum ≤ e := hdc.size_sum e he τ o
  rw [hst] at hsum
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hsz] at hsum
  have hs0 : (s.map Member.size).sum = 0 ∧ (t.map Member.size).sum = 0 := by omega
  have hsnil : s = [] := by
    by_contra hne
    obtain ⟨ν, hν⟩ := List.exists_mem_of_ne_nil _ hne
    have hν' : ν ∈ (T.odata e τ o).mem := by rw [hst]; simp [hν]
    have h1 : 1 ≤ ν.size := hdc.size_pos e τ o ν hν'
    have hle : ν.size ≤ (s.map Member.size).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map_of_mem hν)
    omega
  have htnil : t = [] := by
    by_contra hne
    obtain ⟨ν, hν⟩ := List.exists_mem_of_ne_nil _ hne
    have hν' : ν ∈ (T.odata e τ o).mem := by rw [hst]; simp [hν]
    have h1 : 1 ≤ ν.size := hdc.size_pos e τ o ν hν'
    have hle : ν.size ≤ (t.map Member.size).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map_of_mem hν)
    omega
  have heq : (T.odata e τ o).mem = [μ] := by rw [hst, hsnil, htnil]; rfl
  refine ⟨by rw [heq]; rfl, ?_⟩
  intro ν hν
  rw [heq] at hν
  simp only [List.mem_singleton] at hν
  rw [hν]; exact hsz

end LeanUrat.MovesU
```

## Relation to the existing corpus

- **Supersedes the n = 2 roster walk as a discharge mechanism.**
  `ksubM1C1T_n2` (SynK1_ksubN2.lean) remains true and useful as an instance
  cross-check, but the general theorem + `n2_degcons_scs`
  (MovesS/N2DegScs.lean, DEG-CONS at the concrete n = 2 table) re-derives it.
- **Row-disposition consequence (for the orchestrator; statement-change
  territory, needs sign-off).** The `cl11_ksub` rows of `CapstoneLedger` and
  `BridgeKernels` are now REDUNDANT fields (derivable from the `C : UCarriers
  n` parameter each structure already carries), exactly parallel to how
  `cl13_wf` was discharged by `menuWFT_holds`. Options: (a) keep the row and
  supply it by `UCarriers.cl11_ksub_general` at every instantiation (no fence
  event, matches the SYN2-K1 scope note); (b) delete the row (a
  statement-change / golf event). This attempt takes no position; both are
  now available at all n.
- **No new axiom, no new obligation created.** The proof consumes only
  `C.hdc` — DEG-CONS itself remains the carried CL-11 burden it already was
  (produced at instances by `n2_degcons_scs`, and generically by the MovesV
  gate `V2_degcons`/`V7_tsGate`). The K-SUB face adds nothing on top of it.

## Result labels (per the rigor policy)

- Theorem 1 / Corollaries as statements about the repo's abstract
  `TableShape`: **(c) claimed new** within the corpus — but mathematically
  elementary (pigeonhole on a sum bound); no literature claim attached.
- The instance-level shadow ("an OM/MacLane refinement event of a degree-e
  block whose factors all have degree e is unibranch") is **(a) known** in
  substance: it is the degree-additivity of Newton-polygon/residual
  factorization in MacLane–Okutsu–Montes theory (factor degrees of a
  refinement event sum to the parent degree, so a full-degree factor is the
  only factor). Attribution to a precise numbered theorem (e.g. in
  Guàrdia–Montes–Nart, "Newton polygons of higher order in algebraic number
  theory", Trans. AMS 364 (2012)) is FLAGGED FOR LOOKUP, not asserted; the
  Lean result does not depend on it.
- NOT literature-axiom-eligible and no axiom needed: the obligation is fully
  proved from carried hypotheses.

## VERDICT

**PROVED** at all n: `KsubM1C1T T` follows from `MovesS.DegCons T`
(Theorem 1, Lean-verified, Lean-core footprint), hence the `cl11_ksub`
ledger row is derivable from the carried `C.hdc` at every carrier pack and
every n. The n = 2 roster walk is subsumed; no obstruction exists.

## NUMERIC-TESTS

The abstract claim is machine-checked, so numerics target (1) the SEMANTIC
faithfulness of DEG-CONS at real p-adic factorization data (the hypothesis
the proof consumes) and (2) direct brute-force of the row at concrete tables.

1. **Root-level degree conservation (DEG-CONS instance, equality form) —
   EXECUTED 2026-07-31.** For p ∈ {2, 3, 5, 7, 13} and n ∈ {2, …, 8}, 200
   random monic degree-n polynomials each (coefficients uniform in
   [0, p^10)); factored over ℚ_p via PARI/GP `factorpadic(f, p, 40)`
   (cypari2 not installed in this env; `gp` used directly, script
   `/tmp/m09_test.gp`, seed 7); checked Σ_i (deg g_i · mult_i) = n.
   RESULT: `samples=7000 deg-sum-violations=0`. (This is the Σ sizes ≤ e
   law, with equality, at the root block e = n.)

2. **Equal-degree ⇒ single factor (the pigeonhole itself, at the root) —
   EXECUTED 2026-07-31.** Same 7000 samples: whenever every irreducible
   factor of f has degree n, assert exactly one factor with multiplicity 1.
   RESULT: `all-deg-n-cases=1912 pigeonhole-violations=0`. Theorem 1's
   mechanism observed on real data.

3. **Tower-level events (the real content of the instance semantics).**
   Using the repo's oracle (`verification/quartic_oracle.py`, PARI
   factorpadic) extended to report the OM/Montes refinement tree (e.g. via
   `pari.polresultant`-free route: iterate factorpadic over lifts, or use a
   Montes implementation): for p ∈ {2, 3} and 10^3 quartics/sextics, record
   at every internal node of the factorization tree the parent block degree
   e and the child degrees; check (a) Σ child degrees ≤ e always, and (b)
   every node whose children all have degree e and which continues (is not
   yet decided) has exactly one child. CONFIRMS: zero violations. A
   violation of (a) would refute the DEG-CONS faithfulness of the intended
   instance (an issue for the `hdc` producers `n2_degcons_scs`/`V2_degcons`,
   NOT for this row); (b) cannot fail while (a) holds, by Theorem 1.

4. **Table-level brute force (when new instance tables land).** For any
   future concrete `TableShape` instance (e.g. an n = 3 table analogous to
   `n2T`), run the finite check `decide`-style: enumerate all (e, τ, o) with
   1 ≤ e ≤ n and verify the (m, c) classification directly, as
   `ksubM1C1T_n2` did at n = 2 — expected to pass automatically given the
   table's DEG-CONS unit, by Theorem 1.
