# M16-zf-serre — attempt (Fable): literature identification + independent faithfulness analysis

*Companion to `M16-zf-serre_brief.md` (all objects defined there). This is the
INDEPENDENT faithfulness analysis requested for the concurrently-executing
queue item 2 (the ramIdx/resDeg re-point + Serre axiom declaration). Nothing
here was coordinated with that repair agent; the Lean quotes are from HEAD
(commit 4ceab32), where the axiom is NOT yet declared.*

## 0. Verdict summary

The obligation splits into four laws. Exactly ONE of them carries content
beyond the pinned Mathlib — the DVR-ness/locality of the integral closure of
ℤ_p in the factor field (M16-existence). That one is literature-grade
(Serre, Corps Locaux/Local Fields, Ch. II §2 package; backups below), and the
minimal axiom form `Nonempty (LocalFactorData p h)` for monic h with
ℚ_p-irreducible image states strictly LESS than the citation. The other three
laws (zf_pos, pointwise e·f = deg, zf_factor assembly) are DERIVABLE at the
pin from that one axiom; I give the complete, name-verified Mathlib lemma
inventory. Two faithfulness constraints are load-bearing: (i) the
irreducibility hypothesis on the axiom (dropping it makes the axiom FALSE —
§4.1, rigorous two-line refutation); (ii) the aggregate-vs-pointwise
distinction in `zf_factor` conjunct 4 (both derivable; do not conflate).
Secondary finding: the axiom is plausibly DISCHARGEABLE at the pin by
replaying the corpus's own IP-1 idempotent machinery at the integral closure
(§6) — recorded as a reduction, not executed.

## 1. The obligation split

At the repaired (integral-closure) reading, with h ranging over monic
elements of ℤ_p[X] with irreducible image in ℚ_p[X], K_h = ℚ_p[X]/(h̄),
O_h = integral closure of ℤ_p in K_h:

- **(L0) = (M16-existence):** O_h is a DVR, with maximal ideal over p·ℤ_p —
  formally: `Nonempty (LocalFactorData p h)`.
- **(L1) = zf_pos:** e(h) ≥ 1 ∧ f(h) ≥ 1.
- **(L2) = (M16-pointwise):** e(h)·f(h) = deg h.
- **(L3) = zf_factor:** the four-conjunct assembly over `monicFactors g`.

## 2. The literature statements (all label (a): known)

**(LF-1) Extension of a complete DVR.** Let A be a complete discrete
valuation ring, K = Frac(A), L/K a finite extension of degree n, B the
integral closure of A in L. Then:
(i) the valuation of K extends UNIQUELY to a (discrete) valuation of L, and
    B is its valuation ring — in particular B is a DVR and is local;
(ii) L and B are complete;
(iii) if L/K is separable, B is a free A-module of rank n;
(iv) m_B ∩ A = m_A (the maximal ideal lies over the maximal ideal).

**(LF-2) Fundamental identity, complete discrete separable case.** In the
setting of (LF-1) with L/K separable, writing e = e(L/K) (= v_L(π_K)) and
f = [B/m_B : A/m_A]: e·f = n.

**(LF-3) Positivity.** e ≥ 1 (π_K lands in m_B, by (LF-1)(iv)) and f ≥ 1
(a field extension has degree ≥ 1; finite by (LF-1)(iii)). Trivial
consequences of (LF-1) — no independent citation needed.

Since char ℚ_p = 0, every finite L/ℚ_p is separable: the separability
hypotheses in (iii)/(LF-2) are automatically satisfied on the entire locus
M16 quantifies over, INCLUDING all wild cases (wildness p | e is a
ramification phenomenon, not a separability one). No citation with an
inseparability caveat is therefore load-bearing.

**Citations.**

- PRIMARY: J.-P. Serre, *Corps Locaux* (Hermann, 1962) / *Local Fields* (GTM
  67, transl. Greenberg, 1979), **Ch. II ("Completion"), §2 ("Extension of a
  complete field")** — the section's proposition package is exactly
  (LF-1)+(LF-2); in the GTM edition this is the Prop. 3/Prop. 4 pair
  (structure statement, then e·f = n), consistent with this repo's earlier
  pinned citation practice (`lean/notes/L5fix_complete.md` §5(c) pins
  "Serre LF II §2 Prop. 4" for the fundamental identity/defectlessness).
  ⚠ CONFIDENCE FLAG: chapter+section is certain; the proposition NUMBERS are
  from memory + repo precedent and MUST be page-verified when the
  `AXIOM_FAITHFULNESS.md` entry is written (the axiom policy requires the
  entry at declaration; I could not obtain page images from this sandbox —
  web search returned no quotable text of the propositions).
- Also Serre, **Ch. I §4** (Dedekind extensions): Σᵢ eᵢfᵢ = n over the primes
  above m_A when B is module-finite over A (Prop. 10-region; same flag);
  (LF-2) = this + locality from (LF-1)(i).
- BACKUP (independent tradition): J. Neukirch, *Algebraic Number Theory*
  (Grundlehren 322, 1999): **Thm. II.4.8** (complete field: unique extension
  of the absolute value, L complete — high confidence in the number) and the
  Ch. II §6 fundamental identity for henselian discrete separable extensions
  (Thm. 6.8-region — medium confidence, same flag). The repo already cites
  Neukirch II-chapter results (`notes/BB3_infinity.md`, `docs/HUMAN_PROOF.md`
  A5) for the adjacent defectlessness facts.
- BACKUP: Bourbaki, *Algèbre commutative*, Ch. VI §8 ("Extensions d'une
  valuation"), complete-discrete no. (flagged, no. from memory).
- FORMALIZATION COMPANION (verified to exist, statement-level match): M. I.
  de Frutos-Fernández, F. A. E. Nuccio, "A Formalization of Complete Discrete
  Valuation Rings and Local Fields", CPP 2024, arXiv:2310.01998 — §2.5
  formalizes extensions of complete DVRs in Lean 4/Mathlib (their development
  is exactly the not-yet-at-the-pin Mathlib material; it cites Serre Ch. I–II
  as the paper source). Useful both as a second literature anchor and as the
  eventual upstream discharge path for the axiom.

## 3. The minimal axiom and its faithfulness audit

Recommended declaration shape (matches the ratified re-point plan: the
`OM/QpType.lean` vocabulary):

```lean
axiom AX_localFactorData_exists (p : ℕ) [Fact p.Prime] (h : Polynomial ℤ_[p])
    (hm : h.Monic) (hirr : Irreducible (h.map (algebraMap ℤ_[p] ℚ_[p]))) :
    Nonempty (LocalFactorData p h)
```

Field-by-field audit against (LF-1) instantiated at L := ℚ_p[X]/(h̄), n :=
deg h (h̄ = image of h; irreducible by hypothesis, so L is a field):

| bundle field | source | excess over (LF-1)? |
|---|---|---|
| `L`, `fieldL`, `algQL` | the construction L = ℚ_p[X]/(h̄) — standard field theory, Lean-provable (`AdjoinRoot.instField` at irreducible h̄) | none (not literature-conditioned) |
| `algZL`, `towerZQL` | composite ℤ_p → ℚ_p → L | none |
| `finrank_eq` | [L:ℚ_p] = deg h̄ = deg h for irreducible h̄ (`AdjoinRoot.powerBasis`) | none |
| `hasRoot` | X mod (h̄) is a root generating L | none |
| `O`, `crO`, `domO`, `algZO`, `algOL`, `towerZOL`, `intClosure` | O := integralClosure ℤ_[p] L, a subalgebra of the field L | none (definitional packaging; any `IsIntegralClosure` carrier is canonically isomorphic to it, `IsIntegralClosure.equiv`) |
| `dvrO : IsDiscreteValuationRing O` | **(LF-1)(i) — THE axiom content** | none: (LF-1)(i) says exactly this |
| `liesOver` | (LF-1)(iv); ALSO derivable axiom-free (integrality lying-over: the contraction of a maximal ideal under an integral extension of a local domain is the maximal ideal) | none (doubly covered) |

**What the bundle does NOT assert** (i.e., where it is strictly weaker than
the citation): completeness of O ((LF-1)(ii)), module-finiteness/freeness and
the rank ((LF-1)(iii)), e·f = n ((LF-2)), uniqueness of the extension.
Dropping literature content is faithful-safe; the dropped parts that are
needed downstream (finiteness, e·f = n) are RE-DERIVED at the pin (§5), which
gives them an independent machine-checked proof from the axiom rather than a
citation — strictly better for the trust base.

**Quantifier scope check.** The axiom quantifies over all p, all monic h with
irreducible image — exactly the locus (LF-1) covers (each instance is one
finite extension of ℚ_p). Instances with deg h = 1 are provable outright
(witness `trivialFactorData`-style, O = ℤ_p) — harmless overlap. No
uniformity-in-p claim is made (each instance is a separate classical fact).
VERDICT: the axiom states NO MORE than (LF-1); with the guard of §4.1 it is
faithful.

## 4. Load-bearing faithfulness constraints

### 4.1 The irreducibility hypothesis is NOT droppable

Claim: `Nonempty (LocalFactorData p g)` is FALSE for g = X² (monic, degree
2, reducible image). Proof: a bundle D gives x ∈ D.L with x² = 0 in the field
L, so x = 0; then `Algebra.adjoin ℚ_p {0} = ⊤` forces L = ℚ_p, so
finrank = 1, contradicting `finrank_eq : finrank ℚ_p L = 2`. ∎

More generally, bundle-inhabitation CHARACTERIZES irreducibility: if x
generates L with [L:ℚ_p] = deg g and g̅(x) = 0, then minpoly(x) | g̅ with
deg minpoly = [L:ℚ_p] = deg g̅, and both monic, so g̅ = minpoly(x) is
irreducible. So an axiom quantified over all monic g (or with the hypothesis
weakened to "irreducible in ℤ_p[X]" — beware: X²+p·X+p² style examples stay
irreducible over ℤ_p in some rings but the relevant guard is the ℚ_p-image;
over ℤ_p the two agree for monic h by the proved Gauss iff, so either guard
is faithful HERE, but the ℚ_p-image form matches both (LF-1) and the
consumers) would be REFUTABLE inside Lean. Any declared axiom missing the
guard is a stop-the-line defect.

### 4.2 Aggregate vs pointwise (zf_factor conjunct 4)

Conjunct 4 as frozen is the multiset identity {e_i·f_i} = {deg h_i}; the
project record correctly notes it does not pin the pointwise (L2). Both
follow from (LF-2): pointwise directly, aggregate by `Multiset.map_congr`
from conjunct 3 + pointwise. The literature supports the STRONGER pointwise
form, so the queued pointwise retype is faithfulness-neutral (premise-side
strengthening backed by the same citation). No citation supports aggregate-
without-pointwise as a natural statement; if the retype is executed, cite
(LF-2) for the pointwise law and derive the aggregate.

### 4.3 W1 — cross-bundle invariance (watch-point, not currently consumed)

The repaired `ramIdx`/`resDeg` read a classically CHOSEN bundle. All five
`ZpBridge` fields quantify over that one chosen reading, so no law currently
needs two bundles to agree. But the fact is true and citable: any two bundles
D, D′ for the same h are related by a ℚ_p-algebra isomorphism L ≅ L′ (both
are root fields of the same irreducible h̄; map generator to generator),
which carries O onto O′ (integral closures correspond;
`IsIntegralClosure.equiv`) and m_O onto m_{O′}, hence eOf D = eOf D′ and
fOf D = fOf D′. Equivalently: (LF-1)(i)'s UNIQUENESS clause. If any future
consumer (e.g. a seam between `bridgeZfType` and the OM-side `qpType`, whose
`om_leaf_faithful` instances carry their OWN bundles) needs two readings to
agree, this must be added as a lemma — derivable from the citation but NOT
free in Lean at the pin. Record in the faithfulness entry.

### 4.4 W2 — dispatch-locus design for the repaired total functions

The repaired `MovesT.ramIdx`/`resDeg` stay total with junk 0 off a decidable-
by-choice guard. Faithfulness constraint: the guard must be EXACTLY
inhabitation (`Nonempty (LocalFactorData p h)`) or a predicate implied by the
axiom's hypotheses on the consumed locus (monic ∧ irreducible image), so that
every read the zf laws perform is a real (LF-1) read. A guard that can fire
on non-irreducible h (e.g. bare `IsLocalRing (AdjoinRoot h)` — the OLD guard)
re-imports the †11f order-vs-field confusion. The E0 countermodel already
compiled that lesson (`e0_no_zpBridge`); the repair must not reintroduce it
at the new defs.

### 4.5 W3 — the re-point IMPROVES an adjacent cite

`MovesT.OmSat` (the Ore–Montes certificate row) asserts `ramIdx fη = accE H ∧
resDeg fη = accF H` as a GMN citation. GMN's e(L/K), f(L/K) are the FIELD
invariants; at the old order-level defs the cite row claimed something GMN
does not say (and which is false, by †11f). After the re-point the row reads
the invariants GMN actually computes. The faithfulness ledger for the GMN
axiom should note this scope correction.

## 5. Derivability of (L1)–(L3) at the pin from the axiom — verified inventory

All names/locations grep-verified in the PINNED Mathlib
(`lean/.lake/packages/mathlib`). R := ℤ_[p], S := D.O, K := ℚ_[p], L := D.L,
p := maximalIdeal ℤ_[p], P := maximalIdeal D.O, for D the chosen bundle of a
factor h (monic, irreducible image — supplied by the PROVED
`monicFactors_monic`/`monicFactors_natDegree_pos`/`monic_irreducible_map_coe`).

Shared instance chain (once per bundle):
1. `FiniteDimensional ℚ_[p] L` — `FiniteDimensional.of_finrank_pos`
   (`Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:141`) from
   `finrank_eq` + deg h ≥ 1.
2. `Algebra.IsSeparable ℚ_[p] L` — `Algebra.IsSeparable.of_integral`
   (`Mathlib/FieldTheory/Separable.lean:670`; CharZero ℚ_[p]).
3. `IsNoetherian ℤ_[p] O`, hence `Module.Finite ℤ_[p] O` —
   `IsIntegralClosure.isNoetherian`
   (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:151`;
   ℤ_[p] is Noetherian + integrally closed: PID/UFD instances at the pin).
4. `IsFractionRing O L` — `IsIntegralClosure.isFractionRing_of_finite_extension`
   (`Mathlib/RingTheory/Localization/Integral.lean:399`).
5. `IsDedekindDomain O` and `IsDedekindDomain ℤ_[p]` —
   `IsPrincipalIdealRing.isDedekindDomain`
   (`Mathlib/RingTheory/DedekindDomain/Basic.lean:171`; DVR ⟹ PID).
6. `(maximalIdeal ℤ_[p]).IsMaximal` (instance) and `maximalIdeal ℤ_[p] ≠ ⊥`
   (ℤ_p is not a field — p is a nonzero nonunit): routine.

- **(L2) pointwise:** `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
  (`Mathlib/NumberTheory/RamificationInertia/Basic.lean:650`) with 1–6 +
  `[IsLocalRing O]` (DVR) gives e·f = finrank ℚ_[p] L; rewrite by
  `finrank_eq`. This is Mathlib's own Σeᵢfᵢ = n specialized to a local S —
  i.e. (LF-2) re-proved from the axiom + pinned Dedekind theory.
- **(L1) zf_pos:** e ≠ 0 — `Ideal.ramificationIdx_ne_zero_of_liesOver`
  (`…/RamificationInertia/Ramification.lean:253`, or the
  `IsDedekindDomain.…_of_liesOver` form used inside Basic.lean:625) with the
  bundle's `liesOver` + `maximalIdeal ℤ_[p] ≠ ⊥`. f ≠ 0 —
  `Ideal.inertiaDeg_ne_zero` (`…/RamificationInertia/Inertia.lean:98`;
  hypotheses `[p.IsMaximal] [Module.Finite R S] [P.LiesOver p]`, all
  supplied). Alternatively (L1) follows from (L2) + deg h ≥ 1 + Nat facts.
- **(L3) zf_factor:** witnesses := `monicFactors g` (proved corpus, brief
  §5.1). Conjunct 1: `monicFactors_prod` + `Polynomial.map_multiset_prod`.
  Conjunct 2: `monicFactors_monic` + `monic_irreducible_map_coe`. Conjunct 3:
  definitional at the repaired defs (`zfType := bridgeZfType`). Conjunct 4:
  conjunct 3 + (L2) + `Multiset.map_map`/`Multiset.map_congr`. Degree side
  condition Σ deg h_i = n (needed by the `SplittingType` consumers, not by
  `zf_factor` itself): `natDegree_multiset_prod` of monic factors.

So the FULL zf package is: one axiom instance per irreducible factor +
routine pinned-Mathlib assembly. No second axiom, no strengthening of
(LF-1)/(LF-2), is required. (This is the sense in which the obligation is
LITERATURE: the only conditionality is (LF-1)(i).)

## 6. Reduction remark: the axiom itself is plausibly dischargeable at the pin

Not executed; recorded because it would DELETE the conditionality rather than
cite it. The corpus's IP-1 proof (`BridgeZp.lean`, `ip1_holds`) already
machine-checks the schema "finite torsion-free ℤ_p-algebra + domain ⟹ local"
via: freeness over the PID, adic-completeness transfer along coordinates
(general proved helpers `isAdicComplete_of_linearEquiv`,
`isAdicComplete_pi_of_fintype`), `IsAdicComplete.henselianRing`
(`Mathlib/RingTheory/Henselian.lean:170`), finite (hence Artinian) residue
ring, the proved two-maximal-ideals-give-an-idempotent factory, Hensel-lift
along X² − X, and domain-kills-idempotents. Replaying it at O :=
integralClosure ℤ_[p] L (module-finite by §5 item 3, free by
`Module.free_of_finite_type_torsion_free'`
(`Mathlib/LinearAlgebra/FreeModule/PID.lean:386`), domain as a subring of L)
yields `IsLocalRing O`; then `IsIntegralClosure.isDedekindDomain`
(`…/DedekindDomain/IntegralClosure.lean:219`) + local + not-a-field (p is a
nonunit in O: p⁻¹ would be integral over ℤ_p inside ℚ_p, hence in ℤ_p) gives
DVR via the local-Dedekind leg of `IsDiscreteValuationRing.TFAE`
(`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean:210`). Every named piece
exists at the pin or in the corpus; the open cost is glue (~300–500 lines).
Mathematically this is (LF-1)(i) for char-0 K with the completeness used only
through henselian-ness — a standard proof (label (b): new machine proof of a
known result). DECISION POINT for the orchestrator: declare the axiom now
(unblocks group E immediately; goal-compatible) and queue this discharge as a
follow-up unit that would retire it.

## 7. VERDICT

VERDICT: **LITERATURE** — the single literature-conditioned content of the
M16 zf laws is (LF-1)(i) (integral closure of ℤ_p in a finite extension of
ℚ_p is a DVR; Serre, Local Fields, Ch. II §2 — proposition number to be
page-verified at declaration), correctly captured by
`Nonempty (LocalFactorData p h)` guarded by monic + ℚ_p-irreducible-image;
the guard is load-bearing (unguarded form REFUTED, §4.1); zf_pos, pointwise
e·f = deg, and the zf_factor assembly are then derivable at the pinned
Mathlib via the verified inventory of §5; secondary: the axiom is plausibly
dischargeable at the pin (§6, reduction recorded).

## 8. NUMERIC-TESTS

Environment: the cypari2 env referenced by `verification/quartic_oracle.py`
(`/workspace-vast/asving/envs/padic/bin/python`) is NOT present on this box;
`gp` (PARI/GP 2.17.4, `~/.local/bin/gp`) is, and suffices — the protocol
below is pure PARI. ⚠ Do NOT reuse the oracle's `_ef_of_factor` selector for
these tests: it picks the prime by `e·f == d`, which PRESUPPOSES (L2). Use
the non-circular protocol below.

**SMOKE-TEST EXECUTED (this session, gp 2.17.4; script pattern in the test
descriptions):** T3 all five (p,c) pairs → (e,f) = (1,2), as predicted;
mini-T1 (p ∈ {2,3,5}, n ∈ {2..5}, 15 random g each; 325 factors checked) →
0 locality violations, 0 pointwise violations, all aggregates = n, 18 wild
(p | e) factors exercised; T2 spot: X⁴+2 → (4,1), X⁸+2 → (8,1) at p=2,
X⁹+3 → (9,1) at p=3, X²+2X+2 → (2,1); T5 spot (`padicfields(p,n,1)`, entry
format `[pol,e,f,d,c]`): 0 violations of e·f = n over (2,4),(3,3),(5,4),
(7,6) — 59/10/7/12 extensions respectively. The full-scale runs below remain
for the numerics fleet.

**T1 — locality + pointwise law, random sweep (tests L0's key content and
L2/L1).** For p ∈ {2,3,5,7,11,13}, n ∈ {2,…,8}, ≥200 random monic g ∈ ℤ[x]
per (p,n) with coefficients uniform in [−p⁴, p⁴]:
`fac = pari.factorpadic(g, p, 60)`; for each factor h of degree d ≥ 2:
G = `pari.liftall(h)` (monic ℤ-lift agreeing mod p^60);
(a) check `pari.factorpadic(G, p, 60)` is a single irreducible factor of
degree d (Krasner-closeness gate; on failure raise precision, do not skip);
(b) `dec = pari.idealprimedec(pari.nfinit([G,[p]]), p)`; ASSERT `len(dec) ==
1` — this is the numerical shadow of (LF-1)(i)/the axiom: ONE prime above p
in the root field ⟺ the integral closure is local;
(c) ASSERT `e·f == d` for that unique prime (pr[2], pr[3]) — (L2);
(d) ASSERT e ≥ 1, f ≥ 1 — (L1).
Per g: ASSERT Σ over all factors (counting linear factors as (1,1)) of
e_i·f_i == n — zf_factor conjunct 4 + the SplittingType sum law.
CONFIRMS: zero violations. REFUTES: any (b) failure refutes the axiom's
transcription (or Krasner precision — distinguished by (a)); any (c) failure
at a passing (b) refutes (L2) as transcribed.

**T2 — wild stress (the locus the old Mathlib wall blocked).** Same checks on
structured families: Eisenstein X^n − p·u (u ∈ {1,…,p−1}); X^n − p^k·c with
1 ≤ k ≤ n, c a unit; p = 2 with n ∈ {2,4,8}: X²+2X+2, X⁴+2, X⁸+2, and
(x+1)-recentered variants; p = 3, n = 9: X⁹ + 3c. Expected: all pass; e
divisible by p occurs (log it — confirms the wild locus was actually
exercised).

**T3 — the †11f countermodel semantics (confirms the re-point target).** For
p ∈ {3,5,7,13} and c a non-residue unit mod p (at p=2: c ≡ 5 mod 8), h = X² −
p²c: T1's protocol must yield (e,f) = (1,2) — the FIELD invariants — while
the retired order-level defs provably read (1,1) (`e0_ramIdx`/`e0_resDeg`,
compiled at p=3). Confirms the countermodel's semantic claim numerically and
at more primes than the compiled p = 3 instance.

**T4 — cross-bundle invariance (W1, §4.3).** For each factor h in a T1/T2
sample, recompute (e,f) from a SECOND Krasner lift G′ = G + p^{55}·x^{d−1}
(re-checking gate (a)); ASSERT the same (e,f). Numerical shadow of the
uniqueness clause / bundle-independence.

**T5 — PARI-internal cross-check.** For n ≤ 6, p ≤ 7: `pari.padicfields(p,n)`
lists all degree-n extensions as (e,f,j)-triples; ASSERT every listed triple
has e·f = n and every (e,f) observed in T1/T2 at degree n occurs in the list.
Guards against a systematic idealprimedec misreading.
