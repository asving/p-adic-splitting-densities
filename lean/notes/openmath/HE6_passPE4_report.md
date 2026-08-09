# HE6 passPE4 — FABLE HOSTILE VERIFIER (fresh context) — THE ACCEPTANCE ATTEMPT

**VERDICT: CLEAN — 0 CRITICAL / 0 GAP / 2 MINOR on the target. Grade 1/2 → 2/2 —
HE6 IS ACCEPTED. The text freezes; dated appends only (two MINOR queue items
below land as dated appends at the owner's discretion, not as blockers).**

**Target:** `HE6_PROOF_2026-08-08.md` + `HE6R1_RECON_2026-08-08.md` at HEAD
(git-verified this pass: ZERO diffs 9f02ad4 → HEAD on both target files — the
text graded here is byte-identical to what PE3 graded CLEAN). Arc: seal
a77c376 → close 1f5a417 → Codex PE1 06f55f0 → r1 850e77e → PE2 404dae1
(0C+2G+3m) → r2 (8797a34/9bdfbb5/cec49ba/d1b0bc8) → PE3 CLEAN 0/0/0 9f02ad4
(counter 1/2) → **this pass (PE4, the 2/2 attempt)**. Protocol:
quote-and-classify, fix nothing. Charged surfaces, all executed: (1) the
DEFINITIONS layer (DEFINITION HE6-1 + the point-set definitions — the trust
boundary no pass had made its main target); (2) the middle lemmas
(HE6-2/HE6-2′/HE6-0′/HE6-2″ — the least-visited of the lemma list); (3) the
reconciliation note's own status at HEAD vs HE7's frozen consumers; (4) the
disclosed arc-wide gap — the non-prime-q BASE oracle leg, never run in this
arc — RUN (§S3); (5) free hunt across both files and the artifacts.

---

## S1. FINDINGS (2 MINOR; nothing GAP-or-worse survives)

### F-1 (MINOR — §S9 record, fresh): the headline "1,385 members over six rows" is not derivable from the committed artifacts

> Quoted (HE6 §S9, L897–899): "**2,226 PARI σ jobs** · 1,385 members over six
> rows (ℤ_3/ℤ_5/ℤ_7 at λ = 5/2, ℤ_5 at λ = 7/2, F_3[[t]] and F_5[[t]] at
> λ = 5/2)."

The committed `he6_checks_results.json` records 18 config-rows with member
counts 209/299/185/157/79/57 per row, IDENTICAL across the three configs of
each row (member_counts grid: 209 of 625, 299 of 6561, 185 of 2401, 157 of
625, 79 of 625, 57 of 625). The natural aggregations are **986** (unique
perturbation members per row, summed over six rows) and **2,958** (config
member instances, 3 × 986); the per-row values in §S9's own Q3 table (209 /
299 / 185 / 157 / 79 / 57) match the json exactly. **No natural aggregation
equals 1,385** (an exhaustive subset-sum over the 18 config counts finds only
meaningless ≥7-element subsets). Every OTHER §S9 total was re-verified
against the artifacts this pass: 72,315 GEN (also re-derived arithmetically:
Σ members × tests/member = 209·3·15 + 299·3·24 + 185·3·37 + 157·3·28 +
79·3·15 + 57·3·24 = 64,656 + 7,659 = 72,315 ✓), 4,232 SEP, 2,226 SIG
(= 742·3 ✓, per-config PARI capped at 200 ✓), 24 XI, 6 ORTH, all teeth.
The 1,385 was audited by NO prior pass (PE2's "totals equal the committed
json field-for-field" covered the legs fields; PE3 re-verified the F-2
record-repair facts; the figure appears exactly once in the corpus).
**Failure scenario:** an auditor reconciling §S9's member headline against
the committed json cannot derive it under any reading and must treat that
sentence as failing the count audit — while every load-bearing total passes.
**Classification MINOR:** zero consumers (no theorem, leg, tooth or
downstream note reads the figure); artifacts authoritative and reproduced by
isolated re-run; same family as PE2's F-4 (record overstatement), strictly
below PE2's F-2 (no pin, no provenance implication). Queue: one dated append
correcting the sentence (to the json's 986 unique / 2,958 config-instances,
whichever was meant).

### F-2 (MINOR — LEMMA HE6-2's statement, fresh): the β-definedness guard is broader than β's domain of definition

> Quoted (HE6 §S1, LEMMA HE6-2): "Let ξ be any (T1)/(T2) point,
> δ := dv(Φ′(ξ)), and — when δ has denominator dividing ℓ —
> β := res(Φ′(ξ)^ℓ/ϖ(ξ)^u)."

The guard admits δ with ℓδ ∈ ℤ but ℓδ ≠ u, where the displayed element is
not a unit: at ℓδ > u the residue is 0, at ℓδ < u the element is not
integral and `res` is undefined (e.g. δ = 2 ∈ ℤ, κ = 5/2, ℓ = 2, u = 5:
dv = −1). The defining condition for β should be δ = κ. **No consumer is
affected** (checked at the sites): the lemma's own dichotomy "ε(ξ) > 0 ⟺
δ = κ and ι_ξ(r)(β) = 0" consults β only under its first conjunct δ = κ,
where β is a unit residue; HE6-3/HE6-4/HE6.A read ε through that dichotomy
only; and even an unguarded β = 0 read cannot create a spurious ε > 0
because r(0) ≠ 0 forces ι_ξ(r)(0) ≠ 0. **Failure scenario:** a reader
instantiating β from the statement alone at δ ≠ κ gets an undefined or zero
read; no statement of the note or of HE7/recon consumes that reading.
Classification MINOR (definitional looseness, zero consumers, conclusion
unaffected).

**Out-of-scope observations (round-dated statements overtaken by favorable
events; not findings):** (obs-a) the recon R3 row [r2]'s parenthetical "does
not soften HE7's own fold-box 'verbatim' sentence (an HE7-side residue,
noted here)" is discharged at HEAD — HE7's dated line db0001a (post-PE3)
scoped the fold box, and 07dfbb7 landed PE3's obs-1 res(·) form; (obs-b) HE6
§S7.2's "Both suppliers are at attempt grade 0/2" and HE6-BOX-2/HE6R1-BOX-1's
supplier-grade lists are r1/r2-dated — at HEAD HE7 is ACCEPTED 2/2 (its r1
text folds in HE6R1-F1/F2 and consumes LEMMA HE6R1-1/2/3), which STRENGTHENS
the composition claim those boxes conditionalize; (obs-c) the grade box's
"PE3 next" is r2-dated; PE3 since ran CLEAN (9f02ad4).

---

## S2. CLEAN CHARGES (what was attacked and held)

1. **DEFINITIONS layer (charge 1) — audited item by item, held.**
   DEFINITION HE6-1: degree bookkeeping (deg B_tΦ′^{ℓt} ≤ D′(1+ℓd−ℓ) < D′ℓd
   incl. the ℓ = 1 equality corner); every lift height k = (d−t)u ≥ u >
   ℓD′h ≥ D′h > (D′−1)h so only HE6-1L's fullness clause is consumed —
   coset-invariant under the [r2] η^{−q(k)} factor; the B_t = 0 (c_t = 0)
   convention against the R8 nonzero-terms rider; r monic irreducible with
   r(0) ≠ 0 pins both endpoints; Ψ_{κ,r} is a CHOICE (lifts not unique) and
   each consumer (HE6-1/2, HE6-3/4's instruments) was checked to use only
   dv/residue data, choice-independently. Point-set definitions: S_{λ,r}
   well-defined via COROLLARY HE6-2″ (β_ρ a unit at λ_ρ; r_ρ = the minimal
   polynomial, divides R_λ); n_λ counts simple roots (disc f ≠ 0); R_λ's
   zero-coefficient convention (pins strictly above the λ-line ↦ 0) coherent
   at both endpoints (left endpoint a hull vertex ⟹ R_λ(0) ≠ 0); the ϖ
   convention (dv(ϖ(ξ)) = 1 exact needs only (T1)); the i₀-vs-i₀(k) symbol
   overload resolved by the RIDER's two equations (re-derived: q =
   (i₀k − i₀(k))/e₁ ∈ ℤ_{≥0}). Machine corroboration: this pass's fresh
   reader (§S3) rebuilt DEFINITION HE6-1 and the §S1 residual convention
   independently over a NON-PRIME base and matched PARI 60/60 — including
   FROBSPLIT members whose middle pin sits strictly ABOVE the line, the
   zero-coefficient convention exercised live for the first time in this arc.
2. **Middle lemmas (charge 2) — the least-visited four re-derived, held.**
   LEMMA HE6-2: the three-case minimum analysis over nonzero terms (endpoints
   always nonzero), the tie-residue sum Σι_ξ(c_t)β^t = ι_ξ(r)(β), residue
   transport exact BECAUSE the [r2] twist is an η-power (ι_ξ(η_θ) = η_ξ
   transports it, so res at ξ = ι_ξ(res at θ) with the twist absorbed), the
   label clause via minimal-polynomial uniqueness, and the extended-value
   reading at δ = ∞ (ξ = θ: both sides give du, consistent) and at shared
   roots (ε = ∞ ⟹ membership in S — HE6-4's nonemptiness survives). LEMMA
   HE6-2′: the mod-ℓ congruence of attaining pins (gcd(u,ℓ) = 1 +
   integrality), the division exponents (j₁κ + m₁ = h_F(κ); k_t = m₁ − tu ≥
   m₂ ≥ 0), above-line pins contributing residue 0 = R_λ's convention.
   LEMMA HE6-0′: e₁ℓ | e via the value group (two gcd steps), f₁d_r | f via
   η_ρ, β_ρ ∈ k_{L_ρ}, e·f = [L:K₀] over a complete DVR with finite residue
   field, and — char-p — orbit size = [L_ρ:K₀] from separability (disc
   f ≠ 0 doing double duty). COROLLARY HE6-2″: κ := λ_ρ finite by the §S1
   Φ′ ∤ f CONVENTION. Also re-derived, because the recon's LEMMA HE6R1-2(a)
   consumes it: HE6-3/HE6-4 apply to a monic divisor g | f with all roots
   (T1)/(T2) — deg g ≡ 0 (mod D′) via HE6-0′, and the zero-slope corner of
   HE6-3(a)-for-g closes by the total count Σ_λ n_λ = D′μ_g forcing
   Σ_{λ>D′h} L_λ = μ_g = Σ_{all λ} L_λ.
3. **The recon at HEAD vs HE7's frozen consumers (charge 3) — NO DAYLIGHT.**
   Git-verified: the ONLY post-r1 change to the recon is the R3 row [r2]
   (one line replaced by one line — §S3.3/S3.4/S3.4b line numbers stable);
   LEMMA HE6R1-1/2/3's statements are byte-untouched since r1, which is the
   text HE7's ACCEPTANCE consumed (HE7's r1 text carries HE6R1-F1/F2 at [r1]
   sites — the Ψ ∤ f_S CONVENTION, the widened trichotomy — and names LEMMA
   HE6R1-1/2/3 as consumed; the Codex HE7 ratification pasted recon lines
   226–410). HE7 append-only re-verified independently: first 158,362 bytes
   at HEAD md5 0698155b… = the [r2] correction record's prefix pin; the two
   post-PE3 dated lines (db0001a, 07dfbb7) are appends. The recon's §S3.2
   item 2 and HE7's own [r1] use-site check (§S4.3: every level-1 call at
   m_t > λ > (D′−1)h with margin > h) agree — fullness only, the [r2] coset
   factor invisible. HE6R1-1's descent displays re-derived (n_λ = D′L_λ by
   (SEP)-free HE6-3(b) load-bearing at the repeated node; 4 ≤ μ_J ≤
   μ/2^{J−1} ⟹ J ≤ log₂μ − 1); HE6R1-2(a)/(b)/(c) re-derived under attack
   (the r ∤ R_λ^{(g)} contradiction via HE6-4-for-g; the constant-difference
   breakpoint argument on (T₂,∞); radical equality via ι-transport of
   divisibility); HE6R1-3's Galois-orbit forcing (deg g₀ = D″ ⟹ Ψ
   irreducible, e = e₁ℓ, f = f₁d_r) re-derived.
4. **The [r2] non-propagation inventory — COMPLETED at-site across the arc.**
   Routes (5) and (6), the two PE3 explicitly did not re-walk, verified at
   their HE7 sites this pass: (5) §S4.2's W₁/W₂ sharpness display consumes
   fullness/emptiness only and its sub-threshold sentence ("a proper
   subgroup-coset of K₂ is reached, or the height is not attained") is
   already coset-correct; (6) tooth HE7-T-LIFT2SHARP's predicates (W1_set /
   W2_set / V1_set in `he7_checks.py` L375–415) are slot-availability counts
   and onto-ness checks — invariant under any coset translate. Combined with
   PE2's original 8-route trace and PE3's at-site verification of (1), (4),
   (7), (8), the eight-route inventory has now been at-site verified within
   this arc.
5. **Free hunt (charge 5) — items that held:** §S2's first-bite arithmetic
   (μ ≥ 4, n ≥ 8, q-thresholds, both σ predictions); HE6-3's (†)/(★)
   derivation incl. the c₀ elimination and the gap-sampling telescope;
   THEOREM HE6.A's sandwich steps 1–4 (partition under separability; orbit
   lower bound; e·f forcing); LEMMA HE6-5's two transport displays; §S6.5's
   two branch verdicts; §S7.3's local layout pin (the FGMN layout file
   exists, 150,185 bytes); the §S1 CONVENTION's peel display; the header's
   [r2] freeze-anchor sentence (runner + artifact md5s at HEAD = 1f5a417
   values, re-computed). The §S9 Q3 table's internal arithmetic (row sums,
   ALPHA2 three-σ splits, 742 = 4-row SPLIT PARI total) all reconcile — the
   ONE number that does not is F-1.

---

## S3. MACHINE + FRESH-ROUTE LEGS (this pass's instruments)

**Isolated re-runs (sandbox /tmp/he6pe4_iso, import-closure copy, md5s
verified before launch = HEAD: he6_checks.py 321fa4d4990e, he6r1_checks.py
7112f7c738ed, he6r1_supp.py 79da51dcd405):**
* `he6_checks.py`: exit 0, **0 violations**, legs 72,315 GEN / 4,232 SEP /
  2,226 SIG / 24 XI / 6 ORTH, **5/5 teeth fired**, 195.2 s; output
  byte-identical to the committed artifact except ONE timing line and the
  presence-conditional pins line (sandbox carried the import closure only;
  he3_checks.py/json pins print only when present — PE3's identical
  disclosed difference).
* `he6r1_checks.py --full`: exit 0; results json identical to the committed
  artifact except `secs` and per-row `secs` on 3 rows; the **21 sealed,
  disclosed exceptions reproduced exactly** (4 SEP2 leg-construction
  artifacts + 12 Ψ | f_S BADTOTAL non-decisions + 5 PARI non-agreement
  flags — the recon §S6's accounting); teeth 5/5; import pins in the
  artifact match HEAD md5s. *Verifier-side environment slip, disclosed: the
  first sandbox run crashed AFTER 0 violations at the PINS dictcomp
  (he7_checks.py is a pin, not an import, and was not copied); re-run with
  the pinned file present, exit 0.*
* `he6r1_supp.py`: exit 0, json identical field-for-field (peel 12/12
  decided, 5/5 PARI agree; refine 4/4 strict).

**Fresh route (`verification/openmath/he6_pe4_fresh.py` + output + json;
md5s 5e675cbcb37e / 0ab93745a9b3 / c9fd905b5ca7; committed b99f6b0; exit 0,
1.4 s, 0 violations, first full run): THE FIRST NON-PRIME-q BASE ORACLE LEG
OF THE ARC** — the coverage hole PE2 and PE3 both disclosed (every prior σ
leg had a prime base; PE3's f₁ = 3 leg reached non-prime RESIDUE fields but
not a non-prime base).
* **Frames:** base F = ℚ(w)/(w²−d) with p INERT — (d,p) = (−1,3) (local base
  ℚ_9, F_Q = F_9) and (2,5) (ℚ_25, F_Q = F_25); Z[w] p-maximal, v_P exact;
  Φ′ = x²−p Eisenstein: (e₁,f₁,h) = (2,1,1), η = 1 (twist-free), μ = 4,
  deg f = 8, λ = 5/2, pins (0,10)–(2,5)–(4,0).
* **Configs × 10 members each (base + 9 strictly-above-line perturbations, 4
  with w-components) per frame:** FROBSPLIT R = (Z−w̄)(Z−w̄^p) — a Frobenius
  PAIR over the prime field, irreducible over F_p but split over F_{p²}, the
  sharpest base-field discriminator; SPLITMIX R = (Z−1)(Z−w̄); INERT2
  R = Z²+aZ+b brute-verified rootless over F_{p²} with b ∉ F_p. Reader
  re-derives development/hull/R_λ from raw expanded coefficients + gcd
  separability check on every member.
* **Oracle (decorrelated from every prior leg):** nffactor over F +
  rnfequation + nfinit([abs,[p]]) + idealprimedec; relative invariants
  e(Q|P) = e(Q|p), f(Q|P) = f(Q|p)/2 (parity asserted; Σ e·f_rel = 8
  asserted; no linear factors asserted).
* **Results:** σ_rel = THEOREM HE6.A's dictionary **60/60** (FROBSPLIT +
  SPLITMIX {(4,1),(4,1)} 40/40; INERT2 {(4,2)} 20/20), invariant under all
  perturbations; flat identities over the non-prime base EXACT
  (2v_P(Res(f,Ψ_{5/2,r₃})) = 120 with a generic cubic letter over F_{p²};
  2v_P(Res(f,Ψ_{3,Z−1})) = 20 at a non-slope height) + strict excess at
  every label (> 40 split, > 80 inert) — the first P1/P2-analogues over a
  non-prime base.
* **Teeth 3/3 fired:** **T-BASEFIELD** — the 5 all-integer FROBSPLIT members
  per frame scored over BOTH bases: the SAME BYTES give {(4,2)} over ℚ_p and
  {(4,1),(4,1)} over the unramified base, 10/10 (kills "re-labeled
  prime-base computation" and kills a reader consulting the prime residue
  field — over F_p the FROBSPLIT residual is irreducible and would
  mispredict); **T-PLANTDICT** — planted {(8,1)} refuted 40/40;
  **T-BADPERT** — a deliberately ON-line perturbation (changing R_λ's middle
  coefficient to a repeated-root residual) is caught by the reader. Smoke
  record disclosed in the docstring (one reader predicate relaxed to the
  note's actual above-line convention before any oracle comparison; no
  prediction or tooth changed at any point).
* **What the fresh leg establishes for the acceptance question:** the
  charged trust boundary — DEFINITION HE6-1 and the §S1 residual
  convention — was rebuilt from the note's text alone by a hostile party in
  a frame class the arc had never exercised (q non-prime AT THE BASE,
  labels in F_{p²} ∖ F_p, Frobenius-pair labels that are base-rational),
  and THEOREM HE6.A's dictionary held against an independent oracle with the
  base field demonstrably load-bearing.

---

## S4. GRADE LINE

**CLEAN under the charge bar: nothing at GAP-or-worse survives this pass on
the two target files (2 MINOR: F-1 the §S9 member headline, F-2 the HE6-2
β-guard — both zero-consumer, both queued as dated appends). HE6-BOX-2
counter: 1/2 → 2/2 — HE6 IS ACCEPTED; the text freezes, dated appends only.**
The five charged surfaces were executed: the definitions layer and the
least-visited middle lemmas held under re-derivation and under a fresh
machine rebuild in a never-exercised frame class; the recon's consumed lemma
statements are byte-stable since the r1 landing that HE7's accepted text
consumes; the disclosed non-prime-q BASE coverage hole is CLOSED by this
pass's exact leg (60/60 dictionary, dual-base disagreement 10/10); the
sealed instruments reproduce their committed verdicts in isolation (three
re-runs, pins verified). Composition note for the chain: with HE7 ACCEPTED
2/2 and this acceptance, THEOREM HE6.A and COROLLARY HE6.B [r1] stand at
2-clean with their conditionality boxes as displayed (HE6-BOX-1 discharged
via HE7 + recon; supplier grades per the round-dated boxes, GENHN's own arc
proceeding in parallel).

*Verifier: Fable (fresh context, zero prior stake), 2026-08-09. Artifacts:
`verification/openmath/he6_pe4_fresh.py`, `he6_pe4_fresh_output.txt`,
`he6_pe4_fresh_results.json` (commit b99f6b0); isolated-re-run sandbox
/tmp/he6pe4_iso (ephemeral; md5 comparisons recorded above).*
