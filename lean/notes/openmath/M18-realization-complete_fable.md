# M18-realization-complete — Attempt (Fable)

Companion to `M18-realization-complete_brief.md` (all notation, Lean quotes,
law roster, and intended-instance semantics live there; §-references of the
form B§n point into the brief). Date: 2026-07-31.

## 0. Summary of results

- **Theorem 0** (§1): unconditional `RealizationComplete` is REFUTED
  outright — the recorded census-coupled toy `HmcToy.TE` itself violates
  it. New compiled theorem `not_realizationComplete_toy` (machine-checked
  against HEAD, Lean-core axioms), strengthening the corpus' recorded
  ∃-shape `coupling_signature` to a direct negation.
- **Theorem A** (§3): `RealizationComplete` is PROVED from ONE added
  one-step law, `MarkGraft` (§2), together with the standing length-1
  surjectivity laws. Compiled, Lean-core.
- **Theorem B** (§4): conversely `RealizationComplete ⟹ MarkGraft` — the
  reduction is LOSSLESS: `MarkGraft` is exactly the composite-template
  content of the row, no more. Compiled, Lean-core.
- **Theorem C** (§5): `RealizationComplete` ⟺ the counting tie
  T_γ = T̂_γ (all γ, h, over pools at zc histories), given the standing
  injectivity law. Compiled, Lean-core. This gives the numerically testable
  form and a second, cardinality-shaped discharge route.
- **Instance analysis** (§6): at the intended p-adic semantics (B§5),
  `MarkGraft` is bookkeeping, NOT new existence content: a mark of the tail
  template at the a-extended history is already a full realization of the
  composite; grafting re-indexes the same marked pair (f, η). All genuine
  existence content of `RealizationComplete` is confined by Theorem A to
  length 1, where it is the already-standing law `tmark_last_surj`. The
  named instance duties (I0)–(I3) under which this becomes a proof are
  displayed, each with its source-note warrant.
- Verdict: **REDUCED** (see the VERDICT line at the end).

Status labels: Theorems 0, A, B, C are (c) claimed new, machine-checked in
a scratch module against HEAD (not yet landed in a repo file; full source
displayed in §7 for verbatim landing). The §6 instance analysis is (c)
claimed-new analysis, conditional on the displayed duties — the instance is
not on disk (B§6), so nothing there is certified. No literature match: the
structures are project-specific transcriptions (B§2), and the mathematical
content at the instance is the note's own C.1.5/D4R.4 layer, not an
external citation. NOT literature-axiom-eligible.

## 1. Theorem 0 — the bare row is false (compiled)

**Theorem 0.** `¬ RealizationComplete HmcToy.TE`.

*Proof (as compiled).* Take the composite template γ = cons(mv, last mv) at
the toy's unique cell, q₀ = 2 ∈ Pools, any history x (zc ≡ true), and the
ZERO height point h = 0 ∈ ℕ². The toy's composite census at h = 0 is empty
(`census(cons …)(x, 0) = 0`), so tinst(γ, x, 0, ℓ(γ)) = ∅. But
Chains(γ, x, 0) is inhabited (`HmcToy.chainDefault`; indeed T̂ = 4 there,
`coupling_signature`). A surjection from the empty subtype onto an
inhabited type yields, applied to the default chain, a member b of the
empty census — and its membership proof contradicts the census bound
0 ≤ (b : ℕ) < 0. ∎

Consequences. (i) No proof of the row can proceed from the standing
`TmplEvents` + `XHDd` laws — the toy satisfies all of them (B§4.4). (ii)
Any discharge must consume instance structure; the minimal such structure
is isolated in §2. (iii) The toy also pins where the failure lives: its
composite censuses are decoupled from its step layer — exactly the freedom
the standing laws leave open (the `CompProduct` diagnosis, B§4.5).

## 2. The added row: one-step mark grafting

**Definition (MarkGraft).** For a marked-event carrier TE over a step
system S: for every continuing move m : α → β, every template γ from β,
every pool element q₀, every zc history x ∈ Hist(q₀, α), every height
point h of cons(m, γ) (split h = (h₁, h′)), every fresh assignment
a ∈ Assign(m, x, h₁), and every counted tail mark
b′ ∈ tinst(γ, ext(x, a), h′, ℓ(γ)): there exists a counted composite mark
b ∈ tinst(cons(m, γ), x, h, ℓ(cons(m, γ))) whose reading is the paired
chain:

  tmark(cons(m, γ), x, h)(b) = ⟨a, tmark(γ, ext(x, a), h′)(b′)⟩.

In Lean (compiled form, §7): `MarkGraft TE`. Three sanity checks:

- *Content check against the countermodel:* `HmcToy.TE` violates
  `MarkGraft` (as it must, by Theorems 0 + A). Directly: at h = 0 the
  head assignment set is nonempty and the tail census (a length-1 census,
  = 2) is nonempty, but the composite census at 0 is empty — no b exists.
- *Locality:* `MarkGraft` mentions ONE composite constructor application;
  no recursion, no quantification over all templates' internals beyond the
  tail as a black box. It is a law of the same genre as the standing
  length-1 ties — a candidate `TmplEvents`-adjacent named row.
- *No domain content:* `MarkGraft` never mentions dom(γ), and it holds at
  the full-census witness toy `witTE` (B§4.3) where HMC holds, while
  implying nothing about domain factorization: the height point h is FIXED
  throughout — no coupling across height coordinates is asserted or
  needed. In particular the reduction does NOT smuggle in the open kernel
  HMC (B§4.4's bracket): HMC constrains which h lie in dom(cons(m,γ)) as a
  product; `MarkGraft` constrains census-vs-chain surjectivity at each h
  separately. (`witTE` satisfies both; `HmcToy` fails both; the two
  properties still concern disjoint data — domains vs. mark readings.)

## 3. Theorem A — MarkGraft discharges the row (compiled)

**Theorem A.** For any TE satisfying the standing laws:
`MarkGraft TE → RealizationComplete TE`.

*Proof.* Induction on the template γ (the motive quantifies over q₀, x, h
and the guards; α rides as the index of the inductive family).

- γ = last m: surjectivity of tmark(last m, x, h) is the standing law
  `tmark_last_surj` at the guards (q₀ ∈ Pools, zc x).
- γ = lastT m: likewise `tmark_lastT_surj`.
- γ = cons(m, γ′): let c ∈ Chains(cons(m, γ′), x, h). By the Σ-shape of the
  chain carrier (B§2.2), c = ⟨a, c′⟩ with a ∈ Assign(m, x, h₁) and
  c′ ∈ Chains(γ′, ext(x, a), h′). The extended history ext(x, a) is zc by
  the standing step-system law `ext_zc`, and q₀ is unchanged; so the
  induction hypothesis (surjectivity for γ′ at ext(x, a), h′) yields a
  counted tail mark b′ with tmark(γ′, ext(x, a), h′)(b′) = c′. `MarkGraft`
  at (m, γ′, x, h, a, b′) yields a counted composite mark b with
  tmark(b) = ⟨a, tmark(b′)⟩ = ⟨a, c′⟩ = c. ∎

Two remarks. (i) The proof consumes exactly three standing facts —
`tmark_last_surj`, `tmark_lastT_surj`, `ext_zc` — plus the new row; no
XHDd, XHDu, valuation, or mass law enters. (ii) The quantifier discipline
is exact: the IH is invoked at the EXTENDED history, which is where the
`ext_zc` guard is needed; this is the only place zc-preservation is used.

## 4. Theorem B — the reduction is lossless (compiled)

**Theorem B.** `RealizationComplete TE → MarkGraft TE`.

*Proof.* Given (m, γ, x, h, a, b′) as in the definition, apply surjectivity
of tmark(cons(m, γ), x, h) — available since q₀ ∈ Pools and zc x — to the
chain ⟨a, tmark(γ, ext(x, a), h′)(b′)⟩. ∎

So `MarkGraft` ⟺ `RealizationComplete` modulo the standing laws: adopting
it as the named row loses nothing and gains the confinement of Theorem A —
an instance builder discharges a ONE-STEP law and the ledger field `hRC`
follows by Theorem A. (Fence: this equivalence means `MarkGraft` is NOT
"strictly weaker" content; its value is locality/provability-shape at the
instance, per §6, exactly as `tmark_last_surj` is the local form of the
length-1 tie.)

## 5. Theorem C — the counting-tie form (compiled)

**Theorem C.** For any TE satisfying the standing laws:
`RealizationComplete TE` ⟺ for all γ, q₀ ∈ Pools, zc x, and all h:
T_γ(x, h) = T̂_γ(x, h).

*Proof.* (⇒) is the corpus' `tgam_eq_chainCount_of_complete`. (⇐): tmark
is injective (standing law `tmark_inj`) between finite carriers; the
source has cardinality T_γ(x, h) by definition, the target T̂_γ(x, h) by
`chains_card`; equal finite cardinalities upgrade an injection to a
bijection, hence surjectivity. ∎

Uses. (i) The instance builder may equivalently discharge the counting tie
(a per-(γ, h) cardinality identity — the note's D4R.4-genre statement)
instead of the graft; Theorems A/B/C let the ledger consume whichever
lands. (ii) The ⇐ direction makes `RealizationComplete` NUMERICALLY
testable: it is refuted at the intended instance iff some concrete
stratum has T < T̂ (see NUMERIC-TESTS). (iii) Composing with Theorem A:
MarkGraft ⟹ the counting tie — the graft law is also the one-step engine
for the T = T̂ identity.

## 6. Truth at the intended instance

Claim (conditional, per the duties below): at the intended p-adic instance
(B§5), `MarkGraft` — hence, by Theorem A, `RealizationComplete` — is true,
and its proof is re-indexing, not measure theory.

### 6.1 The structural point

A counted tail mark b′ ∈ tinst(γ, ext(x, a), h′, ℓ(γ)) is, semantically, a
(level-ℓ(γ) residue of a) marked pair (f, η): a p-adic polynomial f and a
branch prefix η of T_can(f) that (i) realizes the history ext(x, a) —
which already includes the prefix x AND the fresh digit cell a — and (ii)
continues from it along γ at heights h′. The SAME pair (f, η) therefore
realizes, from the prefix x, the fresh assignment a at height h₁ followed
by γ at h′: it is a realization of (cons(m, γ), h) from x. Grafting
produces no new polynomial and runs no new existence argument; it re-reads
an existing realization one constructor higher. This is exactly the
mechanism the corpus already recorded for the adjacent composite-event law
(`CompProduct` docstring, B§4.5: "the instance's cevt is BUILT as the
entrance-extended biUnion, where the split is definitional").

By Theorem A all remaining existence content sits at length 1
(`tmark_last_surj`): THERE the instance must genuinely produce, for each
realized fresh assignment, a polynomial in its digit cylinder — the note's
C.1.5 layer supplies it, each fresh assignment being a digit cell of
positive conditional mass q₀^{−E(h)} > 0 (XHD-w, B§5), and a nonempty open
cylinder in the coefficient space contains a point. But that law is
ALREADY a standing field of `TmplEvents`; it is an instance-construction
duty regardless of this problem.

### 6.2 The named instance duties

The re-indexing becomes a proof of `MarkGraft` under four duties on the
B§5 carriers — each a construction-time obligation, none a new axiom:

- **(I0) Realized-fiber build.** `Assign(m, x, h)` is the set of fresh
  digit cells REALIZING (m, h) from x (nonempty locus), and zc histories
  are realized prefixes. Warrant: this is the note's own definition (V.0:
  "T_γ(x, h) := #{fresh-assignment chains from x realizing (γ, h)}";
  blueprint §2.B: "`Assign` = the fresh-assignment fiber realizing
  (m, o, β) at h from x", "zc = (ZC)-satisfying realizable prefixes").
  If a build violated (I0) — e.g. syntactic digit menus with unrealizable
  entries — `RealizationComplete` would be FALSE at that build, and
  `tmark_last_surj` would already be unprovable at it: the fence is
  upstream of this row.
- **(I1) Faithful census.** tinst(γ, x, h, N) at N = ℓ(γ) contains the
  level-N residue of EVERY marked pair (f, η) realizing (γ, h) from x.
  (Censuses that undercount realized marks would break grafting even
  though the realization exists.)
- **(I2) Level coherence.** ℓ(cons(m, γ)) is a stabilization level for the
  composite shape: every realizability equation of the composite path is
  resolved at it, so a realized (f, η) has a well-defined counted residue.
  Warrant: the note's D4R.4/L12 defines exactly this level, N(P̂) := the
  max of the per-prefix resolution levels N(η, ⊤) over the finite
  unquotiented prefix set — finite by L8 (§C C.2 base levels).
- **(I3) Reading coherence.** tmark is computed by reading off the digit
  cells η consumed: the first consumed cell of the grafted mark is a, and
  the tail of its reading equals the reading of b′. If tmark is DEFINED
  this way at the instance (the blueprint's "the marks ARE the realized
  histories η"), (I3) is definitional; the graft target
  ⟨a, tmark(b′)⟩ is then hit by the grafted mark's reading on the nose.

Under (I0)–(I3): given (a, b′), lift b′ to a realizing pair (f, η) [(I1)
at the tail level + (I2)], observe (f, η) realizes the composite [(I0):
histories/assignments are realized objects, so no consistency gap can open
between the head cell a and the tail realization — b′'s history argument
ALREADY pins a], take its counted composite residue b [(I1)+(I2) at the
composite level], and compute tmark(b) = ⟨a, tmark(b′)⟩ [(I3)]. ∎(cond.)

Honest gap, displayed: (I1)–(I3) are stated against carriers that do not
exist on disk (B§6). They are DESIGN constraints; the alternative
discharge (equally warranted by the corpus' own diagnosis) is to BUILD
tinst at composites as the Σ-indexed union over first assignments of the
tail censuses, making `MarkGraft` definitional and shifting the proof
burden onto the XHDd laws for the built census — where the note keys them
(B§2.4 is stated at T_γ) — so no burden is silently dropped.

### 6.3 Answers to the brief's three questions

1. **Is the row true at the real instance?** Yes at the intended semantics,
   conditional on duties (I0)–(I3) — each of which transcribes a
   definition or displayed lemma of the source note (citations in §6.2),
   none of which is an added mathematical assumption. Equivalently: the
   counterexample shape 0 < T̂ ∧ T = 0 is excluded at the real instance
   because every formal chain there is a nested sequence of REALIZED digit
   cells, and realized objects carry marks. A REFUTATION at the real
   instance would require a zc history or assign-fiber entry with empty
   realization locus — barred by (I0).
2. **Added hypothesis:** `MarkGraft` (§2), with Theorem A (proof), Theorem
   B (losslessness), Theorem C (equivalent counting form), and the
   countermodel check (§2). All compiled.
3. **Provable at the bridged instance?** Yes under (I0)–(I3), by §6.1's
   re-indexing — or definitionally under the biUnion build of §6.2's last
   paragraph. Not provable from anything currently on disk (Theorem 0
   bars every law-only route), so the row correctly remains a ledger
   field until the Phase-B instance lands.

## 7. Compiled artifacts (verbatim; scratch-checked against HEAD)

Compiled 2026-07-31 with `lake env lean` against the built HEAD
(`/tmp/M18_scratch.lean`; imports `MovesV.V2_valB`, `MovesV.V1_chains`,
`MovesV.V4_hmc`). All four `#print axioms` reports:
`[propext, Classical.choice, Quot.sound]`. Statement fence respected:
nothing existing is touched; one new `def`, four new theorems.

```lean
def MarkGraft {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) : Prop :=
  ∀ {α β : S.Cell} (m : S.Move α β) (γ : Template n S β) {q₀}
    (x : S.Hist q₀ α) (h : Hpt (Template.cons m γ).D),
    q₀ ∈ S.Pools → S.zc x →
    ∀ (a : S.Assign m x (Hpt.take h))
      (b' : {b // b ∈ TE.tinst γ (S.ext m x (Hpt.take h) a) (Hpt.drop h) (TE.tmplLvl γ)}),
      ∃ b : {b // b ∈ TE.tinst (.cons m γ) x h (TE.tmplLvl (.cons m γ))},
        TE.tmark (.cons m γ) x h b
          = ⟨a, TE.tmark γ (S.ext m x (Hpt.take h) a) (Hpt.drop h) b'⟩

theorem realizationComplete_of_markGraft {n : ℕ} {S : StepSys n}
    (TE : TmplEvents n S) (hG : MarkGraft TE) : RealizationComplete TE := by
  intro α γ
  induction γ with
  | last m => intro q₀ x h hq hzc; exact TE.tmark_last_surj m x h hq hzc
  | lastT m => intro q₀ x h hq hzc; exact TE.tmark_lastT_surj m x h hq hzc
  | cons m γ' ih =>
    intro q₀ x h hq hzc c
    obtain ⟨a, c'⟩ := c
    obtain ⟨b', hb'⟩ := ih (S.ext m x (Hpt.take h) a) (Hpt.drop h) hq
      (S.ext_zc m x (Hpt.take h) a hzc) c'
    obtain ⟨b, hb⟩ := hG m γ' x h hq hzc a b'
    exact ⟨b, by rw [hb, hb']⟩

theorem markGraft_of_realizationComplete {n : ℕ} {S : StepSys n}
    (TE : TmplEvents n S) (hRC : RealizationComplete TE) : MarkGraft TE := by
  intro α β m γ q₀ x h hq hzc a b'
  exact hRC (.cons m γ) x h hq hzc
    ⟨a, TE.tmark γ (S.ext m x (Hpt.take h) a) (Hpt.drop h) b'⟩

theorem realizationComplete_iff_counting {n : ℕ} {S : StepSys n}
    (TE : TmplEvents n S) :
    RealizationComplete TE ↔
      ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
        q₀ ∈ S.Pools → S.zc x → Tgam TE γ x h = chainCount S γ x h := by
  constructor
  · intro hRC α γ q₀ x h hq hzc
    exact tgam_eq_chainCount_of_complete TE hRC γ x h hq hzc
  · intro hC α γ q₀ x h hq hzc
    letI : Fintype (Chains S γ x h) := chainsFintype S γ x h
    have hinj := TE.tmark_inj γ x h hq hzc
    have hcard : Fintype.card {b // b ∈ TE.tinst γ x h (TE.tmplLvl γ)}
        = Fintype.card (Chains S γ x h) := by
      rw [Fintype.card_coe, chains_card]
      exact hC γ x h hq hzc
    exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩).2

theorem not_realizationComplete_toy : ¬ RealizationComplete HmcToy.TE := by
  intro hRC
  have hsurj := hRC
    (.cons HmcToy.mv (.last HmcToy.mv)) (q₀ := 2) ((0 : Fin 2)) (fun _ => 0)
    rfl trivial
  obtain ⟨b, -⟩ := hsurj
    (HmcToy.chainDefault (.cons HmcToy.mv (.last HmcToy.mv)) ((0 : Fin 2)) (fun _ => 0))
  have hb : b.1 ∈ HmcToy.tin (Template.cons HmcToy.mv (Template.last HmcToy.mv))
      (q₀ := 2) ((0 : Fin 2)) (fun _ => 0) := b.2
  have hc : HmcToy.census (Template.cons HmcToy.mv (Template.last HmcToy.mv))
      (q₀ := 2) ((0 : Fin 2)) (fun _ => 0) = 0 := by
    simp only [HmcToy.census]
    exact if_pos rfl
  have hbc := (Finset.mem_filter.mp hb).2
  rw [hc] at hbc
  exact absurd hbc (Nat.not_lt_zero _)
```

## 8. Recommended disposition (for the orchestrator; not executed here)

1. Land §7 as a unit (e.g. `MovesV/V2_valC.lean` or appended to V2_valB
   behind the existing row) after ratification; keep `hRC` as the ledger
   field, now derivable from a `MarkGraft` field via Theorem A if the
   ledger prefers the local row.
2. Charge the Phase-B TE-instance blueprint with duties (I0)–(I3), or with
   the compositional-census build (§6.2 close), whichever fits the
   `cevt`/biUnion design already recorded at `CompProduct`.
3. Note for consumers: `val_b` consumes the row only at in-domain h, but
   no weakening is warranted — the instance-side proof is not any easier
   on the restricted domain (the IH would then need domain factorization
   through drops of h, which is HMC-adjacent and OPEN; the unrestricted
   row avoids domains entirely).

## VERDICT

REDUCED — `RealizationComplete` is (i) refuted as an unconditional
statement (Theorem 0, compiled), (ii) proved equivalent, over the standing
laws, to the new one-step law `MarkGraft` (Theorems A+B, compiled) and to
the counting tie T_γ = T̂_γ (Theorem C, compiled), and (iii) argued TRUE at
the intended p-adic instance conditional on four displayed instance-build
duties (I0)–(I3), each transcribing a source-note definition/lemma; the
instance itself is not yet on disk, so no unconditional discharge is
claimed.

## NUMERIC-TESTS

The testable form is Theorem C's counting tie: T_γ(x, h) = T̂_γ(x, h) —
"realized marked-prefix census = product-recursion chain census". Any
concrete stratum with T < T̂ (in particular the recorded shape
0 < T̂ ∧ T = 0) refutes the intended-instance claim; agreement across all
probed strata confirms it. Concretely (sympy for exact bookkeeping;
cypari2's `factorpadic`, cf. `verification/quartic_oracle.py`, as the
branch oracle):

1. **Setup.** For (n, p, N) ∈ {(2,2,8), (2,3,6), (3,2,6), (3,3,4)}:
   enumerate ALL monic f ∈ (ℤ/p^N)[x] of degree n (sizes p^{nN}: 2^{16} =
   65 536, 3^{12} = 531 441, 2^{18} = 262 144, 3^{12} = 531 441). Height
   caps H per row must satisfy the stabilization check of Test B (N vs
   N−1 agreement); expect H = 3 for the n = 2 rows and H = 1–2 for the
   n = 3 rows at these N — if a stratum fails stabilization, raise N for
   that stratum alone (sparse enumeration on its digit cylinder), never
   trust an unstabilized count. For each f compute the first TWO
   reads of the canonical branch tree: root Newton polygon of f (slopes =
   first heights h₁, per-slope residual polynomials), then for each branch
   with a repeated residual factor, the descended read (next slope h₂
   after the Montes lift/recentering at a chosen representative).
2. **Test A (length-1 realization = `tmark_last_surj` analogue).** Group
   the census by (first-read species m, height h₁, digit cell a): check
   every (m, h₁, a) that is REALIZED by at least one f is counted, and —
   the surjectivity direction — that the per-(m, h₁) chain count (number
   of distinct digit cells a with nonempty locus) equals the number of
   distinct mark classes (residue classes of f at the stabilization level
   realizing (m, h₁)) divided by the common fiber size p^{nN−A} (D4R.4:
   each realized prefix contributes exactly p^{nN−A(P̂)} residues).
   Confirms: census(m, h₁) = #Assign(m, h₁) · p^{nN−A}.
3. **Test B (the graft / counting tie at length 2).** For each two-step
   template (m₁ at h₁ ≤ H, m₂ at h₂ ≤ H), H = 3: compute
   T := #{marked prefixes (f mod p^N, η) following (m₁, h₁)(m₂, h₂) from
   the root} / p^{nN−A(P̂)} (the branch-weighted D4R.4-SUM count, exact at
   N ≥ N(P̂) — verify stabilization by comparing N and N−1), and
   T̂ := Σ_{a ∈ first digit cells realizing (m₁,h₁)} #{second digit cells
   realizing (m₂, h₂) from the a-extended prefix}. CONFIRMS if T = T̂ on
   every stratum; REFUTES if any stratum has T < T̂ — then print the
   offending (h₁, h₂, a-chain): it is a formal chain with empty locus, a
   direct counterexample to duty (I0)/(I1) and to the row at the real
   instance.
4. **Test C (targeted shape scan).** Scan specifically for strata with
   T̂ > 0 ∧ T = 0 across ALL templates reachable in two reads (including
   terminal second steps, e.g. unramified/totally-ramified exits (e, f)):
   expected count 0. Any hit is a minimal machine counterexample to carry
   back into the Lean toy layer as a REAL-instance negation witness.
5. **Wild corner emphasis.** Include p = 2, n = 2 (wild quadratic:
   ramification polygon reads with carries) and p = 3, n = 3 (wild cubic)
   — the carry-coupled strata are where an (I0)-violation (a syntactically
   consistent but unrealizable digit chain) would most plausibly hide;
   height caps H = 3 already cross the first carry thresholds there.

