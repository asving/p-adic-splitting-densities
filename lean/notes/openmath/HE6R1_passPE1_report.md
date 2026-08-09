# HE6R1 passPE1 — hostile pass 1 on the RECONCILIATION note (fresh context)

**VERDICT: NOT CLEAN — 0 CRITICAL, 2 GAP, 5 MINOR. Both GAPs sit on LEMMA
HE6R1-2 (block projection) — a missing hypothesis and an overconsumption —
and neither propagates to a consumer at HEAD (HE7's standing Ψ ∤ f_S
convention guards the one frozen consumption site). The literal-instance
theorem (§S3.1–S3.2), LEMMA HE6R1-1, LEMMA HE6R1-3, the §S2 rewording, and
the R1–R9 record survived every check run here. Machine leg: bit-identical
isolated re-run; the 5 disclosed exceptions reproduced exactly and
independently. Fresh route: 2 new legs, 406 fresh PARI jobs, 0 mismatches.**

Target: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md` at HEAD (seal
4f5ebaa, verdict 850e77e, [r2] row via cec49ba/d1b0bc8). Protocol:
quote-and-classify, nothing fixed. Endpoints read at HEAD:
`HE6_PROOF_2026-08-08.md` (post-r2) and `HE7_PROOF_2026-08-08.md` (post-r3
+ dated appends). Attack order followed: (1) literal-instance statement vs
the frozen endpoints, (2) LEMMAS HE6R1-1/2/3 as a composition, (3) the 5
disclosed exceptions, (4) R1–R9 spot-checks, (5) free hunt; plus the
machine-leg integrity charges and the mandatory fresh route.

---

## FINDINGS

### F-1 (GAP, CONFIRMED) — LEMMA HE6R1-2 omits the Ψ ∤ f_S hypothesis its own proof consumes

Quote (§S3.4, statement): "Let f be monic on the opening locus with
disc f ≠ 0 and Φ′ ∤ f, let (λ, r) be a level-1 label of f, S = S_{λ,r},
f_S the block factor (LEMMA HE7-6) and g := f/f_S ∈ O[x]." — no Ψ ∤ f_S
(equivalently Ψ ∤ f) hypothesis. The proof of (b) cites THEOREM HE7.A(1)
— which at frozen HEAD carries "**with Ψ ∤ f_S**" (HE7 §S1 CONVENTION
[r1], the hypothesis THIS NOTE discovered as FINDING HE6R1-F2) — and both
support functions h_{F₂,f}, h_{F₂,f_S} need their j = 0 pins finite
(A₀^{(2)} ≠ 0) for the large-κ₂ minimizer that makes the finite-slope
lengths sum to μ₂.

Failure scenario (concrete, on the note's own data): take any of the 12
battery members with Ψ | f (block = everything, g = 1, c_g = 0 — the
lemma's hypotheses as stated are satisfied). Then μ₂ = 2 but the
finite-slope sides of P₂(f) above T₂ sum to μ₂ − 1 = 1 (the j = 0 pin is
at ∞), so (b)'s display "μ₂ = Σ_{λ₂>T₂} L_{λ₂}(f)" is FALSE by exactly the
missing block — the identical failure mode FINDING HE6R1-F2 names one
section later. Non-propagating at HEAD: HE7's only frozen consumption
(COROLLARY HE7.B [r1], proper blocks) sits inside HE7 §S2–S8's standing
Ψ ∤ f_S convention, and Ψ ∤ f_S ⟹ Ψ ∤ f ⟹ Ψ ∤ g (roots of Ψ are
level-2 points with label (λ, r), hence in S). Repair is one line: peel
first per LEMMA HE6R1-3. The irony is structural: the note that found the
missing-hypothesis genus omitted the same hypothesis in its own new lemma.

### F-2 (GAP, CONFIRMED) — LEMMA HE6R1-2(b)/(c) consume LEMMA HE7-7′(b) at f, outside its stated scope

Quote (§S3.4(b)): "so LEMMA HE7-7′(b) gives dv₂(f(ξ)) = h_{F₂,f}(κ₂) and
dv₂(f_S(ξ)) = h_{F₂,f_S}(κ₂), both with no excess"; (c) applies it to f
again. Frozen HE7-7′(b) (HE7 §S5.4) is stated ONLY for f_S:
"dv₂(f_S(ξ)) = h_{F₂}(κ₂) + δ(ξ) …". The variant for an arbitrary monic
F ∈ O[x] with a Ψ-development and Ψ ∤ F — needed at F = f — is stated
nowhere in either frozen endpoint. The generalization is true by the same
proof ((SLOT₂) on the development coefficients + the gcd(u₂,ℓ₂) congruence;
HE7 §S5.8's audit itself notes the argument is key-free), so this is a
justification gap / overconsumption, not a falsity — the same genus as
Codex PE1 finding 6 on GENHN-2, one level up, in the note that applied that
very finding as R5.

### F-3 (MINOR) — HE6R1-2(c)'s "in the separable case they are equal" overshoots by a K₂^× scalar

R^f_{λ₂} and R^{f_S}_{λ₂} agree up to the constant factor given by g's
level-2 residue (a fixed element of K₂^×, nonzero by (a)); equality of the
polynomials needs that scalar to be 1, which is not proven and is false in
general. Same radical + same degree + separable gives equality up to
K₂^×-scaling only. No consumer sees it: HE7's §S1 twist convention already
declares residuals meaningful "up to K₂^×-scaling", and HE7.A(2) consumes
only the monic irreducible factors.

### F-4 (MINOR) — §S6 Totals line miscounts the strict-excess certificates

Quote: "46 strict-excess + 4 infinite-excess certificates". The runner's
HE6R1-SEP2 counter (= 46) counts TESTED instances including the 4 that
violated at the seal; sealed strict-excess certificates number 42. The
P4/P5 paragraph two blocks later does disclose "46 strict excesses with 4
accounted-for exceptions"; the Totals line calls all 46 certificates.

### F-5 (MINOR) — the ten-item instance map predates HE7's [r2] refined-key package

§S3.2 enumerates the literal-instance check over HE7 §S1–S6 as of 62d683f.
At HEAD, HE7 §S5 also contains LEMMA HE7-12 (SLOT-DOMINATION) and LEMMA
HE7-13 [r2], consumed by every ℓ = 1 read that α-refines (the note's own
battery refines); the recon contains no ℓ = 1 instance check for them.
No mathematical hole: both lemmas are stated and proved at general ℓ
inside frozen HE7 (arc-passed), and HE7's PE2 ran a fresh ℓ = 1, d_r = 2,
K₂ = F_{p²} α-refine family (634/634 PARI, 2-step chains). Recorded as
citation-era incompleteness of the "ten items, no adaptation" sentence.

### F-6 (MINOR) — R8's record row describes a different application shape than the applied one

The table says "'every NONZERO term' inserted at the three displays"
(site "HE6 §S3.3, §S4"); the applied form at HEAD is ONE standing sentence
at HE6 §S3.3 ("**[r1, R8/F9]** every term-by-term exactness display below
is read over the NONZERO terms…") whose "below" scopes §S4. Content
equivalent; the record's description of where/how does not match the byte
reality it points at.

### F-7 (MINOR) — P1's scoreboard symbol is generous relative to the preregistration

P1 as sealed reads "On every member the … read returns a sigma … and PARI
… AGREES, member by member, 0 mismatches." As stated it failed on 12 of
944 members (no σ returned; 5 of them in the PARI count). The note scores
"✓ with one honest qualification" rather than "failed-as-preregistered,
diagnosed and cured post-seal". Every number is disclosed in the same
sentence and in the artifacts (nothing hidden — the exceptions are the
note's own FINDING HE6R1-F2), so this is presentation, not concealment.

---

## CLEAN CHARGES (attacked, survived)

* **Literal-instance statement vs frozen endpoints (attack 1).** §S3.1's
  table checked row-by-row against DEFINITION HE7-1 at HEAD (dv₂, K₂, T₂,
  n₂, the twist c, the substitution table — line-level agreement,
  including T₂ = ℓd_r·u ↦ d_rλ and n₂(k) ↦ ϖ^k). §S3.2's ten items
  checked against HE7 §S3/§S4/§S5 at HEAD: item 1 vs (SLOT₂)'s Steps 1–3
  (Step 2 genuinely vacuous at one class; Step 3's basis argument is
  HE7's own); item 2's (†₂)/(‡₂) coincidence at ℓ = 1 and both use-site
  chains re-derived here and matching HE7 §S4.3 [r1]'s independent
  re-derivation; item 5's margin chain re-derived — the ℓ = 1
  specialization of HE7's (S5.3)-fold display, with the recon using only
  the r2-CORRECTED ε₀/ε₁ split (it does not reproduce HE7's pre-r2 false
  dichotomy); items 3, 4, 6–10 statement-for-statement. §S2's HE6.B
  rendition matches HE6.B [r1] at HEAD clause for clause; the four-case
  table matches the Codex F1 adjudication item for item; the n ≤ 7 chain
  (L_λ ≥ m·ℓd_r ≥ 4, n ≥ D′μ ≥ 8) re-derived.
* **LEMMA HE6R1-1 as a composition (attack 2).** Jump-condition complement
  = §S2's enumeration (post-R2 convention supplies Σ L_λ = μ); the two
  displays re-derived (deg f_S ≤ n_λ = D′L_λ via HE6-3(b), then
  deg R_λ/d_r ≤ μ/(ℓd_r)); iteration 4 ≤ μ_J ≤ μ/2^{J−1} gives
  J ≤ log₂μ − 1 ≤ log₂n − 2 with D′ ≥ 2; bounds character-match THEOREM
  HE7.C [r1] at HEAD, which credits this lemma.
* **LEMMA HE6R1-3 as a composition (attack 2).** Every step checked
  (HE6-1 for the key's roots; HE6-0′ at roots of f — legitimate since
  Ψ | f_S | f; Galois-stability of g₀; deg pinch D″ from orbit ≥ D″ and
  g₀ | Ψ; e ≥ e₁ℓ, f ≥ f₁d_r, ef = D″ forcing equality; simplicity from
  disc f ≠ 0). Its (e,f) = (e₁ℓ, f₁d_r) = (2,2) prediction and Ψ's
  irreducibility verified independently by PARI on 5 members (below).
* **The 5 disclosed exceptions (attack 3).** Honest and sound — see
  machine leg: each is a non-decision (σ = None, never a wrong σ), each
  lies on the Ψ | f stratum by exact division run with fresh code, each is
  decided by the peel with independent PARI agreement.
* **R1–R9 record (attack 4).** Spot-checked R3 (HE6-1L [r1/r2] at HEAD:
  the struck (LIFT), both finders' counter-instances — Codex's (1,2,1)
  k = 0 matches CODEX_HE6PE1 finding 4 verbatim; HE7-F1's (3,1,2) k = 1
  matches HE7 §S4.1; the [r2] coset row's byte-diff enumeration
  spot-verified on the checkable items: `^k` vs `^{k}`, `))h` vs `))·h`,
  `{0,…,f₁−1}` spacing, and the T(k) display line currently byte-identical
  across the two files; HE7's fold-box "verbatim" indeed unsoftened by the
  5da0552 append — the [r2] row's "HE7-side residue" note is accurate),
  R4 (ψ-cancellation proof present at HE6 §S3.1; Codex's ξ = −θ instance
  untouched), R5 (HE6-0″ at HEAD with the [r2] −q sign and the exact
  proof line the recon quotes), R7 (ϖ ∈ K₀[x] + Codex's (2,3) example at
  the CONVENTION site), R9 (GENHN [r1] annex: corrected node
  {dv(A_j) ≥ (μ−j)D′h + 1}, derivation chain and GENHN-ERR-1 residue
  matching the recon's row sentence for sentence), and the R2/R6 standing
  CONVENTION [r1] on HE6 §S1 + THEOREM HE6.A [r1].
* **FINDING HE6R1-F1/F2 landing sites.** Both present in frozen HE7 at
  HEAD exactly as the recon states them (HE7.A(3) [r1] widened trichotomy;
  HE7.C [r1]; §S1 CONVENTION [r1] with the peel; HE7-BOX-4 superseded-in-
  read-form box; HE7-BOX-2 [r1] crediting this battery).

---

## MACHINE LEG

* **Pins.** Runner md5 7112f7c738ed13fb352f96849da1d309 at HEAD ==
  850e77e; import pins in the committed json (he6_checks 321fa4d4…,
  he7_checks 688adbe8…, w12 7dc040d9…, w10 a9c34244…) == the 850e77e blob
  md5s == HEAD blob md5s. he6r1 artifacts byte-unchanged since 850e77e.
* **Post-seal diff.** 4f5ebaa → 850e77e runner diff is exactly the
  disclosed `pstr` guard: one function + two call sites (a print and the
  record's 'f' string); no predicate in the diff. Verified from the diff
  itself, not the note.
* **Isolated re-run.** Full battery re-run from 850e77e blobs in a clean
  directory (transitive imports also pinned from 850e77e; the PINS list
  itself omits the deeper import chain w11/iterlawn/jd0/grt_jc/engine_ext/
  grb — noted, all fetched from the same commit): output byte-identical
  modulo timing; results json identical except per-row 'secs'; 21
  violation records identical (12 READ2 + 5 SIG2 + 4 SEP2); legs
  {LIFT2 59, READ2 932, SLOT2 1512, GEN2 252, SEP2 46, SEP2-inf 4,
  SIG2 682}; teeth 5/5 FIRED. 87.2 s claim matches.
* **Tautology audit.** The reader (`level2_read`) makes no PARI call; PARI
  enters only at scoring. Fresh cross-tab over the 944 members with MY OWN
  exact division code: status BADTOTAL ⟺ Ψ | f, 12 members, 0 mismatches
  — the exceptions are exactly the stratum the note names, and only it.
* **The 5 exceptions, reproduced independently.** Direct gp (fresh script,
  factorpadic + nfinit([g,[p]]) + idealprimedec): each of the 5 char-0
  BADTOTAL members has σ = {(2,2),(2,2)}, matching the committed SIG2
  records; Ψ | f exactly (remainder 0); Ψ itself irreducible over ℚ_p with
  (e,f) = (2,2) — LEMMA HE6R1-3's prediction — and the peeled cofactor has
  σ = {(2,2)}. The supp leg re-run isolated: output identical (12/12
  peels, 5/5 PARI, SEP2 4/4 recovered STRICT at 68>64, 68>64, 100>96,
  100>96 — the note's exact numbers).
* **SEP2 diagnosis verified in code.** `grid2_labels` harvests labels from
  the reader's final (post-α-refine) trace while `build_psi2` always
  builds over `fr.Psi` — the note's leg-construction diagnosis is what the
  sealed code does.
* **Note-vs-artifact numbers.** 944/932/682/677/12/5, the per-row σ census
  table, the P3 table (onto exactly k ≥ λ; threshold λ+1 sufficient, not
  tight), and the teeth details (CRACK 54/3/2 over 59 and 47/6/1 over 54,
  read agreeing 59/59 and 54/54; NAIVEHE6A 57/59, 53/54; BASIS dv₂ = 5,
  v(Res) = 20; TWIST0 1,276 zeros; WITHHOLD → UNDETERMINED) each match the
  committed artifacts. The one number that does not survive is F-4's "46
  … certificates".

## FRESH ROUTE (`verification/openmath/he6r1_pe1_fresh.py` + artifacts)

Two legs, preregistered in the runner docstring before the run; sealed
instrument consumed by import (pins printed), every σ scored against PARI
directly. **0 violations.**

* **Leg A — third-plus characteristic pair.** Same ℓ = 1, d_r = 2 frame at
  p = 11 (r = Z²+1) and p = 13 (r = Z²+2), full member enumeration:
  139 + 139 members, 278/278 PARI agreements, 0 mismatches, three-σ
  alphabet reproduced (11: 125/6/8; 13: 131/4/4). No Ψ | f members arose
  at these primes (278 decided directly).
* **Leg B — the peel COMPOSED with a refine (the interaction the two
  disclosed exception families sit next to; exercised nowhere before —
  the sealed peels all landed at μ₂ − 1 = 1 where no refine can occur,
  and HE7-BOX-5 names "a peel at μ₂ ≥ 3" unexercised).** n = 12, μ₂ = 3:
  f = Ψ·((Ψ−W)² + E) with W a (LIFT₂)-lift of a K₂-rational residue at
  λ₂ = 7 > T₂ and E a height-15/16 perturbation; every member forces
  peel → α-refine → decide. p = 3: 32 members; p = 5: 96 members;
  128/128 PARI agreements, 0 mismatches; σ ∈ {(2,2)}⊔{(4,2)} and
  {(2,2)}×3 exactly as the composed dictionary predicts. First machine
  instances of LEMMA HE6R1-3 ∘ HE7.A(3)-refine, and first μ₂ = 3 peels.
* **Not run:** non-prime q (an f₁ ≥ 2 / K = F_{q²} tower needs a fresh
  K₂-over-K implementation; disclosed in the runner docstring as the
  remaining fresh-route candidate).

---

## GRADE LINE

passPE1 verdict **NOT CLEAN**: 0 CRITICAL, 2 GAP (F-1, F-2 — both on
LEMMA HE6R1-2's statement/citations; the (b)(c) conclusions survive under
the one-line Ψ ∤ f_S repair and the HE7-7′(b) scope widening, and the one
frozen consumer is guarded at HEAD), 5 MINOR. Machine leg GREEN
(bit-identical isolated re-run; tautology audit clean; 5 exceptions
reproduced exactly, independently, with their exclusions verified sound).
Fresh route GREEN (406 fresh PARI jobs across a new characteristic pair
and the never-exercised peel∘refine composition, 0 mismatches). The
2-clean count does NOT start: **HE6R1 stays 0/2**; the r1 text owes the
F-1/F-2 repairs and then a fresh hostile pass.
