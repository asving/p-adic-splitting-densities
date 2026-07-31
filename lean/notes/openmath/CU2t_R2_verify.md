# CU-2t R2 hostile verification (pass CU2tpass, 2026-07-31)

**Charge:** fresh-context hostile pass on the R2 text of
`lean/notes/openmath/CU_cluster_phaseB.md` §9 (unit CU2t), per the §9.7 +
§10 charge: (iii-a)/(iii-b) layered injectivity, Definition RC's
non-circularity display, the rescoped §1, the §9.4/§9.5 residue honesty,
and the §10 F1–F11 disposition table. Read ONLY the target file (its own
git history consulted solely to check the file's claims about itself: F11
and byte-stability). Quote-and-classify; nothing fixed.

**VERDICT: SOUND-WITH-GAPS** — 0 critical errors, 4 justification gaps,
2 minor. The F1 critical of the pass-1 report is genuinely repaired: the
pair-carrying Θ^τ makes (iii-a) a valid strip-and-compare argument, and
(iii-b)'s determination-as-injectivity over Definition RC is valid as
displayed. The gaps are on the EMITTED-side tie (the (RC-read) half of
run-emitted RC-consistency has no supply row) and on citation/standalone
hygiene.

---

## 1. What was checked and held (the positives, so the gaps are scoped)

* **(iii-a), verified sound.** Θ^τ(𝐇°, ν) := Θ(𝐇°) ⌢ (λ_{k'+1}, ⊥,
  (E_ν, F_ν)). Equal images ⇒ equal lengths ⇒ equal last entries and equal
  prefixes; Lemma R (cited, both prefixes all-continuing Cons_f) recovers
  𝐇°; the appended triple returns the announced pair. Injectivity at
  (𝐇°, announced-pair) granularity follows; the pass-1 F1 counterexample
  class (one 𝐇°, two records announcing different pairs) separates in the
  image. The trailing-⊥ separation from Θ-images (⊥ not a ψ̂ value, typed;
  entry arity differs too) is sound.
* **(iii-b), verified sound AS SCOPED.** Over RC-consistent seam objects,
  (RC-verd) pins (E_ν, F_ν) to the accumulator pair (arithmetic of 𝐇°'s
  discrete fields) and (RC-read) pins the shape fields to (i)'s
  single-valued side datum, so equal 𝐇° forces equal RC-constrained
  vectors — injectivity at datum granularity through the Θ(𝐇°)-coordinate,
  with full-record recovery honestly fenced behind the §9.2a inventory
  caveat. Valid, and the caveat is displayed and routed.
* **Definition RC non-circularity, verified as displayed.** Neither clause
  references the true factor or its invariants: (RC-read) is a polygon
  read of f over the prefix chain; (RC-verd) is a record function of 𝐇°.
  Correctness (RC-pinned pair = true invariant pair) is kept as theorem
  (ii)-main, outside the definition. The circularity the pass-1 F2
  worried about is genuinely absent. (But see G4 on (c1)'s displayability.)
* **Rescoped §1, internally consistent.** The continuing-part 𝔈-membership
  claim, the seam-pair reading of the terminal record, and the
  W3-interior-clause parenthetical are mutually consistent and consistent
  with the §9.1 carrier note; "each emitted CONTINUING record" correctly
  narrows the GMN-datum clause; the index charge now reads dCert(𝐇°).
  (But see G3 on the surviving "This IS Theorem 2(D)" line.)
* **§9.4/§9.5 pricing honesty, executed as charged.** The rev-1 "zero new
  open inputs" sentence is gone; (T-DEC)/(T-VERD) are displayed as two NEW
  unproved mandatory-path obligations, no new family, with the four
  ledger/ROOT touches enumerated and marked owed-not-executed. (But see G1:
  the count of new rows is still one short.)
* **§10 table, verified against the file's own diff record.** The F1–F4
  "FIXED" rows match the actual R2 edits (checked against
  `git diff 254d4de..567814d` on this file); F5–F10 "ROUTED" rows name
  owners and route real holes, none silently absorbed; F11's
  "Git-verified: every commit of this file is calendar 2026-07-31" is TRUE
  (commits a9f294c, 254d4de, 52d4eed, 567814d, all 2026-07-31). The
  byte-stability claim is TRUE: the regions listed as unedited ((i),
  (ii)-main up to its uniqueness tail, (iv), the (i)/(iv) proof bodies,
  the Corollary, §§9.0–9.1, 9.6, the §6.1 audit) appear in neither R2
  diff hunk. Note for the record: R2 straddles TWO commits (52d4eed
  carries §1/§9.2a/header; 567814d carries (iii)/§9.4/§9.5/§10), so the
  intermediate tree state has a header referencing a not-yet-existing §10;
  the final text — the object of this pass — is consistent.
* **Spot-checks on the carried-over proof body** (not re-verification of
  the byte-stable cores, which have their own record): the j₀ ≤ 1
  separability argument (φ² | f ⇒ repeated root ⇒ disc f = 0) is sound at
  every level and indeed does not use φ-irreducibility; the (i) case split
  is exhaustive over DEC and each polygon read is single-valued given the
  quoted Lemma 2.17(2)/(3) + Def 1.8 pins; (iv) consumes TB-CAP only as
  bookkeeping.

## 2. Findings (quoted and classified)

### G1 — JUSTIFICATION GAP (the load-bearing one): run-emitted RC-consistency is overclaimed; the (RC-read) half has no supply row

Quoted, §2 R2 note (and again verbatim in §9.3(iii-b)):

> "every run-emitted record is RC-consistent via the (T-DEC)/(T-VERD)
> rows of §9.4"

and §9.4's conclusion:

> "Given the rows: emitted verdict-carrying ⇒ DEC configuration with
> Cons_f prefix ⇒ (Lemma CU-2t) the terminal datum is the forced
> T(f, 𝐇°) and the emitted verdict equals the true invariant pair…"

RC-consistency (Definition RC) has TWO clauses. The displayed rows supply:
(T-PREFIX) → Cons_f(𝐇°); (T-DEC) → the DEC configuration; (T-VERD) → the
announced pair = accumulator pair = exactly (RC-verd). **No displayed row
supplies (RC-read)** — that the emitted terminal record's shape/position
fields (e, h, ℓ, s, u), which terminal nodes carry per §9.1's own carrier
recap (ν_i = (e_i, h_i, ℓ_i, s_i, u_i, sel_i, inc_i)), are the
(c1)-shape datum of the level-(k'+1) polygon side. Cons_f cannot supply
it (Lemma R's terminal non-claim: "Cons_f constrains no terminal field" —
§9.1, quoted from O-2a). Failure scenario: the engine emits a terminal
record whose shape fields are, say, copies of the last continuing read or
defaults; (T-DEC)/(T-VERD) both hold, RC fails, (iii-b)'s coverage of
run-emitted records fails, and the read-entry half of §9.4's "the terminal
datum is the forced T(f, 𝐇°)" fails (the verdict half survives on
(T-VERD) alone). The missing supply is a THIRD engine-bookkeeping row of
exactly the (T-DEC)/(T-VERD) grade — call it (T-READ) — absent from §9.4,
from the F4 pricing correction ("(T-DEC) and (T-VERD) are TWO NEW open
inputs" — the honest count is three, or (T-DEC) must be restated to
constrain the record's read fields, not just the emission site), and from
the four enumerated ledger/ROOT touches. Downstream of the assumption the
chain is fine, so: gap, not critical — but it touches the pass's
"honest residue growth" target directly: the R2 residue correction itself
still undercounts by one row.

### G2 — JUSTIFICATION GAP: the (T-DEC) row is not a well-formed single statement (the corner booking contradicts its "ONLY")

Quoted, §9.4:

> "The engine emits a verdict-carrying terminal record on a branch ONLY
> at a decided configuration … ; the deep exact-key booking, if the
> engine performs one, is the displayed Corollary corner."

The deep exact-key corner (Corollary CU-2t-deep: k' ≥ 1, μ_{k'} ≥ 2,
j₀ = 1) is NOT a DEC configuration (§9.2 defines DEC(τ-irr) with
μ_{k'} = 1 and DEC(τ-hen) with k' = 0). So the row simultaneously asserts
"only at decided configurations" and admits a possible emission outside
them. If the engine ever corner-books, the §9.4 implication "emitted
verdict-carrying ⇒ DEC configuration" is false and Lemma CU-2t does not
apply to that record (T(f, 𝐇°) is undefined outside DEC; the Corollary is
explicitly out of the lemma's grade and conditional on (REP-IRR)). The
emitted-side tie is therefore silently conditional on "the engine never
corner-books", which is stated nowhere as an obligation. Resolution
belongs to the GD-4 owner (either strengthen (T-DEC) to exclude corner
bookings, or widen the tie's conclusion) — a same-grade bookkeeping
disambiguation, hence gap.

### G3 — JUSTIFICATION GAP: §1's "This IS O-2a rev 5 Theorem 2(D)" identity is unattested after the rescope, and the W3 carrier finding's implication for the cited home is unrouted

Quoted, §1 (unedited from rev 1 while the statement above it changed):

> "**Proof by citation.** This IS O-2a rev 5 **Theorem 2(D)** (brief §5)
> composed with 2(A)–(C)…"

The R2 statement is materially different from rev 1's (continuing part
only; terminal record expelled from the 𝔈 element). Both cannot literally
BE 2(D). Two cases, undecidable from this file: (a) 2(D) as printed in
O-2a already asserts only continuing-part membership — then rev 1's CU-2
was a misquote, now fixed, and the citation line is again accurate; or
(b) 2(D) as printed asserts full-history 𝔈-membership — then by this
unit's own §9.1 carrier finding (appending ν at a saturated prefix
violates W3's interior clause), 2(D)-as-printed is FALSE at
(τ-irr)-decided leaves and needs its own repair before CU-2 can cite it.
The file displays the carrier finding ("a finding of this unit,
displayed — nothing edited") and P(O-2a r5) is a named pending pass, but
NO owed pointer routes the finding to the O-2a owner: it is absent from
§8's owed-pointers list, from §9.5's four enumerated touches, and from
§10 (F3's disposition edits only THIS file's §1/§2). A finding that the
cited home's carrier laws clash with its flagship theorem's apparent
scope must be delivered to that home's pass, not merely displayed here.
Gap (the P(O-2a r5) verifier would likely catch it, but "likely caught
elsewhere" is not a routing).

### G4 — JUSTIFICATION GAP (standalone discipline): Definition RC's defining clause leans on the undisplayed (c1)

Quoted, §9.2a:

> "**(RC-read)** ν's shape/position fields (e, h, ℓ, s, u), with sel = ⊥,
> are the (c1)-shape datum of a side of N_{k'+1}^−(f)…"

against §9's own declared discipline:

> "every consumed external statement is quoted or pinpointed"

(c1) is pinpointed (O-2a §2, via the §9.1 recap "Cons_f = (c0)+(c1)+(c2)")
but never quoted, and Definition RC — a NEW predicate introduced in this
file, whose exact content the R2 charge asks to be verified — is defined
by shape-reference to it. A standalone verifier can confirm
non-circularity for any reasonable polygon-side-datum reading of (c1)
(done above), but cannot confirm well-formedness of (RC-read) itself
(e.g. that (c1)'s shape datum is exactly the 5-tuple (e, h, ℓ, s, u) and
that "sel = ⊥ in place of a selection" type-checks against it). One
displayed quotation of (c1) closes this. Gap, low.

### M5 — MINOR: two overstating labels inside §9.3(iii)

* Quoted: "the extension map now READS ν; the appended record carries
  ν's data." It carries ν's VERDICT data only ((E_ν, F_ν)); λ_{k'+1} is a
  function of (f, c) and ν's shape fields are not in the image. §2's R2
  note says it right ("carries ν's verdict data"); the (iii) preamble
  overstates. Harmless given (iii-a)'s precise granularity label, but the
  two sentences disagree.
* Quoted: "**(iii-a) [unconditional; …]**" and §9.5's "unconditional at
  (𝐇°, announced-pair) level (iii-a)". (iii-a) consumes Lemma R
  (P(O-2a r5)) and, for Θ^τ's well-definedness at k' ≥ 1, the ι/OL-1 read
  behind (i). "Unconditional" evidently means "no RC hypothesis", and
  §9.5's blanket conditionality covers the lemma as a whole — but a
  consumer told to "pick their granularity explicitly" could read the
  label as exemption from the blanket. One qualifier ("unconditional
  GIVEN the lemma's standing row") closes it.

### M6 — MINOR: §10's F3 row attributes to R2 an edit half of which predates the R2 commit

The §2 R2 note's seam-pair sentence and the Definition-RC reference were
committed at 52d4eed, the (t-ii)-entry-format sentence at 567814d; §10
presents them as one R2 disposition. The final text is what it claims to
be; only the "in place at R2" narrative compresses two commits into one.
No content consequence; recorded for the diff-record's accuracy only.

## 3. Verdict and what it prices

**VERDICT: SOUND-WITH-GAPS.**

* The R2 repairs discharge the pass-1 F1 critical and F2 root as claimed:
  no critical error survives in §9's R2 text. Lemma CU-2t as stated over
  RC-consistent seam objects — clauses (i), (ii), (iii-a), (iii-b), (iv)
  — is sound as displayed, at its displayed conditionality.
* The gaps G1/G2 concentrate on the EMITTED-side tie (§9.4): the bridge
  from "the run emitted this record" to "this record is RC-consistent"
  is one supply row short ((RC-read) for emitted records) and one
  disambiguation short ((T-DEC) vs the corner booking). Both are
  GD-4-grade bookkeeping, same family as the two rows R2 already priced —
  so the honest pricing is "GD residue + THREE GD-4 terminal rows, one of
  them ((T-DEC)) needing a corner disambiguation", and the four
  ledger/ROOT touches of §9.5 should be amended accordingly by their
  executor.
* G3 adds one owed pointer (route the W3 carrier finding + the 2(D)
  scope question to the O-2a owner for the P(O-2a r5) pass); G4 asks one
  quotation ((c1)) be displayed in §9.2a.
* Grade implication: CU-2t stays PROVED-UNVERIFIED after this pass —
  this is one hostile pass with gaps, not the required consecutive clean
  passes; the seam-object lemma core is confirmed sound, the emitted-side
  tie needs the G1/G2 repairs before a clean pass is available.

*Verifier: fresh-context Fable (CU2tpass), 2026-07-31. Nothing fixed;
no file other than this report touched.*
