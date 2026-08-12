# T4 — THE CERTIFICATE WITNESS
## One touched-coordinate definition for GENTOW-3’s \(\Theta_j\) threshold and GENTOW-6’s CERT-TOP
### COMPOSITION unit S-3, 2026-08-12

**STATUS: COMPLETE at attempt grade 0/2. Hostile arc owed.**  
**SOURCES:** GENTOW-3 and GENTOW-6 at HEAD, including their dated repairs and appends through 2026-08-12.  
**CHARGE:** define the certificate meaning of “touched coordinate” once; prove one attainment lemma; record GENTOW-3’s threshold certificate and GENTOW-6’s CERT-TOP as literal instances without strengthening either source’s scope.

## S0. SETTING AND NOTATION

Work in the full-side tower setting shared by GENTOW-3 and the certificate part of GENTOW-6. Thus

\[
D'=e_1f_1,\qquad E_2=e_2f_2u_2,\qquad
\delta=u_2-e_2D'h\ge 1,
\]

and for each composed coordinate \(j<\mu_2\),

\[
\Theta_j=(\mu_2-j)E_2+\delta.
\]

The composed key is read in the corrected gauge:

\[
\widehat c_t=\operatorname{lift}\!\left(c_t\eta^{W(t)}\right),
\qquad
W(t)=\left\lfloor\frac{(f_2-t)i(u_2)}{e_1}\right\rfloor ,
\]

with the exact-height lift interpretation at \(f_1\ge2\).

For a member \(f\), write

\[
f=\Phi_2^{\mu_2}+\sum_{j<\mu_2} C_j(f)\Phi_2^j
\]

for its honest composed development, and let \(\operatorname{Sh}C_j(f)\) be the stage-shadow coordinate obtained by the \(K_2(x,Y)\)-division over \(\widehat{\mathcal O}[x]/(\Phi')\). Put

\[
\Delta_j(f):=\operatorname{Sh}C_j(f)-C_j(f).
\]

For any coordinate digit string \(A\), let

\[
\operatorname{gr}_m(A)
\]

denote its canonical assembled digit at \(dv_2\)-height \(m\): all branches, carries, recarries, and terms landing in the same canonical \(K_2\)-slot at height \(m\) are added before the class is taken. Thus cancellation inside a slot is already reflected in \(\operatorname{gr}_m(A)\); distinct canonical slots form separate components. The exact-height separation supplied by GENHN-2′ makes this graded digit unambiguous.

The distinguished certificate member is

\[
f_{\mathrm{key}}:=\Phi_2^{\mu_2}.
\]

Its honest coordinates vanish:

\[
C_j(f_{\mathrm{key}})=0\qquad(j<\mu_2).
\]

## S1. DEFINITION — THE CERTIFICATE WITNESS

> **DEFINITION T4.1 (touched coordinate; certificate sense).**  
> For each \(j<\mu_2\), define the certificate witness
>
> \[
> \omega_j
> :=
> \operatorname{gr}_{\Theta_j}
> \bigl(\Delta_j(f_{\mathrm{key}})\bigr)
> =
> \operatorname{gr}_{\Theta_j}
> \bigl(\operatorname{Sh}C_j(\Phi_2^{\mu_2})\bigr).
> \]
>
> Equivalently, \(\omega_j\) is the fully assembled height-\(\Theta_j\)
> \(K_2\)-digit obtained from all single-\(\Phi'\)-extraction routes
> of the key power, after every collision and cancellation in the
> canonical composed grid.
>
> The coordinate \(j\) is **touched** iff
>
> \[
> \omega_j\ne0.
> \]
>
> It is **untouched** iff \(\omega_j=0\).

This is the certificate reading pinned by GENTOW-3’s GT3-r2 repair. It is deliberately stronger than either of the following informal readings:

- \(\operatorname{Sh}C_j(\Phi_2^{\mu_2})\ne0\);
- some unassembled single-extraction branch is nonzero.

A shadow coordinate may be nonzero while its height-\(\Theta_j\) digit cancels. FR-M3 at \(j=0\) is the committed separator: the self-shadow has pin \(12\), but \(\Theta_0=10\) and \(\omega_0=0\).

## S2. LEMMA — CERTIFICATE ATTAINMENT

> **LEMMA T4.2 (certificate witness and threshold attainment).**  
> Assume the GENTOW-3 discrepancy floor
>
> \[
> \operatorname{gr}_m(\Delta_j(f))=0
> \qquad\text{for every }m<\Theta_j
> \tag{FLOOR}
> \]
>
> at each coordinate \(j\). Then:
>
> **(a) Exact attainment for the key power.**
>
> \[
> j\text{ is touched}
> \quad\Longleftrightarrow\quad
> \min\{m:\operatorname{gr}_m(\Delta_j(f_{\mathrm{key}}))\ne0\}
> =\Theta_j.
> \]
>
> Thus a touched coordinate attains the GENTOW-3 floor exactly.
> At an untouched coordinate the key power’s first discrepancy is
> strictly above \(\Theta_j\), or the discrepancy is identically
> zero.
>
> **(b) Perturbation stability.** If
>
> \[
> f=f_{\mathrm{key}}+g
> \]
>
> and
>
> \[
> \operatorname{gr}_{\Theta_j}(\Delta_j(g))=0,
> \]
>
> then
>
> \[
> \operatorname{gr}_{\Theta_j}(\Delta_j(f))=\omega_j.
> \]
>
> In particular, GENTOW-3’s in-budget hypothesis implies this
> vanishing: its repaired margin ledger places every discrepancy
> of \(g\) at height at least \(\Theta_j+1\). Hence every touched
> coordinate remains divergent exactly at \(\Theta_j\) under an
> in-budget perturbation.
>
> **(c) Exposed-slot criterion.** Suppose a canonical slot of
> coordinate \(j\) at height \(\Theta_j\) receives exactly one
> single-extraction contribution and that contribution has
> nonzero normalized digit. Then \(\omega_j\ne0\), so \(j\) is
> touched and the floor is attained there.
>
> **(d) No-source criterion.** If no source monomial can undergo
> a single \(\Phi'\)-extraction into coordinate \(j\) at height
> \(\Theta_j\), or if the complete assembled contribution cancels,
> then \(\omega_j=0\). No attainment statement for another member
> follows: entry-driven content may still attain \(\Theta_j\).

*Proof.* By (FLOOR), the key-power discrepancy has no nonzero digit
below \(\Theta_j\). Its first discrepancy is therefore exactly
\(\Theta_j\) iff its height-\(\Theta_j\) graded digit is nonzero,
which is precisely the definition of \(\omega_j\ne0\). This proves
(a).

Both reads are linear in the dividend, so

\[
\Delta_j(f_{\mathrm{key}}+g)
=
\Delta_j(f_{\mathrm{key}})+\Delta_j(g).
\]

Taking the height-\(\Theta_j\) graded component proves (b). The
in-budget specialization is GENTOW-3 S8.1’s repaired ledger:
starting one weight unit above the key-power source layer and
adding one extraction cost \(\delta\) places every perturbation
discrepancy at least one height above \(\Theta_j\).

For (c), the selected slot is a nonzero component of the assembled
graded digit and has no second contribution with which to cancel.
Hence \(\omega_j\ne0\). Clause (d) is the definition after complete
assembly. Its final warning is necessary because \(\omega_j\)
classifies the key-power witness, not all members of the genre. ∎

## S3. INSTANCE RECORD — GENTOW-3’S \(\Theta_j\) THRESHOLD

<!-- T4-INSTANCE-GT3:BEGIN -->

**Instance name:** `GT3-THRESHOLD`.

**Substitution.**

\[
\Delta_j=\operatorname{Sh}C_j-C_j,\qquad
\Theta_j=(\mu_2-j)E_2+\delta,
\]

with \(\delta=u_2-e_2D'h\), and with \(\omega_j\) the key power’s
assembled single-\(\Phi'\)-extraction digit.

**Consumed facts.**

1. GENTOW-3(i) supplies (FLOOR).
2. GENTOW-3(iv), read through GT3-r2 and GT3-r3, supplies the
   per-genre, per-coordinate computation of \(\omega_j\).
3. GENTOW-3 S8.1 supplies the \(\Theta_j+1\) perturbation margin
   used in LEMMA T4.2(b).
4. GENTOW-3(iii) gives the x-free extreme: every discrepancy is
   zero, hence every \(\omega_j=0\).

**Result.** GENTOW-3(iv)’s phrase “touched coordinate(s)” is exactly
DEFINITION T4.1. Its attainment conclusion is LEMMA T4.2(a), and
its repaired deep-perturbation persistence is LEMMA T4.2(b).

The instance is one-sided at member level. If \(\omega_j=0\), the
key power does not attain the floor at \(j\); this does not imply
that no other member can attain it. The committed FR-M3 \(W\)
member does attain \(\Theta_0=10\) through entry-driven content
although the key-power certificate at \(j=0\) cancels.

**Measured configurations retained by this instance.**

- **Attained:** FAM-A5/A7/B/C and FR-GL have \(\omega_j\ne0\) at
  the recorded coordinates.
- **Cancelled with slack:** FR-M3 has thresholds
  \([10,7,4]\), self-shadow pins \([12,7,4]\), hence
  \(\omega_0=0\) and \(\omega_1,\omega_2\ne0\).
- **Identically zero:** FR5X supplies coordinates on which the
  complete self-shadow coordinate vanishes.
- **Other-member attainment at an untouched key-power
  coordinate:** the FR-M3 \(W\) member has first discrepancy
  \(10=\Theta_0\); this is compatible with T4.2(d).

**Marker-delimited source pins, HEAD.**

Source:
`GENTOW3_PROOF_2026-08-09.md`.

The governing semantic stack is the ordered union of these
half-open spans:

1. BEGIN substring  
   `## S0. THE ONE CONSTANT AND THE THRESHOLD`  
   END substring  
   `## S3. COROLLARY GENTOW-3.C`

2. BEGIN substring  
   `## S7.6 [GT3-r2] PE2 REPAIR RECORD:`  
   END substring  
   `## S7.7 [GT3-r3] PE3 REPAIR RECORD:`

3. BEGIN substring  
   `## S7.7 [GT3-r3] PE3 REPAIR RECORD:`  
   END substring  
   `### Dated acceptance record`

4. BEGIN substring  
   `### S8.1 [B-F1, GAP] Clause (iv)'s deep-perturbation persistence:`  
   END substring  
   `### S8.2 [B-F2, GAP]`

The later S8.2/S8.4 non-functionality scope is not consumed by
this instance.

<!-- T4-INSTANCE-GT3:END -->

## S4. INSTANCE RECORD — GENTOW-6’S CERT-TOP

<!-- T4-INSTANCE-GT6:BEGIN -->

**Instance name:** `GT6-CERT-TOP`.

### S4.1 The sealed \(f_1=1,\ \mu_2=2\) instance

Let

\[
T=\{t<f_2:\widehat c_t\ne0\},\qquad t^*=\max T,
\]

and write the lift monomial at \(t\) as

\[
\widehat c_t\,\pi^{a_t}x^{i_t}.
\]

Assume

\[
2i_{t^*}\ge D'.
\]

The \((t^*,t^*)\) pair has a direct single-\(\Phi'\)-extraction
into

\[
j^*=
\left\lfloor
\frac{2e_2t^*+1}{e_2f_2}
\right\rfloor ,
\qquad
b^*=(2e_2t^*+1)\bmod e_2f_2,
\qquad
a^*=2i_{t^*}-D'.
\]

Its normalized digit is

\[
(\widehat c_{t^*})^2\pi^{2a_{t^*}}
\cdot(\text{wrap unit}),
\]

which is nonzero. Maximality of \(t^*\) makes this the unique
height-\(\Theta_{j^*}\) branch in the displayed slot. LEMMA
T4.2(c) therefore gives

\[
\omega_{j^*}\ne0,
\]

so \(j^*\) is touched and the discrepancy first occurs at

\[
\Theta_{j^*}=(2-j^*)E_2+\delta.
\]

This is GENTOW-6.3(b), CERT-TOP, as a literal exposed-slot instance
of the certificate-witness lemma.

If

\[
i_t+i_{t'}<D'
\qquad\text{for every }(t,t')\in T^2,
\]

there is no overflowing pair. GENTOW-6.3(c) proves the stronger
conclusion \(\operatorname{Sh}C_j=C_j=0\) for every \(j\), hence
every coordinate is untouched. Between these regimes, an
assembled pair sum can vanish; no universal non-cancellation is
asserted.

### S4.2 The corrected-lift \(f_1\)-general instance

For

\[
L_{m_t}(c_t\eta^{W(t)})
=
\sum_{r<f_1}
\widetilde\lambda_{t,r}\,
\pi^{a_t-rh}x^{i_t+e_1r},
\]

put

\[
I_t=i_t+e_1r_{\max}(t).
\]

Under

\[
2I_{t^*}\ge D',
\]

ANNEX-THEOREM GENTOW-6.3′ isolates the unique top-monomial slot

\[
(a^*,b^*)
=
\left(
2I_{t^*}-D',
\ (2e_2t^*+1)\bmod e_2f_2
\right)
\]

in coordinate \(j^*\), with digit

\[
\widetilde\lambda_{t^*,r^*}^{\,2}
\pi^{2(a_{t^*}-r^*h)}
\cdot(\text{wrap unit}),
\qquad r^*=r_{\max}(t^*).
\]

It is nonzero and uniquely exposed. Thus T4.2(c) again gives
\(\omega_{j^*}\ne0\). At \(f_1=1\), \(I_t=i_t\) and this
specializes to S4.1.

The dated GENTOW6-BOX-4 append supplies sealed-battery-grade
machine contact for this corrected-lift instance at four
\(f_1=2\), x-ful rows. It does not change the logical form of the
instance or erase the source note’s prose-grade ledger for the
annex derivation.

### S4.3 The later \(\mu_2\ge3\) refinement

GENTOW-6.5’s \(f_1=1\) refinement computes a distinguished
certificate-slot component proportional to

\[
\binom{\mu_2}{2}
(\widehat c_{t^*})^2\pi^{2a_{t^*}}
\cdot(\text{wrap unit}).
\]

When the residue characteristic does not divide
\(\binom{\mu_2}{2}\), this component is nonzero and proves
touchedness by T4.2(c). The converse is not retained: cancellation
of that particular slot does not imply \(\omega_j=0\), because
another slot may attain the same coordinate’s floor. The committed
BP3 and FR5X measurements exhibit the two possible outcomes.

**Marker-delimited source pins, HEAD.**

Source:
`GENTOW6_PROOF_2026-08-09.md`.

The governing semantic stack is the ordered union of these spans:

1. BEGIN substring  
   `## S3. THEOREM GENTOW-6.3`  
   END substring  
   `## S4. MACHINE LEG`

2. BEGIN substring  
   `### S6.1 THE DATED GAUGE ANNEX`  
   END substring  
   `### S6.2 THE 𝒯-FREE CAP LEMMA`

3. BEGIN substring  
   `**GENTOW6-BOX-1 (mu2 >= 3 attainment): CLOSED AT f1 = 1**`  
   END substring  
   `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):`

4. BEGIN substring  
   `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):`  
   END substring  
   `6.3' keeps its prose-only grading in the note's own terms.`

<!-- T4-INSTANCE-GT6:END -->

## S5. FAIL-CLOSED PIN CONVENTION

Every pin above is interpreted byte-literally against the named
source at the revision being consumed.

A pin resolves only if:

1. its BEGIN substring occurs exactly once;
2. its END substring occurs exactly once;
3. BEGIN precedes END;
4. the resolved span belongs to the named source;
5. the spans in one semantic stack occur in the recorded order;
6. no later dated rider or append inside or after the pinned stack
   supersedes a consumed assertion.

If any condition fails, the instance is **UNRESOLVED** and
consumption stops. The orchestrator must not substitute a nearby
heading, normalize punctuation, choose among multiple matches, or
fall back to an earlier revision. A source edit that changes,
duplicates, removes, or reorders a marker therefore fails closed
and requires an explicit T4 pin update plus re-verification.

The HTML instance markers in this note delimit the complete
consumer records. They are not substitutes for validation of the
source markers.

## S6. COMPRESSION AND CONSUMPTION

After T4 is accepted, the following local arguments may be
shortened to instance records:

- GENTOW-3’s local definition of “touched coordinate(s)” and its
  floor-attainment inference become `GT3-THRESHOLD`;
- GENTOW-6.3(b)’s final implication from the unique CERT-TOP slot
  to threshold attainment becomes `GT6-CERT-TOP`;
- GENTOW-6.3′ and the later \(\mu_2\ge3\) certificate computation
  use the same exposed-slot clause with their recorded scopes.

The algebra that computes a proposed witness is not deleted:
GENTOW-6 still owns the top-slot uniqueness calculation, the
corrected-lift support calculation, and the higher-\(\mu_2\)
binomial coefficient. T4 owns only the shared meaning of the
assembled witness and the inference from a nonzero critical digit
to attainment.

No accepted source is rewritten by this composition unit. The
orchestrator’s later consumption update must preserve the frozen
source notes through dated references or brackets.

## S7. HONESTY LEDGER

**Delivered here.**

- One canonical definition of touched coordinate in the
  certificate sense.
- One attainment lemma, including the repaired perturbation
  margin and the exposed-slot test.
- Two source-scoped instance records.
- Fail-closed, marker-delimited source pins.
- A single home for later certificate and count refinements.

**Not claimed.**

- No genre-general non-vanishing theorem beyond the hypotheses
  already proved in GENTOW-6.
- No converse to CERT-TOP.
- No claim that an untouched key-power coordinate cannot be
  reached by another member.
- No claim that \(\operatorname{Sh}C_j\ne0\) implies touchedness.
- No promotion of GENTOW-6.3’s sealed \(f_1=1\) statement to
  \(f_1\ge2\); that scope remains the corrected-lift annex.
- No promotion of the \(\mu_2\ge3\) sufficient condition to an
  iff.
- No closure of entry-driven regime classification.
- No new count theorem.

**Residue home.**

- `GENTOW6-BOX-1`: lower-coordinate and compound
  \(f_1\ge2,\mu_2\ge3\) certificate classification.
- `GENTOW6-BOX-2`: the partial-side product-measure count ledger.
- `GENTOW6-BOX-3`: entry-driven and non-top-overflow
  classification.
- `GENTOW6-BOX-4`: its stated sealed-row ask is discharged at
  HEAD, but any widening of corrected-lift certificate coverage
  belongs here.
- `GENTOW3-BOX-1`: the original genre-general non-cancellation ask
  is replaced, not magically solved, by the explicit witness
  \(\omega_j\); deciding its vanishing outside the proved
  CERT-TOP regimes remains refinement work.

**Evidence status.** This note adds no machine computation. Its
regression evidence is inherited from the byte-frozen GENTOW-3
and GENTOW-6 artifacts and their dated hostile-arc instruments.
Those artifacts support the two instance checks; they are not
fresh evidence for a stronger theorem.

**GRADE: 0/2 (attempt).** The definition and lemma are new
composition text. Two consecutive clean hostile passes are
required before acceptance.

## S8. HOSTILE ARC PLAN

### Pass PE1 — statement and scope attack

The first adversarial pass must check:

1. that \(\operatorname{gr}_{\Theta_j}\) is taken after complete
   slot assembly and cancellation;
2. that T4.2(a) uses the GENTOW-3 floor and does not infer a
   member-general converse;
3. that T4.2(b) uses the repaired S8.1 margin, not the withdrawn
   “same shift” inference;
4. that the \(f_1=1\), corrected-lift \(f_1\)-general, and
   \(\mu_2\ge3\) scopes remain separated;
5. that CERT-TOP is used as a sufficient exposed-slot witness;
6. that the higher-\(\mu_2\) binomial condition is not stated as
   necessary;
7. that every marker pin resolves uniquely and in order.

A finding of GAP or CRITICAL resets the counter to 0/2. Repairs
must be re-derived from the pinned source spans.

### Pass PE2 — independent consumption and regression attack

After a clean PE1, the second pass must re-resolve every pin and
perform two consumption checks:

- **GT3 consumption:** recover GENTOW-3(iv)’s certificate-scoped
  attainment and S8.1 persistence solely by substituting
  DEFINITION T4.1 and LEMMA T4.2. Re-run the accepted GENTOW-3
  battery and specifically inspect FR-M3’s measured slack
  \([12,7,4]\) against \([10,7,4]\), the \(W\)-member’s
  entry-driven attainment at \(j=0\), FR-GL’s two-coordinate
  attainment, and FR5X’s identically-zero coordinates.

- **GT6 consumption:** recover CERT-TOP solely through T4.2(c)
  after retaining GENTOW-6’s source-slot uniqueness calculation.
  Re-run the accepted GENTOW-6 battery, the corrected-lift
  \(f_1=2\) BOX-4 rows, the gauge-live \(\eta\ne1\) rows, and the
  no-overflow FAM-E/FAM-D controls. Check the BP3 and FR5X
  higher-\(\mu_2\) rows against the one-sided binomial statement.

Acceptance requires PE1 CLEAN followed by PE2 CLEAN. Minor-only
riders may be folded without changing the theorem statement;
anything that changes the meaning of touchedness, the threshold
layer, or an instance scope requires a new repair round and
restarts the two-clean counter.

---

**Composition record, 2026-08-12.** T4 makes no source-file edit
and no artifact edit. Its sole mathematical compression is:

\[
\boxed{
\text{touched at }j
\;:\Longleftrightarrow\;
\omega_j\ne0
\;\Longrightarrow\;
\text{first discrepancy at }\Theta_j
}
\]

with the converse at the key power supplied by the discrepancy
floor, and with GENTOW-6’s CERT-TOP serving as an explicit,
unique-slot proof that \(\omega_{j^*}\ne0\).


---

## r1 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp6/T4R1_output.log; transcribed unaltered; counter resets.)*

Four verbatim-ready r1 repairs follow. C1 remains operationally unresolved; its repair makes T4 correctly fail closed without alleging a marker mismatch.

### R1-C1 — fail-closed pin status

Replace the status line with:

```markdown
**STATUS: R1 TEXT REPAIRED; UNRESOLVED at attempt grade 0/2.**
No clean hostile pass has been earned. Both instance records remain
non-consumable until their HEAD pins are successfully validated.
```

Insert after S5’s numbered conditions:

```markdown
### S5.1 R1 PIN-VALIDATION RECORD — UNRESOLVED

On 2026-08-12, byte-literal validation was attempted against the
two named HEAD sources. The workspace command runner failed before
either source could be read because `bubblewrap is unavailable`.

Consequently none of the eight listed half-open spans—four in the
GT3 stack and four in the GT6 stack—was checked for occurrence
count, source identity, byte order, stack order, or later
supersession. Under the convention above, `GT3-THRESHOLD` and
`GT6-CERT-TOP` are therefore **UNRESOLVED**, and consumption stops.

This is an infrastructure result. It is neither evidence that a
marker mismatches nor a clean hostile pass. The acceptance counter
remains 0/2.

A later validation record may supersede this rider only after it
reports, for every listed BEGIN and END substring, its exact
occurrence count and resolved byte position, verifies the recorded
stack order, and checks all later dated riders and appends for
supersession.
```

### R1-G2 — define the perturbation domain

Replace S0 from “For a member \(f\), write” through the statement of the key’s honest coordinates with:

```markdown
Let \(\mathscr D_{\le\mu_2}\) be the ambient module of dividends to
which the composed \(K_2(x,Y)\)-division applies and whose honest
\(\Phi_2\)-development has degree at most \(\mu_2\). For
\(q\in\mathscr D_{\le\mu_2}\), write uniquely

\[
q=\sum_{k\le\mu_2}C_k(q)\Phi_2^k.
\]

Let

\[
\mathscr D_{<\mu_2}
:=
\{q\in\mathscr D_{\le\mu_2}:C_{\mu_2}(q)=0\}.
\]

The member family lies in the affine slice
\(C_{\mu_2}(q)=1\), while differences of members with the same
leading key power lie in \(\mathscr D_{<\mu_2}\).

For every \(q\in\mathscr D_{\le\mu_2}\), define
\(\operatorname{Sh}C_j(q)\) to be the \(j\)-th stage-shadow
coordinate produced by applying the \(K_2(x,Y)\)-division over
\(\widehat{\mathcal O}[x]/(\Phi')\) to the dividend \(q\). Thus

\[
C_j,\operatorname{Sh}C_j:
\mathscr D_{\le\mu_2}\longrightarrow\mathscr A_j
\]

are the coefficient maps of two linear division operators. Put

\[
\Delta_j(q):=\operatorname{Sh}C_j(q)-C_j(q)
\qquad(q\in\mathscr D_{\le\mu_2}).
\]

This is the required linear extension of the notation from the
member affine slice to lower perturbations; in particular,
\(\Delta_j(g)\) is defined for
\(g\in\mathscr D_{<\mu_2}\).

The distinguished certificate member is

\[
f_{\mathrm{key}}:=\Phi_2^{\mu_2}.
\]

It belongs to \(\mathscr D_{\le\mu_2}\), and its honest lower
coordinates vanish:

\[
C_j(f_{\mathrm{key}})=0\qquad(j<\mu_2).
\]
```

Replace the opening of T4.2(b)’s proof with:

```markdown
By the definitions in S0, \(C_j\) and
\(\operatorname{Sh}C_j\) are linear maps on
\(\mathscr D_{\le\mu_2}\); hence so is \(\Delta_j\). Therefore,
for \(g\in\mathscr D_{<\mu_2}\),

\[
\Delta_j(f_{\mathrm{key}}+g)
=
\Delta_j(f_{\mathrm{key}})+\Delta_j(g).
\]
```

### R1-m1 — totalize first-discrepancy height

Insert immediately before LEMMA T4.2:

```markdown
For \(q\in\mathscr D_{\le\mu_2}\), define its first discrepancy
height at coordinate \(j\) by

\[
\nu_j(q)
:=
\min\{m:\operatorname{gr}_m(\Delta_j(q))\ne0\},
\]

with the convention

\[
\min\varnothing:=+\infty.
\]

Thus \(\nu_j(q)=+\infty\) exactly when
\(\Delta_j(q)\) is identically zero.
```

Replace T4.2(a) with:

```markdown
**(a) Exact attainment for the key power.**

\[
j\text{ is touched}
\quad\Longleftrightarrow\quad
\nu_j(f_{\mathrm{key}})=\Theta_j.
\]

Thus a touched coordinate attains the GENTOW-3 floor exactly.
At an untouched coordinate,

\[
\nu_j(f_{\mathrm{key}})>\Theta_j,
\]

where \(+\infty>\Theta_j\) includes the case of an identically
zero discrepancy.
```

Replace the first proof paragraph with:

```markdown
By (FLOOR),

\[
\nu_j(f_{\mathrm{key}})\ge\Theta_j.
\]

Equality holds exactly when the height-\(\Theta_j\) assembled
graded digit is nonzero. That digit is \(\omega_j\), so

\[
\nu_j(f_{\mathrm{key}})=\Theta_j
\quad\Longleftrightarrow\quad
\omega_j\ne0.
\]

This proves (a), including the identically-zero case through the
convention \(\nu_j(f_{\mathrm{key}})=+\infty\).
```

### R1-G1 — expose the higher-\(\mu_2\) slot explicitly

Replace S4.3 in full with:

```markdown
### S4.3 The later \(\mu_2\ge3\) refinement

GENTOW-6.5’s \(f_1=1\) refinement computes, in a distinguished
canonical certificate slot of some coordinate \(j\) at height
\(\Theta_j\), a single-extraction contribution proportional to

\[
\binom{\mu_2}{2}
(\widehat c_{t^*})^2\pi^{2a_{t^*}}
\cdot(\text{wrap unit}).
\tag{6.5-CAND}
\]

For the exposed-slot inference, impose the additional hypothesis

\[
\tag{EXPOSE-6.5}
\text{the slot containing \((6.5\text{-CAND})\) receives exactly
one single-extraction contribution.}
\]

Equivalently, under (EXPOSE-6.5), the displayed expression is the
complete assembled value of that canonical slot, rather than one
unassembled summand of it.

If the residue characteristic does not divide
\(\binom{\mu_2}{2}\), then the displayed contribution is nonzero.
Together with (EXPOSE-6.5), T4.2(c) gives

\[
\omega_j\ne0,
\]

so \(j\) is touched and its discrepancy first occurs at
\(\Theta_j\).

Without (EXPOSE-6.5), nonvanishing of the displayed contribution
alone proves no touchedness statement: another contribution may
land in the same canonical slot and cancel it after assembly.
Accordingly, if GENTOW-6.5 supplies only the computation
\((6.5\text{-CAND})\) and not the exposure hypothesis, T4 records
that expression only as a candidate witness and does not invoke
T4.2(c).

No converse is retained. Vanishing of this particular assembled
slot, when it is assembled, does not imply \(\omega_j=0\), because
another canonical slot may attain the same coordinate’s floor.
The committed BP3 and FR5X measurements exhibit the two possible
outcomes.
```

No files were changed, and no claim of successful HEAD-pin validation is made.


---

## r2 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp8/T4R2_output.log; transcribed unaltered; counter resets.)*

Two criticals come first. The HEAD-pin critical remains operationally blocked; claiming it repaired would be false. The remaining five findings have merge-ready repairs below.

## R2-C1 — HEAD-pin validation remains blocked

Replace S5.1 with:

```markdown
### S5.1 R2 PIN-VALIDATION RECORD — UNRESOLVED

On 2026-08-12, a fresh byte-literal validation attempt was made
against the two named HEAD sources. The workspace command runner
again failed before either source could be read because
`bubblewrap is unavailable`.

Consequently none of the eight listed half-open spans—four in the
GT3 stack and four in the GT6 stack—has been checked for occurrence
count, source identity, byte position, span order, stack order, or
later supersession. Under S5, `GT3-THRESHOLD` and
`GT6-CERT-TOP` remain **UNRESOLVED**, and consumption stops.

This supersedes the R1 pin-validation record only as a record of
the latest attempt. It is not a successful validation, does not
satisfy PE1 condition 7, and earns no hostile-pass credit. The
acceptance counter remains 0/2.

Only a later validation record reporting the exact occurrence
count and byte position of every listed BEGIN and END substring,
verifying all span and stack orders, and auditing all later dated
riders and appends for supersession may replace this unresolved
status.
```

This is an accurate fail-closed record, not a resolution of C1. A fresh command attempt again failed at the `bubblewrap` boundary before either source was read.

## R2-C2 — restore the deleted definition of \(\operatorname{gr}_m\)

In the R1-G2 replacement for S0, insert immediately after

```markdown
\[
\Delta_j(q):=\operatorname{Sh}C_j(q)-C_j(q)
\qquad(q\in\mathscr D_{\le\mu_2}).
\]
```

the following:

```markdown
For any coordinate digit string \(A\), let

\[
\operatorname{gr}_m(A)
\]

denote its canonical assembled digit at \(dv_2\)-height \(m\):
all branches, carries, recarries, and terms landing in the same
canonical \(K_2\)-slot at height \(m\) are added before the class
is taken. Thus cancellation inside a slot is already reflected in
\(\operatorname{gr}_m(A)\), while distinct canonical slots form
separate components. The exact-height separation supplied by
GENHN-2′ makes this graded digit unambiguous.
```

Also replace:

```markdown
It belongs to \(\mathscr D_{\le\mu_2}\), and its honest lower
coordinates vanish:
```

with:

```markdown
It is a member, hence belongs to
\(\mathscr D_{\le\mu_2}\), and its honest lower coordinates
vanish:
```

This restores every operation used by \(\omega_j\), (FLOOR), and \(\nu_j\), and makes the key-power specialization below explicit.

## R2-G1 — bind the FLOOR variable

Replace the opening of LEMMA T4.2, from “Assume the GENTOW-3 discrepancy floor” through “Then:”, with:

```markdown
> **LEMMA T4.2 (certificate witness and threshold attainment).**  
> Assume the GENTOW-3 discrepancy floor holds for every member:
>
> \[
> \operatorname{gr}_m(\Delta_j(f))=0
> \qquad
> \text{for every member \(f\), every \(j<\mu_2\), and every
> \(m<\Theta_j\).}
> \tag{FLOOR}
> \]
>
> Then, for each \(j<\mu_2\):
```

Replace the first proof paragraph supplied by R1-m1 with:

```markdown
Because \(f_{\mathrm{key}}\) is a member, (FLOOR) specializes to

\[
\operatorname{gr}_m
\bigl(\Delta_j(f_{\mathrm{key}})\bigr)=0
\qquad(m<\Theta_j).
\]

Hence

\[
\nu_j(f_{\mathrm{key}})\ge\Theta_j.
\]

Equality holds exactly when the height-\(\Theta_j\) assembled
graded digit is nonzero. That digit is \(\omega_j\), so

\[
\nu_j(f_{\mathrm{key}})=\Theta_j
\quad\Longleftrightarrow\quad
\omega_j\ne0.
\]

This proves (a), including the identically-zero case through the
convention \(\nu_j(f_{\mathrm{key}})=+\infty\).
```

## R2-G2 — put the perturbation domain in T4.2(b)

Replace T4.2(b) in full with:

```markdown
> **(b) Perturbation stability.** Let
>
> \[
> g\in\mathscr D_{<\mu_2},
> \qquad
> f:=f_{\mathrm{key}}+g,
> \]
>
> and suppose that \(f\) is a member. If
>
> \[
> \operatorname{gr}_{\Theta_j}(\Delta_j(g))=0,
> \]
>
> then
>
> \[
> \operatorname{gr}_{\Theta_j}(\Delta_j(f))=\omega_j.
> \]
>
> In particular, if \(g\) satisfies GENTOW-3’s in-budget
> hypotheses, so that \(f_{\mathrm{key}}+g\) is a member, its
> repaired margin ledger places every discrepancy of \(g\) at
> height at least \(\Theta_j+1\). Hence every touched coordinate
> remains divergent exactly at \(\Theta_j\) under such an
> in-budget perturbation.
```

Replace T4.2(b)’s proof paragraph with:

```markdown
Let \(g\in\mathscr D_{<\mu_2}\) and let
\(f=f_{\mathrm{key}}+g\) be a member. By the definitions in S0,
\(C_j\) and \(\operatorname{Sh}C_j\) are linear maps on
\(\mathscr D_{\le\mu_2}\); hence so is \(\Delta_j\). Therefore

\[
\Delta_j(f)
=
\Delta_j(f_{\mathrm{key}})+\Delta_j(g).
\]

Taking the height-\(\Theta_j\) graded component proves the first
assertion of (b). Under GENTOW-3’s in-budget hypothesis, S8.1’s
repaired ledger places every perturbation discrepancy at height
at least \(\Theta_j+1\), so the required graded component of
\(\Delta_j(g)\) vanishes. If \(j\) is touched, the resulting
height-\(\Theta_j\) digit is \(\omega_j\ne0\); (FLOOR), applied
to the member \(f\), excludes every lower digit. Thus
\(\nu_j(f)=\Theta_j\).
```

## R2-G3 — downgrade GENTOW-6.5 from instance to candidate

Replace S4.3 in full with:

```markdown
### S4.3 The later \(\mu_2\ge3\) candidate

GENTOW-6.5’s \(f_1=1\) refinement computes a distinguished
single-extraction contribution proportional to

\[
\binom{\mu_2}{2}
(\widehat c_{t^*})^2\pi^{2a_{t^*}}
\cdot(\text{wrap unit}).
\tag{6.5-CAND}
\]

The source facts consumed by this record do not prove that the
canonical slot containing \((6.5\text{-CAND})\) receives exactly
one single-extraction contribution. They therefore do not
establish the exposed-slot premise of T4.2(c).

Accordingly, even when the residue characteristic does not divide
\(\binom{\mu_2}{2}\), the displayed nonzero expression is recorded
here only as an unassembled candidate witness. This instance does
not infer that \(\omega_j\ne0\), does not assert that \(j\) is
touched, and does not assert threshold attainment from
\((6.5\text{-CAND})\).

If a later source rider proves that this contribution is uniquely
exposed, that new assertion must be covered by an explicit pin
update and fresh validation before T4.2(c) may be invoked. Proof
that an expression is the complete assembled value of a slot
would prove touchedness directly when that value is nonzero, but
it is not equivalent to proving that the slot received exactly
one contribution: additional contributions may be present and
sum to zero.

No converse is retained. Vanishing or cancellation of this
candidate does not imply \(\omega_j=0\), because another canonical
slot may attain the same coordinate’s floor. The committed BP3
and FR5X measurements remain source measurements of the possible
outcomes; they are not exposed-slot instances supplied by this
record.
```

In S6, replace:

```markdown
- GENTOW-6.3′ and the later \(\mu_2\ge3\) certificate computation
  use the same exposed-slot clause with their recorded scopes.
```

with:

```markdown
- GENTOW-6.3′ uses the same exposed-slot clause within its recorded
  corrected-lift scope;
- the later \(\mu_2\ge3\) computation is not consumable through
  T4.2(c): it remains the candidate record of S4.3 unless a
  separately pinned and validated source assertion proves the
  required exposure premise.
```

This also repairs the minor false-equivalence claim: the new text states only the valid one-way implication and explicitly rejects its converse.

No files were changed. C1 remains an infrastructure blocker; the other five findings are repaired textually.


---

## r3 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp10/T4R3_output.log; transcribed unaltered; counter resets.)*

## r3 (2026-08-12): assembled-slot cancellation repair

### R3-G1 — strengthen exposure to exclude every assembled-slot input

Insert in S0 immediately after the definition of \(\operatorname{gr}_m\):

```markdown
A canonical slot is **fully exposed by a contribution \(\xi\)**
if, after every branch term and every incoming carry and recarry
has been propagated to the canonical grid, the complete list of
summands landing in that slot consists of \(\xi\) alone.

Full exposure therefore quantifies over contributions of every
provenance. Uniqueness merely among single-extraction
contributions does not imply full exposure.
```

In DEFINITION T4.1, replace the paragraph beginning
“Equivalently, \(\omega_j\) is” with:

```markdown
> Equivalently, \(\omega_j\) is the fully assembled
> height-\(\Theta_j\) \(K_2\)-digit of the key power. Its assembly
> includes every input landing in the canonical composed grid,
> including all single-\(\Phi'\)-extraction routes, all other
> branch terms, and every incoming carry and recarry. Every
> collision and cancellation is completed before the digit is
> taken.
```

Replace T4.2(c) in full with:

```markdown
> **(c) Fully exposed assembled-slot criterion.** Suppose a
> canonical slot of coordinate \(j\) at height \(\Theta_j\) is
> fully exposed by a single-extraction contribution whose
> normalized digit is nonzero. Then that slot is a nonzero
> component of \(\omega_j\). Consequently
>
> \[
> \omega_j\ne0,
> \]
>
> so \(j\) is touched and the floor is attained there.
>
> Uniqueness only among single-extraction contributions does not
> discharge this premise: the exposure calculation must also
> exclude every other term and every incoming carry or recarry
> from the slot.
```

Replace T4.2(c)’s proof paragraph with:

```markdown
For (c), full exposure says that, after complete propagation and
assembly, the selected slot has exactly the displayed
single-extraction contribution as its assembled value. No other
branch term, carry, or recarry supplies a summand that could alter
or cancel it. Its normalized digit is nonzero, so the selected
slot is a nonzero component of the height-\(\Theta_j\) assembled
graded digit. Distinct canonical slots are separate components;
hence \(\omega_j\ne0\).
```

In S4.1, replace the paragraph beginning “Maximality of \(t^*\)”
and ending with the displayed formula for \(\Theta_{j^*}\) with:

```markdown
Maximality of \(t^*\) excludes competing branches of the displayed
pair type. To invoke T4.2(c), the CERT-TOP slot-isolation
calculation must establish the stronger assembled-slot fact that,
after every branch term and every incoming carry and recarry has
been propagated, the displayed contribution is the sole summand
in its canonical height-\(\Theta_{j^*}\) slot.

When that source-owned calculation establishes this full
exposure, the nonzero displayed digit gives

\[
\omega_{j^*}\ne0
\]

by T4.2(c). Hence \(j^*\) is touched and the discrepancy first
occurs at

\[
\Theta_{j^*}=(2-j^*)E_2+\delta.
\]

If the pinned source span establishes uniqueness only among
single-extraction branches, the premise of T4.2(c) is not
discharged and `GT6-CERT-TOP` remains unresolved; neither FLOOR
nor maximality alone supplies the missing exclusion.
```

In S4.2, replace:

```markdown
It is nonzero and uniquely exposed. Thus T4.2(c) again gives
\(\omega_{j^*}\ne0\). At \(f_1=1\), \(I_t=i_t\) and this
specializes to S4.1.
```

with:

```markdown
It is nonzero. The annex may invoke T4.2(c) only when its
slot-isolation calculation proves that this contribution is fully
exposed in the assembled-slot sense of S0: no other branch term
and no incoming carry or recarry lands in the same canonical
height-\(\Theta_{j^*}\) slot. Under that premise,

\[
\omega_{j^*}\ne0.
\]

Uniqueness only among top-monomial or single-extraction candidates
does not suffice. If the pinned annex proves only that weaker
uniqueness, this invocation remains unresolved. At \(f_1=1\),
\(I_t=i_t\) and the fully exposed case specializes to S4.1.
```

In S8, replace PE1 item 5 with:

```markdown
5. that CERT-TOP is invoked through T4.2(c) only after the source
   calculation excludes every other assembled-slot input,
   including other terms and incoming carries and recarries;
```

In the GT6 consumption check, replace the first sentence with:

```markdown
- **GT6 consumption:** recover CERT-TOP solely through T4.2(c)
  after retaining GENTOW-6’s complete assembled-slot exposure
  calculation. Uniqueness only among single-extraction branches
  does not count as consumption of T4.2(c).
```

This closes the invalid inference from “one single-extraction contribution” to “nothing can cancel it” without attributing the stronger exposure fact to either pinned source before validation.


---

## r4 (2026-08-12): arc repairs

*(Fable-arm repair under the 2026-08-12 parallel regime; findings runs/comp11/T4P4_output.log; counter resets.)*

Five verbatim-ready r4 repairs follow, one per T4P4 finding. Unlike the r1 and r2 rounds, byte-literal pin validation could be executed this round; the complete grep evidence (occurrence count, 1-based line, 0-based byte offset for every marker of the post-r4 stacks) is recorded in R4-C1's S5.1 replacement below.

### R4-C1 — the reversed GT6 BOX-4 pin re-anchored to the actual discharge record (finding 1, CRITICAL)

Diagnosis, confirmed byte-literally at HEAD: in `GENTOW6_PROOF_2026-08-09.md` the r0 span-4 END substring `6.3' keeps its prose-only grading in the note's own terms.` occurs exactly once — at line 673 (byte 38211), inside the S5 acceptance-fold bracket — while the span-4 BEGIN substring occurs exactly once at line 1249 (byte 70410), in the final dated append. BEGIN does not precede END, S5 condition 3 fails, and the BOX-4 span — hence `GT6-CERT-TOP` — correctly failed closed. The actual BOX-4 discharge record is the closing block of the final dated append (lines 1249–1265, the end of the source).

In S4's "Marker-delimited source pins, HEAD." list, replace span 4 with:

```markdown
4. BEGIN substring  
   `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):`  
   END substring  
   `output md5 2d8d617a, verdict commit follows this append.`
```

The new END is the source's final line. The half-open span covers the entire BOX-4 discharge record that S4.2 consumes — the four x-ful \(f_1=2\) rows at sealed-battery grade, GREEN 265/0, certificate pins \(=\Theta_0\) exactly on the floor, and 6.3′'s derivation keeping the prose grade of the source arc — and excludes only the closing artifact-hash clause, which T4 does not consume. The retired r0 END substring remains where it always was, in the earlier S5 bracket; it is no longer a marker.

Replace S5.1 (the R2-C1 text) with:

```markdown
### S5.1 R4 PIN-VALIDATION RECORD (2026-08-12)

On 2026-08-12 the r4 round executed the byte-literal validation
that the R1 and R2 attempts could not run. Every BEGIN and END
substring of the post-r4 pin lists was matched literally
(`grep -F`) against its named HEAD source. Occurrence counts,
1-based line numbers, and 0-based byte offsets:

Source `GENTOW3_PROOF_2026-08-09.md` (1,041 lines) — the GT3
stack of six spans:

| marker (role) | count | line | byte |
|---|---|---|---|
| `## S0. THE ONE CONSTANT AND THE THRESHOLD` (1-BEGIN) | 1 | 74 | 3886 |
| `## S3. COROLLARY GENTOW-3.C` (1-END) | 1 | 317 | 17886 |
| `### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t` (2-BEGIN) | 1 | 504 | 28156 |
| `### S7.2 (m-1 repair): the (iv) certificate's digit-value` (2-END) | 1 | 610 | 33968 |
| `## S7.6 [GT3-r2] PE2 REPAIR RECORD:` (3-BEGIN) | 1 | 680 | 37757 |
| `## S7.7 [GT3-r3] PE3 REPAIR RECORD:` (3-END, 4-BEGIN) | 1 | 763 | 42380 |
| `### Dated acceptance record` (4-END, 5-BEGIN) | 1 | 817 | 45302 |
| `## S8. [GT3-r4] CODEX TOWERRAT2 RUN B REPAIRS` (5-END) | 1 | 880 | 48739 |
| `### S8.1 [B-F1, GAP] Clause (iv)'s deep-perturbation persistence:` (6-BEGIN) | 1 | 894 | 49488 |
| `### S8.2 [B-F2, GAP]` (6-END) | 1 | 941 | 52157 |

Source `GENTOW6_PROOF_2026-08-09.md` (1,265 lines) — the GT6
stack of four spans:

| marker (role) | count | line | byte |
|---|---|---|---|
| `## S3. THEOREM GENTOW-6.3` (1-BEGIN) | 1 | 344 | 19136 |
| `## S4. MACHINE LEG` (1-END) | 1 | 529 | 29718 |
| `### S6.1 THE DATED GAUGE ANNEX` (2-BEGIN) | 1 | 702 | 39709 |
| `### S6.2 THE 𝒯-FREE CAP LEMMA` (2-END) | 1 | 851 | 47646 |
| `**GENTOW6-BOX-1 (mu2 >= 3 attainment): CLOSED AT f1 = 1**` (3-BEGIN) | 1 | 1204 | 67667 |
| `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):` (3-END, 4-BEGIN) | 1 | 1249 | 70410 |
| `output md5 2d8d617a, verdict commit follows this append.` (4-END) | 1 | 1265 | 71408 |

Every count is exactly 1 (S5 conditions 1–2); every match lies in
its named source (condition 4); within each pair the BEGIN byte
offset strictly precedes the END byte offset, and each stack's
spans occur in the recorded byte order (conditions 3 and 5). The
retired r0 GT6 span-4 END substring `6.3' keeps its prose-only
grading in the note's own terms.` occurs once at line 673 (byte
38211), before the span-4 BEGIN at byte 70410 — the reversal this
record retires.

Rider audit (condition 6), for the spans r4 adds or repairs. GT3
spans 2 and 5: the dated appends after them are S8 (GT3-r4) and
S8.4 (GT3-r5, 2026-08-12); S8.4 fences itself — "This correction
changes only S8.2's non-functionality scope" — and no sentence of
S8–S8.4 supersedes the S7.1 FR-GL row or the acceptance record's
FR5X measurements. GT6 span 4: nothing follows its END, which is
the source's final line. For the five pairs r4 does not touch,
the T4P4 audit found unique, correctly ordered markers and raised
no supersession finding.

This record supersedes the R1 and R2 pin-validation records. It
is a pin-validation result, not hostile-pass credit: the
acceptance counter stays 0/2, and `GT6-CERT-TOP`'s invocation of
T4.2(c) additionally awaits the source-owned full-exposure
calculation required by the r3 repairs.
```

### R4-G1 — T4.2(d)'s exclusion hypothesis extended to every assembled provenance (finding 2, GAP)

After r3, \(\omega_j\) assembles single-\(\Phi'\)-extraction routes, all other branch terms, and every incoming carry and recarry. Excluding single-extraction sources alone therefore no longer forces \(\omega_j=0\), and (FLOOR) supplies no such exclusion. The repair strengthens (d)'s hypothesis to all provenances; the clause claims strictly less than before, and no consumer is affected: the instance records invoke (d) only through its cancellation leg (FR-M3's measured \(\omega_0=0\)) and its no-other-member warning, never through the no-source leg.

Replace T4.2(d) in full with:

```markdown
> **(d) No-contribution criterion.** Suppose that, after every
> branch term and every incoming carry and recarry has been
> propagated to the canonical grid, no summand of any provenance
> lands in any slot of coordinate \(j\) at height \(\Theta_j\) —
> the single-\(\Phi'\)-extraction routes, all other branch terms,
> and every incoming carry and recarry are excluded alike. Or
> suppose the complete assembled contribution cancels. Then
> \(\omega_j=0\).
>
> Absence of single-extraction sources alone does not discharge
> the first hypothesis: the exclusion must cover every provenance
> named in DEFINITION T4.1's assembly. No attainment statement
> for another member follows: entry-driven content may still
> attain \(\Theta_j\).
```

Replace the proof's clause-(d) sentences ("Clause (d) is the definition after complete assembly. Its final warning is necessary because \(\omega_j\) classifies the key-power witness, not all members of the genre.") with:

```markdown
Clause (d) is the definition after complete assembly, read under
its all-provenance hypothesis: if no summand of any provenance
lands in any height-\(\Theta_j\) slot of coordinate \(j\), the
assembled graded digit is empty, and if the complete assembled
contribution cancels, it is zero; in either case \(\omega_j=0\).
Excluding single-extraction sources alone would leave the other
branch terms and the incoming carries and recarries unaccounted,
which is why the weaker hypothesis proves nothing. The final
warning is necessary because \(\omega_j\) classifies the
key-power witness, not all members of the genre.
```

### R4-G2 — the GT3 stack extended to cover the FR-GL and FR5X records (finding 3, GAP)

The instance claims "FAM-A5/A7/B/C and FR-GL have \(\omega_j\ne0\) at the recorded coordinates" and "FR5X supplies coordinates on which the complete self-shadow coordinate vanishes", and PE2 requires re-inspecting both. FR-GL is recorded in GENTOW3 S7.1 (the adopted \(\eta\ne1\) machine row: corrected key, \(\Theta=(13,7)\), floor attained at both coordinates), which fell in the gap between span 1's END and span 2's BEGIN; FR5X is recorded in the post-PE5 dated acceptance record (PE5 obs-1: \(\mu_2=2\) pins \([61,\mathrm{None}]\), attained at \(\Theta_0=61\) with \(j=1\) identically zero; \(\mu_2=3\) pins \([91,61,\mathrm{None}]\) against \(\Theta=[87,61,35]\), slack at \(j=0\), attained at \(j=1\), identically zero at \(j=2\)), which fell after span 3's END. Neither claim was recoverable from the recorded stack. The repair adds the two missing spans; no instance claim is widened.

In S3's "Marker-delimited source pins, HEAD." block, replace the four-item span list with:

```markdown
1. BEGIN substring  
   `## S0. THE ONE CONSTANT AND THE THRESHOLD`  
   END substring  
   `## S3. COROLLARY GENTOW-3.C`

2. BEGIN substring  
   `### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t`  
   END substring  
   `### S7.2 (m-1 repair): the (iv) certificate's digit-value`

3. BEGIN substring  
   `## S7.6 [GT3-r2] PE2 REPAIR RECORD:`  
   END substring  
   `## S7.7 [GT3-r3] PE3 REPAIR RECORD:`

4. BEGIN substring  
   `## S7.7 [GT3-r3] PE3 REPAIR RECORD:`  
   END substring  
   `### Dated acceptance record`

5. BEGIN substring  
   `### Dated acceptance record`  
   END substring  
   `## S8. [GT3-r4] CODEX TOWERRAT2 RUN B REPAIRS`

6. BEGIN substring  
   `### S8.1 [B-F1, GAP] Clause (iv)'s deep-perturbation persistence:`  
   END substring  
   `### S8.2 [B-F2, GAP]`
```

The sentence following the list ("The later S8.2/S8.4 non-functionality scope is not consumed by this instance.") is retained unchanged: new span 5 is half-open at the S8 heading and consumes nothing of S8–S8.4, and span 6 is half-open at S8.2. New span 2 supplies the FR-GL configuration and the corrected-\(\widehat c_t\) gauge annex it sits in; new span 5 supplies the FR5X measurements and the arc's three measured certificate configurations. Validation and rider audit for both new spans are in the S5.1 R4 record.

### R4-m1 — S6's pre-r3 uniqueness terminology upgraded to assembled-slot exposure (finding 4, MINOR)

In S6, replace:

```markdown
- GENTOW-6.3(b)’s final implication from the unique CERT-TOP slot
  to threshold attainment becomes `GT6-CERT-TOP`;
```

with:

```markdown
- GENTOW-6.3(b)’s final implication from the fully exposed
  assembled CERT-TOP slot to threshold attainment becomes
  `GT6-CERT-TOP`;
```

and replace:

```markdown
The algebra that computes a proposed witness is not deleted:
GENTOW-6 still owns the top-slot uniqueness calculation, the
corrected-lift support calculation, and the higher-\(\mu_2\)
binomial coefficient.
```

with:

```markdown
The algebra that computes a proposed witness is not deleted:
GENTOW-6 still owns the complete assembled-slot exposure
calculation — the exclusion, in S0's full-exposure sense, of
every other branch term and every incoming carry and recarry
from the slot, not merely uniqueness among single-extraction
branches — together with the corrected-lift support calculation
and the higher-\(\mu_2\) binomial coefficient.
```

This brings S6's compression instructions to the same assembled-slot standard r3 imposed on T4.2(c), S4.1/S4.2, and S8.

### R4-m2 — the governing status label brought to r4 (finding 5, MINOR)

Replace the governing status block (the R1-C1 replacement of the title status line) with:

```markdown
**STATUS: R4 TEXT REPAIRED; UNRESOLVED at attempt grade 0/2.**
No clean hostile pass has been earned. The r4 round repaired the
reversed GT6 BOX-4 pin, extended the GT3 stack to cover the FR-GL
and FR5X records, and byte-validated every listed marker (S5.1 R4
record). Consumption still awaits a clean hostile re-resolution,
and `GT6-CERT-TOP`'s invocation of T4.2(c) additionally awaits
the source-owned full-exposure calculation required by r3. The
acceptance counter remains 0/2.
```

The unresolved conclusion is unchanged; only the stale revision label and its reason are updated.

No source file is touched by r4; all five corrections are dated, verbatim-ready replacements within this note. The acceptance counter remains 0/2; a fresh hostile pass must re-resolve the repaired pins and re-grade the note.


---

## r5 (2026-08-12): the membership seam + stale-sentence withdrawal

*(Fable-arm; counter resets.)*

Repairs for the latest hostile pass (0 CRITICAL + 2 GAP + 2 MINOR;
all seventeen pre-r5 marker pins byte-verified by that pass), plus
the consumption display its no-finding observation asked to be
evaluated. Every NEW quote and span pin of this round is
byte-validated in R5-V at the end; the R4 S5.1 record continues to
govern the pre-r5 stacks.

### R5-F1 — the member class \(\mathfrak M\) defined on the sources' actual quantification domain (finding F-1, GAP: the membership seam)

**Diagnosis.** T4 quantifies (FLOOR) "for every member" (R2-G1) and
hypothesizes "suppose that \(f\) is a member" (R2-G2) while never
defining "member". The corpus displays a hostile reader can bind
that word to include a disc hypothesis — GENTOW-3(iv)'s own
deep-perturbation parenthetical, byte-quoted:

```
(g in-budget with slots at heights > THETA_j, disc ≠ 0): both
```

[GT3 span 1] — and \(f_{\mathrm{key}}=\Phi_2^{\mu_2}\) FAILS
\(\operatorname{disc}\ne0\) (a \(\mu_2\)-th power; disc \(=0\)), so
under that reading T4.2(a)'s proof step "Because
\(f_{\mathrm{key}}\) is a member" is unfounded. Nor does any
in-budget hypothesis imply \(\operatorname{disc}\ne0\): at
\(\mu_2=2\), \(g=2c\Phi_2+c^2\) gives
\(f_{\mathrm{key}}+g=(\Phi_2+c)^2\) with disc \(=0\), and \(g\) is
in-budget once \(v(c)\) is large — so R2-G2's "so that
\(f_{\mathrm{key}}+g\) is a member" is unfounded too. The repair
defines the member class as the domain the pinned sources actually
quantify over — a pure coefficient slice carrying NO disc
hypothesis — and rebinds every load-bearing "member" to it.

**The sources' domain, read off the pinned spans.** GENTOW-3(i) is
displayed on the tower locus — its setting reads the two divisions
at

```
member f ∈ 𝒯, per composed coordinate j < mu2:
```

[GT3 span 1] — but the only membership fact the (i)/(ii) proof
consumes is Step 1's weak entry bound, byte-quoted:

```
On 𝒯 the entry pins lie weakly above the inner side:
```

\(e_2\cdot dv(A_J)\ge(\mu_1-J)u_2\) [GT3 span 1]. Steps 0–2 consume
nothing else about the dividend — in particular never
\(\operatorname{disc}\ne0\) — and the corpus already consumes
Steps 0–2 at proof strength on objects outside the 𝒯 display:
pinned S8.1's own derivation is headed

```
The corrected derivation (this note's Steps 0-2, run on g).
```

[GT3 span 6], run on \(g\), which is not even monic of degree
\(n\). The sources also apply the floor to the key power itself —

```
f = Phi2^{mu2} has composed read DRAIN (C_j = 0) while its shadow
```

[GT3 span 1, clause (iv)], and

```
THEOREM GENTOW-3(i) floors every discrepancy at
```

\(\Theta_j\), said of the self-shadow object \(f=\Phi_2^{\mu_2}\)
[GT6 span 1, S3 setting] — and to the measured W row, which GT3's
S0 itself names a member:

```
f = Phi2³ + 2x·Phi2² + 8·Phi2 + 64 at FR-M3 j = 0 has first
```

disagreeing height exactly \(10=\Theta_0\) [GT3 span 1]. That W row
sits at slot weight exactly \(\mu_2E_2\), OUTSIDE the strict
GENTOW-1(a) box — S8.1's boundary confirmation, byte-quoted:

```
FR-M3 W member's g_W = 2x*Phi2^2 + 8*Phi2 has slot weights 9, 9 <
10 = mu2*E2 + 1 — OUTSIDE the box — and its discrepancy lands at
```

[GT3 span 6]. So the domain the sources actually run the floor on
is the WEAK affine development slice (slot weights \(\ge\mu_2E_2\)),
not the strict box (\(\ge\mu_2E_2+1\)): the weak slice contains
every polynomial the sources apply (i) to — the key power at
equality, the W row at equality, every box element strictly — and
membership in it is a pure coefficient condition.

**Insertion (verbatim-ready).** In the R1-G2 replacement for S0,
replace

```markdown
The member family lies in the affine slice
\(C_{\mu_2}(q)=1\), while differences of members with the same
leading key power lie in \(\mathscr D_{<\mu_2}\).
```

with:

```markdown
> **DEFINITION (the member class \(\mathfrak M\)).** Writing
>
> \[
> f=\Phi_2^{\mu_2}+g,\qquad
> g=\sum_{j<\mu_2}C_j(g)\,\Phi_2^{\,j}\in\mathscr D_{<\mu_2},
> \qquad
> C_j(g)=\sum_{a<D',\,b<e_2f_2}c_{j,a,b}\,x^a\Phi'^{\,b}
> \in\mathscr A_j,
> \]
>
> the member class is the affine development slice
>
> \[
> \mathfrak M:=
> \Bigl\{\,f=\Phi_2^{\mu_2}+g:\
> e_1e_2\,v(c_{j,a,b})+w(a,b)\;\ge\;(\mu_2-j)E_2
> \ \text{whenever}\ c_{j,a,b}\ne0\,\Bigr\}
> \]
>
> — leading digit pinned to \(1\), every lower slot digit weakly
> at or above the composed side (equivalently: every composed
> slot of \(g\) has weight \(\ge\mu_2E_2\)). Equivalently at the
> level-1 read — by the same Step-0 carry conversion that pinned
> GENTOW-3 S8.1 item (1) runs for its box — the entry pins of
> \(f\) lie weakly above the inner side,
> \(e_2\cdot dv(A_J)\ge(\mu_1-J)u_2\): exactly the membership
> fact, and the only one, that GENTOW-3's Steps 0–2 consume.
>
> Membership in \(\mathfrak M\) is a pure coefficient condition
> on the development digits. It carries NO discriminant
> hypothesis and no decidedness hypothesis. Everywhere in this
> note "member" means "element of \(\mathfrak M\)". The member
> family lies in the affine slice \(C_{\mu_2}(q)=1\), and
> differences of members with the same leading key power lie in
> \(\mathscr D_{<\mu_2}\).
>
> Three membership facts, each by inspection of the definition:
>
> 1. \(f_{\mathrm{key}}=\Phi_2^{\mu_2}\in\mathfrak M\): its lower
>    development is \(g=0\), so the slot condition is vacuous.
>    Note \(\operatorname{disc}(f_{\mathrm{key}})=0\): the
>    sources' floor domain provably contains a disc \(=0\)
>    element, so no disc hypothesis can be part of membership.
> 2. In-budget perturbations stay in \(\mathfrak M\): if every
>    composed slot of \(g\) clears weight \(\mu_2E_2+1\) —
>    GENTOW-3 S8.1's box, which is STRICTLY inside the membership
>    floor — then \(f_{\mathrm{key}}+g\in\mathfrak M\), and
>    \(f+g\in\mathfrak M\) for every \(f\in\mathfrak M\)
>    (slotwise ultrametric). Pure coefficient arithmetic; no disc
>    condition is implied, and the \((\Phi_2+c)^2\) example shows
>    none could be.
> 3. The measured FR-M3 W member lies in \(\mathfrak M\) at exact
>    equality (slot weights \(9=\mu_2E_2\)) while sitting OUTSIDE
>    S8.1's box — which is why the weak slice, and not the box,
>    is the membership reading: GENTOW-3's S0 names it a member
>    and records its floor-exact first divergence.
```

**(FLOOR) displayed on \(\mathfrak M\).** In the R2-G1 replacement,
replace

```markdown
> Assume the GENTOW-3 discrepancy floor holds for every member:
>
> \[
> \operatorname{gr}_m(\Delta_j(f))=0
> \qquad
> \text{for every member \(f\), every \(j<\mu_2\), and every
> \(m<\Theta_j\).}
> \tag{FLOOR}
> \]
```

with:

```markdown
> Assume the GENTOW-3 discrepancy floor on the member class
> \(\mathfrak M\) (S0):
>
> \[
> \operatorname{gr}_m(\Delta_j(f))=0
> \qquad
> \text{for every \(f\in\mathfrak M\), every \(j<\mu_2\), and
> every \(m<\Theta_j\).}
> \tag{FLOOR}
> \]
```

The supplier cite, exactly: (FLOOR) on \(\mathfrak M\) is
GENTOW-3(i) read at its Steps 0–2 quantification domain. The (i)
display —

```
(i) [FLOOR] every dv2-height at which ShC_j and C_j carry
```

different slot digits is \(\ge\Theta_j\) [GT3 span 1] — is proved
from \(\mathfrak M\)'s defining entry bound alone (Step 1, quoted
above) with every discrepancy branch priced at \(+k\delta\),
\(k\ge1\), above the source layer (Step 2); no disc hypothesis
enters, and the S8.1 precedent quoted above licenses consuming
Steps 0–2 at proof strength. Accordingly, in S3's "Consumed
facts.", replace

```markdown
1. GENTOW-3(i) supplies (FLOOR).
```

with:

```markdown
1. GENTOW-3(i), read at its Steps 0–2 quantification domain
   \(\mathfrak M\) (the S0 definition: the Step-1 entry bound is
   the only membership fact the proof consumes, and pinned S8.1
   consumes Steps 0–2 at proof strength on \(g\) itself), supplies
   (FLOOR) on \(\mathfrak M\).
```

**Rebinding replacements (each verbatim-ready).**

(1) In the R2-G1 proof paragraph, replace

```markdown
Because \(f_{\mathrm{key}}\) is a member, (FLOOR) specializes to
```

with

```markdown
Because \(f_{\mathrm{key}}\in\mathfrak M\) (S0, membership fact 1;
no disc hypothesis is available or needed), (FLOOR) specializes to
```

(2) In R2-G2's statement of T4.2(b), replace

```markdown
> and suppose that \(f\) is a member. If
```

with

```markdown
> and suppose \(f\in\mathfrak M\) — a pure coefficient condition
> (S0). If
```

and replace

```markdown
> In particular, if \(g\) satisfies GENTOW-3’s in-budget
> hypotheses, so that \(f_{\mathrm{key}}+g\) is a member, its
```

with

```markdown
> In particular, if \(g\) is in-budget in pinned S8.1's box sense
> (every composed slot of \(g\) clears weight \(\mu_2E_2+1\)),
> then \(f=f_{\mathrm{key}}+g\in\mathfrak M\) by S0's membership
> fact 2 — pure coefficient arithmetic, no disc condition implied
> or needed — and S8.1's
```

(3) In R2-G2's proof paragraph, replace

```markdown
Let \(g\in\mathscr D_{<\mu_2}\) and let
\(f=f_{\mathrm{key}}+g\) be a member. By the definitions in S0,
```

with

```markdown
Let \(g\in\mathscr D_{<\mu_2}\) and let
\(f=f_{\mathrm{key}}+g\in\mathfrak M\). By the definitions in S0,
```

and replace

```markdown
(FLOOR), applied
to the member \(f\), excludes every lower digit.
```

with

```markdown
(FLOOR), applied
to \(f\in\mathfrak M\), excludes every lower digit.
```

(4) In the R2-C2 replacement, replace

```markdown
It is a member, hence belongs to
\(\mathscr D_{\le\mu_2}\), and its honest lower coordinates
vanish:
```

with

```markdown
It lies in \(\mathfrak M\) (S0, membership fact 1), hence in
\(\mathscr D_{\le\mu_2}\), and its honest lower coordinates
vanish:
```

No other "member" site is load-bearing: with \(\mathfrak M\) the
weak slice, T4.2(d)'s warning and the S3 instance sentences about
the W member's entry-driven attainment are true as written (the W
member IS an element of \(\mathfrak M\), at the boundary).

**Where \(\operatorname{disc}\ne0\) stays.** The sources demand
disc \(\ne0\) on their σ-read legs, and only there:
GENTOW-3(iv)'s deep-perturbation parenthetical (byte-quoted in
the diagnosis) carries it so that the perturbed member's honest
read is a DECIDED leaf whose σ the trailing-pair construction
consults, and the GENHN-family σ-decision displays quantify over
disc \(\ne0\) lifts. T4 consumes none of that σ-content: every
clause of LEMMA T4.2 is a graded-digit statement, and the supplier
of its in-budget leg decouples that parenthetical explicitly —
pinned S8.1, byte-quoted:

```
consumed by the corrected derivation; the box hypothesis is the
```

operative one [GT3 span 6: "The parenthetical hypothesis '(slots
at heights > THETA_j)' is NOT ..."], its digit conclusion being

```
every disagreeing height of g's two reads is >= THETA_j + 1,
```

with the box hypothesis

```
"in-budget" at the GENTOW-1(a) box this corpus defines: every
```

composed slot of \(g\) clears weight \(\mu_2E_2+1\) — and nothing
else. So \(\operatorname{disc}\ne0\) is NOT part of
\(\mathfrak M\) and appears in no digit-floor clause of this note;
any later consumer that needs a decided-leaf σ must import the
source's own disc \(\ne0\) hypothesis at that consumption site,
alongside — not inside — membership.

### R5-F2 — the stale r0 CERT-TOP sentence WITHDRAWN (finding F-2, GAP)

The r0 sentence at S4.1's tail, byte-quoted:

```
This is GENTOW-6.3(b), CERT-TOP, as a literal exposed-slot instance
of the certificate-witness lemma.
```

is **WITHDRAWN** and deleted. It survived r3's replacement span —
which ended at the displayed \(\Theta_{j^*}\) formula, one
sentence short — and asserts consumed-instance status on the
pre-r3 "exposed-slot" (uniqueness-among-single-extractions)
basis. That contradicts the r3 repair, whose S4.1 text makes the
T4.2(c) invocation conditional and states that single-extraction
uniqueness alone leaves `GT6-CERT-TOP` unresolved, and the r4
status, which records that the invocation "additionally awaits
the source-owned full-exposure calculation required by r3". The
governing status of the instance is the r3/r4 language — now
resolved at the \(f_1=1\) scope, and only there, by R5-63A's
consumption display below.

### R5-m1 — the boxed compression scoped to the key power (finding m-1, MINOR)

In the composition record, replace the boxed display and its
trailing sentence, i.e.

```markdown
\[
\boxed{
\text{touched at }j
\;:\Longleftrightarrow\;
\omega_j\ne0
\;\Longrightarrow\;
\text{first discrepancy at }\Theta_j
}
\]

with the converse at the key power supplied by the discrepancy
floor, and with GENTOW-6’s CERT-TOP serving as an explicit,
unique-slot proof that \(\omega_{j^*}\ne0\).
```

with:

```markdown
\[
\boxed{
\text{touched at }j
\;:\Longleftrightarrow\;
\omega_j\ne0
\;\Longleftrightarrow\;
\nu_j(f_{\mathrm{key}})=\Theta_j
}
\]

The first equivalence is DEFINITION T4.1; the second is LEMMA
T4.2(a) under (FLOOR), and the whole box is a statement about the
KEY POWER alone: no other member's first discrepancy is
compressed here (the measured FR-M3 W member attains \(\Theta_0\)
at a coordinate the key power leaves untouched). Transfer to any
other member goes only through T4.2(b)'s perturbation hypothesis.
GENTOW-6's CERT-TOP serves as the source-owned, fully exposed
assembled-slot proof that \(\omega_{j^*}\ne0\), at its \(f_1=1\)
scope (R5-63A).
```

### R5-m2 — \(\mathscr A_j\) defined at its first use (finding m-2, MINOR)

\(\mathscr A_j\) enters undefined at R1-G2's display
\(C_j,\operatorname{Sh}C_j:\mathscr D_{\le\mu_2}\to\mathscr A_j\).
The right codomain is NOT the degree-\(<\mu_2D_2\) dividend
module; it is one coordinate's slot grid, read off LEMMA
GENTOW-6.4(a)'s own display, byte-quoted:

```
> a < D', b < e2f2; slot degree jD2 + bD' + a; slot dv2-height
> e1e2·v(c_{j,a,b}) + w(a,b), w(a,b) = a·e2h + b·u2). Then:
```

[GT6 NEW span 3; validation in R5-V]. In the R1-G2 replacement for
S0, insert immediately after the \(\mathscr D_{<\mu_2}\) display:

```markdown
For each \(j<\mu_2\), let

\[
\mathscr A_j:=\bigoplus_{a<D',\;b<e_2f_2}
\widehat{\mathcal O}\cdot x^a\Phi'^{\,b}
\]

— the module of composed-grid coordinate strings at ONE
coordinate \(j\): elements \(\sum_{a,b}c_{a,b}x^a\Phi'^{\,b}\)
with \(a<D'\), \(b<e_2f_2\); as polynomials these have
\(x\)-degree \(<D_2=\deg\Phi_2\) (one coordinate's grid, not the
dividend module). The slot \((a,b)\) at digit value \(v\) carries
\(dv_2\)-height \(e_1e_2\,v+w(a,b)\), with
\(w(a,b)=a\,e_2h+b\,u_2\), and one \(K_2\)-digit per height by
GENHN-2′. This is LEMMA GENTOW-6.4(a)'s grid display read at one
coordinate. Only the grid-and-height display is consumed here:
6.4(a)'s bijection-codomain face (corrected by the post-PE2 rider
inside the same pinned span) is consumed nowhere in this note.
```

(R5-F1's \(\mathfrak M\) definition lands after this insertion in
the assembled S0 and uses \(\mathscr A_j\) and \(w(a,b)\) as
defined here.)

**Pin update (the new GT6 span).** LEMMA GENTOW-6.4 lies outside
the r0–r4 GT6 stack (old span 2 is half-open AT the S6.2 heading).
In S4's "Marker-delimited source pins, HEAD." list, as repaired by
R4-C1, replace the four-span GT6 stack with this five-span stack:

```markdown
1. BEGIN substring  
   `## S3. THEOREM GENTOW-6.3`  
   END substring  
   `## S4. MACHINE LEG`

2. BEGIN substring  
   `### S6.1 THE DATED GAUGE ANNEX`  
   END substring  
   `### S6.2 THE 𝒯-FREE CAP LEMMA`

3. BEGIN substring  
   `### S6.2 THE 𝒯-FREE CAP LEMMA`  
   END substring  
   `> (b) [BAND-1 CAP, 𝒯-FREE] across ambient window-N lifts of f:`

4. BEGIN substring  
   `**GENTOW6-BOX-1 (mu2 >= 3 attainment): CLOSED AT f1 = 1**`  
   END substring  
   `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):`

5. BEGIN substring  
   `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):`  
   END substring  
   `output md5 2d8d617a, verdict commit follows this append.`
```

New span 3 covers the 𝒯-free triangularity paragraph and LEMMA
GENTOW-6.4's head and clause (a) with its codomain rider; it is
half-open at clause (b), which is not consumed. Validation and
rider audit: R5-V.

### R5-63A — the r3-awaited full-exposure calculation: THEOREM GENTOW-6.3(a) supplies it at \(f_1=1\) (the pass's no-finding observation, answered)

**Verdict: YES at the sealed scope — \(f_1=1\), \(\mu_2=2\),
\(2i_{t^*}\ge D'\) — and NO elsewhere.**

**What r3 requires.** By S0's full-exposure clause, invoking
T4.2(c) at `GT6-CERT-TOP` needs a source-owned calculation that,
after every branch term and every incoming carry and recarry has
been propagated to the canonical grid, the complete list of
summands landing in the certificate slot is the displayed
contribution alone — exclusion across EVERY provenance, not
uniqueness among single-extraction branches.

**What the already-validated GT6 span 1 proves.** THEOREM
GENTOW-6.3(a) is a closed clause of the validated span, and it
classifies the ENTIRE assembled height-\(\Theta\) layer.
Byte-quoted at its head:

```
> (a) [SOURCE CLASSIFICATION] the height-THETA graded layer of the
```

discrepancy (\(\operatorname{Sh}C_j-C_j\) over the composed grid)
is a sum of single-\(\Phi'\)-extraction branches, one per
x-overflowing lift pair — and at its close:

```
> Multi-extraction branches sit at weight >= THETA + delta; tail
```

(non-extraction) routes are shared by both reads and cancel. The
clause's own bookkeeping covers the carry and recarry provenances:
every downstream step of a height-\(\Theta\) branch is tracked —

```
> division/recarry step emits terms of Y-exponent LOWERED by
```

\(e_2f_2-e_2s\ge e_2>0\) at the same weight — so carries and
recarries are not an unaccounted provenance; they are the
branches' own tracked steps. Everything else either leaves the
layer (multi-extraction, at \(\ge\Theta+\delta\)) or cancels
between the two reads (tail routes). Then 6.3(b), in the same
span, proves the certificate slot

```
> b* = (2e2t*+1) mod e2f2, a* = 2i_{t*} − D' — receives EXACTLY ONE
```

height-\(\Theta\) branch, its proof closing the slot against every
other height-\(\Theta\) branch —

```
> equality iff zero steps and t + t' = 2t*: the (t*,t*) direct
```

branch alone, and

```
> lands at (a*, Y^{B*+1}) by the uniqueness just shown (branches
```

— with the digit nonzero unconditionally:

```
A product of units in K2^x: nonzero — no
```

binomial coefficient, no characteristic condition, no zero
divisors.

**How this discharges T4.2(c)'s premise at the GT6 instance.** By
(a), every summand of the assembled height-\(\Theta\) layer of the
key power's discrepancy — the same object \(\omega\) assembles —
is a term of some overflowing pair's single-extraction branch
chain; there is no other provenance left to exclude. By (b), the
only such term at the canonical position \((a^*,Y^{B^*+1})\) is
the \((t^*,t^*)\) direct branch. Uniqueness among branch-chain
terms is therefore uniqueness among ALL summands: the certificate
slot is FULLY EXPOSED, in S0's r3 sense, by the displayed digit
\((\widehat c_{t^*})^2\pi^{2a_{t^*}}\cdot(\text{wrap unit})\ne0\).
T4.2(c) fires: \(\omega_{j^*}\ne0\), \(j^*\) is touched, and
\(\nu_{j^*}(f_{\mathrm{key}})=\Theta_{j^*}\). S4.1's r3
conditional ("When that source-owned calculation establishes this
full exposure ...") is resolved AFFIRMATIVELY at this scope; its
fail-closed branch ("If the pinned source span establishes
uniqueness only among single-extraction branches ...") does not
bite, because 6.3(a) is a classification of the whole layer, not
a uniqueness claim inside one provenance.

**Scope fences (what is NOT supplied).**

- \(f_1\ge2\): the same span's GT6-r1 scope pin —

  ```
  > genre" reads AT f1 = 1, at the corrected chat_t. At f1 >= 2 the
  ```

  displays below "are NOT proved as written" — so S4.2's
  corrected-lift invocation (ANNEX 6.3′) still awaits ITS OWN
  full-exposure calculation; no (a)-grade layer classification is
  sealed at \(f_1\ge2\) (GENTOW6-BOX-4 residue). S4.2's r3
  conditional language stands unchanged.
- \(\mu_2\ge3\): S4.3's candidate status is unchanged (R2-G3
  governs; (6.5-CAND) remains an unassembled candidate).
- No hostile-pass credit: this is a consumption display added by
  a repair round; the acceptance counter stays 0/2 and the next
  hostile pass re-adjudicates it.

**Status refresh.** Replace the governing status block (R4-m2's
replacement text) with:

```markdown
**STATUS: R5 TEXT REPAIRED; UNRESOLVED at attempt grade 0/2.**
No clean hostile pass has been earned. The r5 round defined the
member class \(\mathfrak M\) on the sources' actual quantification
domain (pure coefficient slice, no disc hypothesis), withdrew the
stale r0 CERT-TOP consumption sentence, scoped the boxed
compression to the key power, defined \(\mathscr A_j\) from
GENTOW-6.4(a)'s grid display under a new validated span, and added
the R5-63A consumption display: at \(f_1=1\), \(\mu_2=2\),
\(2i_{t^*}\ge D'\), THEOREM GENTOW-6.3(a)+(b) supply the
source-owned full-exposure calculation required by r3, so
`GT6-CERT-TOP`'s invocation of T4.2(c) is discharged at that scope
only. The \(f_1\ge2\) annex leg (6.3′) and the \(\mu_2\ge3\)
candidate still await their own exposure calculations. The
acceptance counter remains 0/2.
```

### R5-V — byte-literal validation of the r5 pins and quotes (2026-08-12)

Every quote displayed in a fenced block above and every marker of
the new span was matched byte-literally (fixed-string) against its
named HEAD source. Occurrence counts, 1-based lines, 0-based byte
offsets:

Source `GENTOW3_PROOF_2026-08-09.md`:

| quote (role) | count | line | byte |
|---|---|---|---|
| `member f ∈ 𝒯, per composed coordinate j < mu2:` (S2 setting) | 1 | 164 | 8952 |
| `(i) [FLOOR] every dv2-height at which ShC_j and C_j carry` ((i) display) | 1 | 189 | 10420 |
| `On 𝒯 the entry pins lie weakly above the inner side:` (Step 1 = \(\mathfrak M\)'s consumption) | 1 | 230 | 12643 |
| `f = Phi2^{mu2} has composed read DRAIN (C_j = 0) while its shadow` ((iv) at the key power) | 1 | 204 | 11313 |
| `f = Phi2³ + 2x·Phi2² + 8·Phi2 + 64 at FR-M3 j = 0 has first` (S0's W member) | 1 | 93 | 4921 |
| `(g in-budget with slots at heights > THETA_j, disc ≠ 0): both` ((iv) σ-leg parenthetical) | 1 | 296 | 16733 |
| `The corrected derivation (this note's Steps 0-2, run on g).` (S8.1 proof-strength precedent) | 1 | 907 | 50145 |
| `"in-budget" at the GENTOW-1(a) box this corpus defines: every` (S8.1 box) | 1 | 908 | 50212 |
| `every disagreeing height of g's two reads is >= THETA_j + 1,` (S8.1 margin) | 1 | 923 | 51137 |
| `FR-M3 W member's g_W = 2x*Phi2^2 + 8*Phi2 has slot weights 9, 9 <` (S8.1 boundary) | 1 | 932 | 51697 |
| `10 = mu2*E2 + 1 — OUTSIDE the box — and its discrepancy lands at` (S8.1 boundary) | 1 | 933 | 51763 |
| `consumed by the corrected derivation; the box hypothesis is the` (S8.1 decoupling) | 1 | 938 | 52077 |

Source `GENTOW6_PROOF_2026-08-09.md`:

| quote (role) | count | line | byte |
|---|---|---|---|
| `THEOREM GENTOW-3(i) floors every discrepancy at` (S3 setting at the key power) | 1 | 371 | 20760 |
| `> (a) [SOURCE CLASSIFICATION] the height-THETA graded layer of the` (6.3(a) head) | 1 | 393 | 21910 |
| `> division/recarry step emits terms of Y-exponent LOWERED by` (6.3(a) downstream tracking) | 1 | 400 | 22379 |
| `> Multi-extraction branches sit at weight >= THETA + delta; tail` (6.3(a) close) | 1 | 402 | 22511 |
| `> b* = (2e2t*+1) mod e2f2, a* = 2i_{t*} − D' — receives EXACTLY ONE` (6.3(b) slot) | 1 | 408 | 22842 |
| `> equality iff zero steps and t + t' = 2t*: the (t*,t*) direct` (6.3(b) proof) | 1 | 469 | 26344 |
| `A product of units in K2^x: nonzero — no` (6.3(b) digit) | 1 | 475 | 26723 |
| `> lands at (a*, Y^{B*+1}) by the uniqueness just shown (branches` (6.3(b) proof close) | 1 | 480 | 27030 |
| `> genre" reads AT f1 = 1, at the corrected chat_t. At f1 >= 2 the` (GT6-r1 scope pin) | 1 | 382 | 21265 |
| `### S6.2 THE 𝒯-FREE CAP LEMMA` (span-2 END; NEW span-3 BEGIN) | 1 | 851 | 47646 |
| `> (b) [BAND-1 CAP, 𝒯-FREE] across ambient window-N lifts of f:` (NEW span-3 END) | 1 | 920 | 51652 |
| `> a < D', b < e2f2; slot degree jD2 + bD' + a; slot dv2-height` (6.4(a) grid) | 1 | 884 | 49514 |
| `> e1e2·v(c_{j,a,b}) + w(a,b), w(a,b) = a·e2h + b·u2). Then:` (6.4(a) heights) | 1 | 885 | 49577 |

Every count is exactly 1 (S5 conditions 1–2); every match lies in
its named source (condition 4). The post-r5 GT6 stack's markers
occur in strictly increasing byte order
\(19136<29718<39709<47646<51652<67667<70410<71408\), BEGIN
preceding END in every pair (conditions 3 and 5); the S6.2 marker
serves as span-2 END and span-3 BEGIN, as the GT3 stack already
does with its shared markers. All quotes above lie inside their
stacks' pinned spans; the S6.2-block quotes lie inside the NEW
span 3 (bytes 47646–51652).

Rider audit (condition 6), new span 3: the post-PE2 codomain rider
sits INSIDE the span and corrects LEMMA GENTOW-6.4(a)'s
bijection-codomain face (above-top slots forced to zero). r5
consumes only the grid-and-height display, which the rider leaves
intact and machine-confirms (its grid-census leg); the rider
itself records that the bijection/count face "is consumed nowhere
at HEAD", and this note keeps it that way. Nothing after the
span's END touches 6.4(a)'s grid display (the later dated appends
are the BOX records for 6.3-family content). For the pre-r5 spans,
the R4 S5.1 record and the latest pass's 17/17 byte-verification
govern; no new supersession was found against the quotes above.

This record is a pin-validation and consumption result, not
hostile-pass credit: the acceptance counter stays 0/2. A fresh
hostile pass must re-resolve the six-plus-five span stacks,
re-grade the \(\mathfrak M\) quantification, and re-adjudicate the
R5-63A consumption display.


---

**Dated rider (2026-08-12, post-pass — the single minor of the clean
Fable pass, folded per the minors-only precedent, no grade event).**
The 𝔐-definition's level-1 gloss "Equivalently at the level-1 read —
by the same Step-0 carry conversion…" is read as the ONE-DIRECTIONAL
"In particular, at the level-1 read…" (𝔐 ⟹ the weak entry bound —
the only direction any current consumer uses). The converse (weak
entry bound ⟹ 𝔐) is TRUE but rides GT3 Step 1's weight-monotone
K₂-division + Step 2's re-expansion (inside pinned GT3 span 1), not
the Step-0 carry conversion alone — a consumer needing the converse
must cite those two legs. Pass of record: the Fable-arm hostile pass
returned 0C + 0G + 1m with the 𝔐 mechanism, the 6.3(a)+(b)
full-exposure discharge, all 25 pins, and the boundary cases verified
sound — clean pass 1 of 2.
