# T1 — LEMMA GAUGE-COCYCLE (the ϑ/wrap recursion, stated once)
## RCT unit S-1-T1-gauge-cocycle — CODEX arm — 2026-08-10

**[RCT CODEX-arm: composed by gpt-5.6-sol high; transcribed unaltered.]**
Everything below the marker line is the composing model's text, VERBATIM
(source: `verification/openmath/t1_codex_run1_output.txt` @ 6e9968bd, the
final agent message, log lines 2509–3777; one foreground call, wall 6m02s,
46,892 tokens, no continuation). Per the prover-RCT protocol
(docs/PROVER_RCT_PROTOCOL_2026-08-10.md §3) the lab tech may NOT alter
mathematical content; this header is the tech's record, not part of the
composed note.

**GRADE: attempt 0/2.** The 2-clean hostile arc has not run. Charge and
gate: blueprint T1 (docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md §2) as
amended by Plan revision 1 §R.2's S-1a gate + §R.3's joint-frame rule.

**S-1a gate record (tech audit of FORM, not content).** (i) Conclusions:
FIVE displayed theorem conclusions (C1 letter recursion; C2 wrap cocycle /
telescope / corrected key; C3 read dictionary + B-law + gauge-invariance;
C4 exact-height lift shape + x-free criterion; C5 Q-bookkeeping) — the
gate's ≥ 3 met; the carrier-rule audit sentence is displayed in §1.
(ii) Absorption map: 18 site rows over the seven annexes (GENTOW4 = 4
sites, as required) + 2 supporting-context rows (GENTOW5). (iii) The R.3
joint frame (f₁ = 2 ∧ w ≠ 1 ∧ live wrap): PRESENT in the composed plan as
frame F4-JOINT (also η = ω ≠ 1 and a μ = 3 three-digit leg) — no
tech-added leg was needed.

**TECH-RECORDED GAPS (recorded, NOT fixed — they are the arc's data).**
- **G-1 (computational slip in M2, F4-JOINT quadratic test).** The
  composed text predicts ψ^{(w)} = y² + ωy + ω for ψ = y² + y + ω,
  w = ω. By the note's own (C3-three-reads) / the standing DEF W-2
  (ψ^{(w)} = w^f ψ(y/w)): w²ψ(y/w) = y² + ωy + ω³ = y² + ωy + 1, and the
  note's own slot computation gives the coefficients (c₁w, c₀w²) =
  (ω, 1) — so the predicted polynomial should be y² + ωy + 1. Both
  candidates are irreducible over F₄, so the invariance CLAUSE is
  unaffected; the displayed exact value is wrong. The sealed instrument
  preregisters Codex's value as written and scores it (expected RED on
  that row); the note text stays untouched.
- **G-2 (interface-strength note, C3 proof).** The abstract proof of the
  B-law consumes carrier item 9's "canonical residual map is
  multiplicative on homogeneous initial forms" as carrier data. In the
  absorbed corpus (GENTOW2-B″) the corresponding step is PROVED via the
  Φ₂-adic expansion argument (steps (ii)–(iv), Cor 4.7 + Lemma 3.17 +
  eq (14)), not assumed. The abstract lemma is sound relative to its
  carrier; whether the FGMN instance discharges item 9 at B″'s
  generality is a consumption-check obligation (R.1 leg (b)/(c)), open
  here. Not a defect of the statement; a named obligation.
- **G-3 (honest scope, recorded by the composer itself).** (C1) is fully
  explicit at level 2 only; the general level gets ρ_i by a terminating
  reduction algorithm with no closed exponent formula (Honesty ledger
  item 1) — matches the brief's allowance. The F4-JOINT frame is a
  finite graded-carrier model, not a claimed Q_p-realization (ledger
  item 8 + OPEN SUB-LEMMA JOINT-PADIC-REALIZATION, item 9).

**Machine leg (sealed separately, two-commit).** Instrument
`verification/openmath/t1_gauge_checks.py`: implements M1–M4 as
specified (frames X / FR-G / F4-JOINT / LP-LD; exact F₄ + integer
arithmetic; dual PARI routes on X and FR-G; the four planted teeth; the
FR-G member-level preregistrations discharged by re-running the
COMMITTED instrument `gentow4_pe1_fresh.py` UNMODIFIED as a regression
leg, per blueprint §5.3-2). Verdict appended below the composed text
after the sealed run, from artifacts only.

---- BEGIN VERBATIM COMPOSED TEXT (gpt-5.6-sol high, 2026-08-10) ----
## 1. STATEMENT

### LEMMA GAUGE-COCYCLE

#### Carrier data

Fix the following data.

1. A discretely valued base field with uniformizer \(\pi\), residue field
   \(\mathbf F_Q\), and a MacLane/Okutsu tower whose level-\(i\) residue field is
   \(K_i\).

2. Level \(1\) integers
   \[
   e_1\ge 1,\qquad f_1\ge 1,\qquad h\ge 1,\qquad \gcd(e_1,h)=1,
   \qquad D'=e_1f_1.
   \]
   The base key is \(x\), with \(dv_1(x)=h\) and \(dv_1(\pi)=e_1\).

3. The level-\(1\) stage letter
   \[
   \eta:=\operatorname{res}\!\left(\frac{x^{e_1}}{\pi^h}\right)\in K_1^\times,
   \qquad K_1=\mathbf F_Q(\eta),
   \]
   where \(1,\eta,\ldots,\eta^{f_1-1}\) is the chosen
   \(\mathbf F_Q\)-basis.

4. For every integer \(k\ge0\), the level-\(1\) ladder normalizer
   \[
   \widehat n_1(k)=x^{i(k)}\pi^{a(k)},\qquad
   0\le i(k)<e_1,\qquad i(k)h+a(k)e_1=k.
   \]

5. At a general level \(i\), ladder normalizers
   \(\widehat n_i(m)\) of exact \(dv_i\)-height \(m\), in the prescribed
   bounded-exponent normal form in
   \(\pi,x,\Phi_2,\ldots,\Phi_i\).

6. Stage data
   \[
   e_{i+1},\quad f_{i+1},\quad u_{i+1},
   \]
   and a monic residual polynomial
   \[
   \psi_{i+1}(y)=y^{f_{i+1}}-\sum_{t<f_{i+1}}c_ty^t
   \in K_i[y],\qquad c_0\ne0.
   \]

7. Exact-height lift maps
   \[
   \operatorname{lift}_i(d;m)
   \]
   satisfying
   \[
   dv_i(\operatorname{lift}_i(d;m))=m,\qquad
   \operatorname{res}\!\left(
      \frac{\operatorname{lift}_i(d;m)}
           {\widehat n_i(m)}
   \right)=d.
   \]
   Zero is lifted as zero.

8. The repo letter
   \[
   \eta_{i+1}:=
   \operatorname{res}\!\left(
      \frac{\Phi_i^{e_{i+1}}}{\widehat n_i(u_{i+1})}
   \right),
   \]
   the canonical FGMN uniformizer \(\pi_{i+1}\), and the canonical FGMN
   letter
   \[
   z_{i+1}:=
   \operatorname{res}\!\left(
      \frac{\Phi_i^{e_{i+1}}}{\pi_{i+1}^{u_{i+1}}}
   \right).
   \]
   At level \(1\),
   \[
   \pi_2=x^{\ell_1}\pi^{\ell'_1},\qquad
   \ell_1h+\ell'_1e_1=1,\qquad 0\le\ell_1<e_1.
   \]

9. Three reads of a homogeneous slot of height \(su_{i+1}\):

   - its coherent digit, read against \(\widehat n_i(su_{i+1})\);
   - its multiplicative coefficient, read against
     \(\widehat n_i(u_{i+1})^s\);
   - its canonical FGMN residual read \(R_{i+1,\beta}\).

   The canonical residual map is multiplicative on homogeneous initial
   forms and agrees with residue evaluation on value-zero elements.

10. For the top slot grade
    \[
    \bar\kappa_i:=u_{i+1}/e(\mu_i),
    \]
    define only the carrier unit
    \[
    w_i:=
    R_{i+1,\bar\kappa_i}\bigl(\widehat n_i(u_{i+1})\bigr)\in K_i^\times.
    \]

**Carrier-rule audit.**
\[
\boxed{\text{The carrier data contain neither the letter recursion (C1), nor
the cocycle/corrected-key identities (C2), nor the read dictionary and
gauge-invariance assertions (C3).}}
\]

### (C1) Letter recursion

At every level for which the displayed canonical and repo letters are defined,
\[
\boxed{
z_{i+1}
 =\eta_{i+1}\rho_i,\qquad
\rho_i:=
\operatorname{res}\!\left(
 \frac{\widehat n_i(u_{i+1})}{\pi_{i+1}^{u_{i+1}}}
\right).
}
\tag{C1-general}
\]
The quotient has value zero. Reduction by the successive tower relations
expresses \(\rho_i\) as a monomial in the preceding canonical letters
\(z_1,\ldots,z_i\).

At level \(2\), this recursion is explicit:
\[
\boxed{
z_2=\eta_2\,z_1^{-\lfloor\ell_1u_2/e_1\rfloor}.
}
\tag{C1-level-2}
\]

### (C2) Gauge cocycle, telescope, and corrected key

Define
\[
\operatorname{wrap}(a,b):=
\left\lfloor\frac{i(a)+i(b)}{e_1}\right\rfloor\in\{0,1\}.
\]
Then
\[
\boxed{
\widehat n_1(a)\widehat n_1(b)
 =
\widehat n_1(a+b)
 \left(\frac{x^{e_1}}{\pi^h}\right)^{\operatorname{wrap}(a,b)}.
}
\tag{C2-wrap}
\]

This is a normalized multiplicative \(2\)-cocycle:
\[
\tau_1(a,b):=
\frac{\widehat n_1(a)\widehat n_1(b)}{\widehat n_1(a+b)},\qquad
\tau_1(0,a)=\tau_1(a,0)=1,
\]
and
\[
\boxed{
\tau_1(a,b)\tau_1(a+b,c)
 =
\tau_1(b,c)\tau_1(a,b+c).
}
\tag{C2-cocycle}
\]

For \(s\ge0\),
\[
\boxed{
\widehat n_1(u_2)^s
 =
\widehat n_1(su_2)
 \left(\frac{x^{e_1}}{\pi^h}\right)^{
       \lfloor s\,i(u_2)/e_1\rfloor}.
}
\tag{C2-telescope-1}
\]
Thus, for \(s=f_2-t\),
\[
W(t):=\left\lfloor
       \frac{(f_2-t)i(u_2)}{e_1}
      \right\rfloor
\]
and
\[
\boxed{
\widehat n_1(u_2)^{f_2-t}
 =
\widehat n_1((f_2-t)u_2)
 \left(\frac{x^{e_1}}{\pi^h}\right)^{W(t)}.
}
\tag{C2-telescope-2}
\]

At a general level define the building-orientation telescope unit
\[
\boxed{
\vartheta_{i,s}:=
\operatorname{res}\!\left(
 \frac{\widehat n_i(u_{i+1})^s}
      {\widehat n_i(su_{i+1})}
\right)\in K_i^\times.
}
\tag{C2-vartheta}
\]
Then
\[
\boxed{
\vartheta_{i,0}=\vartheta_{i,1}=1,\qquad
\vartheta_{i,s+1}
 =
\vartheta_{i,s}\,
\operatorname{res}\bigl(\tau_i(su_{i+1},u_{i+1})\bigr),
}
\tag{C2-recursion}
\]
where
\[
\tau_i(a,b):=
\frac{\widehat n_i(a)\widehat n_i(b)}
     {\widehat n_i(a+b)}.
\]
At level \(1\),
\[
\boxed{
\vartheta_{1,s}
 =
\eta^{\lfloor s\,i(u_2)/e_1\rfloor}.
}
\tag{C2-level-1-vartheta}
\]

The corrected composed key is
\[
\boxed{
\Phi_{i+1}
 =
\Phi_i^{e_{i+1}f_{i+1}}
 -
\sum_{t<f_{i+1}}
 \widehat k_t\,\Phi_i^{e_{i+1}t},
}
\tag{C2-key}
\]
with
\[
\boxed{
\widehat k_t
 :=
\operatorname{lift}_i\!\left(
 c_t\vartheta_{i,f_{i+1}-t};
 u_{i+1}(f_{i+1}-t)
\right).
}
\tag{C2-corrected-lift}
\]

In particular,
\[
\boxed{
\widehat c_t
 =
\operatorname{lift}\bigl(c_t\eta^{W(t)}\bigr),
}
\]
and, when \(f_1\ge2\), the entire coefficient block is
\[
\boxed{
L_{(f_2-t)u_2}\bigl(c_t\eta^{W(t)}\bigr).
}
\tag{C2-level-2-key}
\]

The naive and corrected recipes coincide precisely when
\[
c_t\bigl(\vartheta_{i,f_{i+1}-t}-1\bigr)=0
\quad\text{for every }t.
\]
In particular they coincide when all relevant letters equal \(1\), and when
\(f_{i+1}=1\).

### (C3) Gauge-invariance of reads

For \(s=f_{i+1}-t\), let

- \(\gamma_t\) be the coherent digit against
  \(\widehat n_i(su_{i+1})\);
- \(c_t^{\mathrm{mult}}\) be the multiplicative coefficient against
  \(\widehat n_i(u_{i+1})^s\).

Then
\[
\boxed{
\gamma_t=c_t^{\mathrm{mult}}\vartheta_{i,s},
\qquad
c_t^{\mathrm{mult}}=\gamma_t\vartheta_{i,s}^{-1}.
}
\tag{C3-dictionary}
\]

To match the orientation used in the B-law, define
\[
\boxed{
\Theta_i(t):=\vartheta_{i,f_{i+1}-t}^{-1}
 =
\operatorname{res}\!\left(
 \frac{\widehat n_i((f_{i+1}-t)u_{i+1})}
      {\widehat n_i(u_{i+1})^{f_{i+1}-t}}
\right).
}
\tag{C3-B-cocycle}
\]
Thus \(\Theta_i(t)\) is the object denoted \(\vartheta(t)\) in
GENTOW2-B″; it is the inverse of the building-orientation
\(\vartheta_{i,s}\).

Let \(\beta_t\) be the grade of that slot and put
\[
u(\beta_t):=
R_{i+1,\beta_t}\bigl(
 \widehat n_i((f_{i+1}-t)u_{i+1})
\bigr).
\]
Then
\[
\boxed{
u(\beta_t)
 =
\Theta_i(t)\,w_i^{f_{i+1}-t}.
}
\tag{C3-B-law}
\]
Consequently, for an element with coherent digit \(\gamma_t\),
\[
\boxed{
R_{i+1,\beta_t}(\text{element})
 =
w_i^{f_{i+1}-t}\Theta_i(t)\gamma_t.
}
\tag{C3-FGMN-read}
\]

At the corrected key,
\[
\gamma_t=c_t\vartheta_{i,f_{i+1}-t},
\]
so the letter cocycles cancel:
\[
R_{i+1,\beta_t}(\text{slot }t)
 =
c_t w_i^{f_{i+1}-t}.
\]
Therefore the three reads of the corrected key are
\[
\boxed{
\begin{aligned}
\text{multiplicative residual}&=\psi_{i+1}(y),\\
\text{coherent digits}&=
 \bigl(c_t\vartheta_{i,f_{i+1}-t}\bigr)_{t<f_{i+1}},\\
\text{FGMN residual}&=
 \psi_{i+1}^{(w_i)}(y)
 :=w_i^{f_{i+1}}\psi_{i+1}(y/w_i).
\end{aligned}
}
\tag{C3-three-reads}
\]

The substitution \(y\mapsto w_i y\) is an automorphism of \(K_i[y]\).
Hence \(\psi\) and \(\psi^{(w_i)}\) have identical irreducible-factor
degrees and multiplicities. All verdict-level data depending only on those
patterns—splitting types, admissible residual genres, and their counts—are
gauge-invariant.

### (C4) Exact-height lift shape and x-free criterion

At level \(1\), write
\[
m=i(m)h+a(m)e_1,\qquad
d=\sum_{r<f_1}\lambda_r\eta^r.
\]
Then
\[
\boxed{
L_m(d)=
\sum_{r<f_1}
 \operatorname{lift}(\lambda_r)
 x^{i(m)+e_1r}\pi^{a(m)-rh}.
}
\tag{C4-LIFT}
\]
Every nonzero monomial has height \(m\), and the \(x\)-exponents are
pairwise distinct and less than \(D'=e_1f_1\). Subject to the tower's
integrality/clearance inequality \(a(m)-rh\ge0\), this is an integral
polynomial lift.

For \(d\ne0\),
\[
\boxed{
L_m(d)\text{ is an \(x\)-free monomial}
\iff i(m)=0\ \text{and}\ d\in\mathbf F_Q.
}
\tag{C4-x-free}
\]
Thus \(\eta=1\) makes corrected and naive coefficients equal, but does not,
when \(f_1\ge2\), imply that arbitrary \(K_1\)-digits are \(x\)-free.

### (C5) \(Q\)-bookkeeping

Let \(i_0\in[0,e_1)\) satisfy \(i_0h\equiv1\pmod {e_1}\), and put
\[
Q(k):=\frac{i_0k-i(k)}{e_1}.
\]
Then
\[
\boxed{
Q(a+b)=Q(a)+Q(b)+\operatorname{wrap}(a,b).
}
\tag{C5}
\]

## 2. PROOF

### Proof of (C1)

From the definitions,
\[
z_{i+1}
 =
\operatorname{res}\!\left(
 \frac{\Phi_i^{e_{i+1}}}{\pi_{i+1}^{u_{i+1}}}
\right)
\]
and
\[
\eta_{i+1}
 =
\operatorname{res}\!\left(
 \frac{\Phi_i^{e_{i+1}}}{\widehat n_i(u_{i+1})}
\right).
\]
Dividing the first fraction by the second gives
\[
z_{i+1}
 =
\eta_{i+1}
 \operatorname{res}\!\left(
 \frac{\widehat n_i(u_{i+1})}
      {\pi_{i+1}^{u_{i+1}}}
 \right).
\]
Both denominator normalizations have height \(u_{i+1}\), so their quotient
has value zero. This proves (C1-general).

Successive reduction of a value-zero Laurent monomial gives a preceding-letter
monomial as follows. At the highest key occurring in the quotient, the
value-zero equation, reduced modulo the corresponding ramification index,
forces that key's exponent to be divisible by that index because the stage
numerator and ramification index are coprime. Remove the corresponding power
of the defining value-zero element
\(\Phi_j^{e_j}/\widehat n_{j-1}(u_j)\). Repeat at level \(j-1\).
The process terminates with a value-zero \(x,\pi\)-monomial, which is a power
of \(x^{e_1}/\pi^h\). Taking residues expresses \(\rho_i\) as a monomial in
\(z_1,\ldots,z_i\). No closed formula for its exponent vector is asserted
beyond this reduction algorithm.

At level \(2\), put \(u=u_2\), \(i=i(u)\), and \(a=a(u)\). Then
\[
\frac{\widehat n_1(u)}{\pi_2^u}
 =
x^{i-\ell_1u}\pi^{a-\ell'_1u}.
\]
Because
\[
ih+ae_1=u
\]
and
\[
\ell_1h+\ell'_1e_1=1,
\]
the quotient has value zero. Reducing the two identities modulo \(e_1\)
gives
\[
ih\equiv u\equiv \ell_1uh\pmod {e_1}.
\]
Since \(h\) is invertible modulo \(e_1\),
\[
i\equiv\ell_1u\pmod {e_1}.
\]
The constraints \(0\le i,\ell_1<e_1\) give
\[
i=\ell_1u-e_1\left\lfloor\frac{\ell_1u}{e_1}\right\rfloor.
\]
Therefore
\[
i-\ell_1u
 =
-e_1\left\lfloor\frac{\ell_1u}{e_1}\right\rfloor.
\]
The value-zero equation then forces
\[
a-\ell'_1u
 =
h\left\lfloor\frac{\ell_1u}{e_1}\right\rfloor.
\]
Hence
\[
\frac{\widehat n_1(u)}{\pi_2^u}
 =
\left(\frac{x^{e_1}}{\pi^h}\right)^{
 -\lfloor\ell_1u/e_1\rfloor}.
\]
Taking residues proves
\[
z_2=\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}.
\]

### Proof of (C2)

Write
\[
\widehat n_1(a)=x^{i(a)}\pi^{a(a)},\qquad
\widehat n_1(b)=x^{i(b)}\pi^{a(b)}.
\]
Since \(i(a+b)\) is the unique representative in \([0,e_1)\) congruent to
\(i(a)+i(b)\) modulo \(e_1\),
\[
i(a)+i(b)
 =
i(a+b)+e_1\operatorname{wrap}(a,b).
\]
Using height additivity,
\[
a(a)+a(b)
 =
a(a+b)-h\operatorname{wrap}(a,b).
\]
Consequently
\[
\begin{aligned}
\widehat n_1(a)\widehat n_1(b)
 &=
x^{i(a+b)+e_1\operatorname{wrap}(a,b)}
\pi^{a(a+b)-h\operatorname{wrap}(a,b)}\\
&=
\widehat n_1(a+b)
\left(\frac{x^{e_1}}{\pi^h}\right)^{
 \operatorname{wrap}(a,b)}.
\end{aligned}
\]
This proves (C2-wrap).

Associativity of multiplication gives
\[
\frac{\widehat n(a)\widehat n(b)\widehat n(c)}
     {\widehat n(a+b+c)}
\]
in either parenthesization, yielding (C2-cocycle).

For \(s\ge0\), the \(x\)-exponent of \(\widehat n_1(u)^s\) is
\(s\,i(u)\). Its reduced representative is \(i(su)\), so
\[
s\,i(u)
 =
i(su)+e_1\left\lfloor\frac{s\,i(u)}{e_1}\right\rfloor.
\]
The equality of heights then determines the corresponding
\(\pi\)-exponent. This proves (C2-telescope-1), and substituting
\(s=f_2-t\) proves (C2-telescope-2). Taking residues gives
\[
\vartheta_{1,s}
 =
\eta^{\lfloor s\,i(u_2)/e_1\rfloor}.
\]

At a general level,
\[
\frac{\widehat n_i(u)^{s+1}}{\widehat n_i((s+1)u)}
 =
\frac{\widehat n_i(u)^s}{\widehat n_i(su)}
\frac{\widehat n_i(su)\widehat n_i(u)}
     {\widehat n_i((s+1)u)}.
\]
Taking residues proves (C2-recursion). The cases \(s=0,1\) are immediate.

Now let \(s=f_{i+1}-t\) and let the coherent digit of
\(\widehat k_t\) be
\[
\gamma_t=c_t\vartheta_{i,s}.
\]
Its multiplicative coefficient is
\[
\begin{aligned}
\operatorname{res}\!\left(
 \frac{\widehat k_t}{\widehat n_i(u_{i+1})^s}
\right)
&=
\operatorname{res}\!\left(
 \frac{\widehat k_t}{\widehat n_i(su_{i+1})}
\right)
\operatorname{res}\!\left(
 \frac{\widehat n_i(su_{i+1})}
      {\widehat n_i(u_{i+1})^s}
\right)\\
&=
\gamma_t\vartheta_{i,s}^{-1}\\
&=c_t.
\end{aligned}
\]
Thus the residual coefficient in slot \(t\) is exactly \(c_t\). This proves
the corrected recipe.

A naive digit \(\gamma_t=c_t\) instead gives multiplicative coefficient
\(c_t\vartheta_{i,s}^{-1}\). It agrees with \(c_t\) exactly when
\(c_t(\vartheta_{i,s}-1)=0\). This proves the degeneracy clause.

### Proof of (C3)

Let an exact-height element \(g\) have coherent digit \(\gamma\) at height
\(su_{i+1}\). Then
\[
\operatorname{in}(g)
 =
\gamma\,\operatorname{in}(\widehat n_i(su_{i+1})).
\]
Reading instead against \(\widehat n_i(u_{i+1})^s\) gives
\[
c^{\mathrm{mult}}
 =
\gamma\operatorname{res}\!\left(
 \frac{\widehat n_i(su_{i+1})}
      {\widehat n_i(u_{i+1})^s}
\right)
 =
\gamma\vartheta_{i,s}^{-1}.
\]
This is (C3-dictionary).

Put
\[
N:=\widehat n_i(u_{i+1}),\qquad
M_s:=\widehat n_i(su_{i+1}).
\]
By multiplicativity of canonical homogeneous initial forms,
\[
R(N^s)=R(N)^s=w_i^s.
\]
On the other hand,
\[
N^s=M_s\,(N^s/M_s).
\]
The second factor has value zero, and its canonical read is its residue,
namely \(\vartheta_{i,s}\). Therefore
\[
w_i^s=R(M_s)\vartheta_{i,s}.
\]
Thus
\[
R(M_s)=w_i^s\vartheta_{i,s}^{-1}
      =w_i^s\Theta_i(t),
\]
which proves the B-law.

Since
\[
\operatorname{in}(g)=\gamma\,\operatorname{in}(M_s),
\]
canonical reading gives
\[
R(g)=\gamma R(M_s)
    =w_i^s\Theta_i(t)\gamma.
\]
At the corrected key,
\[
\gamma=c_t\vartheta_{i,s}.
\]
Hence
\[
R(g)=c_tw_i^s.
\]
Summing the slots gives
\[
y^f-\sum_{t<f}c_tw_i^{f-t}y^t
 =
w_i^f\psi(y/w_i).
\]

Finally, the map
\[
K_i[y]\longrightarrow K_i[y],\qquad
P(y)\longmapsto w_i^{\deg P}P(y/w_i)
\]
sends a factorization \(P=\prod P_j\) to the corresponding factorization
\(\prod P_j^{(w_i)}\), preserving each factor's degree, multiplicity, and
irreducibility. This proves gauge-invariance of factor patterns and all
splitting/count data derived from them.

### Proof of (C4)

Because
\[
\widehat n_1(m)=x^{i(m)}\pi^{a(m)}
\]
and \(\eta\) is represented by \(x^{e_1}/\pi^h\), the lift of
\[
d=\sum_{r<f_1}\lambda_r\eta^r
\]
against \(\widehat n_1(m)\) is
\[
\sum_{r<f_1}
 \operatorname{lift}(\lambda_r)
 \widehat n_1(m)
 \left(\frac{x^{e_1}}{\pi^h}\right)^r.
\]
Expanding gives (C4-LIFT).

Each term has height
\[
i(m)h+e_1rh+\bigl(a(m)-rh\bigr)e_1=m.
\]
The \(x\)-exponents \(i(m)+e_1r\) are pairwise distinct. Moreover
\[
0\le i(m)+e_1r
 \le(e_1-1)+e_1(f_1-1)=D'-1.
\]
Thus no \(x\)-overflow or cancellation between different \(r\)'s occurs.

For a nonzero lift to be one \(x\)-free monomial, exactly one coefficient
\(\lambda_r\) may be nonzero and its exponent \(i(m)+e_1r\) must be zero.
Both summands are nonnegative, so this is equivalent to \(i(m)=0\) and
\(r=0\), which is equivalent to \(i(m)=0\) and \(d\in\mathbf F_Q\).

### Proof of (C5)

By definition,
\[
e_1Q(k)=i_0k-i(k).
\]
Therefore
\[
\begin{aligned}
e_1\bigl(Q(a+b)-Q(a)-Q(b)\bigr)
 &=i(a)+i(b)-i(a+b)\\
 &=e_1\operatorname{wrap}(a,b).
\end{aligned}
\]
Division by \(e_1\) proves (C5).

## 3. ABSORPTION MAP

| Annex | Site | Absorbing conclusion | Specialization |
|---|---|---|---|
| A1 GENHN | Dated-erratum corrected display | C2 | \(i=1,\ s=f_2-t\): \(\vartheta_{1,s}=\eta^{W(t)}\), hence \(\widehat c_t=L_{su_2}(c_t\eta^{W(t)})\). |
| A1 GENHN | “Corrected = naive at \(\eta=1\)” | C2 | If \(\eta=1\), every \(\vartheta_{1,s}=1\). |
| A2 HETOW | Wrap-cocycle preamble | C2, C5 | C2-wrap and \(Q(a+b)=Q(a)+Q(b)+\operatorname{wrap}(a,b)\). |
| A2 HETOW | Telescope and wrap-corrected key | C2 | \(s=f_2-t\) gives \(W(t)\) and the corrected exact-height lift. |
| A3 GENTOW1 | S0/S2/S3 corrected \(\widehat c_t\) pin | C2 | The multiplicative slot coefficient of the corrected lift is exactly \(c_t\). |
| A3 GENTOW1 | Value-blindness of budgets and floors | C2 | Corrected and naive lifts have the same exact height \(su_2\); they differ only by a residue unit. |
| A4 GENTOW3 | Corrected key pin | C2 | Same level-\(1\) specialization. |
| A4 GENTOW3 | x-free equivalence re-scope | C4 | \(L_m(d)\) is x-free iff \(i(m)=0\) and \(d\in\mathbf F_Q\); the \(i(m)=0\) test alone is valid only when \(f_1=1\). |
| A5 GENTOW4 | S0 naive key display | C2 | Replace plain lifts by \(L_{(f_2-t)u_2}(c_t\eta^{W(t)})\). |
| A5 GENTOW4 | 4.1(c)/S3 consumption of bridge lemmas | C2, C3 | The bridge residual is valid at the corrected key because its multiplicative coefficients are exactly \(c_t\). |
| A5 GENTOW4 | BOX-3 uniformity with no \(\eta\)-axis | C2 | A battery confined to \(\vartheta=1\) cannot test the corrected-versus-naive distinction. |
| A5 GENTOW4 | S4 residue-\(1\) x-relation | C2, C4 | The residue relation \(x^{e_1}/\pi^h=1\) is the condition \(\eta=1\), not the condition \(f_1=1\). |
| A6 GENTOW6 | S3 corrected coefficient and full digit support | C2, C4 | The corrected digit is \(L_m(c_t\eta^{W(t)})\), with support \(i(m)+e_1r<D'\). |
| A6 GENTOW6 | ANNEX-THEOREM 6.3′ scope repair | C4 | Overflow must be tested using the actual top exponent \(I_t\), not merely \(i_t\); the remainder of 6.3′ is not proved by this lemma. |
| A7 GENTOW2 | S5.1 LETTER FORMULA | C1 | \(z_2=\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}\). |
| A7 GENTOW2 | S5.2 B-law | C3 | With \(\Theta_i(t)=\vartheta_{i,f-t}^{-1}\), \(u(\beta_t)=\Theta_i(t)w_i^{f-t}\). |
| A7 GENTOW2 | Factor-pattern invariance under \(w\) | C3 | The canonical residual is \(w^f\psi(y/w)\), which has the same factor degrees and multiplicities as \(\psi\). |
| S1 GENTOW5 | Supporting-context GT5-r1 gauge pin | C2, C3 | The general recipe \(\widehat k_t=\operatorname{lift}_i(c_t\vartheta_{i,f-t};(f-t)u)\) is C2-corrected-lift. |
| S1 GENTOW5 | Supporting-context dictionary lemma | C3 | \(\gamma=c^{\mathrm{mult}}\vartheta\), with the B-law cocycle using the inverse orientation. |

## 4. MACHINE PLAN

### M1. Frames

Use exact finite-field arithmetic and exact integer/rational polynomial
arithmetic. PARI is used only for the explicitly p-adic rows.

Let \(\omega\in\mathbf F_4\) satisfy
\[
\omega^2+\omega+1=0,\qquad \omega^3=1.
\]

| Frame | Purpose | Data |
|---|---|---|
| X | Canonical \(\eta\ne1\) p-adic witness | \(p=3,\ \Phi'=x^2-6,\ e_1=2,\ f_1=1,\ h=1,\eta=2,\ (e_2,f_2)=(1,2),u_2=3\). |
| FR-G | Partial-side p-adic witness | Same level-\(1\) data as X, with the exact GENTOW4 corrected and naive keys below. |
| F4-JOINT | Joint \(f_1=2\), \(w\ne1\), live-wrap, three-digit frame | \(K_1=\mathbf F_4,\ e_1=2,\ f_1=2,\ h=1,\eta=\omega,\ u=3,\ i(u)=1,\ w=\omega\). Test both \(f=2\) key construction and \(\mu=3\) read conversion. This is a finite graded-carrier frame, not a claimed explicit \(\mathbf Q_p\)-polynomial realization. |
| LP/LD | Recorded GENTOW2 letter/cocycle geography | \(K_2=\mathbf F_4,\ z_1=\omega,\ z_2=1,\ e_1=2,h=1,\ell_1=1,u_2=9;\ e_3=1,f_3=2,u_3=19;\ N=4x\Phi', M=512x\). Test LD1 and LD2. |

F4-JOINT simultaneously has \(f_1=2\), \(\eta=\omega\ne1\),
\(w=\omega\ne1\), \(W(0)=1\), and a \(\mu=3\) three-digit read.

### M2. Preregistered exact predictions

#### Frame X

Here
\[
i(3)=1,\qquad W(1)=0,\qquad W(0)=1,
\]
and
\[
(\vartheta_{1,1},\vartheta_{1,2})=(1,2).
\]

The exact keys are
\[
\Phi_X^{\mathrm{naive}}
 =(x^2-6)^2+3x(x^2-6)+54,
\]
\[
\Phi_X^{\mathrm{corr}}
 =(x^2-6)^2+3x(x^2-6)+108.
\]

Predictions:
\[
\sigma(\Phi_X^{\mathrm{naive}})=\{(4,1)\},
\qquad
\sigma(\Phi_X^{\mathrm{corr}})=\{(2,2)\}.
\]
The naive slot polynomial is
\[
(Z+1)^2=Z^2+2Z+1.
\]
In the recorded root coordinate
\(\beta=\eta^{-1}\eta_2\), the corrected slot polynomial is
\[
Z^2+2Z+2.
\]
The corrected multiplicative residual in the repo \(\eta_2\)-coordinate is
\[
\psi_2(Z)=Z^2+Z+2.
\]

#### Frame FR-G

Again
\[
W(1)=0,\qquad W(0)=1,\qquad
(\vartheta_{1,1},\vartheta_{1,2})=(1,2).
\]

The exact keys are
\[
\Phi_{\mathrm{FRG}}^{\mathrm{naive}}
 =(x^2-6)^2-6x(x^2-6)-27,
\]
\[
\Phi_{\mathrm{FRG}}^{\mathrm{corr}}
 =(x^2-6)^2-6x(x^2-6)-54.
\]

Predictions:
\[
\sigma(\Phi_{\mathrm{FRG}}^{\mathrm{naive}})=\{(4,1)\},
\qquad
\sigma(\Phi_{\mathrm{FRG}}^{\mathrm{corr}})=\{(2,2)\}.
\]
The corrected multiplicative residual is
\[
Z^2+Z+2;
\]
the naive residual is
\[
(Z-1)^2=Z^2+Z+1.
\]

For the two recorded partial-side members, preregister:

- corrected \(\mu_2^\*=2\);
- naive \(\mu_2^\*=0\);
- the naive initial segment above \(T_2=6\) is empty;
- corrected class valuations are strictly above the separator;
- naive class valuations land exactly on the separator.

#### Frame F4-JOINT: quadratic key test

Use
\[
\widehat n(3)=\pi x,\qquad
\widehat n(6)=\pi^3,
\]
so
\[
W(1)=0,\qquad W(0)=1,\qquad
\vartheta_1=1,\quad\vartheta_2=\omega.
\]

Take
\[
\psi(y)=y^2+y+\omega.
\]
In the convention
\(\psi=y^2-\sum c_ty^t\), characteristic \(2\) gives
\[
c_1=1,\qquad c_0=\omega.
\]

Corrected coherent digits:
\[
\gamma_1=1,\qquad
\gamma_0=\omega\vartheta_2=\omega^2.
\]
Naive coherent digits:
\[
\gamma_1^{N}=1,\qquad
\gamma_0^{N}=\omega.
\]

Using \(\omega^2=\omega+1\),
\[
L_3(1)=\pi x,
\]
\[
L_6(\omega)=x^2\pi^2,
\]
\[
L_6(\omega^2)=\pi^3+x^2\pi^2.
\]

Thus the associated-graded key representatives are
\[
\Phi_{\mathrm{corr}}
 =\Phi^2+\pi x\,\Phi+\pi^3+x^2\pi^2,
\]
\[
\Phi_{\mathrm{naive}}
 =\Phi^2+\pi x\,\Phi+x^2\pi^2.
\]

Multiplicative residuals:
\[
R_{\mathrm{corr}}(y)=y^2+y+\omega,
\]
\[
R_{\mathrm{naive}}(y)=y^2+y+1.
\]
Over \(\mathbf F_4\),
\[
y^2+y+\omega\quad\text{is irreducible},
\]
because \(\operatorname{Tr}_{\mathbf F_4/\mathbf F_2}(\omega)=1\), while
\[
y^2+y+1=(y+\omega)(y+\omega^2).
\]

Formal tower splitting predictions are therefore
\[
\sigma_{\mathrm{corr}}=\{(2,4)\},
\qquad
\sigma_{\mathrm{naive}}=\{(2,2),(2,2)\}.
\]
These are residual-to-tower predictions inside the finite graded model, not
PARI claims about an unstated p-adic lift.

With \(w=\omega\), the FGMN residual is
\[
\psi^{(w)}(y)
 =y^2+\omega y+\omega.
\]
It is irreducible, as required by gauge-invariance.

#### Frame F4-JOINT: \(\mu=3\) three-digit test

Use the same \(e_1,h,u,\eta,w\). Then
\[
(\vartheta_0,\vartheta_1,\vartheta_2,\vartheta_3)
 =(1,1,\omega,\omega).
\]
For slots \(t=0,1,2\), with \(s=3-t\),
\[
(\Theta(0),\Theta(1),\Theta(2))
 =(\omega^2,\omega^2,1).
\]

Take the multiplicative residual
\[
\psi(y)=(y+1)^3=y^3+y^2+y+1.
\]
The corrected coherent digits, ordered \(t=2,1,0\), are
\[
(\gamma_2,\gamma_1,\gamma_0)=(1,\omega,\omega).
\]

The B-law units are
\[
\begin{aligned}
u(\beta_2)&=\Theta(2)w=\omega,\\
u(\beta_1)&=\Theta(1)w^2=\omega,\\
u(\beta_0)&=\Theta(0)w^3=\omega^2.
\end{aligned}
\]
Their products with the corrected coherent digits are
\[
(\omega,\omega^2,1),
\]
so the canonical residual is
\[
\psi^{(w)}(y)
 =y^3+\omega y^2+\omega^2y+1
 =(y+\omega)^3.
\]

For comparison, naive coherent digits \((1,1,1)\) give multiplicative residual
\[
y^3+y^2+\omega^2y+\omega^2
 =(y+1)(y+\omega)^2
\]
and canonical residual
\[
y^3+\omega y^2+\omega y+\omega^2
 =(y+\omega)(y+\omega^2)^2.
\]

#### Frame LP/LD

The letter prediction is
\[
z_2=\eta_2z_1^{-\lfloor9/2\rfloor}
   =\eta_2z_1^{-4}
   =\eta_2z_1^2.
\]
With \(z_2=1\), this gives
\[
\eta_2=z_1=\omega.
\]

At stage \(3\),
\[
N=\widehat n_2(19)=4x\Phi',\qquad
M=\widehat n_2(38)=512x.
\]
The exact cocycle is
\[
\operatorname{res}(N^2/M)=z_1^2=\omega^2.
\]
Hence
\[
\vartheta_{2,2}=\omega^2,\qquad
\Theta(0)=\omega,\qquad
\Theta(1)=1.
\]

In the \(w\)-quotiented decode frame:

- LD1 coherent digits are
  \[
  (c_1,c_0)=(\omega,1),
  \]
  multiplicative digits are
  \[
  (\omega,\omega),
  \]
  and the residual is
  \[
  y^2+\omega y+\omega;
  \]

- LD2 coherent digits are
  \[
  (c_1,c_0)=(\omega,\omega^2),
  \]
  multiplicative digits are
  \[
  (\omega,1),
  \]
  and the residual is
  \[
  y^2+\omega y+1.
  \]

Both quadratics are irreducible over \(\mathbf F_4\). The supplied record does
not determine the raw canonical \(w\) in these LP/LD rows; therefore no
numerical raw-\(w\) value or p-adic key sigma is preregistered for them.

### Exact implementation

1. Implement \(\mathbf F_4\) as pairs \((a,b)\in\mathbf F_2^2\) representing
   \(a+b\omega\), reduced by \(\omega^2=\omega+1\).

2. Implement
   \[
   i(k)=h^{-1}k\bmod e_1,\qquad
   a(k)=\frac{k-i(k)h}{e_1}.
   \]

3. Verify the wrap identity for every \(0\le a,b\le100\) in each numerical
   \((e_1,h)\)-frame by comparing exponent pairs exactly.

4. Verify telescopes for \(0\le s\le20\), both by direct exponent reduction and
   by the recursive product of \(\tau(su,u)\).

5. Implement coherent, multiplicative, and canonical coefficient conversions
   as
   \[
   \gamma=c\vartheta,\qquad
   c=\gamma\vartheta^{-1},\qquad
   R=\Theta w^s\gamma.
   \]

6. Factor every finite-field residual by exhaustive monic division, not by a
   probabilistic routine.

7. For X and FR-G, use two independent PARI routes:

   - Route A: expand each key in \(\mathbf Z[x]\), call `factorpadic(P,p,N)`
     with increasing \(N=20,30,40\), and extract each stable factor's degree,
     ramification index, and residue degree.

   - Route B: for every irreducible factor found over \(\mathbf Q_p\), construct
     its number field with `nfinit`, compute primes above \(p\) with
     `idealprimedec`, and recover \(e,f\); additionally evaluate \(\Phi'\) with
     `nfeltval` at the selected prime to check the prescribed tower height.
     Reject the run unless Routes A and B give identical multisets.

### M3. Planted teeth

1. **Gauge-naive tooth.**

   Replace every corrected digit \(c_t\vartheta_{i,s}\) by \(c_t\).

   Expected signatures:

   - X: constant \(108\to54\), sigma
     \(\{(2,2)\}\to\{(4,1)\}\), residual
     \(Z^2+2Z+2\to(Z+1)^2\).
   - FR-G: constant \(-54\to-27\), sigma
     \(\{(2,2)\}\to\{(4,1)\}\), residual
     \(Z^2+Z+2\to(Z-1)^2\).
   - F4-JOINT: corrected constant digit
     \(\omega^2\to\omega\), residual
     \(y^2+y+\omega\to y^2+y+1\), irreducible to split.

2. **Wrong-sign tooth.**

   Use \(\eta^{-W(t)}\) instead of \(\eta^{W(t)}\).

   In F4-JOINT quadratic degree \(2\), the constant coherent digit becomes
   \[
   \omega\omega^{-1}=1
   \]
   instead of \(\omega^2\), and the multiplicative constant becomes
   \[
   1/\omega=\omega^2
   \]
   instead of \(\omega\). The realized residual is
   \[
   y^2+y+\omega^2,
   \]
   so the exact coefficient comparison must fail even though this wrong
   residual is also irreducible. This tooth must not rely only on sigma.

3. **Misindexed-telescope tooth.**

   Replace
   \[
   \vartheta_{s+1}
   =\vartheta_s\operatorname{res}\tau(su,u)
   \]
   by
   \[
   \vartheta_{s+1}
   =\vartheta_s\operatorname{res}\tau((s+1)u,u).
   \]
   In F4-JOINT, the wrong recursion yields
   \(\vartheta_2=1\) instead of \(\omega\). It therefore changes the corrected
   quadratic constant digit from \(\omega^2\) to \(\omega\), reproducing the
   split naive residual \(y^2+y+1\). In the three-digit test it also changes
   at least one of \(\vartheta_2,\vartheta_3\), so the vector
   \((1,\omega,\omega)\) must fail.

4. **Orientation-confusion tooth.**

   Use \(\Theta=\vartheta\) rather than \(\Theta=\vartheta^{-1}\) in the
   B-law. In F4-JOINT with \(s=2\), the predicted B-unit becomes
   \[
   \omega\cdot\omega^2=1
   \]
   instead of
   \[
   \omega^2\cdot\omega^2=\omega.
   \]
   The canonical three-digit coefficient vector ceases to equal
   \((\omega,\omega^2,1)\).

Every tooth must fire. A run in which any planted tooth passes is invalid,
even if all positive tests pass.

### M4. Annex-to-frame coverage

| Annex | Frames exercising its geography |
|---|---|
| A1 GENHN | X, FR-G |
| A2 HETOW | X, FR-G, F4-JOINT |
| A3 GENTOW1 | X and FR-G for the corrected carrier; F4-JOINT for \(f_1=2\) digits |
| A4 GENTOW3 | F4-JOINT for the x-free re-scope and nontrivial digit support |
| A5 GENTOW4 | FR-G for all four seam sites; F4-JOINT for the missing \(f_1/\eta\) axes |
| A6 GENTOW6 | F4-JOINT for full \(f_1=2\) lift support and overflow-sensitive top exponents |
| A7 GENTOW2 | LP/LD for the recorded letter and \(\Theta\) values; F4-JOINT for an explicit \(w\ne1\) B-law |
| S1 GENTOW5 | F4-JOINT three-digit test for \(\gamma=c\vartheta\) and the general corrected recipe |

## 5. HONESTY LEDGER

1. The fully explicit canonical-letter exponent formula is proved only at
   level \(2\). At general level the theorem proves
   \[
   z_{i+1}=\eta_{i+1}\rho_i
   \]
   and gives the terminating lattice-reduction algorithm expressing
   \(\rho_i\) as a preceding-letter monomial. It does not claim a closed
   formula for the exponent vector at arbitrary depth.

2. The general letter-monomial reduction uses the standard MacLane tower
   normal forms and coprimality relations included in the stated tower data.
   A different normalizer or canonical-uniformizer convention changes the
   exponent vector but not the ratio formula.

3. The symbols have two inverse orientations in the pasted corpus. This note
   fixes them explicitly:
   \[
   \vartheta_{i,s}
    =\operatorname{res}\frac{\widehat n_i(u)^s}{\widehat n_i(su)}
   \]
   is the building/dictionary unit, while
   \[
   \Theta_i(t)=\vartheta_{i,f-t}^{-1}
   \]
   is GENTOW2-B″'s slot cocycle. Identifying these without inversion is false.

4. Gauge-invariance proves invariance of residual factor degrees and
   multiplicities. Translating those residual patterns into p-adic splitting
   types additionally uses the surrounding tower correctness theorem; that
   theorem is not reproved here.

5. C4 proves the support and x-free classification of exact-height lifts. It
   does not prove every note-specific clearance inequality
   \(a(m)-rh\ge0\); those inequalities remain obligations of the relevant
   tower genre.

6. This lemma does not prove GENTOW1's budgets, floors, or refinement
   transport; GENTOW4's fullness counts or separator inequalities; or the
   monomial-pair uniqueness, extraction, and attainment claims of
   GENTOW6 ANNEX-THEOREM 6.3′. It supplies only their gauge correction and
   the correct full-digit support on which those arguments must operate.

7. The LP/LD source determines the \(w\)-quotiented values
   \((\Theta(1),\Theta(0))=(1,\omega)\), but does not determine the raw
   canonical value of \(w\). This note therefore makes no invented numerical
   claim for raw \(w\) in those recorded frames.

8. F4-JOINT is a sealed exact finite graded-carrier test. It is sufficient to
   test the algebraic conclusions of this lemma, including the joint
   \(f_1=2\), \(w\ne1\), live-wrap defect. No explicit p-adic polynomial
   realizing that entire joint frame is supplied. Its displayed sigma values
   are formal residual-to-tower predictions and must not be reported as PARI
   measurements.

9. **OPEN SUB-LEMMA JOINT-PADIC-REALIZATION.** Construct an explicit polynomial
   over a specified finite extension of \(\mathbf Q_2\) whose tower data realize
   the complete F4-JOINT carrier, including canonical \(w=\omega\), and verify
   its corrected and naive sigma values by two independent p-adic oracle
   routes. This existence statement is not needed for the algebraic
   gauge-cocycle lemma and is not proved here.

---- END VERBATIM COMPOSED TEXT ----
