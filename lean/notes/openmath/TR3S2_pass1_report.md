The core S3–S5 compose identity survives verification. However, the note contains one false universal claim about key divergence and two material justification gaps.

## Findings

1. **CRITICAL ERROR — universal key-divergence claim is contradicted by its own falsifier**

> “The two key classes COINCIDE at e₀ = 1 … and DIVERGE at e₀ ≥ 2 (measured: 20 of the 52 tower instances diverge, exactly the preregistered twist-visible set, S8.2).”

This is false as stated. Only 20 of the 52 tested towers diverge. The script’s actual criterion is:

```python
some k < g1 has psi1_k != 0
and z1^(theta*e1*(g1-k)) != 1
```

Thus divergence occurs precisely when the character is visible on the support of `ψ₁`, not merely when `e₀ ≥ 2`. The note itself elsewhere acknowledges this condition:

> “which is ∼ ψ₁ ONLY when the character is invisible on ψ₁'s support.”

Consequently, the table claim

> “the state-key convention BIFURCATES on (ii) … PROVED + measured”

is also overbroad unless “bifurcates” means only that the conventions can differ. Any dependent claim that all stratum-(ii) states have distinct key classes fails. I stopped accepting that universal branch. The matched-label transport and ORD-INV were checked independently below.

2. **JUSTIFICATION GAP — FGMN-normalized key transformation omits the necessary initial-slot argument**

> “By (TR3-S2-form) these transform into each other through the character: the FGMN-normalized key has  
> `R_λ(Φ₂^h) = T_{c⁻¹}ψ₁`…”

The two-form gives, initially,

\[
\psi_1(y)
 = \bar z^{\theta s_0(\Phi_2^h)}
   R_\lambda(\Phi_2^h)(cy).
\]

The displayed conclusion requires \(s_0(\Phi_2^h)=0\). That likely follows from monicity, the fixed degree \(e_1g_1\deg\Phi_1\), and the degree-\(g_1\) side read, analogously to step 1’s GMN-lawful-key argument. But step 0 neither states those hypotheses nor performs that argument. Under the requested semi-formal rigor bar, “By the two-form” is insufficient.

The script checks `s == 0` for its constructed harness keys, but finite testing does not prove this for every shared FGMN-normalized key.

3. **JUSTIFICATION GAP — the units-only refutation assumes an unproved universal witness-realization result**

> “take f with two consecutive on-line slots whose GMN coefficients \(c^G_s,c^G_{s+e_1}\) are both nonzero (any two-slot realization; the harness builds them at will).”

and

> “Concretely: any f whose two consecutive on-line GMN coefficients are EQUAL…”

Conditional on such an \(f\), the argument is sound: the FGMN coefficient ratio is \(c=\bar z^{\theta e_1}\), and under any relabeling \(\sigma'_1=\tau\circ\sigma_1\) it becomes \(\tau(c)\neq1\); a per-argument scalar cannot change a coefficient ratio. Thus it cannot equal the GMN ratio \(1\).

What is missing is a displayed general construction proving that an equal-nonzero-coefficient, consecutive-slot witness exists for every state with \(c\neq1\). “The harness builds them at will” is numerical evidence, not a theorem. Therefore the note proves refutation for the displayed witness class, but has not justified its universal “whenever \(c\neq1\)” scope.

The A6 meter tests only failure of the naive identity under the fixed concrete identification. It does not test resistance to every possible field relabeling.

## Declared attack points

### A. EXP and the ordinate bookkeeping

This part is correct.

For an on-line outer slot \(S=s_j\),

\[
w_1(a_S)=\beta_j,\qquad
u_S=w_1(a_S)+S\,w_1(\Phi_1)
=\beta_j+S e_0g_0h_0.
\]

Thus the corrected-\(\epsilon\) exponent uses the equation-(12) pair

\[
e_0u+s h_0=\beta_j,
\]

while GMN’s \(t_1\) correctly uses the distinct ordinate \(u_S\). Multiplying the FGMN exponent by \(e_0\) gives

\[
e_0(\ell'_0s-\ell_0u+m_0)=s_1-\ell_0\beta_j.
\]

Meanwhile,

\[
e_0\left(
\frac{s_1-\ell_0u_S}{e_0}
+\ell_0g_0h_0S
\right)
=s_1-\ell_0\beta_j.
\]

The \(S e_0g_0h_0\) term from display (18) is indeed load-bearing and cancels exactly against the slot character. No confusion between equation-(12)’s \(u\) and GMN’s \(u_S\) occurs in the compose calculation.

### B. Level-1 slot weight

The recomputation is correct:

\[
\begin{aligned}
\delta_{m'}
&=\frac{\beta}{e_0}
 -(s(\beta)+m'e_0)\frac{h_0}{e_0}\\
&=\frac{\beta-s(\beta)h_0}{e_0}-m'h_0\\
&=u(\beta)-m'h_0.
\end{aligned}
\]

The \(E_1=e_0\) dilation and stride \(e_0\) are both correctly placed. There is no off-by-one.

The congruence argument also works: on-line \(m\) satisfies \(mh_0\equiv\beta\pmod{e_0}\), hence \(m\equiv\ell_0\beta\equiv s(\beta)\pmod{e_0}\). Since \(m\ge0\) and \(0\le s(\beta)<e_0\), the resulting progression index is nonnegative.

### C. No-absorption and key relabeling

The no-absorption passage is not a complete displayed general argument because witness realization is assumed, as finding 3 records.

The key-relabeling passage likewise omits the \(s_0=0\) derivation for the FGMN-normalized class, as finding 2 records.

## Remaining compose chain

Subject to the explicitly consumed operator pins, every S2–S5 step checks:

- The \(\sigma_1\) construction follows once A-GEN at \(\Phi_1\), monicity, and the lawful degree \(g_0\) are accepted. The top \(\Phi_0\)-digit forces \(s_1(\Phi_1)=0\).
- A-GEN’s support dichotomy is valid. Evaluation in \(K_0\) is nonzero because a nonzero reduced digit of degree below \(d_0\) cannot vanish at the degree-\(d_0\) root class.
- Outer support equality follows from
  \[
  e_1u_i+ih_1=e_1w_1(a_i)+i\gamma_2.
  \]
- The per-slot coefficient calculation uses A-GEN and EXP with the correct inputs.
- The degree bound
  \[
  \left\lfloor\frac{e_0g_0-1-s(\beta_j)}{e_0}\right\rfloor\le g_0-1
  \]
  makes evaluation at \(\bar z\) injective on the relevant nonzero polynomial.
- Reindexing \(j=j_0+k\) gives exactly
  \[
  \sigma_1(R^F_2(f))(y)
  =\bar z^{\theta s_0(f)}
   R_\lambda(f)(\bar z^{\theta e_1}y).
  \]

Therefore the claimed discrepancy really is a per-argument scalar times a fixed variable rescaling.

## ORD-INV

ORD-INV is correctly stated. For any single shared key \(\Phi_2\), the two-form applied both to \(f\) and to \(\Phi_2\) gives the same automorphism \(T_c:y\mapsto cy\). Hence

\[
\operatorname{ord}_{R_\lambda(\Phi_2)}R_\lambda(f)
=
\operatorname{ord}_{\psi_2^F}R_2^F(f),
\]

up to harmless nonzero scalar associates and transport through \(\sigma_1\).

TS2c and TS2d genuinely support this:

- TS2c tests both matched key conventions.
- TS2d tests both resulting matched-label order equalities.
- Run 1’s 214 failures are exactly the deliberately mismatched-label comparison.
- Run 2 reports zero failures for both corrected pairings.

This does not support universal key divergence; it supports convention-independent matched-key transport.

## Script/output reconciliation

The advertised counts are internally exact:

- 52 towers.
- 68 samples per tower, giving \(52\cdot68=3536\) for TS2a/b/d.
- 16 \(e_0=1\) control towers, giving \(16\cdot68=1088\).
- Total:
  \[
  3536+3536+52+3536+1088=11748.
  \]
- The displayed 20/52 meter and histogram \(3192+182+162=3536\) match.
- Run 1’s \(20+214=234\) total violations also matches.

The script does not test:

- construction or well-definedness of \(\sigma_1\), which its header explicitly admits;
- the FGMN-internal Corollary-5.15/properness leg, explicitly excluded;
- the universal no-absorption claim against every field identification;
- the general existence of equal-coefficient two-slot witnesses.

I attempted a fresh execution, but the provided execution environment failed before Python started because its sandbox launcher could not find `bwrap`. The supplied outputs are nevertheless arithmetically and statically consistent with the script.

TR3S2-P1 FINDINGS: 1 critical, 2 gaps
VERDICT: CRITICAL