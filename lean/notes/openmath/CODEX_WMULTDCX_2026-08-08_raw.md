# RAW CODEX OUTPUT (verbatim below the marker) — (W-MULT-DCX-m) prover leg, session 019fdfc8-4362-7cb3-8846-e15f4ecbdffe, gpt-5.6-sol @ high, 2026-08-08 05:17 UTC. UNGRADED INPUT: the adjudicated/verified version is CODEX_WMULTDCX_2026-08-08.md.
=== VERBATIM FINAL MESSAGE BEGINS ===
VERDICT: TIER-0 — (SRC-m) is proved on T-scope(m), in fact without assuming LAW-DCX-(m+1): every re-entrant term is strictly above the relevant line, and the flat \(e_m=1\) cascade terminates by strict polynomial-degree descent.

## 1. Notation and consumed inputs

Put \(m=n-1\) and abbreviate

\[
\Phi:=\Phi_{n-1},\qquad
\widehat C:=\widehat C_{n-1},\qquad
e:=e_{n-1},
\]

\[
a:=w_{n-1}(\Phi)=e_{n-2}\gamma_{n-1},\qquad
G:=\gamma_n=ea+h_{n-1},
\]

\[
b:=B_{n-1},\qquad B:=B_n=e\,b+T_nG .
\]

The equality \(a=e_{n-2}\gamma_{n-1}\) uses \(g_{n-2}=1\), forced by
\(E_1^{\mathrm{IH}}\neq0\) through the consumed \((P\text{-DS})\)/CII clause.

The engine inputs satisfy

\[
w_{n-1}(E_0^{\mathrm{IH}})=b,\qquad
R_{n-1,b}(E_0^{\mathrm{IH}})=v^0\neq0,
\]

\[
\lambda_1:=w_{n-1}(E_1^{\mathrm{IH}})\ge b-a.
\]

Write the two canonical engine divisions as

\[
E_i^{\mathrm{IH}}\widehat C=R^i+Q^i\Phi
\qquad(i=0,1).
\]

By RM-GEN:

\[
w_{n-1}(R^0)\ge b+G,\qquad
w_{n-1}(Q^0)\ge b+G-a,
\tag{1.1}
\]

\[
w_{n-1}(R^1)\ge\lambda_1+G\ge b+G-a,
\tag{1.2}
\]

\[
w_{n-1}(Q^1)\ge\lambda_1+G-a\ge b+G-2a.
\tag{1.3}
\]

Moreover,

\[
R_{n-1,b+G}(R^0)
 =z_{n-1}^{\epsilon'}v^0\tau_{n-1},
\qquad
\tau_{n-1}=\epsilon_{n-1}(G)^{-1}c_{n-1}.
\tag{1.4}
\]

Because every displayed factor in (1.4) is nonzero, the bound for \(R^0\)
is attained:

\[
w_{n-1}(R^0)=b+G.
\tag{1.5}
\]

All applications of RM-GEN below are on

\[
T\text{-scope}(n-1):
\quad
d_0=1
\ \lor\
\bigl(e_0\ge2\ \land\ e_i\ge2\text{ for }1\le i\le n-2\bigr).
\]

Labels: (1.1)–(1.5) are **CONSUMED — [RMG], ACCEPTED**, together with
L-VNZ; the \(E_i^{\mathrm{IH}}\) data are **CONSUMED — [ILN] \((P\text{-DS})\)**.

## 2. A general line calculation

### SRC-L1 — Line of a coefficient term

**PROVED-HERE.** If \(F\) occurs at \(\Phi\)-slot \(j\) inside a
level-\(n\) digit, its level-\(n\) line is

\[
L_n(F,j):=e\,w_{n-1}(F)+jG.
\tag{2.1}
\]

If \(\deg F<\deg\Phi\), then, regarded alone as a level-\(n\) polynomial,

\[
w_n(F)=e\,w_{n-1}(F),
\tag{2.2}
\]

because its \(\Phi\)-development consists only of the slot-zero digit
\(F\).

These are direct applications of the definition of \(w_n\).

## 3. Case II-2

Here

\[
k:=T_n-e,\qquad k+2=e,
\]

so

\[
k=e-2,\qquad T_n=2e-2,\qquad e\ge2,
\tag{3.1}
\]

and therefore

\[
B=eb+(2e-2)G.
\tag{3.2}
\]

Before the second substitution, the slot-\(T_{n+1}\) coefficient is

\[
-R^0\Phi^k-(Q^0+R^1)\Phi^{k+1}-Q^1\Phi^e.
\tag{3.3}
\]

### SRC-L2 — The one-round principal term has the required read

**PROVED-HERE.** From (1.5), (3.1), and (3.2),

\[
\begin{aligned}
L_n(R^0,k)
 &=e(b+G)+(e-2)G\\
 &=eb+(2e-2)G\\
 &=B.
\end{aligned}
\tag{3.4}
\]

For \(Q^0\Phi^{k+1}\), (1.1) gives

\[
\begin{aligned}
L_n(Q^0,k+1)
 &\ge e(b+G-a)+(e-1)G\\
 &=eb+(2e-1)G-ea\\
 &=B+(G-ea)\\
 &=B+h_{n-1}.
\end{aligned}
\tag{3.5}
\]

Likewise, by (1.2),

\[
L_n(R^1,k+1)\ge B+h_{n-1}.
\tag{3.6}
\]

Thus the only term on the line \(B\) in the principal part

\[
F_{\mathrm{pr}}
:=-R^0\Phi^k-(Q^0+R^1)\Phi^{k+1}
\tag{3.7}
\]

is \(-R^0\Phi^k\).

Since \(\delta_n^{\mathrm{pl}}=1\), EQ12-ADD gives

\[
s_n(B)=T_n-e=k.
\tag{3.8}
\]

The level-\(n\) grid through \(B\) therefore has abscissae

\[
k+je,\qquad j\in\mathbb Z.
\]

Among the digit slots \(0,\ldots,e-1\), only \(k\) is on this grid. Hence

\[
R_{n,B}(F_{\mathrm{pr}})
 =\epsilon_{n-1}(b+G)\,
   \bigl(-z_{n-1}^{\epsilon'}v^0\tau_{n-1}\bigr).
\tag{3.9}
\]

EXP-KIT(b) gives

\[
\epsilon_{n-1}(b)\epsilon_{n-1}(G)
 =z_{n-1}^{\epsilon'}\epsilon_{n-1}(b+G).
\tag{3.10}
\]

Using (3.10) and
\(\tau_{n-1}=\epsilon_{n-1}(G)^{-1}c_{n-1}\),

\[
\begin{aligned}
R_{n,B}(F_{\mathrm{pr}})
 &=-v^0\epsilon_{n-1}(b)c_{n-1}\\
 &=z_n\,v^0\epsilon_{n-1}(b)\\
 &=z_n^{\delta_n^{\mathrm{pl}}}
   v^0\epsilon_{n-1}(B_{n-1}),
\end{aligned}
\tag{3.11}
\]

because \(z_n=-c_{n-1}\) and \(\delta_n^{\mathrm{pl}}=1\).

Labels: EQ12-ADD and EXP-KIT(b) are **CONSUMED — [IL]/[ILN], accepted**;
all line arithmetic is **PROVED-HERE**.

### SRC-L3 — The overflowing \(Q^1\)-term is already strictly above \(B\)

**PROVED-HERE.** From (1.3),

\[
\begin{aligned}
L_n(Q^1,e)
 &\ge e(b+G-2a)+eG\\
 &=eb+2eG-2ea\\
 &=B+2G-2ea\\
 &=B+2h_{n-1}.
\end{aligned}
\tag{3.12}
\]

Thus the overflow occurs in polynomial degree, but its entire term lies
at least \(2h_{n-1}\) above the line \(B\).

### SRC-L4 — The second round closes after one further engine division

Use

\[
\Phi^e=\Phi_n-\widehat C.
\]

Then

\[
-Q^1\Phi^e=-Q^1\Phi_n+Q^1\widehat C.
\tag{3.13}
\]

If \(Q^1\neq0\), apply RM-GEN once more:

\[
Q^1\widehat C=R^2+Q^2\Phi.
\tag{3.14}
\]

If \(Q^1=0\), take \(R^2=Q^2=0\).

Put \(q_1:=w_{n-1}(Q^1)\). RM-GEN and (1.3) give

\[
w_{n-1}(R^2)\ge q_1+G\ge b+2G-2a,
\tag{3.15}
\]

\[
w_{n-1}(Q^2)\ge q_1+G-a\ge b+2G-3a.
\tag{3.16}
\]

Therefore

\[
\begin{aligned}
L_n(R^2,0)
 &\ge e(b+2G-2a)\\
 &=eb+2eG-2ea\\
 &=B+2h_{n-1},
\end{aligned}
\tag{3.17}
\]

and

\[
\begin{aligned}
L_n(Q^2,1)
 &\ge e(b+2G-3a)+G\\
 &=eb+(2e+1)G-3ea\\
 &=B+3G-3ea\\
 &=B+3h_{n-1}.
\end{aligned}
\tag{3.18}
\]

Because \(e\ge2\),

\[
\deg(R^2+Q^2\Phi)
 <2\deg\Phi
 \le e\deg\Phi
 =\deg\Phi_n.
\tag{3.19}
\]

Hence \(R^2+Q^2\Phi\) is a valid \(\Phi_n\)-digit and no further
substitution is possible.

The final slot-\(T_{n+1}\) digit is

\[
E_0^{\mathrm{new}}
 =F_{\mathrm{pr}}+R^2+Q^2\Phi.
\tag{3.20}
\]

Equations (3.17)–(3.18) show

\[
w_n(R^2+Q^2\Phi)>B.
\tag{3.21}
\]

By READ-ADD,

\[
w_n(E_0^{\mathrm{new}})=B
\tag{3.22}
\]

and

\[
R_{n,B}(E_0^{\mathrm{new}})
 =z_n^{\delta_n^{\mathrm{pl}}}
   v^0\epsilon_{n-1}(B_{n-1}).
\tag{3.23}
\]

This proves clause (a) in Case II-2. No residue cancellation or
LAW-DCX hypothesis is used: the re-entrant contribution is strictly
above \(B\).

Labels: the substitution identity and degree telescope are
**CONSUMED — [ILN] WELL-DEF/S4.1**; RM-GEN is **CONSUMED — [RMG],
accepted**; READ-ADD is **CONSUMED — [ILN] S4.1**; the closure and bounds
are **PROVED-HERE**.

### SRC-L5 — The new top-slot contribution satisfies the \(E_1\) bound

The term \(-Q^1\Phi_n\) in (3.13) joins the slot-\((T_{n+1}+1)\) digit.
Since \(\deg Q^1<\deg\Phi\), (2.2) and (1.3) give

\[
w_n(Q^1)\ge e(b+G-2a).
\tag{3.24}
\]

The required \((P\text{-DS})\) bound is

\[
B-eG,
\]

because

\[
w_n(\Phi_n)=eG
\tag{3.25}
\]

when \(g_{n-1}=1\). From (3.2),

\[
\begin{aligned}
e(b+G-2a)-(B-eG)
 &=eb+eG-2ea-\bigl(eb+(e-2)G\bigr)\\
 &=2G-2ea\\
 &=2h_{n-1}>0.
\end{aligned}
\tag{3.26}
\]

Consequently adding \(-Q^1\) to the pre-existing \(E_1\)-digit preserves

\[
w_n(E_1^{\mathrm{new}})\ge B-eG.
\tag{3.27}
\]

This proves the level-\(n\) part of clause (b) in Case II-2.

## 4. Case II-3: the flat cascade

Here

\[
e=e_{n-1}=1,\qquad T_n=e-1=0,
\]

so

\[
B=b,\qquad G=a+h_{n-1}.
\tag{4.1}
\]

Before resolving the overflow, the coefficients are

\[
E_{0,\mathrm{pre}}
 =E_0^{\mathrm{IH}}-R^1-Q^1\Phi,
\qquad
E_{1,\mathrm{pre}}=E_1^{\mathrm{IH}}.
\tag{4.2}
\]

From (1.2),

\[
w_{n-1}(R^1)\ge b-a+G=B+h_{n-1}>B.
\tag{4.3}
\]

Therefore

\[
w_n(E_0^{\mathrm{IH}}-R^1)=B
\tag{4.4}
\]

and, since \(s_n(B)=0\),

\[
R_{n,B}(E_0^{\mathrm{IH}}-R^1)
 =\epsilon_{n-1}(B)\,v^0
 =z_n^{0}v^0\epsilon_{n-1}(B_{n-1}).
\tag{4.5}
\]

### SRC-L6 — Strict degree descent terminates the flat cascade

**PROVED-HERE.** Define recursively, whenever \(Q^r\neq0\),

\[
Q^r\widehat C=R^{r+1}+Q^{r+1}\Phi,
\qquad r\ge1,
\tag{4.6}
\]

using the canonical division by the monic \(\Phi\).

Let \(d=\deg\Phi\). Since

\[
\deg\widehat C<d,\qquad \deg Q^r<d,
\]

if \(Q^{r+1}\neq0\), then

\[
\begin{aligned}
\deg Q^{r+1}
 &=\deg(Q^r\widehat C)-d\\
 &=\deg Q^r+\deg\widehat C-d\\
 &<\deg Q^r.
\end{aligned}
\tag{4.7}
\]

The equality in the second line uses that \(O\) is a DVR and hence an
integral domain.

Thus the nonnegative integer \(\deg Q^r\) strictly decreases whenever the
next quotient is nonzero. There exists \(N\ge1\) such that

\[
Q^{N+1}=0.
\tag{4.8}
\]

This proves clause (c)'s termination assertion.

### SRC-L7 — Exact finite form of the cascade

**PROVED-HERE.** Since \(e=1\),

\[
\Phi=\Phi_n-\widehat C.
\]

Using (4.6) successively gives the finite identity

\[
-Q^1\Phi
 =
\left(\sum_{r=1}^{N}(-1)^rQ^r\right)\Phi_n
 +
\sum_{r=1}^{N}(-1)^{r+1}R^{r+1}.
\tag{4.9}
\]

Proof by induction on \(N\): the first substitution is

\[
-Q^1\Phi=-Q^1\Phi_n+R^2+Q^2\Phi.
\]

Replacing \(Q^2\Phi\) by
\(Q^2\Phi_n-R^3-Q^3\Phi\) produces the next two alternating terms.
At the final stage \(Q^{N+1}=0\), so no remainder involving \(\Phi\)
remains.

Consequently

\[
E_0^{\mathrm{new}}
 =
E_0^{\mathrm{IH}}-R^1
 +\sum_{r=1}^{N}(-1)^{r+1}R^{r+1},
\tag{4.10}
\]

\[
E_1^{\mathrm{new}}
 =
E_1^{\mathrm{IH}}
 +\sum_{r=1}^{N}(-1)^rQ^r.
\tag{4.11}
\]

Both have degree \(<\deg\Phi_n\), because \(e=1\), \(g_{n-1}=1\), and hence

\[
\deg\Phi_n=\deg\Phi,
\tag{4.12}
\]

while every \(R^r,Q^r\) has degree \(<\deg\Phi\).

### SRC-L8 — Every re-entrant flat-cascade remainder is strictly above \(B\)

Let

\[
q_r:=w_{n-1}(Q^r).
\]

From (1.3) and (4.1),

\[
q_1\ge B-a+h_{n-1}.
\tag{4.13}
\]

RM-GEN applied to (4.6) gives

\[
q_{r+1}\ge q_r+G-a=q_r+h_{n-1}.
\tag{4.14}
\]

Induction on \(r\) yields

\[
q_r\ge B-a+r h_{n-1}.
\tag{4.15}
\]

Again by RM-GEN,

\[
\begin{aligned}
w_{n-1}(R^{r+1})
 &\ge q_r+G\\
 &\ge B-a+r h_{n-1}+a+h_{n-1}\\
 &=B+(r+1)h_{n-1}.
\end{aligned}
\tag{4.16}
\]

Since \(e=1\) and \(\deg R^{r+1}<\deg\Phi=\deg\Phi_n\),

\[
w_n(R^{r+1})=w_{n-1}(R^{r+1})>B.
\tag{4.17}
\]

The sum in (4.10) is finite, so its cascade part has weight \(>B\).
Combining this with (4.4), READ-ADD gives

\[
w_n(E_0^{\mathrm{new}})=B
\tag{4.18}
\]

and

\[
R_{n,B}(E_0^{\mathrm{new}})
 =z_n^{\delta_n^{\mathrm{pl}}}
   v^0\epsilon_{n-1}(B_{n-1}),
\qquad \delta_n^{\mathrm{pl}}=0.
\tag{4.19}
\]

This proves clauses (a) and (c) in Case II-3.

### SRC-L9 — The flat-cascade top coefficient preserves its bound

From (4.15),

\[
q_r\ge q_1\ge B-a+h_{n-1}.
\tag{4.20}
\]

The required \(E_1\)-bound is

\[
B-eG=B-G=B-a-h_{n-1}.
\tag{4.21}
\]

Hence every cascade quotient satisfies

\[
\begin{aligned}
w_n(Q^r)
 &=q_r\\
 &\ge B-a+h_{n-1}\\
 &=(B-G)+2h_{n-1}\\
 &>B-G.
\end{aligned}
\tag{4.22}
\]

Since the sum in (4.11) is finite,

\[
w_n\left(\sum_{r=1}^{N}(-1)^rQ^r\right)>B-G.
\tag{4.23}
\]

The pre-existing \(E_1^{\mathrm{IH}}\) satisfies the consumed
\((P\text{-DS})\) bound \(w_n(E_1^{\mathrm{IH}})\ge B-G\). Therefore

\[
w_n(E_1^{\mathrm{new}})\ge B-G=B-eG.
\tag{4.24}
\]

This proves the level-\(n\) part of clause (b) in Case II-3.

## 5. The top-slot line and read

### SRC-L10 — The slot-\((T_{n+1}+1)\) digit is harmless

**PROVED-HERE.** In both II-2 and II-3 we have established

\[
w_n(E_1^{\mathrm{new}})
 \ge B-eG
 =B-w_n(\Phi_n).
\tag{5.1}
\]

At level \(n+1\),

\[
\Gamma''=e_nB+T_{n+1}\gamma_{n+1}.
\tag{5.2}
\]

The line of \(E_1^{\mathrm{new}}\) at slot \(T_{n+1}+1\) is at least

\[
\begin{aligned}
&e_n(B-eG)+(T_{n+1}+1)\gamma_{n+1}\\
&\quad
=\Gamma''+\gamma_{n+1}-e_n eG\\
&\quad
=\Gamma''+h_n,
\end{aligned}
\tag{5.3}
\]

because

\[
w_n(\Phi_n)=eG,\qquad
\gamma_{n+1}=e_nw_n(\Phi_n)+h_n=e_neG+h_n.
\tag{5.4}
\]

If \(e_n\ge2\), the slots \(T_{n+1}\) and \(T_{n+1}+1\) cannot both lie
on the same level-\((n+1)\) grid, whose spacing is \(e_n\); the upper slot
is off-grid.

If \(e_n=1\), the upper slot is on-grid but (5.3) places it at least
\(h_n>0\) strictly above \(\Gamma''\), so READ-ADD kills its read at
\(\Gamma''\).

This proves clause (b).

## 6. Completion of W-MULT and the digit-shape exports

### SRC-L11 — Top read and multiplicative value

The final development is

\[
P
 =
E_0^{\mathrm{new}}\Phi_n^{T_{n+1}}
 +
E_1^{\mathrm{new}}\Phi_n^{T_{n+1}+1},
\tag{6.1}
\]

with

\[
\deg E_0^{\mathrm{new}}<\deg\Phi_n,\qquad
\deg E_1^{\mathrm{new}}<\deg\Phi_n.
\tag{6.2}
\]

By clauses (a) and (b),

\[
w_{n+1}(P)=\Gamma'',
\tag{6.3}
\]

and only the slot-\(T_{n+1}\) digit contributes to the read. EQ12-ADD at
the top gives

\[
s_{n+1}(\Gamma'')=T_{n+1}-\delta e_n.
\tag{6.4}
\]

Thus \(E_0^{\mathrm{new}}\) occurs at read slot \(\delta\), and

\[
\begin{aligned}
\operatorname{val}(P)
 &=\bar z^\delta\,
   \epsilon_n(B)\,
   R_{n,B}(E_0^{\mathrm{new}})\\
 &=\bar z^\delta\,
   \epsilon_n(B)\,
   z_n^{\delta_n^{\mathrm{pl}}}
   v^0\epsilon_{n-1}(B_{n-1}).
\end{aligned}
\tag{6.5}
\]

Substituting the IH certified expression for \(v^0\) yields

\[
\operatorname{val}(P)
 =
\bar z^\delta
 \prod_{j=1}^{n}z_j^{\delta_j^{\mathrm{pl}}}
 \prod_{j=1}^{n}\epsilon_j(B_j).
\tag{6.6}
\]

By EXP-KIT(b) at each level and L6-(n),

\[
\operatorname{val}(P)
 =
\bar z^\delta\,
\operatorname{val}(\phi_\gamma)\,
\operatorname{val}(\phi_{\gamma'}).
\tag{6.7}
\]

This proves clause (d)'s multiplicative law.

Labels: the last conversion is **CONSUMED — [ILN] S4.2 L6 and S3
EXP-KIT(b), accepted**; (6.1)–(6.6) are **PROVED-HERE**.

### SRC-L12 — \((P\text{-DS})\) exports on DCX

The construction gives exactly:

\[
\operatorname{supp}_{\Phi_n}(P)
 \subseteq\{T_{n+1},T_{n+1}+1\};
\tag{6.8}
\]

\[
\deg E_i^{\mathrm{new}}<\deg\Phi_n
\qquad(i=0,1);
\tag{6.9}
\]

\[
w_n(E_0^{\mathrm{new}})=B_n;
\tag{6.10}
\]

\[
R_{n,B_n}(E_0^{\mathrm{new}})
 =
z_n^{\delta_n^{\mathrm{pl}}}
v^0\epsilon_{n-1}(B_{n-1});
\tag{6.11}
\]

\[
w_n(E_1^{\mathrm{new}})
 \ge B_n-e_{n-1}\gamma_n
 =B_n-w_n(\Phi_n).
\tag{6.12}
\]

The construction occurs only in Cases II-2/II-3, already contained in the
CII predicate, so the conditional support statement for a nonzero
\(E_1^{\mathrm{new}}\) is preserved. Cancellation may make
\(E_1^{\mathrm{new}}=0\), which is allowed.

Thus all \((P\text{-DS})\) exports of S4.6 hold on \(DCX_n\).

## 7. Family-level conclusion

### SRC-L13 — \(W\)-MULT-DCX-m

Proceed simultaneously by rung.

- The rung-one package has no DCX locus.

- Suppose the full \((P\text{-WM})/(P\text{-DS})\) package is available at
  the truncated rung. Cases I, II-1, and the non-DCX parts of II-2/II-3
  are supplied by the consumed [ILN] S4.5–S4.6 argument.

- On \(DCX_n\), SRC-L2–SRC-L12 supply the previously missing II-2/II-3
  clause, consuming RM-GEN only at engine level \(n-1\).

Therefore, whenever all called engine levels satisfy their T-scopes, the
package propagates across DCX as well. In the family notation
\(m=n-1\),

\[
\boxed{
T\text{-scope}(m)
\Longrightarrow
(W\text{-MULT-DCX-}m).
}
\tag{7.1}
\]

In particular,

\[
\boxed{
\mathrm{LAW\text{-}DCX}(m+1)
\Longrightarrow
(W\text{-MULT-DCX-}m)
}
\tag{7.2}
\]

on T-scope(m), but LAW-DCX is not used in the proof. Its role is only to
characterize when \(Q^1\neq0\); the argument above works for either value
of \(Q^1\).

No “DEV-at-depth” residue-survival lemma is needed for SRC: W-D5's
attained lower bound concerns \(Q^1\), while the re-entrant term
\(Q^1\widehat C\) acquires an additional correction weight. The exact
computations (3.17)–(3.18) and (4.16) place all such re-entrant
contributions strictly above \(B_n\).

## Dependency list

- **[RMG], ACCEPTED:** RM-GEN clauses (C-W\(_R\)), (C-W\(_Q\)),
  (C-READ), (C-EPS), canonical quotient degree bounds, and L-VNZ;
  consumed on T-scope(\(m\)).
- **[ILN], ACCEPTED:** tower identities, WELL-DEF, degree telescope,
  READ-ADD, EQ12 calculus, L6, EXP-KIT, CASE-SPLIT, and the
  \((P\text{-DS})\) input package.
- **[IL]/[IL3], accepted through the pasted packages:** base EQ12 and
  read calculus.
- **LAW-DCX-(m+1): not consumed.**
- **W-D0–W-D7/PID†, attempt grade: not consumed.**
- **E-THM, S-THM, SD-THM-A, attempt grade: not consumed.**
- **Instance evidence: not consumed.**
