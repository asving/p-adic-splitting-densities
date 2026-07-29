# MovesU RE-RATIFICATION (Codex, 2026-07-30): REJECT 6/1 — convergence real (C2/C6/G1/G2 REPAIRED; r_is_solve pins the solve) but the "15 fenced typed statements" claim was FALSE (bare Props with docstrings — the writer mislabel caught by ratification); tree/classifier unpinned; RegPin missing bsplit/beta/act/menu; RegP still strengthened; zfType only degree products (the (e,f) refinement free); cl7_bound automatic. Round 2 charged with the C9 homes (MovesX weight/progress Props BUILT; ramIdx/resDeg for (e,f)).

I’ll audit this as proposition semantics again, not as an implementation-intent review. I’ll first inspect the actual MovesU/MovesS declarations and build status, then map every prior 7+2 finding to exact retyped clauses and sweep the new seams (`UpstreamKernelStatements`, `TreeSeam`, `SolveSeam`, `RegPin`, `ZpBridge`, and `theoremU`) for vacuity or quantifier drift.

The first decisive contradiction is already in the submitted source: the residual pack is not “note-faithful typed statements.” Its own declaration says “Every slot below is STILL a bare `Prop`,” and all 15 fields have type `Prop`. I’m continuing the sweep because the retype also introduces substantive seams beyond that issue—especially the roster pin, the finite-tree premise, and the claimed \(\mathbb Z_p\) identification.

The narrow repairs do land in several places: `R = S.R` is exported; `r_is_solve` ties that family to `MovesS.Rsh`; `(U-n)` is a theorem conjunct; `sq2_partial` no longer imports VP-SOUND; and literal/ACT agreement for `S.R` is now stated. The remaining failures are semantic, not cosmetic: the residual ledger remains truth-instantiable, `RegPin` omits several operative objects, finite-tree content is partly baked into data, and `ZpBridge` identifies only factor-degree products—not the \((e,f)\) splitting type asserted by Theorem U.

# REJECT (6 CRITICAL / 1 GAP)

The retype makes several real improvements, but it does not satisfy the stated charge. Most decisively, the claimed “15 note-faithful typed statements” are explicitly still bare `Prop` fields.

## Prior findings re-audited

| Prior finding | Classification | Result |
|---|---|---|
| C1 — bare `Prop` ledger | CRITICAL | Not repaired |
| C2 — assumed operative stacks | — | Substantially repaired |
| C3 — objects not pinned | CRITICAL | Partially repaired only |
| C4 — surrogate `(REG-p)` roster | CRITICAL | Not fully repaired |
| C5 — incorrect regularity gate | CRITICAL | Missing clause repaired; strengthening remains |
| C6 — bracket not exported | — | Repaired |
| C7 — no genuine \(\mathbb Z_p\) density | CRITICAL | Degree shape only; \((e,f)\) missing |
| G1 — enlarged `sq2_partial` slice | — | Repaired |
| G2 — witness not identified | — | Repaired |

## CRITICAL 1 — The residual ledger is expressly still bare `Prop`

The source says:

```lean
Every slot below is STILL a bare `Prop`
```

and declares:

```lean
structure UpstreamKernelStatements where
  weightCharge : Prop
  progressX2 : Prop
  trackCount : Prop
  dnDuty : Prop
  genuineIncrement : Prop
  rel1 : Prop
  ...
  sibJcMulti : Prop
  ctsmSyntax : Prop
  m1m5X1aM4bJcInv : Prop
```

The capstone merely consumes these tags:

```lean
cl2 : KR.weightCharge
cl3 : KR.progressX2
cl7 : KR.trackCount ∧ KR.dnDuty ∧ KR.genuineIncrement
...
cl14_16 : KR.m1m5X1aM4bJcInv
```

“Fenced,” “disclosed,” owner comments, and docstrings have no proposition-level effect. One may instantiate every field with `True`. In particular, the bundled final field erases the content of CL-14, CL-15, CL-16, and the untyped part of CL-19 simultaneously.

The built rows—such as `MovesS.RegP`, `LedgerIV`, `PolyGeomLaws`, `wsh17_pin`, and the `jPCell` carrier—are genuine improvements. They do not cure the remaining 15 bare tags.

## Prior C2 — Substantially repaired

The former direct fields named `finiteness_stack` and `solve_stack` are gone.

The count identity is now proved from:

```lean
structure TreeSeam ... where
  treeOf : ...
  thr_le : ...
  count_tie : ...
```

and the solve result is derived from:

```lean
structure SolveSeam ... where
  series_tie : ...
  r_is_solve : ...
```

together with `RegPin.detHyp`, `rsh_interp`, and `r_bdd`.

These are strong conditional seam statements, but they now contain typed mathematical equations and reach the real `MovesS.Rsh`. Thus the narrow prior complaint that the final two stacks themselves were assumed verbatim is repaired.

## CRITICAL 2 — Canonical trees and the classifier remain abstract surrogates

`r_is_solve` successfully pins `S.R`, but the analogous classifier/tree pin is absent.

The operative tree link is:

```lean
treeOf : ∀ ...,
  {f : Box p n N // X.canonical N f = some σ} → F.Tree σ
```

Nothing in its type identifies `F.Tree σ` with the owner corpus’s complete finite realizable canonical trees, or `treeOf` with \(T_{\rm can}^{\tau}\). `count_tie` constrains the masses of fibers of this arbitrary map, but does not supply that identification.

Likewise:

```lean
canonical : ∀ N, Box p n N → Option (SplittingType n)
```

remains an abstract classifier. Stability, VP-SOUND, and a count-compatible `treeOf` constrain it, but do not state that it is the decomposition-note canonical algorithm.

Thus prior C3 is repaired for `SolveData.R`, but not for the principal tree/classifier objects.

## CRITICAL 3 — `RegPin` does not pin the complete operative roster

Several important components of `RegData` have no equation to the real §S objects.

Most notably, `RegPin` has no:

```lean
bsplit_pin
betaLeg_pin
act_pin
```

The declaration itself admits:

```lean
The β-leg ENTRY tie ... recorded residual.
```

The only terminal pin is also weak:

```lean
bterm_pin : ∀ ...,
  ∃ σ' ∈ C.chain.Sigmas,
    D.bterm b i = MovesS.bTerm ... σ' ...
```

This permits an instance-selected `σ'` for every row rather than identifying the designated assembled entry.

More seriously, the active-value operation remains free data:

```lean
act : RatFunc ℚ → ℕ → ℚ
```

and `RegPin` never relates it to the real CTS-M active semantics. An instance can define `D.act g q₀` to be literal evaluation wherever convenient.

The separate `MenuData M` is also not re-keyed to `C.T` or the real outcome catalogue. Hence:

```lean
cl11_ksub : KsubM1C1 M
cl13_wf : MenuWF M
```

may hold for a toy menu unrelated to the solve.

The block/state/K/iota/J/W/count pins are useful, but they do not establish the exact roster demanded by `(r1)`–`(r2)`.

## CRITICAL 4 — The formal `RegP` is still stronger than the note’s named schema

The missing active-agreement clause was added:

```lean
∀ σ,
  (S.R σ).eval ... = D.act (S.R σ) p
```

That repairs the incomplete half of prior C5.

But `RegP` also retains:

```lean
∀ σ, DefinedAt (S.R σ) (p : ℚ)
```

and the new agreement conjunct as independent premises. The note defines `(REG-p)` by `(r1)` and `(r2)` and states definedness/agreement of \(R_\sigma(p)\) as consequences of the typed assembly.

The code openly acknowledges this as:

```lean
the honest explicitly-carried strengthening of the displayed schema
```

Disclosure removes the word “silent”; it does not make the proposition equivalent to the note’s `(REG-p)`. `theoremU` consequently adjudicates a potentially smaller set of primes than the statement of record.

Moreover, because `D.act` is unpinned, the added agreement is not yet agreement with the note’s active value.

## Prior C6 and G2 — Repaired

The capstone now exports both required clauses:

```lean
R = S.R
```

and

```lean
∀ σ N,
  (evalℝ ⟨R⟩ σ p - X.env N) * ...
      ≤ X.decided σ N ∧
  X.decided σ N
      ≤ evalℝ ⟨R⟩ σ p * ...
```

`SolveSeam.r_is_solve` further identifies `S.R` with `MovesS.Rsh` under the transported determinant hypothesis. These are proper proposition-level repairs.

## CRITICAL 5 — `ZpBridge` does not encode the \((e,f)\) splitting type

The bridge reaches genuine objects:

```lean
Polynomial ℤ_[p]
Polynomial ℚ_[p]
```

which is substantial progress. But its factorization law states only:

```lean
(zfType g).map (fun ef => ef.1 * ef.2)
  = factors.map Polynomial.natDegree
```

Therefore it determines only the multiset of products \(ef\), i.e. factor degrees. It does not require either coordinate to be the actual ramification index or residue degree.

For a degree-six irreducible factor, for example, `(1,6)`, `(2,3)`, `(3,2)`, and `(6,1)` are indistinguishable to `zf_factor`. The free function

```lean
zfType : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)
```

may select any such refinement.

The source itself concedes:

```lean
the refinement ... into its ramification index e and residue degree f
... is not yet typed
```

Consequently `zpDmass` is a density of an HC-2-supplied degree refinement, not yet the note’s splitting density of type \(\sigma=(e_i,f_i)\). Calling it “factors to σ” in `theoremU`’s documentation overstates the formal proposition.

## CRITICAL 6 — CL-7 finiteness is baked in and its typed bound is vacuous

`FiberSeries` already requires:

```lean
thrSlice : ∀ σ, ℕ → Finset (Tree σ)
```

so finiteness of every threshold slice is part of the data before TRACK-COUNT is supplied.

The alleged typed CL-7 conclusion is:

```lean
cl7_bound : ∃ B : ℕ → ℕ, ∀ σ N,
  (F.thrSlice σ N).card ≤ B N
```

For a fixed instance, this follows merely because `SplittingType n` is finite: take the maximum of the finitely many slice cardinalities for each `N`. It does not encode:

- the TRACK assignment;
- a bound on track-opening events;
- the denominator duty;
- the genuine-increment claim;
- an explicit formula \(T(n,N)\);
- uniformity in \(p\).

Because `CapstoneLedger` is itself per-\(p\), its witness `B` may also depend on `p`, `X`, and `F`. The real CL-7 mechanics remain only the three bare tags in `KR`.

Thus the tree seam proves an algebraic partition identity, but the note’s derivation of finite canonical-tree families is not represented.

## GAP 1 — The evaluated checksum is still assumed

The lower bracket consumes:

```lean
rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1
```

as a ledger field, and `un_bracket` uses it directly:

```lean
LS.rs4_eval hreg
```

The source acknowledges that this should be derived from:

```lean
rs4_checksum : ∑ σ, S.R σ = 1
```

plus defined evaluation, but says the derivation has not landed. This is typed and plausibly derivable, so I classify it as a gap rather than a critical semantic substitution.

## Prior G1 — Repaired

`sq2_partial` now assumes exactly:

```lean
seam : TreeSeam n p X F
```

It no longer imports VP-SOUND or the whole former `FinStack`. The local hypothesis-slice defect is repaired.

## Verdict

The retype successfully repairs the exported witness, the exported bracket, the direct stack fields, and the local SQ.2 hypothesis slice. It also creates meaningful links to the real MovesS solve.

It cannot be ratified because:

- the claimed residual typed ledger is literally 15 bare `Prop` slots;
- the classifier/canonical-tree object remains unpinned;
- the regularity roster omits `bsplit`, β-entry, ACT, and real-menu pins;
- `RegP` remains a strengthened gate;
- the \(\mathbb Z_p\) bridge does not type the actual \((e,f)\) invariants;
- CL-7 finiteness is structurally assumed and its stated bound is automatic.

**Verdict: REJECT (6 CRITICAL / 1 GAP).**

I could not run the Lean build because the provided managed command sandbox failed to launch (`bubblewrap` is unavailable). This verdict is therefore a statement-semantic audit of the complete source reproduced in the charge; none of the rejection grounds depends on proof compilation.