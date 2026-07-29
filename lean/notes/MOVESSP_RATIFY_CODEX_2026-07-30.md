# MovesSp AS-BUILT RATIFICATION (Codex, 2026-07-30): REJECT 3M/2N with the COMBINATORIAL CORE RATIFIED (SnRaw3_eq, 53-card, menu exactness, DAG, loops, terminals — the sealed numbers genuine). M1/M2/M3 = the instantiation seam: SP_COMP needs the ACTUAL tree (CanTreeModel from built MovesT TreeModel), non-vacuity needs the real-instance witness, hVerdictPin retypes to the VPPinned/TB-CAP vocabulary. N2 = the recorded R6 erratum (quadruple-confirmed). ADJUDICATION: accepted as wave-C instantiation charges.

I’ll audit the checked-in MovesSp corpus against the quoted note, focusing on theorem faithfulness, non-vacuity, SP-DAG, and the sealed n=3 catalogue/menu exactness. I’ll also verify the build and kernel-assumption surface rather than relying on the pasted “67/67” label.

The combinatorial core is materially stronger than a mere hand list: the supplied statements prove `SnRaw3_eq`, the 53-cardinality/Nodup result, global successor exactness, and the rank-based `6n²` collapsed-walk bound. The pressure point is SP-COMP: its “engine” is an arbitrary hypothesis structure, and the file itself says those laws are open and the verdict pin is weak/trivially dischargeable. I’m separating that conditional interface result from an actual theorem about the canonical tree of the given polynomial.

## Verdict: REJECT (3M/2N)

The finite combinatorial catalogue is convincingly formalized, including the 53-letter instance and successor menu. The advertised faithfulness and non-vacuous SP-COMP theorem are not.

### Ratified portions

| Note statement | Formal corpus | Classification |
|---|---|---|
| “\(\mathcal S_n^{raw}\) is finite and independent of \(p\)” | `SP_FIN`, with `SnRaw` prime-free by type and the stated cardinal bound | RATIFIED |
| “the loop-collapsed menu graph is a DAG … ≤ \(6n²\) letters” | `rank_strict`, `SP_DAG_walk`, and `SP_DAG_words` establish strict rank growth, the length bound, and finiteness | RATIFIED |
| “\(|\mathcal S_3^{raw}|=53\)” | `SnRaw3_eq` identifies the inductive catalogue with `catalogue3`; `catalogue3_card` proves length 53 and `Nodup` | RATIFIED |
| Sealed n=3 successor map | `menu3_exact_global` proves, for every catalogue source and arbitrary target, `SuccStep 3 s s' ↔ s' ∈ menuMap3 s` | RATIFIED |
| Exactly two n=3 loop letters | `loops3` pins `[loopQ3, loopQ23]` | RATIFIED |
| Five confirming letters | `terminal3`, together with the definitions of `Succ` and `Out`, gives no species successors and all three verdict labels | RATIFIED |

Thus the sealed number is genuinely exact, not merely “53 hand-written terms”: `SnRaw3_eq` supplies the essential extensional equality.

### Major findings

**M1 — SP-COMP is an interface closure lemma, not the note’s actual-tree completeness theorem.**

The note quantifies over:

> “every \(f\) … every chain \(\eta \in T_{\rm can}(f)\)”

The formal theorem instead quantifies over an arbitrary:

> `M : CanTreeModel n p f`

Its fields already assume `hRoot`, `hStage`, and `hCoh`, which are precisely the engine/coherence facts needed to construct catalogue membership. There is no definition of the actual canonical tree and no theorem constructing `CanTreeModel` from it. `SP_COMP` consequently proves:

> assumed root datum + assumed stage laws + assumed coherence/budgets ⇒ inductive catalogue membership.

That closure induction is correct, but it does not ratify the note’s completeness claim about the actual move engine.

**M2 — non-vacuity fails for every \(n\ne1\).**

Although `CanTreeModel.hTotal` makes `Branch` inhabited, it does not require any branch to contain a catalogue read. For, say, \(n=2\), a model can take:

- `Branch := Unit`,
- `len _ := 0`,
- arbitrary `datum`,
- `verdict _ := none`.

Every read-law premise is then false, and `hVerdictPin` is also vacuous. Therefore `SP_COMP`, `SP_COMP_edges`, and `SP_COMP_collapsed` can all hold with zero reads and no engine content.

The special field `hN1` repairs this only at \(n=1\). It does not establish general non-vacuity or connect zero-read branches to VP’s legitimate τ-hen cases.

**M3 — `hVerdictPin` does not carry the stated residual D4R.0-K(c).**

The note says the residual comprises:

> “alphabet \(V\) + halting rule \(\tau\) + the uniform detection cap”

The formal field is only:

```lean
hVerdictPin :
  ∀ η m, len η = (m : ℕ∞) → 0 < m → (verdict η).isSome
```

This asserts merely that some label exists after a finite nonempty word. It does not express:

- which verdict is correct;
- where τ fires;
- the parent-read versus confirming-read pin;
- mutual exclusivity;
- the detection cap.

The corpus comments explicitly concede that this hypothesis is “weak by design” and “trivially dischargeable.” It therefore cannot faithfully represent the note’s claimed remaining conditionality.

### Narrow findings

**N1 — `CatalogueWord` covers only confirming-\(W=1\) endings.**

Its laws require a nonempty word whose last letter has `W = 1`. The note also allows finite words ending at a `V_term` edge from a continuing letter, plus infinite branches prefixwise. Those cases are discussed through `CanTreeModel`, but are not instances of the datatype named `CatalogueWord`. The τ-word results are therefore correct only for the confirming-ending subtype.

**N2 — the entrance roster deliberately changes the quoted note.**

The note says direct μ=2 entrances are:

> “root▸(1,2) [R4/R5 rows]”

`entrance3_patterns` proves three rows:

```lean
[rootR4sel12, rootR5sel12, rootR6sel12]
```

The corpus calls the note’s bracket an “ERRATUM CANDIDATE.” The correction is consistent with the sealed menu law—R6 really does select `(1,2)`—but it is not a literal ratification of the supplied note.

### Sealed-data classification

`Nstar3six`, its domain, and its six values are faithfully pinned as data. They are not formal realizability theorems: no level-\(N\) boxes, canonical engine execution, witnesses, or “iff \(N\ge N_p^*\)” predicate appears in the formalization. This matches the corpus’s own “gate-censused DATA … never theorems” disclaimer.

I could not independently rerun the claimed 67/67 build because the workspace command sandbox could not start (`bwrap` unavailable). Nothing visible in the supplied source contains a live `sorry`; the rejection is about statement strength and faithfulness, not the displayed proof terms or the n=3 enumeration.