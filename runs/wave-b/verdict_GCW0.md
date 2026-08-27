# Verdict GCW0 — GC-13 F1/F3 print-read and exact wiring law

Unit GCW0, 2026-08-27.  Deliverables: the `[GCW-0]` amendment at the bottom of
`docs/in-progress/GC13_WIRING_2026-08-27.md` and the optional zero-new-axiom elaboration probe
`leanfinal/scratch/GCW0_probe.lean`.  No production Lean file or leanspec file was edited;
no commit was made.

## Decision

* **F2=P2 inherited** from the orchestrator: `GC13Wiring` is a standalone `Prop` record
  demanded by chapter-I suppliers at arising witnesses.
* **F1 = scalar-read relation, abstract D.44 surface.**  Keep
  `N : NormSection G`, `q : ℤ`, and `R : G → Kt`; relate
  `R (N.n (s*q))` to the receiver image of the FGMN polynomial read.  Do not assert a
  nonsensical lattice-equals-polynomial equality and do not hard-wire
  `arenaNormSection0` into P2.  The arising-witness views already pin `N.n` to the
  transported Laurent normalizer and live `R` to that same witness's `towerRead`.
* **F3 = DEFINE in the source, law in split Lean.**  EFF.T3.21 says “Define” and sets
  `w_i = R_{i+1,k̄_i}(n̂_i(u_{i+1}))`; GENTOW2 B′ defines the per-grade factor by the same
  residual read, and B″ then proves the peel/power identity.  There is no independent
  source gauge read whose equality is proved.  Because Lean's PK-1 split carrier made
  `towerRead` free, the faithful source definition must appear as a signed P2 law.
  Witness assembly may enact it definitionally only after signing (the P3/D-D12 fence).

## Exact signed-law candidate

```lean
universe uT

/-- GC-13's read/normalizer dictionary at one D.44 site. -/
structure GC13Wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    (N : NormSection G) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (φ : W.fld r →+* Kt) : Prop where
  read_norm : ∀ s : ℕ, 1 ≤ s → s ≤ f' →
    R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u')))
```

The two easy-to-drift tokens are fixed by prior adjudications:

* grade `e' * (s * u')`, not `s * u'` — OPEN-DICT-2 full-current clearing;
* `chainNormBelow r`, not `chainNorm r` — the source's below-current-key `n̂_i`.

`A` is absent intentionally.  IFC2 discharged the theta half independently; this record
contains exactly the remaining read dictionary and no stronger content.

## Print-read basis

1. `spec/EFF-T3.md` EFF.T3.21 / `T3_COCYCLE_TELESCOPE_2026-08-12.md` §5 pins
   `N(q)=n̂_i(u_{i+1})`, `N(sq)=n̂_i(su_{i+1})`, then defines
   `w_i=R_{i+1,k̄_i}(n̂_i(u_{i+1}))`.
2. `GENTOW2_PROOF_2026-08-09.md` S5.1 lines 489–523 defines the full per-grade family
   `u(β) := R_{3,β}(n̂₂(β̂))`.  S5.2 lines 705–752 defines the normalizer cocycle, takes
   `w := u(k̄)=R_{3,k̄}(n̂₂(u₃))`, and proves the peel equality; lines 740–752 explicitly
   use `N=n̂₂(u₃)` and the scalar residual read.  The read is defined; its B-law
   factorization is proved.
3. `MU3_CAMPAIGN_2026-08-26.md` §2 decides both the full-current cleared grade and the
   below-current normalizer index (`chainNormBelow I r k := chainNorm I (r-1) k`).
4. `FGMNCALCULUS_FIELDLIST_2026-08-24.md` §8 items 3–4 classify the missing scalar
   specialization/field transport and normalizer-letter compatibility as
   OPEN-DICT-3/4.
5. `C130vw.lean` pins `N.n` through `GaugeFamilyViewEq`, and pins live `R` to the same
   arising witness's `towerRead` through `ArenaFamilyViewEq`.  This is why the law can and
   should retain D.44's abstract exported binders.

## Consumer check

For the μ₃ instance, if

```lean
hwire : GC13Wiring N q R (s2Mu3Calculus h2 hq) φ
```

then

```lean
hwire.read_norm 1 le_rfl le_rfl
```

elaborates as exactly the `hread` argument of
`IFC2.s2Mu3_gentowWWindow_of_hread`.  The probe theorem `s2_consumer_shape` passes that
projection directly, without `simpa`, casts, or rewriting.  IFC2's
`s2Mu3_hread_iff` separately reduces the equation to the S2 normalization
`R (N.n ((1 : ℕ) * q)) = 1`, confirming that the record discharges exactly one binder.

## Validation

```text
lake build Uniformity.ChapI.IFC2
lake env lean scratch/GCW0_probe.lean
```

Both exited 0.  The probe contains zero `sorry`, zero `axiom`, and no declaration beyond
the proposed structure plus the consumer-shape theorem.  `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` for both declarations: the expected Lean-core
footprint, with no new axiom.

The continuation audit re-ran both commands after reading the whole blueprint and the
specified D-chapter, GENTOW2, OPEN-DICT-2, OPEN-DICT-3/4, and IFC2 sources.  It found no
reason to revise the predecessor's five `[GCW-0]` sections; the appended continuation
closure marks the decision final.

## Handoff

GCW-1 can sign the displayed sitewise record verbatim.  The chapter-I amendment should
quantify it at each consumed live level under the existing arising-witness guard, using
that guard's own `(N, q j, R j)` exports and the corresponding calculus/receiver.  It must
not treat `s2_gentowW_of_read_one` as supply; that theorem remains only the fenced freedom
half of the underdetermination argument.
