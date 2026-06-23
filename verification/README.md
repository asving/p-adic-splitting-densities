# Verification

Reproducible cross-checks for the densities. All are exact (symbolic / finite-field
enumeration / exact-rational), except the PARI oracle which samples to a stated precision.

## Scripts

- **`cert_crosschecks.py`** — 25 exact checks underlying the certificate: self-loop
  exponents and the $C_1$ rescale; the closed forms $I_2=q/(q+1)$ and
  $I_3=q^3(q^2-q+1)/((q+1)\Phi_5)$; the BB1 column-product collapse; the squarefree count
  $Q^m-Q^{m-1}$ and the Gauss/necklace irreducible count by $\mathrm{GF}(Q)$ enumeration
  ($Q\in\{2,3,5\}$); the $n=3$ type densities (palindromic, sum 1); the $n=4$ wild
  slope-$\tfrac12$ Artin–Schreier atom $q/(q+1)$ vs. the recorded oracle (incl. wild $p=2$);
  and the $n=6$ deep-wild order-3 cluster law $\beta_{(6,1)}=q^2(q-1)(q^2+1)/(q^5-1)$.
  Self-contained (needs only `sympy`). Expected output: `25 checks, 0 failures`.

- **`reconcile_om_bcfg.py`** — runs the symbolic OM density engine and checks every
  $P(n,r;q)$ and binomial moment against Bhargava–Cremona–Fisher–Gajović
  (arXiv:2101.09590), as exact rational functions, through $n=5$/$6$; also verifies
  $\sum_r P=1$ and $\sum_\sigma \rho=1$ at each $n$. Writes
  `results/reconcile_om_bcfg.json`.

- **`om_density_engine.py`** — the symbolic OM density engine (per-type monic densities
  `alpha_full(n)`; projective `rho`).

- **`padic_types.py`** — closed forms for $n\le 3$ (`monic_quad_pred`, `monic_cubic_pred`,
  `proj_cubic_pred`).

- **`quartic_oracle.py`** — the trusted ground-truth classifier via PARI `factorpadic`
  (and `nfinit`/`idealprimedec` for ramification). Used for the $n\le 4$ wild-prime checks.
  **Requires PARI/GP via `cypari2`.**

## Running

```
pip install sympy            # for the two cross-check scripts
python3 cert_crosschecks.py
python3 reconcile_om_bcfg.py

# oracle (optional, needs PARI):
pip install cypari2
python3 quartic_oracle.py
```

## `results/`

Curated inputs/outputs only: `beta{4,5,6}.json` (precomputed order-4/5/6 cluster-law
caches), `bcfg_distribution_final.json` (BCFG reference distributions), and
`reconcile_om_bcfg.json` (the reconciliation output). The raw per-run Monte-Carlo and oracle
dumps from development were pruned; they are regenerable from the engine and the oracle.
