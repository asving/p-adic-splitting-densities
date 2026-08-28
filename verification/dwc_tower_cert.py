#!/usr/bin/env python3
"""Arithmetic certificate for the revised Deep Witness Campaign candidate.

This checks the integer tower bookkeeping, the formal polynomial shape of the planned
recentering, parent/quotient key-freeness in the sparse control model, and multiplicity of
the selected residual factor.  It does not assert existence of the future Lean operators
or the Guàrdia--Nart slope/residual dictionary; those remain named proof nodes in the
campaign.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import gcd


@dataclass(frozen=True)
class Stage:
    e: int
    f: int
    u: int

    @property
    def ell(self) -> int:
        return self.e * self.f

    @property
    def econst(self) -> int:
        return self.e * self.f * self.u


def product(values: list[int]) -> int:
    answer = 1
    for value in values:
        answer *= value
    return answer


def solve(u: int, e: int, k: int) -> int:
    """C.83's finite rung solve, specialized to positive e."""
    return next(b for b in range(e) if (b * u) % e == k % e)


def degree(poly: dict[int, int]) -> int:
    support = [exponent for exponent, coefficient in poly.items() if coefficient]
    return max(support, default=-1)


def add(left: dict[int, int], right: dict[int, int]) -> dict[int, int]:
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, 0) + coefficient
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def neg(poly: dict[int, int]) -> dict[int, int]:
    return {exponent: -coefficient for exponent, coefficient in poly.items()}


def mul(left: dict[int, int], right: dict[int, int]) -> dict[int, int]:
    result: dict[int, int] = {}
    for i, a in left.items():
        for j, b in right.items():
            result[i + j] = result.get(i + j, 0) + a * b
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def scale(poly: dict[int, Fraction], scalar: Fraction) -> dict[int, Fraction]:
    return {exponent: scalar * coefficient for exponent, coefficient in poly.items()
            if scalar * coefficient}


def to_fraction_poly(poly: dict[int, int]) -> dict[int, Fraction]:
    return {exponent: Fraction(coefficient) for exponent, coefficient in poly.items()
            if coefficient}


def divmod_poly(
    dividend: dict[int, Fraction], divisor: dict[int, Fraction]
) -> tuple[dict[int, Fraction], dict[int, Fraction]]:
    """Exact Euclidean division over Q for sparse coefficient dictionaries."""
    assert divisor
    quotient: dict[int, Fraction] = {}
    remainder = dict(dividend)
    divisor_degree = degree(divisor)
    divisor_lead = divisor[divisor_degree]
    while remainder and degree(remainder) >= divisor_degree:
        exponent = degree(remainder) - divisor_degree
        coefficient = remainder[degree(remainder)] / divisor_lead
        quotient[exponent] = quotient.get(exponent, Fraction(0)) + coefficient
        for i, value in divisor.items():
            target = i + exponent
            remainder[target] = remainder.get(target, Fraction(0)) - coefficient * value
            if remainder[target] == 0:
                del remainder[target]
    return quotient, remainder


def monic_normalize(poly: dict[int, Fraction]) -> dict[int, Fraction]:
    if not poly:
        return {}
    return scale(poly, Fraction(1, 1) / poly[degree(poly)])


def gcd_poly(left: dict[int, int], right: dict[int, int]) -> dict[int, Fraction]:
    a = to_fraction_poly(left)
    b = to_fraction_poly(right)
    while b:
        _, remainder = divmod_poly(a, b)
        a, b = b, remainder
    return monic_normalize(a)


def is_coprime(left: dict[int, int], right: dict[int, int]) -> bool:
    return gcd_poly(left, right) == {0: Fraction(1)}


def factor_order(poly: dict[int, int], factor: dict[int, int]) -> int:
    """ord_factor(poly), for the monic sparse residual controls used below."""
    order = 0
    remainder = to_fraction_poly(poly)
    divisor = to_fraction_poly(factor)
    while remainder:
        quotient, rem = divmod_poly(remainder, divisor)
        if rem:
            break
        order += 1
        remainder = quotient
    return order


# Landed S2 stages followed by the proper depth-four extension recorded by the
# examples-first recurrence u_next = e_next * E_current + 1.
stages = {
    1: Stage(2, 1, 1),
    2: Stage(2, 1, 5),
    3: Stage(2, 1, 21),
    4: Stage(2, 1, 85),
}

dcum = {i: product([stages[j].ell for j in range(1, i + 1)]) for i in stages}
assert dcum == {1: 2, 2: 4, 3: 8, 4: 16}
assert all(stages[i].ell >= 2 for i in range(2, 5))
assert all(gcd(stages[i].u, stages[i].e) == 1 for i in range(2, 5))

floor_rows = []
for i in range(1, 4):
    lhs = stages[i + 1].e * stages[i].econst
    rhs = stages[i + 1].u
    assert lhs < rhs
    floor_rows.append((i, lhs, rhs))
assert floor_rows == [(1, 4, 5), (2, 20, 21), (3, 84, 85)]


def tower_norm(i: int, k: int) -> tuple[int, int, list[int]]:
    """C.83 ``towerNorm i k`` as (uniformizer, X, key exponents)."""
    if i == 0:
        slot = solve(stages[1].u, stages[1].e, k)
        return ((k - slot * stages[1].u) // stages[1].e, slot, [])
    next_stage = stages[i + 1]
    b = solve(next_stage.u, next_stage.e, k)
    m = (k - b * next_stage.u) // next_stage.e
    uniformizer, x_power, keys = tower_norm(i - 1, m)
    return (uniformizer, x_power, keys + [b])


def tower_norm_degree(row: tuple[int, int, list[int]]) -> int:
    _, x_power, keys = row
    return x_power + sum(exponent * dcum[j] for j, exponent in enumerate(keys, start=1))


# The two new B-1 normalizers.  These are the next worked rows after the landed
# towerNorm 1 21 = (4,0,[1]).
assert tower_norm(2, 85) == (8, 0, [0, 1])
assert tower_norm_degree(tower_norm(2, 85)) == 4 < dcum[3]
assert tower_norm(3, 171) == (1, 1, [1, 1, 1])
assert tower_norm_degree(tower_norm(3, 171)) == 15 < dcum[4]

# At tower depth 3, the next proper μ4 datum builds the degree-16 key from g8.
depth3_operator = Stage(2, 1, 85)
assert depth3_operator.e * stages[3].econst == 84 < depth3_operator.u
assert depth3_operator.e * depth3_operator.f * dcum[3] == dcum[4] == 16

# The all-proper depth-4 continuation is the worked 341 row, but it cannot put its odd
# key grade in the preceding group: this is the same numerical warning as 21 mod 2.
depth4_all_proper = Stage(2, 1, 341)
assert depth4_all_proper.e * stages[4].econst == 340 < depth4_all_proper.u
assert depth4_all_proper.e * depth4_all_proper.f * dcum[4] == 32
assert depth4_all_proper.u % depth4_all_proper.e != 0
assert tower_norm(3, 341) == (16, 0, [0, 0, 1])
assert tower_norm_degree(tower_norm(3, 341)) == 8 < dcum[4]

# Chosen μ5 refinement at the already-built depth-four tower.  Its product e'f'=1 keeps
# the normalized-existence leaf at degree 16, and e'=1 removes the previous-group parity
# obstruction.  It is operator data, not a fifth proper DeepTower stage.
depth4_refinement = Stage(1, 1, 171)
assert depth4_refinement.e * stages[4].econst == 170 < depth4_refinement.u
assert gcd(depth4_refinement.u, depth4_refinement.e) == 1
assert depth4_refinement.u % depth4_refinement.e == 0
leaf_degree = depth4_refinement.e * depth4_refinement.f * dcum[4]
assert leaf_degree == dcum[4] == 16

# Formal recentering shape.  The future Lean polynomials are not these sparse polynomials;
# the model checks degree cancellation, nonzero Lambda, exact subtraction, divisibility,
# mass, and the two key-freeness obligations.  The constant term on key_model makes the
# coprimality controls non-degenerate (unlike the old x^16 placeholder).
key_model = {16: 1, 0: 1}
lambda_model = {15: 1}
leaf_model = add(key_model, neg(lambda_model))
cofactor_model = add(key_model, {0: 1})
input_model = mul(leaf_model, cofactor_model)
rejected_square_input = mul(leaf_model, leaf_model)
assert lambda_model
assert degree(lambda_model) < dcum[4]
assert add(key_model, neg(lambda_model)) == leaf_model
assert mul(leaf_model, cofactor_model) == input_model
assert degree(leaf_model) == 16
assert degree(cofactor_model) == 16
assert degree(input_model) == 32
accepted_quotient, accepted_remainder = divmod_poly(
    to_fraction_poly(input_model), to_fraction_poly(leaf_model)
)
square_quotient, square_remainder = divmod_poly(
    to_fraction_poly(rejected_square_input), to_fraction_poly(leaf_model)
)
assert not accepted_remainder
assert accepted_quotient == to_fraction_poly(cofactor_model)
assert not square_remainder
assert square_quotient == to_fraction_poly(leaf_model)
assert is_coprime(input_model, key_model)              # parent BlockData.hkeyfree
assert is_coprime(cofactor_model, leaf_model)           # quotient BlockData.hkeyfree
assert is_coprime(rejected_square_input, key_model)      # old parent gate passed
assert not is_coprime(leaf_model, leaf_model)           # DWV C1 control

input_mass = 2
quotient_mass = 1
assert degree(input_model) == input_mass * dcum[4]
assert degree(cofactor_model) + dcum[4] == degree(input_model)  # MP1StepCore.hmass
assert quotient_mass + 1 == input_mass

# A mass-one input cannot satisfy hmass: every quotient BlockData has degree at least D,
# while hmass would demand deg(quot.F) + D = D.
mass_one_input_degree = dcum[4]
minimum_quotient_degree = dcum[4]
assert minimum_quotient_degree + dcum[4] != mass_one_input_degree

# Residual-ring controls.  Assigning R(leaf)=psi=X+1 and the distinct cofactor a unit
# residual makes the revised input have ord_psi 1.  This tests multiplicity algebra only;
# it does not certify GN slope/key indexing.  The rejected square has order 2.
psi_model = {1: 1, 0: 1}
unit_residual = {0: 1}
input_residual = mul(psi_model, unit_residual)
rejected_square_residual = mul(psi_model, psi_model)
assert factor_order(input_residual, psi_model) == 1
assert factor_order(rejected_square_residual, psi_model) == 2

deep_live = [j for j in range(5) if 3 <= j < 4]
assert deep_live == [3]

print("chosen tower stages:")
for i, stage in stages.items():
    print(
        f"  i={i}: (e,f,u)=({stage.e},{stage.f},{stage.u}), "
        f"E={stage.econst}, Dcum={dcum[i]}"
    )
print(f"floor rows (i, lhs, rhs): {floor_rows}")
print("depth-3 operator: (e',f',u')=(2,1,85), successor degree=16")
print("  towerNorm 2 85=(8,0,[0,1]), normalizer degree=4<8")
print("rejected depth-4 proper operator: (2,1,341), 341 mod 2 = 1")
print("  towerNorm 3 341=(16,0,[0,0,1]), normalizer degree=8<16")
print("chosen depth-4 refinement: (e',f',u')=(1,1,171), leaf degree=16")
print("  towerNorm 3 171=(1,1,[1,1,1]), correction degree=15<16")
print(
    "counts: proper_stages=4, live_deep_levels=1, full_input_mass=2, "
    "input_degree=32, leaf_degree=16, cofactor_degree=16, quotient_mass=1"
)
print("accepted input: F0=leaf*(keyAt4+1), Lambda != 0, deg Lambda=15<16")
print("  exact_quotient=keyAt4+1, parent_keyfree=True, quotient_keyfree=True")
print("  hmass=16+16=32, ord_psi(residual)=1")
print("rejected controls: leaf^2 parent_keyfree=True but quotient_keyfree=False")
print("  exact_quotient=leaf, ord_psi(residual)=2")
print("  mass-one leaf input hmass=False (minimum quotient degree 16 gives 16+16 != 16)")
print("FORMAL PASS: the distinct-factor input clears arithmetic/key-free/multiplicity controls")
print("  NOT CERTIFIED: GN principal-slope membership, key indexing, or selected-factor identity")
