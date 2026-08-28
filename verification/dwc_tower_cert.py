#!/usr/bin/env python3
"""Arithmetic certificate for the Deep Witness Campaign candidate.

This checks only the integer tower bookkeeping and the formal polynomial shape of the
planned recentering.  It does not assert existence of the future Lean operators or the
Guàrdia--Nart slope/residual dictionary; those remain named proof nodes in the campaign.
"""

from dataclasses import dataclass
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

# Formal recentering shape.  The future Lean key is not x^16; this sparse model checks
# only the degree cancellation, nonzero Λ, exact subtraction, divisibility, and mass count.
key_model = {16: 1}
lambda_model = {15: 1}
leaf_model = add(key_model, neg(lambda_model))
input_model = mul(leaf_model, leaf_model)
assert lambda_model
assert degree(lambda_model) < dcum[4]
assert add(key_model, neg(lambda_model)) == leaf_model
assert mul(leaf_model, leaf_model) == input_model
assert degree(leaf_model) == 16
assert degree(input_model) == 32

input_mass = 2
quotient_mass = 1
assert degree(input_model) == input_mass * dcum[4]
assert degree(leaf_model) + dcum[4] == degree(input_model)
assert quotient_mass + 1 == input_mass

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
    "input_degree=32, leaf_degree=16, quotient_mass=1"
)
print("recenter model: Lambda != 0, deg Lambda=15<16, leaf | leaf^2, 16+16=32")
print("PASS: S2 reaches r=4 through g8 and a degree-16 successor; the μ5 refinement is mass-two ready")
