#!/usr/bin/env python3
"""Finite spot-certificate for the LVS live-range arithmetic.

The Lean proof in ``leanfinal/scratch/LVS_probe.lean`` is general.  This independent
enumeration makes the first non-vacuous depth and its demanded indices visible.
"""


def gauge_live(r: int, i: int) -> bool:
    return 1 <= i < r


def demanded_live_indices(r: int) -> list[int]:
    return [i for i in range(0, r + 3) if 3 <= i and gauge_live(r, i)]


expected = {
    0: [],
    1: [],
    2: [],
    3: [],
    4: [3],
    5: [3, 4],
    6: [3, 4, 5],
    7: [3, 4, 5, 6],
    8: [3, 4, 5, 6, 7],
}

observed = {r: demanded_live_indices(r) for r in expected}
assert observed == expected
assert all(bool(observed[r]) == (4 <= r) for r in observed)

for r, indices in observed.items():
    print(f"r={r}: demanded-and-live={indices}")
print("PASS: depth 2 is empty; the first real tooth is r=4, i=3")
