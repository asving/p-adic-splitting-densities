#!/usr/bin/env python3
"""
Exhaustive numerical certificate for the conjectured history-resolved
all-degree order-1 law, specialized to

    n in {3,4}, q in {2,3}, 2 <= N <= 6.

Only the Python standard library is used.

Enumeration convention
----------------------
A degree-d branch is read over Q = q^d in the equal-characteristic
digit model F_Q[t]/(t^N).  A node C_m(s) consists of

    a_j with v(a_j) >= (m-j)*s + 1,  0 <= j < m.

Every exact lower polygon and every residual lattice digit is enumerated.
Repeated linear residual roots on e=1 sides recurse to C_a(k), where a
is the root multiplicity and -k is the side slope.  Repeated factors of
degree > 1, and repetitions on e > 1 sides, are composite-stage exits
and are not order-1 keys.

The "OBS" count enumerates actual residual polynomials and assignments
of child histories to their actual roots.  The "LAW" count uses only
factorization censuses, free-slot exponents, transfer normalizations,
and orbit factors.

The script also checks:
  * every W12-L0 history-resolved quadratic control formula;
  * all relevant translation matrices are invertible;
  * all relevant coprime residual multiplication maps have full rank;
  * four deliberately corrupted laws fail.

Output:
  PATTERNS ...          exact level-0 configurations and their C0 counts
  KEY ... OBS ... LAW   one row for every realized letter-free key
  CONTROL-L0 ...        W12-L0 control totals
  TEETH ...             mandatory mutation failures
  FINAL VERDICT: LAW-CONFIRMED | MISMATCH
"""

from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import ceil, comb, factorial


# ----------------------------------------------------------------------
# Finite fields F_p and the only extensions needed here, F_{p^2}.
# Elements are integers with base-p coefficients.
# ----------------------------------------------------------------------

class Field:
    def __init__(self, p, d):
        self.p = p
        self.d = d
        self.Q = p ** d
        if d == 1:
            self.modulus = None
        elif d == 2:
            # x^2 + x + 1 over F_2; x^2 + 1 over F_3.
            self.modulus = (1, 1, 1) if p == 2 else (1, 0, 1)
        else:
            raise ValueError("Only d=1,2 are required for n <= 4")

    def add(self, a, b):
        if self.d == 1:
            return (a + b) % self.p
        a0, a1 = a % self.p, a // self.p
        b0, b1 = b % self.p, b // self.p
        return ((a0 + b0) % self.p) + self.p * ((a1 + b1) % self.p)

    def neg(self, a):
        if self.d == 1:
            return (-a) % self.p
        a0, a1 = a % self.p, a // self.p
        return (-a0) % self.p + self.p * ((-a1) % self.p)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def mul(self, a, b):
        if self.d == 1:
            return (a * b) % self.p
        a0, a1 = a % self.p, a // self.p
        b0, b1 = b % self.p, b // self.p
        c0 = a0 * b0
        c1 = a0 * b1 + a1 * b0
        c2 = a1 * b1
        m0, m1, _ = self.modulus
        c0 -= c2 * m0
        c1 -= c2 * m1
        return (c0 % self.p) + self.p * (c1 % self.p)

    def pow(self, a, n):
        r = 1
        while n:
            if n & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            n >>= 1
        return r

    def inv(self, a):
        if a == 0:
            raise ZeroDivisionError
        return self.pow(a, self.Q - 2)

    def scalar(self, a):
        return a % self.p


@lru_cache(None)
def get_field(p, d):
    return Field(p, d)


# ----------------------------------------------------------------------
# Polynomials over finite fields.  Coefficients are low to high.
# ----------------------------------------------------------------------

def ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)


def pdeg(a):
    return len(ptrim(a)) - 1


def padd(a, b, F):
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        out.append(F.add(x, y))
    return ptrim(out)


def psub(a, b, F):
    return padd(a, tuple(F.neg(x) for x in b), F)


def pmul(a, b, F):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = F.add(out[i + j], F.mul(x, y))
    return ptrim(out)


def pdivmod(a, b, F):
    a = list(ptrim(a))
    b = ptrim(b)
    db = pdeg(b)
    ib = F.inv(b[-1])
    if pdeg(a) < db:
        return (0,), tuple(a)
    q = [0] * (pdeg(a) - db + 1)
    while len(a) - 1 >= db and not (len(a) == 1 and a[0] == 0):
        k = len(a) - 1 - db
        c = F.mul(a[-1], ib)
        q[k] = c
        for j in range(db + 1):
            a[j + k] = F.sub(a[j + k], F.mul(c, b[j]))
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    return ptrim(q), ptrim(a)


def pmonic(a, F):
    a = ptrim(a)
    z = F.inv(a[-1])
    return tuple(F.mul(z, x) for x in a)


def pgcd(a, b, F):
    a, b = ptrim(a), ptrim(b)
    while not (len(b) == 1 and b[0] == 0):
        _, r = pdivmod(a, b, F)
        a, b = b, r
    return pmonic(a, F)


def monics(r, F):
    for low in product(range(F.Q), repeat=r):
        yield tuple(low) + (1,)


@lru_cache(None)
def irreducibles(p, d, r):
    F = get_field(p, d)
    if r == 1:
        return tuple(monics(1, F))
    ans = []
    for f in monics(r, F):
        good = True
        for e in range(1, r // 2 + 1):
            for g in irreducibles(p, d, e):
                _, rem = pdivmod(f, g, F)
                if rem == (0,):
                    good = False
                    break
            if not good:
                break
        if good:
            ans.append(f)
    return tuple(ans)


@lru_cache(None)
def factor_monic(p, d, f):
    F = get_field(p, d)
    rem = ptrim(f)
    out = []
    original_degree = pdeg(rem)
    for r in range(1, original_degree + 1):
        for g in irreducibles(p, d, r):
            multiplicity = 0
            while pdeg(rem) >= r:
                q, z = pdivmod(rem, g, F)
                if z != (0,):
                    break
                rem = q
                multiplicity += 1
            if multiplicity:
                out.append((g, multiplicity))
    if pdeg(rem) != 0:
        raise AssertionError(("factorization failed", p, d, f, rem))
    return tuple(sorted(out, key=lambda z: (pdeg(z[0]), z[0])))


def factor_type(p, d, f):
    return tuple(sorted((pdeg(g), a) for g, a in factor_monic(p, d, f)))


@lru_cache(None)
def residual_census(p, d, g, ftype):
    F = get_field(p, d)
    total = 0
    for f in monics(g, F):
        if f[0] != 0 and factor_type(p, d, f) == ftype:
            total += 1
    return total


# ----------------------------------------------------------------------
# Exact polygons.
# ----------------------------------------------------------------------

def cross(a, b, c):
    return ((b[0] - a[0]) * (c[1] - a[1])
            - (b[1] - a[1]) * (c[0] - a[0]))


def lower_hull(points):
    h = []
    for z in sorted(points):
        while len(h) >= 2 and cross(h[-2], h[-1], z) <= 0:
            h.pop()
        h.append(z)
    return tuple(h)


@lru_cache(None)
def node_polygons(m, s, N):
    choices = []
    for j in range(m):
        lower = (m - j) * s + 1
        if lower >= N:
            choices.append((N,))
        else:
            choices.append(tuple(range(lower, N + 1)))
    ans = set()
    for hs in product(*choices):
        if hs[0] == N:
            continue                    # non-visible constant term
        points = [(j, hs[j]) for j in range(m) if hs[j] < N]
        points.append((m, 0))
        hull = lower_hull(points)
        if hull[0][0] != 0 or hull[-1] != (m, 0):
            continue
        if all(hull[i][1] > hull[i + 1][1]
               for i in range(len(hull) - 1)):
            ans.add(hull)
    return tuple(sorted(ans))


def side_height(left, right, j):
    x0, y0 = left
    x1, y1 = right
    return Fraction(y0 * (x1 - j) + y1 * (j - x0), x1 - x0)


def polygon_height(vertices, j):
    for a, b in zip(vertices, vertices[1:]):
        if a[0] <= j <= b[0]:
            return side_height(a, b, j)
    raise AssertionError(("outside polygon", vertices, j))


def polygon_B(vertices, m, N):
    heights = [polygon_height(vertices, j) for j in range(m)]
    ceiling_sum = sum((h.numerator + h.denominator - 1) // h.denominator
                      for h in heights)
    L = sum(h.denominator == 1 for h in heights)
    return m * N - ceiling_sum - L


def polygon_L(vertices, m):
    return sum(polygon_height(vertices, j).denominator == 1
               for j in range(m))


def node_dimension(m, s, N):
    return sum(max(N - ((m - j) * s + 1), 0) for j in range(m))


def side_descriptor(left, right):
    x0, y0 = left
    x1, y1 = right
    dx = x1 - x0
    drop = y0 - y1
    g0 = __import__("math").gcd(dx, drop)
    e = dx // g0
    g = g0
    return x0, y0, x1, y1, e, g


# ----------------------------------------------------------------------
# History-resolved node enumeration.
#
# Node key:
#   ("V", m, s, vertices, sides, child_groups)
#
# sides[i] =
#   (x0,y0,x1,y1,e,g,factorization_type)
#
# child_groups[i] is the sorted tuple of child keys attached to the
# repeated linear factors on side i.
# ----------------------------------------------------------------------

@lru_cache(None)
def node_distribution(p, d, m, s, N):
    F = get_field(p, d)
    Q = F.Q
    answer = defaultdict(Fraction)

    for vertices in node_polygons(m, s, N):
        side_geometries = [
            side_descriptor(a, b) for a, b in zip(vertices, vertices[1:])
        ]

        boundary = set()
        vertex_x = {x for x, _ in vertices[:-1]}
        for j in range(m):
            if polygon_height(vertices, j).denominator == 1:
                boundary.add(j)
        boundary = tuple(sorted(boundary))

        choices = []
        for j in boundary:
            if j in vertex_x:
                choices.append(tuple(range(1, Q)))
            else:
                choices.append(tuple(range(Q)))

        B = polygon_B(vertices, m, N)
        base_weight = Fraction(Q ** B, 1)

        for digits in product(*choices):
            digit = dict(zip(boundary, digits))
            side_data = []
            actual_factorizations = []
            valid = True

            for geom in side_geometries:
                x0, y0, x1, y1, e, g = geom
                coeffs = []
                for r in range(g + 1):
                    j = x0 + r * e
                    if j == m:
                        coeffs.append(1)
                    else:
                        h = side_height((x0, y0), (x1, y1), j)
                        if h.denominator != 1:
                            raise AssertionError("side lattice error")
                        coeffs.append(digit.get(j, 0))

                # Normalize by the already-fixed right endpoint.
                z = F.inv(coeffs[-1])
                residual = tuple(F.mul(z, c) for c in coeffs)
                fac = factor_monic(p, d, residual)
                ftype = tuple(sorted((pdeg(h), a) for h, a in fac))
                side_data.append(geom + (ftype,))
                actual_factorizations.append(fac)

                for h, a in fac:
                    if a > 1 and (e != 1 or pdeg(h) != 1):
                        valid = False
            if not valid:
                continue

            child_specs = []
            for side_index, (geom, fac) in enumerate(
                    zip(side_geometries, actual_factorizations)):
                x0, y0, x1, y1, e, g = geom
                k = (y0 - y1) // (x1 - x0) if e == 1 else None
                for h, a in fac:
                    if a > 1:
                        dist = node_distribution(p, d, a, k, N)
                        if not dist:
                            valid = False
                            break
                        child_specs.append((side_index, a, k, dist))
                if not valid:
                    break
            if not valid:
                continue

            states = [([], base_weight)]
            for side_index, a, k, dist in child_specs:
                denominator = Q ** node_dimension(a, k, N)
                nxt = []
                for selected, weight in states:
                    for child_key, child_count in dist.items():
                        nxt.append((
                            selected + [(side_index, child_key)],
                            weight * child_count / denominator
                        ))
                states = nxt

            for selected, weight in states:
                groups = [[] for _ in side_data]
                for side_index, child_key in selected:
                    groups[side_index].append(child_key)
                groups = tuple(
                    tuple(sorted(gp, key=repr)) for gp in groups
                )
                key = (
                    "V", m, s, vertices, tuple(side_data), groups
                )
                answer[key] += weight

    return dict(answer)


# ----------------------------------------------------------------------
# Closed conjectured law evaluated from a node key.
# ----------------------------------------------------------------------

@lru_cache(None)
def node_law(key, p, d, N, mutation="NONE"):
    tag, m, s, vertices, sides, child_groups = key
    assert tag == "V"
    F = get_field(p, d)
    Q = F.Q

    B = polygon_B(vertices, m, N)
    if mutation == "DROP-L":
        B += polygon_L(vertices, m)

    value = Fraction(Q ** B, 1)

    for side_index, side in enumerate(sides):
        x0, y0, x1, y1, e, g, ftype = side
        census = residual_census(p, d, g, ftype)

        if mutation == "DROP-HISTORY-CENSUS" and child_groups[side_index]:
            census = 1

        if (mutation == "BASE-q-LETTERS"
                and child_groups[side_index]
                and len(ftype) == 1
                and ftype[0][0] == 1
                and ftype[0][1] > 1):
            census = p - 1

        value *= census

        by_multiplicity = defaultdict(list)
        for child in child_groups[side_index]:
            by_multiplicity[child[1]].append(child)

        for _, children in by_multiplicity.items():
            counts = Counter(children)
            orbit = factorial(len(children))
            for r in counts.values():
                orbit //= factorial(r)
            value *= orbit

        for child in child_groups[side_index]:
            cm = child[1]
            cs = child[2]
            value *= node_law(child, p, d, N, mutation)
            value /= Q ** node_dimension(cm, cs, N)

    return value


# ----------------------------------------------------------------------
# Level-0 configurations and full degree-n keys.
# ----------------------------------------------------------------------

@lru_cache(None)
def residue_configurations(n, q):
    F = get_field(q, 1)
    rows = []
    for f in monics(n, F):
        fac = factor_monic(q, 1, f)
        branches = tuple(sorted(
            ((pdeg(g), a, g) for g, a in fac),
            key=lambda z: (z[0], z[1], z[2])
        ))
        pattern = tuple(sorted((d, a) for d, a, _ in branches))
        rows.append((f, branches, pattern))
    return tuple(rows)


@lru_cache(None)
def c0_table(n, q):
    c = Counter()
    for _, _, pattern in residue_configurations(n, q):
        c[pattern] += 1
    return dict(c)


def full_distribution(n, q, N):
    answer = defaultdict(Fraction)

    for _, branches, _ in residue_configurations(n, q):
        states = [([], Fraction(1, 1))]

        for d, m, actual_factor in branches:
            if m == 1:
                options = {
                    ("SIMPLE",): Fraction(q ** (d * (N - 1)), 1)
                }
            else:
                options = node_distribution(q, d, m, 0, N)

            nxt = []
            for entries, weight in states:
                for decoration, count in options.items():
                    nxt.append((
                        entries + [(d, m, decoration)],
                        weight * count
                    ))
            states = nxt

        for entries, weight in states:
            key = tuple(sorted(entries, key=lambda z: (z[0], z[1], repr(z[2]))))
            answer[key] += weight

    return dict(answer)


def full_law(key, n, q, N, mutation="NONE"):
    pattern = tuple(sorted((d, m) for d, m, _ in key))
    value = Fraction(c0_table(n, q)[pattern], 1)

    by_dm = defaultdict(list)
    for d, m, decoration in key:
        by_dm[(d, m)].append(decoration)

    if mutation != "DROP-KAPPA0":
        for decorations in by_dm.values():
            mult = Counter(decorations)
            orbit = factorial(len(decorations))
            for r in mult.values():
                orbit //= factorial(r)
            value *= orbit

    for d, m, decoration in key:
        if m == 1:
            value *= q ** (d * (N - 1))
        else:
            value *= node_law(decoration, q, d, N, mutation)

    return value


# ----------------------------------------------------------------------
# W12-L0 control, decoded independently from m=2 node keys.
# ----------------------------------------------------------------------

def decode_l0(key, history=()):
    _, m, s, vertices, sides, child_groups = key
    if m != 2:
        raise ValueError("not an m=2 key")

    children = [
        child for gp in child_groups for child in gp
    ]
    if children:
        if len(children) != 1:
            raise ValueError("unexpected quadratic branching")
        side_index = next(i for i, gp in enumerate(child_groups) if gp)
        side = sides[side_index]
        x0, y0, x1, y1, e, g, ftype = side
        k = (y0 - y1) // (x1 - x0)
        return decode_l0(children[0], history + (k,))

    u = vertices[0][1]
    if len(vertices) == 3:
        w = vertices[1][1]
        return history, "2SIDED", (w, u - w)

    if len(vertices) != 2 or len(sides) != 1:
        raise ValueError(("unrecognized quadratic leaf", key))

    ftype = sides[0][-1]
    if u % 2 == 1:
        return history, "RAM", (u,)
    k = u // 2
    if ftype == ((1, 1), (1, 1)):
        return history, "SPLITEQ", (k,)
    if ftype == ((2, 1),):
        return history, "INERTDEEP", (k,)
    raise ValueError(("nonterminal quadratic residual", key))


def l0_formula(q, N, decoded):
    history, kind, params = decoded
    prefactor = (q - 1) ** len(history)

    if kind == "RAM":
        u, = params
        leaf = ((q - 1)
                * q ** (N - 1 - u)
                * q ** (N - (u + 1) // 2))
    elif kind == "2SIDED":
        w, other = params
        u = w + other
        leaf = (q - 1) ** 2 * q ** (2 * N - 2 - u - w)
    elif kind == "SPLITEQ":
        k, = params
        leaf = ((q - 1) * (q - 2) // 2) * q ** (2 * N - 3 * k - 2)
    elif kind == "INERTDEEP":
        k, = params
        leaf = (q * (q - 1) // 2) * q ** (2 * N - 3 * k - 2)
    else:
        raise ValueError(kind)

    return prefactor * leaf


# ----------------------------------------------------------------------
# Linear-algebra checks for the local transfer mechanisms.
# ----------------------------------------------------------------------

def matrix_rank(matrix, F):
    if not matrix:
        return 0
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0])
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        z = F.inv(a[rank][col])
        a[rank] = [F.mul(z, x) for x in a[rank]]
        for r in range(rows):
            if r != rank and a[r][col]:
                z = a[r][col]
                a[r] = [
                    F.sub(a[r][c], F.mul(z, a[rank][c]))
                    for c in range(cols)
                ]
        rank += 1
        if rank == rows:
            break
    return rank


def translation_checks():
    failures = []
    checks = 0
    for p in (2, 3):
        for d in (1, 2):
            F = get_field(p, d)
            max_m = 4 // d
            for m in range(2, max_m + 1):
                for N in range(2, 7):
                    size = m * N
                    for k in range(1, N):
                        for z in range(1, F.Q):
                            matrix = [[0] * size for _ in range(size)]
                            for j in range(m):
                                for h in range(N):
                                    out = j * N + h
                                    for i in range(j, m):
                                        shift = k * (i - j)
                                        source_h = h - shift
                                        if source_h < 0:
                                            continue
                                        scalar = F.scalar(comb(i, j))
                                        c = F.mul(scalar, F.pow(z, i - j))
                                        inp = i * N + source_h
                                        matrix[out][inp] = F.add(
                                            matrix[out][inp], c
                                        )
                            checks += 1
                            if matrix_rank(matrix, F) != size:
                                failures.append(
                                    ("translation", p, d, m, N, k, z)
                                )
    return checks, failures


def hensel_split_checks():
    failures = []
    checks = 0
    for p in (2, 3):
        for d in (1, 2):
            F = get_field(p, d)
            max_m = 4 // d
            for m in range(2, max_m + 1):
                for a in range(1, m):
                    b = m - a
                    for g in monics(a, F):
                        for h in monics(b, F):
                            if pdeg(pgcd(g, h, F)) != 0:
                                continue

                            matrix = [[0] * m for _ in range(m)]
                            # delta-g * h
                            for col in range(a):
                                for j, c in enumerate(h):
                                    matrix[col + j][col] = F.add(
                                        matrix[col + j][col], c
                                    )
                            # g * delta-h
                            for local_col in range(b):
                                col = a + local_col
                                for j, c in enumerate(g):
                                    matrix[local_col + j][col] = F.add(
                                        matrix[local_col + j][col], c
                                    )

                            checks += 1
                            if matrix_rank(matrix, F) != m:
                                failures.append(
                                    ("hensel", p, d, m, g, h)
                                )
    return checks, failures


# ----------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------

def integer_string(x):
    if isinstance(x, Fraction):
        if x.denominator != 1:
            return f"{x.numerator}/{x.denominator}"
        return str(x.numerator)
    return str(x)


def main():
    offending = []
    control_bad = []
    tooth_counts = Counter()
    total_keys = 0

    translation_count, translation_bad = translation_checks()
    hensel_count, hensel_bad = hensel_split_checks()

    for q in (2, 3):
        for n in (3, 4):
            patterns = c0_table(n, q)
            print(
                "PATTERNS",
                f"n={n}",
                f"q={q}",
                " ".join(
                    f"{pattern}:{count}"
                    for pattern, count in sorted(patterns.items(), key=repr)
                )
            )

            for N in range(2, 7):
                observed = full_distribution(n, q, N)

                for key in sorted(observed, key=repr):
                    obs = observed[key]
                    law = full_law(key, n, q, N)
                    total_keys += 1

                    status = "OK" if obs == law else "MISMATCH"
                    print(
                        "KEY",
                        f"n={n}",
                        f"q={q}",
                        f"N={N}",
                        f"OBS={integer_string(obs)}",
                        f"LAW={integer_string(law)}",
                        status,
                        repr(key)
                    )

                    if obs != law:
                        offending.append((n, q, N, key, obs, law))

                    mutations = (
                        "DROP-HISTORY-CENSUS",
                        "BASE-q-LETTERS",
                        "DROP-KAPPA0",
                        "DROP-L",
                    )
                    for mutation in mutations:
                        mutant = full_law(key, n, q, N, mutation)
                        if mutant != obs:
                            tooth_counts[mutation] += 1

                # Independent W12-L0 control at every q,N.
                control_dist = node_distribution(q, 1, 2, 0, N)
                checked = 0
                for key, obs in control_dist.items():
                    decoded = decode_l0(key)
                    expected = l0_formula(q, N, decoded)
                    checked += 1
                    if obs != expected:
                        control_bad.append(
                            (q, N, key, obs, expected, decoded)
                        )
                print(
                    "CONTROL-L0",
                    f"q={q}",
                    f"N={N}",
                    f"keys={checked}",
                    "OK" if not any(z[0] == q and z[1] == N
                                    for z in control_bad) else "MISMATCH"
                )

    print(
        "TRANSFER",
        f"translations={translation_count}",
        f"translation_bad={len(translation_bad)}",
        f"hensel_splits={hensel_count}",
        f"hensel_bad={len(hensel_bad)}"
    )

    required_teeth = (
        "DROP-HISTORY-CENSUS",
        "BASE-q-LETTERS",
        "DROP-KAPPA0",
        "DROP-L",
    )
    dead_teeth = []
    for tooth in required_teeth:
        fired = tooth_counts[tooth]
        print("TEETH", tooth, f"fired={fired}")
        if fired == 0:
            dead_teeth.append(tooth)

    bad = bool(
        offending or control_bad or translation_bad or hensel_bad or dead_teeth
    )

    if bad:
        print("OFFENDING-KEYS")
        for row in offending:
            n, q, N, key, obs, law = row
            print(
                f"n={n} q={q} N={N}",
                f"OBS={integer_string(obs)}",
                f"LAW={integer_string(law)}",
                repr(key)
            )
        for row in control_bad:
            print("CONTROL-OFFENDER", repr(row))
        for row in translation_bad:
            print("TRANSLATION-OFFENDER", repr(row))
        for row in hensel_bad:
            print("HENSEL-OFFENDER", repr(row))
        for tooth in dead_teeth:
            print("DEAD-TOOTH", tooth)
        print("FINAL VERDICT: MISMATCH")
    else:
        print(
            "SUMMARY",
            f"per_key_comparisons={total_keys}",
            f"control_mismatches={len(control_bad)}",
            f"law_mismatches={len(offending)}"
        )
        print("FINAL VERDICT: LAW-CONFIRMED")


if __name__ == "__main__":
    main()
