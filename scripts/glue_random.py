"""Stress test of the P1 principle on random G-invariant subspaces of Q^{3m} with 3-integral projector.
For each sample: d_S = det(Z^{3m} ∩ V) must be prime to 3; then compare d_1 and d_w mod 3.
"""
import random, sys
from collections import Counter
import sympy as sp
from glue import int_kernel, gram_det, std, trace_form, isqrt_exact, factor_small


def sat_lattice(vectors, n):
    """Z^n ∩ Q-span(vectors)."""
    A = sp.Matrix(vectors)  # rows
    ns = A.nullspace()  # basis of complement (w.r.t. dot product)
    if not ns:
        return [[int(i == j) for j in range(n)] for i in range(n)]
    rows = []
    for v in ns:
        den = sp.ilcm(*[sp.fraction(x)[1] for x in v])
        rows.append([int(x * den) for x in v])
    return int_kernel(rows, n)


def w_coeffs(x, m):
    """c_U = sum_b x(U,b) w^{-b}, as (p,q) with p + q w ;  w^{-1} = w^2 = -1 - w, w^{-2} = w."""
    out = []
    for U in range(m):
        a0, a1, a2 = x[3 * U], x[3 * U + 1], x[3 * U + 2]
        # a0 + a1 w^2 + a2 w = a0 + a1(-1-w) + a2 w = (a0 - a1) + (a2 - a1) w
        out.append((a0 - a1, a2 - a1))
    return out


def realify_vec(c):
    v = []
    for p, q in c:
        v += [p, q]
    return v


def times_w(c):
    # w (p + q w) = p w + q w^2 = -q + (p - q) w
    return [(-q, p - q) for p, q in c]


def g_act(x, m):
    # g (U,b) -> (U,b+1): (g x)(U,b+1) = x(U,b)
    y = [0] * (3 * m)
    for U in range(m):
        for b in range(3):
            y[3 * U + (b + 1) % 3] = x[3 * U + b]
    return y


def sample(m, t, R, rng):
    xs = [[rng.randint(-R, R) for _ in range(3 * m)] for _ in range(t)]
    span = []
    for x in xs:
        y = x
        for _ in range(3):
            span.append(y)
            y = g_act(y, m)
    S = sat_lattice(span, 3 * m)
    if len(S) != 3 * t:
        return None
    dS = gram_det(S, std)
    if dS % 3 == 0:
        return ("not3int", dS)
    V1 = sat_lattice([[sum(x[3 * U:3 * U + 3]) for U in range(m)] for x in xs], m)
    d1 = gram_det(V1, std)
    cs = [w_coeffs(x, m) for x in xs]
    Vw = sat_lattice([realify_vec(c) for c in cs] + [realify_vec(times_w(c)) for c in cs], 2 * m)
    r = len(Vw) // 2
    dz = gram_det(Vw, trace_form)
    assert dz % 3 ** r == 0
    dw = isqrt_exact(dz // 3 ** r)
    return ("ok", dS, d1, dw, len(V1), r)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    stats = Counter()
    bad = []
    for it in range(N):
        m = rng.randint(1, 6)
        t = rng.randint(1, max(1, min(3, m)))
        R = rng.choice([1, 1, 2, 3])
        res = sample(m, t, R, rng)
        if res is None:
            stats["degenerate"] += 1
            continue
        if res[0] == "not3int":
            stats["not 3-integral"] += 1
            continue
        _, dS, d1, dw, r1, rw = res
        key = f"d1%3={d1%3}, dw%3={dw%3}"
        stats[key] += 1
        if (d1 - dw) % 3:
            bad.append((m, t, dS, d1, dw))
    print(dict(stats))
    print("violations:", len(bad))
    for b in bad[:10]:
        print("  ", b)
