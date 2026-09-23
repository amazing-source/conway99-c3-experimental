"""P1 extension to G-sets WITH fixed points (needed for the 'fixed triangle' case).
X = m free orbits (coords 3U,3U+1,3U+2) + f fixed points.  V G-stable, projector 3-integral.
beta = dim V^G - dim V_w  (= number of trivial summands of F = P Z_3^X).  If beta = 0, F is free and the
claim is:  d_1 := det_b( Z^X ∩ V^G ) / 3^r   ≡   d_w := det( Z[w]^m ∩ V_w )   (mod 3).
For beta > 0 the lemma does not apply (violations are allowed there; we just record them).
"""
import random, sys
from collections import Counter
from glue import gram_det, std, trace_form, isqrt_exact
from glue_random import sat_lattice, realify_vec, times_w


def g_act(x, m, f):
    y = list(x)
    for U in range(m):
        for b in range(3):
            y[3 * U + (b + 1) % 3] = x[3 * U + b]
    return y


def w_coeffs(x, m):
    return [(x[3 * U] - x[3 * U + 1], x[3 * U + 2] - x[3 * U + 1]) for U in range(m)]


def sample(m, f, t, R, rng):
    n = 3 * m + f
    xs = [[rng.randint(-R, R) for _ in range(n)] for _ in range(t)]
    span = []
    for x in xs:
        y = x
        for _ in range(3):
            span.append(y)
            y = g_act(y, m, f)
    S = sat_lattice(span, n)
    dS = gram_det(S, std)
    if dS % 3 == 0:
        return None
    Nx = []
    for x in xs:
        a, b = x, g_act(x, m, f)
        c = g_act(b, m, f)
        Nx.append([a[i] + b[i] + c[i] for i in range(n)])
    Lam = sat_lattice(Nx, n)
    r1 = len(Lam)
    cs = [w_coeffs(x, m) for x in xs]
    vecs = [realify_vec(c) for c in cs] + [realify_vec(times_w(c)) for c in cs]
    if all(v == 0 for vec in vecs for v in vec):
        rw, dw = 0, 1
    else:
        Vw = sat_lattice(vecs, 2 * m)
        rw = len(Vw) // 2
        dz = gram_det(Vw, trace_form)
        dw = isqrt_exact(dz // 3 ** rw)
    beta = r1 - rw
    dL = gram_det(Lam, std) if r1 else 1
    return beta, r1, dL, rw, dw


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    stats, bad = Counter(), []
    for _ in range(N):
        m, f = rng.randint(1, 5), rng.randint(1, 4)
        t = rng.randint(1, 3)
        res = sample(m, f, t, rng.choice([1, 1, 2]), rng)
        if res is None:
            stats["not 3-integral"] += 1
            continue
        beta, r1, dL, rw, dw = res
        if beta != 0:
            stats[f"beta={beta} (lemma n/a)"] += 1
            continue
        v3 = 0
        x = dL
        while x % 3 == 0:
            x //= 3
            v3 += 1
        if v3 != r1:
            bad.append(("v3(det Lambda) != r", r1, dL))
            continue
        d1 = x
        stats[f"beta=0: d1%3={d1%3} dw%3={dw%3}"] += 1
        if (d1 - dw) % 3:
            bad.append((m, f, t, d1, dw))
    print(dict(stats))
    print("violations (beta=0):", len(bad))
    for b in bad[:10]:
        print("  ", b)
