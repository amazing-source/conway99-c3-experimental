"""P1 -- 3-adic gluing congruence between the trivial-character lattice and the omega-lattice.

Claim under test (general principle, [HEUR]):
  G = C3 acting freely on a finite set X (|X| = 3m), V a G-invariant subspace of Q^X whose
  orthogonal projector is 3-integral. Let
    V_1  = invariant part of V in orbit coordinates        (subspace of Q^m)
    V_w  = omega-isotypic part in transversal coordinates (subspace of Q(w)^m)
    d_1  = det(Z^m    ∩ V_1)   (standard form)
    d_w  = det(Z[w]^m ∩ V_w)   (standard hermitian form, hermitian determinant)
  Then d_1 ≡ d_w (mod 3)   (both are prime to 3).

Everything here is exact integer arithmetic.
"""
from fractions import Fraction
import itertools, random, sys


# ---------- exact integer linear algebra ----------
def int_kernel(B, n=None):
    """Z-basis (list of column vectors) of {x in Z^n : B x = 0}; saturated by construction."""
    if n is None:
        n = len(B[0])
    B = [list(r) for r in B]
    k = len(B)
    U = [[int(i == j) for j in range(n)] for i in range(n)]  # U[row][col]

    def colop(dst, src, q):  # col dst -= q * col src
        for r in range(k):
            B[r][dst] -= q * B[r][src]
        for r in range(n):
            U[r][dst] -= q * U[r][src]

    def swap(a, b):
        if a == b:
            return
        for r in range(k):
            B[r][a], B[r][b] = B[r][b], B[r][a]
        for r in range(n):
            U[r][a], U[r][b] = U[r][b], U[r][a]

    col = 0
    for i in range(k):
        if col >= n:
            break
        while True:
            nz = [j for j in range(col, n) if B[i][j] != 0]
            if not nz:
                break
            jmin = min(nz, key=lambda j: abs(B[i][j]))
            swap(col, jmin)
            done = True
            for j in range(col + 1, n):
                if B[i][j] != 0:
                    colop(j, col, B[i][j] // B[i][col])
                    if B[i][j] != 0:
                        done = False
            if done:
                break
        if B[i][col] != 0 if col < n else False:
            col += 1
    for r in range(k):
        assert all(B[r][j] == 0 for j in range(col, n))
    return [[U[r][j] for r in range(n)] for j in range(col, n)]


def bareiss_det(M):
    M = [list(r) for r in M]
    n = len(M)
    if n == 0:
        return 1
    sign, prev = 1, 1
    for i in range(n - 1):
        if M[i][i] == 0:
            sw = next((r for r in range(i + 1, n) if M[r][i] != 0), None)
            if sw is None:
                return 0
            M[i], M[sw] = M[sw], M[i]
            sign = -sign
        for r in range(i + 1, n):
            for c in range(i + 1, n):
                M[r][c] = (M[r][c] * M[i][i] - M[r][i] * M[i][c]) // prev
        prev = M[i][i]
    return sign * M[n - 1][n - 1]


def gram_det(basis, form):
    """basis: list of vectors; form(u,v) -> int."""
    G = [[form(u, v) for v in basis] for u in basis]
    return bareiss_det(G)


def std(u, v):
    return sum(a * b for a, b in zip(u, v))


def trace_form(u, v):
    """u,v in Z^{2m}, coordinates (a0,b0,a1,b1,...) meaning a + b*w.  Tr(u * conj v) = 2ac+2bd-ad-bc."""
    s = 0
    for t in range(0, len(u), 2):
        a, b, c, d = u[t], u[t + 1], v[t], v[t + 1]
        s += 2 * a * c + 2 * b * d - a * d - b * c
    return s


def isqrt_exact(x):
    import math
    r = math.isqrt(x)
    assert r * r == x, x
    return r


# ---------- Z[w] helpers: element = (p, q) meaning p + q w, w^2 = -1 - w ----------
def zw_mul(x, y):
    p, q = x
    r, s = y
    # (p+qw)(r+sw) = pr + (ps+qr) w + qs w^2 = (pr - qs) + (ps + qr - qs) w
    return (p * r - q * s, p * s + q * r - q * s)


def w_pow(b):
    return [(1, 0), (0, 1), (-1, -1)][b % 3]


def realify(Mw, lam):
    """Integer 2m x 2m matrix of c -> (M - lam I) c acting on Z[w]^m (coords a + b w)."""
    m = len(Mw)
    R = [[0] * (2 * m) for _ in range(2 * m)]
    for U in range(m):
        for V in range(m):
            p, q = Mw[U][V]
            if U == V:
                p -= lam
            # z (a + b w) = (p a - q b) + (q a + (p - q) b) w
            R[2 * U][2 * V] += p
            R[2 * U][2 * V + 1] += -q
            R[2 * U + 1][2 * V] += q
            R[2 * U + 1][2 * V + 1] += p - q
    return R


# ---------- graphs with a free C3 action ----------
def orbit_data(n, perm):
    """perm: list, vertex -> image, of order 3 and fixed-point free. Returns labels (U,b) and inverse."""
    seen, reps = set(), []
    for v in range(n):
        if v not in seen:
            o = [v, perm[v], perm[perm[v]]]
            assert perm[o[2]] == v and len(set(o)) == 3, "not a free order-3 action"
            seen.update(o)
            reps.append(v)
    lab = {}
    for U, r in enumerate(reps):
        x = r
        for b in range(3):
            lab[x] = (U, b)
            x = perm[x]
    inv = {val: key for key, val in lab.items()}
    return reps, lab, inv


def quotients(adj, perm):
    n = len(adj)
    reps, lab, inv = orbit_data(n, perm)
    m = len(reps)
    Q = [[0] * m for _ in range(m)]
    Mw = [[(0, 0)] * m for _ in range(m)]
    for U in range(m):
        u = inv[(U, 0)]
        for V in range(m):
            acc = (0, 0)
            for b in range(3):
                if adj[u][inv[(V, b)]]:
                    Q[U][V] += 1
                    wp = w_pow(b)
                    acc = (acc[0] + wp[0], acc[1] + wp[1])
            Mw[U][V] = acc
    return Q, Mw


def d1_dw(Q, Mw, lam):
    m = len(Q)
    B = [[Q[i][j] - (lam if i == j else 0) for j in range(m)] for i in range(m)]
    K1 = int_kernel(B)
    d1 = gram_det(K1, std)
    Kw = int_kernel(realify(Mw, lam))
    r = len(Kw) // 2
    assert len(Kw) == 2 * r
    dz = gram_det(Kw, trace_form)
    assert dz % (3 ** r) == 0, (dz, r)
    dw = isqrt_exact(dz // 3 ** r)
    return len(K1), d1, r, dw


def factor_small(x):
    x = abs(x)
    f, p = {}, 2
    while p * p <= x:
        while x % p == 0:
            f[p] = f.get(p, 0) + 1
            x //= p
        p += 1
    if x > 1:
        f[x] = f.get(x, 0) + 1
    return f


def triangular_graph(n):
    V = list(itertools.combinations(range(n), 2))
    idx = {e: i for i, e in enumerate(V)}
    adj = [[int(len(set(a) & set(b)) == 1) for b in V] for a in V]
    sig = list(range(n))
    for t in range(0, n, 3):
        sig[t], sig[t + 1], sig[t + 2] = t + 1, t + 2, t
    perm = [idx[tuple(sorted((sig[a], sig[b])))] for (a, b) in V]
    return adj, perm


def eigen_ints(adj):
    import numpy as np
    ev = np.linalg.eigvalsh(np.array(adj, dtype=float))
    vals = {}
    for e in ev:
        r = int(round(e))
        if abs(e - r) < 1e-6:
            vals[r] = vals.get(r, 0) + 1
    return vals


def projector_3_integral(adj, lam, vals):
    """E_lam = prod_{mu != lam} (A - mu)/(lam - mu); check 3-integrality exactly (graph with integer spectrum)."""
    n = len(adj)
    A = [[Fraction(x) for x in r] for r in adj]
    E = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for mu in vals:
        if mu == lam:
            continue
        # E = E (A - mu I)/(lam - mu)
        new = [[sum(E[i][t] * (A[t][j] - (mu if t == j else 0)) for t in range(n)) / (lam - mu)
                for j in range(n)] for i in range(n)]
        E = new
    return all(e.denominator % 3 != 0 for r in E for e in r)


def test_graph(name, adj, perm):
    vals = eigen_ints(adj)
    Q, Mw = quotients(adj, perm)
    k = sum(adj[0])
    print(f"== {name}: n={len(adj)}, spectrum {vals}")
    for lam in sorted(vals):
        if lam == k:
            continue
        integ = projector_3_integral(adj, lam, vals)
        r1, d1, rw, dw = d1_dw(Q, Mw, lam)
        ok = (d1 - dw) % 3 == 0
        print(f"   lam={lam:>3}: E 3-integral={integ}  rank1={r1} d1={d1} {factor_small(d1)}  "
              f"rank_w={rw} dw={dw} {factor_small(dw)}  d1 mod3={d1%3} dw mod3={dw%3}  "
              f"{'CONGRUENT' if ok else 'NOT congruent'}")


if __name__ == "__main__":
    for n in (6, 9, 12):
        adj, perm = triangular_graph(n)
        test_graph(f"T({n})", adj, perm)
