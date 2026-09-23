"""General p=3 criterion derived from P1 (see notes/P1_recollement.md), applied to feasible srg parameters.

For srg(v,k,lam,mu), integer eigenvalues k, r, s, 3 | v (free C3 action possible), take theta in {r,s},
theta' the other one. E_theta is 3-integral iff 3 ∤ (r-s) and v_3(k - theta') >= v_3(v).
If moreover every prime divisor of (r-s) is ≡ 1 (mod 3), then d_w ≡ 1 (mod 3) and
   d_1 ≡ prod_{q | m, q ∤ 3(r-s)(k-theta')} q^{v_q(m)}   (mod 3),    m = v/3,
so a free C3 action forces this product to be ≡ 1 (mod 3).
Output: parameter sets where the product is ≡ 2, i.e. free order-3 automorphisms are excluded.
Validation: T(n) (triangular graphs) exist with free C3 actions for 3 | n; they must never be excluded.
"""
import math, sys
from fractions import Fraction


def vp(x, p):
    x = abs(x)
    if x == 0:
        return 99
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def primes(x):
    x = abs(x)
    out, p = [], 2
    while p * p <= x:
        if x % p == 0:
            out.append(p)
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        out.append(x)
    return out


def feasible(v, k, l, mu):
    if k * (k - l - 1) != mu * (v - k - 1):
        return None
    D = (l - mu) ** 2 + 4 * (k - mu)
    sd = math.isqrt(D)
    if sd * sd != D:
        return None  # irrational eigenvalues (conference type): no rational projector
    if (l - mu + sd) % 2:
        return None
    r, s = (l - mu + sd) // 2, (l - mu - sd) // 2
    num_f = -k * (s + 1) * (k - s)
    den = (k + r * s) * (r - s)
    if den == 0 or num_f % den:
        return None
    f = num_f // den
    g = v - 1 - f
    if f <= 0 or g <= 0:
        return None
    # Krein
    if (r + 1) * (k + r + 2 * r * s) > (k + r) * (s + 1) ** 2:
        return None
    if (s + 1) * (k + s + 2 * r * s) > (k + s) * (r + 1) ** 2:
        return None
    # absolute bound
    if v > f * (f + 3) // 2 or v > g * (g + 3) // 2:
        return None
    return r, s, f, g


def criterion(v, k, r, s):
    """Return list of (theta, verdict, product) for theta with 3-integral E_theta and split (r-s)."""
    out = []
    if v % 3:
        return out
    d = r - s
    if d % 3 == 0:
        return out
    if any(q % 3 != 1 for q in primes(d)):
        return out
    m = v // 3
    for theta, other in ((r, s), (s, r)):
        if vp(k - other, 3) < vp(v, 3):
            continue
        prod = 1
        for q in primes(m):
            if q == 3 or d % q == 0 or (k - other) % q == 0:
                continue
            prod *= q ** vp(m, q)
        out.append((theta, "EXCLUDED" if prod % 3 == 2 else "allowed", prod))
    return out


if __name__ == "__main__":
    # validation on triangular graphs T(n), 3 | n
    print("Validation T(n):")
    bad = 0
    for n in range(6, 301, 3):
        v, k, l, mu = n * (n - 1) // 2, 2 * (n - 2), n - 2, 4
        fe = feasible(v, k, l, mu)
        res = criterion(v, k, fe[0], fe[1]) if fe else []
        if any(x[1] == "EXCLUDED" for x in res):
            bad += 1
            print("   T(%d) wrongly excluded:" % n, res)
    print("   T(n) wrongly excluded:", bad)
    # Conway 99
    fe = feasible(99, 14, 1, 2)
    print("srg(99,14,1,2):", fe, criterion(99, 14, fe[0], fe[1]))
    # scan
    VMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1300
    hits = []
    for v in range(3, VMAX + 1, 3):
        for k in range(1, (v - 1) // 2 + 1):
            for l in range(0, k):
                num = k * (k - l - 1)
                if num % (v - k - 1):
                    continue
                mu = num // (v - k - 1)
                if mu < 1 or mu > k:
                    continue
                fe = feasible(v, k, l, mu)
                if not fe:
                    continue
                r, s, f, g = fe
                for theta, verdict, prod in criterion(v, k, r, s):
                    if verdict == "EXCLUDED":
                        hits.append((v, k, l, mu, r, s, f, g, theta, prod))
    print(f"\nFeasible srg (v <= {VMAX}, k <= (v-1)/2) where the criterion EXCLUDES a free C3 action: {len(hits)}")
    for h in hits:
        print("   srg(%d,%d,%d,%d)  eig %d^%d, %d^%d  theta=%d  J-product=%d" %
              (h[0], h[1], h[2], h[3], h[4], h[6], h[5], h[7], h[8], h[9]))
