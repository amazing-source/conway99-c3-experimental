"""D2 -- p=3 criterion for all feasible srg, including actions with fixed points whose Brauer quotient vanishes (beta=0).
E_theta = a I + b A + c J (rational).  3-integral iff 3 ∤ (r-s) and v_3(k-theta') >= v_3(v).
beta = rank_F3( E_theta[Fix] mod 3 ).  beta = 0 configurations of Fix (reduction a,b,c mod 3):
   Fix empty (needs 3 | v); Fix = clique K_f (needs a+c ≡ 0 and, if f>=2, b+c ≡ 0);
   Fix = coclique (needs a+c ≡ 0 and, if f>=2, c ≡ 0); general Fix: a+c ≡ 0, b+c ≡ 0 on edges, c ≡ 0 on non-edges.
If every prime of (r-s) is ≡ 1 (mod 3): d_w ≡ 1 and d_1 ≡ prod_{q | v, q ∤ 3(r-s)(k-theta')} q^{v_q(v)} (mod 3).
"""
import sys
from fractions import Fraction
from criterion_scan import feasible, primes, vp


def mod3(fr):
    fr = Fraction(fr)
    assert fr.denominator % 3
    return (fr.numerator * pow(fr.denominator, -1, 3)) % 3


def analyse(v, k, l, mu, r, s):
    out = []
    d = r - s
    if d % 3 == 0 or any(q % 3 != 1 for q in primes(d)):
        return out
    for th, ot in ((r, s), (s, r)):
        if vp(k - ot, 3) < vp(v, 3):
            continue
        a = Fraction(-ot, th - ot)
        b = Fraction(1, th - ot)
        c = Fraction(-(k - ot), v * (th - ot))
        a3, b3, c3 = mod3(a), mod3(b), mod3(c)
        prod = 1
        for q in primes(v):
            if q == 3 or d % q == 0 or (k - ot) % q == 0:
                continue
            prod *= q ** vp(v, q)
        verdict = "EXCLUDED" if prod % 3 == 2 else "allowed"
        # which beta=0 fixed sets exist in principle
        cfg = []
        if v % 3 == 0:
            cfg.append("free")
        if (a3 + c3) % 3 == 0:
            cfg.append("K1")
            if (b3 + c3) % 3 == 0:
                cfg.append("cliques")
            if c3 == 0:
                cfg.append("cocliques")
            if c3 == 0 and b3 == 0:
                cfg.append("any-Fix")
        out.append((th, verdict, prod, (a3, b3, c3), cfg))
    return out


if __name__ == "__main__":
    VMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1300
    print("srg(99,14,1,2):", analyse(99, 14, 1, 2, 3, -4))
    n_app, hits = 0, []
    for v in range(5, VMAX + 1):
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
                res = analyse(v, k, l, mu, r, s)
                if res:
                    n_app += 1
                for th, verdict, prod, abc, cfg in res:
                    if verdict == "EXCLUDED" and cfg:
                        hits.append((v, k, l, mu, r, s, th, prod, abc, cfg))
    print(f"feasible parameter sets where the criterion applies: {n_app}")
    print(f"order-3 automorphisms with beta=0 EXCLUDED for {len(hits)} (set, theta):")
    for h in hits:
        print("   srg(%d,%d,%d,%d) r=%d s=%d theta=%d J-prod=%d E=(a,b,c) mod 3=%s  beta=0 possible for: %s" % h)
