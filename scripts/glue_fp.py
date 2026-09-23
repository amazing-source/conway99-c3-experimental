"""Elementary form of P1: the reductions of the two unimodular lattices are the SAME F_p quadratic space.
P^Q (mod p) = P^M (mod pi), since omega ≡ 1 (mod pi). Hence
   disc_Fp( P^Q mod p on F_p^m / rad ) == d_1 (mod squares) == d_w (mod squares).
Check on real graphs: rank and discriminant of the F_3-form P̄ vs d_1, d_w computed from the lattices.
For Conway 99, P^Q ≡ Q + I (mod 3).
"""
from fractions import Fraction
from glue import triangular_graph, quotients, d1_dw


def sym_form_disc_mod_p(G, p):
    """Rank and discriminant (in F_p^*, up to squares -> Legendre symbol) of the symmetric form G over F_p."""
    G = [[x % p for x in row] for row in G]
    n = len(G)
    diag = []
    active = list(range(n))
    M = [row[:] for row in G]
    while active:
        piv = next((i for i in active if M[i][i] % p), None)
        if piv is None:
            # all diagonal zero on active part: find i,j with M[i][j] != 0, replace e_i by e_i + e_j
            pair = next(((i, j) for i in active for j in active if i != j and M[i][j] % p), None)
            if pair is None:
                break  # remaining part is radical
            i, j = pair
            for k in range(n):
                M[i][k] = (M[i][k] + M[j][k]) % p
            for k in range(n):
                M[k][i] = (M[k][i] + M[k][j]) % p
            continue
        d = M[piv][piv]
        diag.append(d)
        inv = pow(d, -1, p)
        for i in active:
            if i != piv and M[i][piv] % p:
                f = M[i][piv] * inv % p
                for k in range(n):
                    M[i][k] = (M[i][k] - f * M[piv][k]) % p
                for k in range(n):
                    M[k][i] = (M[k][i] - f * M[k][piv]) % p
        active.remove(piv)
    disc = 1
    for d in diag:
        disc = disc * d % p
    leg = pow(disc, (p - 1) // 2, p) if p > 2 else 1
    return len(diag), disc, (1 if leg == 1 else -1)


def PQ_mod3(adj, perm, lam, spectrum_others, k):
    """P^Q = sum over orbit of E_lam, with E_lam = prod (A - mu)/(lam - mu); computed exactly on the quotient:
    E_lam restricted to G-invariant vectors acts as prod (Q - mu)/(lam - mu) on orbit coordinates."""
    Q, Mw = quotients(adj, perm)
    m = len(Q)
    E = [[Fraction(int(i == j)) for j in range(m)] for i in range(m)]
    for mu in spectrum_others:
        E = [[sum(E[i][t] * (Q[t][j] - (mu if t == j else 0)) for t in range(m)) / (lam - mu) for j in range(m)]
             for i in range(m)]
    assert all(x.denominator % 3 for row in E for x in row)
    return [[(x.numerator * pow(x.denominator, -1, 3)) % 3 for x in row] for row in E], Q, Mw


if __name__ == "__main__":
    for n, lam, others in ((6, -2, (8, 2)), (9, -2, (14, 5)), (12, -2, (20, 8)), (15, -2, (26, 11)), (18, -2, (32, 14))):
        adj, perm = triangular_graph(n)
        k = 2 * (n - 2)
        Pbar, Q, Mw = PQ_mod3(adj, perm, lam, others, k)
        rk, disc, leg = sym_form_disc_mod_p(Pbar, 3)
        r1, d1, rw, dw = d1_dw(Q, Mw, lam)
        print(f"T({n}) lam={lam}: F3-form rank={rk} disc={disc}  | lattice rank={r1} d1%3={d1%3} dw%3={dw%3}  "
              f"{'MATCH' if rk == r1 and disc == d1 % 3 == dw % 3 else 'MISMATCH'}")
