"""Independent recomputation of d_1 and d_w (sympy only, no int_kernel):
det(Z^n ∩ ker B) = det(Z^n ∩ rowspace(B)_sat) and for the saturation S of a row lattice L with basis R (k x n):
   det(S) = det(R R^T) / (prod of invariant factors of R)^2.
Hermitian side: realified B, trace form Gram T (block [[2,-1],[-1,2]]):  Z-lattice det with form T equals
   det(R T R^T) / (inv. factors)^2 computed on the T-orthogonal complement ... -> we avoid that and use
   d(ker) = det(K^T T K) with K a saturated kernel basis obtained from sympy nullspace + Smith saturation.
"""
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form, hermite_normal_form
from glue import triangular_graph, quotients, realify
import math


def sat_basis_from_rational(cols):
    """cols: sympy Matrix n x r (rational). Return integer n x r basis of Z^n ∩ colspace via
    the dual trick: saturation of L = colspace ∩ Z^n  =  { x in Z^n : C x = 0 } where C spans the complement;
    here instead: scale to integers, then divide by the invariant factors using HNF of the transpose."""
    n, r = cols.shape
    M = sp.Matrix.hstack(*[c * sp.ilcm(*[sp.fraction(x)[1] for x in c]) for c in [cols[:, j] for j in range(r)]])
    # L = M Z^r (integer, full column rank). Saturation index = product of invariant factors of M.
    return M


def det_saturated(cols, T):
    """det of Z^n ∩ colspace(cols) w.r.t. integer form T."""
    M = sat_basis_from_rational(cols)
    g = 1
    snf = smith_normal_form(M, domain=sp.ZZ)
    for i in range(min(snf.shape)):
        if snf[i, i] != 0:
            g *= abs(int(snf[i, i]))
    D = (M.T * T * M).det()
    assert D % (g * g) == 0
    return int(D // (g * g))


def check(n):
    adj, perm = triangular_graph(n)
    Q, Mw = quotients(adj, perm)
    m = len(Q)
    lam = -2
    B = sp.Matrix(Q) - lam * sp.eye(m)
    ns = sp.Matrix.hstack(*B.nullspace())
    d1 = det_saturated(ns, sp.eye(m))
    R = sp.Matrix(realify(Mw, lam))
    nsw = sp.Matrix.hstack(*R.nullspace())
    T = sp.zeros(2 * m, 2 * m)
    for i in range(m):
        T[2 * i, 2 * i] = 2; T[2 * i + 1, 2 * i + 1] = 2
        T[2 * i, 2 * i + 1] = -1; T[2 * i + 1, 2 * i] = -1
    dz = det_saturated(nsw, T)
    r = nsw.shape[1] // 2
    dw = math.isqrt(dz // 3 ** r)
    assert dw * dw * 3 ** r == dz
    print(f"T({n}) lam=-2 (sympy path): d1={d1}  dw={dw}  mod3: {d1%3} {dw%3}")


if __name__ == "__main__":
    for n in (6, 9, 12):
        check(n)
