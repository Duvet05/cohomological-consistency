"""Check the general construction behind Theorem B (non-nilpotent groups).

H = E x| Z_q, where E = F_p^m and the generator of Z_q acts by a matrix M with no nonzero
fixed vector (p != q primes). T is the 3rd pp-power of H^[3] described in the paper:
  z = (z1, z2, z3) in H^3; marker = Q-part of z3;
  marker 0 ("Z_q sort"): value t = Q-part of z1, selector sigma = Q-part of z2;
  marker 1 ("E sort"):   selector s = Q-part of z1, value e = E-part of z1.
Relations (one for each Tseitin-type relation of the Lichter-Pago template OR_T[A1, A2]):
  Z_q: eps.t = lam      becomes  markers 0, common sigma, eps.t = (1 - sigma) * lam
  E:   eps.e = lam      becomes  markers 1, common s,     eps.e = N_s lam,
                                 N_s = (M^s - I)(M - I)^{-1}
  S:   marker(z) = 0, marker(z') = 1, sigma(z) = s(z').
We verify, for each H:
  (1) every E-relation, as a relation on the z1-coordinates, is a subgroup of H^3 (a coset);
      the Z_q-relations and S depend only on Q-parts and are preimages of affine subspaces of
      Z_q^k, which we also check;
  (2) the map e : A -> T (A = OR_T over the Tseitin-type relations) is a homomorphism;
  (3) for every selector value j the twisted systems behave as claimed: N_0 = 0, N_1 = I,
      N_j invertible for j != 0, and (1 - j) != 0 for j != 1. This is what makes the
      Lichter-Pago instances unsatisfiable over T (see the paper).

Run: python3 -I ppconstruct_schmidt.py
"""

import itertools


def matmul(A, B, p):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n)) % p for j in range(n))
                 for i in range(n))


def matvec(A, v, p):
    return tuple(sum(A[i][j] * v[j] for j in range(len(v))) % p for i in range(len(A)))


def ident(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def matpow(A, e, p):
    R = ident(len(A))
    for _ in range(e):
        R = matmul(R, A, p)
    return R


def matsub(A, B, p):
    return tuple(tuple((a - b) % p for a, b in zip(ra, rb)) for ra, rb in zip(A, B))


def matinv(A, p):
    n = len(A)
    aug = [list(A[i]) + [int(i == j) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next((r for r in range(c, n) if aug[r][c] % p), None)
        if piv is None:
            return None
        aug[c], aug[piv] = aug[piv], aug[c]
        iv = pow(aug[c][c], p - 2, p)
        aug[c] = [(x * iv) % p for x in aug[c]]
        for r in range(n):
            if r != c and aug[r][c]:
                f = aug[r][c]
                aug[r] = [(x - f * y) % p for x, y in zip(aug[r], aug[c])]
    return tuple(tuple(row[n:]) for row in aug)


class H:
    def __init__(self, name, p, q, M):
        self.name, self.p, self.q, self.M = name, p, q, M
        self.m = len(M)
        assert matpow(M, q, p) == ident(self.m), "M must have order dividing q"
        I = ident(self.m)
        for s in range(1, q):
            assert matinv(matsub(matpow(M, s, p), I, p), p) is not None, "fixed points"
        self.E = list(itertools.product(range(p), repeat=self.m))
        self.zero = tuple([0] * self.m)
        self.els = [(e, s) for s in range(q) for e in self.E]
        self.Ms = [matpow(M, s, p) for s in range(q)]
        self.Minv1 = matinv(matsub(M, I, p), p)
        self.N = [matmul(matsub(self.Ms[s], I, p), self.Minv1, p) for s in range(q)]

    def mul(self, x, y):
        (e, s), (f, t) = x, y
        return (tuple((a + b) % self.p for a, b in zip(e, matvec(self.Ms[s], f, self.p))),
                (s + t) % self.q)


def eps_combo(G, eps, vecs):
    out = [0] * G.m
    for e_, v in zip(eps, vecs):
        out = [(o + e_ * x) % G.p for o, x in zip(out, v)]
    return tuple(out)


def check(G):
    p, q = G.p, G.q
    signs = list(itertools.product([1, -1], repeat=3))
    # (3) twist matrices
    I = ident(G.m)
    assert G.N[0] == tuple(tuple(0 for _ in range(G.m)) for _ in range(G.m))
    assert G.N[1] == I
    for j in range(1, q):
        assert matinv(G.N[j], p) is not None
    # (1) E-relations as subgroups of H^3 on z1 coordinates
    for eps in signs:
        for lam in G.E:
            rel = set()
            for s in range(q):
                target = matvec(G.N[s], lam, p)
                for e1 in G.E:
                    for e2 in G.E:
                        # solve eps3*e3 = target - eps1 e1 - eps2 e2
                        rest = tuple((t - eps[0] * a - eps[1] * b) % p
                                     for t, a, b in zip(target, e1, e2))
                        e3 = tuple((eps[2] * r) % p for r in rest)  # eps3 = +-1
                        rel.add(((e1, s), (e2, s), (e3, s)))
            ident_el = ((G.zero, 0),) * 3
            assert ident_el in rel
            rl = list(rel)
            for x in rl:
                for y in rl:
                    prod = tuple(G.mul(a, b) for a, b in zip(x, y))
                    assert prod in rel, (G.name, eps, lam)
    # Z_q relations: preimage of {(t1,t2,t3,sigma): eps.t = (1-sigma) lam} - affine in Z_q^4
    for eps in signs:
        for lam in range(q):
            pts = [(t, s) for t in itertools.product(range(q), repeat=3) for s in range(q)
                   if sum(e_ * x for e_, x in zip(eps, t)) % q == ((1 - s) * lam) % q]
            vecs = [t + (s,) for t, s in pts]
            v0 = vecs[0]
            diffs = {tuple((a - b) % q for a, b in zip(v, v0)) for v in vecs}
            for d1 in diffs:
                for d2 in diffs:
                    assert tuple((a + b) % q for a, b in zip(d1, d2)) in diffs
    # (2) the homomorphism e : A -> T, on features
    def eZ(t):
        return ("Zq", t)

    def feat_T(x):
        # features of the image element: (marker, selector, value)
        if x[0] == "Zq":
            return (0, 0, x[1])
        if x[0] == "c1":
            return (0, 1, 0)
        if x[0] == "E":
            return (1, 1, x[1])
        return (1, 0, G.zero)  # c2

    def T_Zq(fs, eps, lam):
        if any(f[0] != 0 for f in fs) or len({f[1] for f in fs}) != 1:
            return False
        sig = fs[0][1]
        return sum(e_ * f[2] for e_, f in zip(eps, fs)) % q == ((1 - sig) * lam) % q

    def T_E(fs, eps, lam):
        if any(f[0] != 1 for f in fs) or len({f[1] for f in fs}) != 1:
            return False
        s = fs[0][1]
        return eps_combo(G, eps, [f[2] for f in fs]) == matvec(G.N[s], lam, p)

    def T_S(f, g):
        return f[0] == 0 and g[0] == 1 and f[1] == g[1]

    for eps in signs:
        for lam in range(q):
            rel = [tuple(("Zq", x) for x in t) for t in itertools.product(range(q), repeat=3)
                   if sum(e_ * x for e_, x in zip(eps, t)) % q == lam]
            rel.append((("c1",),) * 3)
            for tup in rel:
                assert T_Zq([feat_T(x) for x in tup], eps, lam)
        for lam in G.E:
            rel = [tuple(("E", x) for x in t) for t in itertools.product(G.E, repeat=3)
                   if eps_combo(G, eps, t) == lam]
            rel.append((("c2",),) * 3)
            for tup in rel:
                assert T_E([feat_T(x) for x in tup], eps, lam)
    S_A = [(("Zq", t), ("c2",)) for t in range(q)] + [(("c1",), ("E", e)) for e in G.E]
    for a, b in S_A:
        assert T_S(feat_T(a), feat_T(b))
    print(f"{G.name}: p={p} q={q} |E|={len(G.E)} -- all checks passed", flush=True)


if __name__ == "__main__":
    check(H("S3 = Z3:Z2", 3, 2, ((2,),)))
    check(H("D10 = Z5:Z2", 5, 2, ((4,),)))
    check(H("Z7:Z3", 7, 3, ((2,),)))
    check(H("A4 = F2^2:Z3", 2, 3, ((0, 1), (1, 1))))
    check(H("Z11:Z5", 11, 5, ((3,),)))
    check(H("F2^3:Z7", 2, 7, ((0, 0, 1), (1, 0, 1), (0, 1, 0))))
