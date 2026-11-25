"""Empirical check of the locality behind Theorem A.

For a coset-CSP instance B over G = N x| Q (N abelian normal, Q = G/N), let
  P = solutions of the projected Q-instance,
  F = projections to Q of the solutions of B   (F is a subset of P).
Theorem A's proof shows: if gcd(|N|, |Q|) = 1 and Q acts on N through an abelian group,
then F is cut out of P by unary conditions, i.e.
      F = { tau in P : tau_v in pr_v(F) for every variable v }.          (*)
This is the property that pinning a single local solution can detect.

We test (*) on random instances over coprime groups (S3, D5, Z7:Z3, Z5:Z4, A4) and over the
non-coprime groups D4 and Z9:Z3. Small random instances satisfy (*) in all cases, so (*) is
only a sanity check here, not a separating test.
We also check Lemma A1 on random cosets: over tau in pr(R), the N-fibre of R is
U + (T_1(tau_1), ..., T_r(tau_r)) for some functions T_i (coordinatewise translations).
This holds for every sampled coset over the coprime groups and fails for many cosets over
D4 and Z9:Z3, which shows that the coprimality hypothesis is doing real work.

Run: python3 -I locality_check.py
"""

import itertools
import random
import sys


class SemiDirect:
    """G = N x| Q with N = Z_m^d (additive, vectors), Q given by a list of elements, a
    multiplication table, and an action Q -> Aut(N) as matrices over Z_m."""

    def __init__(self, name, m, d, qelems, qmul, qact):
        self.name, self.m, self.d = name, m, d
        self.Q = qelems
        self.qmul = qmul          # dict (q, q') -> q q'
        self.qact = qact          # dict q -> d x d matrix (tuple of tuples)
        self.N = list(itertools.product(range(m), repeat=d))
        self.G = [(n, q) for q in qelems for n in self.N]
        self.qid = next(q for q in qelems if all(qmul[(q, x)] == x for x in qelems))
        self.nzero = tuple([0] * d)

    def act(self, q, n):
        A = self.qact[q]
        return tuple(sum(A[i][j] * n[j] for j in range(self.d)) % self.m for i in range(self.d))

    def nadd(self, a, b):
        return tuple((x + y) % self.m for x, y in zip(a, b))

    def mul(self, x, y):
        (n, q), (n2, q2) = x, y
        return (self.nadd(n, self.act(q, n2)), self.qmul[(q, q2)])

    def inv(self, x):
        for y in self.G:
            if self.mul(x, y) == (self.nzero, self.qid):
                return y
        raise ValueError


def cyclic(n):
    els = list(range(n))
    return els, {(a, b): (a + b) % n for a in els for b in els}


def mat_pow_scalar(lam, e, m):
    return ((pow(lam, e, m),),)


def make_Zp_semidirect_Zn(p, n, lam, name):
    """N = Z_p, Q = Z_n acting by multiplication by lam (lam^n = 1 mod p)."""
    assert pow(lam, n, p) == 1
    qe, qm = cyclic(n)
    act = {q: mat_pow_scalar(lam, q, p) for q in qe}
    return SemiDirect(name, p, 1, qe, qm, act)


def make_A4():
    # A4 = V4 x| Z3, Z3 acting on F2^2 by the matrix of order 3 [[0,1],[1,1]]
    qe, qm = cyclic(3)
    M = ((0, 1), (1, 1))
    I = ((1, 0), (0, 1))

    def mm(A, B):
        return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) % 2 for j in range(2)) for i in range(2))
    act = {0: I, 1: M, 2: mm(M, M)}
    return SemiDirect("A4", 2, 2, qe, qm, act)


def make_D4():
    # D4 = Z4 x| Z2 with inversion: not coprime (control)
    qe, qm = cyclic(2)
    act = {0: ((1,),), 1: ((3,),)}
    return SemiDirect("D4", 4, 1, qe, qm, act)


def make_Z9_Z3():
    # Z9 x| Z3 with 1 acting as multiplication by 4 (order 3 mod 9): a non-abelian group of
    # order 27, 2-nilpotent; not coprime (control)
    qe, qm = cyclic(3)
    act = {q: ((pow(4, q, 9),),) for q in qe}
    return SemiDirect("Z9:Z3", 9, 1, qe, qm, act)


def closure(Gr, gens, mul, ident):
    sub = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in sub:
                    sub.add(y)
                    new.append(y)
        frontier = new
    return sub


def random_coset(G, r, rng, ngens):
    ident = tuple([(G.nzero, G.qid)] * r)

    def mulr(x, y):
        return tuple(G.mul(a, b) for a, b in zip(x, y))
    gens = [tuple(rng.choice(G.G) for _ in range(r)) for _ in range(ngens)]
    H = closure(None, gens, mulr, ident)
    delta = tuple(rng.choice(G.G) for _ in range(r))
    return frozenset(mulr(h, delta) for h in H)


def check_lemma_A1(G, R, r):
    """Fibres of R over tau are U + (T_i(tau_i))_i for some T_i : Q -> N."""
    fib = {}
    for x in R:
        tau = tuple(q for (_, q) in x)
        fib.setdefault(tau, set()).add(tuple(n for (n, _) in x))
    taus = list(fib)
    # U = fibre difference set (same for all tau)
    t0 = taus[0]
    base = next(iter(fib[t0]))
    U = {tuple(G.nadd(a, tuple((-c) % G.m for c in b)) for a, b in zip(v, base)) for v in fib[t0]}
    # search T_i by backtracking over the values tau_i that occur
    values = [sorted({t[i] for t in taus}) for i in range(r)]
    keys = [(i, q) for i in range(r) for q in values[i]]
    Nlist = G.N

    def consistent(assign):
        for t in taus:
            if all((i, t[i]) in assign for i in range(r)):
                T = tuple(assign[(i, t[i])] for i in range(r))
                # fibre(t) == U + T ?
                shifted = {tuple(G.nadd(u_i, T_i) for u_i, T_i in zip(u, T)) for u in U}
                if shifted != fib[t]:
                    return False
        return True

    def bt(idx, assign):
        if idx == len(keys):
            return True
        for n in Nlist:
            assign[keys[idx]] = n
            if consistent(assign) and bt(idx + 1, assign):
                return True
            del assign[keys[idx]]
        return False
    return bt(0, {})


def random_instance(G, nvars, ncons, r, rng):
    cons = []
    for _ in range(ncons):
        scope = tuple(rng.randrange(nvars) for _ in range(r))
        R = random_coset(G, r, rng, rng.choice([1, 1, 2, 2, 3]))
        cons.append((scope, R))
    return cons


def solve_all(G, nvars, cons):
    sols = []
    for a in itertools.product(G.G, repeat=nvars):
        if all(tuple(a[v] for v in scope) in R for scope, R in cons):
            sols.append(a)
    return sols


def q_solutions(G, nvars, cons):
    projs = [(scope, {tuple(q for (_, q) in x) for x in R}) for scope, R in cons]
    out = []
    for t in itertools.product(G.Q, repeat=nvars):
        if all(tuple(t[v] for v in scope) in PR for scope, PR in projs):
            out.append(t)
    return out


def run(G, trials, nvars, ncons, r, seed):
    rng = random.Random(seed)
    stats = {"interesting": 0, "unary_ok": 0, "unary_fail": 0, "a1_ok": 0, "a1_fail": 0}
    for _ in range(trials):
        cons = random_instance(G, nvars, ncons, r, rng)
        for _, R in cons[:1]:
            if check_lemma_A1(G, R, r):
                stats["a1_ok"] += 1
            else:
                stats["a1_fail"] += 1
        P = q_solutions(G, nvars, cons)
        if not P:
            continue
        sols = solve_all(G, nvars, cons)
        F = {tuple(q for (_, q) in s) for s in sols}
        if F == set(P):
            continue
        stats["interesting"] += 1
        prv = [{t[v] for t in F} for v in range(nvars)]
        F2 = {t for t in P if all(t[v] in prv[v] for v in range(nvars))}
        if F2 == F:
            stats["unary_ok"] += 1
        else:
            stats["unary_fail"] += 1
    return stats


if __name__ == "__main__":
    groups = [
        (make_Zp_semidirect_Zn(3, 2, 2, "S3"), 5, 2),
        (make_Zp_semidirect_Zn(5, 2, 4, "D5"), 4, 2),
        (make_Zp_semidirect_Zn(7, 3, 2, "Z7:Z3"), 3, 2),
        (make_Zp_semidirect_Zn(5, 4, 2, "Z5:Z4"), 3, 2),
        (make_A4(), 4, 2),
        (make_D4(), 5, 2),
        (make_Z9_Z3(), 3, 2),
        (make_Zp_semidirect_Zn(3, 2, 2, "S3"), 5, 3),
        (make_Zp_semidirect_Zn(5, 2, 4, "D5"), 4, 3),
        (make_A4(), 4, 3),
        (make_D4(), 5, 3),
    ]
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    for G, nvars, r in groups:
        st = run(G, trials, nvars, nvars + 2, r, seed=7)
        print(f"{G.name:7s} |G|={len(G.G):3d} n={nvars} r={r}: {st}", flush=True)
