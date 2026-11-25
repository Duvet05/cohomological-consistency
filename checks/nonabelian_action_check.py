"""Does the locality behind Theorem A survive a non-abelian coprime action?

G = M x| S3 where M = {x in F_p^3 : x1+x2+x3 = 0} (p >= 5) and S3 permutes coordinates:
the 2-dimensional irreducible representation, so the action is coprime but not abelian.
For random binary coset instances we compute
    P = Q-solutions of the projected instance   (Q = S3),
    F = { tau in P : the M-system at tau is solvable }   (linear algebra over F_p),
and test whether F is cut out of P by unary conditions:
    F == { tau in P : tau_v in pr_v(F) for all v }.                         (*)
(*) holds for groups in the class of Theorem A. A failure here would show that the
abelian-action hypothesis is needed for locality.

Run: python3 -I nonabelian_action_check.py [trials] [p]
"""

import itertools
import random
import sys

P_MOD = int(sys.argv[2]) if len(sys.argv) > 2 else 5
S3 = list(itertools.permutations(range(3)))  # perm as tuple: i -> perm[i]


def pmul(a, b):  # (a*b)(i) = a(b(i))
    return tuple(a[b[i]] for i in range(3))


def pinv(a):
    r = [0] * 3
    for i in range(3):
        r[a[i]] = i
    return tuple(r)


ID = (0, 1, 2)
# M as pairs (x0, x1) with x2 = -x0-x1; full vector helpers
def full(m):
    return (m[0], m[1], (-m[0] - m[1]) % P_MOD)


def red(v):
    return (v[0] % P_MOD, v[1] % P_MOD)


def act(q, m):
    """q permutes coordinates: (q.x)_{q(i)} = x_i."""
    x = full(m)
    y = [0, 0, 0]
    for i in range(3):
        y[q[i]] = x[i]
    return red(y)


MEL = [(a, b) for a in range(P_MOD) for b in range(P_MOD)]


def madd(a, b):
    return ((a[0] + b[0]) % P_MOD, (a[1] + b[1]) % P_MOD)


def gmul(x, y):
    (n, q), (n2, q2) = x, y
    return (madd(n, act(q, n2)), pmul(q, q2))


GEL = [(m, q) for q in S3 for m in MEL]
IDG = ((0, 0), ID)


def closure(gens, r):
    ident = tuple([IDG] * r)
    sub = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = tuple(gmul(a, b) for a, b in zip(x, g))
                if y not in sub:
                    sub.add(y)
                    new.append(y)
        frontier = new
    return sub


def random_coset(rng, r):
    gens = [tuple(rng.choice(GEL) for _ in range(r)) for _ in range(rng.choice([1, 2, 2, 3]))]
    H = closure(gens, r)
    delta = tuple(rng.choice(GEL) for _ in range(r))
    R = frozenset(tuple(gmul(a, b) for a, b in zip(h, delta)) for h in H)
    # fibres: tau -> set of N-tuples
    fib = {}
    for x in R:
        tau = tuple(q for (_, q) in x)
        fib.setdefault(tau, set()).add(tuple(n for (n, _) in x))
    return fib


def solve_mod_p(rows, ncols):
    """rows: list of (coeffs list len ncols, rhs). Return True iff consistent over F_p."""
    rows = [list(c) + [b] for c, b in rows]
    rank_row = 0
    for col in range(ncols):
        piv = None
        for i in range(rank_row, len(rows)):
            if rows[i][col] % P_MOD:
                piv = i
                break
        if piv is None:
            continue
        rows[rank_row], rows[piv] = rows[piv], rows[rank_row]
        inv = pow(rows[rank_row][col], P_MOD - 2, P_MOD)
        rows[rank_row] = [(v * inv) % P_MOD for v in rows[rank_row]]
        for i in range(len(rows)):
            if i != rank_row and rows[i][col] % P_MOD:
                f = rows[i][col]
                rows[i] = [(a - f * b) % P_MOD for a, b in zip(rows[i], rows[rank_row])]
        rank_row += 1
    for row in rows[rank_row:]:
        if all(v % P_MOD == 0 for v in row[:-1]) and row[-1] % P_MOD:
            return False
    return True


def coset_equations(fibset, scope, nvars):
    """Linear equations (over F_p, unknowns = 2 coords per variable) describing that the
    N-tuple on `scope` lies in the coset `fibset` (a coset of a subgroup of M^r)."""
    pts = list(fibset)
    base = pts[0]
    r = len(scope)
    # subgroup U = differences; get its F_p-span (subgroups of p-groups M^r are F_p-spaces)
    vecs = []
    for pt in pts:
        v = []
        for (a, b), (c, d) in zip(pt, base):
            v += [(a - c) % P_MOD, (b - d) % P_MOD]
        vecs.append(v)
    dim = 2 * r
    # compute orthogonal complement: equations e with e.u = 0 for all u in U
    # brute-force basis of U then solve nullspace
    basis = []
    for v in vecs:
        w = v[:]
        for bv, pc in basis:
            if w[pc]:
                f = w[pc]
                w = [(x - f * y) % P_MOD for x, y in zip(w, bv)]
        pc = next((i for i in range(dim) if w[i]), None)
        if pc is not None:
            inv = pow(w[pc], P_MOD - 2, P_MOD)
            w = [(x * inv) % P_MOD for x in w]
            basis = [([(x - bv[pc] * y) % P_MOD for x, y in zip(bv, w)], bpc) for bv, bpc in basis]
            basis.append((w, pc))
    pivots = {pc for _, pc in basis}
    free = [i for i in range(dim) if i not in pivots]
    eqs = []
    for fcol in free:
        e = [0] * dim
        e[fcol] = 1
        for bv, pc in basis:
            e[pc] = (-bv[fcol]) % P_MOD
        eqs.append(e)
    basevec = []
    for (a, b) in base:
        basevec += [a, b]
    rows = []
    for e in eqs:
        coeffs = [0] * (2 * nvars)
        for j, v in enumerate(scope):
            coeffs[2 * v] = (coeffs[2 * v] + e[2 * j]) % P_MOD
            coeffs[2 * v + 1] = (coeffs[2 * v + 1] + e[2 * j + 1]) % P_MOD
        rhs = sum(x * y for x, y in zip(e, basevec)) % P_MOD
        rows.append((coeffs, rhs))
    return rows


def run(trials, nvars, ncons, seed):
    rng = random.Random(seed)
    st = {"interesting": 0, "unary_ok": 0, "unary_fail": 0}
    examples = []
    for _ in range(trials):
        cons = []
        for _ in range(ncons):
            scope = tuple(rng.sample(range(nvars), 2))
            cons.append((scope, random_coset(rng, 2)))
        Pset = [t for t in itertools.product(S3, repeat=nvars)
                if all(tuple(t[v] for v in sc) in fib for sc, fib in cons)]
        if not Pset:
            continue
        F = set()
        for t in Pset:
            rows = []
            for sc, fib in cons:
                rows += coset_equations(fib[tuple(t[v] for v in sc)], sc, nvars)
            if solve_mod_p(rows, 2 * nvars):
                F.add(t)
        if F == set(Pset) or not F:
            continue
        st["interesting"] += 1
        prv = [{t[v] for t in F} for v in range(nvars)]
        F2 = {t for t in Pset if all(t[v] in prv[v] for v in range(nvars))}
        if F2 == F:
            st["unary_ok"] += 1
        else:
            st["unary_fail"] += 1
            if len(examples) < 3:
                examples.append((cons, len(Pset), len(F), len(F2)))
    return st, examples


if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    for nvars, ncons in [(3, 3), (4, 4), (4, 6), (5, 6)]:
        st, ex = run(trials, nvars, ncons, seed=11)
        print(f"p={P_MOD} n={nvars} m={ncons}: {st}", flush=True)
        for cons, a, b, c in ex[:1]:
            print("   example: |P|=%d |F|=%d |unary closure|=%d" % (a, b, c))
