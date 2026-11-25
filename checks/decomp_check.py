"""Test of Lemmas shape, split(b), decomp, dichotomy (Section 4 of paper.tex).

Written during an independent check of the draft.

G = N x| Q with N = (Z/m)^d, Q a finite group (mult table), rho: Q -> GL_d(Z/m).
For random instances we build exactly the objects of the paper:
  shape data (Sigma, U, q0, m, d) for each constraint,
  Galois ring Lambda = GR(p^a, f), Teichmueller group mu, characters chi, M_chi,
  points/blocks/components, coherent assignments, component systems L_K(gamma), A_K,
and check
  (S)  R_tau = U + m + (tau q0^{-1}).d               for every tau in pi(R)
  (P)  U^Lambda = sum of its psi-projections          (split (b))
  (C0) c(tau)|_K is coherent for tau in Sol(pi B)
  (D)  B_tau solvable  <=>  c(tau)|_K in A_K for all p, K       (decomp)
  (Y)  |A_K| in {0, 1, |Coh_K|}                                  (dichotomy)
"""
import itertools, random, sys
from math import gcd

# `--mutant` replaces chi(q0)^{-1} by chi(q0) in the component translations; the decomposition
# test must then report failures, which shows that the check can detect a wrong formula.
MUTANT = "--mutant" in sys.argv
if MUTANT:
    sys.argv.remove("--mutant")

# ---------------------------------------------------------------- groups
def cyclic(n):
    return list(range(n)), [[(a + b) % n for b in range(n)] for a in range(n)]

def sym3():
    els = list(itertools.permutations(range(3)))
    idx = {e: i for i, e in enumerate(els)}
    tab = [[idx[tuple(a[b[i]] for i in range(3))] for b in els] for a in els]
    sign = []
    for p in els:
        inv = sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j])
        sign.append(inv % 2)
    return list(range(6)), tab, sign

def matmul(A, B, m):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n)) % m for j in range(n)) for i in range(n))

def matpow(A, e, m):
    n = len(A)
    R = tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))
    for _ in range(e):
        R = matmul(R, A, m)
    return R

class Grp:
    def __init__(self, name, m, d, Q, qtab, rho):
        self.name, self.m, self.d = name, m, d
        self.Q, self.qtab, self.rho = Q, qtab, rho
        self.qid = next(q for q in Q if all(qtab[q][x] == x for x in Q))
        self.qinv = {q: next(x for x in Q if qtab[q][x] == self.qid) for q in Q}
        self.N = list(itertools.product(range(m), repeat=d))
        self.G = [(n, q) for q in Q for n in self.N]
        self.zero = tuple([0] * d)
        # check rho is a hom
        for a in Q:
            for b in Q:
                assert matmul(rho[a], rho[b], m) == rho[qtab[a][b]]
        assert gcd(m, len(Q)) == 1

    def act(self, q, n):
        A = self.rho[q]
        return tuple(sum(A[i][j] * n[j] for j in range(self.d)) % self.m for i in range(self.d))

    def nadd(self, a, b):
        return tuple((x + y) % self.m for x, y in zip(a, b))

    def nneg(self, a):
        return tuple((-x) % self.m for x in a)

    def mul(self, x, y):
        (n, q), (n2, q2) = x, y
        return (self.nadd(n, self.act(q, n2)), self.qtab[q][q2])

    def inv(self, x):
        n, q = x
        qi = self.qinv[q]
        return (self.nneg(self.act(qi, n)), qi)

def mk_cyc_action(name, p, n, lam):
    Q, tab = cyclic(n)
    rho = {q: ((pow(lam, q, p),),) for q in Q}
    return Grp(name, p, 1, Q, tab, rho)

def mk_matrix_action(name, m, n, M):
    Q, tab = cyclic(n)
    rho = {q: matpow(M, q, m) for q in Q}
    return Grp(name, m, len(M), Q, tab, rho)

def mk_Z7_S3():
    Q, tab, sign = sym3()
    rho = {q: (((-1) ** sign[q]) % 7,) for q in Q}
    rho = {q: ((rho[q][0],),) for q in Q}
    return Grp("Z7:S3(sign)", 7, 1, Q, tab, rho)

# ---------------------------------------------------------------- Galois ring
def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def mult_order(p, e):
    if e == 1:
        return 1
    k, x = 1, p % e
    while x != 1:
        x = x * p % e
        k += 1
    return k

def irreducible_poly(p, f):
    """monic degree-f polynomial over F_p with no root / irreducible (f <= 3), coeffs low->high"""
    for coeffs in itertools.product(range(p), repeat=f):
        g = list(coeffs) + [1]
        if f == 1:
            return g
        # f in {2,3}: irreducible iff no root
        if all(sum(c * pow(x, i, p) for i, c in enumerate(g)) % p != 0 for x in range(p)):
            return g
    raise ValueError

class GR:
    def __init__(self, p, a, f):
        self.p, self.a, self.f, self.q = p, a, f, p ** a
        self.g = irreducible_poly(p, f)  # lift: same integer coefficients
        self.one = tuple([1] + [0] * (f - 1))
        self.zero = tuple([0] * f)
        self.elems = list(itertools.product(range(self.q), repeat=f))
        self.mu = [x for x in self.elems if self.pow(x, p ** f - 1) == self.one]
        assert len(self.mu) == p ** f - 1, (p, a, f, len(self.mu))

    def add(self, x, y):
        return tuple((u + v) % self.q for u, v in zip(x, y))

    def sub(self, x, y):
        return tuple((u - v) % self.q for u, v in zip(x, y))

    def mul(self, x, y):
        f, q = self.f, self.q
        prod = [0] * (2 * f - 1)
        for i, u in enumerate(x):
            if u:
                for j, v in enumerate(y):
                    prod[i + j] += u * v
        for k in range(2 * f - 2, f - 1, -1):
            c = prod[k]
            if c:
                prod[k] = 0
                for i in range(f):
                    prod[k - f + i] -= c * self.g[i]
        return tuple(c % q for c in prod[:f])

    def smul(self, c, x):
        return tuple((c * u) % self.q for u in x)

    def const(self, c):
        return tuple([c % self.q] + [0] * (self.f - 1))

    def pow(self, x, e):
        r = self.one
        for _ in range(e):
            r = self.mul(r, x)
        return r

    def inv(self, x):
        for y in self.elems:
            if self.mul(x, y) == self.one:
                return y
        raise ZeroDivisionError

# ---------------------------------------------------------------- prime data
class PrimeData:
    def __init__(self, G, p):
        self.G, self.p = G, p
        a = factor(G.m)[p]
        self.a, self.pa = a, p ** a
        # exponent e of A_N (image of Q in GL_d(Z/m))
        e = 1
        I = matpow(G.rho[G.qid], 0, G.m)
        for q in G.Q:
            k, A = 1, G.rho[q]
            while A != I:
                A = matmul(A, G.rho[q], G.m)
                k += 1
            e = e * k // gcd(e, k)
        self.e = e
        self.f = mult_order(p, e)
        L = self.L = GR(p, a, self.f)
        self.chars = self._characters()
        Qinv_mod = pow(len(G.Q), -1, self.pa)
        self.Qinv_mod = Qinv_mod
        # M = Lambda^d ; e_chi
        self.Mchi = {}
        for ci, chi in enumerate(self.chars):
            basis_imgs = [self.echi(ci, self.unit_vec(i)) for i in range(G.d)]
            span = set()
            for lams in itertools.product(L.elems, repeat=G.d):
                v = self.mzero()
                for lam, b in zip(lams, basis_imgs):
                    v = self.madd(v, self.mscal(lam, b))
                span.add(v)
            if len(span) > 1:
                self.Mchi[ci] = sorted(span)
        # sanity: sum of e_chi = id
        for i in range(G.d):
            tot = self.mzero()
            for ci in range(len(self.chars)):
                tot = self.madd(tot, self.echi(ci, self.unit_vec(i)))
            assert tot == self.unit_vec(i)

    # M elements: tuple of d Lambda elements
    def mzero(self):
        return tuple([self.L.zero] * self.G.d)

    def unit_vec(self, i):
        return tuple(self.L.one if j == i else self.L.zero for j in range(self.G.d))

    def madd(self, x, y):
        return tuple(self.L.add(u, v) for u, v in zip(x, y))

    def msub(self, x, y):
        return tuple(self.L.sub(u, v) for u, v in zip(x, y))

    def mscal(self, lam, x):
        return tuple(self.L.mul(lam, u) for u in x)

    def mact(self, q, x):
        A = self.G.rho[q]
        d = self.G.d
        out = []
        for i in range(d):
            s = self.L.zero
            for j in range(d):
                s = self.L.add(s, self.L.smul(A[i][j] % self.pa, x[j]))
            out.append(s)
        return tuple(out)

    def from_N(self, n):
        return tuple(self.L.const(c % self.pa) for c in n)

    def _characters(self):
        G, L = self.G, self.L
        # kernel of Q -> A_N
        I = matpow(G.rho[G.qid], 0, G.m)
        ker = [q for q in G.Q if G.rho[q] == I]
        chars = []
        for vals in itertools.product(range(len(L.mu)), repeat=len(G.Q)):
            pass  # too slow in general; replaced below
            break
        # brute force via generators
        gens = []
        span = {G.qid}
        for q in G.Q:
            if q not in span:
                gens.append(q)
                # closure
                span = {G.qid}
                frontier = [G.qid]
                while frontier:
                    new = []
                    for x in frontier:
                        for g in gens:
                            y = G.qtab[x][g]
                            if y not in span:
                                span.add(y)
                                new.append(y)
                    frontier = new
        for vals in itertools.product(L.mu, repeat=len(gens)):
            chi = {G.qid: L.one}
            frontier = [G.qid]
            ok = True
            while frontier and ok:
                new = []
                for x in frontier:
                    for g, v in zip(gens, vals):
                        y = G.qtab[x][g]
                        val = L.mul(chi[x], v)
                        if y in chi:
                            if chi[y] != val:
                                ok = False
                                break
                        else:
                            chi[y] = val
                            new.append(y)
                    if not ok:
                        break
                frontier = new
            if not ok:
                continue
            # hom check
            if any(chi[G.qtab[x][y]] != L.mul(chi[x], chi[y]) for x in G.Q for y in G.Q):
                continue
            if any(chi[k] != L.one for k in ker):
                continue
            chars.append(chi)
        return chars

    def echi(self, ci, x):
        chi = self.chars[ci]
        L = self.L
        tot = self.mzero()
        for q in self.G.Q:
            tot = self.madd(tot, self.mscal(L.inv(chi[q]), self.mact(q, x)))
        c = L.const(self.Qinv_mod)
        return self.mscal(c, tot)

# ---------------------------------------------------------------- cosets and shape
def random_coset(G, r, rng, ngens):
    ident = tuple([(G.zero, G.qid)] * r)
    mulr = lambda x, y: tuple(G.mul(a, b) for a, b in zip(x, y))
    gens = [tuple(rng.choice(G.G) for _ in range(r)) for _ in range(ngens)]
    H = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mulr(x, g)
                if y not in H:
                    H.add(y)
                    new.append(y)
        frontier = new
    delta = tuple(rng.choice(G.G) for _ in range(r))
    return frozenset(mulr(h, delta) for h in H)

def shape_data(G, R, r):
    mulr = lambda x, y: tuple(G.mul(a, b) for a, b in zip(x, y))
    delta = min(R)
    dinv = tuple(G.inv(x) for x in delta)
    Delta = {mulr(x, dinv) for x in R}
    qid = tuple([G.qid] * r)
    U = frozenset(tuple(n for n, _ in x) for x in Delta if tuple(q for _, q in x) == qid)
    a = {}
    for x in Delta:
        s = tuple(q for _, q in x)
        a.setdefault(s, tuple(n for n, _ in x))
    Sigma = sorted(a)
    inv_s = pow(len(Sigma), -1, G.m)
    tot = [G.zero] * r
    for s in Sigma:
        tot = [G.nadd(t, v) for t, v in zip(tot, a[s])]
    mprime = [tuple((-inv_s * c) % G.m for c in t) for t in tot]
    dprime = [n for n, _ in delta]
    q0 = tuple(q for _, q in delta)
    m_ = [G.nneg(x) for x in mprime]
    d_ = [G.nadd(x, y) for x, y in zip(mprime, dprime)]
    return dict(Sigma=Sigma, U=U, q0=q0, m=m_, d=d_)

def check_shape(G, R, r, sd):
    fib = {}
    for x in R:
        fib.setdefault(tuple(q for _, q in x), set()).add(tuple(n for n, _ in x))
    q0 = sd["q0"]
    piR = {tuple(G.qtab[s[i]][q0[i]] for i in range(r)) for s in sd["Sigma"]}
    if piR != set(fib):
        return False
    for tau, F in fib.items():
        sig = [G.qtab[tau[i]][G.qinv[q0[i]]] for i in range(r)]
        t = [G.nadd(sd["m"][i], G.act(sig[i], sd["d"][i])) for i in range(r)]
        pred = {tuple(G.nadd(u[i], t[i]) for i in range(r)) for u in sd["U"]}
        if pred != F:
            return False
    return True

# ---------------------------------------------------------------- per-prime structure for instance
def in_ULambda(pd, Up, y):
    """y in M^r (tuple of r M-elements); U^Lambda membership via Lambda-basis coefficients"""
    f = pd.L.f
    for j in range(f):
        vec = tuple(y[i][k][j] for i in range(len(y)) for k in range(pd.G.d))
        if vec not in Up:
            return False
    return True

def analyse(G, cons, nvars, pds, stats):
    r_of = lambda C: len(C[0])
    datas = [shape_data(G, R, len(sc)) for sc, R in cons]
    for (sc, R), sd in zip(cons, datas):
        ok = check_shape(G, R, len(sc), sd)
        stats["shape_ok" if ok else "shape_FAIL"] += 1
    # Q-solutions
    piR = [{tuple(q for _, q in x) for x in R} for _, R in cons]
    P = [t for t in itertools.product(G.Q, repeat=nvars)
         if all(tuple(t[v] for v in sc) in pr for (sc, _), pr in zip(cons, piR))]
    if not P:
        return
    # per prime: points, blocks, components, Coh_K, A_K
    comp_info = []  # list of (pd, K-points, gamma0 or None, A_K set of lambdas)
    for pd in pds:
        L = pd.L
        pts = [(v, ci) for v in range(nvars) for ci in pd.Mchi]
        blocks = []
        Ups = []
        for cidx, ((sc, R), sd) in enumerate(zip(cons, datas)):
            r = len(sc)
            Up = {tuple(c % pd.pa for c in itertools.chain.from_iterable(u)) for u in sd["U"]}
            Ups.append(Up)
            # partition (i,chi) by sigma -> chi(sigma_i)
            groups = {}
            for i in range(r):
                for ci in pd.Mchi:
                    key = tuple(pd.chars[ci][s[i]] for s in sd["Sigma"])
                    groups.setdefault(key, []).append((i, ci))
            # (P): U^Lambda = sum of psi-projections: check on U_p generators (all elements)
            for u in sd["U"]:
                y = tuple(pd.from_N(u[i]) for i in range(r))
                for key, J in groups.items():
                    proj = []
                    for i in range(r):
                        comp = pd.mzero()
                        for (ii, ci) in J:
                            if ii == i:
                                comp = pd.madd(comp, pd.echi(ci, y[i]))
                        proj.append(comp)
                    if not in_ULambda(pd, Up, tuple(proj)):
                        stats["split_FAIL"] += 1
                    else:
                        stats["split_ok"] += 1
            for key, J in groups.items():
                blocks.append((cidx, J))
        # adjacency / components
        parent = {w: w for w in pts}
        def find(w):
            while parent[w] != w:
                parent[w] = parent[parent[w]]
                w = parent[w]
            return w
        for (cidx, J) in blocks:
            sc = cons[cidx][0]
            ws = [(sc[i], ci) for i, ci in J]
            for w in ws[1:]:
                parent[find(w)] = find(ws[0])
        comps = {}
        for w in pts:
            comps.setdefault(find(w), []).append(w)
        blocks_of = {}
        for b in blocks:
            sc = cons[b[0]][0]
            root = find((sc[b[1][0][0]], b[1][0][1]))
            blocks_of.setdefault(root, []).append(b)
        for root, K in comps.items():
            Kb = blocks_of.get(root, [])
            # coherent gamma0 by BFS
            gamma = {K[0]: L.one}
            changed, coherent = True, True
            while changed and coherent:
                changed = False
                for (cidx, J) in Kb:
                    sc, sd = cons[cidx][0], datas[cidx]
                    q0 = sd["q0"]
                    known = [(i, ci) for i, ci in J if (sc[i], ci) in gamma]
                    if not known:
                        continue
                    i, ci = known[0]
                    b = L.mul(gamma[(sc[i], ci)], L.inv(pd.chars[ci][q0[i]]))
                    for j, cj in J:
                        val = L.mul(b, pd.chars[cj][q0[j]])
                        w = (sc[j], cj)
                        if w in gamma:
                            if gamma[w] != val:
                                coherent = False
                        else:
                            gamma[w] = val
                            changed = True
            if not coherent:
                comp_info.append((pd, K, Kb, None, None))
                stats["CohK_empty"] += 1
                continue
            assert len(gamma) == len(K)
            # A_K by brute force over lambda in mu
            AK = []
            for lam in L.mu:
                g = {w: L.mul(lam, gamma[w]) for w in K}
                if solve_component(pd, cons, datas, Ups, K, Kb, g):
                    AK.append(lam)
            sz = len(AK)
            if sz in (0, 1, len(L.mu)):
                stats["dich_ok"] += 1
            else:
                stats["dich_FAIL"] += 1
            if 0 < sz < len(L.mu):
                stats["singleton_components"] += 1
            comp_info.append((pd, K, Kb, gamma, set(AK)))
    # compare with B_tau solvability
    for tau in P:
        sol = solvable_Btau(G, cons, nvars, tau)
        pred = True
        for pd, K, Kb, gamma, AK in comp_info:
            L = pd.L
            c = {w: pd.chars[w[1]][tau[w[0]]] for w in K}
            if gamma is None:
                stats["C0_FAIL"] += 1
                pred = False
                continue
            # is c a multiple of gamma?
            w0 = K[0]
            lam = L.mul(c[w0], L.inv(gamma[w0]))
            if any(c[w] != L.mul(lam, gamma[w]) for w in K):
                stats["C0_FAIL"] += 1
            else:
                stats["C0_ok"] += 1
            if lam not in AK:
                pred = False
        if pred == sol:
            stats["decomp_ok"] += 1
        else:
            stats["decomp_FAIL"] += 1
            print("DECOMP FAIL", G.name, cons, tau, sol, pred)
        stats["tau_solvable" if sol else "tau_unsolvable"] += 1

def solve_component(pd, cons, datas, Ups, K, Kb, gamma):
    L = pd.L
    order = K
    domain = {w: pd.Mchi[w[1]] for w in K}
    # translation per block
    btrans = []
    for (cidx, J) in Kb:
        sc, sd = cons[cidx][0], datas[cidx]
        tr = {}
        for (i, ci) in J:
            em = pd.echi(ci, pd.from_N(sd["m"][i]))
            ed = pd.echi(ci, pd.from_N(sd["d"][i]))
            # MUTANT (negative control): use chi(q0) instead of chi(q0)^{-1}
            qfac = pd.chars[ci][sd["q0"][i]] if MUTANT else L.inv(pd.chars[ci][sd["q0"][i]])
            coef = L.mul(gamma[(sc[i], ci)], qfac)
            tr[(i, ci)] = pd.madd(em, pd.mscal(coef, ed))
        btrans.append(tr)
    pos = {w: k for k, w in enumerate(order)}
    blocks_by_last = {}
    for bi, (cidx, J) in enumerate(Kb):
        sc = cons[cidx][0]
        last = max(pos[(sc[i], ci)] for i, ci in J)
        blocks_by_last.setdefault(last, []).append(bi)
    assign = {}

    def check(bi):
        cidx, J = Kb[bi]
        sc = cons[cidx][0]
        r = len(sc)
        y = [pd.mzero() for _ in range(r)]
        for (i, ci) in J:
            y[i] = pd.madd(y[i], pd.msub(assign[(sc[i], ci)], btrans[bi][(i, ci)]))
        return in_ULambda(pd, Ups[cidx], tuple(y))

    def bt(k):
        if k == len(order):
            return True
        w = order[k]
        for val in domain[w]:
            assign[w] = val
            if all(check(bi) for bi in blocks_by_last.get(k, [])) and bt(k + 1):
                return True
        del assign[w]
        return False
    return bt(0)

def solvable_Btau(G, cons, nvars, tau):
    fibs = []
    for sc, R in cons:
        tq = tuple(tau[v] for v in sc)
        fibs.append({tuple(n for n, _ in x) for x in R if tuple(q for _, q in x) == tq})
    by_last = {}
    for k, (sc, R) in enumerate(cons):
        by_last.setdefault(max(sc), []).append(k)
    assign = [None] * nvars

    def bt(v):
        if v == nvars:
            return True
        for n in G.N:
            assign[v] = n
            if all(tuple(assign[u] for u in cons[k][0]) in fibs[k] for k in by_last.get(v, [])) and bt(v + 1):
                return True
        assign[v] = None
        return False
    return bt(0)

# ---------------------------------------------------------------- main
def groups():
    out = []
    out.append(mk_cyc_action("S3", 3, 2, 2))
    out.append(mk_cyc_action("D5", 5, 2, 4))
    out.append(mk_cyc_action("Z5:Z4", 5, 4, 2))
    out.append(mk_cyc_action("Z7:Z3", 7, 3, 2))
    out.append(mk_cyc_action("Z7:Z6", 7, 6, 3))
    out.append(mk_cyc_action("D9", 9, 2, 8))
    out.append(mk_cyc_action("D15", 15, 2, 14))
    out.append(mk_Z7_S3())
    out.append(mk_matrix_action("A4", 2, 3, ((0, 1), (1, 1))))
    out.append(mk_matrix_action("Z7^2:Z3 diag(1,2)", 7, 3, ((1, 0), (0, 2))))
    out.append(mk_matrix_action("Z3^2:Z2 diag(1,-1)", 3, 2, ((1, 0), (0, 2))))
    out.append(mk_matrix_action("Z4^2:Z3", 4, 3, ((0, 3), (1, 3))))
    out.append(mk_matrix_action("Z2^3:Z7", 2, 7, ((0, 0, 1), (1, 0, 1), (0, 1, 0))))
    return out

if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    only = sys.argv[3] if len(sys.argv) > 3 else None
    for G in groups():
        if only and G.name != only:
            continue
        pds = [PrimeData(G, p) for p in factor(G.m)]
        rng = random.Random(seed)
        stats = {k: 0 for k in ["shape_ok", "shape_FAIL", "split_ok", "split_FAIL", "C0_ok", "C0_FAIL",
                                "CohK_empty", "dich_ok", "dich_FAIL", "singleton_components",
                                "decomp_ok", "decomp_FAIL", "tau_solvable", "tau_unsolvable"]}
        small = len(G.G) <= 21
        for _ in range(trials):
            nvars = rng.choice([3, 4]) if len(G.N) <= 9 else 3
            ncons = rng.choice([2, 3, 4])
            cons = []
            for _ in range(ncons):
                r = rng.choice([2, 3]) if small else 2
                sc = tuple(rng.randrange(nvars) for _ in range(r))
                R = random_coset(G, r, rng, rng.choice([1, 1, 2]))
                cons.append((sc, R))
            analyse(G, cons, nvars, pds, stats)
        info = ", ".join(f"p={pd.p}: a={pd.a} f={pd.f} |mu|={len(pd.L.mu)} chars={len(pd.chars)} nonzero M_chi={len(pd.Mchi)}" for pd in pds)
        print(f"{G.name:20s} |G|={len(G.G):3d} [{info}]")
        print("    ", {k: v for k, v in stats.items() if v})
        sys.stdout.flush()
