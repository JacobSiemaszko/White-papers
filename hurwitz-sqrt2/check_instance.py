#!/usr/bin/env python3
"""
Exact instance check of the crossing decomposition of Theorem B in
  Claude (Anthropic), "A 2^{o(n)} Time Algorithm for 3-SAT", 26 Oct 2026, Appendix B,
and of the Hurwitz-type identity it yields (see note.md in this folder).

For a given lambda (N = 2^lambda) this script
  1. builds the operators a[r] of (47) on V = Q[t_1, t_2, ...] (exact integer arithmetic),
  2. checks Lemma 10:  a_mu[-h] b_nu = h! [mu = nu],
  3. checks Lemma 9(a): Q_s is unchanged when the two factors are exchanged,
  4. checks the crossing identity  sum_s A_s(x,y,u,v) = h! [x=v][y=u]  on all N^4 inputs,
  5. counts the rank-1 terms R_s^row, R_s^col of (54)/(55) and compares with the formulas
     R_s^row = sum_{i=0}^{2h} p(s+i),  R_s^col = sum_{i=0}^{2h} p(2h-s-i),
  6. builds the bilinear forms f_k, f_k' (cheapest direction per s) and verifies, as an
     exact polynomial identity in 2N commuting variables,
         h! * (x_1^2 + ... + x_N^2)(y_1^2 + ... + y_N^2) = sum_k f_k f_k',
     and reports the number of products  P = sum_s min(R_s^row, R_s^col).

No dependencies beyond the Python standard library.  Run:  python3 check_instance.py --lam 2
"""
import argparse, itertools, math, sys
from collections import defaultdict

# ---------- partitions and the ring V = Q[t1, t2, ...] -----------------------------------
# A monomial t^mu is a partition mu, stored as a tuple of parts in non-increasing order.
# A polynomial is a dict {monomial: integer coefficient}.

def partitions_of(n, maxpart=None):
    """All partitions of n as non-increasing tuples, in lexicographic order."""
    if maxpart is None:
        maxpart = n
    if n == 0:
        return [()]
    out = []
    for first in range(1, min(n, maxpart) + 1):
        for rest in partitions_of(n - first, first):
            out.append((first,) + rest)
    return out

def partitions_lex(h):
    """Partitions of h in lexicographic order of their non-increasing sequences."""
    return sorted(partitions_of(h))

def p(E):
    return len(partitions_of(E)) if E >= 0 else 0

def gbinom(k, j):
    """Generalised binomial coefficient k(k-1)...(k-j+1)/j! for integer k, integer j."""
    if j < 0:
        return 0
    num = 1
    for i in range(j):
        num *= (k - i)
    return num // math.factorial(j)

def weight(mu):
    return sum(mu)

def mono(mu):
    return tuple(sorted(mu, reverse=True))

def padd(f, g, cg=1):
    """f + cg*g"""
    out = dict(f)
    for m, c in g.items():
        out[m] = out.get(m, 0) + cg * c
        if out[m] == 0:
            del out[m]
    return out

def pscale(f, c):
    return {m: c * v for m, v in f.items()} if c != 0 else {}

def pmul(f, g):
    out = defaultdict(int)
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            out[mono(m1 + m2)] += c1 * c2
    return {m: c for m, c in out.items() if c != 0}

def nabla_minus(f, k):
    """nabla_{-k} f = t_k f"""
    return {mono(m + (k,)): c for m, c in f.items()}

def nabla_plus(f, k):
    """nabla_k f = k * d f / d t_k"""
    out = defaultdict(int)
    for m, c in f.items():
        mult = m.count(k)
        if mult == 0:
            continue
        lst = list(m)
        lst.remove(k)
        out[tuple(lst)] += c * k * mult
    return {m: c for m, c in out.items() if c != 0}

def coeff(f, mu):
    return f.get(mono(mu), 0)

# ---------- the operators a[r] of (47) ---------------------------------------------------

def op_monomial(mu, r, f):
    """t^mu [r] applied to f, by (47): sum over nonzero integers k_i (one per part), sum k_i = -r,
    of prod_i C(-k_i-1, mu_i-1) * (multiplications t_{-k_i} for k_i<0) o (derivatives for k_i>0)."""
    if not f:
        return {}
    if len(mu) == 0:
        return dict(f) if r == 0 else {}
    Emax = max(weight(m) for m in f)
    parts = list(mu)
    n = len(parts)
    result = {}
    # choose which parts get a positive k_i (derivatives) and their values, total P <= Emax
    for signs in itertools.product([1, -1], repeat=n):
        pos_idx = [i for i in range(n) if signs[i] == 1]
        neg_idx = [i for i in range(n) if signs[i] == -1]
        # positive values: compositions with each >=1, total P in [len(pos), Emax]
        def pos_choices(idx):
            if not idx:
                yield ()
                return
            for total in range(len(idx), Emax + 1):
                for comp in compositions(total, len(idx)):
                    yield comp
        for pos_vals in pos_choices(pos_idx):
            P = sum(pos_vals)
            # negatives: k_i = -l_i with l_i >= mu_i (else binomial vanishes), sum l_i = r + P
            target = r + P
            if neg_idx:
                lo = [parts[i] for i in neg_idx]
                if target < sum(lo):
                    continue
                neg_choices = list(compositions_min(target, lo))
            else:
                neg_choices = [()] if target == 0 else []
            for neg_vals in neg_choices:
                # coefficient
                cf = 1
                for i, kv in zip(pos_idx, pos_vals):
                    cf *= gbinom(-kv - 1, parts[i] - 1)
                for i, lv in zip(neg_idx, neg_vals):
                    cf *= gbinom(lv - 1, parts[i] - 1)
                if cf == 0:
                    continue
                g = f
                for kv in pos_vals:            # derivatives first
                    g = nabla_plus(g, kv)
                    if not g:
                        break
                if not g:
                    continue
                for lv in neg_vals:            # then multiplications
                    g = nabla_minus(g, lv)
                result = padd(result, g, cf)
    return result

def compositions(total, k):
    """All k-tuples of integers >= 1 summing to total."""
    if k == 0:
        if total == 0:
            yield ()
        return
    for first in range(1, total - k + 2):
        for rest in compositions(total - first, k - 1):
            yield (first,) + rest

def compositions_min(total, mins):
    """All tuples (l_1..l_k) with l_i >= mins[i] summing to total."""
    k = len(mins)
    if k == 0:
        if total == 0:
            yield ()
        return
    for first in range(mins[0], total - sum(mins[1:]) + 1):
        for rest in compositions_min(total - first, mins[1:]):
            yield (first,) + rest

def op(a, r, f):
    """a[r] f for a polynomial a (linear in a)."""
    out = {}
    for mu, c in a.items():
        out = padd(out, op_monomial(mu, r, f), c)
    return out

def op_monomial_O2(mu, r, f):
    """Same operator via the recursion (O2): a = t_n a'."""
    if not f:
        return {}
    if len(mu) == 0:
        return dict(f) if r == 0 else {}
    n, rest = mu[0], mu[1:]
    Emax = max(weight(m) for m in f)
    out = {}
    for l in range(n, Emax + r + 1):           # a'[r-l] f nonzero needs E + r - l >= 0
        g = op_monomial_O2(rest, r - l, f)
        if g:
            out = padd(out, nabla_minus(g, l), gbinom(l - 1, n - 1))
    for k in range(1, Emax + 1):
        g = nabla_plus(f, k)
        if g:
            out = padd(out, op_monomial_O2(rest, r + k, g), gbinom(-k - 1, n - 1))
    return out

# ---------- a_mu, b_mu, a^<i>, Q_s --------------------------------------------------------

def y_poly(n):
    return {(j,): gbinom(n, j) for j in range(1, n + 1)}

def a_mu(mu):
    a = {(): 1}
    for part in mu:
        a = pmul(a, pscale(y_poly(part), (-1) ** (part - 1)))
    return a

def z_mu(mu):
    z = 1
    for k in set(mu):
        m = mu.count(k)
        z *= k ** m * math.factorial(m)
    return z

def b_mu(mu, h):
    return {mono(mu): math.factorial(h) // z_mu(mu)}

def a_angle(a, i, h):
    """a^<i> = sum_{h'} C(h'+h, i) * (weight-h' component of a)"""
    return {m: c * gbinom(weight(m) + h, i) for m, c in a.items() if gbinom(weight(m) + h, i) != 0}

def Q_s(a, b, s, h, f, exchanged=False):
    """Q_s(a,b) f = sum_{i=0}^{2h} (-1)^i a^<i>[s-h+i] ( b[h-s-i] f ).  exchanged: other order."""
    out = {}
    for i in range(0, 2 * h + 1):
        ai = a_angle(a, i, h)
        if exchanged:
            g = op(ai, s - h + i, f)
            g = op(b, h - s - i, g)
        else:
            g = op(b, h - s - i, f)
            g = op(ai, s - h + i, g)
        out = padd(out, g, (-1) ** i)
    return out

# ---------- main check -------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lam", type=int, default=2, help="lambda; N = 2^lambda strings")
    ap.add_argument("--skip-O2", action="store_true", help="skip the (47)-vs-(O2) cross-check")
    args = ap.parse_args()
    lam = args.lam
    N = 2 ** lam
    h = 2
    while p(h) < N:
        h += 1
    hf = math.factorial(h)
    parts = partitions_lex(h)
    mu_of = parts[:N]                    # string x (as an integer) names the partition mu(x)
    print(f"lambda = {lam}, N = {N}, h = {h} (p({h}) = {p(h)}), d = h! = {hf}, I = [{-2*h}, {2*h}]")
    print("partitions used:", mu_of)

    # cross-check (47) against (O2) on a few random-ish inputs
    if not args.skip_O2:
        ok = True
        for mu in parts:
            for f_mu in parts[:3]:
                for r in range(-h, h + 1):
                    f = {f_mu: 1}
                    if op_monomial(mu, r, f) != op_monomial_O2(mu, r, f):
                        ok = False
        print("check (47) == (O2):", "OK" if ok else "FAIL")
        if not ok:
            sys.exit(1)

    # Lemma 10
    ok = True
    for mu in parts:
        for nu in parts:
            val = coeff(op(a_mu(mu), -h, b_mu(nu, h)), ())
            if val != (hf if mu == nu else 0):
                ok = False
                print("Lemma 10 FAIL", mu, nu, val)
    print("check Lemma 10  a_mu[-h] b_nu = h![mu=nu]:", "OK" if ok else "FAIL")
    if not ok:
        sys.exit(1)

    # precompute A_s(x,y,u,v) and Lemma 9(a)
    A = {}                               # A[s][(x,y,u,v)]
    ok9 = True
    for s in range(-2 * h, 2 * h + 1):
        A[s] = {}
        for x in range(N):
            ax = a_mu(mu_of[x])
            for v in range(N):
                bv = b_mu(mu_of[v], h)
                for y in range(N):
                    f = {mu_of[y]: 1}
                    g = Q_s(ax, bv, s, h, f)
                    if s in (-2 * h, 0, 2 * h) or (x, v, y) == (0, 0, 0):
                        g2 = Q_s(ax, bv, s, h, f, exchanged=True)
                        if g != g2:
                            ok9 = False
                    for u in range(N):
                        A[s][(x, y, u, v)] = coeff(g, mu_of[u])
    print("check Lemma 9(a) (factor exchange, sampled):", "OK" if ok9 else "FAIL")

    # crossing identity
    ok = True
    for x, y, u, v in itertools.product(range(N), repeat=4):
        tot = sum(A[s][(x, y, u, v)] for s in A)
        want = hf if (x == v and y == u) else 0
        if tot != want:
            ok = False
    print(f"check sum_s A_s = {hf}*[x=v][y=u] on all {N**4} inputs:", "OK" if ok else "FAIL")
    if not ok:
        sys.exit(1)

    # term counts of (54)/(55) and the bilinear forms
    # (54): A_s = sum_i sum_{|sigma|=s+i} (-1)^i [t^sigma] a^<i>[s-h+i] t^mu(y)  *  [t^mu(u)] b[h-s-i] t^sigma
    # (55): A_s = sum_i sum_{|sigma|=2h-s-i} (-1)^i [t^mu(u)] a^<i>[s-h+i] t^sigma  *  [t^sigma] b[h-s-i] t^mu(y)
    total_terms = 0
    forms = []                           # list of (F, G) with F,G dicts {(a,b): coeff} = bilinear forms in X,Y
    for s in range(-2 * h, 2 * h + 1):
        Rrow = sum(p(s + i) for i in range(0, 2 * h + 1))
        Rcol = sum(p(2 * h - s - i) for i in range(0, 2 * h + 1))
        # count terms actually present (equal to the formulas; the formulas count all pairs (i,sigma))
        if Rrow <= Rcol:
            # row-wise: F(x,y) G(u,v)   ->  f = sum F(x,y) X_x Y_y ,  f' = sum G(u,v) X_v Y_u
            cnt = 0
            for i in range(0, 2 * h + 1):
                for sigma in partitions_of(s + i) if s + i >= 0 else []:
                    F = {}
                    for x in range(N):
                        ai = a_angle(a_mu(mu_of[x]), i, h)
                        for y in range(N):
                            c = ((-1) ** i) * coeff(op(ai, s - h + i, {mu_of[y]: 1}), sigma)
                            if c:
                                F[(x, y)] = c
                    G = {}
                    for v in range(N):
                        bv = b_mu(mu_of[v], h)
                        gpoly = op(bv, h - s - i, {sigma: 1})
                        for u in range(N):
                            c = coeff(gpoly, mu_of[u])
                            if c:
                                G[(v, u)] = c          # keyed (X-index v, Y-index u)
                    cnt += 1
                    forms.append((F, G))
            assert cnt == Rrow, (s, cnt, Rrow)
            total_terms += Rrow
        else:
            # column-wise: F'(x,u) G'(y,v) -> f = sum F'(x,u) X_x Y_u , f' = sum G'(y,v) X_v Y_y
            cnt = 0
            for i in range(0, 2 * h + 1):
                for sigma in partitions_of(2 * h - s - i) if 2 * h - s - i >= 0 else []:
                    F = {}
                    for x in range(N):
                        ai = a_angle(a_mu(mu_of[x]), i, h)
                        gpoly = op(ai, s - h + i, {sigma: 1})
                        for u in range(N):
                            c = ((-1) ** i) * coeff(gpoly, mu_of[u])
                            if c:
                                F[(x, u)] = c          # (X-index x, Y-index u)
                    G = {}
                    for v in range(N):
                        bv = b_mu(mu_of[v], h)
                        for y in range(N):
                            c = coeff(op(bv, h - s - i, {mu_of[y]: 1}), sigma)
                            if c:
                                G[(v, y)] = c          # (X-index v, Y-index y)
                    cnt += 1
                    forms.append((F, G))
            assert cnt == Rcol, (s, cnt, Rcol)
            total_terms += Rcol
    print(f"number of products P = sum_s min(R_s^row, R_s^col) = {total_terms}")
    print(f"  (N^2 = {N**2}; log_N P = {math.log(total_terms)/math.log(N):.3f})")

    # verify the Hurwitz-type identity  h! (sum X_a^2)(sum Y_b^2) = sum_k f_k f_k'
    # monomial in X,Y: tuple of 2N exponents
    def bil_to_poly(F):
        poly = defaultdict(int)
        for (a, b), c in F.items():
            e = [0] * (2 * N)
            e[a] += 1
            e[N + b] += 1
            poly[tuple(e)] += c
        return poly
    def poly_mul(P1, P2):
        out = defaultdict(int)
        for m1, c1 in P1.items():
            for m2, c2 in P2.items():
                out[tuple(i + j for i, j in zip(m1, m2))] += c1 * c2
        return out
    lhs = defaultdict(int)
    for a in range(N):
        for b in range(N):
            e = [0] * (2 * N)
            e[a] = 2
            e[N + b] = 2
            lhs[tuple(e)] += hf
    rhs = defaultdict(int)
    for F, G in forms:
        prod = poly_mul(bil_to_poly(F), bil_to_poly(G))
        for m, c in prod.items():
            rhs[m] += c
    rhs = {m: c for m, c in rhs.items() if c != 0}
    lhs = {m: c for m, c in lhs.items() if c != 0}
    ok = (rhs == lhs)
    print(f"check {hf}*(sum X_a^2)(sum Y_b^2) == sum_k f_k f_k' as polynomials in {2*N} variables:",
          "OK" if ok else "FAIL")
    if not ok:
        diff = {m: rhs.get(m, 0) - lhs.get(m, 0) for m in set(rhs) | set(lhs) if rhs.get(m, 0) != lhs.get(m, 0)}
        print("  first differences:", list(diff.items())[:5])
        sys.exit(1)
    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
