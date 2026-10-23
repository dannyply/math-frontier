#!/usr/bin/env python3
"""certificates.py -- exact-rational branch-and-bound certificates for the paper
"Counting powerful products of consecutive integers".

Everything is computed with fractions.Fraction; no floating point enters any
comparison.  A run prints CERTIFIED only if the whole parameter region has been
covered by boxes on which a *rigorous upper bound* of the per-box exponent
functional is <= the target T.

Notation (exponents relative to log X; see Section 2 of the paper):
  a, b    exponents of the squarefree cube parts d_i ~ X^a, d_j ~ X^b, in [0,1/3]
  s = a+b, t = 1 - 3s/2, u = (1-3a)/2, v = (1-3b)/2
  m = (9/8) s t          (the determinant exponent, (2.2) and Lemma 2.9 of the paper)

Pointwise pair bounds (each is proved or cited in the paper; numbering as in
the paper):
  PELL  = s                                 (Lemma 3.1(i))
  THUE  = t                                 (Lemma 3.1(ii), Stewart)
  HB1   = b + u + max(0, a-3b)/2            (Lemma 3.2, k=2 only)
  HB2   = a + v + max(0, b-3a)/2            (Lemma 3.2, k=2 only)
  REUSS = min(max((s+m)/2, a, b), max((t+m)/2, u, v))   (Reuss Thm 1 = Theorem 2.4, k=2 only)
  BRED  = m + (3/10) l* + (1/5) tau*,  l* = max((s-m)/2, a-m, b-m),
          tau* = max((t-m)/2, u-m, v-m)                 (Theorem 5.4)
  B_theta = m + 3 theta l* + 2 theta tau*               (conditional, Remark 8.3)
REUSS, BRED, B_theta are used only on boxes inside the gate
  G1: s >= c and t >= c on the whole box, and a, b >= 1/100  (c = 1/10).
(The a,b >= 1/100 floor is not needed mathematically; it only makes the gate
 smaller, hence the certified functional larger, hence the certificate weaker.)

Modes run by default:
  K3_MIN      k>=3, functional min_pairs min(PELL, THUE, BRED) on [0,1/3]^3, T=77/320
  K3_MIN_CTL  same, T=0.2406 (negative control: must FAIL)
  K3_REVIEWED the functional of gate_rerun.py (G1, c=1/10) reproduced verbatim, T=77/320
  K2_INT      k=2, min(PELL,THUE,HB1,HB2,REUSS,BRED) on [1/100,1/3]^2, T=101/400 and T=0.2476
  K2_INT_CTL  same, T=0.2474 (must FAIL)
  CENTRAL     min over pairs of BRED on [19/100,21/100]^3, T=38059/160000; control T-1e-6
  THETA       B_theta with theta=1/12 in place of BRED, K3_MIN otherwise, T=89/384; control
  ARITH       closed-form checks
  SELFTEST    soundness self-test: for every accepted leaf of K3_MIN, K2_INT (0.2476),
              CENTRAL and THETA, the exact functional at grid points of the leaf
              (corners, edge and interior points) is <= the accepted box bound, and
              each term's box bound dominates the exact term there; the same term
              check on 3001 random boxes; and a mutation test (reversed endpoint
              choices for the maxima of m and (s+m)/2) that the check must detect.
              SUMMARY is ALL AS EXPECTED only if the self-test passes.
Run:  nice -n 10 python3 certificates.py
"""
from fractions import Fraction as Fr
import sys

F0 = Fr(0)
C_GATE = Fr(1, 10)
FLOOR = Fr(1, 100)


def clamp(x, lo, hi):
    return lo if x < lo else (hi if x > hi else x)


def m_of(s):
    return Fr(9, 8) * s * (1 - Fr(3, 2) * s)


# MUTANT=True reverses the endpoint choices for the maxima of m and (s+m)/2 (the
# wrong-endpoint error described in the paper for endpoint_cert.py).  It is used
# only by the SELFTEST, to show that the self-test detects such an error.
MUTANT = False


def _peak(p, slo, shi):
    if MUTANT:
        return p if slo <= p <= shi else (slo if shi < p else shi)
    return clamp(p, slo, shi)


def m_range(slo, shi):
    """m is concave in s with maximum at s = 1/3."""
    return min(m_of(slo), m_of(shi)), m_of(_peak(Fr(1, 3), slo, shi))


# ---- rigorous box upper bounds for each pointwise term -------------------------
def ub_pell(al, ah, bl, bh):
    return ah + bh


def ub_thue(al, ah, bl, bh):
    return 1 - Fr(3, 2) * (al + bl)


def ub_hb1(al, ah, bl, bh):
    return bh + (1 - 3 * al) / 2 + max(F0, ah - 3 * bl) / 2


def ub_hb2(al, ah, bl, bh):
    return ah + (1 - 3 * bl) / 2 + max(F0, bh - 3 * al) / 2


def f1(s):  # (s+m)/2, concave, maximum at s = 17/27
    return (Fr(17, 8) * s - Fr(27, 16) * s * s) / 2


def f2(s):  # (t+m)/2, decreasing on s >= 0
    return (1 - Fr(3, 8) * s - Fr(27, 16) * s * s) / 2


def ub_reuss(al, ah, bl, bh):
    slo, shi = al + bl, ah + bh
    r1 = max(f1(_peak(Fr(17, 27), slo, shi)), ah, bh)
    r2 = max(f2(slo), (1 - 3 * al) / 2, (1 - 3 * bl) / 2)
    return min(r1, r2)


def ub_btheta(al, ah, bl, bh, theta=Fr(1, 10)):
    """Upper bound for m + 3 theta l* + 2 theta tau* over the box (theta <= 1/10)."""
    slo, shi = al + bl, ah + bh
    mlb, mub = m_range(slo, shi)
    dmax = max(ah - bl, bh - al)
    if dmax <= Fr(2, 3) * mlb:
        # balanced on the whole box: l*=(s-m)/2, tau*=(t-m)/2, 3s+2t=2
        return (1 - Fr(5, 2) * theta) * mub + theta
    t_ub = 1 - Fr(3, 2) * slo
    Xs = [(Fr(3, 2) * theta, Fr(3, 2) * theta * shi), (3 * theta, 3 * theta * ah), (3 * theta, 3 * theta * bh)]
    Ys = [(theta, theta * t_ub), (2 * theta, 2 * theta * (1 - 3 * al) / 2), (2 * theta, 2 * theta * (1 - 3 * bl) / 2)]
    best = None
    for cX, xv in Xs:
        for cY, yv in Ys:
            coef = 1 - cX - cY  # >= 1 - 5 theta > 0
            val = coef * mub + xv + yv
            best = val if best is None or val > best else best
    return best


def in_gate(al, ah, bl, bh, c=C_GATE, floor=FLOOR):
    return (al + bl >= c) and (1 - Fr(3, 2) * (ah + bh) >= c) and al >= floor and bl >= floor


# ---- pair functionals -------------------------------------------------------------
def pair_k3_min(al, ah, bl, bh, theta=Fr(1, 10)):
    v = min(ub_pell(al, ah, bl, bh), ub_thue(al, ah, bl, bh))
    if in_gate(al, ah, bl, bh):
        v = min(v, ub_btheta(al, ah, bl, bh, theta))
    return v


def pair_k2(al, ah, bl, bh):
    v = min(ub_pell(al, ah, bl, bh), ub_thue(al, ah, bl, bh), ub_hb1(al, ah, bl, bh), ub_hb2(al, ah, bl, bh))
    if in_gate(al, ah, bl, bh):
        v = min(v, ub_reuss(al, ah, bl, bh), ub_btheta(al, ah, bl, bh))
    return v


PAIRS3 = ((0, 1), (0, 2), (1, 2))


def triple(pairf):
    def ub(lo, hi):
        return min(pairf(lo[i], hi[i], lo[j], hi[j]) for i, j in PAIRS3)
    return ub


def single(pairf):
    def ub(lo, hi):
        return pairf(lo[0], hi[0], lo[1], hi[1])
    return ub


# ---- branch and bound (same scheme as gate_rerun.py) -------------------------------
def bb(T, lo0, hi0, ubf, cap=3_000_000, minw=Fr(1, 10**7), record=None):
    dim = len(lo0)
    stack = [(tuple(lo0), tuple(hi0))]
    nodes = 0
    worst = F0
    while stack:
        lo, hi = stack.pop()
        nodes += 1
        ub = ubf(lo, hi)
        if ub <= T:
            worst = max(worst, ub)
            if record is not None:
                record.append((lo, hi, ub))
            continue
        if hi[0] - lo[0] < minw:
            return ("FAILED", nodes, [float(x) for x in lo], float(ub))
        mid = [(lo[k] + hi[k]) / 2 for k in range(dim)]
        for code in range(2 ** dim):
            nlo = tuple(lo[k] if not (code >> k) & 1 else mid[k] for k in range(dim))
            nhi = tuple(mid[k] if not (code >> k) & 1 else hi[k] for k in range(dim))
            stack.append((nlo, nhi))
        if nodes > cap:
            return ("CAP", nodes, None, None)
    return ("CERTIFIED", nodes, None, worst)


def report(name, T, res):
    st, nodes, where, val = res
    if st == "CERTIFIED":
        print("%-12s T=%-15s %-9s nodes=%-6d worst box bound=%s (=%.10f)" % (name, T, st, nodes, val, float(val)))
    else:
        print("%-12s T=%-15s %-9s nodes=%-6d near=%s bound=%s" % (name, T, st, nodes,
              None if where is None else [round(x, 6) for x in where], val))
    sys.stdout.flush()
    return st


def reviewed_functional():
    """The functional of gate_rerun.py (G1, c=1/10), functions copied from that script."""
    src = open(__file__.replace("certificates.py", "gate_rerun.py")).read().split("RUNS = [")[0]
    ns = {}
    exec(src, ns)
    return ns["make_ub"]("G1", Fr(1, 10)), ns["bb"]

# ---- soundness self-test ---------------------------------------------------------
# Exact pointwise values of the terms (independent of the box-bound code above).
def pt_terms(a, b, theta=Fr(1, 10)):
    s = a + b
    t = 1 - Fr(3, 2) * s
    u, v = (1 - 3 * a) / 2, (1 - 3 * b) / 2
    m = m_of(s)
    lst = max((s - m) / 2, a - m, b - m)
    tst = max((t - m) / 2, u - m, v - m)
    return {
        "pell": s, "thue": t,
        "hb1": b + u + max(F0, a - 3 * b) / 2,
        "hb2": a + v + max(F0, b - 3 * a) / 2,
        "reuss": min(max((s + m) / 2, a, b), max((t + m) / 2, u, v)),
        "btheta": m + 3 * theta * lst + 2 * theta * tst,
        "gate": s >= C_GATE and t >= C_GATE and a >= FLOOR and b >= FLOOR,
    }


def pt_pair_k3_min(a, b, theta=Fr(1, 10)):
    T = pt_terms(a, b, theta)
    v = min(T["pell"], T["thue"])
    return min(v, T["btheta"]) if T["gate"] else v


def pt_pair_k2(a, b):
    T = pt_terms(a, b)
    v = min(T["pell"], T["thue"], T["hb1"], T["hb2"])
    return min(v, T["reuss"], T["btheta"]) if T["gate"] else v


def box_term_bounds(al, ah, bl, bh, theta):
    return {"pell": ub_pell(al, ah, bl, bh), "thue": ub_thue(al, ah, bl, bh),
            "hb1": ub_hb1(al, ah, bl, bh), "hb2": ub_hb2(al, ah, bl, bh),
            "reuss": ub_reuss(al, ah, bl, bh), "btheta": ub_btheta(al, ah, bl, bh, theta)}


def grid_points(lo, hi, k=3):
    """All points lo + (hi-lo)*i/k, i = 0..k, in each coordinate (corners, edges, interior)."""
    pts = [()]
    for c in range(len(lo)):
        pts = [p + (lo[c] + (hi[c] - lo[c]) * i / k,) for p in pts for i in range(k + 1)]
    return pts


def term_violations(al, ah, bl, bh, theta=Fr(1, 10)):
    B = box_term_bounds(al, ah, bl, bh, theta)
    bad = 0
    for a, b in grid_points((al, bl), (ah, bh)):
        T = pt_terms(a, b, theta)
        bad += sum(1 for k in B if T[k] > B[k])
    return bad


def leaf_violations(leaves, pointf, theta=Fr(1, 10)):
    bad = 0
    for lo, hi, ub in leaves:
        k = 3 if len(lo) == 2 else 2
        for p in grid_points(lo, hi, k):
            if pointf(p) > ub:
                bad += 1
        for i in range(len(lo)):
            for j in range(i + 1, len(lo)):
                bad += term_violations(lo[i], hi[i], lo[j], hi[j], theta)
    return bad


def random_boxes(n, seed=20260930):
    import random
    rng = random.Random(seed)
    third = Fr(1, 3)
    out = [(Fr(1, 10), Fr(3, 20), Fr(1, 10), Fr(3, 20))]
    for _ in range(n):
        k = rng.randint(1, 14)
        q = 3 * 2 ** k
        i, j = rng.randrange(2 ** k), rng.randrange(2 ** k)
        al, bl = Fr(i, q), Fr(j, q)
        ah, bh = min(Fr(i + rng.randint(1, 4), q), third), min(Fr(j + rng.randint(1, 4), q), third)
        assert F0 <= al < ah <= third and F0 <= bl < bh <= third
        out.append((al, ah, bl, bh))
    return out


def selftest():
    global MUTANT
    ok_all = True
    print("SELFTEST: exact values at grid points of every accepted leaf must not exceed the leaf bound;")
    print("          every term's box bound must dominate the exact term at those points")
    th = Fr(1, 12)
    cube0, cube1 = (F0,) * 3, (Fr(1, 3),) * 3
    sq0, sq1 = (FLOOR, FLOOR), (Fr(1, 3), Fr(1, 3))
    c0, c1 = (Fr(19, 100),) * 3, (Fr(21, 100),) * 3
    tri = lambda pf: (lambda p: min(pf(p[i], p[j]) for i, j in PAIRS3))
    runs = [
        ("K3_MIN", Fr(77, 320), cube0, cube1, triple(pair_k3_min), tri(pt_pair_k3_min), Fr(1, 10), {}),
        ("K2_INT", Fr(2476, 10000), sq0, sq1, single(pair_k2), lambda p: pt_pair_k2(p[0], p[1]), Fr(1, 10),
         {"minw": Fr(1, 2**22)}),
        ("CENTRAL", Fr(38059, 160000), c0, c1,
         lambda lo, hi: min(ub_btheta(lo[i], hi[i], lo[j], hi[j]) for i, j in PAIRS3),
         lambda p: min(pt_terms(p[i], p[j])["btheta"] for i, j in PAIRS3), Fr(1, 10), {}),
        ("THETA_1/12", Fr(89, 384), cube0, cube1, triple(lambda al, ah, bl, bh: pair_k3_min(al, ah, bl, bh, th)),
         tri(lambda a, b: pt_pair_k3_min(a, b, th)), th, {}),
    ]
    for name, T, lo, hi, ubf, pf, theta, kw in runs:
        leaves = []
        r = bb(T, lo, hi, ubf, record=leaves, **kw)
        npts = sum(len(grid_points(l, h, 3 if len(l) == 2 else 2)) for l, h, _ in leaves)
        bad = leaf_violations(leaves, pf, theta)
        ok = r[0] == "CERTIFIED" and bad == 0
        print("SELFTEST %-11s %s nodes=%-5d accepted leaves=%-5d leaf points=%-6d violations=%d  [%s]"
              % (name, r[0], r[1], len(leaves), npts, bad, "OK" if ok else "FAIL"))
        ok_all &= ok
    boxes = random_boxes(3000)
    nb = sum(1 for bx in boxes if term_violations(*bx) or term_violations(*bx, theta=th))
    ok = nb == 0
    print("SELFTEST RANDOM      %d boxes (incl. [1/10,3/20]^2), all term bounds, theta=1/10 and 1/12:"
          " boxes with a violation=%d  [%s]" % (len(boxes), nb, "OK" if ok else "FAIL"))
    ok_all &= ok
    MUTANT = True
    try:
        nbm = sum(1 for bx in boxes if term_violations(*bx))
    finally:
        MUTANT = False
    ok = nbm > 0
    print("SELFTEST MUTANT      reversed endpoint choices: boxes with a violation=%d (must be > 0)  [%s]"
          % (nbm, "OK" if ok else "FAIL"))
    ok_all &= ok
    return ok_all


def main():
    out = {}
    cube0, cube1 = (F0,) * 3, (Fr(1, 3),) * 3
    out["K3_MIN"] = report("K3_MIN", "77/320", bb(Fr(77, 320), cube0, cube1, triple(pair_k3_min)))
    out["K3_MIN_CTL"] = report("K3_MIN_CTL", "0.2406", bb(Fr(2406, 10000), cube0, cube1, triple(pair_k3_min)))
    try:
        ubf, bbr = reviewed_functional()
        r = bbr(Fr(77, 320), cube0, cube1, ubf)
        print("%-12s T=%-15s %-9s nodes=%-6d (gate_rerun.py functional, verbatim)" % ("K3_REVIEWED", "77/320", r[0], r[1]))
    except FileNotFoundError:
        print("K3_REVIEWED  skipped (gate_rerun.py not found next to this script)")
    sq0, sq1 = (FLOOR, FLOOR), (Fr(1, 3), Fr(1, 3))
    out["K2_INT"] = report("K2_INT", "101/400", bb(Fr(101, 400), sq0, sq1, single(pair_k2), minw=Fr(1, 2**22)))
    out["K2_INT_2476"] = report("K2_INT", "0.2476", bb(Fr(2476, 10000), sq0, sq1, single(pair_k2), minw=Fr(1, 2**22)))
    out["K2_INT_CTL"] = report("K2_INT_CTL", "0.2474", bb(Fr(2474, 10000), sq0, sq1, single(pair_k2), minw=Fr(1, 2**22)))
    c0, c1 = (Fr(19, 100),) * 3, (Fr(21, 100),) * 3
    bred_only = lambda lo, hi: min(ub_btheta(lo[i], hi[i], lo[j], hi[j]) for i, j in PAIRS3)
    out["CENTRAL"] = report("CENTRAL", "38059/160000", bb(Fr(38059, 160000), c0, c1, bred_only))
    out["CENTRAL_CTL"] = report("CENTRAL_CTL", "T-1e-6", bb(Fr(38059, 160000) - Fr(1, 10**6), c0, c1, bred_only))
    th = Fr(1, 12)
    k3_theta = triple(lambda al, ah, bl, bh: pair_k3_min(al, ah, bl, bh, th))
    out["THETA"] = report("THETA_1/12", "89/384", bb(Fr(89, 384), cube0, cube1, k3_theta))
    out["THETA_CTL"] = report("THETA_CTL", "89/384-1e-4", bb(Fr(89, 384) - Fr(1, 10**4), cube0, cube1, k3_theta))
    # closed-form arithmetic
    sixth = Fr(1, 6)
    m6 = m_of(Fr(1, 3))
    checks = [
        ("m(1/3) = 3/16", m6 == Fr(3, 16)),
        ("BRED(1/6,1/6) = 77/320", ub_btheta(sixth, sixth, sixth, sixth) == Fr(77, 320)),
        ("(3/4)(3/16)+1/10 = 77/320", Fr(3, 4) * Fr(3, 16) + Fr(1, 10) == Fr(77, 320)),
        ("m(19/50) = 7353/40000", m_of(Fr(19, 50)) == Fr(7353, 40000)),
        ("BRED(19/100,19/100) = 38059/160000",
         ub_btheta(Fr(19, 100), Fr(19, 100), Fr(19, 100), Fr(19, 100)) == Fr(38059, 160000)),
        ("B_{1/12}(1/6,1/6) = 89/384", ub_btheta(sixth, sixth, sixth, sixth, Fr(1, 12)) == Fr(89, 384)),
        ("1/4 + (1/100)/4 = 101/400", Fr(1, 4) + FLOOR / 4 == Fr(101, 400)),
        ("REUSS alone at s=t=2/5, a=1/6 gives 29/100", f1(Fr(2, 5)) == Fr(29, 100) and f2(Fr(2, 5)) == Fr(29, 100)),
        ("with 9/8 replaced by 1 the balanced value at s=1/3 is 9/40",
         Fr(3, 4) * (Fr(1, 3) * Fr(1, 2)) + Fr(1, 10) == Fr(9, 40)),
    ]
    for name, ok in checks:
        print("ARITH  %-55s %s" % (name, "OK" if ok else "MISMATCH"))
    expected = {"K3_MIN": "CERTIFIED", "K3_MIN_CTL": "FAILED", "K2_INT": "CERTIFIED", "K2_INT_2476": "CERTIFIED",
                "K2_INT_CTL": "FAILED", "CENTRAL": "CERTIFIED", "CENTRAL_CTL": "FAILED",
                "THETA": "CERTIFIED", "THETA_CTL": "FAILED"}
    bad = [k for k, v in expected.items() if out.get(k) != v] + [n for n, ok in checks if not ok]
    if not selftest():
        bad.append("SELFTEST")
    print("SUMMARY:", "ALL AS EXPECTED" if not bad else "UNEXPECTED: %s" % bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
