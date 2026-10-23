"""gate_rerun.py -- independent rerun of the red_bb2.py (sha 76aa0ed1...) FULLC certificate under
stricter / altered B_red gates. Functions F_ub, Bred_ub, bb copied verbatim from red_bb2.py (736f29ac).
Gate variants (box-level: whole box must satisfy):
  G1: s>=c, t>=c, a,b>=1/100                (= red_bb2 valid_c)
  G2: G1 plus u,v>=1/100 (a,b<=49/150)
  G3: s>=c, t>=c only (no a,b floor)
Reuss term of F also used only under the same gate (as FULLC). Also NOGATE: B_red and Reuss everywhere (control)."""
import sys
from fractions import Fraction as Fr
F0 = Fr(0)
def clamp(x, lo, hi):
    return lo if x < lo else (hi if x > hi else x)
def m_s(s):
    return Fr(9, 8)*s*(1 - Fr(3, 2)*s)
def m_bounds(slo, shi):
    return min(m_s(slo), m_s(shi)), m_s(clamp(Fr(1, 3), slo, shi))
def f1(s):
    return (Fr(17, 8)*s - Fr(27, 16)*s*s)/2
def f2(s):
    return (1 - Fr(3, 8)*s - Fr(27, 16)*s*s)/2
def F_ub(alo, ahi, blo, bhi, use_reuss=True):
    slo, shi = alo+blo, ahi+bhi
    t_ub = 1 - Fr(3, 2)*slo
    u_ub = (1 - 3*alo)/2
    v_ub = (1 - 3*blo)/2
    terms = [shi, t_ub + min(ahi, bhi)/3, bhi + u_ub + max(F0, ahi - 3*blo)/2, ahi + v_ub + max(F0, bhi - 3*alo)/2]
    if use_reuss:
        r1 = max(f1(clamp(Fr(17, 27), slo, shi)), ahi, bhi)
        r2 = max(f2(slo), u_ub, v_ub)
        terms.append(min(r1, r2))
    return min(terms)
def Bred_ub(alo, ahi, blo, bhi):
    slo, shi = alo+blo, ahi+bhi
    mlb, mub = m_bounds(slo, shi)
    dmax = max(ahi-blo, bhi-alo)
    if dmax <= Fr(2, 3)*mlb:
        return Fr(3, 4)*mub + Fr(1, 10)
    Xs = [(Fr(3, 20), shi/2), (Fr(3, 10), ahi), (Fr(3, 10), bhi)]
    t_ub = 1 - Fr(3, 2)*slo
    Ys = [(Fr(1, 10), t_ub/2), (Fr(1, 5), (1-3*alo)/2), (Fr(1, 5), (1-3*blo)/2)]
    best = None
    for cX, Xub in Xs:
        for cY, Yub in Ys:
            val = (1 - cX - cY)*mub + Fr(3, 10)*Xub + Fr(1, 5)*Yub
            if best is None or val > best:
                best = val
    return best
H = Fr(1, 100)
def gate(kind, c):
    def g(al, ah, bl, bh):
        s_ok = (al+bl >= c) and (1 - Fr(3, 2)*(ah+bh) >= c)
        if kind == "NOGATE":
            return True
        if kind == "G3":
            return s_ok
        ok = s_ok and al >= H and bl >= H
        if kind == "G2":
            ok = ok and ah <= Fr(49, 150) and bh <= Fr(49, 150)
        return ok
    return g
PAIRS3 = ((0, 1), (0, 2), (1, 2))
def make_ub(kind, c):
    g = gate(kind, c)
    def full(lo, hi):
        best = None
        for i, j in PAIRS3:
            al, ah, bl, bh = lo[i], hi[i], lo[j], hi[j]
            ok = g(al, ah, bl, bh)
            v = F_ub(al, ah, bl, bh, ok)
            if ok:
                v = min(v, Bred_ub(al, ah, bl, bh))
            best = v if best is None or v < best else best
        return best
    return full
def bb(T, lo0, hi0, ubf, cap=3000000, minw=Fr(1, 10**7)):
    dim = len(lo0); stack = [(lo0, hi0)]; nodes = 0; worst = Fr(0)
    while stack:
        lo, hi = stack.pop(); nodes += 1
        ub = ubf(lo, hi)
        if ub <= T:
            if ub > worst: worst = ub
            continue
        if hi[0]-lo[0] < minw:
            return ("FAILED", nodes, [round(float(x), 6) for x in lo], float(ub))
        mid = [(lo[k]+hi[k])/2 for k in range(dim)]
        for code in range(2**dim):
            nlo = tuple(lo[k] if not (code >> k) & 1 else mid[k] for k in range(dim))
            nhi = tuple(mid[k] if not (code >> k) & 1 else hi[k] for k in range(dim))
            stack.append((nlo, nhi))
        if nodes > cap:
            return ("CAP", nodes, None, None)
    return ("CERTIFIED", nodes, None, float(worst))
RUNS = [("G1", "1/10", "77/320"), ("G1", "1/10", "2406/10000"),
        ("G2", "1/100", "77/320"), ("G2", "1/10", "77/320"), ("G2", "1/4", "77/320"), ("G2", "1/4", "2406/10000"),
        ("G1", "1/4", "77/320"), ("G1", "1/3", "77/320"), ("G1", "1/3", "2406/10000"),
        ("G3", "1/100", "77/320"), ("G3", "1/100", "2406/10000"),
        ("NOGATE", "0", "77/320")]
for kind, cs, Ts in RUNS:
    res = bb(Fr(Ts), (F0, F0, F0), (Fr(1, 3),)*3, make_ub(kind, Fr(cs)))
    print("%-6s c=%-5s T=%-11s -> %-9s nodes=%-6d at=%s ub=%s" % (kind, cs, Ts, res[0], res[1], res[2], None if res[3] is None else round(res[3], 10)))
