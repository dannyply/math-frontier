"""k2_bb.py -- k=2 sanity test of the per-box functional of red_bb2.py (result 736f29ac).
F_ub, Bred_ub, m_s, f1, f2 copied verbatim from gate_rerun.py (081111185), which copies red_bb2.py.
ONE pair (a,b) in [0,1/3]^2. Pair bound = min(F_ub(use_reuss=gate), Bred_ub if gate).
Gate G1: s>=c, t>=c, a,b>=1/100 (box-level, as valid_c).
Runs:
  K2_RED   : min(F, B_red) gated c=1/10   -> the method's k=2 value
  K2_F     : F alone, Reuss term gated c=1/10 (no B_red)  -> inherited functional (control)
  K2_FNG   : F alone, Reuss term everywhere (no gate)      -> negative control, should be ~Reuss level
  K2_REUSS : Reuss term alone (min(r1,r2)), no B_red      -> sup of Reuss Thm 1 per-box bound
Each run: exact bisection B&B certifying ub<=T, plus bracket search (certify at hi, fail at lo).
Also pointwise evaluation on a fine rational grid to locate the maximiser.
"""
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
def F_ub(alo, ahi, blo, bhi, use_reuss=True, only_reuss=False):
    slo, shi = alo+blo, ahi+bhi
    t_ub = 1 - Fr(3, 2)*slo
    u_ub = (1 - 3*alo)/2
    v_ub = (1 - 3*blo)/2
    terms = [shi, t_ub + min(ahi, bhi)/3, bhi + u_ub + max(F0, ahi - 3*blo)/2, ahi + v_ub + max(F0, bhi - 3*alo)/2]
    if only_reuss:
        terms = [Fr(10**6)]
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
def g1(al, ah, bl, bh, c):
    return (al+bl >= c) and (1 - Fr(3, 2)*(ah+bh) >= c) and al >= H and bl >= H
def make(kind, c=Fr(1, 10)):
    def ub(lo, hi):
        al, bl = lo; ah, bh = hi
        if kind == "K2_REUSS":
            return F_ub(al, ah, bl, bh, True, only_reuss=True)
        if kind == "K2_FNG":
            return F_ub(al, ah, bl, bh, True)
        ok = g1(al, ah, bl, bh, c)
        v = F_ub(al, ah, bl, bh, ok)
        if kind == "K2_RED" and ok:
            v = min(v, Bred_ub(al, ah, bl, bh))
        return v
    return ub
def bb(T, ubf, cap=400000, minw=Fr(1, 2**18)):
    stack = [((F0, F0), (Fr(1, 3), Fr(1, 3)))]; nodes = 0
    while stack:
        lo, hi = stack.pop(); nodes += 1
        u = ubf(lo, hi)
        if u <= T:
            continue
        if hi[0]-lo[0] < minw:
            return ("FAILED", nodes, (float(lo[0]), float(lo[1])), float(u))
        mid = [(lo[k]+hi[k])/2 for k in range(2)]
        for code in range(4):
            nlo = tuple(lo[k] if not (code >> k) & 1 else mid[k] for k in range(2))
            nhi = tuple(mid[k] if not (code >> k) & 1 else hi[k] for k in range(2))
            stack.append((nlo, nhi))
        if nodes > cap:
            return ("CAP", nodes, None, None)
    return ("CERTIFIED", nodes, None, None)
def point(kind, a, b, c=Fr(1, 10)):
    return make(kind, c)((a, b), (a, b))
def grid_max(kind, N=600):
    best = (Fr(-1), None)
    for i in range(N+1):
        a = Fr(i, 3*N)
        for j in range(i, N+1):
            b = Fr(j, 3*N)
            v = point(kind, a, b)
            if v > best[0]:
                best = (v, (a, b))
    return best
if __name__ == "__main__":
    for kind in ["K2_RED", "K2_F", "K2_FNG", "K2_REUSS"]:
        v, (a, b) = grid_max(kind)
        s = a+b
        print("%-8s grid(N=600) max=%s=%.6f at a=%s b=%s s=%.5f t=%.5f m=%.5f" % (kind, v, float(v), a, b, float(s), float(1-Fr(3,2)*s), float(m_s(s))))
        for T in [v, v + Fr(1, 10**4)]:
            r = bb(T, make(kind))
            print("   bb T=%.6f -> %s nodes=%d at=%s ub=%s" % (float(T), r[0], r[1], r[2], r[3]))
    # point diagnostics
    for (a, b) in [(Fr(1,6),Fr(1,6)), (Fr(1,12),Fr(1,4)), (Fr(1,10),Fr(1,5))]:
        al, ah, bl, bh = a, a, b, b
        print("pt a=%s b=%s F(reuss)=%.5f Reuss=%.5f Bred=%.5f" % (a, b, float(F_ub(al,ah,bl,bh,True)), float(F_ub(al,ah,bl,bh,True,True)), float(Bred_ub(al,ah,bl,bh))))
