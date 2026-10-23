#!/usr/bin/env python3
"""endpoint_cert.py -- exact-rational verification for the k=2 endpoint x^{1/4+eps}.

Independent re-implementation (does not import the paper's scripts).  All
comparisons use fractions.Fraction; no floating point enters any decision
(floats appear only in printed diagnostics).

Numbering as in paper-final/main.pdf: strip lemma = Lemma 6.3, full-square
bound = Proposition 6.4, Reuss Thm 1 = Theorem 2.4.
Exponents (paper, Section 2):  a, b in [0,1/3];  s=a+b;  t=1-3s/2;
  ub=(1-3a)/2, vb=(1-3b)/2;  m=(9/8)st.
Pointwise per-box exponents available for k=2 (h=1, d,e squarefree):
  PELL  = s                        Lemma 3.1(i)            always
  THUE  = t                        Lemma 3.1(ii)           always
  HB1   = b+ub+max(0,a-3b)/2       Lemma 3.2               always
  HB2   = a+vb+max(0,b-3a)/2       Lemma 3.2               always
  REUSS = min(max((s+m)/2,a,b), max((t+m)/2,ub,vb))   Reuss Thm 1 (h=1)
          valid when log(DE) ~ log(UV) ~ log x, i.e. s,t >= c > 0 (and D,E>1)
  BRED  = m+(3/10)l*+(1/5)t*       Theorem 5.4, valid when s,t >= c
The paper's functional Phi_2 gates REUSS and BRED by
  G = {s>=1/10, t>=1/10, a>=1/100, b>=1/100}.
The endpoint functional Phi_2# gates REUSS only by G0 = {s>=1/10, t>=1/10}
(the hypothesis of Reuss's Theorem 1) and BRED by G as before.

Runs (nice -n 10 python3 endpoint_cert.py):
  ARITH      corner values and the constants in the strip lemma
  STRIP      box B&B of min(PELL,HB2,REUSS[G0]) on [0,1/100]x[0,1/3] at T=1/4
  STRIP_CTL  same without REUSS  (must FAIL: value 1/4+a/4)
  FULL       box B&B of Phi_2# on [0,1/3]^2 at T=1/4          (main certificate)
  FULL_CTL1  same at T=1/4-10^-6                               (must FAIL at a corner)
  FULL_CTL2  Phi_2 (paper gate, REUSS floored) on [0,1/3]^2 at T=1/4 (must FAIL)
  INT        Phi_2 on [1/100,1/3]^2: T=0.2476 certify, T=0.2474 fail (paper K2_INT)
  FLOOR      sup of Phi_2 on [H,1/3]^2 bracketed for several H (expect 1/4-H/4)
  GRID       exact pointwise max of Phi_2# on a rational grid; ridge 1/4-a/4
  SELFTEST   soundness self-test: for every accepted leaf of STRIP, FULL, FULL_B0
             and INT, the exact functional at 16 rational points of the leaf
             (corners, edges, interior) is <= the accepted box bound, and every
             term's box bound dominates the exact term there; the same term check
             on 4001 random boxes; and a mutation test showing that the reversed
             endpoint choices are detected.
  The SUMMARY line is ALL AS EXPECTED only if the self-test passes.
"""
from fractions import Fraction as Fr
import sys

Z = Fr(0)
C = Fr(1, 10)
FLOOR = Fr(1, 100)
Q = Fr(1, 4)


def m_of(s):
    return Fr(9, 8) * s * (1 - Fr(3, 2) * s)


# ---------------- pointwise terms ----------------
def terms_point(a, b):
    s = a + b
    t = 1 - Fr(3, 2) * s
    ub = (1 - 3 * a) / 2
    vb = (1 - 3 * b) / 2
    m = m_of(s)
    hb1 = b + ub + max(Z, a - 3 * b) / 2
    hb2 = a + vb + max(Z, b - 3 * a) / 2
    reuss = min(max((s + m) / 2, a, b), max((t + m) / 2, ub, vb))
    lst = max((s - m) / 2, a - m, b - m)
    tst = max((t - m) / 2, ub - m, vb - m)
    bred = m + Fr(3, 10) * lst + Fr(1, 5) * tst
    g0 = s >= C and t >= C
    g = g0 and a >= FLOOR and b >= FLOOR
    return dict(s=s, t=t, hb1=hb1, hb2=hb2, reuss=reuss, bred=bred, g0=g0, g=g)


def phi_point(a, b, reuss_gate="G0", use_bred=True, only=None):
    T = terms_point(a, b)
    vals = []
    names = only if only is not None else ["s", "t", "hb1", "hb2", "reuss", "bred"]
    for nm in names:
        if nm == "reuss":
            ok = T["g0"] if reuss_gate == "G0" else (T["g"] if reuss_gate == "G" else False)
            if ok:
                vals.append(T["reuss"])
        elif nm == "bred":
            if use_bred and T["g"]:
                vals.append(T["bred"])
        else:
            vals.append(T[nm])
    return min(vals)


# ---------------- rigorous box upper bounds ----------------
# MUTANT=True reverses the endpoint choices (the wrong-endpoint error described in
# the paper); used only by the SELFTEST to show that the self-test
# detects that error.  Never set outside SELFTEST.
MUTANT = False


def clamp(x, lo, hi):
    return min(max(x, lo), hi)


def m_range(slo, shi):
    # m concave in s, maximum at s=1/3: on [slo,shi] the maximum is at clamp(1/3)
    third = Fr(1, 3)
    if MUTANT:
        peak = third if slo <= third <= shi else (slo if shi < third else shi)
    else:
        peak = clamp(third, slo, shi)
    return min(m_of(slo), m_of(shi)), m_of(peak)


def f1(s):  # (s+m)/2 = (17s/8 - 27s^2/16)/2, concave, peak at 17/27
    return (Fr(17, 8) * s - Fr(27, 16) * s * s) / 2


def f2(s):  # (t+m)/2 = (1 - 3s/8 - 27s^2/16)/2, decreasing for s>=0
    return (1 - Fr(3, 8) * s - Fr(27, 16) * s * s) / 2


def box_terms(al, ah, bl, bh):
    slo, shi = al + bl, ah + bh
    ub_hi = (1 - 3 * al) / 2
    vb_hi = (1 - 3 * bl) / 2
    t_hi = 1 - Fr(3, 2) * slo
    out = {}
    out["s"] = shi
    out["t"] = t_hi
    # HB2 = max(a+(1-3b)/2, 1/2-b-a/2): each linear piece maximised at a corner
    out["hb2"] = max(ah + (1 - 3 * bl) / 2, Fr(1, 2) - bl - al / 2)
    out["hb1"] = max(bh + (1 - 3 * al) / 2, Fr(1, 2) - al - bl / 2)
    pk = Fr(17, 27)   # (s+m)/2 is concave with maximum at s=17/27
    if MUTANT:
        s1 = pk if slo <= pk <= shi else (slo if shi < pk else shi)
    else:
        s1 = clamp(pk, slo, shi)
    r1 = max(f1(s1), ah, bh)
    r2 = max(f2(slo), ub_hi, vb_hi)
    out["reuss"] = min(r1, r2)
    mlo, mhi = m_range(slo, shi)
    if max(ah - bl, bh - al) <= Fr(2, 3) * mlo:
        out["bred"] = Fr(3, 4) * mhi + Fr(1, 10)       # balanced form (Lemma 5.5)
    else:
        Xs = [(Fr(3, 20), Fr(3, 20) * shi), (Fr(3, 10), Fr(3, 10) * ah), (Fr(3, 10), Fr(3, 10) * bh)]
        Ys = [(Fr(1, 10), Fr(1, 10) * t_hi), (Fr(1, 5), Fr(1, 5) * ub_hi), (Fr(1, 5), Fr(1, 5) * vb_hi)]
        out["bred"] = max((1 - cx - cy) * mhi + X + Y for cx, X in Xs for cy, Y in Ys)
    g0 = slo >= C and (1 - Fr(3, 2) * shi) >= C
    out["g0"] = g0
    out["g"] = g0 and al >= FLOOR and bl >= FLOOR
    return out


def phi_box(al, ah, bl, bh, reuss_gate="G0", use_bred=True, only=None):
    B = box_terms(al, ah, bl, bh)
    names = only if only is not None else ["s", "t", "hb1", "hb2", "reuss", "bred"]
    vals = []
    for nm in names:
        if nm == "reuss":
            ok = B["g0"] if reuss_gate == "G0" else (B["g"] if reuss_gate == "G" else False)
            if ok:
                vals.append(B["reuss"])
        elif nm == "bred":
            if use_bred and B["g"]:
                vals.append(B["bred"])
        else:
            vals.append(B[nm])
    return min(vals)


def bb(region, T, ubf, minw=Fr(1, 2 ** 24), cap=2_000_000, record=None):
    """Bisect both coordinates.  CERTIFIED iff every leaf box has ub <= T.
    If record is a list, accepted leaves (al, ah, bl, bh, ub) are appended to it."""
    (al, ah), (bl, bh) = region
    stack = [(al, ah, bl, bh)]
    nodes = 0
    worst = None
    while stack:
        al, ah, bl, bh = stack.pop()
        nodes += 1
        u = ubf(al, ah, bl, bh)
        if u <= T:
            worst = u if worst is None or u > worst else worst
            if record is not None:
                record.append((al, ah, bl, bh, u))
            continue
        if ah - al < minw and bh - bl < minw:
            return ("FAILED", nodes, (al, bl), u)
        am, bm = (al + ah) / 2, (bl + bh) / 2
        stack += [(al, am, bl, bm), (am, ah, bl, bm), (al, am, bm, bh), (am, ah, bm, bh)]
        if nodes > cap:
            return ("CAP", nodes, None, None)
    return ("CERTIFIED", nodes, worst, None)


def show(tag, T, r, expect):
    st, nodes, x, u = r
    ok = (st == expect)
    if st == "CERTIFIED":
        extra = "worst leaf bound=%s (=%.10f)" % (x, float(x))
    elif st == "FAILED":
        extra = "near=(%.6f, %.6f) bound=%.12f" % (float(x[0]), float(x[1]), float(u))
    else:
        extra = ""
    print("%-10s T=%-22s %-9s nodes=%-7d %s  [%s]" % (tag, T, st, nodes, extra, "OK" if ok else "UNEXPECTED"))
    return ok

# ---------------- soundness self-test ----------------
TERMS = ["s", "t", "hb1", "hb2", "reuss", "bred"]


def sample_points(al, ah, bl, bh):
    """16 exact rational points: the 4x4 grid with steps (ah-al)/3, (bh-bl)/3,
    which contains the 4 corners, points on every edge and 4 interior points."""
    return [(al + (ah - al) * i / 3, bl + (bh - bl) * j / 3) for i in range(4) for j in range(4)]


def term_violations(al, ah, bl, bh):
    """Each box bound of box_terms must dominate the exact term at every sample point
    (independently of any gate)."""
    B = box_terms(al, ah, bl, bh)
    bad = []
    for a, b in sample_points(al, ah, bl, bh):
        T = terms_point(a, b)
        for k in TERMS:
            if T[k] > B[k]:
                bad.append((k, a, b, T[k], B[k]))
        # the decoupled H1/H2 box bounds used by the LOOSE runs
        hb1 = bh + (1 - 3 * al) / 2 + max(Z, ah - 3 * bl) / 2
        hb2 = ah + (1 - 3 * bl) / 2 + max(Z, bh - 3 * al) / 2
        if T["hb1"] > hb1 or T["hb2"] > hb2:
            bad.append(("loose-hb", a, b, None, None))
    return bad


def leaf_violations(leaves, point_f):
    """For every accepted leaf, the exact functional at each sample point must be at
    most the box bound that was accepted, and every term bound must be valid."""
    bad = []
    for al, ah, bl, bh, u in leaves:
        for a, b in sample_points(al, ah, bl, bh):
            v = point_f(a, b)
            if v > u:
                bad.append(("phi", a, b, v, u))
        bad += term_violations(al, ah, bl, bh)
    return bad


def random_boxes(n, seed=20260930):
    import random
    rng = random.Random(seed)
    third = Fr(1, 3)
    out = [(Fr(1, 10), Fr(3, 20), Fr(1, 10), Fr(3, 20))]   # the review's counterexample box
    for _ in range(n):
        if rng.random() < 0.5:
            k = rng.randint(1, 14)
            q = 3 * 2 ** k
            i, j = rng.randrange(2 ** k), rng.randrange(2 ** k)   # al, bl in [0, 1/3)
            wi, wj = rng.randint(1, 4), rng.randint(1, 4)
            al, bl = Fr(i, q), Fr(j, q)
            ah, bh = min(Fr(i + wi, q), third), min(Fr(j + wj, q), third)
        else:
            d = rng.choice([97, 1000, 3 * 1024, 7919])
            x1, x2 = sorted(rng.sample(range(0, d // 3 + 1), 2))
            y1, y2 = sorted(rng.sample(range(0, d // 3 + 1), 2))
            al, ah, bl, bh = Fr(x1, d), Fr(x2, d), Fr(y1, d), Fr(y2, d)
        assert Z <= al < ah <= third and Z <= bl < bh <= third
        out.append((al, ah, bl, bh))
    return out


def selftest():
    global MUTANT
    ok_all = True
    print("== SELFTEST: box bounds dominate exact values (accepted leaves, 16 points each) ==")
    sq = ((Z, Fr(1, 3)), (Z, Fr(1, 3)))
    strip = ((Z, FLOOR), (Z, Fr(1, 3)))
    intr = ((FLOOR, Fr(1, 3)), (FLOOR, Fr(1, 3)))

    def p_full_B0(a, b):
        T = terms_point(a, b)
        vals = [T["s"], T["t"], T["hb1"], T["hb2"]]
        if T["g0"]:
            vals += [T["reuss"], T["bred"]]
        return min(vals)

    def f_full_B0(al, ah, bl, bh):
        B = box_terms(al, ah, bl, bh)
        vals = [B["s"], B["t"], B["hb1"], B["hb2"]]
        if B["g0"]:
            vals += [B["reuss"], B["bred"]]
        return min(vals)

    runs = [
        ("STRIP", strip, Q, lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, only=["s", "hb2", "reuss"]),
         lambda a, b: phi_point(a, b, only=["s", "hb2", "reuss"])),
        ("FULL", sq, Q, lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, reuss_gate="G0"),
         lambda a, b: phi_point(a, b, reuss_gate="G0")),
        ("FULL_B0", sq, Q, f_full_B0, p_full_B0),
        ("INT", intr, Fr(2476, 10000), lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, reuss_gate="G"),
         lambda a, b: phi_point(a, b, reuss_gate="G")),
    ]
    for name, reg, T, ubf, pf in runs:
        leaves = []
        r = bb(reg, T, ubf, record=leaves)
        bad = leaf_violations(leaves, pf)
        ok = r[0] == "CERTIFIED" and not bad
        print("   %-8s %s nodes=%-5d accepted leaves=%-5d points checked=%-6d violations=%d  [%s]"
              % (name, r[0], r[1], len(leaves), 16 * len(leaves), len(bad), "OK" if ok else "FAIL"))
        ok_all &= ok
    boxes = random_boxes(4000)
    nbad = sum(1 for bx in boxes if term_violations(*bx))
    ok = nbad == 0
    print("   RANDOM   %d boxes (incl. [1/10,3/20]^2), all six term bounds and loose H1/H2 at 16 points each:"
          " boxes with a violation=%d  [%s]" % (len(boxes), nbad, "OK" if ok else "FAIL"))
    ok_all &= ok
    # mutation test: the reversed endpoint choices must be detected
    MUTANT = True
    try:
        nbad_m = sum(1 for bx in boxes if term_violations(*bx))
        leaves = []
        bb(sq, Q, lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, reuss_gate="G0"), record=leaves)
        lbad_m = leaf_violations(leaves, lambda a, b: phi_point(a, b, reuss_gate="G0"))
    finally:
        MUTANT = False
    B = box_terms(Fr(1, 10), Fr(3, 20), Fr(1, 10), Fr(3, 20))
    ok = nbad_m > 0 and len(lbad_m) > 0
    print("   MUTANT   reversed endpoint choices: random boxes with a violation=%d, FULL leaf violations=%d"
          " (must both be > 0)  [%s]" % (nbad_m, len(lbad_m), "OK" if ok else "FAIL"))
    ok_all &= ok
    v = phi_point(Fr(3, 20), Fr(3, 20))
    ok = v == Fr(1531, 6400) and phi_box(Fr(1, 10), Fr(3, 20), Fr(1, 10), Fr(3, 20)) >= v
    print("   review box [1/10,3/20]^2: Phi2#(3/20,3/20)=%s <= corrected phi_box=%s  [%s]"
          % (v, phi_box(Fr(1, 10), Fr(3, 20), Fr(1, 10), Fr(3, 20)), "OK" if ok else "FAIL"))
    ok_all &= ok
    return ok_all


def main():
    global FLOOR
    allok = True
    third = Fr(1, 3)

    # ---------------- ARITH ----------------
    print("== ARITH: corner (a,b)=(0,1/4) ==")
    T = terms_point(Z, Q)
    for k in ["s", "t", "hb1", "hb2", "reuss", "bred"]:
        print("   %-6s = %-12s = %.6f" % (k, T[k], float(T[k])))
    chk = [
        ("m(1/4) = 45/256", m_of(Q) == Fr(45, 256)),
        ("PELL(0,1/4)=HB2(0,1/4)=REUSS(0,1/4)=1/4", T["s"] == Q and T["hb2"] == Q and T["reuss"] == Q),
        ("BRED(0,1/4) = 673/2560 > 1/4", T["bred"] == Fr(673, 2560) and T["bred"] > Q),
        ("Phi2#(0,1/4) = 1/4 exactly", phi_point(Z, Q) == Q),
        ("max_s m(s) = m(1/3) = 3/16", m_of(third) == Fr(3, 16)),
        ("strip lemma: (13/50 + 3/16)/2 = 179/800 < 1/4", (Fr(13, 50) + Fr(3, 16)) / 2 == Fr(179, 800) and Fr(179, 800) < Q),
        ("strip lemma: a<=1/100, s>1/4 => b>1/4-1/100 >= 3/100 >= 3a", Q - FLOOR >= 3 * FLOOR),
        ("strip lemma: s<=13/50 => t>=1-39/100=61/100>=1/10", 1 - Fr(3, 2) * Fr(13, 50) == Fr(61, 100)),
        ("strip lemma works up to a<=1/16: 1/4+1/16+3/16 = 1/2", Q + Fr(1, 16) + Fr(3, 16) == Fr(1, 2)),
        ("old strip value 1/4+a/4 at a=1/100 is 101/400", Q + FLOOR / 4 == Fr(101, 400)),
        ("REUSS alone at a=1/6,b=7/30 (s=t=2/5) = 29/100", terms_point(Fr(1, 6), Fr(7, 30))["reuss"] == Fr(29, 100)),
    ]
    for nm, ok in chk:
        print("   %-62s %s" % (nm, "OK" if ok else "FAIL"))
        allok &= ok

    # ---------------- STRIP ----------------
    print("== STRIP: [0,1/100]x[0,1/3] ==")
    strip = ((Z, FLOOR), (Z, third))
    f_strip = lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, only=["s", "hb2", "reuss"])
    f_strip_noR = lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, only=["s", "hb2"])
    allok &= show("STRIP", "1/4", bb(strip, Q, f_strip), "CERTIFIED")
    allok &= show("STRIP_CTL", "1/4", bb(strip, Q, f_strip_noR, minw=Fr(1, 2 ** 16)), "FAILED")
    allok &= show("STRIP_CTL", "1/4-1e-6", bb(strip, Q - Fr(1, 10 ** 6), f_strip), "FAILED")
    # the old elementary strip bound 1/4+a/4 is exact without REUSS:
    a0 = Fr(1, 200); b0 = Q - Fr(3, 4) * a0
    v = phi_point(a0, b0, only=["s", "hb2"])
    ok = (v == Q + a0 / 4)
    print("   min(PELL,HB2) at (1/200, 1/4-3/800) = %s = 1/4+a/4: %s" % (v, "OK" if ok else "FAIL")); allok &= ok
    v2 = phi_point(a0, b0, only=["s", "hb2", "reuss"])
    ok = v2 < Q
    print("   ... with REUSS: %s (=%.6f) < 1/4: %s" % (v2, float(v2), "OK" if ok else "FAIL")); allok &= ok

    # ---------------- FULL ----------------
    print("== FULL: Phi_2# on [0,1/3]^2 (REUSS gated by s,t>=1/10 only; BRED by paper gate G) ==")
    sq = ((Z, third), (Z, third))
    f_full = lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, reuss_gate="G0")
    f_paper = lambda al, ah, bl, bh: phi_box(al, ah, bl, bh, reuss_gate="G")
    allok &= show("FULL", "1/4", bb(sq, Q, f_full), "CERTIFIED")
    allok &= show("FULL_CTL1", "1/4-1e-6", bb(sq, Q - Fr(1, 10 ** 6), f_full), "FAILED")
    allok &= show("FULL_CTL2", "1/4 (paper gate)", bb(sq, Q, f_paper, minw=Fr(1, 2 ** 16)), "FAILED")
    w = phi_point(Fr(1, 200), Q - Fr(3, 800), reuss_gate="G")
    ok = w == Fr(201, 800)
    print("   exact witness for FULL_CTL2: Phi_2(1/200, 1/4-3/800) = %s > 1/4  [%s]" % (w, "OK" if ok else "FAIL"))
    allok &= ok
    # variant: BRED also without floor (Theorem 5.4 needs only s,t>=c)
    def f_full_nofloorB(al, ah, bl, bh):
        B = box_terms(al, ah, bl, bh)
        vals = [B["s"], B["t"], B["hb1"], B["hb2"]]
        if B["g0"]:
            vals += [B["reuss"], B["bred"]]
        return min(vals)
    allok &= show("FULL_B0", "1/4", bb(sq, Q, f_full_nofloorB), "CERTIFIED")

    # ---------------- LOOSE: paper's decoupled H1/H2 box bound, no floor ----------------
    print("== LOOSE: no floor (REUSS, BRED gated by s,t>=1/10), paper's decoupled H1/H2 box bounds ==")
    def f_loose(al, ah, bl, bh):
        B = box_terms(al, ah, bl, bh)
        hb1 = bh + (1 - 3 * al) / 2 + max(Z, ah - 3 * bl) / 2
        hb2 = ah + (1 - 3 * bl) / 2 + max(Z, bh - 3 * al) / 2
        vals = [B["s"], B["t"], hb1, hb2]
        if B["g0"]:
            vals += [B["reuss"], B["bred"]]
        return min(vals)
    for T, exp in [(Fr(251, 1000), "CERTIFIED"), (Fr(2501, 10000), "CERTIFIED"), (Fr(25001, 100000), "CERTIFIED"),
                   (Fr(250001, 1000000), "CERTIFIED"), (Q, "FAILED")]:
        allok &= show("LOOSE", str(T), bb(sq, T, f_loose, minw=Fr(1, 2 ** 22)), exp)
    print("   (with the vertex-wise H1/H2 bound the same functional certifies exactly 1/4: run FULL_B0)")

    # ---------------- INT (reproduce paper K2_INT) ----------------
    print("== INT: paper Phi_2 on [1/100,1/3]^2 ==")
    intr = ((FLOOR, third), (FLOOR, third))
    allok &= show("INT", "0.2476", bb(intr, Fr(2476, 10000), f_paper), "CERTIFIED")
    allok &= show("INT_CTL", "0.2474", bb(intr, Fr(2474, 10000), f_paper), "FAILED")
    allok &= show("INT", "1/4", bb(intr, Q, f_paper), "CERTIFIED")

    # ---------------- FLOOR: sup of Phi_2 on [H,1/3]^2 with floor H ----------------
    print("== FLOOR: sup of Phi_2(floor H) on [H,1/3]^2, expected 1/4 - H/4; strip (PELL,HB2 only) sup 1/4 + H/4 ==")
    saved = FLOOR
    for H in [Fr(1, 50), Fr(1, 100), Fr(1, 400), Fr(1, 1000)]:
        FLOOR = H
        reg = ((H, third), (H, third))
        pred = Q - H / 4
        eta = Fr(1, 10 ** 5)
        r_hi = bb(reg, pred + eta, f_paper)
        r_lo = bb(reg, pred - eta, f_paper)
        # the maximiser on the floor edge: (H, 1/4 - H/4)
        vpt = phi_point(H, Q - H / 4, reuss_gate="G")
        ok = r_hi[0] == "CERTIFIED" and r_lo[0] == "FAILED" and vpt == pred
        print("   H=%-7s pred=%-10s certify(pred+1e-5)=%s[%d]  fail(pred-1e-5)=%s near=(%.5f,%.5f)  Phi_2(H,1/4-H/4)=%s  [%s]"
              % (H, pred, r_hi[0], r_hi[1], r_lo[0], float(r_lo[2][0]) if r_lo[2] else -1,
                 float(r_lo[2][1]) if r_lo[2] else -1, vpt, "OK" if ok else "CHECK"))
        allok &= ok
    # away from the corner the functional is smaller: bracket sup Phi_2 on [1/20,1/3]^2
    FLOOR = Fr(1, 20)
    reg = ((FLOOR, third), (FLOOR, third))
    lo, hi = Fr(2, 10), Q
    while hi - lo > Fr(1, 10 ** 5):
        mid = (lo + hi) / 2
        if bb(reg, mid, f_paper, minw=Fr(1, 2 ** 20))[0] == "CERTIFIED":
            hi = mid
        else:
            lo = mid
    # hi is a certified upper bound for sup Phi_2 on this region.  lo is only the
    # largest target at which the box-bound certification failed: NOT a lower bound.
    # An exact lower bound comes from a pointwise witness (grid search below).
    wit, warg = Fr(-1), None
    for i in range(0, 601):
        for j in range(0, 601):
            a, b = FLOOR + (third - FLOOR) * Fr(i, 600), FLOOR + (third - FLOOR) * Fr(j, 600)
            v = phi_point(a, b, reuss_gate="G")
            if v > wit:
                wit, warg = v, (a, b)
    print("   Phi_2 on [1/20,1/3]^2 (floor 1/20): certified sup <= %.6f; certification fails at target %.6f"
          " (a threshold of the box bounds, not a lower bound); exact witness Phi_2(%.5f,%.5f) = %.6f, so sup >= %.6f"
          % (float(hi), float(lo), float(warg[0]), float(warg[1]), float(wit), float(wit)))
    ok = wit <= hi
    allok &= ok
    FLOOR = saved

    # ---------------- GRID ----------------
    print("== GRID: exact pointwise Phi_2# on {i/(3N)}^2, N=600 ==")
    N = 600
    best = Fr(-1); arg = []
    for i in range(N + 1):
        a = Fr(i, 3 * N)
        for j in range(N + 1):
            b = Fr(j, 3 * N)
            v = phi_point(a, b)
            if v > best:
                best, arg = v, [(a, b)]
            elif v == best:
                arg.append((a, b))
    ok = best == Q and sorted(arg) == [(Z, Q), (Q, Z)]
    print("   max = %s attained at %s  [%s]" % (best, arg, "OK" if ok else "CHECK"))
    allok &= ok
    # second-largest value away from the corners (distance >= 1/100 in a and b)
    best2 = Fr(-1); arg2 = None
    for i in range(N + 1):
        a = Fr(i, 3 * N)
        for j in range(N + 1):
            b = Fr(j, 3 * N)
            if a < FLOOR or b < FLOOR:
                continue
            v = phi_point(a, b)
            if v > best2:
                best2, arg2 = v, (a, b)
    print("   max on grid of [1/100,1/3]^2 = %s (=%.6f) at (%s, %s)" % (best2, float(best2), arg2[0], arg2[1]))
    print("   ridge near the corner: sup_b Phi_2#(a,b) for fixed a (b on grid 1/(4*10^5)):")
    for a in [Fr(1, 10 ** 4), Fr(1, 1000), Fr(1, 200), Fr(1, 100), Fr(1, 50)]:
        pred = Q - a / 4
        # candidate maximiser b = 1/4 - a/4 and neighbours
        bs = [pred + Fr(k, 4 * 10 ** 5) for k in range(-400, 401)]
        vals = [(phi_point(a, b), b) for b in bs]
        mv, mb = max(vals)
        ok = mv == pred and mb == pred
        print("     a=%-7s max=%s (=%.7f) at b=%s  pred 1/4-a/4  [%s]" % (a, mv, float(mv), mb, "OK" if ok else "CHECK"))
        allok &= ok
    # binding terms along the ridge
    a = Fr(1, 1000); b = Q - a / 4
    T = terms_point(a, b)
    print("   terms at (1/1000, 1/4-1/4000): " + ", ".join("%s=%.6f" % (k, float(T[k])) for k in ["s", "t", "hb1", "hb2", "reuss", "bred"]))

    allok &= selftest()

    print("SUMMARY:", "ALL AS EXPECTED" if allok else "SOMETHING UNEXPECTED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
