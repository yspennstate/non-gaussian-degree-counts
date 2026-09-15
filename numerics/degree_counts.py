"""
Exact computations for the lacunary subcritical offspring law and the first
stage of the critical construction.

Part A: the subcritical law pi (stages, integrality, moments, the constants
        nu, sigma^2, a_*, v_* with rigorous tail enclosures).
Part B: the exact law of N_1(T_n) at n = n_1 = 256, computed two ways
        (Lukasiewicz-path dynamic programming over the tree itself, and the
        conditioned multinomial formula), and at n = n_2 = 2^32 by the
        conditioned multinomial formula, with the mixture weights and the
        conditional moments compared to the limit.
Part C: the first stage of the critical construction: the gates at the base
        law Q^(0) = (5/8, 1/4, 1/8), scanned over n = 2^l.

Run:  python degree_counts.py     (writes results.md and ../figures/thevenin_n2_law.pdf)
"""
from fractions import Fraction as F
from math import isqrt
import mpmath as mp
import numpy as np
from scipy.special import gammaln
from scipy.stats import norm

mp.mp.dps = 60
out = []


def P(s=""):
    print(s)
    out.append(s)


# ---------------------------------------------------------------- Part A
q = F(1, 4)
R = 4                       # stages kept exactly
n = [None]; d = [F(3, 4)]; H = [None]; Lm = [None]; Lp = [None]; p = [None]
nr = 256
for r in range(1, R + 1):
    n.append(nr)
    s = isqrt(nr)
    assert s * s == nr
    Hr = d[r - 1] * nr
    assert Hr.denominator == 1
    H.append(int(Hr)); Lm.append(int(Hr) - s); Lp.append(int(Hr) + s)
    p.append(F(1, nr ** 4))
    d.append(d[r - 1] * (1 - 2 * F(1, nr ** 3)))
    nr = nr ** 4

P("# Results of degree_counts.py\n")
P("## A. The subcritical law\n")
P("| r | n_r | H_r | L_r^- | L_r^+ | p_r |")
P("|---|---|---|---|---|---|")
for r in range(1, 4):
    P(f"| {r} | 2^{n[r].bit_length()-1} | {H[r]} | {Lm[r]} | {Lp[r]} | 2^-{(n[r]**4).bit_length()-1} |")
for r in range(1, R + 1):
    assert Lm[r] % 16 == 0 and Lp[r] % 16 == 0
    assert 2 * Lm[r] > n[r] - 1                      # at most one current atom
    if r < R:
        assert Lm[r + 1] > n[r]                      # later atoms too large
P("\nAll H_r and L_r^+- are integers divisible by 16; 2 L_r^- > n_r - 1 and L_{r+1}^- > n_r for r <= 4.")

S0 = sum(2 * p[r] for r in range(1, R + 1))
S1 = sum(p[r] * (Lm[r] + Lp[r]) for r in range(1, R + 1))
S2 = sum(p[r] * (Lm[r] ** 2 + Lp[r] ** 2) for r in range(1, R + 1))
nR1 = n[R] ** 4
# tails beyond stage R (L_r^+ < n_r, p_r = n_r^{-4}, stage ratio <= 2^-32):
t0 = 4 * F(1, nR1 ** 4); t1 = 2 * F(1, nR1 ** 3); t2 = 4 * F(1, nR1 ** 2)
pi0_lo, pi0_hi = F(3, 4) - S0 - t0, F(3, 4) - S0
nu_lo, nu_hi = q + S1, q + S1 + t1
m2_lo, m2_hi = q + S2, q + S2 + t2
sig_lo = m2_lo - nu_hi ** 2; sig_hi = m2_hi - nu_lo ** 2
gam_lo, gam_hi = q * (1 - nu_hi), q * (1 - nu_lo)
a_lo, a_hi = gam_lo / sig_hi, gam_hi / sig_lo
b = q * (1 - q)
v_lo, v_hi = b - gam_hi ** 2 / sig_lo, b - gam_lo ** 2 / sig_hi


def fl(x):
    return mp.mpf(x.numerator) / x.denominator


def show(name, lo, hi, dig=34):
    P(f"{name} in [{mp.nstr(fl(lo), dig)}, {mp.nstr(fl(hi), dig)}]")


P("")
show("pi_0   ", pi0_lo, pi0_hi); show("nu     ", nu_lo, nu_hi); show("sigma^2", sig_lo, sig_hi)
show("a_*    ", a_lo, a_hi); show("v_*    ", v_lo, v_hi)
P(f"\nExact: nu = 1 - d_inf, d_1 = {d[1]}, d_2 = {d[2]} (as fractions).")
P("Moments: E xi^h finite iff h < 4 (rare part sum_r 2 n_r^(h-4) up to bounded factors).")

# ---------------------------------------------------------------- Part B
pi0 = fl(pi0_lo)                      # differs from pi_0 by < 2^-4096
lpi0, lpi1 = mp.log(pi0), mp.log(mp.mpf(1) / 4)


def lgam(x):
    return mp.loggamma(mp.mpf(x) + 1)


def multinomial_law(nn, stage, amax=45):
    """Log-weights of the configurations with one current atom of sign eps.
    stage 1: no earlier atoms. stage 2: (a2, a3) stage-1 atoms, each < amax."""
    Lcur = {+1: Lp[stage], -1: Lm[stage]}
    res = {}
    lgn = lgam(nn)
    for eps in (+1, -1):
        rows = []
        if stage == 1:
            a1 = nn - 1 - Lcur[eps]; a0 = nn - 1 - a1
            lw = lgn - lgam(a0) - lgam(a1) + a0 * lpi0 + a1 * lpi1 + mp.log(mp.mpf(1) / nn ** 4)
            rows.append((a1, 0, 0, lw))
        else:
            lp1 = mp.log(mp.mpf(1) / n[1] ** 4); lp2 = mp.log(mp.mpf(1) / nn ** 4)
            for a2 in range(0, amax):
                for a3 in range(0, amax):
                    a1 = nn - 1 - Lcur[eps] - Lm[1] * a2 - Lp[1] * a3
                    a0 = nn - 1 - a1 - a2 - a3
                    lw = (lgn - lgam(a0) - lgam(a1) - lgam(a2) - lgam(a3)
                          + a0 * lpi0 + a1 * lpi1 + (a2 + a3) * lp1 + lp2)
                    rows.append((a1, a2, a3, lw))
        res[eps] = rows
    return res


P("\n## B. The law of N_1 at n_1 = 256 and n_2 = 2^32\n")
nn = 256
steps = {0: pi0, 1: mp.mpf(1) / 4, Lm[1]: mp.mpf(1) / nn ** 4, Lp[1]: mp.mpf(1) / nn ** 4}
Hmax = 1 + Lp[1] + 2
cur = {(1, 0): mp.mpf(1)}
for step in range(1, nn + 1):
    nxt = {}
    for (h, o), w in cur.items():
        for k, pk in steps.items():
            h2 = h + k - 1; o2 = o + (1 if k == 1 else 0)
            if step < nn and h2 < 1:
                continue
            if step == nn and h2 != 0:
                continue
            if h2 > Hmax:
                continue
            nxt[(h2, o2)] = nxt.get((h2, o2), mp.mpf(0)) + w * pk
    cur = nxt
dp = {o: w for (h, o), w in cur.items()}
tot = sum(dp.values())
P(f"n = 256, Lukasiewicz DP on the tree: P(|T| = 256) = {mp.nstr(tot, 12)}; support of N_1 = {sorted(dp)}")
for o in sorted(dp):
    P(f"  P(N_1 = {o} | size 256) = {mp.nstr(dp[o]/tot, 12)}")
law1 = multinomial_law(256, 1)
lw0 = lgam(256) - lgam(1) - lgam(255) + 1 * lpi0 + 255 * lpi1
w = {eps: mp.e ** law1[eps][0][3] for eps in law1}; w0 = mp.e ** lw0
tot2 = (w[+1] + w[-1] + w0) / 256
P(f"n = 256, conditioned multinomial formula: P(|T| = 256) = {mp.nstr(tot2, 12)}  (ratio to DP = {mp.nstr(tot2/tot, 20)})")
P(f"  weights: L^+ atom (N_1 = 47): {mp.nstr(w[+1]/(w[+1]+w[-1]+w0), 12)}, L^- atom (N_1 = 79): {mp.nstr(w[-1]/(w[+1]+w[-1]+w0), 12)}, no atom (N_1 = 255): {mp.nstr(w0/(w[+1]+w[-1]+w0), 6)}")

nn = n[2]
law2 = multinomial_law(nn, 2)
sq = mp.sqrt(nn)
P(f"\nn = 2^32: enumeration of one stage-2 atom and (a_2, a_3) stage-1 atoms, a_2, a_3 <= 44.")
tw = {}; mom = {}
for eps in (+1, -1):
    rows = law2[eps]
    m = max(r[3] for r in rows)
    ws = [(r[0], mp.e ** (r[3] - m)) for r in rows]
    Z = sum(wt for _, wt in ws)
    tw[eps] = m + mp.log(Z)
    xs = [(a1 - nn / mp.mpf(4)) / sq for a1, _ in ws]
    mean = sum(x * wt for x, (_, wt) in zip(xs, ws)) / Z
    var = sum((x - mean) ** 2 * wt for x, (_, wt) in zip(xs, ws)) / Z
    mom[eps] = (mean, var)
tot = mp.e ** tw[+1] + mp.e ** tw[-1]
P(f"  mixture weights: P(L^+ | size) = {mp.nstr(mp.e**tw[+1]/tot, 12)}, P(L^- | size) = {mp.nstr(mp.e**tw[-1]/tot, 12)}")
sig = fl(sig_lo)
P(f"  P(|T| = 2^32) = {mp.nstr(tot/nn, 8)};  2 C_sigma n^(-9/2), C_sigma = exp(-1/(2 sigma^2))/sqrt(2 pi sigma^2): "
  f"{mp.nstr(2*mp.e**(-1/(2*sig))/mp.sqrt(2*mp.pi*sig)*mp.mpf(nn)**(-4.5), 8)}")
for eps in (+1, -1):
    lab = "+" if eps > 0 else "-"
    P(f"  given L^{lab}: mean of (N_1 - n/4)/sqrt n = {mp.nstr(mom[eps][0], 10)}, variance = {mp.nstr(mom[eps][1], 8)}  "
      f"(limit: {'-' if eps>0 else '+'}a_* = {mp.nstr(-eps*fl(a_lo), 10)}, v_* = {mp.nstr(fl(v_lo), 8)})")
M = Lp[1]; D = mp.mpf(nn) / 3; V = mp.mpf(1)
P(f"  no-current-atom route: Bernstein bound with D >= n/3, Var <= 1, M = {M}: exp(-{mp.nstr(D**2/(2*(nn*V + M*D/3)), 6)}), against P(|T| = n) = 10^{mp.nstr(mp.log10(tot/nn), 5)}")
cnt = {}
for eps in (+1, -1):
    for a1, a2, a3, lw in law2[eps]:
        j = a2 + a3; cnt[j] = cnt.get(j, mp.mpf(0)) + mp.e ** (lw - tw[+1])
Zc = sum(cnt.values())
P("  P(a_2 + a_3 = j | size) for j = 0..6: " + ", ".join(f"{j}: {mp.nstr(cnt[j]/Zc, 5)}" for j in range(7)))

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    xs = []; ws = []
    for eps in (+1, -1):
        for a1, a2, a3, lw in law2[eps]:
            xs.append(float((a1 - nn / mp.mpf(4)) / sq)); ws.append(float(mp.e ** (lw - mp.log(tot))))
    xs = np.array(xs); ws = np.array(ws)
    fig, ax = plt.subplots(figsize=(5.2, 3.0))
    bins = np.linspace(-1.25, 1.25, 101)
    hist, _ = np.histogram(xs, bins=bins, weights=ws)
    width = bins[1] - bins[0]
    ax.bar((bins[:-1] + bins[1:]) / 2, hist / width, width=width, color="0.25", label=r"exact law at $n=2^{32}$")
    g = np.linspace(-1.25, 1.25, 600)
    ax.plot(g, np.exp(-g ** 2 / (2 * 3 / 16)) / np.sqrt(2 * np.pi * 3 / 16), "k--", lw=1, label=r"$N(0,\,3/16)$")
    ax.set_xlabel(r"$(N_1(T_n)-n/4)/\sqrt{n}$"); ax.set_ylabel("density"); ax.legend(frameon=False, fontsize=8)
    fig.tight_layout(); fig.savefig("../figures/thevenin_n2_law.pdf")
    P("\nFigure written to ../figures/thevenin_n2_law.pdf")
except Exception as e:
    P(f"figure skipped: {e}")

# ---------------------------------------------------------------- Part C
P("\n## C. First stage of the critical construction\n")
mu = F(1, 2); V1 = F(1, 2); Delta = F(1, 2); M1 = 2; eps1 = F(1, 11)
v1 = q * (1 - q) - q * q * Delta * Delta / V1
c1 = mp.e ** (-fl(V1) / (2 * fl(q) ** 2 * fl(Delta) ** 2)) / mp.sqrt(2 * mp.pi * fl(V1))
P(f"Q^(0) = (5/8, 1/4, 1/8): mu_1 = {mu}, V_1 = {V1}, Delta_1 = {Delta}, v_1 = {v1}, c_1 = {mp.nstr(c1, 6)}, eps_1 = 1/11")


def stage1_gates(l):
    nn = 2 ** l; N = nn - 1
    D = 4 * np.sqrt(N)
    res = {}
    for sgn in (+1, -1):
        L = int(np.floor(N * 0.5 + sgn * D)); k = N - L
        bb = np.arange(0, N + 1)
        jj = (k - bb)
        ok = (jj >= 0) & (jj % 2 == 0) & (jj // 2 <= N - bb)
        bb = bb[ok]; j = jj[ok] // 2
        lw = (gammaln(N + 1) - gammaln(bb + 1) - gammaln(N - bb + 1) + bb * np.log(0.25)
              + gammaln(N - bb + 1) - gammaln(j + 1) - gammaln(N - bb - j + 1)
              + j * np.log(0.125) + (N - bb - j) * np.log(0.625))
        m = lw.max(); w = np.exp(lw - m); Z = w.sum()
        PS = np.exp(m) * Z
        G2 = abs(np.sqrt(N) * PS / float(c1) - 1)
        cdf = np.cumsum(w) / Z
        x = (bb - N * 0.25) / np.sqrt(N)
        Gx = norm.cdf((x - (-sgn)) / np.sqrt(float(v1)))
        K = max(np.max(np.abs(cdf - Gx)), np.max(np.abs(np.concatenate(([0.0], cdf[:-1])) - Gx)))
        res[sgn] = (L, k, G2, K, (k - N * 0.5) / np.sqrt(N))
    w1 = float(c1) * nn ** -3 / np.sqrt(N)
    E = (nn * 0.5 - 1) ** 2 / (2 * (nn * 0.5 + 2 * (nn * 0.5 - 1) / 3))
    G1 = (nn >= 2 ** 8) and (M1 <= nn / 22) and (D + 0.5 + 1 <= nn / 22) and (res[-1][0] < res[+1][0])
    G4 = np.exp(-E) < w1 / 11
    G5 = 2 * nn ** -6 < w1 / 11
    return res, G1, G4, G5


P("\n| l | L^- | L^+ | (k^+ - N mu)/sqrt N | G2 rel. err (+ / -) | G3 Kolmogorov (+ / -) | G1 | G4 | G5 | all |")
P("|---|---|---|---|---|---|---|---|---|---|")
first = None
for l in range(10, 25):
    res, G1, G4, G5 = stage1_gates(l)
    g2ok = res[+1][2] < 1 / 11 and res[-1][2] < 1 / 11
    g3ok = res[+1][3] < 1 / 11 and res[-1][3] < 1 / 11
    allok = bool(G1 and G4 and G5 and g2ok and g3ok)
    if allok and first is None:
        first = l
    P(f"| {l} | {res[-1][0]} | {res[+1][0]} | {res[+1][4]:.4f} | {res[+1][2]:.4f} / {res[-1][2]:.4f} | {res[+1][3]:.4f} / {res[-1][3]:.4f} | {bool(G1)} | {bool(G4)} | {bool(G5)} | {allok} |")
P(f"\nFirst power of two passing every stage-1 gate: n_1 = 2^{first}.")
if first:
    res, *_ = stage1_gates(first)
    P(f"At n_1 = 2^{first}: L_1^- = {res[-1][0]}, L_1^+ = {res[+1][0]}, p_1 = 2^-{4*first}, H_1 = 2^{4*first}; gate G1 at stage 2 then needs n_2 >= 4 * 12 * 2^{4*first}.")

open("results.md", "w", encoding="utf-8").write("\n".join(out) + "\n")
