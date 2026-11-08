# Deliverables 3 & 4: Candidate Deterministic Zero-Testing Lemmas, Proofs, and Counterexample Obstructions

## Overview

In this note we address Deliverables 3 and 4 of `idea.txt` (using the status labels **[Lean]**, **[Paper]**, and **[Open]** defined in §4.0):
- **Part I (Proven Deterministic Polynomial-Time Lemmas):** We establish two deterministic polynomial-time zero-testing lemmas covering major subclasses of Order-$\le 4$ LRS:
  1. **Lemma 1 (Two-Root / Repeated-Root Subclass up to Order 4) [Paper: Dobrowolski/Voutier + Yu; Lean deduction]:** Deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$-time zero-testing via **both** a direct Weil-height magnitude cutoff $N_{\text{height}} = O(\|\boldsymbol{u}\|)$ (which requires no Baker bound at all) and a single prime-power modulus $p^\nu$ (using Yu's $p$-adic Baker bound). This settles deterministic polynomial-time Skolem for **all order-$d \le 2$ LRS** and **all order-$3$ and order-$4$ LRS with at most $2$ distinct characteristic roots**.
  2. **Lemma 2 (Archimedean Equi-Dominant & Well-Separated MSTV Subclasses at Order $d \le 4$) [Paper: Baker–Matveev + Beukers–Tijdeman; Lean certification]:** Deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$-time zero-testing via **dyadic ball / interval matrix exponentiation** at bit-precision $P = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$, whenever the dominant-root separation condition $n \log(|\lambda_1|/|\lambda_{k+1}|) \ge P(\|\boldsymbol{u}\|, \log n)$ holds (including all exact equi-dominant instances where $B(n) \equiv 0$).
- **Part II (Counterexamples & Obstructions to Plausible Modulus-Selection Rules) [Lean]:** We formulate two natural deterministic modulus-selection / $p$-adic precision rules and prove **explicit counterexample obstructions** showing why they fail on general Order-$3$ and Order-$4$ instances:
  1. **Obstruction 1 (Pisano-Period Defeat of Oblivious Polynomial Modulus Sets) [Lean]:** Any rule that tests $u_n \equiv 0 \pmod m$ over a polynomial-bit-length set of moduli $S$ coprime to $a_0$ (without enforcing $p$-adic disc uniqueness $N < M p^R$) is defeated by an explicit binary index $n = \mathrm{lcm}_{m \in S} \mathrm{ord}_m(A)$ of bit-length $\le d^2 \sum_{m \in S} \log_2 m$ where $u_n \ne 0$ yet $u_n \equiv 0 \pmod m$ for all $m \in S$.
  2. **Obstruction 2 ($p$-adic Ghost-Root Defeat of Single-Prime and Multi-Prime Hensel Filtering at Order $d \ge 3$) [Lean]:** For order $d \ge 3$ with $\ge 3$ distinct roots, the Mahler interpolant $F_\ell(x)$ can possess a non-integer $p$-adic root $x_0 \in \mathbb{Z}_p \setminus \mathbb{N}$ ("ghost root"). Truncating $x_0$ at any depth $R$ yields a valid `ZeroSearch` candidate $n_R = M(x_0 \bmod p^R) + \ell$ with $v_p(u_{n_R}) \ge V(F_\ell) + R$ and $u_{n_R} \ne 0$.
- **Part III (The Archimedean Transition Window left by Lemmas 1 & 2):** We isolate the regime at order $d \in \{3, 4\}$ where neither Lemma 1 nor Lemma 2 immediately runs in polynomial time, namely when $s \in \{3, 4\}$ roots have distinct but exponentially close Archimedean moduli ($0 < \delta_\infty \le 2^{-\Omega(\|\boldsymbol{u}\|)}$).
- **Part IV (Revised: Zero Bounds from a Global–Local Dichotomy):** Attacking the transition window of Part III via slope normalization and root-power ratios yields explicit polynomial **bounds on the largest zero** ($u_k \ne 0$ for $k \ge B(\boldsymbol{u}) = \mathrm{poly}(\|\boldsymbol{u}\|)$) across all covered branches:
  - The unit-root branch $k_q = 1$ (Theorems 5, 6, and general order-$d$) and the slope-normalization identity $S^{d-1} v_k = S^k z_k$ are proved in **Lean 4 with no external hypotheses** (`Skolem/UnitRootDominance.lean`) and work for unfactored composite $q$.
  - The unit branch $D = 1$ at Order 3 (Theorem 3′) and at Order 4 with $k_\infty \le 2$ give polynomial zero bounds on paper (**[Paper: Smyth + Baker]**), as does $k_q = 2$ at small primes $q \le \mathrm{poly}(\|\boldsymbol{u}\|)$ (**[Paper: Yu]**), with the algebraic deductions formalized in `Skolem/DeterministicZeroTest.lean`.
  - The remaining order-3/4 obstacle is narrowed to a single residual class (**[Open]**, §4.6): three-term clusters with no 1- or 2-term split at any usable place.

---

## Part I: Proven Deterministic Zero-Testing Lemmas

### Lemma 1 (Deterministic Zero-Testing for LRS with at Most 2 Distinct Characteristic Roots)

> **Lemma 1 (Statement):**
> Let $\boldsymbol{u} = \langle u_n \rangle_{n=0}^\infty$ be an integer LRS of fixed order $d \le 4$ whose characteristic polynomial $g(x) = x^d - a_{d-1}x^{d-1} - \dots - a_0$ ($a_0 \ne 0$) has **at most $s \le 2$ distinct roots** in $\overline{\mathbb{Q}}$ (this includes all LRS of order $d \le 2$, and all LRS of order $d \in \{3, 4\}$ with root multiplicity partitions $(3), (2,1), (4), (3,1), (2,2)$).
>
> 1. **(Unbounded Skolem via Weil Heights — Purely Algebraic, No Baker Bound Required):**
>    After decomposing $\boldsymbol{u}$ into $L(d) \le 12$ subsequences $v_n^{(r)} = u_{L(d)n + r}$ ($0 \le r < L(d)$), each subsequence is either identically zero (checked on $0 \le n < d$) or non-degenerate with every zero satisfying a **polynomial magnitude bound**
>    $$n \le N_{\text{height}}(\boldsymbol{u}) = \mathrm{poly}(\|\boldsymbol{u}\|).$$
>    Hence the unrestricted Skolem Problem (and the function problem of finding all zeros) for this class is solvable in **deterministic $\mathrm{poly}(\|\boldsymbol{u}\|)$ time** by direct exact evaluation up to $N_{\text{height}}(\boldsymbol{u})$.
>
> 2. **(Bounded Skolem Candidate Test via a Single Prime Power $p^\nu$):**
>    Given any binary candidate index $n \in \mathbb{N}$, let $p \ge d+2$ be the smallest prime not dividing $a_0$ (so $p = \mathrm{poly}(\|\boldsymbol{u}\|)$). If $\boldsymbol{u}$ is non-degenerate, there exists an explicit polynomial precision bound
>    $$\nu(\boldsymbol{u}, n) = C_0(\|\boldsymbol{u}\|) \cdot (\log(n + 3))^2 = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$$
>    such that for the single modulus $m = p^{\nu(\boldsymbol{u}, n)}$,
>    $$u_n = 0 \quad \Longleftrightarrow \quad \alpha A^n \beta \equiv 0 \pmod{p^{\nu(\boldsymbol{u}, n)}}.$$
>    Consequently, testing $u_n = 0$ via modular matrix powering $\alpha A^n \beta \pmod{p^\nu}$ runs in **deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ time**.

#### Proof of Lemma 1

**Part 1 (Weil-Height Bound):**
Since $g(x) \in \mathbb{Z}[x]$ has degree $d \le 4$, its roots $\lambda_i$ have degree at most $4$ over $\mathbb{Q}$, so any ratio $\gamma = \lambda_1 / \lambda_2$ lies in a number field $K = \mathbb{Q}(\lambda_1, \lambda_2)$ of degree $D = [K:\mathbb{Q}] \le 12$. If $\gamma$ is a root of unity, then $\varphi(\mathrm{ord}(\gamma)) \le 12$, so $\mathrm{ord}(\gamma)$ divides $L = \mathrm{lcm}\{m : \varphi(m) \le 12\} = 2^3 \cdot 3^2 \cdot 5 \cdot 7 \cdot 13$. (In fact, checking whether any ratio of roots is a root of unity and passing to $u_{Ln+r}$ takes $\mathrm{poly}(\|\boldsymbol{u}\|)$ time.)

Now assume $u_n$ is non-degenerate with $s \le 2$ distinct roots:
- **If $s = 1$:** $u_n = P_1(n) \lambda_1^n$ with $\deg P_1 \le d-1$. Since $\lambda_1 \ne 0$, $u_n = 0 \iff P_1(n) = 0$. The integer/algebraic polynomial $P_1(x)$ has coefficients of bit-size $O(\|\boldsymbol{u}\|)$, so any integer root $n$ divides the constant term of the primitive form of $P_1$ and satisfies $n \le 2^{O(\|\boldsymbol{u}\|)}$; better yet, we can evaluate the univariate polynomial $P_1(n) = 0$ at any binary $n$ (or find its $\le d-1$ rational roots) in deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ time!
- **If $s = 2$:** Write $u_n = P_1(n) \lambda_1^n + P_2(n) \lambda_2^n$ with $\deg P_1 + \deg P_2 \le d - 2 \le 2$.
  Suppose $u_n = 0$ for some $n \in \mathbb{N}$. If $P_1(n) = 0$, then $P_2(n)\lambda_2^n = 0 \implies P_2(n) = 0$, which is checked directly in $\mathrm{poly}(\|\boldsymbol{u}\|)$ time. Otherwise $P_1(n) \ne 0$ and $P_2(n) \ne 0$, and
  $$\left(\frac{\lambda_1}{\lambda_2}\right)^n = -\frac{P_2(n)}{P_1(n)}.$$
  Applying the absolute logarithmic Weil height $h(\cdot)$ (Section 2.1 of the 2026 Survey) to both sides yields:
  $$n \cdot h\!\left(\frac{\lambda_1}{\lambda_2}\right) = h\!\left(\left(\frac{\lambda_1}{\lambda_2}\right)^n\right) = h\!\left(-\frac{P_2(n)}{P_1(n)}\right) \le C_1 \|\boldsymbol{u}\| + (d-2) \log(n + 1).$$
  Because $\boldsymbol{u}$ is non-degenerate, $\gamma = \lambda_1 / \lambda_2$ is neither $0$ nor a root of unity, and $\deg(\gamma) \le 12$. By Dobrowolski's theorem (or Voutier's explicit lower bound $h(\gamma) \ge \frac{1}{4D}\left(\frac{\log\log(3D)}{\log(3D)}\right)^3 > 10^{-4}$ for $D \le 12$), $h(\lambda_1/\lambda_2) \ge c_{12} > 0$ is bounded below by an absolute positive constant. Thus
  $$c_{12} \, n \le C_1 \|\boldsymbol{u}\| + 2 \log(n + 1) \implies n \le N_{\text{height}}(\boldsymbol{u}) = O(\|\boldsymbol{u}\|).$$
  Since $N_{\text{height}}(\boldsymbol{u})$ is bounded by a linear function of $\|\boldsymbol{u}\|$, we can compute $u_0, u_1, \dots, u_{N_{\text{height}}}$ exactly in deterministic $\mathrm{poly}(\|\boldsymbol{u}\|)$ time!

**Part 2 (Single Prime-Power Test via Yu's $p$-adic Baker Theorem):**
For a given binary integer $n \in \mathbb{N}$ where $u_n \ne 0$, let $\mathfrak{p}$ be a prime ideal of $\mathcal{O}_K$ lying above $p$. Since $p \nmid a_0$ and $\prod_{i=1}^s \lambda_i^{e_i} = (-1)^{d-1} a_0$, each $\lambda_i$ is a $\mathfrak{p}$-adic unit ($v_{\mathfrak{p}}(\lambda_i) = 0$). Writing
$$u_n = P_1(n) \lambda_1^n \left( \left(-\frac{P_2(n)}{P_1(n)}\right)^1 \left(\frac{\lambda_2}{\lambda_1}\right)^n - 1 \right),$$
Theorem 8 of the Survey (Kunrui Yu's $p$-adic Baker bound) gives:
$$v_p(u_n) \le v_{\mathfrak{p}}(u_n) \le v_{\mathfrak{p}}(P_1(n)) + C(d, p) \, h(\lambda_2/\lambda_1) \max\{h(P_2(n)/P_1(n)), \log p\} \log(\max(n, 3)) = O(\mathrm{poly}(\|\boldsymbol{u}\|) (\log n)^2).$$
Hence taking $\nu = \nu(\boldsymbol{u}, n)$ strictly larger than this polynomial bound guarantees $u_n \ne 0 \implies v_p(u_n) < \nu \implies u_n \not\equiv 0 \pmod{p^\nu}$. $\blacksquare$

---

### Lemma 2 (Deterministic Dyadic Interval Matrix Exponentiation for Archimedean MSTV Candidates)

> **Lemma 2 (Statement):**
> Let $\boldsymbol{u}$ be a non-degenerate integer LRS of order $d \le 4$ with characteristic roots $\lambda_1, \dots, \lambda_s \in \mathbb{C}$ ordered by modulus $|\lambda_1| = \dots = |\lambda_k| > |\lambda_{k+1}| \ge \dots \ge |\lambda_s|$, where $k \le 3$ (this covers **all** non-degenerate LRS of order $d \le 3$, and all non-degenerate LRS of order $d = 4$ with at most $3$ dominant roots in $\mathbb{C}$).
> Write $u_n = A(n) + B(n)$ where $A(n) = \sum_{j=1}^k Q_j(n) \lambda_j^n$ is the dominant part and $B(n) = \sum_{j=k+1}^s Q_j(n) \lambda_j^n$ is the subdominant tail ($B(n) \equiv 0$ if $k = s$).
>
> Then there exists an explicit polynomial precision function $P(\|\boldsymbol{u}\|, \log n) = O(\mathrm{poly}(\|\boldsymbol{u}\|) (\log n)^2)$ such that for any candidate index $n$ satisfying the dominance-separation condition
> $$n \cdot \log\!\left(\frac{|\lambda_1|}{|\lambda_{k+1}|}\right) \ge P(\|\boldsymbol{u}\|, \log n) \qquad (\text{which holds for all } n \ge 1 \text{ whenever } k = s, \text{ i.e. } B(n) \equiv 0),$$
> evaluating $u_n = \alpha A^n \beta$ via repeated squaring in **$2P(\|\boldsymbol{u}\|, \log n)$-bit dyadic ball arithmetic** deterministically decides whether $u_n = 0$ in **$\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ bit operations**.

#### Proof of Lemma 2

By the Baker–Matveev theorem and the Beukers–Tijdeman circle-intersection argument for $k \le 3$ dominant roots (Equation (9), Section 5.3 of the 2026 Survey), there is an effective constant $C_{\text{Baker}} = \mathrm{poly}(\|\boldsymbol{u}\|)$ (since $d \le 4$ is fixed) such that for every $n$ with $A(n) \ne 0$:
$$|A(n)| \ge |\lambda_1|^n \cdot 2^{-C_{\text{Baker}} (\log(n+2))^2},$$
while the subdominant tail satisfies $|B(n)| \le 2^{C_0 \|\boldsymbol{u}\| + d \log(n+2)} |\lambda_{k+1}|^n$.
When the dominance-separation hypothesis holds with $P(\|\boldsymbol{u}\|, \log n) = C_{\text{Baker}}(\log(n+2))^2 + C_0 \|\boldsymbol{u}\| + d \log(n+2) + 2$, we have $|B(n)| \le \frac{1}{2} |\lambda_1|^n 2^{-C_{\text{Baker}}(\log(n+2))^2}$, and therefore:
- Either $A(n) = 0$ and $B(n) = 0$ (which for $B(n) \ne 0$ can be tested separately since $B(n)$ has $\le 1$ root at $d \le 4$),
- Or $u_n \ne 0$ and
  $$|u_n| \ge |A(n)| - |B(n)| \ge \frac{1}{2} |\lambda_1|^n 2^{-C_{\text{Baker}} (\log(n+2))^2}.$$
On the other hand, in the companion matrix power $A^n$, the operator norm satisfies $\|A^n\|_\infty \le (n+1)^d |\lambda_1|^n 2^{O(\|\boldsymbol{u}\|)}$.
When we compute $A^n$ by repeated squaring ($\le \lceil \log_2(n+1) \rceil$ matrix multiplications of $d \times d$ matrices) using dyadic floating-point intervals $[m - r, m + r] \cdot 2^e$ with $2P(\|\boldsymbol{u}\|, \log n)$ bits of significand precision, each multiplication loses at most $O(\log d + 1)$ bits of relative precision, so after $O(\log n)$ multiplications the accumulated absolute error on $u_n = \alpha A^n \beta$ is at most:
$$\varepsilon_n \le \|A^n\|_\infty \|\beta\|_\infty \cdot 2^{-2P(\|\boldsymbol{u}\|, \log n) + O(\log n)} < \frac{1}{4} |\lambda_1|^n 2^{-C_{\text{Baker}} (\log(n+2))^2} \le \frac{1}{2} |u_n| \quad (\text{whenever } u_n \ne 0).$$
Hence:
- If $u_n \ne 0$, the computed interval $[\hat{u}_n - \varepsilon_n, \hat{u}_n + \varepsilon_n]$ does **not** contain $0$, certifying $u_n \ne 0$.
- If $0 \in [\hat{u}_n - \varepsilon_n, \hat{u}_n + \varepsilon_n]$, then $|u_n| \le 2\varepsilon_n < \frac{1}{2} |\lambda_1|^n 2^{-C_{\text{Baker}}(\log(n+2))^2}$, which by the contrapositive of the lower bound forces $u_n = 0$!
Each of the $O(\log n)$ matrix multiplications multiplies $d \times d$ ($d \le 4$) intervals of bit-length $2P = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ with exponents of bit-length $O(\log n + \log \|\boldsymbol{u}\|)$, taking deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ time overall. $\blacksquare$

---

## Part II: Counterexamples & Obstructions to Plausible Modulus-Selection Rules

As proposed in `idea.txt` (lines 96–113), a natural idea for deterministic zero-testing of $u_n = \alpha A^n \beta$ is to choose a deterministic collection of moduli $S$ of polynomial total bit-length $\sum_{m \in S} \log_2 m = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ and test whether
$$u_n \equiv 0 \pmod m \quad \text{for all } m \in S.$$
Below we analyze two concrete modulus-selection rules and prove **exact counterexample obstructions** demonstrating why they fail.

---

### Obstruction 1: Pisano-Period Defeat of Oblivious Polynomial Modulus Sets

> **Candidate Rule A (Oblivious Polynomial Modulus Set):**
> Given an order-$d$ LRS $\boldsymbol{u}$ and a binary index $n \ge 1$, select a deterministic set of moduli $S = \{m_1, \dots, m_K\}$ (e.g., the first $K$ primes not dividing $a_0$, or prime powers $p_i^{\nu_i}$) of total bit-length $B = \sum_{i=1}^K \log_2 m_i = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$, and declare $u_n = 0$ iff $\alpha A^n \beta \equiv 0 \pmod{m_i}$ for all $i \in \{1, \dots, K\}$.

> **Theorem B1 (Pisano-Period Counterexample / Obstruction to Candidate Rule A):**
> Let $\boldsymbol{u}$ be **any** integer LRS of order $d \ge 2$ such that $u_0 = 0$, $u_n \ne 0$ for all $n \ge 1$ (for instance, the order-2 sequence $u_n = 3^n - 2^n$ satisfying $u_{n+2} = 5u_{n+1} - 6u_n$, $u_0 = 0, u_1 = 1$, or the order-3 sequence $u_n = 5^n - 3^n - 2^n + 1$ shifted appropriately), and let $S = \{m_1, \dots, m_K\}$ be **any** finite set of moduli coprime to $a_0$ with total bit-length $B = \sum_{i=1}^K \log_2 m_i$.
> Then there exists an explicit positive integer
> $$n^* = \mathrm{lcm}_{m \in S} \, \mathrm{ord}_{\mathrm{GL}_d(\mathbb{Z}/m\mathbb{Z})}(A)$$
> such that:
> 1. **Polynomial Binary Length:** $\log_2 n^* \le d^2 B$ (and $\log_2 n^* \le d B$ whenever $A$ is diagonalizable or evaluated on prime powers), so $\|n^*\| = O(B)$ is polynomial in the bit-length of $S$.
> 2. **Total Modular Vanishing:** For **every** modulus $m \in S$,
>    $$u_{n^*} = \alpha A^{n^*} \beta \equiv \alpha I \beta = u_0 = 0 \pmod m.$$
> 3. **True Non-Zeroness:** $u_{n^*} \ne 0$.
>
> Consequently, no modulus set $S$ coprime to $a_0$ of bit-length $B < \frac{1}{d^2} \log_2 n^*$ can distinguish $u_{n^*} \ne 0$ from $0$ without using an upper bound $N < n^*$ on the candidate index.

#### Proof of Theorem B1
Since $\gcd(a_0, m) = \gcd(\det A, m) = 1$ for every $m \in S$, the companion matrix $A \bmod m$ belongs to the finite general linear group $\mathrm{GL}_d(\mathbb{Z}/m\mathbb{Z})$, which has cardinality at most $m^{d^2}$. Thus $r_m := \mathrm{ord}_{\mathrm{GL}_d(\mathbb{Z}/m\mathbb{Z})}(A)$ satisfies $1 \le r_m \le m^{d^2}$, and $A^{r_m} \equiv I \pmod m$. Setting $n^* = \mathrm{lcm}_{m \in S} r_m \le \prod_{m \in S} m^{d^2} = 2^{d^2 B}$, we have $A^{n^*} \equiv I \pmod m$ for all $m \in S$, so $u_{n^*} = \alpha A^{n^*} \beta \equiv \alpha \beta = u_0 = 0 \pmod m$ for all $m \in S$, while $u_{n^*} \ne 0$ by assumption. $\blacksquare$

> **Why `ZeroSearch` Avoids Obstruction 1 Only at its Primary Prime $p$, and Why Secondary Primes $q \in S$ Suffer From It:**
> At the primary prime $p$ used by `ZeroSearch`, the search depth $R$ is chosen so that $M p^R > N \ge n$. Thus $n = 0$ and $n^* = M p^R$ cannot both lie in $[0, N]$; in $[0, N]$, $n = 0$ is the unique candidate in $\overline{D}(0, R)$.
> **However**, if we try to test a false candidate $n_1 \in [0, N]$ (which arose from a *non-integer* $p$-adic root $x_0 \in \mathbb{Z}_p \setminus \mathbb{N}$ of $F_\ell$) by checking $u_{n_1} \equiv 0 \pmod q$ for small secondary primes $q_1, \dots, q_K$, the secondary primes $q_i$ have small multiplicative periods $M_{q_i} < q_i^{d^2} \ll n_1$. Thus $u_n \bmod q_i$ wraps around its Pisano period exponentially many times before reaching $n_1$, allowing $u_{n_1} \equiv 0 \pmod{q_i}$ whenever $n_1 \bmod \pi(q_i)$ lands on a modular zero of $\boldsymbol{u} \bmod q_i$!

---

### Obstruction 2: $p$-adic Ghost-Root Defeat of Single-Prime and Multi-Prime Hensel Filtering at Order $d \ge 3$

By Lemma 1, for $s \le 2$ distinct roots, a single prime power $p^\nu$ with $\nu = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$ suffices to test $u_n = 0$. A natural next candidate rule is:

> **Candidate Rule B (Single-Prime Linear/Polynomial $p$-adic Precision Rule at Order $d = 3$):**
> Given an order-$3$ non-degenerate LRS $\boldsymbol{u}$ and a candidate index $n = Mz + \ell \in [0, N]$ output by `ZeroSearch` at depth $R = \lceil \log_p(N/M) \rceil$, test whether $u_n = 0$ by checking
> $$u_n \equiv 0 \pmod{p^{V(F_\ell) + R}}$$
> (or by checking $u_n \equiv 0 \pmod{p^\nu}$ for a fixed linear function $\nu = c \cdot \log_p n + C_0$).

> **Theorem B2 ($p$-adic Ghost-Root Counterexample / Obstruction to Candidate Rule B):**
> Consider the SODA 2026 order-$3$ recurrence (or any order-$3$ LRS with a simple non-integer $p$-adic root $x_0 \in \mathbb{Z}_p \setminus \mathbb{Z}$):
> $$u_{n+3} = 2u_{n+2} - 3u_{n+1} + u_n, \qquad u_0 = -1, \; u_1 = 1, \; u_2 = 7,$$
> with $p = 5$ and $M = 8$.
> 1. The subsequence $F_3(n) = u_{8n+3}$ has **no integer zeros** ($u_{8n+3} \ne 0$ for all $n \in \mathbb{N}$), because the unique integer zero of $\boldsymbol{u}$ is $n = 4 \equiv 4 \pmod 8$.
> 2. However, $F_3(x)$ has a **unique simple $5$-adic integer root** $x_0 \in \mathbb{Z}_5 \setminus \mathbb{Z}$ ($j(F_3) = 1$, $V(F_3) = 1$) with base-$5$ expansion
>    $$x_0 = 2 + 1 \cdot 5 + 1 \cdot 5^2 + 0 \cdot 5^3 + 3 \cdot 5^4 + 4 \cdot 5^5 + 2 \cdot 5^6 + 0 \cdot 5^7 + \dots \in \mathbb{Z}_5.$$
> 3. For **every** search depth $R \ge 1$, setting $N_R = 8 \cdot 5^R$, `ZeroSearch` outputs the candidate index
>    $$n_R = 8 z_R + 3, \qquad z_R := x_0 \bmod 5^R \in \{0, \dots, 5^R - 1\},$$
>    which has binary bit-length $\|n_R\| = \Theta(R)$ and satisfies:
>    $$v_5(u_{n_R}) = v_5(F_3(z_R)) = V(F_3) + v_5(z_R - x_0) \ge R + 1,$$
>    so $u_{n_R} \equiv 0 \pmod{5^{R+1}}$ **always holds**, even though $u_{n_R} \ne 0$ for every $R \ge 1$!
> 4. Furthermore, whenever the base-$5$ expansion of $x_0$ has a run of $K$ consecutive zeros starting at position $R$ (for example, at $R = 3$ where the digit at $5^3$ is $0$), $z_R = z_{R+K}$, so $u_{n_R} \equiv 0 \pmod{5^{R + K + 1}}$ and `ZeroSearch` extended to depth $R + K$ **still** retains $z_R$!

#### Proof of Theorem B2
By Theorem 2.5 and Table 1 of `arXiv:2507.11234`, for $\ell = 3$ we have $(\Delta^0 F_3)(0) \equiv 10 \pmod{5^5}$, $(\Delta^1 F_3)(0) \equiv 2845 \equiv 5 \cdot 569 \pmod{5^5}$, and $(\Delta^2 F_3)(0) \equiv 1200 \equiv 25 \cdot 48 \pmod{5^5}$, so $V(F_3) = 1$ and $j(F_3) = 1$. By Theorem 2.1 ($p$-adic Weierstrass Preparation), $F_3(x)$ has a unique root $x_0 \in \mathcal{O}_5$, and since $F_3(x) \in \mathbb{Z}_5[[x]]$, uniqueness under $\mathrm{Gal}(\overline{\mathbb{Q}_5}/\mathbb{Q}_5)$ forces $x_0 \in \mathbb{Z}_5$.
Since $j(F_3) = 1$, $v_5(F_3'(x_0)) = V(F_3) = 1$, and by Taylor expansion of $F_3$ around $x_0$:
$$F_3(z_R) = F_3'(x_0)(z_R - x_0) + \sum_{k=2}^\infty \frac{F_3^{(k)}(x_0)}{k!} (z_R - x_0)^k.$$
Since $v_5(F_3^{(k)}(x_0)/k!) \ge V(F_3) + 1 = 2 > 1 = v_5(F_3'(x_0))$ for all $k \ge 2$ and $v_5(z_R - x_0) \ge R \ge 1$, the linear term strictly dominates in $5$-adic valuation:
$$v_5(u_{n_R}) = v_5(F_3(z_R)) = 1 + v_5(z_R - x_0) \ge R + 1.$$
Yet $u_{n_R} \ne 0$ because the unique integer zero of $\boldsymbol{u}$ is $n = 4$ (as certified by the real/complex root structure of $x^3 - 2x^2 + 3x - 1$, which lies in the MSTV class). $\blacksquare$

---

## Part III: What Obstructions 1 & 2 Teach Us — And the Exact Remaining Gap at Order $d \in \{3, 4\}$

Combining **Lemmas 1–2** with **Obstructions 1–2** gives a sharp structural picture of deterministic zero-testing for Order-$\le 4$ Skolem:

1. **Why Purely $p$-adic Single-Prime Tests Cannot Work Alone at $s \ge 3$ Roots without Global Bounds:**
   When $s \ge 3$ distinct roots are $p$-adic units, $F_\ell(x)$ is a $p$-adic analytic function that can have genuine irrational $p$-adic integer roots $x_0 \in \mathbb{Z}_p \setminus \mathbb{Z}$ (Theorem B2). Locally in $\mathbb{Z}_p$, an irrational root $x_0 \in \mathbb{Z}_p$ is indistinguishable at depth $R$ from an integer root $z_R = x_0 \bmod p^R$, unless we have an *upper bound* on how many consecutive zero base-$p$ digits $x_0$ can have after position $R$ (which is equivalent to bounding $v_p(F_\ell(z_R)) = v_p(u_{n_R})$ from above when $u_{n_R} \ne 0$, a $3$-logarithm $p$-adic Baker problem where $x_0 \in \mathbb{Z}_p$ makes the $p$-adic linear form vanish to arbitrary order along $z_R \to x_0$!).

2. **Why Archimedean Interval Exponentiation (Lemma 2) Defeats $p$-adic Ghost Roots:**
   A $p$-adic ghost root $x_0 \in \mathbb{Z}_p \setminus \mathbb{Z}$ makes $u_{n_R}$ small in the **$p$-adic metric** $|u_{n_R}|_p \le p^{-R-1}$, NOT in the **Archimedean metric** $|u_{n_R}|_\infty$!
   In fact, for the ghost-root candidates $n_R = 8 z_R + 3$ of Theorem B2, the Archimedean dominant part $A(n_R) = c \lambda^{n_R} + \overline{c} \overline{\lambda}^{n_R}$ satisfies Baker's Archimedean lower bound $|A(n_R)| \ge |\lambda|^{n_R} e^{-C(\log n_R)^2}$, while the real root $\rho \approx 0.43016$ has $|\rho| < 1 < |\lambda| \approx 1.5247$.
   Thus **Lemma 2 (dyadic interval matrix exponentiation) immediately certifies $u_{n_R} \ne 0$ in deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n_R)$ time for EVERY $R \ge 1$**!

3. **The Exact Remaining Open Regime at Order $d \in \{3, 4\}$:**
   By Lemmas 1 and 2, the **only** regime at order $d \le 4$ not yet covered by deterministic polynomial-time zero testing is when **all three** of the following hold simultaneously:
   - $s \in \{3, 4\}$ distinct characteristic roots,
   - The dominant and subdominant Archimedean root moduli are **distinct but exponentially close**:
     $$0 < \log\!\left(\frac{|\lambda_1|}{|\lambda_{k+1}|}\right) \le 2^{-\Omega(\|\boldsymbol{u}\|)},$$
   - The candidate index $n$ produced by `ZeroSearch` falls inside the narrow **Archimedean transition window**:
     $$n \lesssim \frac{C_{\text{Baker}}(\log n)^2}{\log(|\lambda_1|/|\lambda_{k+1}|)},$$
     where $|\lambda_1|^n$ and $|\lambda_{k+1}|^n$ have not yet separated exponentially, so $u_n$ behaves in $\mathbb{C}$ like a $3$- or $4$-term sum of nearly equal moduli while simultaneously approximating a $p$-adic root modulo $p^R$.

---

## Part IV: Zero Bounds from a Global–Local Dichotomy (Revised)

> [!NOTE]
> **Revision (Nov 2026).** An earlier version of this part described each branch as a *modular zero test* `u_n ≡ 0 (mod D^ν)`. An external review pointed out (with the example `u_n = Dⁿ`) that a vanishing residue proves nothing unless a separate precision theorem bounds `v_q(u_n)` for nonzero `u_n`. Looking at the branches again, every argument we have proves something **stronger and simpler**: an explicit **bound on the largest zero**,
> $$u_k \ne 0 \quad \text{for all } k \ge B(\boldsymbol{u}),\qquad B(\boldsymbol{u}) = \mathrm{poly}(\|\boldsymbol{u}\|).$$
> Given such a bound, the deterministic test for a `ZeroSearch` candidate `n` is trivial: if `n ≥ B`, answer *nonzero*; otherwise compute `u_n` exactly (it has `poly(‖u‖)` bits). Neither the `D^ν` modular test nor interval arithmetic is needed. The Lean theorem `factorization_free_composite_power_test_iff` is kept for history but is superseded by Theorems 5 and 6 below.

Throughout, `v_k = u_{L_d M k + r}` is a non-degenerate subsequence of order `d ∈ {3,4}` produced by `ZeroSearch` ($L_3 = 6$, $L_4 = 12$, so all Newton-polygon slopes are integers). It has characteristic polynomial $\chi(x) = x^d + b_{d-1}x^{d-1} + \dots + b_0 \in \mathbb{Z}[x]$, and `s = d` active roots (fewer roots fall under Lemma 1).

### 4.0 Status legend

| Label | Meaning |
|---|---|
| **[Lean]** | Proved in Lean 4 with no external hypotheses (`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`). |
| **[Paper: Smyth + Baker]** | Pen-and-paper argument using Smyth's/Boyd's Mahler-measure bounds and Archimedean linear forms in **two** logarithms (Baker–Wüstholz / Matveev). The algebraic deduction from the gap and Baker inequality is formalized in `Skolem/DeterministicZeroTest.lean`. |
| **[Paper: Yu]** | Uses Yu's $p$-adic linear forms in two logarithms. The constant grows like $q^f$, so the bound is polynomial only for $q \le \mathrm{poly}(\|\boldsymbol{u}\|)$. |
| **[Open]** | No polynomial zero bound is known to us. |

#### 4.0.1 Literature comparison: what is known vs. what is new here

- **Known general bounds on the largest zero ($N = 2^{\mathrm{poly}(\|\boldsymbol{u}\|)}$):** Mignotte–Shorey–Tijdeman (1984), Vereshchagin (1985), Chonev–Ouaknine–Worrell (2016, *JACM*, Appendix C), Bacik (2025, *TheoretiCS*), Bilu (2025, `arXiv:2501.16290`), and Bacik–Ouaknine–Worrell (SODA 2026, Corollary 3.7; see also §5.3–5.4 of the 2026 MPI-SWS Survey) establish an **exponential** upper bound $N = 2^{\mathrm{poly}(\|\boldsymbol{u}\|)}$ in the bit-size $\|\boldsymbol{u}\|$ (equivalently, polynomial/quasi-polynomial in the naive magnitude $H_u = 2^{\|\boldsymbol{u}\|}$) for all non-degenerate LRS of order $d \le 4$ and in $\mathrm{MSTV}(d)$. Separately, Beukers (1991) and Schmidt (1999) bound the *number* of zeros (zero-multiplicity, e.g. $\le 6$ for integer ternary LRS), using ineffective Subspace-Theorem / hypergeometric methods that do not bound the index $n$.
- **Classical polynomial-in-bit-size subcases ($N = \mathrm{poly}(\|\boldsymbol{u}\|)$):**
  1. *At most two distinct roots ($s \le 2$, Lemma 1):* Solving $(\lambda_1/\lambda_2)^n = -P_2(n)/P_1(n)$ via logarithmic Weil heights (Dobrowolski/Voutier) bounds $n = O(\|\boldsymbol{u}\|)$ in polynomial time (Chonev–Ouaknine–Worrell 2016; Survey §5.3).
  2. *Single $v$-dominant root ($k_v = 1$) at a prime place $v \mid p$:* In the $k = 1$ subcase of the MSTV theorem (Survey §5.3, p. 22), $|A(n)|_v = |Q_1(n)|_v |\lambda_1|_v^n$ is bounded below by Liouville's inequality without Baker's theorem, giving $n \le O(\|\boldsymbol{u}\|/\log p)$.
- **What is new in this repository:**
  1. **Factorization-free, elementary $k_q = 1$ zero bounds in Lean 4 (`Skolem/UnitRootDominance.lean`):** Theorems 5, 6, and `order_d_unit_root_zero_bound` formulate the $k_q = 1$ window-climbing argument directly on the integer recurrence coefficients modulo $q^{m+1}$ via $w_k = u_{k+d-1} + \sum_{i < d-1} s_i u_{k+i}$, proving $q^{m+1} \nmid u_k$ and $u_k \ne 0$ for $k \ge (d-1)(m+1)$ **without factoring $q$** (so $q$ may be composite), **without splitting fields or $p$-adic valuations**, and **with zero external hypotheses in Lean 4**, together with the exact slope-normalization scaling identity $S^{d-1} v_k = S^k z_k$ (`order3_slope_normalization_scaling`).
  2. **The $D = 1$ unit-branch consecutive-gap bound (§4.3, §4.5):** Applying Smyth's/Boyd's Mahler-measure lower bounds to the normalized root-power polynomial $P_\xi(t) = \prod (t - \hat{\mu}_i^d / ((-1)^d \hat{b}_0))$ when $D = 1$ forces an absolute lower bound on the largest consecutive Archimedean log-modulus gap ($\ge \frac{1}{4}\log\theta_0 > 0.0703$ at order 3; $\ge \frac{1}{12}\log\theta_0 > 0.0234$ at order 4), yielding a $\mathrm{poly}(\|\boldsymbol{u}\|)$ zero bound via two-logarithm Baker whenever that gap splits off a 1- or 2-root dominant block.

### 4.1 Normalization (corrected) **[Lean: `order3_slope_normalization_scaling`]**

Bernstein's coprime base of $\{|b_{d-1}|,\dots,|b_0|\}$, followed by `reduce_perfect_powers`, yields pairwise coprime integers $c_1,\dots,c_t$, **none of which is a perfect power**, with $|b_{d-r}| = \prod_j c_j^{e_{rj}}$. Set
$$S = \prod_j c_j^{\,\min_r \lfloor e_{rj}/r \rfloor}, \qquad \hat{b}_{d-r} = b_{d-r}/S^r \in \mathbb{Z}.$$

*Why this is correct prime by prime (it uses only genuine prime valuations).* For a prime $p \mid c_j$ we have $v_p(b_{d-r}) = e_{rj}\,v_p(c_j)$. The leftmost Newton slope $\kappa_p = \min_r v_p(b_{d-r})/r = v_p(c_j)\cdot \min_r e_{rj}/r$ is an integer for **every** $p \mid c_j$, because the roots are $L_d$-th powers. Write $\min_r e_{rj}/r = a/b$ in lowest terms. Then $b$ divides $v_p(c_j)$ for every $p \mid c_j$, so $b \mid \gcd_p v_p(c_j) = 1$, since $c_j$ is not a perfect power. Hence the minimum $\min_r e_{rj}/r$ is an integer, so it equals $\min_r \lfloor e_{rj}/r \rfloor$, and $v_p(S) = \kappa_p$. Without `reduce_perfect_powers` this step fails.

*Normalized integer sequence (corrects the earlier "$v_k/\gcd(v_k, S^k)$", which was wrong).* Define $z_k := S^{\,d-1-k}\, v_k$ (`src/deterministic_zero_test.py :: slope_normalize_lrs`). Dividing the recurrence by $S^{k+d}$ shows that $z_k$ satisfies the recurrence with coefficients $\hat{b}_i$ and integer initial values $z_j = S^{d-1-j} v_j$ ($0 \le j < d$), so every $z_k$ is an integer and satisfies the exact non-negative exponent identity
$$S^{d-1} v_k = S^k z_k \qquad \text{for all } k \in \mathbb{N}$$
(formalized in `Skolem/UnitRootDominance.lean :: order3_slope_normalization_scaling` and `order3_normalized_unit_root_zero_bound`). Since $S \ne 0$, $z_k = 0 \iff v_k = 0$ for all $k$. Its characteristic roots $\hat{\mu}_i = \mu_i/S$ satisfy $\min_i v_p(\hat{\mu}_i) = 0$ at every prime $p$.

Define $\xi_i = \hat{\mu}_i^d / ((-1)^d \hat{b}_0)$, $P_\xi(t) = \prod_i (t - \xi_i) \in \mathbb{Q}[t]$, and let $D$ be the lcm of the denominators of its coefficients (explicit formulas in `order3_global_local_dichotomy` / `order4_global_local_dichotomy`). Then $D = 1$ iff all roots have equal valuation at every prime. For a prime $q \mid D$, let $k_q \in \{1,\dots,d-1\}$ be the length of the slope-0 segment, i.e. the number of $q$-adic unit roots.

### 4.2 Theorems 5, 6, and General Order $d$ — the unit-root branch $k_q = 1$ **[Lean]**

> [!IMPORTANT]
> **Theorem 5 (Order 3) / Theorem 6 (Order 4) / General Order $d = r + 1$** — `Skolem/UnitRootDominance.lean`: `order3_unit_root_zero_bound`, `order4_unit_root_zero_bound`, `order_d_unit_root_zero_bound`.
> Let $u$ be an integer recurrence with characteristic polynomial $\chi(x) = x^d + b_{d-1}x^{d-1} + \dots + b_0$. Let $q \in \mathbb{Z}$ be **any** integer, prime or composite (it is never factored). Suppose $\mu, s_0, \dots, s_{d-2} \in \mathbb{Z}$ and $m \in \mathbb{N}$ satisfy
> $$\chi(x) \equiv (x-\mu)\big(x^{d-1} + s_{d-2}x^{d-2} + \dots + s_0\big) \pmod{q^{m+1}}, \qquad q \mid s_i,\qquad \gcd(\mu, q) = 1,$$
> and that $q^m \mid w_0$ but $q^{m+1} \nmid w_0$, where $w_0 = u_{d-1} + \sum_i s_i u_i$. Then
> $$q^{m+1} \nmid u_k \quad\text{and hence}\quad u_k \ne 0 \qquad \text{for every } k \ge (d-1)(m+1).$$

*Proof idea (entirely elementary).* Set $w_k = u_{k+d-1} + \sum_i s_i u_{k+i}$. The factorization gives $w_{k+1} \equiv \mu w_k \pmod{q^{m+1}}$. Since $\mu$ is a unit mod $q$, the $q$-order of $w_k$ stays frozen at exactly $m$ (`unit_ratio_order_frozen`). Meanwhile $u_{k+d-1} = w_k - \sum_i s_i u_{k+i}$ with every $q \mid s_i$. So the power of $q$ dividing a window of $d-1$ consecutive terms rises by one every $d-1$ steps until it reaches $m$. After that the frozen $w$ decides the $q$-order of every later term (`window_climb_zero_bound`). Only divisibility and $\gcd(\mu,q)=1$ are used, so the fact that $\mathrm{ord}_q$ is not a valuation for composite $q$ does no harm.

**When does a certificate exist, and how large is $m$?** The certificate exists on the normalized sequence $z$ exactly when $q \mid \hat{b}_0,\dots,\hat{b}_{d-2}$ and $\gcd(\hat{b}_{d-1}, q) = 1$. The largest such $q$ is computed without factoring as $q = \mathrm{Strip}(\gcd(\hat{b}_0,\dots,\hat{b}_{d-2}),\, \hat{b}_{d-1}) = D_{k=1}$.

The root $\mu \equiv -\hat{b}_{d-1}$ is simple mod $q$, because $\chi'(\mu) \equiv \mu^{d-1}$ is a unit. So Newton/Hensel lifting modulo $q^{m+1}$ works for composite $q$, and synthetic division then gives the $s_i$ (`src/deterministic_zero_test.py :: unit_root_certificate`). The $q$-adic limit of $w_0$ equals the unit-root coefficient times a nonzero algebraic factor. Hence $m$ is finite iff that coefficient is nonzero, and then $m = O(\mathrm{poly}(\|\boldsymbol{u}\|)/\log q)$. If the coefficient is zero, $u$ satisfies a recurrence of order $d-1$ and falls to a lower case.

**Verification.**
- Lean: `lake build` succeeds across all 5 modules (1270 jobs). A concrete instance with composite $q = 15$ (`unitRootExample_no_late_zeros`: $x^3 - x^2 + 15x + 15$, $u = (0,0,1,\dots)$) proves $u_k \ne 0$ for **all** $k \ge 2$.
- Python: on 3,077 random order-3/4 recurrences with a certificate (1,626 with composite $q$, 1,726 with $m > 0$, maximum $m = 12$), brute force found no zero and no $q^{m+1} \mid u_k$ beyond the bound (`experiments/unit_root_zero_bounds.py`).

### 4.3 Theorem 3′ — Order 3, unit branch $D = 1$ **[Paper: Smyth + Baker; Lean deduction]**

If $D = 1$, the $\xi_i$ are algebraic units of degree $\le 3$ with $\xi_1\xi_2\xi_3 = 1$. Order the moduli as $|\hat{\mu}_1| \ge |\hat{\mu}_2| \ge |\hat{\mu}_3|$; equal moduli are covered by Lemma 2. Then
$$\theta_0 \le M(\xi_1) \le M(P_\xi) = \max\!\Big(\tfrac{|\hat\mu_1|^2}{|\hat\mu_2||\hat\mu_3|},\ \tfrac{|\hat\mu_1||\hat\mu_2|}{|\hat\mu_3|^2}\Big) \le \Big(\tfrac{|\hat\mu_1|}{|\hat\mu_3|}\Big)^2.$$
The left inequality uses Smyth for irreducible cubics, which are never reciprocal, and $M \ge \varphi$ for quadratic units. So the larger of the two consecutive gaps is at least $\tfrac14\log\theta_0 > 0.0703$ (`smyth_mahler_measure_consecutive_gap_order3`). Split the roots at that gap:
- **Single dominant root ($k_\infty = 1$):** one term dominates; there is no cancellation inside the block.
- **Two dominant roots ($k_\infty = 2$):** a dominant complex pair, or two nearly equal real roots as in $x(x-N)^2 - 1$. Baker in two logarithms bounds $|c_1\hat\mu_1^k + c_2\hat\mu_2^k|$ from below in terms of the *Weil height* $h(\hat\mu_1/\hat\mu_2)$. That bound does not depend on how small $|\hat\mu_1/\hat\mu_2 - 1|_\infty$ is.

Either way, **$u_k \ne 0$ for all $k > \mathrm{poly}(\|\boldsymbol{u}\|)$** (the deduction from the gap and two-term Baker inequality is formalized in `Skolem/DeterministicZeroTest.lean :: archimedean_gap_zero_bound` and `order3_unit_branch_smyth_baker_zero_bound`). For a dominant complex pair the reviewer's direct computation gives the sharper constant $\delta \ge \tfrac12\log\theta_0 \approx 0.1406$. For totally real roots, Schinzel's bound for totally real units improves the constant further.

### 4.4 Order 3, $D > 1$

Every $q \mid D$ has $k_q \in \{1, 2\}$.
- **$D_{k=1} > 1$:** Theorem 5 **[Lean]** (`order3_unit_root_zero_bound` / `order3_normalized_unit_root_zero_bound`).
- **$k_q = 2$ at some $q \le \mathrm{poly}(\|\boldsymbol{u}\|)$:** the two tied unit roots are controlled by Yu; the zero bound is $\mathrm{poly}(\|\boldsymbol{u}\|)\cdot q^f$ **[Paper: Yu]** (deduction formalized in `padic_two_root_yu_zero_bound`).
- **The largest Archimedean consecutive gap is $\ge 1/\mathrm{poly}(\|\boldsymbol{u}\|)$:** a 1- or 2-term Archimedean block plus two-log Baker gives a polynomial zero bound **[Paper: Baker]**.
- **Residual [Open]:** all three moduli $|\hat\mu_i|$ lie within a superpolynomially small factor of each other, $D_{k=1} = 1$, and every prime $q \mid D$ is superpolynomially large.

*Why Smyth cannot help here.* When $D > 1$ the $\xi_i$ are not algebraic integers, and nothing like Kronecker's theorem holds for non-integers: $(3+4i)/5$ has every conjugate exactly on the unit circle. Nearly equal moduli are therefore no longer ruled out by arithmetic.

### 4.5 Order 4

- **$D_{k=1} > 1$**, i.e. $q \mid \hat b_0, \hat b_1, \hat b_2$ and $\gcd(\hat b_3, q) = 1$: Theorem 6 **[Lean]**.
- **$D = 1$:** by Kronecker and non-degeneracy, the four moduli are not all equal. $\xi_1$ is then a non-cyclotomic unit of degree $\le 4$, and $M(\xi_1) \ge \theta_0$: Smyth if it is non-reciprocal; $\varphi \approx 1.618$ for reciprocal quadratics; and, for reciprocal quartics, the smallest degree-4 Salem number $\approx 1.7221$, the root of $x^4 - x^3 - x^2 - x + 1$. Hence the largest of the three consecutive gaps is at least $\tfrac1{12}\log\theta_0 > 0.0234$ (`smyth_mahler_measure_consecutive_gap_order4`). If that gap is at $j \in \{1, 2\}$, the dominant block has at most 2 roots, and we get a polynomial zero bound **[Paper: Smyth + Baker]**.
- **$k_q \in \{1, 2\}$ at a small prime** ($D_{\le 2}$ has a prime factor $\le \mathrm{poly}$): **[Paper: Yu]**.

### 4.6 The single remaining obstacle: three terms with no smaller split at any place **[Open]**

Every order-3/4 case not covered above has the same shape. At **every** place that we can use efficiently, the dominant block contains at least three roots:
1. **Order-4 Archimedean three-root cluster with $D = 1$ ($k_\infty = 3$).**
   Example: $h_N(x) = x(x-N)^3 - 1$, a quartic with unit roots and $D = 1$. Three of its roots are $N + N^{-1/3}\omega + o(N^{-1/3})$ with $\omega^3 = 1$: a real root of modulus $\approx N + N^{-1/3}$ and a complex pair of modulus $\approx N - \tfrac12 N^{-1/3}$. The fourth root is $\approx -N^{-3}$. For large $N$ the consecutive log-gaps are $\approx 1.5N^{-4/3}$, $0$, and $\approx 4\log N$, so the only large gap is at $j = 3$. This embeds the classical hard order-3 configuration (a real root against a complex pair of nearly equal modulus) inside an order-4 unit.
2. **Order-3 open-class family with $D > 1$, $D_{k=1} = 1$, and large prime $q \mid D$ ($k_q = 2$).**
   In `experiments/near_equal_modulus_search.py`, we construct the explicit family
   $$g_{N,c}(x) = (x - N)(x^2 + x + N^2) - c = x^3 - (N - 1)x^2 + N(N - 1)x - (N^3 + c)$$
   for $c \in \{-2, +2\}$ and $N$ chosen so that $q = |N^3 + c|$ is prime (e.g., $c = -2, N \in \{9, 15, 19, 27, 31, 37\}$ with $q \in \{727, 3373, 6857, 19681, 29789, 50651\}$; or $c = +2, N \in \{3, 5, 29, 45, 63, 65\}$ with $q \in \{29, 127, 24391, 91127, 250049, 274627\}$):
   - Because $v_q(b_1) = v_q(N(N-1)) = 0$, every $q$-adic Newton polygon already has integer slopes $(0, 0, 1)$, so $S = 1$, $\gcd(b_0, b_1) = 1 \implies D_{k=1} = 1$, and $D = q^2$ has the unique prime factor $q = \Theta(N^3) = 2^{\Theta(\|\boldsymbol{u}\|)}$ with $k_q = 2$.
   - The real root has modulus $|\mu_1| = N + \frac{c}{2N^2} + O(N^{-3})$ and the complex conjugate pair has modulus $|\mu_2| = |\mu_3| = N + \frac{c}{4N^2} + O(N^{-3})$, so the consecutive Archimedean log-modulus gaps are $\frac{|c|}{4N^3} + O(N^{-4}) = 2^{-\Theta(\|\boldsymbol{u}\|)}$ and $0$. For $c = -2$, the complex conjugate pair has strictly larger modulus than the real root by $\delta_\infty \approx \frac{1}{2N^3}$.

#### Why standard reductions to two-logarithm bounds stall on this residual class

- **Why Beukers–Tijdeman circle intersection works for exact equi-dominance ($|\lambda_1| = |\lambda_2| = |\lambda_3|$) but fails on a near-equal 3-cluster ($0 < \delta_\infty \ll 1$):**
  When $|\lambda_1| = |\lambda_2| = |\lambda_3|$ *exactly* (Lemma 2), writing $A(n) = c_1 \lambda_1^n (z_1(n) - z_0(n))$ places $z_0(n) = -(c_2/c_1)(\lambda_2/\lambda_1)^n$ and $z_1(n) = 1 + (c_3/c_1)(\lambda_3/\lambda_1)^n$ on circles centered at $0$ and $1$ whose radii $r_0 = |c_2/c_1|$ and $r_1 = |c_3/c_1|$ are **independent of $n$**. Their intersection points $\varsigma, \overline{\varsigma}$ are fixed algebraic numbers of Weil height $h(\varsigma) = O(\|\boldsymbol{u}\|)$, so applying two-logarithm Baker to $z_0(n) - \varsigma$ gives $|A(n)| \ge |\lambda_1|^n 2^{-\mathrm{poly}(\|\boldsymbol{u}\|)\log n}$.
  By contrast, when $|\lambda_1| = R > |\lambda_2| = |\lambda_3| = r = R e^{-\delta_\infty}$ with $0 < \delta_\infty \le 2^{-\Omega(\|\boldsymbol{u}\|)}$, the radius at step $n$ scales by $(r/R)^n$. Because $r/R \ne 1$ is not a root of unity, Dobrowolski's theorem bounds its Weil height $h(r/R) \ge c_d > 0$ away from zero *regardless of how small $\delta_\infty = \log(R/r)$ is*. Thus the circle-intersection point $\varsigma_n$ at step $n$ has Weil height $h(\varsigma_n) = n \, h(r/R) + O(\|\boldsymbol{u}\|) = \Theta(n)$, and plugging $h(\varsigma_n) = \Theta(n)$ into two-logarithm Baker gives $\exp(-C n \log n)$, which is much smaller than $e^{-n\delta_\infty}$ and yields no zero bound.
- **Why the naive global norm bound on $Z_k = c_1 \hat{\mu}_1^k + c_2 \hat{\mu}_2^k$ is an exact tautology at $u_k = 0$ (exact constant analysis for $k_q = 2$):**
  At a prime $q \mid D$ with $k_q = 2$ (such as $q = |N^3 + c|$ in $g_{N,c}$), $\chi(x)$ factors over $\mathbb{Q}_q$ into a linear factor $(x - \hat{\mu}_3)$ with $v_q(\hat{\mu}_3) = \Delta_q = v_q(\hat{b}_0) \ge 1$ and a unit quadratic. Because $u_k \in \mathbb{Z}$, the two-term sum $Z_k = c_1 \hat{\mu}_1^k + c_2 \hat{\mu}_2^k = u_k - c_3 \hat{\mu}_3^k$ is invariant under swapping $\hat{\mu}_1 \leftrightarrow \hat{\mu}_2$ and therefore lies in the **cubic subfield $F = \mathbb{Q}(\hat{\mu}_3)$ of degree $[F:\mathbb{Q}] = 3$** (not $[K:\mathbb{Q}] = 6$), where the prime ideal $\mathfrak{p}_3 \mid q$ with $v_{\mathfrak{p}_3}(\hat{\mu}_3) = \Delta_q$ has $e(\mathfrak{p}_3\mid q) = f(\mathfrak{p}_3\mid q) = 1$ and $N_{F/\mathbb{Q}}(\mathfrak{p}_3) = q$. Thus the degree-to-residue ratio $[F:\mathbb{Q}]/(3 f)$ is **1** (not 2).
  However, in $F$, the three conjugates of $Z_k$ are $x+y$, $y+z$, and $z+x$, where $(x,y,z) = (c_1\hat{\mu}_1^k, c_2\hat{\mu}_2^k, c_3\hat{\mu}_3^k)$ and $x+y+z = u_k$. By the elementary symmetric identity (`Skolem/DeterministicZeroTest.lean :: cubic_two_sum_norm_identity`, `cubic_two_sum_norm_at_zero`)
  $$N_{F/\mathbb{Q}}(Z_k) = (x+y)(y+z)(z+x) = u_k(xy + yz + zx) - xyz,$$
  whenever $u_k = 0$, the field norm $N_{F/\mathbb{Q}}(Z_k)$ collapses **identically** to the monomial $-xyz = -c_1 c_2 c_3 (-\hat{b}_0)^k$. At a hypothetical zero $u_k = 0$, $Z_k = -c_3\hat{\mu}_3^k$ is a single exponential term, so $|N_{F/\mathbb{Q}}(Z_k)|_\infty = |c_1 c_2 c_3| |\hat{b}_0|^k$ and $q^{v_{\mathfrak{p}_3}(Z_k)} = q^{v_{\mathfrak{p}_3}(c_3) + k v_q(\hat{b}_0)}$ match identically when $|\hat{b}_0| = q^{\Delta_q}$ by the product formula on $-c_3\hat{\mu}_3^k$. Any bound that beats Yu's $q^f$ factor must therefore combine multiple shifts $Z_{k+j}$ inside an interpolation determinant so that the determinant does not collapse to a monomial at $u_k = 0$.

#### Empirical behavior of zeros in the near-equal-modulus and open families (`experiments/near_equal_modulus_search.py`)

Across all three families — $f_N(x) = x(x-N)^2 - 1$ (Order 3, $D=1$), $h_N(x) = x(x-N)^3 - 1$ (Order 4, $D=1, k_\infty=3$), and $g_{N,\pm 2}(x) = (x-N)(x^2+x+N^2) \mp 2$ (Order 3, $D = q^2, D_{k=1}=1$) — scanning both small initial boxes ($u_i \in [-4, 4]$) and initial states with planted zeros at $0 = k_1 < k_2 \le 25$ up to index $k = 300$ found **zero** unexpected extra zeros beyond the planted zero (`extra_zeros_beyond_plant = 0`), and the largest zero index satisfied $k_{\max} / \|\boldsymbol{u}\| < 0.40$ in every case (decreasing as $\Theta(1/\log N)$ as $N$ grows). This supports the expectation that the largest zero remains $O(\|\boldsymbol{u}\|)$ even in the residual 3-term class.

### 4.7 Lean inventory for Part IV

| Theorem | File | Assumptions |
|---|---|---|
| `unit_ratio_order_frozen`, `window_climb_zero_bound`, `order3_unit_root_zero_bound`, `order4_unit_root_zero_bound`, `order3_unit_root_mod_q`, `order_d_unit_root_zero_bound`, `unitRootExample_no_late_zeros` | `Skolem/UnitRootDominance.lean` | **none** (standard axioms only) |
| `order3_slope_normalization_scaling`, `order3_normalized_unit_root_zero_bound` | `Skolem/UnitRootDominance.lean` | **none** (standard axioms only; proves $S^2 v_k = S^k z_k$ and transfers Theorem 5 across slope normalization) |
| `cubic_two_sum_norm_identity`, `cubic_two_sum_norm_at_zero` | `Skolem/DeterministicZeroTest.lean` | **none** (standard axioms only; proves $(x+y)(y+z)(z+x) = (x+y+z)(xy+yz+zx)-xyz$ and its monomial collapse at $x+y+z=0$) |
| `smyth_mahler_measure_consecutive_gap_order3/4`, `archimedean_gap_zero_bound`, `order3_unit_branch_smyth_baker_zero_bound`, `padic_two_root_yu_zero_bound` | `Skolem/DeterministicZeroTest.lean` | Smyth's bound, Mahler-measure inequality, and two-term Baker/Yu bounds passed as explicit hypotheses; the deduction to $u_k \ne 0$ is formal |
| `factorization_free_composite_power_test_iff`, `order3_global_local_dichotomy_iff` | `Skolem/DeterministicZeroTest.lean` | Baker/Yu-type precision bound as a hypothesis; **superseded** by the zero-bound theorems above |
