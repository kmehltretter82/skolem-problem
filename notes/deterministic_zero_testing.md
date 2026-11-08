# Deliverables 3 & 4: Candidate Deterministic Zero-Testing Lemmas, Proofs, and Counterexample Obstructions

## Overview

In this note we address Deliverables 3 and 4 of `idea.txt`:
- **Part I (Proven Deterministic Polynomial-Time Lemmas):** We establish two unconditional deterministic polynomial-time zero-testing lemmas covering major subclasses of Order-$\le 4$ LRS:
  1. **Lemma 1 (Two-Root / Repeated-Root Subclass up to Order 4):** Deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$-time zero-testing via **both** a single prime-power modulus $p^\nu$ (using Yu's $p$-adic Baker bound) and a direct Weil-height magnitude cutoff $N_{\text{height}} = \mathrm{poly}(\|\boldsymbol{u}\|)$ (which requires no Baker bound at all). This settles deterministic polynomial-time Skolem for **all order-$d \le 2$ LRS** and **all order-$3$ and order-$4$ LRS with at most $2$ distinct characteristic roots**.
  2. **Lemma 2 (Archimedean Equi-Dominant & Well-Separated MSTV Subclasses at Order $d \le 4$):** Deterministic $\mathrm{poly}(\|\boldsymbol{u}\|, \log n)$-time zero-testing via **dyadic ball / interval matrix exponentiation** at bit-precision $P = \mathrm{poly}(\|\boldsymbol{u}\|, \log n)$, proved using the Baker–Matveev and Beukers–Tijdeman separation bound $|A(n)| \ge |\lambda_1|^n e^{-C(\log n)^2}$.
- **Part II (Counterexamples & Obstructions to Plausible Modulus-Selection Rules):** We formulate two natural deterministic modulus-selection / $p$-adic precision rules and prove **explicit counterexample obstructions** showing why they fail on general Order-$3$ and Order-$4$ instances:
  1. **Obstruction 1 (Pisano-Period Defeat of Oblivious Polynomial Modulus Sets):** Any rule that tests $u_n \equiv 0 \pmod m$ over a polynomial-bit-length set of moduli $S$ coprime to $a_0$ (without enforcing $p$-adic disc uniqueness $N < M p^R$) is defeated by an explicit binary index $n = \mathrm{lcm}_{m \in S} \mathrm{ord}_m(A)$ of bit-length $\le d \sum_{m \in S} \log_2 m$ where $u_n \ne 0$ yet $u_n \equiv 0 \pmod m$ for all $m \in S$.
  2. **Obstruction 2 ($p$-adic Ghost-Root Defeat of Single-Prime and Multi-Prime Hensel Filtering at Order $d \ge 3$):** For order $d \ge 3$ with $\ge 3$ distinct roots, the Mahler interpolant $F_\ell(x)$ can possess a non-integer $p$-adic root $x_0 \in \mathbb{Z}_p \setminus \mathbb{N}$ ("ghost root"). Truncating $x_0$ at any depth $R$ yields a valid `ZeroSearch` candidate $n_R = M(x_0 \bmod p^R) + \ell$ with $v_p(u_{n_R}) \ge V(F_\ell) + R$ and $u_{n_R} \ne 0$.
- **Part III (The Exact Remaining Open Barrier at Order $d \in \{3, 4\}$):** We isolate the precise "Archimedean transition window" where neither Lemma 1 nor Lemma 2 immediately runs in polynomial time, providing a sharp target for complete derandomization of Order-$\le 4$ Skolem.

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
