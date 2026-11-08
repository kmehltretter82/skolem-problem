"""Empirical stress test of Theorems 5/6 (unit-root zero bounds) against brute force."""
import random
import sys

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.dirname(__import__("os").path.abspath(__file__))))
from src.deterministic_zero_test import unit_root_certificate, check_unit_root_certificate
from src.skolem_algorithm import LinearRecurrenceSequence

random.seed(1)
tested = with_m_pos = composite_q = violations = 0
max_m_seen = 0
for trial in range(4000):
    d = random.choice([3, 4])
    q0 = random.choice([2, 3, 5, 6, 7, 10, 12, 15, 30, 77, 1001])
    # chi = x^d + b_{d-1} x^{d-1} + ... + b_0 with q0 | b_0..b_{d-2}
    b = [q0 * random.randint(-5, 5) for _ in range(d - 1)] + [random.randint(-9, 9)]
    if b[0] == 0:
        continue
    coeffs = [-x for x in b]
    init = [random.randint(-50, 50) for _ in range(d)]
    # sometimes make the leading initial value highly q0-divisible to exercise m > 0
    if random.random() < 0.5:
        init[-1] = q0 ** random.randint(1, 4) * random.randint(-3, 3)
        init[:-1] = [q0 * x for x in init[:-1]]
    lrs = LinearRecurrenceSequence(coeffs=coeffs, initial=init)
    cert = unit_root_certificate(lrs)
    if cert is None:
        continue
    assert check_unit_root_certificate(lrs, cert)
    q, m, K = cert["q"], cert["m"], cert["zero_bound"]
    tested += 1
    with_m_pos += m > 0
    composite_q += any(q % p == 0 for p in range(2, int(q ** 0.5) + 1))
    max_m_seen = max(max_m_seen, m)
    Q = q ** (m + 1)
    u = list(init)
    for k in range(d, K + 120):
        u.append(sum(coeffs[i] * u[k - d + i] for i in range(d)))
    for k in range(K, K + 120):
        if u[k] == 0 or u[k] % Q == 0:
            violations += 1
            print("VIOLATION", d, b, init, cert, k)
            break
print(f"tested={tested} m>0={with_m_pos} composite_q={composite_q} max_m={max_m_seen} violations={violations}")
