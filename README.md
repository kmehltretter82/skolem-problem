# Skolem Problem

Computational, number-theoretic, and formal exploration of the Skolem problem for linear recurrence sequences.

## Research Directions

1. **Derandomizing Order-$\le 4$ Skolem**: Investigating deterministic polynomial-time zero testing for structured matrix-power expressions $u_n = \alpha A^n \beta$ (with $n$ in binary) arising in the $\mathrm{coRP}$ algorithm of Bacik, Ouaknine, and Worrell (SODA 2026).
2. **Order-5 Boundary & Explicit Open Sequences**: Studying unresolved low-order instances, including the explicit order-6 sequence
   $$u_n = 2(-4+7i)^n + 2(-4-7i)^n + 4(8+i)^n + 4(8-i)^n + n.$$
3. **Matrix Mortality & Arithmetic Encodings**: Investigating generator-count and determinant restrictions for $2 \times 2$ matrix mortality.

## Repository Structure

- `idea.txt` — Initial research problem analysis and roadmap.
- `notes/` — Mathematical notes, literature extracts, and candidate lemmas.
- `src/` — Reference implementations of the low-order Skolem algorithm and zero-testing routines.
- `experiments/` — Scripts for searching for counterexamples to deterministic modulus-selection rules.
