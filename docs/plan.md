# Formalization plan: Kovač–Tao Theorem 2.11 (Erdős #266)

Source: arXiv:2406.17593v4, Sections 7–8 (with Lemmas 7.1, 7.2). Target:
`Erdos266.erdos_266_rational_shifts` in `Solution.lean` (the only remaining
sorry; `erdos_266` is already derived from it via `Erdos266/Glue.lean`).

## The proof, digested

**Setup (Section 7).** Fix an enumeration $(t_i)_{i\ge 1}$ of $\mathbb{Q}$
with $|t_i| \le i$ (7.1). For each $i$ define
$f_i(x) := 1/\prod_{j=1}^{i}(x+t_j)$ (set to $0$ at the poles
$x \in \{-t_1,\dots,-t_i\}$). Partial fractions give unique **nonzero**
rationals $m_{i,j}$ with $f_i(x) = \sum_{j=1}^i m_{i,j}/(x+t_j)$ away from
poles; in particular the (triangular, invertible) change of variables $U$
with rows $m_{i,\cdot}$ satisfies $U\mathbb{Q}^\mathbb{N} = \mathbb{Q}^\mathbb{N}$ (7.2).

**Reduction.** Theorem 2.11 follows from: there is a strictly increasing
sequence of positive integers $(a_n)$ with $\sum_n 1/a_n < \infty$ and
$\sum_n f_i(a_n) \in \mathbb{Q}$ for every $i$. (Invert the triangular
system: by strong induction on $i$, rationality of $\sum_n f_i(a_n)$ and of
$\sum_n 1/(a_n+t_j)$ for $j<i$, plus $m_{i,i}\ne 0$, give rationality of
$\sum_n 1/(a_n+t_i)$.)

**Lemma 7.1 (slope lemma).** For every $i$ there is $C_i>0$ with
$|f_i(N) - f_i(N+n) - in/N^{i+1}| \le C_i n^2 / N^{i+2}$ for $N \in \mathbb{N}$,
$n \in \mathbb{Z}$, $|n| \le N/4i$. ($f_i$ is locally linear of slope
$-i/N^{i+1}$ near large $N$.) Paper's $C_i = 2^{10i}$; any constant works.

**Lemma 7.2 (lattice lemma).** For every $d$ there are $0<\varepsilon_d\le 1\le D_d$
such that for $N \in \mathbb{N}$, $0 \le M \le N/4d$, the point
$s := (\sum_{j=1}^d f_i(jN))_{i=1}^d$ and the set
$S := \{(\sum_{j=1}^d f_i(jN+n_j))_{i=1}^d : n_j \in [-M,M]\cap\mathbb{Z}\}$
satisfy the box inclusion (7.5):
$s + \varepsilon_d \prod_i [-M/N^{i+1}, M/N^{i+1}] \subseteq S + D_d \prod_i [-(1/N^{i+1} + M^2/N^{i+2}), \dots]$.
Proof: Lemma 7.1 linearizes $S$; the linear model is the Vandermonde-type
integer matrix $VD$, whose invertibility gives a full sub-lattice
$v_d\mathbb{Z}^d \subseteq V\mathbb{Z}^d$ ($v_d = |\det VD|$, Vandermonde
determinant), so lattice points $\varepsilon_d$-fill the box (7.7)–(7.8).

**Section 8 (the algorithm).** Choose $N_k$ with (8.1) $N_{k+1} \ge (2k+1)N_k$
and (8.2) $N_{k+1}/N_k^\theta \to 0$ for every $\theta > 1$. Set
$M_k := \min(\lfloor N_k/4k\rfloor, \lfloor N_k^{1/2}\rfloor) \approx N_k^{1/2}$.
Let $m(d)$ be (inductively, least $> m(d-1)$) such that (7.17)
$D_{d}/N_k^{i+1} + D_{d}M_k^2/N_k^{i+2} \le \varepsilon_{d} M_{k+1}/N_{k+1}^{i+1}$
holds for all $1\le i\le d$, $k \ge m(d)$ — possible by (8.2). For
$k \ge m(1)$ let $d(k)$ be the unique $d$ with $m(d) \le k < m(d+1)$; note
$d(k) \le k$ (8.3). Set $\delta_{i,k} := \varepsilon_{d(k)} M_k / N_k^{i+1}$.

Build $(a_n)$ in blocks of length $d(k)$ at step $k$: having maintained the
invariant (8.5)
$x_i \in \sum_{l=m(1)}^{k-1}\sum_{j=1}^{d(l)} f_i(a_{n(l)+j}) + \sum_{l=k}^{\infty}\sum_{j=1}^{d(l)} f_i(jN_l) + [-\delta_{i,k}, \delta_{i,k}]$
for all $i$ with $m(i) \le k$ (when $m(i)=k$, *choose* the rational $x_i$
inside the interval, which is nonempty), apply Lemma 7.2 with $d = d(k)$,
$M = M_k$, $N = N_k$ — inclusion (7.16) $s_k + R_k \subseteq S_k + R_{k+1}$
holds because (7.17) holds for $k \ge m(d(k))$ — to find
$n_1,\dots,n_{d(k)} \in [-M_k, M_k]$; append $a_{n(k)+j} := jN_k + n_j$.
The invariant survives with $k+1$. Strict monotonicity: within a block,
$(j+1)N_k - jN_k = N_k > 2M_k$; across blocks, (8.1). Positivity:
$N_k - M_k > 0$. Summability: $a_n \gtrsim N_l$ on block $l$ with
$d(l) \le l$ terms, and $N_l$ grows superexponentially.
Finally $\delta_{i,k} \to 0$ ($\delta_{i,k} \le N_k^{1/2}/N_k^{i+1} \to 0$),
so the nested intervals force $\sum_n f_i(a_n) = x_i \in \mathbb{Q}$.

**Pole/exclusion bookkeeping (surfaced by formalization; the paper glosses
it).** $f_i(a_n) = 0$ at poles, i.e. when $t_j = -a_n$ for some $j \le i$;
since $(a_n)$ is strictly increasing this happens for at most $i$ values of
$n$. In the reduction, the partial-fraction identity fails at those finitely
many $n$, and the series $\sum_n 1/(a_n+t_j)$ skips its (at most one)
undefined term only when $t_j \notin \{-a_n\}$ — which is exactly the
exclusion in the theorem statement. The finite corrections are rational, so
the induction still closes; this needs careful Lean bookkeeping but no new
mathematics. Note the constructed $a_n = jN_k + n_j \ge N_k - M_k$ grows, so
for each fixed $i$ the poles affect only an explicitly finite prefix.

## Design decisions (deviations from the paper, all proof-simplifying)

1. **$N_k := 2^{k^2}$** instead of $(2k-1)!$ spliced with
   $\lfloor 2^{2^{\sqrt k}}\rfloor$. Check: (8.1) $N_{k+1}/N_k = 2^{2k+1} \ge 2k+1$;
   (8.2) $N_{k+1}/N_k^\theta = 2^{(1-\theta)k^2 + 2k + 1} \to 0$ for every
   $\theta > 1$. Everything downstream only uses (8.1), (8.2), and
   $M_k \approx N_k^{1/2}$, all satisfied. Enormously simpler in Lean.
2. **Existential constants.** $C_i$, $\varepsilon_d$, $D_d$, $v_d$ are all
   existentially quantified; never chase the paper's explicit values
   ($2^{10i}$, $d^{-10d^2}$, $(4d)^{10d^2}$). Compactness/crude bounds
   suffice.
3. **No operator $U$.** Replace the infinite matrix $U$ and
   $U\mathbb{Q}^\mathbb{N} = \mathbb{Q}^\mathbb{N}$ by the finite strong
   induction described in the Reduction above.
4. **Indexing.** Lean-side, `t : ℕ → ℚ` is 0-indexed with
   `|t j| ≤ (j : ℚ) + 1`, and `f i` (for `i : ℕ`, meaningful for `i ≥ 1`)
   uses factors `j < i`, i.e. `t 0, …, t (i-1)`. Paper index $i$ = Lean `i`.

## Module plan (Erdos266/)

| Module | Content | Status |
|---|---|---|
| `Glue.lean` | #266 negative answer from `RationalShifts` | **done** |
| `Enumeration.lean` | bijection `t : ℕ → ℚ`, `\|t j\| ≤ j+1` (greedy over a `Denumerable` enumeration) | **done** |
| `Defs.lean` | `f i x`, partial-fraction coefficients `m i j`, basic facts (`m i i ≠ 0`, the identity away from poles) | **done** |
| `Reduction.lean` | strong induction: `(∀ i ≥ 1, ∑ f i (a n) ∈ ℚ)` + monotone ⇒ `RationalShifts a` (with pole corrections; summability hypothesis turned out unnecessary) | **done** |
| `SlopeLemma.lean` | Lemma 7.1, existential constant (via telescoping products, no calculus; constant `3(i+1)²16^i`) | **done** |
| `LatticeLemma.lean` | Lemma 7.2 via `Matrix.vandermonde`; `ε_d` from invertibility, box inclusion (7.5) | — |
| `Growth.lean` | `N k = 2^(k^2)`, (8.1), (8.2)-consequences, `M k`, `m(d)`, `d(k)`, `δ i k`, (7.17) | — |
| `Algorithm.lean` | recursive block construction + invariant (8.5) | — |
| `Convergence.lean` | monotone/positive/summable; nested intervals ⇒ `∑ f i (a n) = x i` | — |
| `Main.lean` | assemble `erdos_266_rational_shifts` | — |

Suggested order of attack: Enumeration → Defs → Reduction (these three give a
complete conditional path from "the construction exists" to the Challenge),
then SlopeLemma → LatticeLemma → Growth → Algorithm → Convergence → Main.

## Risk register

- ~~Lemma 7.1~~ done, via a telescoping-product route with no calculus:
  `∏(N+n+tⱼ) - ∏(N+tⱼ) = n·∑ₖ(hybrid products)` gives the linear term
  exactly, and a single induction bounds every product against `N^k`.
- **Algorithm.lean** carries a recursive construction with a per-step choice
  from a set-inclusion; needs a careful recursion package (define the state
  as a structure, recurse with `Nat.rec`, extract via choice).
- **HasSum vs. ordered sums**: all series here have nonnegative terms after
  a finite prefix; stay in `HasSum`/`tsum` throughout (the Challenge already
  does) and never convert to ordered partial sums except inside the
  invariant, which is about finite partial sums anyway.
