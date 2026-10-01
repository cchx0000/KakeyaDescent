I have read both `mission_auditor.md` and the theorem file. I am working blind: I have not seen the paper, the mission pitch, or any informal description beyond what is in the Lean file itself. Below is my read-back of `FilteredDescent.ordered_cauchy_binet`, translating exactly what the code asserts.

---

**Read-back for `FilteredDescent.ordered_cauchy_binet`** (declared inside `namespace FilteredDescent`, so its full name is `FilteredDescent.ordered_cauchy_binet`):

The declaration asserts an identity of real numbers, universally quantified over natural numbers $n$ and $d$ (both implicit binders). It assumes the following hypotheses and data:

- $d \le n$ (hypothesis `hdn`);
- $0 < d$, i.e. $d \ge 1$ (hypothesis `hd`);
- $s$, a family of $n$ vectors in $\mathbb{R}^d$: for each index $i \in \{0, \dots, n-1\}$, $s_i$ is a $d$-tuple of reals, with $s_i(a)$ denoting its $a$-th coordinate;
- $w$, a real-valued weight $w_i$ attached to each index $i \in \{0, \dots, n-1\}$;
- every weight is nonneg: $w_i \ge 0$ for all $i$ (hypothesis `hw`).

Under these assumptions, the following equation holds. The left-hand side is a finite sum over **all** ordered $d$-tuples $U = (U_0, \dots, U_{d-1})$ of indices in $\{0, \dots, n-1\}$ — that is, over all functions $U : \{0,\dots,d-1\} \to \{0,\dots,n-1\}$, with repetitions allowed. For each such tuple $U$, the summand is the product of the weights of its entries times the square of a determinant:

$$\sum_{U} \left(\prod_{j=0}^{d-1} w_{U_j}\right) \cdot \left(\det S_U\right)^2,$$

where $S_U$ is the $d \times d$ real matrix whose $(a, b)$-entry is $s_{U_b}(a)$ — equivalently, the matrix whose $b$-th column is the vector $s_{U_b}$ (the vector of the family $s$ selected by the $b$-th entry of the tuple $U$).

The right-hand side is $d!$ (the factorial of $d$, cast from $\mathbb{N}$ to $\mathbb{R}$) multiplied by the determinant of the $d \times d$ matrix $M$ whose $(a, b)$-entry is

$$M_{a,b} = \sum_{i=0}^{n-1} w_i \cdot s_i(a) \cdot s_i(b),$$

i.e. the weighted Gram matrix $M = \sum_i w_i\, s_i s_i^\top$ built from the same vectors $s_i$ and weights $w_i$.

Fine print and edge cases:

- The case $d = 0$ is excluded by the hypothesis $0 < d$.
- The inequality $d \le n$ is an explicit hypothesis; nothing is asserted for $d > n$.
- If $n = 0$, the hypotheses $d \le n$ and $0 < d$ contradict each other, so the statement holds vacuously for $n = 0$ (there is no $d$ satisfying the hypotheses).
- The sum on the left ranges over *all* ordered tuples, including tuples with repeated entries. (The file's own module comment claims that tuples with repeated entries contribute $0$ because the matrix then has a repeated column; that claim appears in the comment, not in the code itself.)
- The declaration carries no proof: its body is `by sorry`.

---

This is my complete read-back, written blind from the Lean code and `mission_auditor.md` only.