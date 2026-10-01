I have read the auditor instructions and the Lean file. I have not consulted any other files. Here are the read-backs.

---

**Read-back for `margLaw`**

For any natural numbers $m$ and $n$ (implicitly quantified, including the degenerate cases $m = 0$ or $n = 0$), any real-valued function $P$ defined on full assignments — i.e. on all functions from the $m$ slots $\{0, \dots, m-1\}$ to the $n$ values $\{0, \dots, n-1\}$ — and any finite set $A$ of slots, the declaration defines a new real-valued function on full assignments. Given a full assignment $x$, its value is the finite sum, over all full assignments $y$, of $P(y)$ when $y$ agrees with $x$ on every slot $a \in A$, and $0$ when $y$ disagrees with $x$ on at least one slot of $A$:

$$\mathrm{margLaw}(P, A)(x) = \sum_{y} \begin{cases} P(y) & \text{if } y(a) = x(a) \text{ for all } a \in A, \\ 0 & \text{otherwise.} \end{cases}$$

In particular the value at $x$ depends only on the restriction of $x$ to $A$. Edge cases: if $A$ is empty, the agreement condition is vacuous and the value is the total sum $\sum_y P(y)$ regardless of $x$; if $A$ is the set of all slots, only $y = x$ contributes and the value is $P(x)$; if $m > 0$ and $n = 0$ there are no assignments at all, so the sum is over the empty type and the value is $0$. No hypothesis is placed on $P$ — it need not be nonnegative, need not sum to $1$, and may be identically zero (in which case the marginal is identically zero).

---

**Read-back for `insKernel`**

For any natural numbers $m$ and $n$, any real-valued function $P$ on full assignments (functions from the $m$ slots to the $n$ values), and any two finite sets of slots $A$ and $B$, the declaration defines a real-valued function of *two* full assignments. Despite the argument names $x_B$ and $x_A$, both arguments are full assignments $x_B, x_A : \{0,\dots,m-1\} \to \{0,\dots,n-1\}$ — the code does not restrict them to $B$ or $A$, and it imposes no requirement that $A \subseteq B$. The value is defined by cases: if $x_B$ and $x_A$ agree on every slot $a \in A$ **and** the marginal $\mathrm{margLaw}(P, A)(x_A)$ is nonzero, the value is the quotient

$$\frac{\mathrm{margLaw}(P, B)(x_B)}{\mathrm{margLaw}(P, A)(x_A)} = \frac{\sum_{y \text{ agrees with } x_B \text{ on } B} P(y)}{\sum_{y \text{ agrees with } x_A \text{ on } A} P(y)};$$

otherwise — i.e. if $x_B$ and $x_A$ disagree on some slot of $A$, or if the denominator $\mathrm{margLaw}(P, A)(x_A)$ equals $0$ — the value is $0$. Because the denominator is checked to be nonzero in the branch where division occurs, the division never hits a zero denominator; the numerator is unrestricted and may be zero or negative since $P$ is arbitrary. Edge cases: if $A$ is empty, the agreement condition holds vacuously and the denominator is the total mass $\sum_y P(y)$ (the value is $0$ whenever that total mass is $0$); if $B$ is empty, the numerator is the total mass; if $x_B = x_A$ the agreement condition is automatic but the nonzero-denominator check still applies. The declaration is noncomputable and carries no positivity, normalization, or subset hypotheses.