**Read-back for `FilteredDescent.unweighted_projection_false`:**

This theorem is a closed statement (no free variables, hypotheses, or binders) asserting a single numerical inequality about one concrete example. It first fixes, by local definition, a weight function $w$ on the two-element type $\mathrm{Fin}\,2$ given by $w(i) = 1$ for both $i$, and an event $A$ consisting of the single ordered $1$-tuple $U_0 \colon \mathrm{Fin}\,1 \to \mathrm{Fin}\,2$ with $U_0(j) = 0$ for the unique slot $j$. It uses two auxiliary notions, expanded here inline: the *packet law* assigns to each tuple $U$ the value $\prod_j w(U_j)$ divided by $(\sum_i w_i)^r$ (here $r = 1$, the number of slots), and the *retained mass* of an event $A$ is the sum of the packet-law values over the tuples in $A$.

Concretely: the total weight is $W = \sum_{i \in \mathrm{Fin}\,2} w_i = 2$; the packet law at the unique tuple $U_0$ is $\frac{w(0)}{W^1} = \frac{1}{2}$; hence the retained mass of $A$ is $\frac{1}{2}$ (a sum over a singleton). The left-hand side of the asserted inequality is the ratio

$$\frac{\sum_{U \in A} \bigl(\text{if } U_0 = 0 \text{ then } \mathrm{packetLaw}(w, U) \text{ else } 0\bigr)}{\mathrm{retainedMass}(w, A)},$$

which evaluates as follows: since $A = \{U_0\}$ and $U_0(0) = 0$, the indicator is true, the numerator is $\frac{1}{2}$, and dividing by the retained mass $\frac{1}{2}$ gives $1$. The right-hand side is $w(0)/W = \frac{1}{2}$. The theorem therefore asserts, literally,

$$1 \neq \tfrac{1}{2}.$$

Notes on what the code does and does not say: both divisions are by nonzero quantities ($\frac{1}{2}$ and $2$ respectively), so no degenerate total-function behavior (division by zero) is exercised here. The inequality is the exact negation of equality between the two real numbers — the statement claims they differ, nothing about how much or why. There are no edge cases from quantification because nothing is quantified: $w$ and $A$ are fixed concrete objects, not arbitrary instances. The declaration carries no hypotheses, so there is no way for it to hold vacuously.