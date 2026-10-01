I have read both files and the auditor instructions. Here is my blind read-back, based solely on what the Lean code literally asserts.

---

**Read-back for `FilteredDescent.kernel_chain_confluence`:**

Fix implicit natural numbers $m$ and $n$. Let $P$ be a real-valued function on all assignments $x : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$ (i.e. functions from $m$ slots to values in an $n$-element type), satisfying the hypothesis $P(x) \ge 0$ for every $x$. Let $A, B, C$ be finite sets of slots with $A \subseteq B$ and $B \subseteq C$, and let $x_C, x_A$ be two full assignments (functions $\mathrm{Fin}\,m \to \mathrm{Fin}\,n$). Two auxiliary notions from the imported definitions, expanded inline: the *marginal*
$$\operatorname{margLaw}_P(A)(x) = \sum_{y : \mathrm{Fin}\,m \to \mathrm{Fin}\,n} \begin{cases} P(y), & \text{if } y(a) = x(a) \text{ for all } a \in A, \\ 0, & \text{otherwise,} \end{cases}$$
the total $P$-weight of all assignments agreeing with $x$ on the slots of $A$ (hence depending on $x$ only through its values on $A$); and the *insertion kernel*
$$K_{A,B}(x_B \mid x_A) = \operatorname{insKernel}_P(A,B)(x_B, x_A) = \begin{cases} \dfrac{\operatorname{margLaw}_P(B)(x_B)}{\operatorname{margLaw}_P(A)(x_A)}, & \text{if } \bigl(\forall a \in A,\ x_B(a) = x_A(a)\bigr) \text{ and } \operatorname{margLaw}_P(A)(x_A) \neq 0, \\ 0, & \text{otherwise,} \end{cases}$$
which is defined to be exactly $0$ (not a ratio) whenever the two assignments disagree anywhere on $A$ or the conditioning marginal vanishes. The theorem asserts the conjunction of two claims. **(1) Chain rule:**
$$K_{A,C}(x_C \mid x_A) = K_{B,C}(x_C \mid x_C)\cdot K_{A,B}(x_C \mid x_A),$$
where note the middle factor $K_{B,C}$ is evaluated with the *same* assignment $x_C$ in both of its argument positions. **(2) Confluence of insertion order:** for all slots $i, j \in \mathrm{Fin}\,m$ satisfying $i \notin A$, $j \notin A$, and $i \neq j$, both of the following equations hold:
$$K_{A,\,A\cup\{i,j\}}(x_C \mid x_A) = K_{A\cup\{i\},\,A\cup\{i,j\}}(x_C \mid x_C)\cdot K_{A,\,A\cup\{i\}}(x_C \mid x_A)$$
and
$$K_{A,\,A\cup\{i,j\}}(x_C \mid x_A) = K_{A\cup\{j\},\,A\cup\{i,j\}}(x_C \mid x_C)\cdot K_{A,\,A\cup\{j\}}(x_C \mid x_A),$$
i.e. inserting slot $i$ then slot $j$, or slot $j$ then slot $i$, both factor the same kernel $K_{A,\,A\cup\{i,j\}}(x_C \mid x_A)$ (again with the intermediate factor taking $x_C$ in both argument positions). Fine print: the nonnegativity hypothesis on $P$ and the inclusions $A \subseteq B \subseteq C$ are hypotheses of the whole conjunction, but claim (2) never mentions $B$ or $C$; the side conditions $i \notin A$, $j \notin A$, $i \neq j$ are hypotheses of claim (2) only. Degenerate inputs are all permitted by the quantifiers: $m = 0$ or $n = 0$ (sums over empty assignment types are $0$), empty or equal slot sets $A, B, C$, and assignments $x_C, x_A$ disagreeing on $A$ (in which case both sides of the chain rule are $0$, since the kernel is defined to return $0$ on disagreement). The declaration's proof is `by sorry` — the statement is admitted, not proved.