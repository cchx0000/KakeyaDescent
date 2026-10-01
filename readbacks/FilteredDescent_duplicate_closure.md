**Read-back for `FilteredDescent.duplicate_closure`**

This theorem is implicitly quantified over a type $\alpha$ (with decidable equality, taken as a typeclass hypothesis) and implicit natural numbers $n$ and $m$. Its explicit arguments and hypotheses are: a finite set $T$ of finite lists over $\alpha$; the hypothesis `hroot` that the empty list $[]$ belongs to $T$ (so $T$ is nonempty); the hypothesis `hprefix` that $T$ is prefix-closed, i.e. every prefix $p$ of every word $l \in T$ is itself in $T$; a real-valued function $u$ on lists; the hypothesis `hu` that $u_\gamma \geq 0$ for every leaf $\gamma$ of $T$ (no condition is imposed on $u$ at non-leaf words, and indeed $u$ is only ever evaluated at leaves); a function $\tau$ (`termTube`) assigning to each word a tube index in $\mathrm{Fin}\,n = \{0, \dots, n-1\}$; a function $\kappa$ (`carrier`) assigning to each word a carrier index in $\mathrm{Fin}\,m$; real numbers $A, B$ with `hA` : $A \geq 0$ and `hB` : $B \geq 0$; and the hypothesis `hagg` that for **every** tube index $t \in \mathrm{Fin}\,n$ and **every** carrier index $c \in \mathrm{Fin}\,m$,

$$\sum_{\substack{\gamma \text{ a leaf of } T \\ \tau(\gamma) = t,\ \kappa(\gamma) = c}} u_\gamma \;\leq\; A \cdot B,$$

where the sum ranges over the subset of leaves selected by the filter $\{\gamma \in \mathrm{leaves}(T) : \tau(\gamma) = t \land \kappa(\gamma) = c\}$ (for $(t,c)$ hit by no leaf this sum is $0$, and $0 \leq A\cdot B$ then follows from `hA`, `hB`).

The auxiliary notions, unfolded from the imported definitions, are:

- $\mathrm{leaves}(T)$ (`treeLeaves`) is the set of $\preceq$-maximal words of $T$: those $l \in T$ such that every $l' \in T$ having $l$ as a prefix satisfies $l' = l$.
- $\mathrm{lca}(\gamma, \gamma')$ (`treeLCA`) is the longest common prefix of the two words, computed as $\gamma.\mathrm{take}(k)$ for the largest $k \in \{0, \dots, |\gamma|\}$ with $\gamma.\mathrm{take}(k)$ a prefix of $\gamma'$ (this set always contains $0$, since the empty word is a prefix of everything).
- $X^{\mathrm{root}}(T, u) = \sum_{\gamma, \gamma' \in \mathrm{leaves}(T)} [\mathrm{lca}(\gamma,\gamma') = []] \cdot u_\gamma u_{\gamma'}$, i.e. the sum of $u_\gamma u_{\gamma'}$ over leaf pairs whose least common ancestor is the root $[]$, and $0$ for all other pairs.
- $X^{\mathrm{dup}}(T, u, \tau)$ is the same double sum restricted by the additional condition $\tau(\gamma) = \tau(\gamma')$ (root-cross pairs ending in the same terminal tube).
- $X^{\mathrm{geom}}(T, u, \tau)$ is the same double sum restricted instead by $\tau(\gamma) \neq \tau(\gamma')$ (root-cross pairs ending in different terminal tubes).

The conclusion is a conjunction of two claims. First, the exact splitting identity

$$X^{\mathrm{root}}(T, u) \;=\; X^{\mathrm{geom}}(T, u, \tau) \;+\; X^{\mathrm{dup}}(T, u, \tau),$$

which the code asserts termwise via the `if` conditions: for a leaf pair with $\mathrm{lca} \neq []$ all three summands are $0$, while for a pair with $\mathrm{lca} = []$ exactly one of the conditions $\tau(\gamma) = \tau(\gamma')$ / $\tau(\gamma) \neq \tau(\gamma')$ holds (equality on $\mathrm{Fin}\,n$ is decidable and exhaustive), so the $X^{\mathrm{root}}$ summand $u_\gamma u_{\gamma'}$ appears in precisely one of the two parts. Second, the duplicate bound

$$X^{\mathrm{dup}}(T, u, \tau) \;\leq\; m \cdot (A \cdot B) \cdot \sum_{\gamma \in \mathrm{leaves}(T)} u_\gamma,$$

where $m$ is the real cast of the implicit natural number $m$ (the number of carrier indices, i.e. the cardinality of the codomain of $\kappa$), not an independent hypothesis.

Degenerate and edge cases made explicit: if $n = 0$ then $\mathrm{Fin}\,n$ is empty and, since the word $[] : \mathrm{List}\,\alpha$ always exists, no function $\tau : \mathrm{List}\,\alpha \to \mathrm{Fin}\,0$ exists — so the theorem is vacuously true; likewise if $m = 0$ no carrier function $\kappa$ exists and the statement is vacuous. The contentful case therefore has $n, m \geq 1$. The hypothesis `hroot` rules out $T = \emptyset$. Nothing is assumed about $u$ off the leaves, about distinctness of leaves, or about the tree being anything beyond prefix-closed with $[] \in T$. The declaration's proof is `by sorry` (an unproved draft); what is rendered above is exactly what the statement asserts.