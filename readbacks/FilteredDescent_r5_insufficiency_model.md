## Read-back: `FilteredDescent.r5_insufficiency_model`

The declaration is a theorem in the `FilteredDescent` namespace. It takes one explicit natural number parameter $R$ together with one explicit hypothesis $h_R : 2 \le R$ (so $R$ is at least $2$). It then introduces two local definitions via `let`-bindings:

- $T$ is the finite set of lists of natural numbers
  $$T = \{[\,]\} \cup \{\, [k] \mid 0 \le k < R \,\},$$
  i.e. the empty list together with the $R$ one-element lists $[0], [1], \dots, [R-1]$.

- $u : \mathrm{List}(\mathbb{N}) \to \mathbb{R}$ is the function
  $$u(\gamma) = \begin{cases} 1 & \text{if } \gamma = [k] \text{ for some } k < R, \\ 0 & \text{otherwise,} \end{cases}$$
  i.e. it is $1$ exactly on the singleton lists with entry below $R$ and $0$ everywhere else. (The membership test is decidable because it is membership in a finite set.)

The theorem asserts the conjunction of three claims about this $T$ and $u$:

1. **Root-cross pair mass.** $X_{\mathrm{root}}(T, u) = R^2 - R$ (with $R$ cast to a real number). Here $X_{\mathrm{root}}$ is defined as the double sum
   $$X_{\mathrm{root}}(T, u) = \sum_{\gamma \in L} \sum_{\gamma' \in L} \begin{cases} u(\gamma)\, u(\gamma') & \text{if } \mathrm{LCA}(\gamma, \gamma') = [\,], \\ 0 & \text{otherwise,} \end{cases}$$
   where $L = \mathrm{treeLeaves}(T)$ is the set of $\sqsubseteq$-maximal elements of $T$ under the list-prefix order ($l \sqsubseteq l'$ meaning $l$ is a prefix of $l'$), and $\mathrm{LCA}(\gamma, \gamma')$ is the least common ancestor, computed as the longest common prefix: $\gamma$ truncated to the largest $k \le |\gamma|$ such that the first $k$ entries of $\gamma$ form a prefix of $\gamma'$. For this particular $T$, the empty list is a proper prefix of every singleton so it is not maximal, and each singleton $[k]$ is maximal; hence $L = \{[k] : k < R\}$. For distinct singletons $[i] \ne [j]$ the longest common prefix is $[\,]$, while for $i = j$ it is $[i]$ itself; so the sum effectively ranges over ordered pairs of distinct singletons, each contributing $u([i])\,u([j]) = 1 \cdot 1$.

2. **Total leaf mass.** $\sum_{\gamma \in L} u(\gamma) = R$.

3. **Unit leaf bound.** For every leaf $\gamma \in L$, $u(\gamma) \le 1$.

Remarks on implicit content: the definitions `treeLeaves` and `Xroot` require a `DecidableEq` instance on the element type; here it is instantiated at lists of natural numbers (inherited from decidable equality on $\mathbb{N}$). The hypothesis $2 \le R$ guarantees there are at least two distinct leaves, so the off-diagonal sum in (1) is over a nonempty index set. The theorem's proof body is omitted (it ends in `sorry`), so nothing is asserted about how the three claims are proved — only the three claims themselves are asserted.