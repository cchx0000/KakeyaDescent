Read-backs for each declaration in `Def_FilteredDescent_Tree.lean` (namespace `FilteredDescent`), based solely on the code:

---

**FilteredDescent.treeLeaves**

Given an arbitrary type $\alpha$ with decidable equality and a finite set $T$ of finite lists over $\alpha$, `treeLeaves` returns the sub-finset of $T$ consisting of those lists $l$ such that every list $l'$ in $T$ of which $l$ is a prefix (written $l \prec_+ l'$) is equal to $l$ itself — i.e., the prefix-maximal elements of $T$. The definition places no requirement on $T$ (in particular it does not check that $T$ is prefix-closed); if $T$ is empty, the result is empty. Maximality is with respect to the prefix relation only, so a short list can be a "leaf" as long as no list in $T$ strictly extends it.

---

**FilteredDescent.nodeAgg**

Given an arbitrary type $\alpha$ with decidable equality, a finite set $T$ of finite lists over $\alpha$, a real-valued function $u$ on finite lists over $\alpha$, and a list $a$, `nodeAgg` returns the real number $\sum_{\gamma} u_\gamma$, where the sum ranges over the prefix-maximal elements $\gamma$ of $T$ (as computed by `treeLeaves`) such that $a$ is a prefix of $\gamma$; leaves not extending $a$ contribute $0$ rather than being excluded from the sum. If $a$ is a prefix of no leaf of $T$ (for instance if $T$ is empty, or $a$ is unrelated to $T$), the value is $0$. Note the sum is over leaves of $T$ only, not over all of $T$, and no hypothesis relates $a$ to $T$.

---

**FilteredDescent.treeLCA**

Given an arbitrary type $\alpha$ with decidable equality and two finite lists $\gamma, \gamma'$ over $\alpha$, `treeLCA` is computed as follows: form the finite set of natural numbers $k$ with $0 \le k \le |\gamma|$ (i.e. $k$ in $\{0, 1, \dots, |\gamma|\}$) such that the list of the first $k$ entries of $\gamma$ is a prefix of $\gamma'$; take the largest such $k$ (the set is nonempty because $k = 0$ always qualifies, since the empty list is a prefix of every list — this is discharged by the `by simp` proof); then return the first $k$ entries of $\gamma$. The result is always a prefix of $\gamma$; it is the empty list exactly when $\gamma$ and $\gamma'$ have no common first entry (or $\gamma$ is empty), and it equals $\gamma$ itself when $\gamma$ is a prefix of $\gamma'$. Note the computation is not syntactically symmetric: it truncates $\gamma$ to the longest length at which its initial segment still prefixes $\gamma'$.

---

**FilteredDescent.Xroot**

Given an arbitrary type $\alpha$ with decidable equality, a finite set $T$ of finite lists over $\alpha$, and a real-valued function $u$ on finite lists over $\alpha$, `Xroot` returns the double sum over all pairs $(\gamma, \gamma')$ of prefix-maximal elements (leaves) of $T$ of the quantity $u_\gamma \cdot u_{\gamma'}$ when `treeLCA γ γ'` equals the empty list, and $0$ otherwise. In other words, it sums the products of the $u$-values over exactly those ordered leaf pairs whose longest common prefix is empty. If $T$ has no leaves, or no two leaves have empty longest common prefix, the value is $0$; diagonal pairs $(\gamma, \gamma)$ contribute $u_\gamma^2$ only when the leaf $\gamma$ is itself the empty list (since otherwise its longest common prefix with itself is $\gamma \ne []$).

---

**FilteredDescent.Xdup**

Given an arbitrary type $\alpha$ with decidable equality, a finite set $T$ of finite lists over $\alpha$, a real-valued function $u$ on finite lists over $\alpha$, an implicit natural number $n$, and a function $\mathrm{termTube}$ from finite lists over $\alpha$ to $\mathrm{Fin}\,n$ (the type of natural numbers less than $n$), `Xdup` returns the double sum over all ordered pairs $(\gamma, \gamma')$ of leaves of $T$ of $u_\gamma \cdot u_{\gamma'}$ when both `treeLCA γ γ' = []` and $\mathrm{termTube}(\gamma) = \mathrm{termTube}(\gamma')$ hold, and $0$ otherwise. That is, it is the same pair-sum as `Xroot` but restricted to pairs whose longest common prefix is empty and which are additionally assigned the same value by $\mathrm{termTube}$. Note $\mathrm{termTube}$ is defined on all lists, but is only ever evaluated at leaves here; if $n = 0$ then $\mathrm{Fin}\,n$ is empty, so no such $\mathrm{termTube}$ can exist and the declaration is vacuous in that case.

---

**FilteredDescent.Xgeom**

Given exactly the same arguments as `Xdup` (an arbitrary type $\alpha$ with decidable equality, a finite set $T$ of lists over $\alpha$, a real-valued $u$, an implicit $n : \mathbb{N}$, and $\mathrm{termTube} : \mathrm{List}\,\alpha \to \mathrm{Fin}\,n$), `Xgeom` returns the double sum over all ordered leaf pairs $(\gamma, \gamma')$ of $T$ of $u_\gamma \cdot u_{\gamma'}$ when both `treeLCA γ γ' = []` and $\mathrm{termTube}(\gamma) \ne \mathrm{termTube}(\gamma')$ hold, and $0$ otherwise. It differs from `Xdup` only in the second conjunct of the summation condition: inequality of the $\mathrm{termTube}$ values rather than equality. Consequently, for each fixed ordered leaf pair, at most one of the summands of `Xdup` and `Xgeom` is nonzero, and the pair contributes to exactly one of them (when the longest common prefix is empty) or to neither (when it is nonempty).

---

**FilteredDescent.treeChildren**

Given an arbitrary type $\alpha$ with decidable equality, a finite set $T$ of finite lists over $\alpha$, and a list $a$, `treeChildren` returns the sub-finset of $T$ consisting of those lists $b$ such that $a$ is a prefix of $b$ and the length of $b$ is exactly one more than the length of $a$. No hypothesis requires $a$ itself to belong to $T$; if $a \notin T$ or nothing in $T$ extends $a$ by exactly one entry, the result is empty.