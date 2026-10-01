## Motivation

The Kakeya problem asks how small a set in $\mathbb{R}^d$ can be while containing a unit line segment in every direction. Its finite-scale form — bounding the overlap (incidence) of thickened tubes pointing in separated directions — is the engine behind restriction theory, Bochner–Riesz, and Falconer-type problems. The paper formalized here develops a **filtered descent**: a multi-scale ledger that tracks tube incidences through successive refinements, closing a recurrence on the incidence count. Readers who care about Kakeya-type maximal estimates and their applications to harmonic analysis are the audience.

Timeline: Córdoba's planar estimate [2] handles $d = 2$; the sticky Kakeya theory of Wang–Zahl [7] and the sticky/non-sticky reduction [10] handle $d = 3$; a companion manuscript [9] supplies the marked 4D sticky input for $d = 4$. Dimensions $d \geq 5$ remain open — this mission does not claim them.

## Setting

Fix a finite family $\mathcal{T}$ of direction-separated $\delta$-tubes in $\mathbb{R}^d$, each carrying a shading $Y(T) \subset T$ (the "physical" incidence data). Write $|Y(T)|$ for the shading volume, $|\bigcup_T Y(T)|$ for the union volume, and $\mu = \sum_T |Y(T)| / |\bigcup_T Y(T)|$ for the average multiplicity. The descent organizes tubes into packets and histories: an ordered packet is a tuple $U = (U_1, \dots, U_r)$ weighted by $\prod_j w(U_j)$; a history $\gamma$ is a word recording successive refinements; the load $u_\gamma \geq 0$ is the mass carried by that history. For a node $a$ in the history tree, $W_a = \sum_{\gamma \supset a} u_\gamma$ aggregates descendant loads. The least common ancestor $a(\gamma, \gamma')$ of two histories is their longest common prefix; pairs with $a(\gamma,\gamma') = r^*$ (the root) are the **root-cross** pairs, whose mass $X^{\mathrm{root}} = \sum_{a(\gamma,\gamma') = r^*} u_\gamma u_{\gamma'}$ drives the descent. A quantity $X$ is **subpower-bounded** by $Y$, written $X \lesssim_\delta Y$, if $X \leq C \delta^{-\varepsilon} Y$ for every $\varepsilon > 0$ (with $C$ independent of $\delta$).

## Formalization targets

### Goal — scalar filtered-descent closure
$$\sum_T |Y(T)| \lesssim_\delta \Bigl|\bigcup_T Y(T)\Bigr|$$
for $d \in \{2, 3, 4\}$, assuming the three imported analytic estimates below and $\lambda_{\mathrm{in}}^{-1} = \delta^{-o(1)}$. This is the paper's §13.2: the descent closes and the incidence count follows.

### Supporting — root-cross gate
$$X^{\mathrm{root}} \lesssim_\delta B^{\mathrm{pred}} \cdot \int N$$
at each descent stage, from the duplicate closure (unconditional) plus the per-dimension analytic assembly.

## Significance

The result gives a unified incidence bound for shaded tube families in dimensions $2$–$4$ via a descent that is robust to the sticky/non-sticky dichotomy. Formalizing it produces the first machine-checked ledger of a modern Kakeya descent: the finite packet calculus (R5, Cauchy–Binet, insertion kernels), the history-tree combinatorics (LCA reduction, duplicate closure), and the conditional analytic closure — each as an independent, reusable statement. Status honesty: the paper's proofs are not machine-checked; the deep analytic inputs ([2], [7], [9], [10]) are taken as explicit named hypotheses, and the descent assembly is the open proof obligation. The typed Hall-capacity comparison and $d \geq 5$ are excluded.

## Difficulty

The naive approach — bounding each history's load separately (chartwise R5) and summing — fails: the paper's one-point model (§10.5) shows $R$ unit-mass histories in one tube give $X^{\mathrm{root}} = R^2 - R$ while every chart satisfies the unit bound, so no $R$-independent estimate follows. The descent instead controls only root-cross pairs, splits them into duplicate and geometric parts, and closes the duplicate part via a common-source (carrier) argument. The geometric part requires the full per-dimension analytic input; there is no elementary substitute.

## Formalization scope

Finite models throughout: tubes indexed by `Fin n`, packets by `Fin r → Fin n`, histories by `List α` in a prefix-closed `Finset`. Loads are pointwise (one spatial cell); the paper's integrated identities follow by summation. Subpower bounds quantify $C$ after $\varepsilon$ (uniform in $\delta$). Division by zero returns `0` (Lean total functions); the input predicates are unsatisfiable on degenerate (empty-shading) data, as intended. Needed: finite-sum manipulation, Gram determinants, basic tree combinatorics. The packet/kernel/tree layers are reusable for any filtered-descent formalization. Contributions welcome: proofs of the milestone theorems, sharper finite models, the $d \geq 5$ gate.

## Selected references

- Chenxi Cai, *Filtered Descent for the Physical Kakeya Incidence*, 2026. https://cchx0000.github.io/papers/filtered-descent-physical-kakeya/filtered-descent-physical-kakeya.pdf
- A. Córdoba, *The Kakeya maximal function and the spherical summation multipliers*, Amer. J. Math. 1977. [2]
- H. Wang, J. Zahl, *Volume estimates for the set of points where a Kakeya maximal function is large*, 2024. [7]
- Unpublished companion manuscript on the marked 4D sticky estimate. [9]
- Sticky/non-sticky reduction for Kakeya. [10]
