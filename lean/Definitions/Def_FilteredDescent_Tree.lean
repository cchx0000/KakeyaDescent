import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Filtered descent — history tree (paper (131)–(155))

Finite model of the descent's history tree.  Nodes are finite words
(`List α`); the tree is a prefix-closed finite set of words.  The paper's
loads `u_γ` are stated here pointwise (at one spatial cell); the paper's
integrated identities follow by summation over the cells.

* `treeLeaves`: maximal words — the paper's terminal histories.
* `nodeAgg`: `W_a = Σ_{γ ∈ Desc(a)} u_γ`, paper (131)–(136).
* `treeLCA`: least common ancestor = longest common prefix.
* `Xroot`: root-cross pair mass `Σ_{a(γ,γ') = r∗} u_γ u_γ'`, LHS of (142).
* `Xdup` / `Xgeom`: the duplicate / geometric split, paper (143)–(147).
* `treeChildren`: children of a node in the prefix tree.
-/

namespace FilteredDescent

/-- Leaves = maximal elements of a prefix-closed finite node set. -/
def treeLeaves {α : Type} [DecidableEq α] (T : Finset (List α)) :
    Finset (List α) :=
  T.filter (fun l => ∀ l' ∈ T, l <+: l' → l' = l)

/-- Node aggregate `W_a = Σ_{γ ∈ Desc(a)} u_γ`.  Paper (131)–(136). -/
noncomputable def nodeAgg {α : Type} [DecidableEq α] (T : Finset (List α))
    (u : List α → ℝ) (a : List α) : ℝ :=
  ∑ γ ∈ treeLeaves T, if a <+: γ then u γ else 0

/-- Least common ancestor of two histories = their longest common prefix.
`γ.take k <+: γ'` holds for `k = 0`, so the set below is nonempty. -/
noncomputable def treeLCA {α : Type} [DecidableEq α] (γ γ' : List α) :
    List α :=
  γ.take (((Finset.range (γ.length + 1)).filter
    (fun k => γ.take k <+: γ')).max' ⟨0, by simp⟩)

/-- Root-cross pair mass `X^{root} = Σ_{a(γ,γ') = r∗} u_γ u_γ'`.
LHS of the root-cross gate, paper (142). -/
noncomputable def Xroot {α : Type} [DecidableEq α] (T : Finset (List α))
    (u : List α → ℝ) : ℝ :=
  ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
    if treeLCA γ γ' = [] then u γ * u γ' else 0

/-- Duplicate part: root-cross pairs ending in the same terminal tube.
Paper (143)–(147). -/
noncomputable def Xdup {α : Type} [DecidableEq α] (T : Finset (List α))
    (u : List α → ℝ) {n : ℕ} (termTube : List α → Fin n) : ℝ :=
  ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
    if treeLCA γ γ' = [] ∧ termTube γ = termTube γ' then u γ * u γ' else 0

/-- Geometric part: root-cross pairs ending in different terminal tubes. -/
noncomputable def Xgeom {α : Type} [DecidableEq α] (T : Finset (List α))
    (u : List α → ℝ) {n : ℕ} (termTube : List α → Fin n) : ℝ :=
  ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
    if treeLCA γ γ' = [] ∧ termTube γ ≠ termTube γ' then u γ * u γ' else 0

/-- Children of a node in the prefix tree. -/
def treeChildren {α : Type} [DecidableEq α] (T : Finset (List α))
    (a : List α) : Finset (List α) :=
  T.filter (fun b => a <+: b ∧ b.length = a.length + 1)

end FilteredDescent
