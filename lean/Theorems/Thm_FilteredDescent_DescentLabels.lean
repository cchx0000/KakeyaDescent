import Definitions.Def_FilteredDescent_Tree
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Lex

/-!
# Filtered descent — descent labels and the well-founded order (paper (135))

Paper (135) introduces the well-founded analytic order for proper
predecessors of the history tree:

  `(|I|, ℓ(χ), n)`

ordered lexicographically with support outermost, confluence length next
and Cartan height last.  A strict confluence predecessor lowers `ℓ(χ)`,
a proper face lowers support, and a Cartan predecessor lowers `n`.
Supports of size at most one are trivial latching faces; the minimal
nontrivial leaf state is `(2, 0, 0)`, where the planar Córdoba estimate
applies.

This file provides:

* `DescentLt`: the strict lexicographic order on `ℕ × ℕ × ℕ`, with a real
  well-foundedness proof (`DescentLt.wf`) via mathlib's lexicographic
  product instances — no axiom, no sorry.
* `DescentLabels`: the named interface saying the label assignment
  strictly decreases along tree edges (paper (135)).
* `DescentLt.of_strict_prefix`: labels strictly decrease along any strict
  prefix chain inside the tree (proved from `DescentLabels` by induction
  on the connecting word).

## Honesty notes

* The *construction* of the label assignment from the unified tower
  (§§6–9: support faces, confluence type `χ(a)`, Cartan height) is NOT
  built here.  `lab` is an abstract node labelling; `DescentLabels` is
  the named hypothesis recording the decrease property the paper's
  construction guarantees.  The descent induction (Stream D, M3) takes
  it as an explicit hypothesis.
* The leaf estimate at the minimal state `(2, 0, 0)` (paper (53)) is the
  named hypothesis `leaf_bound` in the induction file, not proved here.
-/

namespace FilteredDescent

/-- The descent key: a triple `( |I|, ℓ(χ), n )` viewed in the iterated
lexicographic product, so that `<` is the paper's lexicographic order
(135) with support outermost. -/
def descentKey : (ℕ × ℕ × ℕ) → Lex (Lex (ℕ × ℕ) × ℕ) :=
  fun p => toLex (toLex (p.1, p.2.1), p.2.2)

/-- Paper (135): the strict lexicographic order on descent labels. -/
def DescentLt : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Prop :=
  InvImage (· < ·) descentKey

/-- The lexicographic order on `ℕ³` is well-founded.  Real proof: it is
the inverse image of `<` on the iterated lexicographic product, which
is well-founded by mathlib's `WellFoundedLT` instances for `Lex`
products over `ℕ`. -/
theorem DescentLt.wf : WellFounded DescentLt := by
  have h : WellFounded (InvImage (· < ·) descentKey) :=
    InvImage.wf descentKey wellFounded_lt
  exact h

/-- Transitivity, inherited from `<` on the lexicographic product. -/
theorem DescentLt.trans {p q r : ℕ × ℕ × ℕ} :
    DescentLt p q → DescentLt q r → DescentLt p r := fun h1 h2 =>
  lt_trans h1 h2

/-- Irreflexivity, inherited from `<` on the lexicographic product. -/
theorem DescentLt.irrefl (p : ℕ × ℕ × ℕ) : ¬ DescentLt p p := fun h =>
  lt_irrefl _ h

/-- The node-level well-founded relation used by the descent induction:
`a` precedes `b` when its label is lexicographically smaller. -/
theorem DescentLt.wf_node {α : Type} (lab : List α → ℕ × ℕ × ℕ) :
    WellFounded (fun a b : List α => DescentLt (lab a) (lab b)) :=
  InvImage.wf lab DescentLt.wf

/-- Paper (135): the label assignment strictly decreases along every
tree edge.  A strict confluence predecessor lowers `ℓ(χ)`, a proper face
lowers support, a Cartan predecessor lowers `n`.

Named hypothesis: the tree construction of §§6–9 that produces such a
labelling is not formalized here. -/
def DescentLabels {α : Type} [DecidableEq α] (T : Finset (List α))
    (lab : List α → ℕ × ℕ × ℕ) : Prop :=
  ∀ a ∈ T, ∀ b ∈ treeChildren T a, DescentLt (lab b) (lab a)

/-- Labels strictly decrease along any strict prefix chain inside the
tree.  Proved from `DescentLabels` by induction on the connecting word
`t` with `c = a ++ t`: each letter appends one tree edge, and `hlab`
fires at every step. -/
theorem DescentLt.of_strict_prefix {α : Type} [DecidableEq α]
    (T : Finset (List α)) (lab : List α → ℕ × ℕ × ℕ)
    (hlab : DescentLabels T lab)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    {a c : List α} (ha : a ∈ T) (hc : c ∈ T)
    (hpc : a <+: c) (hne : a ≠ c) :
    DescentLt (lab c) (lab a) := by
  obtain ⟨t, ht⟩ := hpc
  have key : ∀ t : List α, ∀ a : List α, a ∈ T → a ++ t ∈ T → a ≠ a ++ t →
      DescentLt (lab (a ++ t)) (lab a) := by
    intro t
    induction t with
    | nil =>
        intro a _ _ hne
        exfalso
        exact hne (by simp)
    | cons x t' ih =>
        intro a ha hmem hne
        -- one tree edge: `b = a ++ [x]`
        set b : List α := a ++ [x] with hb
        have hbt : b ++ t' = a ++ (x :: t') := by
          simp [hb, List.append_assoc]
        have hb_pre : b <+: a ++ (x :: t') := ⟨t', hbt⟩
        have hbT : b ∈ T := hprefix _ hmem b hb_pre
        have hmem' : b ∈ treeChildren T a := by
          rw [treeChildren, Finset.mem_filter]
          refine ⟨hbT, ⟨[x], hb⟩, ?_⟩
          simp [hb]
        have h1 : DescentLt (lab b) (lab a) := hlab a ha b hmem'
        by_cases ht'nil : t' = []
        · -- `a ++ (x :: t') = b`: single step
          have heq : a ++ (x :: t') = b := by rw [ht'nil]
          rw [heq]
          exact h1
        · -- longer chain: recurse below `b`, then transitivity
          have h2 : DescentLt (lab (b ++ t')) (lab b) :=
            ih b hbT (by rwa [← hbt] at hmem) (by
              intro hcon
              apply ht'nil
              have hlen := congrArg List.length hcon
              simp only [List.length_append] at hlen
              have h0 : t'.length = 0 := by omega
              exact List.length_eq_zero_iff.mp h0)
          rw [hbt] at h2
          exact DescentLt.trans h2 h1
  have hmem : a ++ t ∈ T := by rw [ht]; exact hc
  have hne' : a ≠ a ++ t := by rwa [ht]
  have := key t a ha hmem hne'
  rwa [ht] at this

end FilteredDescent
