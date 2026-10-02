import Theorems.Thm_FilteredDescent_DescentLabels
import Theorems.Thm_FilteredDescent_DescentTree
import Mathlib.Data.Finset.Card

/-!
# Filtered descent — faithful descent state (paper §§6–9, (135))

The faithful descent state for the §§6–9 history-tree construction.
A state has three components, and the (135) label is the lexicographic
triple

  `(|I|, ℓ(χ), n)`

with support size outermost, confluence length next, and Cartan height
last:

* `support I`: a finset of tube indices (the "face" support); a proper
  face step strictly shrinks `I`, lowering `|I|`;
* `confl`: the confluence word (reduced insertion history); a strict
  confluence predecessor shortens it, lowering `ℓ(χ)`;
* `cartan`: the Cartan/root–Moore height; a Cartan predecessor lowers it.

Supports of size at most one are trivial latching faces; the minimal
nontrivial leaf state is `(2, 0, 0)`.

This file defines the state, the label, and the three step types, and
proves each step strictly decreases the (135) label — the foundation
for the well-founded recursion that builds the real history tree.
The symmetric model (`Thm_FilteredDescent_DescentTree.lean`) is the
special case where the support is constantly `univ` (so face steps
never occur).
-/

namespace FilteredDescent

/-- Faithful descent state (paper §§6–9): support, confluence word,
Cartan height.  `α` is the mark type for confluence steps. -/
structure DescentState (α : Type) (n : ℕ) where
  support : Finset (Fin n)
  confl : List α
  cartan : ℕ

/-- The (135) label: `(|I|, ℓ(χ), n)`, lexicographically ordered. -/
def descentLabel {α : Type} {n : ℕ} (s : DescentState α n) : ℕ × ℕ × ℕ :=
  (s.support.card, s.confl.length, s.cartan)

/-- The (135) strict order on states, via the label. -/
def DescentStateLt {α : Type} {n : ℕ} (s t : DescentState α n) : Prop :=
  DescentLt (descentLabel s) (descentLabel t)

/-- The (135) order on states is well-founded. -/
theorem DescentStateLt.wellFounded {α : Type} {n : ℕ} :
    WellFounded (@DescentStateLt α n) :=
  InvImage.wf descentLabel DescentLt.wf

/-- A face step: proper support shrink, confluence and Cartan unchanged.
Lowers the first (135) component. -/
def IsFaceStep {α : Type} {n : ℕ} (s t : DescentState α n) : Prop :=
  s.support ⊂ t.support ∧ s.confl = t.confl ∧ s.cartan = t.cartan

/-- A confluence step: support unchanged, confluence word strictly
shortened (prefix), Cartan unchanged.  Lowers the second (135)
component. -/
def IsConflStep {α : Type} {n : ℕ} (s t : DescentState α n) : Prop :=
  s.support = t.support ∧ s.confl <+: t.confl ∧ s.confl ≠ t.confl ∧
    s.cartan = t.cartan

/-- A Cartan step: support and confluence unchanged, Cartan height
strictly lowered.  Lowers the third (135) component. -/
def IsCartanStep {α : Type} {n : ℕ} (s t : DescentState α n) : Prop :=
  s.support = t.support ∧ s.confl = t.confl ∧ s.cartan < t.cartan

/-- A face step strictly decreases the (135) label. -/
theorem DescentStateLt.of_faceStep {α : Type} {n : ℕ} {s t : DescentState α n}
    (h : IsFaceStep s t) : DescentStateLt s t := by
  obtain ⟨hss, -, -⟩ := h
  have hcard : s.support.card < t.support.card := Finset.card_lt_card hss
  unfold DescentStateLt descentLabel
  rw [DescentLt_triple]
  left
  exact hcard

/-- A confluence step strictly decreases the (135) label. -/
theorem DescentStateLt.of_conflStep {α : Type} {n : ℕ} {s t : DescentState α n}
    (h : IsConflStep s t) : DescentStateLt s t := by
  obtain ⟨hsup, hpre, hne, -⟩ := h
  have hlen : s.confl.length < t.confl.length := by
    obtain ⟨u, hu⟩ := hpre
    have hne' : u ≠ [] := by
      intro hempty
      apply hne
      rw [hempty, List.append_nil] at hu
      exact hu
    have hulen : 0 < u.length := List.length_pos_iff.mpr hne'
    have hlen_eq : t.confl.length = s.confl.length + u.length := by
      rw [← hu, List.length_append]
    omega
  unfold DescentStateLt descentLabel
  rw [DescentLt_triple]
  right
  left
  constructor
  · rw [hsup]
  · exact hlen

/-- A Cartan step strictly decreases the (135) label. -/
theorem DescentStateLt.of_cartanStep {α : Type} {n : ℕ} {s t : DescentState α n}
    (h : IsCartanStep s t) : DescentStateLt s t := by
  obtain ⟨hsup, hcon, hlt⟩ := h
  unfold DescentStateLt descentLabel
  rw [DescentLt_triple]
  right
  right
  refine ⟨?_, ?_, hlt⟩
  · rw [hsup]
  · rw [hsup, hcon]

/-- Any of the three step types is a (135)-descent. -/
theorem DescentStateLt.of_step {α : Type} {n : ℕ} {s t : DescentState α n}
    (h : IsFaceStep s t ∨ IsConflStep s t ∨ IsCartanStep s t) :
    DescentStateLt s t := by
  rcases h with h | h | h
  · exact DescentStateLt.of_faceStep h
  · exact DescentStateLt.of_conflStep h
  · exact DescentStateLt.of_cartanStep h

end FilteredDescent
