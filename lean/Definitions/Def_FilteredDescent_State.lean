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

/-- The combined step relation: any of the three (135)-decreasing steps. -/
def DescentStep {α : Type} {n : ℕ} (s t : DescentState α n) : Prop :=
  IsFaceStep s t ∨ IsConflStep s t ∨ IsCartanStep s t

/-- The step relation is well-founded (via the (135) label). -/
theorem DescentStep.wellFounded {α : Type} {n : ℕ} :
    WellFounded (@DescentStep α n) := by
  apply Subrelation.wf (r := @DescentStateLt α n)
  · intro s t h
    exact DescentStateLt.of_step h
  · exact DescentStateLt.wellFounded

/-- A history tree is *state-labelled* if every node carries a
`DescentState` and every tree edge (parent → child) is a `DescentStep`
on the states.  This is the faithful §§6–9 tree structure. -/
def StateLabelled {α : Type} [DecidableEq α] {n : ℕ} (T : Finset (List α))
    (st : List α → DescentState α n) : Prop :=
  ∀ a ∈ T, ∀ b ∈ treeChildren T a, DescentStep (st b) (st a)

/-- A state-labelled tree satisfies `DescentLabels` (paper (135)): the
(135) label strictly decreases along tree edges. -/
theorem StateLabelled.to_DescentLabels {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (st : List α → DescentState α n)
    (h : StateLabelled T st) :
    DescentLabels T (fun w => descentLabel (st w)) := by
  intro a ha b hb
  exact DescentStateLt.of_step (h a ha b hb)

/-! ## F3: Successor branching (finite, packet-driven skeleton) -/

/-- `DescentState` has decidable equality when the mark type does. -/
instance DescentState.decidableEq {α : Type} [DecidableEq α] {n : ℕ} :
    DecidableEq (DescentState α n) := by
  intro s t
  cases s with | mk ss sc sk =>
  cases t with | mk ts tc tk =>
  simp only [DescentState.mk.injEq]
  infer_instance

/-- Successor states of `s`: all one-step (135)-descents, i.e. all `t`
with `DescentStep t s`.
- Face: any proper subset of the support (confl/cartan unchanged);
- Confluence: any proper prefix of the word — the descent *resolves*
  confluence by shortening the remaining word (paper: "a strict
  confluence predecessor lowers ℓ(χ)");
- Cartan: any strictly smaller height.

Finiteness: support has finitely many subsets; the word has finitely
many prefixes; the smaller heights are finite.  The *packet law* (F4)
will *select* the geometrically realized children from these
candidates; this is the full branching skeleton. -/
def successors {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) : Finset (DescentState α n) :=
  ((s.support.powerset.filter (fun J => J ⊂ s.support)).image
      (fun J => ({ s with support := J } : DescentState α n)))
    ∪ ((Finset.range s.confl.length).image
        (fun k => ({ s with confl := s.confl.take k } : DescentState α n)))
    ∪ ((Finset.range s.cartan).image
        (fun m => ({ s with cartan := m } : DescentState α n)))

/-- Every successor is a (135)-descent step. -/
theorem successors_are_steps {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) (t : DescentState α n) (ht : t ∈ successors s) :
    DescentStep t s := by
  have face_case : ∀ u : DescentState α n,
      u ∈ (s.support.powerset.filter (fun J => J ⊂ s.support)).image
        (fun J => ({ s with support := J } : DescentState α n)) →
      DescentStep u s := by
    intro u hu
    left
    rw [Finset.mem_image] at hu
    obtain ⟨J, hJ, rfl⟩ := hu
    rw [Finset.mem_filter] at hJ
    obtain ⟨_, hsub⟩ := hJ
    exact ⟨hsub, rfl, rfl⟩
  have confl_case : ∀ u : DescentState α n,
      u ∈ (Finset.range s.confl.length).image
        (fun k => ({ s with confl := s.confl.take k } : DescentState α n)) →
      DescentStep u s := by
    intro u hu
    right
    left
    rw [Finset.mem_image] at hu
    obtain ⟨k, hk, rfl⟩ := hu
    rw [Finset.mem_range] at hk
    refine ⟨rfl, ?_, ?_, rfl⟩
    · -- take k is a prefix
      exact List.take_prefix _ _
    · -- take k ≠ full word since k < length
      intro heq
      have hlen : (s.confl.take k).length = s.confl.length :=
        congrArg List.length heq
      rw [List.length_take] at hlen
      omega
  have cartan_case : ∀ u : DescentState α n,
      u ∈ (Finset.range s.cartan).image
        (fun m => ({ s with cartan := m } : DescentState α n)) →
      DescentStep u s := by
    intro u hu
    right
    right
    rw [Finset.mem_image] at hu
    obtain ⟨m, hm, rfl⟩ := hu
    rw [Finset.mem_range] at hm
    exact ⟨rfl, rfl, hm⟩
  unfold successors at ht
  simp only [Finset.mem_union] at ht
  rcases ht with (h | h) | h
  · exact face_case t h
  · exact confl_case t h
  · exact cartan_case t h

/-- Branching bound: number of successors is controlled by the support
size, word length, and Cartan height. -/
theorem successors_card_le {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) :
    (successors s).card ≤ 2 ^ s.support.card + s.confl.length + s.cartan := by
  -- Name the three parts
  set F : Finset (DescentState α n) :=
    (s.support.powerset.filter (fun J => J ⊂ s.support)).image
      (fun J => ({ s with support := J } : DescentState α n)) with hF
  set C : Finset (DescentState α n) :=
    (Finset.range s.confl.length).image
      (fun k => ({ s with confl := s.confl.take k } : DescentState α n)) with hC
  set K : Finset (DescentState α n) :=
    (Finset.range s.cartan).image
      (fun m => ({ s with cartan := m } : DescentState α n)) with hK
  have h1 : F.card ≤ 2 ^ s.support.card := by
    rw [hF]
    calc _ ≤ (s.support.powerset.filter (fun J => J ⊂ s.support)).card :=
          Finset.card_image_le
      _ ≤ s.support.powerset.card := Finset.card_filter_le _ _
      _ = 2 ^ s.support.card := Finset.card_powerset _
  have h2 : C.card ≤ s.confl.length := by
    rw [hC]
    calc _ ≤ (Finset.range s.confl.length).card := Finset.card_image_le
      _ = s.confl.length := Finset.card_range _
  have h3 : K.card ≤ s.cartan := by
    rw [hK]
    calc _ ≤ (Finset.range s.cartan).card := Finset.card_image_le
      _ = s.cartan := Finset.card_range _
  have hFC : (F ∪ C).card ≤ 2 ^ s.support.card + s.confl.length :=
    le_trans (Finset.card_union_le F C) (Nat.add_le_add h1 h2)
  have hFCK : (F ∪ C ∪ K).card ≤ 2 ^ s.support.card + s.confl.length + s.cartan :=
    le_trans (Finset.card_union_le (F ∪ C) K) (Nat.add_le_add hFC h3)
  have hsucc : successors s = F ∪ C ∪ K := by
    simp only [successors, hF, hC, hK]
  rw [hsucc]
  -- reassociate: (a + b) + c = a + b + c is rfl by Nat.add_assoc
  simpa [Nat.add_assoc] using hFCK

/-! ## F3b: First-failure face selection (paper §9.1, (42)) -/

/-- First-failed-pivot face selection (paper §9.1): given a support `I`
and a per-element pivot-survival predicate, assign the packet to the
maximal subset of `I` whose pivots survive.

Paper: "assign the packet to the first maximal subset J ⊆ I whose
declared pivots survive, using lexicographic tie breaking, and assign
it to J = I exactly when every pivot survives."

In the per-element survival model, the maximal surviving subset is
unique (the set of all surviving elements), so no tie-breaking is
needed; the lexicographic rule of the paper selects this same unique
maximal set. -/
def firstFailedFace {n : ℕ} (I : Finset (Fin n)) (survives : Fin n → Prop)
    [DecidablePred survives] : Finset (Fin n) :=
  I.filter survives

/-- The selected face is a subset of the support. -/
theorem firstFailedFace_subset {n : ℕ} (I : Finset (Fin n))
    (survives : Fin n → Prop) [DecidablePred survives] :
    firstFailedFace I survives ⊆ I :=
  Finset.filter_subset _ _

/-- If every pivot survives, the packet stays at full support
(paper: "assign it to J = I exactly when every pivot survives"). -/
theorem firstFailedFace_full {n : ℕ} (I : Finset (Fin n))
    (survives : Fin n → Prop) [DecidablePred survives]
    (h : ∀ j ∈ I, survives j) :
    firstFailedFace I survives = I :=
  Finset.filter_true_of_mem h

/-- The selected face has the universal property: it contains every
surviving element of `I`, hence is the unique maximal surviving
subset. -/
theorem firstFailedFace_maximal {n : ℕ} (I : Finset (Fin n))
    (survives : Fin n → Prop) [DecidablePred survives]
    (J : Finset (Fin n)) (hJ : J ⊆ I) (hsurv : ∀ j ∈ J, survives j) :
    J ⊆ firstFailedFace I survives := by
  intro j hj
  rw [firstFailedFace, Finset.mem_filter]
  exact ⟨hJ hj, hsurv j hj⟩

/-- A first-failure face step: moving from support `I` to the selected
face `J` is either trivial (no pivot failed) or a proper face descent
(paper (135): "a proper face lowers support"). -/
theorem firstFailedFace_step {α : Type} [DecidableEq α] {n : ℕ}
    (s : DescentState α n) (survives : Fin n → Prop) [DecidablePred survives]
    (t : DescentState α n)
    (ht_supp : t.support = firstFailedFace s.support survives)
    (ht_confl : t.confl = s.confl) (ht_cartan : t.cartan = s.cartan) :
    t.support ⊆ s.support ∧
      (t.support = s.support ∨ DescentStep t s) := by
  refine ⟨?_, ?_⟩
  · rw [ht_supp]
    exact firstFailedFace_subset _ _
  · by_cases heq : t.support = s.support
    · exact Or.inl heq
    · right
      left
      refine ⟨?_, ht_confl, ht_cartan⟩
      rw [ht_supp]
      exact lt_of_le_of_ne (firstFailedFace_subset _ _) (fun h => heq (ht_supp.trans h))

end FilteredDescent
