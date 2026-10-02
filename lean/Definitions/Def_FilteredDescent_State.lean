import Theorems.Thm_FilteredDescent_DescentLabels
import Theorems.Thm_FilteredDescent_DescentTree
import Definitions.Def_FilteredDescent_Packet
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

/-! ## F3c: Well-founded descent tree -/

/-- The descent tree rooted at `s`: all root-to-node paths `[s, s₁, ...]`
where each step is a successor.  Built by well-founded recursion on
`DescentStep` (paper: the tree `T_{I,k}` with (135)-decreasing edges).

Finiteness is by construction (`Finset`); well-foundedness ensures
every path terminates. -/
noncomputable def descentTree {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) : Finset (List (DescentState α n)) :=
  DescentStep.wellFounded.fix
    (fun s ih =>
      {[s]} ∪ (successors s).attach.biUnion (fun ⟨t, ht⟩ =>
        (ih t (successors_are_steps s t ht)).image (fun p => s :: p)))
    s

/-- Unfolding equation for the descent tree. -/
theorem descentTree_unfold {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) :
    descentTree s = {[s]} ∪ (successors s).attach.biUnion (fun ⟨t, _⟩ =>
      (descentTree t).image (fun p => s :: p)) := by
  unfold descentTree
  rw [WellFounded.fix_eq]

/-- Root membership: the singleton path is in the tree. -/
theorem descentTree_root_mem {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) : [s] ∈ descentTree s := by
  rw [descentTree_unfold]
  exact Finset.mem_union_left _ (Finset.mem_singleton_self [s])

/-- Every path in the tree starts with the root. -/
theorem descentTree_head {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) (p : List (DescentState α n))
    (hp : p ∈ descentTree s) : p.head? = some s := by
  -- By well-founded induction on s
  induction s using WellFounded.induction DescentStep.wellFounded with
  | _ s ih =>
    rw [descentTree_unfold] at hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [Finset.mem_singleton] at hp
      rw [hp]
      rfl
    · rw [Finset.mem_biUnion] at hp
      obtain ⟨⟨t, ht⟩, _, hp⟩ := hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      -- (s :: q).head? = some s by definition
      rfl

/-! ## F3d: Descent chain property and labels -/

/-- A list of states is a descent chain if consecutive elements are
`DescentStep`-related (child < parent). -/
def IsDescentChain {α : Type} {n : ℕ} : List (DescentState α n) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => DescentStep b a ∧ IsDescentChain (b :: rest)

/-- Every path in the descent tree is a descent chain. -/
theorem descentTree_isChain {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) (p : List (DescentState α n))
    (hp : p ∈ descentTree s) : IsDescentChain p := by
  induction s using WellFounded.induction DescentStep.wellFounded
    generalizing p with
  | _ s ih =>
    rw [descentTree_unfold] at hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · -- p = [s], singleton is a chain
      rw [Finset.mem_singleton] at hp
      rw [hp]
      trivial
    · -- p = s :: q for q ∈ descentTree t, t ∈ successors s
      rw [Finset.mem_biUnion] at hp
      obtain ⟨⟨t, ht⟩, _, hp⟩ := hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      -- q ∈ descentTree t, so by ih, q is a chain
      have hchain : IsDescentChain q := ih t (successors_are_steps s t ht) q hq
      -- s :: q is a chain: need DescentStep (q.head) s and chain q
      cases q with
      | nil =>
        -- q = [], so s :: [] = [s], singleton chain
        trivial
      | cons b rest =>
        -- q = b :: rest, need DescentStep b s
        -- Since q ∈ descentTree t, q.head? = some t (by descentTree_head)
        have hhead : (b :: rest).head? = some t := descentTree_head t _ hq
        simp at hhead
        -- hhead : b = t
        rw [hhead]
        -- Goal: DescentStep t s ∧ IsDescentChain (t :: rest)
        -- But q = b :: rest = t :: rest, and hchain : IsDescentChain (t :: rest)
        refine ⟨successors_are_steps s t ht, ?_⟩
        rw [← hhead]
        exact hchain

/-- Label of a path: the (135) label of its last state (the node).
Empty path gets the minimal label. -/
def pathLabel {α : Type} {n : ℕ} (p : List (DescentState α n)) : ℕ × ℕ × ℕ :=
  match p.getLast? with
  | some t => descentLabel t
  | none => (0, 0, 0)

/-- From a descent chain `p ++ [t]` with `p` nonempty, extract the last
step: `t` is a `DescentStep` from the last element of `p`. -/
theorem IsDescentChain_last_step {α : Type} {n : ℕ}
    (p : List (DescentState α n)) (t : DescentState α n) (hp : p ≠ [])
    (hchain : IsDescentChain (p ++ [t])) :
    DescentStep t (p.getLast hp) := by
  induction p with
  | nil => exact absurd rfl hp
  | cons a rest ih =>
    cases rest with
    | nil =>
      -- p = [a]: p ++ [t] = [a, t]; unfold chain to get DescentStep t a
      have h1 : DescentStep t a ∧ IsDescentChain [t] := by
        have h2 : IsDescentChain ([a] ++ [t]) := by simpa using hchain
        simpa [IsDescentChain] using h2
      have hlast : ([a] : List (DescentState α n)).getLast hp = a := by simp
      rw [hlast]
      exact h1.1
    | cons b rest' =>
      -- p = a :: b :: rest': unfold first step, apply IH to b :: rest'
      have h1 : DescentStep b a ∧ IsDescentChain (((b :: rest') : List (DescentState α n)) ++ [t]) := by
        have h2 : IsDescentChain ((a :: b :: rest') ++ [t]) := by simpa using hchain
        simpa [IsDescentChain] using h2
      have hne : ((b :: rest') : List (DescentState α n)) ≠ [] := by simp
      have hstep := ih hne h1.2
      have heq : ((b :: rest') : List (DescentState α n)).getLast hne
          = (a :: b :: rest').getLast hp := by simp [List.getLast]
      rw [heq] at hstep
      exact hstep

/-- The descent tree satisfies `DescentLabels` (paper (135)): the (135)
label strictly decreases along tree edges. -/
theorem descentTree_labels {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (s : DescentState α n) :
    DescentLabels (descentTree s) (pathLabel (α := α) (n := n)) := by
  intro p hp q hq
  rw [treeChildren, Finset.mem_filter] at hq
  obtain ⟨hq_mem, hpref, hlen⟩ := hq
  -- p is nonempty
  have hp_ne : p ≠ [] := by
    intro h
    rw [h] at hp
    have hhead := descentTree_head s [] hp
    simp at hhead
  -- q = p ++ [t]: from prefix and length
  obtain ⟨r, hr⟩ := hpref
  have hr_len : r.length = 1 := by
    have h1 : (p ++ r).length = q.length := by rw [← hr]
    rw [List.length_append] at h1
    omega
  obtain ⟨t, ht⟩ : ∃ t, r = [t] := by
    cases r with
    | nil => simp at hr_len
    | cons t rest =>
      have : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hr_len
      rw [this]
      exact ⟨t, rfl⟩
  -- q = p ++ [t]
  have hq_eq : q = p ++ [t] := by rw [← hr, ht]
  -- Chain property gives the last step
  have hchain : IsDescentChain q := descentTree_isChain s q hq_mem
  rw [hq_eq] at hchain
  have hstep : DescentStep t (p.getLast hp_ne) :=
    IsDescentChain_last_step p t hp_ne hchain
  -- Labels: pathLabel (p ++ [t]) = descentLabel t
  have hlab_q : pathLabel (p ++ [t] : List (DescentState α n)) = descentLabel t := by
    unfold pathLabel
    have : (p ++ [t]).getLast? = some t := by simp
    rw [this]
  -- pathLabel p = descentLabel (p.getLast hp_ne)
  have hlab_p : pathLabel (p : List (DescentState α n)) = descentLabel (p.getLast hp_ne) := by
    unfold pathLabel
    have : p.getLast? = some (p.getLast hp_ne) := List.getLast?_eq_some_getLast hp_ne
    rw [this]
  rw [hq_eq, hlab_q, hlab_p]
  -- DescentStep → DescentLt on labels
  exact DescentStateLt.of_step hstep

/-! ## F4a: Packet-law child selection -/

/-- Packet selection data at a descent state (paper §§6–9): the packet
law induces a mass distribution on the successor states; the realized
children are those with positive mass.

- `faceOf`: assigns each packet (tube tuple) to its first-failed face
  `J ⊆ I` (paper §9.1);
- `childMass`: the induced mass on successor states (from `packetLaw`
  via `retainedMass`; confluence/Cartan masses from the insertion
  kernels).

Only the interface matters here: selected children are a subset of
`successors`, hence valid `DescentStep`s. -/
structure PacketSelect (α : Type) (n r : ℕ) where
  /-- First-failed face of a packet (always a face of the support). -/
  faceOf : (Fin r → Fin n) → Finset (Fin n)
  /-- Mass of each successor state under the packet law. -/
  childMass : DescentState α n → ℝ

/-- Packet-selected children: successors with positive mass.
These are the geometrically realized children (paper: the tree
`T_{I,k}` contains only the retained structural labels). -/
noncomputable def packetChildren {α : Type} [Fintype α] [DecidableEq α] {n r : ℕ}
    (s : DescentState α n) (sel : PacketSelect α n r) :
    Finset (DescentState α n) :=
  (successors s).filter (fun t => 0 < sel.childMass t)

/-- Selected children are among the successors. -/
theorem packetChildren_subset {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n) (sel : PacketSelect α n r) :
    packetChildren s sel ⊆ successors s :=
  Finset.filter_subset _ _

/-- Every packet-selected child is a (135)-descent step. -/
theorem packetChildren_are_steps {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n) (sel : PacketSelect α n r)
    (t : DescentState α n) (ht : t ∈ packetChildren s sel) :
    DescentStep t s :=
  successors_are_steps s t (packetChildren_subset s sel ht)

/-- Selected children satisfy the branching bound a fortiori. -/
theorem packetChildren_card_le {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n) (sel : PacketSelect α n r) :
    (packetChildren s sel).card ≤ 2 ^ s.support.card + s.confl.length + s.cartan :=
  le_trans (Finset.card_le_card (packetChildren_subset s sel))
    (successors_card_le s)

/-! ## F4a-3: Packet-selected subtree -/

/-- The packet-selected subtree: at each node, only the packet-realized
children (`packetChildren`) are taken, not all successors.  This is the
paper's tree `T_{I,k}` ("contains only the retained structural labels").

`selOf` gives the packet selection data at each state. -/
noncomputable def selectedTree {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r) :
    Finset (List (DescentState α n)) :=
  DescentStep.wellFounded.fix
    (fun s ih =>
      {[s]} ∪ (packetChildren s (selOf s)).attach.biUnion (fun ⟨t, ht⟩ =>
        (ih t (packetChildren_are_steps s (selOf s) t ht)).image (fun p => s :: p)))
    s

/-- Unfolding equation for the selected tree. -/
theorem selectedTree_unfold {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r) :
    selectedTree s selOf
      = {[s]} ∪ (packetChildren s (selOf s)).attach.biUnion (fun ⟨t, _⟩ =>
        (selectedTree t selOf).image (fun p => s :: p)) := by
  unfold selectedTree
  rw [WellFounded.fix_eq]

/-- The selected tree is a subtree of the full descent tree. -/
theorem selectedTree_subset {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r) :
    selectedTree s selOf ⊆ descentTree s := by
  induction s using WellFounded.induction DescentStep.wellFounded
    generalizing selOf with
  | _ s ih =>
    intro p hp
    rw [selectedTree_unfold] at hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · -- p = [s]: in the full tree by root_mem
      rw [Finset.mem_singleton] at hp
      rw [hp]
      exact descentTree_root_mem s
    · -- p = s :: q, q ∈ selectedTree t for t ∈ packetChildren
      rw [Finset.mem_biUnion] at hp
      obtain ⟨⟨t, ht⟩, _, hp⟩ := hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hstep : DescentStep t s :=
        packetChildren_are_steps s (selOf s) t ht
      have hq_mem : q ∈ descentTree t := ih t hstep selOf hq
      have ht_succ : t ∈ successors s :=
        packetChildren_subset s (selOf s) ht
      rw [descentTree_unfold]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨⟨t, ht_succ⟩, Finset.mem_attach _ _, ?_⟩
      rw [Finset.mem_image]
      exact ⟨q, hq_mem, rfl⟩

/-- The packet-selected tree satisfies `DescentLabels`: (135) labels
decrease along its edges (inherited from the full tree via the subset
and chain property). -/
theorem selectedTree_labels {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r) :
    DescentLabels (selectedTree s selOf) (pathLabel (α := α) (n := n)) := by
  intro p hp q hq
  rw [treeChildren, Finset.mem_filter] at hq
  obtain ⟨hq_mem, hpref, hlen⟩ := hq
  have hp_ne : p ≠ [] := by
    intro h
    rw [h] at hp
    have hsub := selectedTree_subset s selOf hp
    have hhead := descentTree_head s [] hsub
    simp at hhead
  obtain ⟨rr, hr⟩ := hpref
  have hr_len : rr.length = 1 := by
    have h1 : (p ++ rr).length = q.length := by rw [← hr]
    rw [List.length_append] at h1
    omega
  obtain ⟨t, ht⟩ : ∃ t, rr = [t] := by
    cases rr with
    | nil => simp at hr_len
    | cons t rest =>
      have : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hr_len
      rw [this]
      exact ⟨t, rfl⟩
  have hq_eq : q = p ++ [t] := by rw [← hr, ht]
  -- q is a descent chain via the full tree
  have hq_sub : q ∈ descentTree s := selectedTree_subset s selOf hq_mem
  have hchain : IsDescentChain q := descentTree_isChain s q hq_sub
  rw [hq_eq] at hchain
  have hstep : DescentStep t (p.getLast hp_ne) :=
    IsDescentChain_last_step p t hp_ne hchain
  have hlab_q : pathLabel (p ++ [t] : List (DescentState α n)) = descentLabel t := by
    unfold pathLabel
    have : (p ++ [t]).getLast? = some t := by simp
    rw [this]
  have hlab_p : pathLabel (p : List (DescentState α n)) = descentLabel (p.getLast hp_ne) := by
    unfold pathLabel
    have : p.getLast? = some (p.getLast hp_ne) := List.getLast?_eq_some_getLast hp_ne
    rw [this]
  rw [hq_eq, hlab_q, hlab_p]
  exact DescentStateLt.of_step hstep

/-! ## F4b: Markov deletion and source-mass ledger (paper §9.1, (117)) -/

/-- Source-mass ledger at a descent node (paper §9.1): tracks the total,
deleted, and retained packet mass.  "Every deletion is measured in the
size-biased incidence mass of the same global source."

- `total`: total source mass at the node;
- `deleted`: mass removed by Markov deletion (source-small);
- `retained`: remaining mass after deletion. -/
structure SourceLedger where
  total : ℝ
  deleted : ℝ
  retained : ℝ

/-- Ledger conservation: retained + deleted = total. -/
def SourceLedger.conserved (L : SourceLedger) : Prop :=
  L.retained + L.deleted = L.total

/-- Deleted set: packets where multiplicity exceeds `total / ε`. -/
noncomputable def markovDelSet {n r : ℕ} (w : Fin n → ℝ)
    (mult : (Fin r → Fin n) → ℝ) (ε : ℝ) : Finset (Fin r → Fin n) :=
  Finset.univ.filter (fun U => (∑ V, mult V * packetLaw w V) / ε < mult U)

/-- Retained set: packets where multiplicity is at most `total / ε`. -/
noncomputable def markovRetSet {n r : ℕ} (w : Fin n → ℝ)
    (mult : (Fin r → Fin n) → ℝ) (ε : ℝ) : Finset (Fin r → Fin n) :=
  Finset.univ.filter (fun U => mult U ≤ (∑ V, mult V * packetLaw w V) / ε)

noncomputable def markovDelete {n r : ℕ} (w : Fin n → ℝ)
    (mult : (Fin r → Fin n) → ℝ) (ε : ℝ) : SourceLedger where
  total := ∑ U, mult U * packetLaw w U
  deleted := (markovDelSet w mult ε).sum (fun U => mult U * packetLaw w U)
  retained := (markovRetSet w mult ε).sum (fun U => mult U * packetLaw w U)

/-- The ledger from Markov deletion is conserved (partition of unity). -/
theorem markovDelete_conserved {n r : ℕ} (w : Fin n → ℝ)
    (mult : (Fin r → Fin n) → ℝ) (ε : ℝ) :
    (markovDelete w mult ε).conserved := by
  unfold SourceLedger.conserved markovDelete
  simp only []
  have hunion : markovRetSet w mult ε ∪ markovDelSet w mult ε = Finset.univ := by
    ext U
    simp only [markovRetSet, markovDelSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases lt_or_ge ((∑ V, mult V * packetLaw w V) / ε) (mult U) with h | h
    · exact iff_of_true (Or.inr h) True.intro
    · exact iff_of_true (Or.inl h) True.intro
  have hdisj : Disjoint (markovRetSet w mult ε) (markovDelSet w mult ε) := by
    unfold markovRetSet markovDelSet
    rw [Finset.disjoint_filter]
    intro U _ h1 h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  calc (markovRetSet w mult ε).sum (fun U => mult U * packetLaw w U)
      + (markovDelSet w mult ε).sum (fun U => mult U * packetLaw w U)
      = ((markovRetSet w mult ε) ∪ (markovDelSet w mult ε)).sum
        (fun U => mult U * packetLaw w U) := by rw [Finset.sum_union hdisj]
    _ = ∑ U, mult U * packetLaw w U := by rw [hunion]

/-- Cutoff property (paper (117)): on the retained set, the multiplicity
is bounded by `total / ε`.  This is the hereditary cutoff `BX`. -/
theorem markovRetSet_bounded {n r : ℕ} (w : Fin n → ℝ)
    (mult : (Fin r → Fin n) → ℝ) (ε : ℝ)
    (U : Fin r → Fin n) (hU : U ∈ markovRetSet w mult ε) :
    mult U ≤ (∑ V, mult V * packetLaw w V) / ε := by
  unfold markovRetSet at hU
  rw [Finset.mem_filter] at hU
  exact hU.2

/-- Source-small deletion hypothesis (paper (117)): the deleted mass is
at most `ε` times the total.  In the paper this is achieved by the
infimum definition of `BX`; here it is the interface property that a
concrete deletion must satisfy. -/
def SourceLedger.sourceSmall (L : SourceLedger) (ε : ℝ) : Prop :=
  L.deleted ≤ ε * L.total

/-! ## F4c: (θ,j,c) model data threading (paper (150)–(153)) -/

/-- Model data per descent node (paper (150)–(153)): the typed
predecessor/slot/carrier triple for the common-source aggregation.

- `theta`: typed predecessor mark `ϑ` (which type);
- `slot`: scale/slot index `j`;
- `carrier`: quantized affine carrier mark `c ∈ C_κ` (paper (152)).

Paper: "Let `W^{θ,j} := Σ_c W^{θ,j,c}`. This is one disjoint aggregate
of proper structural nodes" — nodes sharing `(θ,j)` are summed over `c`,
with `|C_κ|` bounding the carrier count. -/
structure ModelData where
  theta : ℕ
  slot : ℕ
  carrier : ℕ
deriving DecidableEq

/-- The (θ,j) key: nodes are aggregated by typed predecessor and slot,
summing over carriers. -/
def ModelData.key (d : ModelData) : ℕ × ℕ := (d.theta, d.slot)

/-- Nodes of a tree with a given (θ,j) key. -/
def nodesWithKey {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List (DescentState α n)))
    (modelOf : List (DescentState α n) → ModelData) (k : ℕ × ℕ) :
    Finset (List (DescentState α n)) :=
  T.filter (fun p => (modelOf p).key = k)

/-- Aggregate load at key (θ,j): sum over carriers `c`.
Paper: "`W^{θ,j} := Σ_c W^{θ,j,c}`. This is one disjoint aggregate of
proper structural nodes." -/
noncomputable def aggLoad {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List (DescentState α n)))
    (modelOf : List (DescentState α n) → ModelData)
    (W : List (DescentState α n) → ℝ) (k : ℕ × ℕ) : ℝ :=
  ∑ p ∈ nodesWithKey T modelOf k, W p

/-- Partition of total load by (θ,j) key: the keys partition the tree,
so the total is the sum of aggregates. -/
theorem total_eq_sum_agg {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List (DescentState α n)))
    (modelOf : List (DescentState α n) → ModelData)
    (W : List (DescentState α n) → ℝ) :
    ∑ p ∈ T, W p = ∑ k ∈ T.image (fun p => (modelOf p).key), aggLoad T modelOf W k := by
  unfold aggLoad nodesWithKey
  symm
  apply Finset.sum_fiberwise_of_maps_to (g := fun p : List (DescentState α n) => (modelOf p).key)
  intro p hp
  exact Finset.mem_image_of_mem _ hp

/-- Carrier count bound interface (paper (152)): for fixed (θ,j), the
number of distinct carriers is at most `|C_κ|`.  This is the named
input `hcard` from the terminal hardening. -/
def carrierBounded {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List (DescentState α n)))
    (modelOf : List (DescentState α n) → ModelData)
    (Ccard : ℝ) : Prop :=
  ∀ k : ℕ × ℕ, ((nodesWithKey T modelOf k).image (fun p => (modelOf p).carrier)).card
    ≤ Ccard

end FilteredDescent
