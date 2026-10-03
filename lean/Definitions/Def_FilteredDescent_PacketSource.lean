import Definitions.Def_FilteredDescent_Packet
import Definitions.Def_FilteredDescent_State

/-!
# Packet source provenance (TODO_GUIDANCE item 7, part 1)

Derives `PacketSelect.childMass` from the packet law, rather than taking
it as arbitrary data.

The paper's construction (§§6–9):
1. Start with the common packet probability law `packetLaw w` on
   `r`-tuples of tubes (paper (17)).
2. For each packet `U`, the first-failed face `faceOf U` determines which
   geometric configuration is realized.
3. The packet law induces a mass on successor states: a successor `t`
   gets mass equal to the total packet mass of tuples `U` that transition
   `s → t`.
4. Retained-mass restriction: only packets in the retained set `A`
   (with `retainedMass w A > 0`) contribute.
5. Source-small deletion: packets whose contribution is below a threshold
   are deleted via the ledger (this is what makes the tree finite and
   the constants uniform).

## Current status (honest)

This file defines:
- `PacketSource`: the source data (weight, face assignment, transition,
  retained set, deletion threshold).
- `derivedChildMass`: the child mass computed from the source data.
- `packetSelectOfSource`: constructs a `PacketSelect` with the derived
  mass (instead of arbitrary `childMass`).

What remains (needs the full §§6–9 construction):
- The state transition function `trans s U` must be proved to respect
  the (135) descent labels (i.e. `DescentStep (trans s U) s`).
- Mass conservation: `∑ t, derivedChildMass src s t = retainedMass ...`
  (this is item 8, `htotalLoad` discharge).
- The deletion ledger must be shown to keep the tree finite with
  uniform complexity bounds (needed for the uniform constant in item 9).
-/

namespace FilteredDescent

/-- Packet source data (TODO_GUIDANCE item 7).

Bundles everything needed to derive the tree's child masses from the
packet law, instead of taking `childMass` as arbitrary.

- `w`: the tube weight function for `packetLaw w` (paper (17)).
- `faceOf`: first-failed face assignment for each packet tuple.
- `trans`: state transition — given current state `s` and packet `U`,
  the successor state. Must satisfy `DescentStep (trans s U) s`
  (the (135) label decrease).
- `retained`: the retained packet set `A` (with positive retained mass).
- `delThresh`: source-small deletion threshold; packets with mass below
  this are deleted from the tree construction. -/
structure PacketSource (α : Type) [Fintype α] [DecidableEq α] (n r : ℕ) where
  w : Fin n → ℝ
  hw_nonneg : ∀ i, 0 ≤ w i
  hw_pos : 0 < ∑ i, w i
  faceOf : (Fin r → Fin n) → Finset (Fin n)
  trans : DescentState α n → (Fin r → Fin n) → DescentState α n
  htrans_step : ∀ s U, DescentStep (trans s U) s
  retained : Finset (Fin r → Fin n)
  hret_nonempty : retained.Nonempty
  hret_pos : 0 < retainedMass w retained
  delThresh : ℝ
  hdel_nonneg : 0 ≤ delThresh

/-- A packet survives deletion iff its mass exceeds the threshold. -/
def packetSurvives {n r : ℕ} (w : Fin n → ℝ) (delThresh : ℝ)
    (U : Fin r → Fin n) : Prop :=
  delThresh < packetLaw w U

noncomputable instance {n : ℕ} {r : ℕ} (w : Fin n → ℝ) (delThresh : ℝ) :
    DecidablePred (packetSurvives (n := n) (r := r) w delThresh) := fun U =>
  Real.decidableLT delThresh (packetLaw w U)

/-- A packet `U` contributes to the `s → t` transition iff it maps to `t`
and survives deletion. -/
def packetContributes {α : Type} [Fintype α] [DecidableEq α] {n r : ℕ}
    (src : PacketSource α n r) (s t : DescentState α n)
    (U : Fin r → Fin n) : Prop :=
  src.trans s U = t ∧ packetSurvives src.w src.delThresh U

noncomputable instance {α : Type} [Fintype α] [DecidableEq α] {n r : ℕ}
    (src : PacketSource α n r) (s t : DescentState α n) :
    DecidablePred (packetContributes src s t) := fun U =>
  inferInstanceAs (Decidable (src.trans s U = t ∧
    packetSurvives src.w src.delThresh U))

/-- Derived child mass (TODO_GUIDANCE item 7).

The mass of successor `t` from state `s` is the total packet-law mass
of retained, non-deleted tuples `U` that transition `s → t`.

This replaces the arbitrary `PacketSelect.childMass` field with a
computed quantity. -/
noncomputable def derivedChildMass {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (src : PacketSource α n r)
    (s : DescentState α n) (t : DescentState α n) : ℝ :=
  ∑ U ∈ src.retained.filter (packetContributes src s t),
    packetLaw src.w U

/-- Constructs a `PacketSelect` from packet source data at state `s`.

The `childMass` is the derived mass, not arbitrary data. This is the
constructor theorem required by TODO_GUIDANCE item 7's acceptance test:
the tree becomes a deterministic object of the source ledger. -/
noncomputable def packetSelectOfSource {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (src : PacketSource α n r)
    (s : DescentState α n) : PacketSelect α n r where
  faceOf := src.faceOf
  childMass := derivedChildMass src s

/-- The derived child mass is nonnegative. -/
theorem derivedChildMass_nonneg {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (src : PacketSource α n r)
    (s t : DescentState α n) : 0 ≤ derivedChildMass src s t := by
  unfold derivedChildMass
  apply Finset.sum_nonneg
  intro U _
  -- packetLaw is nonnegative when w is nonnegative
  unfold packetLaw
  apply div_nonneg
  · apply Finset.prod_nonneg
    intro j _
    exact src.hw_nonneg _
  · apply pow_nonneg
    apply Finset.sum_nonneg
    intro i _
    exact src.hw_nonneg i

/-- Packet-selected children from source data are descent steps.

Since `packetSelectOfSource` uses the derived mass, and the transition
respects `DescentStep`, the selected children are valid (135) steps. -/
theorem packetChildrenOfSource_are_steps {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (src : PacketSource α n r)
    (s : DescentState α n) (t : DescentState α n)
    (ht : t ∈ packetChildren s (packetSelectOfSource src s)) :
    DescentStep t s := by
  -- packetChildren filters successors by positive mass
  have hsub := packetChildren_subset s (packetSelectOfSource src s) ht
  exact successors_are_steps s t hsub

/-- Mass conservation (TODO_GUIDANCE items 7/8, key lemma).

The total derived child mass from `s` equals the total surviving
retained packet mass. Each retained surviving packet `U` contributes
its mass to exactly one successor (`trans s U`) — a fiber-sum argument.

This is the combinatorial heart of `htotalLoad` discharge (item 8):
mass is neither created nor destroyed when passing from the packet law
to the tree's child distribution; only the source-small deletion
removes mass, and that removal is tracked by the ledger. -/
theorem derivedChildMass_sum {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} [Fintype (DescentState α n)] (src : PacketSource α n r)
    (s : DescentState α n) :
    ∑ t, derivedChildMass src s t =
    ∑ U ∈ src.retained.filter (packetSurvives src.w src.delThresh),
      packetLaw src.w U := by
  -- Each derivedChildMass is a fiber sum over the double filter
  have h1 : ∀ t : DescentState α n, derivedChildMass src s t =
      ∑ U ∈ (src.retained.filter
        (packetSurvives src.w src.delThresh)).filter
        (fun U => src.trans s U = t), packetLaw src.w U := by
    intro t
    show ∑ U ∈ src.retained.filter (packetContributes src s t),
      packetLaw src.w U = _
    rw [show (src.retained.filter (packetContributes src s t))
        = (src.retained.filter
          (packetSurvives src.w src.delThresh)).filter
          (fun U => src.trans s U = t) from by
      ext U
      simp only [Finset.mem_filter, packetContributes]
      constructor
      · rintro ⟨hmem, htrans, hsurv⟩
        exact ⟨⟨hmem, hsurv⟩, htrans⟩
      · rintro ⟨⟨hmem, hsurv⟩, htrans⟩
        exact ⟨hmem, htrans, hsurv⟩]
  simp_rw [h1]
  -- Fiberwise sum: ∑ t, ∑_{U : trans s U = t} = ∑ U
  exact Finset.sum_fiberwise_of_maps_to
    (fun U _ => Finset.mem_univ (src.trans s U))
    (fun U => packetLaw src.w U)

end FilteredDescent
