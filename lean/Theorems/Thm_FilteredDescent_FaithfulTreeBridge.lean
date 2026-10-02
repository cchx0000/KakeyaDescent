import Definitions.Def_FilteredDescent_State
import Theorems.Thm_FilteredDescent_EndToEnd

/-!
# Faithful tree bridge to scalar closure

Applies the discharged scalar closure gate to the faithful `[]`-rooted
tree `faithfulTree0`.  The tree hypotheses are proved from the faithful
construction; analytic hypotheses remain as parameters.
-/

namespace FilteredDescent

/-- Scalar closure on the faithful tree: the tree hypotheses (`hroot`,
`hprefix`, `hlab`) are discharged by the faithful construction
(F5-2b); the analytic hypotheses (`termTube`, `load`, hardening, etc.)
remain as parameters to be discharged from packet data. -/
theorem scalar_closure_faithful_tree {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r)
    (S : ShadedTubes n)
    (termTube : List (DescentState α n) → Fin n)
    (load : List (DescentState α n) → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves (faithfulTree0 s selOf), ∀ δ : ℝ, 0 < δ → δ < 1 →
      0 ≤ load γ δ)
    (htotalLoad : ∀ δ, totalLoad (faithfulTree0 s selOf) load δ = ∑ t, S.shadeVol t δ)
    (leaf_bound : ∀ γ ∈ treeLeaves (faithfulTree0 s selOf), ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ S.unionVol δ)
    (terminal_hardening : ∀ x ∈ faithfulTree0 s selOf, SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad (reroot (faithfulTree0 s selOf) x)
        (fun s' => termTube (x ++ s')) (fun s' δ => load (x ++ s') δ) t δ) ^ 2)
      (fun δ => S.unionVol δ * totalLoad (reroot (faithfulTree0 s selOf) x)
        (fun s' δ => load (x ++ s') δ) δ))
    (geom_pair : ∀ x ∈ faithfulTree0 s selOf, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot (faithfulTree0 s selOf) x)
          (fun s' => termTube (x ++ s')) (fun s' δ => load (x ++ s') δ) t δ
          * termLoad (reroot (faithfulTree0 s selOf) x)
          (fun s' => termTube (x ++ s')) (fun s' δ => load (x ++ s') δ) t' δ
        else 0)
      (fun δ => S.unionVol δ * totalLoad (reroot (faithfulTree0 s selOf) x)
        (fun s' δ => load (x ++ s') δ) δ)) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol :=
  scalar_closure_discharged S (faithfulTree0 s selOf)
    (faithfulTree0_root s selOf)
    (fun l hl p hpl => faithfulTree0_prefix s selOf l hl p hpl)
    (faithfulLab0 s) (faithfulTree0_labels s selOf)
    termTube load hload htotalLoad leaf_bound
    terminal_hardening geom_pair

/-! ## F6: Discharging analytic hypotheses from packet data -/

/-- Faithful packet model: bundles the per-node selection data with the
leaf tube/load functions derived from the packet law.

- `selOf`: packet selection at each state (F4a);
- `termTubeOf`: terminal tube at each tree node (from packet data);
- `loadOf`: leaf load as a function of δ (from packet mass).

Parameterized by the actual analytic family `S` (TODO_GUIDANCE P0-3):
the old version quantified over all `S`, which is uninhabited for `n > 0`.

The gate hypotheses (`hload`, `htotalLoad`, `leaf_bound`) are proved from
this model's fields. -/
structure FaithfulModel (α : Type) [Fintype α] [DecidableEq α]
    (n r : ℕ) (S : ShadedTubes n) where
  selOf : DescentState α n → PacketSelect α n r
  termTubeOf : List (DescentState α n) → Fin n
  loadOf : List (DescentState α n) → ℝ → ℝ
  /-- Packet mass nonnegativity: the load comes from the packet law
  with nonnegative weights, hence is nonnegative on leaves. -/
  load_nonneg : ∀ γ δ, 0 < δ → δ < 1 → 0 ≤ loadOf γ δ
  /-- Mass conservation: total leaf load equals the tube shading sum
  for *this* `S`. From the packet law's total mass via the tree partition. -/
  mass_conserved : ∀ (s : DescentState α n) (δ : ℝ),
    ∑ γ ∈ treeLeaves (faithfulTree0 s selOf), loadOf γ δ
      = ∑ t, S.shadeVol t δ
  /-- Leaf bound: each leaf's load is at most the union volume of *this* `S`.
  From the packet's geometric bound. -/
  leaf_geometric : ∀ (γ : List (DescentState α n))
    (δ : ℝ), 0 < δ → δ < 1 → loadOf γ δ ≤ S.unionVol δ

/-- Fully assembled scalar closure on the faithful tree: the leaf
hypotheses (`hload`, `htotalLoad`, `leaf_bound`) are discharged from the
`FaithfulModel` fields; `terminal_hardening` and `geom_pair` remain as
named hypotheses (`geom_pair` is from external literature [2][7,10][9];
`terminal_hardening` connects via F4c + stream B). -/
theorem scalar_closure_faithful_full {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n) (S : ShadedTubes n)
    (M : FaithfulModel α n r S)
    (terminal_hardening : ∀ x ∈ faithfulTree0 s M.selOf, SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad (reroot (faithfulTree0 s M.selOf) x)
        (fun s' => M.termTubeOf (x ++ s')) (fun s' δ => M.loadOf (x ++ s') δ) t δ) ^ 2)
      (fun δ => S.unionVol δ * totalLoad (reroot (faithfulTree0 s M.selOf) x)
        (fun s' δ => M.loadOf (x ++ s') δ) δ))
    (geom_pair : ∀ x ∈ faithfulTree0 s M.selOf, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot (faithfulTree0 s M.selOf) x)
          (fun s' => M.termTubeOf (x ++ s')) (fun s' δ => M.loadOf (x ++ s') δ) t δ
          * termLoad (reroot (faithfulTree0 s M.selOf) x)
          (fun s' => M.termTubeOf (x ++ s')) (fun s' δ => M.loadOf (x ++ s') δ) t' δ
        else 0)
      (fun δ => S.unionVol δ * totalLoad (reroot (faithfulTree0 s M.selOf) x)
        (fun s' δ => M.loadOf (x ++ s') δ) δ)) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  apply scalar_closure_faithful_tree s M.selOf S M.termTubeOf M.loadOf
  · -- hload from model
    intro γ hγ δ hδ0 hδ1
    exact M.load_nonneg γ δ hδ0 hδ1
  · -- htotalLoad from model
    intro δ
    exact M.mass_conserved s δ
  · -- leaf_bound from model
    intro γ hγ δ hδ0 hδ1
    exact M.leaf_geometric γ δ hδ0 hδ1
  · exact terminal_hardening
  · exact geom_pair

/-! ## P0-3 acceptance: nontrivial FaithfulModel instance -/

/-- Helper: zero child mass gives empty packet children. -/
theorem packetChildren_empty_of_zero_mass {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n) (sel : PacketSelect α n r)
    (hzero : ∀ t, sel.childMass t = 0) :
    packetChildren s sel = ∅ := by
  unfold packetChildren
  rw [Finset.filter_false_of_mem]
  intro t _
  simp [hzero t]

/-- Helper: zero mass selection gives singleton selected tree. -/
theorem selectedTree_singleton_of_zero_mass {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r)
    (hzero : ∀ s' t, (selOf s').childMass t = 0) :
    selectedTree s selOf = {[s]} := by
  rw [selectedTree_unfold]
  have hempty : packetChildren s (selOf s) = ∅ :=
    packetChildren_empty_of_zero_mass s (selOf s) (hzero s)
  have hbi : (packetChildren s (selOf s)).attach.biUnion
      (fun x : ↥(packetChildren s (selOf s)) =>
        (selectedTree (x : DescentState α n) selOf).image (fun p => s :: p)) = ∅ := by
    rw [hempty]
    simp
  rw [hbi, Finset.union_empty]

/-- Helper: zero mass gives singleton faithful tree. -/
theorem faithfulTree0_singleton_of_zero_mass {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} (s : DescentState α n)
    (selOf : DescentState α n → PacketSelect α n r)
    (hzero : ∀ s' t, (selOf s').childMass t = 0) :
    faithfulTree0 s selOf = {[]} := by
  unfold faithfulTree0
  rw [selectedTree_singleton_of_zero_mass s selOf hzero]
  simp

/-- A concrete `ShadedTubes 1` with unit volumes. -/
noncomputable def unitShadedTubes : ShadedTubes 1 where
  shadeVol := fun _ _ => 1
  unionVol := fun _ => 1
  multiplicity := fun _ => 1
  shade_nonneg := fun _ _ _ _ => zero_le_one
  union_nonneg := fun _ _ _ => zero_le_one
  mult_pos := fun _ _ _ => zero_lt_one
  mult_eq := fun _ _ _ => by simp
  shade_le_union := fun _ _ _ _ => le_refl 1

/-- Acceptance test (TODO_GUIDANCE P0-3): a nontrivial `FaithfulModel`
instance for `n = 1 > 0`.

Uses zero child mass, so every `faithfulTree0 s selOf = {[]}` by the helper
lemmas. With `loadOf = 1` and `S = unitShadedTubes`:
- `mass_conserved`: `∑_{[]} 1 = 1 = ∑_{t:Fin 1} 1`;
- `leaf_geometric`: `1 ≤ 1`. -/
noncomputable def trivialFaithfulModel :
    FaithfulModel Unit 1 1 unitShadedTubes :=
  let selOf : DescentState Unit 1 → PacketSelect Unit 1 1 :=
    fun _ => ⟨fun _ => ∅, fun _ => 0⟩
  have hzero : ∀ s' t, (selOf s').childMass t = 0 := fun _ _ => rfl
  ⟨selOf, fun _ => 0, fun _ _ => 1,
    fun _ _ _ _ => zero_le_one,
    fun s δ => by
      rw [faithfulTree0_singleton_of_zero_mass s selOf hzero]
      -- treeLeaves {[]} = {[]}
      have hleaves : treeLeaves ({[]} : Finset (List (DescentState Unit 1))) = {[]} := by
        unfold treeLeaves
        ext γ
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · intro h
          rw [h]
          refine ⟨rfl, fun l' hl' _ => hl'⟩
      rw [hleaves]
      simp [unitShadedTubes],
    fun _ _ _ _ => by simp [unitShadedTubes]⟩

end FilteredDescent
