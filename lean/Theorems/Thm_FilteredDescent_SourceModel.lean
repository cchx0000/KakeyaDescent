import Theorems.Thm_FilteredDescent_FaithfulTreeBridge
import Definitions.Def_FilteredDescent_PacketSource

/-!
# Source-derived faithful model (TODO_GUIDANCE item 8)

Constructs a `FaithfulModel` from a `PacketSource`, PROVING the
`mass_conserved` field (i.e. `htotalLoad`) via the representative-leaf
lemma `mass_conserved_of_rep`, rather than assuming it.

The tree structure (`selOf`) is derived from the packet source via
`packetSelectOfSource` (item 7). The tube assignment `termTube` and
representative leaves `rep` are explicit geometric input: they witness
that the faithful tree covers the tube family. The mass conservation
identity itself is a THEOREM (from `mass_conserved_of_rep`), not a hypothesis.

Honest scope: the full derivation of `termTube`/`rep` from the packet
geometry (support covering) is the remaining step; here they are parameters.
What item 8 discharges is `htotalLoad` as an assumed identity.
-/

namespace FilteredDescent

/-- A `FaithfulModel` derived from a packet source.

The `selOf` comes from `packetSelectOfSource` (item 7: child mass from the
packet law). The `loadOf` concentrates each tube's shading mass on its
representative leaf; `mass_conserved` is PROVED by `mass_conserved_of_rep`.
-/
noncomputable def FaithfulModel.ofPacketSource {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} [NeZero n] (src : PacketSource α n r) (S : ShadedTubes n)
    (termTube : List (DescentState α n) → Fin n)
    (rep : Fin n → List (DescentState α n))
    (hrep_mem : ∀ (s : DescentState α n) (t : Fin n),
      rep t ∈ treeLeaves (faithfulTree0 s (fun s => packetSelectOfSource src s)))
    (hrep_tube : ∀ t, termTube (rep t) = t) :
    FaithfulModel α n r S where
  selOf := fun s => packetSelectOfSource src s
  termTubeOf := termTube
  loadOf := fun γ δ =>
    if γ ∈ Finset.image rep Finset.univ
    then S.shadeVol (termTube γ) δ else 0
  load_nonneg := by
    intro γ δ hδ0 hδ1
    by_cases h : γ ∈ Finset.image rep Finset.univ
    · rw [if_pos h]
      exact S.shade_nonneg _ _ hδ0 hδ1
    · rw [if_neg h]
  mass_conserved := by
    intro s δ
    exact mass_conserved_of_rep S (faithfulTree0 s (fun s => packetSelectOfSource src s))
      termTube rep (hrep_mem s) hrep_tube δ
  leaf_geometric := by
    intro γ δ hδ0 hδ1
    by_cases h : γ ∈ Finset.image rep Finset.univ
    · rw [if_pos h]
      exact S.shade_le_union _ _ hδ0 hδ1
    · rw [if_neg h]
      -- 0 ≤ unionVol: from a tube's shading mass (Fin n nonempty as n ≠ 0)
      calc (0 : ℝ) ≤ S.shadeVol ⟨0, NeZero.pos n⟩ δ := S.shade_nonneg _ _ hδ0 hδ1
        _ ≤ S.unionVol δ := S.shade_le_union _ _ hδ0 hδ1

/-- Scalar closure from a packet source: `htotalLoad` is discharged.

Takes a `PacketSource` plus the geometric covering data (`termTube`/`rep`),
constructs the `FaithfulModel` via `ofPacketSource` (whose `mass_conserved`
is PROVED), and applies `scalar_closure_faithful_full`.

`htotalLoad` does NOT appear as a parameter: it is `M.mass_conserved`,
a theorem from `mass_conserved_of_rep`.
-/
theorem scalar_closure_from_source {α : Type} [Fintype α] [DecidableEq α]
    {n r : ℕ} [NeZero n] [Fintype (DescentState α n)]
    (s : DescentState α n) (S : ShadedTubes n)
    (src : PacketSource α n r)
    (termTube : List (DescentState α n) → Fin n)
    (rep : Fin n → List (DescentState α n))
    (hrep_mem : ∀ (s : DescentState α n) (t : Fin n),
      rep t ∈ treeLeaves (faithfulTree0 s (fun s => packetSelectOfSource src s)))
    (hrep_tube : ∀ t, termTube (rep t) = t)
    (L : HardeningLedger (DescentState α n) (n := n)
      (faithfulTree0 s (fun s => packetSelectOfSource src s)))
    (hlinkAt : ∀ (x : List (DescentState α n))
      (hx : x ∈ faithfulTree0 s (fun s => packetSelectOfSource src s)),
      NodeHLink L x hx termTube
        (FaithfulModel.ofPacketSource src S termTube rep hrep_mem hrep_tube).loadOf
        S.unionVol)
    (hquantAt : ∀ (x : List (DescentState α n))
      (hx : x ∈ faithfulTree0 s (fun s => packetSelectOfSource src s)),
      NodeHQuant L x hx termTube
        (FaithfulModel.ofPacketSource src S termTube rep hrep_mem hrep_tube).loadOf
        S.unionVol)
    (geom_pair : ∀ x ∈ faithfulTree0 s (fun s => packetSelectOfSource src s),
      SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot (faithfulTree0 s (fun s => packetSelectOfSource src s)) x)
          (fun s' => termTube (x ++ s'))
          (fun s' δ => (FaithfulModel.ofPacketSource src S termTube rep hrep_mem hrep_tube).loadOf (x ++ s') δ) t δ
          * termLoad (reroot (faithfulTree0 s (fun s => packetSelectOfSource src s)) x)
          (fun s' => termTube (x ++ s'))
          (fun s' δ => (FaithfulModel.ofPacketSource src S termTube rep hrep_mem hrep_tube).loadOf (x ++ s') δ) t' δ
        else 0)
      (fun δ => S.unionVol δ * totalLoad (reroot (faithfulTree0 s (fun s => packetSelectOfSource src s)) x)
        (fun s' δ => (FaithfulModel.ofPacketSource src S termTube rep hrep_mem hrep_tube).loadOf (x ++ s') δ) δ)) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  -- Instantiate the model; mass_conserved (htotalLoad) is proved, not assumed
  let M := FaithfulModel.ofPacketSource src S termTube rep hrep_mem hrep_tube
  exact scalar_closure_faithful_full s S M L hlinkAt hquantAt geom_pair

end FilteredDescent
