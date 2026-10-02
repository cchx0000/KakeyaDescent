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

end FilteredDescent
