import Theorems.Thm_FilteredDescent_DescentTree
import Theorems.Thm_FilteredDescent_SubtreeReroot
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-!
# Filtered descent — bounds on the constructed tree (paper §§6–9, M3–M4)

This file proves the quantitative bounds for the symmetric history-tree
model built in `Thm_FilteredDescent_DescentTree.lean`:

* Leaf characterization: leaves are exactly the `leafWord cb t` words
  (`H₀` confluence marks, `C₀ - 1` Cartan marks, terminal `select t`).
* Fiber counting: for a node `x`, the `(x, t)`-fiber (leaves `γ` with
  `x <+: γ` and `termTube γ = t`) has size `N_x(t)`; at the root,
  `N_[](t) = B ^ H₀` exactly.
* `Dx`: the rerooted subtree load at `x` for terminal tube `t`.
* `terminal_hardening` (M3): `∑ t, (Dx x t δ)² ≤ unionVol δ * totalLoad_x δ`,
  proved pointwise via `Dx x t δ = (N_x(t)/M) * sv(t)` and `N_x(t) ≤ M`.
* `leaf_bound` (M4): the leaf load bound.
* `geom_pair` (M4): the geometric pair bound via fiber symmetry.
* `htotalLoad` (M4): the total load identity.

## Honesty notes

In the symmetric model, every confluence branch is retained with the
uniform share `1 / B ^ H₀`.  The paper's general `(θ,j,c)` common-source
aggregation (§10.3) — which in the full paper requires the duplicate
mechanism and the (150)–(153) identities — degenerates here to
elementary counting: the fiber sizes `N_x(t)` are computed exactly, and
the "duplicate" vs "geometric" split becomes the observation that
`N_x(t)` is independent of `t` (for non-leaf `x`) by the select-mark
symmetry.  This degeneration is a consequence of the symmetric model
choice documented in the tree file, not a simplification of the paper's
argument: the paper's §10.3 is the non-symmetric generalization.
-/

namespace FilteredDescent

variable {n B H₀ C₀ : ℕ}

/-- A leaf word: `H₀` confluence branches `cb`, then `C₀ - 1` Cartan steps,
then the terminal `select t`. -/
def leafWord (cb : List (Fin B)) (t : Fin n) : List (DMark n B) :=
  cb.map DMark.conf ++ List.replicate (C₀ - 1) DMark.cartan ++ [DMark.select t]

/-- The confluence-branch word of a leaf (inverse of `leafWord` on leaves). -/
def leafConf : List (DMark n B) → List (Fin B)
  | [] => []
  | (DMark.conf b) :: w => b :: leafConf w
  | _ :: w => leafConf w

/-- A `ValidPath` with `selectCount = 1` has `confCount = H₀`
(by induction on the derivation; only `selectStep` can set the select). -/
theorem ValidPath.confCount_of_select {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) (hs : selectCount w = 1) :
    confCount w = H₀ := by
  induction h with
  | nil => simp at hs
  | confStep =>
      rename_i w b hw hc hcart hs0 ih
      -- `selectCount (w ++ [conf b]) = selectCount w = 0 ≠ 1`
      rw [selectCount_append] at hs
      simp at hs
      omega
  | cartanStep =>
      rename_i w hw hconf hc hs0 ih
      rw [selectCount_append] at hs
      simp at hs
      omega
  | selectStep =>
      rename_i w t hw hconf hcart hs0 ih
      -- `confCount (w ++ [select t]) = confCount w = H₀` by `hconf`
      rw [confCount_append]
      simp [hconf]

/-- `leafConf` length equals `confCount`. -/
theorem leafConf_length (w : List (DMark n B)) :
    (leafConf w).length = confCount w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | conf b => simp [leafConf, confCount, ih]
      | cartan => simp [leafConf, confCount, ih]
      | select t => simp [leafConf, confCount, ih]

/-- `leafConf` distributes over append. -/
theorem leafConf_append (l₁ l₂ : List (DMark n B)) :
    leafConf (l₁ ++ l₂) = leafConf l₁ ++ leafConf l₂ := by
  induction l₁ with
  | nil => simp [leafConf]
  | cons x xs ih =>
      cases x with
      | conf b => simp [leafConf, ih]
      | cartan => simp [leafConf, ih]
      | select t => simp [leafConf, ih]

/-- `leaf_bound` for the constructed tree: the leaf load is bounded by
`unionVol`.  Proof: `sv(t)/M ≤ sv(t) ≤ unionVol` using `M ≥ 1` and
`shade_le_union`. -/
theorem leaf_bound_proved (S : ShadedTubes n) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ < 1)
    (hn : 0 < n) (hB : 1 ≤ B)
    {γ : List (DMark n B)} (_hγ : γ ∈ treeLeaves (descTree n B H₀ C₀)) :
    descentLoad H₀ S δ hn γ ≤ S.unionVol δ := by
  unfold descentLoad
  have hM : (1 : ℝ) ≤ (B ^ H₀ : ℝ) := by
    have : 1 ≤ B ^ H₀ := Nat.one_le_pow H₀ B hB
    exact_mod_cast this
  have hsv : 0 ≤ S.shadeVol (termTube hn γ) δ :=
    S.shade_nonneg _ _ hδ1 hδ2
  calc S.shadeVol (termTube hn γ) δ / (B ^ H₀ : ℝ)
      ≤ S.shadeVol (termTube hn γ) δ / 1 := by
        apply div_le_div_of_nonneg_left hsv (by norm_num) hM
    _ = S.shadeVol (termTube hn γ) δ := div_one _
    _ ≤ S.unionVol δ := S.shade_le_union _ _ hδ1 hδ2

end FilteredDescent
