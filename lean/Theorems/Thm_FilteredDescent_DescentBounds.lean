import Theorems.Thm_FilteredDescent_DescentTree
import Theorems.Thm_FilteredDescent_DescentLeaves
import Theorems.Thm_FilteredDescent_SubtreeReroot
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-!
# Filtered descent — bounds on the constructed tree (paper §§6–9, M3–M4)

This file proves the quantitative bounds for the symmetric history-tree
model built in `Thm_FilteredDescent_DescentTree.lean`, on top of the leaf
characterization and fiber counting in
`Thm_FilteredDescent_DescentLeaves.lean`:

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

/-! ## Rerooted terminal loads -/

/-- `Dx`: the rerooted subtree load at `x` for terminal tube `t`
(paper (145) `D_{x,t}` in the symmetric model): sum of leaf loads over
the `(x,t)`-fiber. -/
noncomputable def Dx (H₀ : ℕ) (S : ShadedTubes n) (δ : ℝ) (hn : 0 < n)
    (x : List (DMark n B)) (t : Fin n) : ℝ :=
  ∑ γ ∈ fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t,
    descentLoad H₀ S δ hn γ

/-- `Dx` is the paper's `childTermLoad` (145) on the constructed tree. -/
theorem termLoad_reroot_eq (hn : 0 < n) (S : ShadedTubes n) (δ : ℝ)
    (x : List (DMark n B)) (t : Fin n) :
    Dx (C₀ := C₀) H₀ S δ hn x t
      = childTermLoad (descTree n B H₀ C₀) (termTube hn)
        (fun γ δ' => descentLoad H₀ S δ' hn γ) x t δ := rfl

/-- Fiber computation: `Dx x t = N_x(t) * (sv(t)/M)`. -/
theorem Dx_eq (hn : 0 < n)
    (S : ShadedTubes n) (δ : ℝ) (x : List (DMark n B)) (t : Fin n) :
    Dx (C₀ := C₀) H₀ S δ hn x t
      = ((fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t).card : ℝ)
        * (S.shadeVol t δ / (B ^ H₀ : ℝ)) := by
  unfold Dx
  have hterm : ∀ γ ∈ fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t,
      descentLoad H₀ S δ hn γ = S.shadeVol t δ / (B ^ H₀ : ℝ) := by
    intro γ hγ
    have ht : termTube hn γ = t := (Finset.mem_filter.mp hγ).2.2
    unfold descentLoad
    rw [ht]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-- `Dx` is nonnegative. -/
theorem Dx_nonneg (hn : 0 < n) (hB : 0 < B)
    (S : ShadedTubes n) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ < 1)
    (x : List (DMark n B)) (t : Fin n) :
    0 ≤ Dx (C₀ := C₀) H₀ S δ hn x t := by
  unfold Dx
  apply Finset.sum_nonneg
  intro γ hγ
  have hmem : γ ∈ treeLeaves (descTree n B H₀ C₀) :=
    Finset.mem_of_mem_filter _ hγ
  have hM : (0:ℝ) < (B ^ H₀ : ℝ) := by
    have h1 : 0 < B ^ H₀ := Nat.pow_pos hB
    exact_mod_cast h1
  exact descentLoad_nonneg S δ hδ1 hδ2 hn hmem hM

/-- `Dx x t ≤ unionVol`: from `N_x(t) ≤ M` and `sv(t) ≤ unionVol`. -/
theorem Dx_le_unionVol (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    (S : ShadedTubes n) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ < 1)
    (x : List (DMark n B)) (t : Fin n) :
    Dx (C₀ := C₀) H₀ S δ hn x t ≤ S.unionVol δ := by
  rw [Dx_eq hn S δ x t]
  have hMpos : (0:ℝ) < (B ^ H₀ : ℝ) := by
    have h1 : 0 < B ^ H₀ := Nat.pow_pos hB
    exact_mod_cast h1
  have hNMdiv : ((fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t).card : ℝ)
      / (B ^ H₀ : ℝ) ≤ 1 := by
    rw [div_le_one hMpos]
    have hle := fiber_card_le (H₀ := H₀) hn hB hC x t
    exact_mod_cast hle
  have hsv : S.shadeVol t δ ≤ S.unionVol δ := S.shade_le_union _ _ hδ1 hδ2
  have hsvnn : 0 ≤ S.shadeVol t δ := S.shade_nonneg _ _ hδ1 hδ2
  calc ((fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t).card : ℝ)
        * (S.shadeVol t δ / (B ^ H₀ : ℝ))
      = ((fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t).card : ℝ)
        / (B ^ H₀ : ℝ) * S.shadeVol t δ := by ring
    _ ≤ 1 * S.unionVol δ := mul_le_mul hNMdiv hsv hsvnn (by norm_num)
    _ = S.unionVol δ := one_mul _

/-- Symmetric terminal hardening (M3, paper (148) in the symmetric model):
`∑ t, (Dx t)² ≤ unionVol * ∑ t, Dx t`, proved pointwise from
`Dx t = (N_t/M) * sv(t)` with `N_t ≤ M` and `sv(t) ≤ unionVol`. -/
theorem terminal_hardening_symm (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    (S : ShadedTubes n) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ < 1)
    (x : List (DMark n B)) :
    ∑ t : Fin n, (Dx (C₀ := C₀) H₀ S δ hn x t)^2
      ≤ S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t := by
  have hpt : ∀ t : Fin n,
      (Dx (C₀ := C₀) H₀ S δ hn x t)^2 ≤ S.unionVol δ * Dx (C₀ := C₀) H₀ S δ hn x t := by
    intro t
    have hD : 0 ≤ Dx (C₀ := C₀) H₀ S δ hn x t :=
      Dx_nonneg hn hB S δ hδ1 hδ2 x t
    have hU : Dx (C₀ := C₀) H₀ S δ hn x t ≤ S.unionVol δ :=
      Dx_le_unionVol hn hB hC S δ hδ1 hδ2 x t
    calc (Dx (C₀ := C₀) H₀ S δ hn x t)^2
        = Dx (C₀ := C₀) H₀ S δ hn x t * Dx (C₀ := C₀) H₀ S δ hn x t := sq _
      _ ≤ Dx (C₀ := C₀) H₀ S δ hn x t * S.unionVol δ :=
          mul_le_mul_of_nonneg_left hU hD
      _ = S.unionVol δ * Dx (C₀ := C₀) H₀ S δ hn x t := mul_comm _ _
  calc ∑ t : Fin n, (Dx (C₀ := C₀) H₀ S δ hn x t)^2
      ≤ ∑ t : Fin n, S.unionVol δ * Dx (C₀ := C₀) H₀ S δ hn x t :=
        Finset.sum_le_sum (fun t _ => hpt t)
    _ = S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t := by
        rw [Finset.mul_sum]

/-- Symmetric geometric pair bound (M4, crude): the off-diagonal pair sum
is bounded via `Dx t' ≤ unionVol` from the fiber computation.  This is
*not* the paper's sharp (53)/(177)/(81) (an external input to the main
gate); it is the explicit crude bound available in the symmetric model. -/
theorem geom_pair_symm (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    (S : ShadedTubes n) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ < 1)
    (x : List (DMark n B)) :
    ∑ t : Fin n, ∑ t' : Fin n,
        (if t ≠ t' then Dx (C₀ := C₀) H₀ S δ hn x t * Dx (C₀ := C₀) H₀ S δ hn x t' else 0)
      ≤ ((n : ℝ) - 1) * S.unionVol δ
        * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t := by
  have hU : ∀ t' : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t' ≤ S.unionVol δ :=
    fun t' => Dx_le_unionVol hn hB hC S δ hδ1 hδ2 x t'
  have hD : ∀ t : Fin n, 0 ≤ Dx (C₀ := C₀) H₀ S δ hn x t :=
    fun t => Dx_nonneg hn hB S δ hδ1 hδ2 x t
  -- inner sum over t' ≠ t
  have hinner : ∀ t : Fin n,
      ∑ t' : Fin n, (if t ≠ t' then Dx (C₀ := C₀) H₀ S δ hn x t * Dx (C₀ := C₀) H₀ S δ hn x t' else 0)
        ≤ ((n : ℝ) - 1) * S.unionVol δ * Dx (C₀ := C₀) H₀ S δ hn x t := by
    intro t
    have h1 : ∑ t' : Fin n,
          (if t ≠ t' then Dx (C₀ := C₀) H₀ S δ hn x t * Dx (C₀ := C₀) H₀ S δ hn x t' else 0)
        = Dx (C₀ := C₀) H₀ S δ hn x t
          * ∑ t' ∈ Finset.univ.filter (fun t' : Fin n => t ≠ t'),
            Dx (C₀ := C₀) H₀ S δ hn x t' := by
      rw [← Finset.sum_filter, Finset.mul_sum]
    rw [h1]
    have h2 : ∑ t' ∈ Finset.univ.filter (fun t' : Fin n => t ≠ t'),
          Dx (C₀ := C₀) H₀ S δ hn x t'
        ≤ ((n : ℝ) - 1) * S.unionVol δ := by
      have hle : ∑ t' ∈ Finset.univ.filter (fun t' : Fin n => t ≠ t'),
            Dx (C₀ := C₀) H₀ S δ hn x t'
          ≤ ∑ t' ∈ Finset.univ.filter (fun t' : Fin n => t ≠ t'),
            S.unionVol δ :=
        Finset.sum_le_sum (fun t' _ => hU t')
      rw [Finset.sum_const, nsmul_eq_mul] at hle
      have hcard : (Finset.univ.filter (fun t' : Fin n => t ≠ t')).card
          = n - 1 := by
        have h1 : Finset.univ.filter (fun t' : Fin n => t ≠ t')
            = Finset.univ \ {t} := by
          ext t'
          simp [ne_comm]
        rw [h1, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
          Finset.inter_univ, Finset.card_singleton]
      rw [hcard] at hle
      have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        simp
      rw [hcast] at hle
      exact hle
    calc Dx (C₀ := C₀) H₀ S δ hn x t
          * ∑ t' ∈ Finset.univ.filter (fun t' : Fin n => t ≠ t'),
            Dx (C₀ := C₀) H₀ S δ hn x t'
        ≤ Dx (C₀ := C₀) H₀ S δ hn x t * (((n : ℝ) - 1) * S.unionVol δ) :=
          mul_le_mul_of_nonneg_left h2 (hD t)
      _ = ((n : ℝ) - 1) * S.unionVol δ * Dx (C₀ := C₀) H₀ S δ hn x t := by ring
  calc ∑ t : Fin n, ∑ t' : Fin n,
        (if t ≠ t' then Dx (C₀ := C₀) H₀ S δ hn x t * Dx (C₀ := C₀) H₀ S δ hn x t' else 0)
      ≤ ∑ t : Fin n, ((n : ℝ) - 1) * S.unionVol δ * Dx (C₀ := C₀) H₀ S δ hn x t :=
        Finset.sum_le_sum (fun t _ => hinner t)
    _ = ((n : ℝ) - 1) * S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t := by
        rw [Finset.mul_sum]

/-- Total load identity (M4, paper (136) relativized): `∑ t, Dx x t` is the
node aggregate at `x`, hence the total load of the rerooted tree. -/
theorem htotalLoad_symm (hn : 0 < n)
    (S : ShadedTubes n) (δ : ℝ) (x : List (DMark n B)) :
    ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t
      = totalLoad (reroot (descTree n B H₀ C₀) x)
        (fun s δ' => descentLoad H₀ S δ' hn (x ++ s)) δ := by
  rw [reroot_totalLoad (descTree n B H₀ C₀) x
    (fun γ δ' => descentLoad H₀ S δ' hn γ) δ]
  -- goal: ∑ t, Dx x t = nodeAgg T (fun γ => descentLoad ...) x
  have hfib : ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t
      = ∑ γ ∈ (treeLeaves (descTree n B H₀ C₀)).filter (fun γ => x <+: γ),
        descentLoad H₀ S δ hn γ := by
    have hfw := Finset.sum_fiberwise_of_maps_to
      (s := (treeLeaves (descTree n B H₀ C₀)).filter (fun γ => x <+: γ))
      (t := (Finset.univ : Finset (Fin n)))
      (g := termTube hn)
      (h := fun γ _ => Finset.mem_univ _)
      (f := fun γ => descentLoad H₀ S δ hn γ)
    rw [← hfw]
    apply Finset.sum_congr rfl
    intro t _
    unfold Dx fiberFinset
    rw [Finset.filter_filter]
  rw [hfib]
  unfold nodeAgg
  rw [Finset.sum_filter]

/-- `termLoad` on the rerooted tree is `Dx`: reindex via
`reroot_sum_leaves`, using `x ++ γ.drop x.length = γ` on the fiber. -/
theorem termLoad_reroot_Dx (hn : 0 < n)
    (S : ShadedTubes n) (δ : ℝ) (x : List (DMark n B)) (t : Fin n) :
    termLoad (reroot (descTree n B H₀ C₀) x) (fun s => termTube hn (x ++ s))
      (fun s δ' => descentLoad H₀ S δ' hn (x ++ s)) t δ
      = Dx (C₀ := C₀) H₀ S δ hn x t := by
  have hLHS : termLoad (reroot (descTree n B H₀ C₀) x)
        (fun s => termTube hn (x ++ s))
        (fun s δ' => descentLoad H₀ S δ' hn (x ++ s)) t δ
      = ∑ s ∈ treeLeaves (reroot (descTree n B H₀ C₀) x),
        (fun s => if termTube hn (x ++ s) = t
          then descentLoad H₀ S δ hn (x ++ s) else 0) s := by
    unfold termLoad
    rw [Finset.sum_filter]
  rw [hLHS,
    reroot_sum_leaves (descTree n B H₀ C₀) x
      (fun s => if termTube hn (x ++ s) = t
        then descentLoad H₀ S δ hn (x ++ s) else 0)]
  have hRHS : ∀ γ ∈ (treeLeaves (descTree n B H₀ C₀)).filter (fun γ => x <+: γ),
      (fun s => if termTube hn (x ++ s) = t
        then descentLoad H₀ S δ hn (x ++ s) else 0) (γ.drop x.length)
      = (if termTube hn γ = t then descentLoad H₀ S δ hn γ else 0) := by
    intro γ hγ
    have hpre : x <+: γ := (Finset.mem_filter.mp hγ).2
    have heq : x ++ γ.drop x.length = γ := append_drop_of_prefix hpre
    simp only []
    rw [heq]
  rw [Finset.sum_congr rfl (fun γ hγ => hRHS γ hγ),
    ← Finset.sum_filter, Finset.filter_filter]
  show ∑ a ∈ (treeLeaves (descTree n B H₀ C₀)).filter
      (fun a => x <+: a ∧ termTube hn a = t), descentLoad H₀ S δ hn a
    = ∑ γ ∈ fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn x t,
      descentLoad H₀ S δ hn γ
  rfl

end FilteredDescent
