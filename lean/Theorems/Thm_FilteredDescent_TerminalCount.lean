import Definitions.Def_FilteredDescent_Subpower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# M8b — Terminal incidence count (paper (130) → (214))

The terminal unweighting (paper (130)): the union volume is at least
`α / (2M)` times the total shading volume, where `α` is the retained mass
and `M` the multiplicity, at every scale `δ ∈ (0,1)`.  With `α⁻¹` and `M`
both subpower in `δ` (uniformly), the incidence count (paper (214))
follows:

  `Σ_T |Y(T)| ≲ |⋃_T Y(T)|`  uniformly for `δ ∈ (0,1)`.
-/

namespace FilteredDescent

theorem terminal_incidence_count {n : ℕ} (hn : 0 < n)
    (shadeVol : Fin n → ℝ → ℝ) (unionVol : ℝ → ℝ)
    (hsh : ∀ t δ, 0 < δ → δ < 1 → 0 ≤ shadeVol t δ)
    (hu : ∀ δ, 0 < δ → δ < 1 → 0 ≤ unionVol δ)
    (α M : ℝ → ℝ)
    (hα : ∀ δ, 0 < δ → δ < 1 → 0 < α δ)
    (hM : ∀ δ, 0 < δ → δ < 1 → 0 < M δ)
    (hαsub : SubpowerLE (fun _ => 1) α)
    (hMsub : SubpowerLE M (fun _ => 1))
    (hcount :
      ∀ δ, 0 < δ → δ < 1 →
        unionVol δ ≥ α δ / (2 * M δ) * ∑ t, shadeVol t δ) :
    SubpowerLE (fun δ => ∑ t, shadeVol t δ) unionVol := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨C₁, hC₁, hC₁bound⟩ := hαsub (ε / 2) hε2
  obtain ⟨C₂, hC₂, hC₂bound⟩ := hMsub (ε / 2) hε2
  refine ⟨2 * C₁ * C₂, by positivity, fun δ hδ0 hδ1 => ?_⟩
  have hαδ : 0 < α δ := hα δ hδ0 hδ1
  have hMδ : 0 < M δ := hM δ hδ0 hδ1
  have huδ : 0 ≤ unionVol δ := hu δ hδ0 hδ1
  have hXpos : 0 < δ ^ (-(ε/2)) := Real.rpow_pos_of_pos hδ0 _
  have h1 : (1 : ℝ) ≤ C₁ * δ ^ (-(ε/2)) * α δ := hC₁bound δ hδ0 hδ1
  have h2 : M δ ≤ C₂ * δ ^ (-(ε/2)) := by
    have h := hC₂bound δ hδ0 hδ1
    rwa [mul_one] at h
  have hαinv_le : 1 / α δ ≤ C₁ * δ ^ (-(ε/2)) := by
    have hαne : α δ ≠ 0 := ne_of_gt hαδ
    calc 1 / α δ = (1 / α δ) * 1 := by ring
      _ ≤ (1 / α δ) * (C₁ * δ ^ (-(ε/2)) * α δ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C₁ * δ ^ (-(ε/2)) := by field_simp
  have hXX : δ ^ (-(ε/2)) * δ ^ (-(ε/2)) = δ ^ (-ε) := by
    rw [← Real.rpow_add hδ0]
    congr 1
    ring
  have hMain : 2 * M δ / α δ ≤ (2 * C₁ * C₂) * δ ^ (-ε) := by
    have h1 : 2 * M δ / α δ = 2 * (M δ * (1 / α δ)) := by ring
    rw [h1, ← hXX]
    have hmul : M δ * (1 / α δ) ≤ (C₂ * δ ^ (-(ε/2))) * (C₁ * δ ^ (-(ε/2))) :=
      mul_le_mul h2 hαinv_le (by positivity) (by positivity)
    calc 2 * (M δ * (1 / α δ))
        ≤ 2 * ((C₂ * δ ^ (-(ε/2))) * (C₁ * δ ^ (-(ε/2)))) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = (2 * C₁ * C₂) * (δ ^ (-(ε/2)) * δ ^ (-(ε/2))) := by ring
  have hSU : ∑ t, shadeVol t δ ≤ (2 * M δ / α δ) * unionVol δ := by
    have hc := hcount δ hδ0 hδ1
    have h1 : ∑ t, shadeVol t δ
        = (1 / (α δ / (2 * M δ))) * ((α δ / (2 * M δ)) * ∑ t, shadeVol t δ) := by
      field_simp
    rw [h1]
    calc (1 / (α δ / (2 * M δ))) * ((α δ / (2 * M δ)) * ∑ t, shadeVol t δ)
        ≤ (1 / (α δ / (2 * M δ))) * unionVol δ :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (2 * M δ / α δ) * unionVol δ := by field_simp
  calc ∑ t, shadeVol t δ
      ≤ (2 * M δ / α δ) * unionVol δ := hSU
    _ ≤ ((2 * C₁ * C₂) * δ ^ (-ε)) * unionVol δ :=
        mul_le_mul_of_nonneg_right hMain huδ
    _ = (2 * C₁ * C₂) * δ ^ (-ε) * unionVol δ := by ring

end FilteredDescent
