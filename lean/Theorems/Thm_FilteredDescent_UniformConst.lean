/-
Uniform subpower constant extraction (TODO_GUIDANCE P1-4).

From pointwise-in-`a` subpower bounds, extracts a UNIFORM constant `C`
valid for all proper vertices `a` simultaneously, at the cost of halving
the subpower exponent (ε → ε/2). This is the key lemma enabling the
fusion of F7 (pointwise `Hpred` hardening) with the well-founded induction
(subpower `Hpred`).

Moved here from `Thm_FilteredDescent_DescentInduction` to break the
import cycle: both `DescentInduction` and `FaithfulHardening` need it.
-/

import Definitions.Def_FilteredDescent_Tree
import Definitions.Def_FilteredDescent_Subpower
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

open FilteredDescent

namespace FilteredDescent

/-- Uniform predecessor constant: from subpower `Hpred` at each proper
vertex, extract a single `C ≥ 0` such that
`nodeAgg a ≤ C * δ^(-ε/2) * Bpred δ` for ALL proper `a` simultaneously. -/
theorem uniform_proper_const {α : Type} [DecidableEq α]
    (T : Finset (List α))
    (load : List α → ℝ → ℝ) (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred_sub : ∀ a ∈ T, a ≠ [] →
      SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) a) Bpred)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ T, a ≠ [] → ∀ δ : ℝ, 0 < δ → δ < 1 →
      nodeAgg T (fun γ => load γ δ) a ≤ C * δ ^ (-(ε / 2)) * Bpred δ := by
  classical
  have key : ∀ a ∈ T.filter (fun a => a ≠ []), ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        nodeAgg T (fun γ => load γ δ) a ≤ C * δ ^ (-(ε / 2)) * Bpred δ := by
    intro a ha
    obtain ⟨haT, hane⟩ := Finset.mem_filter.mp ha
    obtain ⟨Ca, hCa0, hCa⟩ := Hpred_sub a haT hane (ε / 2) (half_pos hε)
    exact ⟨Ca, hCa0, hCa⟩
  choose Cf hCf using key
  by_cases hSne : (T.filter (fun a => a ≠ [])).Nonempty
  · -- Finite max of the per-vertex constants.
    refine ⟨(T.filter (fun a => a ≠ [])).sup' hSne
      (fun a => if ha : a ∈ T.filter (fun a => a ≠ []) then Cf a ha else 0),
      ?_, ?_⟩
    · obtain ⟨a₀, ha₀⟩ := hSne
      have h1 : (0 : ℝ)
          ≤ (if ha : a₀ ∈ T.filter (fun a => a ≠ []) then Cf a₀ ha else 0) := by
        rw [dif_pos ha₀]
        exact (hCf a₀ ha₀).1
      exact le_trans h1 (Finset.le_sup'
        (fun a => if ha : a ∈ T.filter (fun a => a ≠ []) then Cf a ha else 0) ha₀)
    · intro a ha hane δ hδ0 hδ1
      have haS : a ∈ T.filter (fun a => a ≠ []) :=
        Finset.mem_filter.mpr ⟨ha, hane⟩
      have hle : (if ha' : a ∈ T.filter (fun a => a ≠ []) then Cf a ha' else 0)
          ≤ (T.filter (fun a => a ≠ [])).sup' hSne
            (fun a => if ha : a ∈ T.filter (fun a => a ≠ []) then Cf a ha else 0) :=
        Finset.le_sup'
          (fun a => if ha : a ∈ T.filter (fun a => a ≠ []) then Cf a ha else 0) haS
      rw [dif_pos haS] at hle
      have hbound := (hCf a haS).2 δ hδ0 hδ1
      have hKnn : (0 : ℝ) ≤ δ ^ (-(ε / 2)) * Bpred δ :=
        mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hδ0 _))
          (hBpred δ hδ0 hδ1)
      calc nodeAgg T (fun γ => load γ δ) a
          ≤ Cf a haS * δ ^ (-(ε / 2)) * Bpred δ := hbound
        _ = Cf a haS * (δ ^ (-(ε / 2)) * Bpred δ) := by ring
        _ ≤ ((T.filter (fun a => a ≠ [])).sup' hSne
              (fun a => if ha : a ∈ T.filter (fun a => a ≠ []) then Cf a ha else 0)) *
            (δ ^ (-(ε / 2)) * Bpred δ) :=
            mul_le_mul_of_nonneg_right hle hKnn
        _ = ((T.filter (fun a => a ≠ [])).sup' hSne
              (fun a => if ha : a ∈ T.filter (fun a => a ≠ []) then Cf a ha else 0)) *
            δ ^ (-(ε / 2)) * Bpred δ := by ring
  · -- No proper vertices: C = 0 works vacuously.
    refine ⟨0, le_rfl, fun a ha hane δ hδ0 hδ1 => ?_⟩
    have : a ∈ T.filter (fun a => a ≠ []) :=
      Finset.mem_filter.mpr ⟨ha, hane⟩
    have hempty : T.filter (fun a => a ≠ []) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hSne
    rw [hempty] at this
    simp at this

end FilteredDescent
