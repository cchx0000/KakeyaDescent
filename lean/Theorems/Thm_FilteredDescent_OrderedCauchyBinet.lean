import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Perm
import Theorems.Thm_ClassicalGaps_cauchy_binet_det

/-!
# M2 — Ordered Cauchy–Binet packet identity (paper (6))

Summing the squared packet Gram determinant over all ordered `d`-tuples of
tubes gives `d!` times the determinant of the weighted Gram matrix.
Non-distinct tuples contribute `0` (repeated column).  This is the ordered
(packet) form of Cauchy–Binet; it is distinct from the standard
subset-sum form `ClassicalGaps.cauchy_binet_det` already on the platform.
-/

namespace FilteredDescent

open Matrix Finset

-- Helper 1: Gram matrix identification.
private lemma gram_eq {n d : ℕ} (s : Fin n → (Fin d → ℝ)) (w : Fin n → ℝ) :
    Matrix.of (fun a b : Fin d => ∑ i, w i * s i a * s i b)
      = (Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ * Matrix.diagonal w *
        (Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)) := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- Helper 2: (Smatᵀ * SqW) * (SqW * Smat) = Smatᵀ * W * Smat.
private lemma AB_eq {n d : ℕ} (s : Fin n → (Fin d → ℝ)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ *
      Matrix.diagonal (fun i : Fin n => Real.sqrt (w i))) *
     (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
      Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)))
      = (Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ * Matrix.diagonal w *
        (Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)) := by
  have hSq : Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
      Matrix.diagonal (fun i : Fin n => Real.sqrt (w i))
      = Matrix.diagonal w := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg
    funext i
    show Real.sqrt (w i) * Real.sqrt (w i) = w i
    exact Real.mul_self_sqrt (hw i)
  have hassoc : (((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ *
      Matrix.diagonal (fun i : Fin n => Real.sqrt (w i))) *
      (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
      Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)))
      = (((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ *
        (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
         Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)))) *
        Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)) := by
    rw [Matrix.mul_assoc ((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ)
          (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)))
          ((Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
            Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))),
        ← Matrix.mul_assoc (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)))
          (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)))
          (Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)),
        Matrix.mul_assoc ((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ)
          ((Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
            Matrix.diagonal (fun i : Fin n => Real.sqrt (w i))))
          (Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))]
  rw [hassoc, hSq]

-- Helper 3: subset determinant product.
private lemma sub_det_eq {n d : ℕ} (s : Fin n → (Fin d → ℝ)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (e : Fin d → Fin n) :
    (((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ *
      Matrix.diagonal (fun i : Fin n => Real.sqrt (w i))).submatrix id e).det *
    ((Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
      Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)).submatrix e id).det
      = (∏ j : Fin d, (Real.sqrt (w (e j)))^2) *
        (Matrix.of (fun a b : Fin d => s (e b) a)).det ^ 2 := by
  have hA : (((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ *
      Matrix.diagonal (fun i : Fin n => Real.sqrt (w i))).submatrix id e)
      = Matrix.of (fun a b : Fin d => s (e b) a) *
        Matrix.diagonal (fun j : Fin d => Real.sqrt (w (e j))) := by
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hB : ((Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
      Matrix.of (fun (i : Fin n) (a : Fin d) => s i a)).submatrix e id)
      = Matrix.diagonal (fun j : Fin d => Real.sqrt (w (e j))) *
        (Matrix.of (fun a b : Fin d => s (e b) a))ᵀ := by
    ext j b
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply,
      Matrix.of_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hprod : (∏ j : Fin d, Real.sqrt (w (e j))) ^ 2
      = ∏ j : Fin d, (Real.sqrt (w (e j)))^2 := (Finset.prod_pow _ _ _).symm
  rw [hA, hB]
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  rw [← hprod]
  ring

-- Helper 4: product conversion.
private lemma prod_sqrt_eq {n d : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (S : Finset (Fin n)) (hS : S.card = d) :
    (∏ j : Fin d, (Real.sqrt (w (((S.orderIsoOfFin hS j : ↥S) : Fin n))))^2)
      = ∏ i ∈ S, w i := by
  have step1 : (∏ j : Fin d, (Real.sqrt (w (((S.orderIsoOfFin hS j : ↥S) : Fin n))))^2)
      = ∏ j : Fin d, w (((S.orderIsoOfFin hS j : ↥S) : Fin n)) := by
    apply Finset.prod_congr rfl
    intro j _
    exact Real.sq_sqrt (hw _)
  rw [step1]
  have step2 : (∏ j : Fin d, w (((S.orderIsoOfFin hS j : ↥S) : Fin n)))
      = ∏ x : ↥S, w (x : Fin n) := by
    have h := Equiv.prod_comp (S.orderIsoOfFin hS).toEquiv (fun x : ↥S => w (x : Fin n))
    simpa using h
  rw [step2]
  exact Finset.prod_coe_sort _ _

-- Helper 5: non-injective det zero.
private lemma det_zero_of_not_injective {n d : ℕ} (s : Fin n → (Fin d → ℝ))
    (U : Fin d → Fin n) (hU : ¬ Function.Injective U) :
    (Matrix.of (fun a b : Fin d => s (U b) a)).det = 0 := by
  rw [Function.not_injective_iff] at hU
  obtain ⟨b₁, b₂, h_eq, h_ne⟩ := hU
  apply Matrix.det_zero_of_column_eq h_ne
  intro a
  simp only [Matrix.of_apply]
  rw [h_eq]

-- Helper 6: fiber over S is in bijection with (Fin d ≃ ↥S).
private noncomputable def fiberEquiv {n d : ℕ} (S : Finset (Fin n)) :
    {U : Fin d → Fin n // Function.Injective U ∧ Finset.univ.image U = S} ≃ (Fin d ≃ ↥S) where
  toFun := fun ⟨U, h_inj, h_img⟩ =>
    Equiv.ofBijective (fun j : Fin d => (⟨U j, by
      rw [← h_img]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩ : ↥S)) ⟨
      fun j₁ j₂ h => h_inj (congrArg Subtype.val h),
      fun x => by
        obtain ⟨i, hi⟩ := x
        have : i ∈ Finset.univ.image U := h_img ▸ hi
        rw [Finset.mem_image] at this
        obtain ⟨j, _, rfl⟩ := this
        exact ⟨j, rfl⟩⟩
  invFun := fun σ => ⟨fun j => (σ j : Fin n), by
    intro j₁ j₂ h
    have : σ j₁ = σ j₂ := Subtype.ext h
    exact σ.injective this,
    by
      ext i
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact (σ j).2
      · intro hi
        obtain ⟨j, hj⟩ := σ.surjective ⟨i, hi⟩
        exact ⟨j, congrArg Subtype.val hj⟩⟩
  left_inv := fun ⟨U, h_inj, h_img⟩ => by
    apply Subtype.ext
    funext j
    rfl
  right_inv := fun σ => by
    apply Equiv.ext
    intro j
    rfl

-- Helper 7: card (Fin d ≃ ↥S) = d!.
private lemma card_equiv_fin {n d : ℕ} (S : Finset (Fin n)) (hS : S.card = d) :
    Fintype.card (Fin d ≃ ↥S) = Nat.factorial d := by
  have h1 : Fintype.card ↥S = d := by
    rw [Fintype.card_coe]
    exact hS
  have h2 : (Fin d ≃ ↥S) ≃ (Fin d ≃ Fin d) :=
    { toFun := fun σ => σ.trans (Fintype.equivFinOfCardEq h1),
      invFun := fun τ => τ.trans (Fintype.equivFinOfCardEq h1).symm,
      left_inv := fun σ => by
        show ((σ.trans (Fintype.equivFinOfCardEq h1)).trans
          (Fintype.equivFinOfCardEq h1).symm) = σ
        rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl],
      right_inv := fun τ => by
        show ((τ.trans (Fintype.equivFinOfCardEq h1).symm).trans
          (Fintype.equivFinOfCardEq h1)) = τ
        rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl] }
  calc Fintype.card (Fin d ≃ ↥S)
      = Fintype.card (Fin d ≃ Fin d) := Fintype.card_congr h2
    _ = Nat.factorial d := by
        have h : Fintype.card (Equiv.Perm (Fin d)) = (Fintype.card (Fin d)).factorial :=
          Fintype.card_perm
        rw [Fintype.card_fin] at h
        exact h

-- Helper 8: permutation invariance of det^2.
private lemma det_sq_perm_invariant {n d : ℕ} (s : Fin n → (Fin d → ℝ))
    (e : Fin d → Fin n) (σ : Equiv.Perm (Fin d))
    (U : Fin d → Fin n) (hU : ∀ j, U j = e (σ j)) :
    (Matrix.of (fun a b : Fin d => s (U b) a)).det ^ 2
      = (Matrix.of (fun a b : Fin d => s (e b) a)).det ^ 2 := by
  have hMU : Matrix.of (fun a b : Fin d => s (U b) a)
      = (Matrix.of (fun a b : Fin d => s (e b) a)).submatrix id σ := by
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, Matrix.of_apply]
    rw [hU b]
  rw [hMU, Matrix.det_permute']
  have hsign : ((Equiv.Perm.sign σ : ℤˣ) : ℝ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  calc (((Equiv.Perm.sign σ : ℤˣ) : ℝ) * (Matrix.of (fun a b : Fin d => s (e b) a)).det) ^ 2
      = ((Equiv.Perm.sign σ : ℤˣ) : ℝ) ^ 2 * (Matrix.of (fun a b : Fin d => s (e b) a)).det ^ 2 := by
        ring
    _ = (Matrix.of (fun a b : Fin d => s (e b) a)).det ^ 2 := by
        rw [hsign, one_mul]

-- Helper 9: Step 4 — ordered sum equals d! times subset sum.
-- The term for S uses dite to avoid dependent types in the sum.
private lemma step4 {n d : ℕ} (s : Fin n → (Fin d → ℝ)) (w : Fin n → ℝ) :
    ∑ U : Fin d → Fin n, (∏ j, w (U j)) * (Matrix.of (fun a b : Fin d => s (U b) a)).det ^ 2
      = (Nat.factorial d : ℝ) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        (if hS : S.card = d then
          (∏ i ∈ S, w i) * (Matrix.of (fun a b : Fin d =>
            s (((S.orderIsoOfFin hS b : ↥S) : Fin n)) a)).det ^ 2
        else 0) := by
  -- Define g
  set f_sum : (Fin d → Fin n) → ℝ := fun U =>
    (∏ j, w (U j)) * (Matrix.of (fun a b : Fin d => s (U b) a)).det ^ 2 with hf_sum
  -- 4a: restrict to injective
  have step4a : ∑ U : Fin d → Fin n, f_sum U
      = ∑ U ∈ Finset.univ.filter (fun U : Fin d → Fin n => Function.Injective U), f_sum U := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U _
    by_cases h : Function.Injective U
    · rw [if_pos h]
    · rw [if_neg h]
      simp only [hf_sum]
      rw [det_zero_of_not_injective s U h]
      ring
  rw [step4a]
  -- 4b: fiberwise over subsets
  have h_maps : ∀ U ∈ Finset.univ.filter (fun U : Fin d → Fin n => Function.Injective U),
      Finset.univ.image U ∈ (Finset.univ : Finset (Fin n)).powersetCard d := by
    intro U hU
    rw [Finset.mem_filter] at hU
    obtain ⟨_, h_inj⟩ := hU
    rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.subset_univ _
    · rw [Finset.card_image_of_injective _ h_inj, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun U : Fin d → Fin n => Finset.univ.image U)
    (t := (Finset.univ : Finset (Fin n)).powersetCard d) h_maps f_sum]
  -- 4c: each fiber sum = d! * term S
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS_mem
  -- S ∈ powersetCard, so S.card = d
  have hS : S.card = d := (Finset.mem_powersetCard.mp hS_mem).2
  -- The fiber
  set fiberS := (Finset.univ.filter (fun U : Fin d → Fin n => Function.Injective U)).filter
    (fun U => Finset.univ.image U = S) with hfiberS
  -- term S (the dite is true)
  have hterm : (if hS' : S.card = d then
      (∏ i ∈ S, w i) * (Matrix.of (fun a b : Fin d =>
        s (((S.orderIsoOfFin hS' b : ↥S) : Fin n)) a)).det ^ 2
    else 0)
      = (∏ i ∈ S, w i) * (Matrix.of (fun a b : Fin d =>
        s (((S.orderIsoOfFin hS b : ↥S) : Fin n)) a)).det ^ 2 := by
    rw [dif_pos hS]
  -- All U in fiber have f_sum U = term S
  have h_all_eq : ∀ U ∈ fiberS, f_sum U =
      (∏ i ∈ S, w i) * (Matrix.of (fun a b : Fin d =>
        s (((S.orderIsoOfFin hS b : ↥S) : Fin n)) a)).det ^ 2 := by
    intro U hU
    rw [hfiberS, Finset.mem_filter] at hU
    obtain ⟨hU_inj_mem, hU_img⟩ := hU
    rw [Finset.mem_filter] at hU_inj_mem
    obtain ⟨_, hU_inj⟩ := hU_inj_mem
    -- f_sum U = (∏ j, w (U j)) * det(M_U)^2
    simp only [hf_sum]
    -- ∏ j, w (U j) = ∏ i ∈ S, w i
    have h_prod : (∏ j, w (U j)) = ∏ i ∈ S, w i := by
      rw [← hU_img]
      rw [Finset.prod_image]
      intro j _ j' _ h_eq
      exact hU_inj h_eq
    -- det(M_U)^2 = det(M_{e_S})^2 via permutation
    have h_det : (Matrix.of (fun a b : Fin d => s (U b) a)).det ^ 2
        = (Matrix.of (fun a b : Fin d =>
          s (((S.orderIsoOfFin hS b : ↥S) : Fin n)) a)).det ^ 2 := by
      -- Construct the permutation σ
      -- U and e_S are both bijections Fin d → ↥S
      let eS : Fin d → Fin n := fun b => ((S.orderIsoOfFin hS b : ↥S) : Fin n)
      -- U as an equiv to ↥S
      have hU_mem : ∀ j, (U j) ∈ S := by
        intro j
        rw [← hU_img]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      let euU : Fin d ≃ ↥S := Equiv.ofBijective
        (fun j => (⟨U j, hU_mem j⟩ : ↥S))
        ⟨fun j₁ j₂ h => hU_inj (congrArg Subtype.val h),
         fun x => by
           obtain ⟨i, hi⟩ := x
           have : i ∈ Finset.univ.image U := hU_img ▸ hi
           rw [Finset.mem_image] at this
           obtain ⟨j, _, rfl⟩ := this
           exact ⟨j, rfl⟩⟩
      let euS : Fin d ≃ ↥S := (S.orderIsoOfFin hS).toEquiv
      let σ : Equiv.Perm (Fin d) := euU.trans euS.symm
      have hU_eq : ∀ j, U j = eS (σ j) := by
        intro j
        -- Key: euS (σ j) = euU j
        have h_key : euS (σ j) = euU j := by
          show euS ((euU.trans euS.symm) j) = euU j
          rw [Equiv.trans_apply]
          exact Equiv.apply_symm_apply euS (euU j)
        -- Take Subtype.val of both sides
        have h_val := congrArg Subtype.val h_key
        -- LHS: (euS (σ j) : Fin n) = eS (σ j)
        -- RHS: (euU j : Fin n) = U j
        simp only [euS, eS] at h_val
        -- h_val : ((S.orderIsoOfFin hS (σ j) : ↥S) : Fin n) = U j
        -- But eS (σ j) = ((S.orderIsoOfFin hS (σ j) : ↥S) : Fin n) by definition
        exact h_val.symm
      exact det_sq_perm_invariant s eS σ U hU_eq
    rw [h_prod, h_det]
  -- fiberS.card = d!
  have h_card : fiberS.card = Nat.factorial d := by
    -- fiberS.card = Fintype.card ↥fiberS
    have h1 : fiberS.card = Fintype.card ↥fiberS := (Fintype.card_coe fiberS).symm
    -- ↥fiberS ≃ subtype via ofBijective
    -- Key: f preserves the underlying function definitionally
    have h_equiv : ↥fiberS ≃ {U : Fin d → Fin n //
        Function.Injective U ∧ Finset.univ.image U = S} :=
      Equiv.ofBijective
        (fun x =>
          have h : Function.Injective (x : Fin d → Fin n) ∧
              Finset.univ.image (x : Fin d → Fin n) = S := by
            have h_mem : (x : Fin d → Fin n) ∈
                (Finset.univ.filter (fun U : Fin d → Fin n => Function.Injective U)).filter
                (fun U => Finset.univ.image U = S) := x.2
            rw [Finset.mem_filter, Finset.mem_filter] at h_mem
            exact ⟨h_mem.1.2, h_mem.2⟩
          (⟨(x : Fin d → Fin n), h.1, h.2⟩ :
            {U : Fin d → Fin n // Function.Injective U ∧ Finset.univ.image U = S}))
        ⟨by
          intro x y h
          -- h : f x = f y, where f is the forward function
          -- (f x).val = x.val definitionally
          have h1 : (x : Fin d → Fin n) = (y : Fin d → Fin n) := by
            have := congrArg (Subtype.val : {U : Fin d → Fin n //
              Function.Injective U ∧ Finset.univ.image U = S} → (Fin d → Fin n)) h
            -- this : (f x).val = (f y).val
            -- (f x).val = x.val, (f y).val = y.val by definition of f
            simpa using this
          exact Subtype.ext h1,
        by
          intro y
          obtain ⟨U, hU_inj, hU_img⟩ := y
          refine ⟨⟨U, ?_⟩, ?_⟩
          · show U ∈ (Finset.univ.filter (fun U : Fin d → Fin n => Function.Injective U)).filter
              (fun U => Finset.univ.image U = S)
            rw [Finset.mem_filter, Finset.mem_filter]
            exact ⟨⟨Finset.mem_univ U, hU_inj⟩, hU_img⟩
          · apply Subtype.ext
            rfl⟩
    have h2 : Fintype.card ↥fiberS
        = Fintype.card {U : Fin d → Fin n //
          Function.Injective U ∧ Finset.univ.image U = S} :=
      Fintype.card_congr h_equiv
    have h3 : Fintype.card {U : Fin d → Fin n //
          Function.Injective U ∧ Finset.univ.image U = S}
        = Fintype.card (Fin d ≃ ↥S) := Fintype.card_congr (fiberEquiv S)
    rw [h1, h2, h3]
    exact card_equiv_fin S hS
  -- Combine: ∑ U ∈ fiberS, f_sum U = d! * term S
  rw [hterm]
  rw [Finset.sum_congr rfl h_all_eq]
  rw [Finset.sum_const, h_card, nsmul_eq_mul]

-- Main theorem
theorem ordered_cauchy_binet {n d : ℕ} (hdn : d ≤ n) (hd : 0 < d)
    (s : Fin n → (Fin d → ℝ)) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ U : Fin d → Fin n, (∏ j, w (U j)) *
        (Matrix.det (Matrix.of (fun a b : Fin d => s (U b) a))) ^ 2
      = (Nat.factorial d : ℝ) *
        Matrix.det
          (Matrix.of (fun a b : Fin d => ∑ i, w i * s i a * s i b)) := by
  -- Step 1: LHS = d! * ∑ S, term S (by step4)
  have h_step4 := step4 s w
  -- Step 2: det(gram) = ∑ S, term S
  have h_gram : Matrix.det (Matrix.of (fun a b : Fin d => ∑ i, w i * s i a * s i b))
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        (if hS : S.card = d then
          (∏ i ∈ S, w i) * (Matrix.of (fun a b : Fin d =>
            s (((S.orderIsoOfFin hS b : ↥S) : Fin n)) a)).det ^ 2
        else 0) := by
    -- gram = Smatᵀ * W * Smat
    rw [gram_eq]
    -- = (Smatᵀ * SqW) * (SqW * Smat)
    rw [← AB_eq s w hw]
    -- Apply Cauchy-Binet
    rw [ClassicalGaps.cauchy_binet_det hdn
      ((Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))ᵀ *
        Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)))
      (Matrix.diagonal (fun i : Fin n => Real.sqrt (w i)) *
        Matrix.of (fun (i : Fin n) (a : Fin d) => s i a))]
    -- Each term: det(A_S) * det(B_S) = (∏ sqrt^2) * det(M_e)^2 = (∏ w) * det(M_e)^2
    apply Finset.sum_congr rfl
    intro S hS_mem
    by_cases hS : S.card = d
    · rw [dif_pos hS]
      -- A_S = (Smatᵀ * SqW).submatrix id e, B_S = (SqW * Smat).submatrix e id
      -- where e = fun i => ((orderIsoOfFin hS i : ↥S) : Fin n)
      have h_sub := sub_det_eq s w hw (fun i : Fin d => ((S.orderIsoOfFin hS i : ↥S) : Fin n))
      -- h_sub : det(A_S) * det(B_S) = (∏ sqrt^2) * det(M_e)^2
      have h_prod := prod_sqrt_eq w hw S hS
      -- h_prod : (∏ sqrt^2) = ∏ i ∈ S, w i
      rw [dif_pos hS] at *
      -- Need to match the submatrix expressions
      -- The ClassicalGaps.cauchy_binet_det gives det with e = fun i => ((orderIsoOfFin hS i : ↥S) : Fin n)
      -- which matches h_sub
      rw [h_sub, h_prod]
    · rw [dif_neg hS, dif_neg hS]
  -- Combine
  rw [h_step4, h_gram]

end FilteredDescent
