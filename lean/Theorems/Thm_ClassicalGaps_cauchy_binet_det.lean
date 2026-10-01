import Mathlib

open Finset Matrix

namespace ClassicalGaps

/-- Cauchy–Binet formula, proved locally (Leibniz expansion + fiber over m-subsets).

    For `A : Matrix (Fin m) (Fin n) ℝ` and `B : Matrix (Fin n) (Fin m) ℝ`,
    `det (A * B)` equals the sum over all `m`-element subsets `S` of `Fin n`
    of `det A_S * det B_S`, where `A_S`, `B_S` are the submatrices on the
    columns / rows indexed by `S` (in increasing order). -/
theorem cauchy_binet_det {m n : ℕ} (_hmn : m ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if hS : S.card = m then
        (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
        (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
      else 0 := by
  classical
  -- Step 1: Leibniz expansion of det (A * B), regrouped by the column-choice function.
  have expand : (A * B).det
      = ∑ f : Fin m → Fin n, (A.submatrix id f).det * (∏ i, B (f i) i) := by
    have step1 : ∀ σ : Equiv.Perm (Fin m),
        (∏ i, (A * B) (σ i) i)
          = ∑ f : Fin m → Fin n, (∏ i, A (σ i) (f i)) * (∏ i, B (f i) i) := by
      intro σ
      have h1 : ∀ i : Fin m, (A * B) (σ i) i
          = ∑ k : Fin n, A (σ i) k * B k i :=
        fun i => Matrix.mul_apply
      simp_rw [h1, Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.prod_mul_distrib]
    calc (A * B).det
        = ∑ σ : Equiv.Perm (Fin m),
            ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, (A * B) (σ i) i) :=
          Matrix.det_apply' _
      _ = ∑ σ : Equiv.Perm (Fin m), ∑ f : Fin m → Fin n,
            ((Equiv.Perm.sign σ : ℤ) : ℝ)
              * ((∏ i, A (σ i) (f i)) * (∏ i, B (f i) i)) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [step1 σ, Finset.mul_sum]
      _ = ∑ f : Fin m → Fin n, ∑ σ : Equiv.Perm (Fin m),
            ((Equiv.Perm.sign σ : ℤ) : ℝ)
              * ((∏ i, A (σ i) (f i)) * (∏ i, B (f i) i)) :=
          Finset.sum_comm
      _ = ∑ f : Fin m → Fin n,
            (∑ σ : Equiv.Perm (Fin m),
              ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, A (σ i) (f i)))
              * (∏ i, B (f i) i) := by
          apply Finset.sum_congr rfl
          intro f _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro σ _
          rw [mul_assoc]
      _ = ∑ f : Fin m → Fin n, (A.submatrix id f).det * (∏ i, B (f i) i) := by
          apply Finset.sum_congr rfl
          intro f _
          congr 1
          rw [Matrix.det_apply']
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
  -- Step 2: the summand vanishes when `f` is not injective
  -- (two equal columns in `A.submatrix id f`).
  have vanish : ∀ f : Fin m → Fin n, ¬ Function.Injective f →
      (A.submatrix id f).det = 0 := by
    intro f hf
    rw [Function.not_injective_iff] at hf
    obtain ⟨a, b, hab_eq, hab_ne⟩ := hf
    have hrow : ((A.submatrix id f)ᵀ) a = ((A.submatrix id f)ᵀ) b := by
      funext j
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
      rw [hab_eq]
    have h0 := Matrix.det_zero_of_row_eq hab_ne hrow
    rwa [Matrix.det_transpose] at h0
  -- Step 3: for a fixed m-subset S, the fiber sum equals det A_S * det B_S.
  have fiber : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ f ∈ Finset.univ.filter
        (fun f : Fin m → Fin n => Finset.image f Finset.univ = S),
        (A.submatrix id f).det * (∏ i, B (f i) i)
      = if hS : S.card = m then
          (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
          (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
        else 0 := by
    intro S hS_mem
    have hScard : S.card = m := (Finset.mem_powersetCard.mp hS_mem).2
    rw [dif_pos hScard]
    -- `e` is the increasing enumeration of `S`, exactly as in the statement.
    set e : Fin m → Fin n :=
      fun (i : Fin m) => (S.orderIsoOfFin hScard i : Fin n) with he
    have e_inj : Function.Injective e := by
      intro i j hij
      have hij' : (S.orderIsoOfFin hScard i : Fin n)
          = (S.orderIsoOfFin hScard j : Fin n) := by
        simpa [he] using hij
      have h2 : (S.orderIsoOfFin hScard) i = (S.orderIsoOfFin hScard) j :=
        Subtype.val_injective hij'
      exact (S.orderIsoOfFin hScard).injective h2
    have e_mem : ∀ i, e i ∈ S := fun i => by
      rw [he]
      simp only
      exact (S.orderIsoOfFin hScard i).property
    -- `image e univ = S`
    have image_e : Finset.image e Finset.univ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact e_mem i
      · rw [Finset.card_image_of_injective _ e_inj, Finset.card_univ, Fintype.card_fin,
          hScard]
    -- the fiber sum, reindexed by permutations
    have fiber_sum : (A.submatrix id e).det * (B.submatrix e id).det
        = ∑ π : Equiv.Perm (Fin m),
            (A.submatrix id (e ∘ ⇑π)).det * (∏ i, B ((e ∘ ⇑π) i) i) := by
      have hperm : ∀ π : Equiv.Perm (Fin m),
          (A.submatrix id (e ∘ ⇑π)).det
            = ((Equiv.Perm.sign π : ℤ) : ℝ) * (A.submatrix id e).det := by
        intro π
        have hsub : A.submatrix id (e ∘ ⇑π)
            = (A.submatrix id e).submatrix id ⇑π := by
          rw [Matrix.submatrix_submatrix]
          rfl
        rw [hsub, Matrix.det_permute']
      have hexpand : (B.submatrix e id).det
          = ∑ π : Equiv.Perm (Fin m),
              ((Equiv.Perm.sign π : ℤ) : ℝ) * (∏ i, B (e (π i)) i) := by
        rw [Matrix.det_apply']
        apply Finset.sum_congr rfl
        intro π _
        congr 1
      calc (A.submatrix id e).det * (B.submatrix e id).det
          = (A.submatrix id e).det *
              (∑ π : Equiv.Perm (Fin m),
                ((Equiv.Perm.sign π : ℤ) : ℝ) * (∏ i, B (e (π i)) i)) := by
              rw [hexpand]
        _ = ∑ π : Equiv.Perm (Fin m),
              (A.submatrix id e).det *
                (((Equiv.Perm.sign π : ℤ) : ℝ) * (∏ i, B (e (π i)) i)) := by
              rw [Finset.mul_sum]
        _ = ∑ π : Equiv.Perm (Fin m),
              (A.submatrix id (e ∘ ⇑π)).det * (∏ i, B ((e ∘ ⇑π) i) i) := by
              apply Finset.sum_congr rfl
              intro π _
              rw [hperm π]
              simp only [Function.comp_apply]
              ring
    rw [fiber_sum]
    refine Eq.symm (Finset.sum_bij
      (fun (π : Equiv.Perm (Fin m)) _ => e ∘ ⇑π) ?_ ?_ ?_ ?_)
    · -- maps into the fiber
      intro π _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.image_comp, Finset.image_univ_equiv, image_e]
    · -- injective
      intro π₁ _ π₂ _ h
      have h' : ⇑π₁ = ⇑π₂ := by
        funext i
        exact e_inj (congrFun h i)
      exact Equiv.Perm.ext (fun x => congrFun h' x)
    · -- surjective onto the fiber
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      -- `f` lands in `S`
      have hf_mem : ∀ i, f i ∈ S := fun i => by
        rw [← hf]
        exact Finset.mem_image_of_mem f (Finset.mem_univ i)
      -- `g : Fin m → ↥S` is bijective
      set g : Fin m → ↥S := fun i => ⟨f i, hf_mem i⟩ with hg
      have g_surj : Function.Surjective g := by
        intro y
        have hy : y.1 ∈ Finset.image f Finset.univ := by rw [hf]; exact y.2
        rw [Finset.mem_image] at hy
        obtain ⟨i, _, hi⟩ := hy
        exact ⟨i, Subtype.ext hi⟩
      have g_inj : Function.Injective g := by
        by_contra hni
        have hlt := Fintype.card_lt_of_surjective_not_injective g g_surj hni
        rw [Fintype.card_coe, hScard, Fintype.card_fin] at hlt
        exact lt_irrefl _ hlt
      let π : Equiv.Perm (Fin m) :=
        (Equiv.ofBijective g ⟨g_inj, g_surj⟩).trans (S.orderIsoOfFin hScard).symm
      refine ⟨π, Finset.mem_univ π, ?_⟩
      -- `e ∘ π = f`
      funext i
      show e (π i) = f i
      have hπ : π i = (S.orderIsoOfFin hScard).symm (g i) := rfl
      rw [hπ]
      show e ((S.orderIsoOfFin hScard).symm (g i)) = f i
      rw [he]
      simp only
      rw [OrderIso.apply_symm_apply]
    · intro π _
      rfl
  -- Step 4: assemble.  First restrict to `f` with `card (image f univ) = m`.
  have sum_filter :
      ∑ f : Fin m → Fin n, (A.submatrix id f).det * (∏ i, B (f i) i)
      = ∑ f ∈ Finset.univ.filter
          (fun f : Fin m → Fin n => (Finset.image f Finset.univ).card = m),
          (A.submatrix id f).det * (∏ i, B (f i) i) := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    -- `hf : ¬ (image f univ).card = m`, so `f` is not injective
    have hni : ¬ Function.Injective f := by
      intro hinj
      exact hf (by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin])
    rw [vanish f hni, zero_mul]
  have fiberwise :
      ∑ f ∈ Finset.univ.filter
          (fun f : Fin m → Fin n => (Finset.image f Finset.univ).card = m),
          (A.submatrix id f).det * (∏ i, B (f i) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ∑ f ∈ Finset.univ.filter
            (fun f : Fin m → Fin n => Finset.image f Finset.univ = S),
            (A.submatrix id f).det * (∏ i, B (f i) i) := by
    -- s is the filtered univ; t is the powersetCard.
    set s : Finset (Fin m → Fin n) :=
      Finset.univ.filter (fun f : Fin m → Fin n => (Finset.image f Finset.univ).card = m)
      with hs
    set t : Finset (Finset (Fin n)) :=
      (Finset.univ : Finset (Fin n)).powersetCard m with ht
    -- For S ∈ t, the two filters coincide (image = S implies card = m).
    have hfilter_eq : ∀ S ∈ t,
        s.filter (fun f : Fin m → Fin n => Finset.image f Finset.univ = S)
        = Finset.univ.filter (fun f : Fin m → Fin n => Finset.image f Finset.univ = S) := by
      intro S hS
      have hScard : S.card = m := (Finset.mem_powersetCard.mp hS).2
      ext f
      simp only [Finset.mem_filter, hs, Finset.mem_univ, true_and]
      constructor
      · intro ⟨_, himg⟩
        exact himg
      · intro himg
        exact ⟨by rw [himg, hScard], himg⟩
    have hmaps : ∀ f ∈ s, Finset.image f Finset.univ ∈ t := by
      intro f hf
      rw [hs, Finset.mem_filter] at hf
      rw [ht, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hf.2⟩
    have h := Finset.sum_fiberwise_of_maps_to (s := s) (t := t)
      (g := fun f : Fin m → Fin n => Finset.image f Finset.univ)
      (f := fun f : Fin m → Fin n => (A.submatrix id f).det * ∏ i, B (f i) i)
      hmaps
    -- h : ∑ S ∈ t, ∑ f ∈ s.filter (image=S), ... = ∑ f ∈ s, ...
    rw [hs, ht]
    calc ∑ f ∈ s, (A.submatrix id f).det * ∏ i, B (f i) i
        = ∑ S ∈ t, ∑ f ∈ s.filter
            (fun f : Fin m → Fin n => Finset.image f Finset.univ = S),
            (A.submatrix id f).det * ∏ i, B (f i) i := h.symm
      _ = ∑ S ∈ t, ∑ f ∈ Finset.univ.filter
            (fun f : Fin m → Fin n => Finset.image f Finset.univ = S),
            (A.submatrix id f).det * ∏ i, B (f i) i := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [hfilter_eq S hS]
  rw [expand, sum_filter, fiberwise]
  apply Finset.sum_congr rfl
  intro S hS
  exact fiber S hS

end ClassicalGaps
