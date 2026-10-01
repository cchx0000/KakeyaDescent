import Theorems.Thm_FilteredDescent_FaithfulGate_Defs
import Theorems.Thm_FilteredDescent_FaithfulGate_LCA
import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Faithful root-cross gate — exact duplicate/geometric identities (paper §10, (143)–(147))

For a fixed terminal carrier (the `termTube` of §10), the root-cross
pair-sums split exactly over the root's children:

* (146): `X^dup = Σ_T (D_T² − Σ_b D_{b,T}²)`
* (147): `X^geom = Σ_{T≠T'} (D_T D_{T'} − Σ_b D_{b,T} D_{b,T'})`

where `D_T = termLoad` and `D_{b,T} = childTermLoad` (see
`Thm_FilteredDescent_FaithfulGate_Defs`).  We also prove the upper bounds
consumed by the gate: `X^dup ≤ Σ_T D_T²` and
`X^geom ≤ Σ_{T≠T'} D_T D_{T'}`.

The proof works at the integrated pair-sum level of (145)–(147): the
paper's pointwise identities (137)–(144) imply these after summation
against the leaf load; the pointwise layer is not formalized here.

The degenerate case (`[]` itself a leaf, so the tree is the single node
`{[]}`) is handled separately; its `n = 0` subcase is contradictory
since `termTube [] : Fin 0` cannot exist.
-/

namespace FilteredDescent

variable {α : Type} [DecidableEq α] {n : ℕ}

/-! ## Fiber identification -/

/-- Leaves with `take 1 = b` and `termTube = t` are exactly the leaves
below root child `b` with `termTube = t`. -/
private theorem fiber_eq_childTermLoad
    (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ) (δ : ℝ)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    {b : List α} (hb : b ∈ treeChildren T []) (t : Fin n) :
    ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t ∧ γ.take 1 = b), load γ δ
      = childTermLoad T termTube load b t δ := by
  unfold childTermLoad
  refine Finset.sum_congr ?_ (fun γ _ => rfl)
  ext γ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hγ, hTt, htake⟩
    have hpre : γ.take 1 <+: γ :=
      (leaf_take1_mem_children hprefix hγ (hnonroot γ hγ)).2
    exact ⟨hγ, htake ▸ hpre, hTt⟩
  · rintro ⟨hγ, hble, hTt⟩
    exact ⟨hγ, hTt, take1_eq_of_child_mem hb hble⟩

/-! ## Load splitting -/

/-- `D_T = Σ_b D_{b,T}` when no leaf is the root: fiber the leaf sum
over the first step `γ.take 1`. -/
theorem termLoad_eq_sum_childTermLoad
    (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    (t : Fin n) (δ : ℝ) :
    termLoad T termTube load t δ
      = ∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ := by
  unfold termLoad
  have hmaps : ∀ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
      (fun γ => γ.take 1) γ ∈ treeChildren T [] := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact (leaf_take1_mem_children hprefix hγ.1 (hnonroot γ hγ.1)).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun γ => load γ δ)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.filter_filter]
  exact fiber_eq_childTermLoad T hprefix termTube load δ hnonroot hb t

/-! ## Off-diagonal pair algebra -/

/-- Abstract form of the (146)/(147) algebra: summing `[b≠b']·D_{b,t}·D_{b',t'}`
over all child pairs equals the full product minus the diagonal. -/
private theorem pair_offdiag_eq (ch : Finset (List α)) (D : List α → Fin n → ℝ)
    (t t' : Fin n) :
    (∑ b ∈ ch, ∑ b' ∈ ch, (if b ≠ b' then D b t * D b' t' else 0))
    = (∑ b ∈ ch, D b t) * (∑ b' ∈ ch, D b' t') - ∑ b ∈ ch, D b t * D b t' := by
  have hsub : ∀ b ∈ ch, ∀ b' ∈ ch,
      (if b ≠ b' then D b t * D b' t' else 0)
      = D b t * D b' t' - (if b = b' then D b t * D b' t' else 0) := by
    intro b _ b' _
    by_cases hne : b ≠ b'
    · have hne2 : ¬ (b = b') := fun heq => hne heq
      rw [if_pos hne, if_neg hne2, sub_zero]
    · have heq : b = b' := not_ne_iff.mp hne
      rw [if_neg hne, if_pos heq, sub_self]
  have hdiag : ∀ b ∈ ch,
      (∑ b' ∈ ch, (if b = b' then D b t * D b' t' else 0)) = D b t * D b t' := by
    intro b hb
    have h := Finset.sum_ite_eq ch b (fun b' => D b t * D b' t')
    rw [h, if_pos hb]
  calc (∑ b ∈ ch, ∑ b' ∈ ch, (if b ≠ b' then D b t * D b' t' else 0))
      = ∑ b ∈ ch, ∑ b' ∈ ch,
          (D b t * D b' t' - (if b = b' then D b t * D b' t' else 0)) :=
        Finset.sum_congr rfl fun b hb =>
          Finset.sum_congr rfl fun b' hb' => hsub b hb b' hb'
    _ = ∑ b ∈ ch, ((∑ b' ∈ ch, D b t * D b' t')
          - (∑ b' ∈ ch, (if b = b' then D b t * D b' t' else 0))) :=
        Finset.sum_congr rfl fun b hb =>
          Finset.sum_sub_distrib (fun b' => D b t * D b' t')
            (fun b' => if b = b' then D b t * D b' t' else 0)
    _ = ∑ b ∈ ch, ((∑ b' ∈ ch, D b t * D b' t') - D b t * D b t') :=
        Finset.sum_congr rfl fun b hb => by rw [hdiag b hb]
    _ = (∑ b ∈ ch, ∑ b' ∈ ch, D b t * D b' t') - ∑ b ∈ ch, D b t * D b t' :=
        Finset.sum_sub_distrib (fun b => ∑ b' ∈ ch, D b t * D b' t')
          (fun b => D b t * D b t')
    _ = (∑ b ∈ ch, D b t) * (∑ b' ∈ ch, D b' t') - ∑ b ∈ ch, D b t * D b t' := by
        rw [← Finset.sum_mul_sum]

/-! ## The pair-sum over child pairs -/

/-- For fixed carriers `t, t'`, the off-diagonal leaf pair-sum fibers
exactly over root-child pairs. -/
private theorem pair_fiber_eq
    (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    (δ : ℝ) (t t' : Fin n) :
    (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
      ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
      (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))
    = ∑ b ∈ treeChildren T [], ∑ b' ∈ treeChildren T [],
      (if b ≠ b' then childTermLoad T termTube load b t δ
        * childTermLoad T termTube load b' t' δ else 0) := by
  have hmaps1 : ∀ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
      (fun γ => γ.take 1) γ ∈ treeChildren T [] := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact (leaf_take1_mem_children hprefix hγ.1 (hnonroot γ hγ.1)).1
  have hFb : ∀ b ∈ treeChildren T [],
      ∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
        (fun γ => γ.take 1 = b), load γ δ
        = childTermLoad T termTube load b t δ := by
    intro b hb
    rw [Finset.filter_filter]
    exact fiber_eq_childTermLoad T hprefix termTube load δ hnonroot hb t
  have hinner : ∀ b ∈ treeChildren T [],
      (∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
        (fun γ => γ.take 1 = b),
        ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
        (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))
      = ∑ b' ∈ treeChildren T [],
        (if b ≠ b' then childTermLoad T termTube load b t δ
          * childTermLoad T termTube load b' t' δ else 0) := by
    intro b hb
    have hγinner : ∀ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
        (fun γ => γ.take 1 = b),
        (∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
          (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))
        = ∑ b' ∈ treeChildren T [],
          (if b ≠ b' then load γ δ * childTermLoad T termTube load b' t' δ else 0) := by
      intro γ hγ
      have htake : γ.take 1 = b := (Finset.mem_filter.mp hγ).2
      have hmaps2 : ∀ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
          (fun γ' => γ'.take 1) γ' ∈ treeChildren T [] := by
        intro γ' hγ'
        rw [Finset.mem_filter] at hγ'
        exact (leaf_take1_mem_children hprefix hγ'.1 (hnonroot γ' hγ'.1)).1
      have hfib : (∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
            (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))
          = ∑ b' ∈ treeChildren T [],
            ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t' ∧ γ'.take 1 = b'),
            (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0) := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps2 (fun γ' =>
          (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))]
        refine Finset.sum_congr rfl fun b' hb' => ?_
        rw [Finset.filter_filter]
      rw [hfib]
      refine Finset.sum_congr rfl fun b' hb' => ?_
      have hD : ∑ γ' ∈ (treeLeaves T).filter
          (fun γ' => termTube γ' = t' ∧ γ'.take 1 = b'), load γ' δ
          = childTermLoad T termTube load b' t' δ :=
        fiber_eq_childTermLoad T hprefix termTube load δ hnonroot hb' t'
      have hiff : ∀ γ' ∈ (treeLeaves T).filter
          (fun γ' => termTube γ' = t' ∧ γ'.take 1 = b'),
          ((γ.take 1 ≠ γ'.take 1) ↔ (b ≠ b')) := by
        intro γ' hγ'
        have htake' : γ'.take 1 = b' := (Finset.mem_filter.mp hγ').2.2
        rw [htake, htake']
      by_cases hne : b ≠ b'
      · simp only [if_pos hne]
        have hterm : ∀ γ' ∈ (treeLeaves T).filter
            (fun γ' => termTube γ' = t' ∧ γ'.take 1 = b'),
            (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0)
            = load γ δ * load γ' δ :=
          fun γ' hγ' => if_pos ((hiff γ' hγ').mpr hne)
        rw [Finset.sum_congr rfl (fun γ' hγ' => hterm γ' hγ'),
          ← Finset.mul_sum, hD]
      · simp only [if_neg hne]
        have hzero : ∀ γ' ∈ (treeLeaves T).filter
            (fun γ' => termTube γ' = t' ∧ γ'.take 1 = b'),
            (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0) = 0 :=
          fun γ' hγ' => if_neg (mt (hiff γ' hγ').mp hne)
        rw [Finset.sum_congr rfl (fun γ' hγ' => hzero γ' hγ')]
        simp
    calc ∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
          (fun γ => γ.take 1 = b),
          ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
          (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0)
        = ∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
          (fun γ => γ.take 1 = b),
          ∑ b' ∈ treeChildren T [],
          (if b ≠ b' then load γ δ * childTermLoad T termTube load b' t' δ else 0) :=
          Finset.sum_congr rfl fun γ hγ => hγinner γ hγ
      _ = ∑ b' ∈ treeChildren T [],
          ∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
          (fun γ => γ.take 1 = b),
          (if b ≠ b' then load γ δ * childTermLoad T termTube load b' t' δ else 0) :=
          Finset.sum_comm
      _ = ∑ b' ∈ treeChildren T [],
          (if b ≠ b' then childTermLoad T termTube load b t δ
            * childTermLoad T termTube load b' t' δ else 0) := by
          refine Finset.sum_congr rfl fun b' hb' => ?_
          by_cases hne : b ≠ b'
          · simp only [if_pos hne]
            rw [← Finset.sum_mul, hFb b hb]
          · simp only [if_neg hne]
            simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps1 (fun γ =>
    ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
    (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))]
  refine Finset.sum_congr rfl fun b hb => ?_
  exact hinner b hb

/-! ## The exact duplicate identity (146) -/

/-- Paper (146): `X^dup = Σ_T (D_T² − Σ_b D_{b,T}²)`. -/
theorem xdup_eq
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (δ : ℝ) :
    Xdup T (fun γ => load γ δ) termTube
      = ∑ t : Fin n, ((termLoad T termTube load t δ)^2
          - ∑ b ∈ treeChildren T [], (childTermLoad T termTube load b t δ)^2) := by
  by_cases hcase : [] ∈ treeLeaves T
  · -- Degenerate case: the tree is the single node `{[]}`.
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact Fin.elim0 (termTube [])
    · have hTeq : T = {[]} := by
        ext l
        simp only [Finset.mem_singleton]
        constructor
        · intro hl
          exact (Finset.mem_filter.mp hcase).2 l hl ⟨l, rfl⟩
        · intro hl
          rw [hl]; exact hroot
      have hleaves : treeLeaves T = {[]} := by
        rw [hTeq]
        ext γ
        constructor
        · intro hγ
          rw [treeLeaves, Finset.mem_filter] at hγ
          exact hγ.1
        · intro hγ
          rw [treeLeaves, Finset.mem_filter, Finset.mem_singleton.mp hγ]
          refine ⟨Finset.mem_singleton_self [], fun l' hl' _ => ?_⟩
          rw [Finset.mem_singleton.mp hl']
      have hLCA : treeLCA ([] : List α) [] = [] := by
        unfold treeLCA
        simp
      have hXdup : Xdup T (fun γ => load γ δ) termTube = (load [] δ)^2 := by
        unfold Xdup
        rw [hleaves, Finset.sum_singleton, Finset.sum_singleton,
          if_pos ⟨hLCA, rfl⟩, pow_two]
      have hch : treeChildren T [] = ∅ := by
        rw [hTeq]
        apply Finset.eq_empty_of_forall_notMem
        intro b hb
        unfold treeChildren at hb
        rw [Finset.mem_filter, Finset.mem_singleton] at hb
        obtain ⟨rfl, -, hlen⟩ := hb
        simp at hlen
      have hD : ∀ t : Fin n, termLoad T termTube load t δ
          = if termTube [] = t then load [] δ else 0 := by
        intro t
        unfold termLoad
        rw [hleaves]
        by_cases ht : termTube [] = t
        · rw [if_pos ht]
          have hfilter : (({[]} : Finset (List α)).filter
              (fun γ => termTube γ = t)) = {[]} := by
            ext γ
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hγ, -⟩
              exact hγ
            · intro hγ
              subst hγ
              exact ⟨rfl, ht⟩
          rw [hfilter, Finset.sum_singleton]
        · rw [if_neg ht]
          have hfilter : (({[]} : Finset (List α)).filter
              (fun γ => termTube γ = t)) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro γ hγ
            rw [Finset.mem_filter] at hγ
            obtain ⟨hγeq, hγt⟩ := hγ
            rw [Finset.mem_singleton.mp hγeq] at hγt
            exact ht hγt
          rw [hfilter, Finset.sum_empty]
      rw [hXdup, hch]
      simp only [Finset.sum_empty, sub_zero]
      have hsq : ∀ t : Fin n, (termLoad T termTube load t δ)^2
          = if termTube [] = t then (load [] δ)^2 else 0 := by
        intro t
        rw [hD t]
        by_cases ht : termTube [] = t <;> simp [ht]
      simp only [hsq]
      rw [Finset.sum_ite_eq]
      simp
  · -- Main case: no leaf is the root.
    have hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [] := fun γ hγ heq => hcase (heq ▸ hγ)
    -- (i) The LCA condition becomes a take-1 inequality (paper (144)).
    have hcond : ∀ γ ∈ treeLeaves T, ∀ γ' ∈ treeLeaves T,
        (if treeLCA γ γ' = [] ∧ termTube γ = termTube γ' then load γ δ * load γ' δ else 0)
        = (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ = termTube γ' then load γ δ * load γ' δ else 0) := by
      intro γ hγ γ' hγ'
      by_cases hL : treeLCA γ γ' = []
      · have hne := (treeLCA_eq_root_iff (hnonroot γ hγ)).mp hL
        by_cases hT : termTube γ = termTube γ'
        · rw [if_pos ⟨hL, hT⟩, if_pos ⟨hne, hT⟩]
        · rw [if_neg (fun h => hT h.2), if_neg (fun h => hT h.2)]
      · have hne := mt (treeLCA_eq_root_iff (hnonroot γ hγ)).mpr hL
        rw [if_neg (fun h => hL h.1), if_neg (fun h => hne h.1)]
    -- (ii) Rewrite Xdup and fiber over the terminal carrier.
    have hX1 : Xdup T (fun γ => load γ δ) termTube
        = ∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
          ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t),
          (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0) := by
      have hmaps : ∀ γ ∈ treeLeaves T, termTube γ ∈ (Finset.univ : Finset (Fin n)) := by
        intro γ _
        exact Finset.mem_univ _
      have hbase : Xdup T (fun γ => load γ δ) termTube
          = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ = termTube γ'
              then load γ δ * load γ' δ else 0) := by
        unfold Xdup
        refine Finset.sum_congr rfl fun γ hγ =>
          Finset.sum_congr rfl fun γ' hγ' => hcond γ hγ γ' hγ'
      rw [hbase, ← Finset.sum_fiberwise_of_maps_to hmaps (fun γ =>
        ∑ γ' ∈ treeLeaves T, (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ = termTube γ'
          then load γ δ * load γ' δ else 0))]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun γ hγ => ?_
      rw [Finset.mem_filter] at hγ
      have hTt : termTube γ = t := hγ.2
      have hsum : ∀ γ' : List α,
          (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ = termTube γ' then load γ δ * load γ' δ else 0)
          = (if termTube γ' = t then (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0)
            else 0) := by
        intro γ'
        by_cases hC : termTube γ' = t
        · have hB : termTube γ = termTube γ' := hTt.trans hC.symm
          rw [if_pos hC]
          by_cases hA : γ.take 1 ≠ γ'.take 1
          · rw [if_pos hA, if_pos ⟨hA, hB⟩]
          · rw [if_neg hA, if_neg (fun h => hA h.1)]
        · have hB : ¬ (termTube γ = termTube γ') := fun hcon => hC (hcon.symm.trans hTt)
          rw [if_neg hC, if_neg (fun h => hB h.2)]
      calc ∑ γ' ∈ treeLeaves T,
            (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ = termTube γ' then load γ δ * load γ' δ else 0)
          = ∑ γ' ∈ treeLeaves T,
            (if termTube γ' = t then (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0)
              else 0) :=
            Finset.sum_congr rfl fun γ' _ => hsum γ'
        _ = ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t),
            (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0) := by
            rw [← Finset.sum_filter]
    -- (iii) Per-carrier algebra via the child-pair fiber.
    have halg : ∀ t : Fin n,
        (∑ b ∈ treeChildren T [], ∑ b' ∈ treeChildren T [],
          (if b ≠ b' then childTermLoad T termTube load b t δ
            * childTermLoad T termTube load b' t δ else 0))
        = (termLoad T termTube load t δ)^2
          - ∑ b ∈ treeChildren T [], (childTermLoad T termTube load b t δ)^2 := by
      intro t
      have e1 : (∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ)
          * (∑ b' ∈ treeChildren T [], childTermLoad T termTube load b' t δ)
          = (termLoad T termTube load t δ)^2 := by
        rw [← termLoad_eq_sum_childTermLoad T hprefix termTube load hnonroot t δ]
        rw [pow_two]
      have e2 : (∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ
          * childTermLoad T termTube load b t δ)
          = ∑ b ∈ treeChildren T [], (childTermLoad T termTube load b t δ)^2 :=
        Finset.sum_congr rfl fun b _ => (pow_two _).symm
      have hpo : (∑ b ∈ treeChildren T [], ∑ b' ∈ treeChildren T [],
              (if b ≠ b' then childTermLoad T termTube load b t δ
                * childTermLoad T termTube load b' t δ else 0))
          = (∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ)
            * (∑ b' ∈ treeChildren T [], childTermLoad T termTube load b' t δ)
            - ∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ
              * childTermLoad T termTube load b t δ :=
        pair_offdiag_eq (treeChildren T [])
          (fun b s => childTermLoad T termTube load b s δ) t t
      rw [hpo, e1, e2]
    rw [hX1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pair_fiber_eq T hprefix termTube load hnonroot δ t t, halg t]

/-! ## The exact geometric identity (147) -/

/-- Paper (147): `X^geom = Σ_{T≠T'} (D_T D_{T'} − Σ_b D_{b,T} D_{b,T'})`. -/
theorem xgeom_eq
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (δ : ℝ) :
    Xgeom T (fun γ => load γ δ) termTube
      = ∑ t : Fin n, ∑ t' : Fin n,
        (if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
          - ∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ
            * childTermLoad T termTube load b t' δ
        else 0) := by
  by_cases hcase : [] ∈ treeLeaves T
  · -- Degenerate case: the tree is the single node `{[]}`.
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact Fin.elim0 (termTube [])
    · have hTeq : T = {[]} := by
        ext l
        simp only [Finset.mem_singleton]
        constructor
        · intro hl
          exact (Finset.mem_filter.mp hcase).2 l hl ⟨l, rfl⟩
        · intro hl
          rw [hl]; exact hroot
      have hleaves : treeLeaves T = {[]} := by
        rw [hTeq]
        ext γ
        constructor
        · intro hγ
          rw [treeLeaves, Finset.mem_filter] at hγ
          exact hγ.1
        · intro hγ
          rw [treeLeaves, Finset.mem_filter, Finset.mem_singleton.mp hγ]
          refine ⟨Finset.mem_singleton_self [], fun l' hl' _ => ?_⟩
          rw [Finset.mem_singleton.mp hl']
      have hXgeom : Xgeom T (fun γ => load γ δ) termTube = 0 := by
        unfold Xgeom
        rw [hleaves, Finset.sum_singleton, Finset.sum_singleton]
        simp
      have hch : treeChildren T [] = ∅ := by
        rw [hTeq]
        apply Finset.eq_empty_of_forall_notMem
        intro b hb
        unfold treeChildren at hb
        rw [Finset.mem_filter, Finset.mem_singleton] at hb
        obtain ⟨rfl, -, hlen⟩ := hb
        simp at hlen
      have hD : ∀ t : Fin n, termLoad T termTube load t δ
          = if termTube [] = t then load [] δ else 0 := by
        intro t
        unfold termLoad
        rw [hleaves]
        by_cases ht : termTube [] = t
        · rw [if_pos ht]
          have hfilter : (({[]} : Finset (List α)).filter
              (fun γ => termTube γ = t)) = {[]} := by
            ext γ
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hγ, -⟩
              exact hγ
            · intro hγ
              subst hγ
              exact ⟨rfl, ht⟩
          rw [hfilter, Finset.sum_singleton]
        · rw [if_neg ht]
          have hfilter : (({[]} : Finset (List α)).filter
              (fun γ => termTube γ = t)) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro γ hγ
            rw [Finset.mem_filter] at hγ
            obtain ⟨hγeq, hγt⟩ := hγ
            rw [Finset.mem_singleton.mp hγeq] at hγt
            exact ht hγt
          rw [hfilter, Finset.sum_empty]
      rw [hXgeom, hch]
      simp only [Finset.sum_empty, sub_zero]
      simp only [hD]
      rw [eq_comm]
      apply Finset.sum_eq_zero
      intro t _
      apply Finset.sum_eq_zero
      intro t' _
      by_cases hne : t ≠ t'
      · rw [if_pos hne]
        by_cases h1 : termTube [] = t
        · have h2 : ¬ (termTube [] = t') := fun hcon => hne (h1.symm.trans hcon)
          rw [if_pos h1, if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
      · rw [if_neg hne]
  · -- Main case: no leaf is the root.
    have hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [] := fun γ hγ heq => hcase (heq ▸ hγ)
    -- (i) The LCA condition becomes a take-1 inequality (paper (144)).
    have hcond : ∀ γ ∈ treeLeaves T, ∀ γ' ∈ treeLeaves T,
        (if treeLCA γ γ' = [] ∧ termTube γ ≠ termTube γ' then load γ δ * load γ' δ else 0)
        = (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ' then load γ δ * load γ' δ else 0) := by
      intro γ hγ γ' hγ'
      by_cases hL : treeLCA γ γ' = []
      · have hne := (treeLCA_eq_root_iff (hnonroot γ hγ)).mp hL
        by_cases hT : termTube γ ≠ termTube γ'
        · rw [if_pos ⟨hL, hT⟩, if_pos ⟨hne, hT⟩]
        · rw [if_neg (fun h => hT h.2), if_neg (fun h => hT h.2)]
      · have hne := mt (treeLCA_eq_root_iff (hnonroot γ hγ)).mpr hL
        rw [if_neg (fun h => hL h.1), if_neg (fun h => hne h.1)]
    have hmaps : ∀ γ ∈ treeLeaves T, termTube γ ∈ (Finset.univ : Finset (Fin n)) :=
      fun γ _ => Finset.mem_univ _
    have hbase : Xgeom T (fun γ => load γ δ) termTube
        = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
            then load γ δ * load γ' δ else 0) := by
      unfold Xgeom
      refine Finset.sum_congr rfl fun γ hγ =>
        Finset.sum_congr rfl fun γ' hγ' => hcond γ hγ γ' hγ'
    -- (ii) Fiber the double sum over both terminal carriers.
    have hfib2 : (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
            then load γ δ * load γ' δ else 0))
        = ∑ t : Fin n, ∑ t' : Fin n,
          ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
          ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
          (if γ.take 1 ≠ γ'.take 1 ∧ t ≠ t' then load γ δ * load γ' δ else 0) := by
      have hfib_outer : (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
              then load γ δ * load γ' δ else 0))
          = ∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
            ∑ γ' ∈ treeLeaves T,
            (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
              then load γ δ * load γ' δ else 0) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      rw [hfib_outer]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hγfib : ∀ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
          (∑ γ' ∈ treeLeaves T, (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
            then load γ δ * load γ' δ else 0))
          = ∑ t' : Fin n, ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
            (if γ.take 1 ≠ γ'.take 1 ∧ t ≠ t' then load γ δ * load γ' δ else 0) := by
        intro γ hγ
        have hTt : termTube γ = t := (Finset.mem_filter.mp hγ).2
        have hfib_inner : (∑ γ' ∈ treeLeaves T,
              (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
                then load γ δ * load γ' δ else 0))
            = ∑ t' : Fin n, ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
              (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
                then load γ δ * load γ' δ else 0) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
        rw [hfib_inner]
        refine Finset.sum_congr rfl fun t' _ => Finset.sum_congr rfl fun γ' hγ' => ?_
        have hTt' : termTube γ' = t' := (Finset.mem_filter.mp hγ').2
        by_cases hA : γ.take 1 ≠ γ'.take 1
        · by_cases hB : termTube γ ≠ termTube γ'
          · have hB2 : t ≠ t' := fun hcon => hB ((hTt.trans hcon).trans hTt'.symm)
            rw [if_pos ⟨hA, hB⟩, if_pos ⟨hA, hB2⟩]
          · have hB2 : ¬ (t ≠ t') :=
              fun hcon => hB (fun k => hcon ((hTt.symm.trans k).trans hTt'))
            rw [if_neg (fun h => hB h.2), if_neg (fun h => hB2 h.2)]
        · rw [if_neg (fun h => hA h.1), if_neg (fun h => hA h.1)]
      calc ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
            ∑ γ' ∈ treeLeaves T, (if γ.take 1 ≠ γ'.take 1 ∧ termTube γ ≠ termTube γ'
              then load γ δ * load γ' δ else 0)
          = ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
            ∑ t' : Fin n, ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
            (if γ.take 1 ≠ γ'.take 1 ∧ t ≠ t' then load γ δ * load γ' δ else 0) :=
            Finset.sum_congr rfl fun γ hγ => hγfib γ hγ
        _ = ∑ t' : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
            ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
            (if γ.take 1 ≠ γ'.take 1 ∧ t ≠ t' then load γ δ * load γ' δ else 0) :=
            Finset.sum_comm
    -- (iii) Factor the carrier condition out of the inner pair-sum.
    have hfactor : ∀ t t' : Fin n,
        (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
          ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
          (if γ.take 1 ≠ γ'.take 1 ∧ t ≠ t' then load γ δ * load γ' δ else 0))
        = (if t ≠ t' then
            ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
            ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
            (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0)
          else 0) := by
      intro t t'
      by_cases hne : t ≠ t'
      · simp only [if_pos hne]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
        by_cases hA : γ.take 1 ≠ γ'.take 1
        · rw [if_pos hA, if_pos ⟨hA, hne⟩]
        · rw [if_neg hA, if_neg (fun h => hA h.1)]
      · simp only [if_neg hne]
        apply Finset.sum_eq_zero
        intro γ _
        apply Finset.sum_eq_zero
        intro γ' _
        rw [if_neg (fun h : γ.take 1 ≠ γ'.take 1 ∧ t ≠ t' => hne h.2)]
    -- (iv) Per-carrier-pair algebra via the child-pair fiber.
    have halg : ∀ t t' : Fin n,
        (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
          ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t'),
          (if γ.take 1 ≠ γ'.take 1 then load γ δ * load γ' δ else 0))
        = termLoad T termTube load t δ * termLoad T termTube load t' δ
          - ∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ
            * childTermLoad T termTube load b t' δ := by
      intro t t'
      have e1 : (∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ)
          * (∑ b' ∈ treeChildren T [], childTermLoad T termTube load b' t' δ)
          = termLoad T termTube load t δ * termLoad T termTube load t' δ := by
        rw [← termLoad_eq_sum_childTermLoad T hprefix termTube load hnonroot t δ,
          ← termLoad_eq_sum_childTermLoad T hprefix termTube load hnonroot t' δ]
      have hpo : (∑ b ∈ treeChildren T [], ∑ b' ∈ treeChildren T [],
              (if b ≠ b' then childTermLoad T termTube load b t δ
                * childTermLoad T termTube load b' t' δ else 0))
          = (∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ)
            * (∑ b' ∈ treeChildren T [], childTermLoad T termTube load b' t' δ)
            - ∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ
              * childTermLoad T termTube load b t' δ :=
        pair_offdiag_eq (treeChildren T [])
          (fun b s => childTermLoad T termTube load b s δ) t t'
      rw [pair_fiber_eq T hprefix termTube load hnonroot δ t t', hpo, e1]
    rw [hbase, hfib2]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    rw [hfactor t t', halg t t']

/-! ## Upper bounds consumed by the gate -/

/-- Gate bound: `X^dup ≤ Σ_T D_T²`. -/
theorem xdup_le_sum_sq
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (δ : ℝ) :
    Xdup T (fun γ => load γ δ) termTube
      ≤ ∑ t : Fin n, (termLoad T termTube load t δ)^2 := by
  rw [xdup_eq T hroot hprefix termTube load δ]
  refine Finset.sum_le_sum fun t _ => ?_
  have hnn : 0 ≤ ∑ b ∈ treeChildren T [], (childTermLoad T termTube load b t δ)^2 :=
    Finset.sum_nonneg fun b _ => sq_nonneg _
  exact sub_le_self _ hnn

/-- Gate bound: `X^geom ≤ Σ_{T≠T'} D_T D_{T'}` (needs nonnegative load). -/
theorem xgeom_le_offdiag
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Xgeom T (fun γ => load γ δ) termTube
      ≤ ∑ t : Fin n, ∑ t' : Fin n,
        (if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
          else 0) := by
  rw [xgeom_eq T hroot hprefix termTube load δ]
  refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ => ?_
  by_cases hne : t ≠ t'
  · rw [if_pos hne, if_pos hne]
    have hnn : 0 ≤ ∑ b ∈ treeChildren T [],
        childTermLoad T termTube load b t δ * childTermLoad T termTube load b t' δ :=
      Finset.sum_nonneg fun b _ => mul_nonneg
        (childTermLoad_nonneg T termTube load hload b t δ hδ0 hδ1)
        (childTermLoad_nonneg T termTube load hload b t' δ hδ0 hδ1)
    exact sub_le_self _ hnn
  · rw [if_neg hne, if_neg hne]

end FilteredDescent
