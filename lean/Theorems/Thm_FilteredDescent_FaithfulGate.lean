import Theorems.Thm_FilteredDescent_FaithfulGate_Defs
import Theorems.Thm_FilteredDescent_FaithfulGate_LCA
import Theorems.Thm_FilteredDescent_FaithfulGate_Dup
import Theorems.Thm_FilteredDescent_FaithfulGate_Proper
import Definitions.Def_FilteredDescent_Tree
import Definitions.Def_FilteredDescent_Subpower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Faithful root-cross gate — assembly (paper §10, (140)–(153))

Assembles the faithful root-cross gate from its three pieces:

* (144): `X^root = X^geom + X^dup` (root LCA split by terminal tube).
* `H^dup` from the exact identity (146) plus the named terminal-hardening
  input (148).
* `H^geom` from the exact identity (147) plus the named geometric pair input
  ((53)/(177)/(81), chosen at the call site per dimension).
* The full descent step (141)+(142): `N(δ)² ≲ B^pred(δ) · N(δ)`.

## Honesty notes

* We work at the integrated pair-sum level: the paper's pointwise
  identities (137)–(147) in the spatial variable imply ours by integration.
* Only the induction STEP is formalized here.  Three inputs are named, not
  proved, and must be honest about it:
  - `Hpred`: the predecessor invariance (138) — the induction hypothesis;
  - `terminal_hardening`: the terminal-tube estimate (148)/(150)–(153),
    proved by the parallel R5 stream;
  - `geom_pair`: the geometric pair estimate (53)/(177)/(81).
* The well-founded induction on `(|I|, ℓ(χ), n)` (135) is future work;
  this file does not claim it.
-/

namespace FilteredDescent

/-- Paper (144): the root-cross mass splits by terminal tube. -/
theorem Xroot_split {α : Type} [DecidableEq α] (T : Finset (List α))
    (u : List α → ℝ) {n : ℕ} (termTube : List α → Fin n) :
    Xroot T u = Xgeom T u termTube + Xdup T u termTube := by
  unfold Xroot Xgeom Xdup
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ' _ => ?_
  by_cases hlca : treeLCA γ γ' = []
  · by_cases htube : termTube γ = termTube γ'
    · rw [if_pos hlca, if_neg (fun h => h.2 htube), if_pos ⟨hlca, htube⟩, zero_add]
    · rw [if_pos hlca, if_pos ⟨hlca, htube⟩, if_neg (fun h => htube h.2), add_zero]
  · rw [if_neg hlca, if_neg (fun h => hlca h.1), if_neg (fun h => hlca h.1),
      add_zero]

/-- `H^dup`: the duplicate part via the exact identity (146) and the
named terminal-hardening input (148). -/
theorem Hdup_of_terminal_hardening {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (_hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (terminal_hardening : SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad T termTube load t δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ)) :
    SubpowerLE (fun δ => Xdup T (fun γ => load γ δ) termTube)
      (fun δ => Bpred δ * totalLoad T load δ) :=
  SubpowerLE.mono
    (fun δ _ _ => xdup_le_sum_sq T hroot hprefix termTube load δ)
    terminal_hardening

/-- `H^geom`: the geometric part via the exact identity (147) and the
named geometric pair input ((53)/(177)/(81)). -/
theorem Hgeom_of_geom_pair {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (geom_pair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad T load δ)) :
    SubpowerLE (fun δ => Xgeom T (fun γ => load γ δ) termTube)
      (fun δ => Bpred δ * totalLoad T load δ) :=
  SubpowerLE.mono
    (fun δ hδ0 hδ1 => xgeom_le_offdiag T hroot hprefix termTube load hload δ hδ0 hδ1)
    geom_pair

/-- The faithful root-cross gate, paper (142): `X^root ≲ B^pred · N`. -/
theorem faithful_Xroot_gate {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (terminal_hardening : SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad T termTube load t δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ))
    (geom_pair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad T load δ)) :
    SubpowerLE (fun δ => Xroot T (fun γ => load γ δ))
      (fun δ => Bpred δ * totalLoad T load δ) := by
  have hsplit : (fun δ => Xroot T (fun γ => load γ δ))
      = (fun δ => Xgeom T (fun γ => load γ δ) termTube
          + Xdup T (fun γ => load γ δ) termTube) :=
    funext fun δ => Xroot_split T _ termTube
  rw [hsplit]
  have hy : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ * totalLoad T load δ :=
    fun δ hδ0 hδ1 => mul_nonneg (hBpred δ hδ0 hδ1) (totalLoad_nonneg T load hload δ hδ0 hδ1)
  exact SubpowerLE.of_double (SubpowerLE.add
    (Hgeom_of_geom_pair T hroot hprefix termTube load hload Bpred geom_pair)
    (Hdup_of_terminal_hardening T hroot hprefix termTube load hload Bpred
      terminal_hardening)
    hy hy)

/-- `N²` splits into proper-predecessor pairs and root-cross pairs. -/
theorem totalLoad_sq_split {α : Type} [DecidableEq α]
    (T : Finset (List α)) (load : List α → ℝ → ℝ) (δ : ℝ) :
    (totalLoad T load δ) ^ 2
      = (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
        + Xroot T (fun γ => load γ δ) := by
  have h1 : (totalLoad T load δ) ^ 2
      = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T, load γ δ * load γ' δ := by
    unfold totalLoad
    rw [sq, Finset.sum_mul_sum]
  rw [h1]
  unfold Xroot
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
  by_cases h : treeLCA γ γ' = []
  · have h1 : ¬ (treeLCA γ γ' ≠ []) := fun hn => hn h
    rw [if_neg h1, if_pos h, zero_add]
  · rw [if_pos h, if_neg h, add_zero]

/-- The full faithful descent step, (141)+(142): `N(δ)² ≲ B^pred(δ) · N(δ)`.

Named (not proved here): `Hpred` (paper (138), the induction hypothesis),
`terminal_hardening` (paper (148), R5 stream), `geom_pair`
(paper (53)/(177)/(81), chosen per dimension at the call site). -/
theorem faithful_descent_step {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] →
      nodeAgg T (fun γ => load γ δ) a ≤ Bpred δ)
    (terminal_hardening : SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad T termTube load t δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ))
    (geom_pair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad T load δ)) :
    SubpowerLE (fun δ => (totalLoad T load δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ) := by
  have hsplit : (fun δ => (totalLoad T load δ) ^ 2)
      = (fun δ => (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
        + Xroot T (fun γ => load γ δ)) :=
    funext fun δ => totalLoad_sq_split T load δ
  rw [hsplit]
  have hy : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ * totalLoad T load δ :=
    fun δ hδ0 hδ1 => mul_nonneg (hBpred δ hδ0 hδ1) (totalLoad_nonneg T load hload δ hδ0 hδ1)
  exact SubpowerLE.of_double (SubpowerLE.add
    (proper_predecessor_SubpowerLE T hroot hprefix load hload Bpred hBpred Hpred)
    (faithful_Xroot_gate T hroot hprefix termTube load hload Bpred hBpred
      terminal_hardening geom_pair)
    hy hy)

end FilteredDescent
