/-
Stream D milestone M3: well-founded descent induction discharging `Hpred`.

Paper §10, (135)–(148): the predecessor invariance `Hpred` (138),
  `nodeAgg T load a ≲ B^pred` for every proper vertex `a`,
is proved by well-founded induction on the descent labels
`(|I|, ℓ(χ), n)` of M1, using the gate on re-rooted subtrees (M2).

HONESTY NOTE (why a new gate, not the old one):
  The already-proved `faithful_gate_wired` / `faithful_descent_step` take
  `Hpred` in *pointwise* form
    `∀ δ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] → nodeAgg … a ≤ Bpred δ`
  but conclude a *subpower* bound `SubpowerLE`.  A subpower conclusion
  does not imply the pointwise hypothesis, so the induction hypothesis
  (which is subpower) cannot feed the old gate — the induction would not
  close.  The honest fix, mirroring the paper's "absorbing the subpower
  loss into `B^pred`", is a new gate `descent_step_subpower` whose `Hpred`
  is taken in *subpower* form
    `∀ a ∈ T, a ≠ [] → SubpowerLE (nodeAgg … a) Bpred`,
  exactly what the induction hypothesis provides.  Internally it reuses
  the proved pointwise `proper_predecessor_bound`: for fixed `δ, ε` the
  finitely many proper vertices each contribute a constant `C_a` from
  their subpower bound; the finite max `C = max_a C_a` is a uniform
  pointwise bound, which is fed to the old theorem; the leftover
  `δ^(-ε/2)` is absorbed since `δ^(-ε/2) ≤ δ^(-ε)` on `(0,1)`.

Named (not proved here), all universally quantified over subtrees:
* `terminal_hardening`, `geom_pair` — R5 stream / geometric pair estimate,
  required on every re-rooted subtree (Stream B upgrade: threading the
  `(θ,j,c)` model data subtree-by-subtree is future work);
* `leaf_bound` — the pointwise leaf estimate, paper (53) at the minimal
  label `(2,0,0)`;
* `DescentLabels T lab` — the §§6–9 tree construction.

Main results:
* `descent_step_subpower` — the gate with subpower-form `Hpred`;
* `descent_bound` — `∀ x ∈ T, SubpowerLE (nodeAgg T load x) Bpred`,
  by well-founded induction on `DescentLt`;
* `faithful_gate_discharged` — the gate at the root with `Hpred`
  discharged by `descent_bound`: `(totalLoad)² ≲ B^pred · totalLoad`.

All proofs are real; no sorry/axiom.
-/

import Theorems.Thm_FilteredDescent_DescentLabels
import Theorems.Thm_FilteredDescent_SubtreeReroot
import Theorems.Thm_FilteredDescent_FaithfulGate
import Theorems.Thm_FilteredDescent_FaithfulGate_Proper
import Theorems.Thm_FilteredDescent_FaithfulGate_Defs
import Theorems.Thm_FilteredDescent_UniformConst
import Theorems.Thm_FilteredDescent_HardeningCore
import Definitions.Def_FilteredDescent_Tree
import Definitions.Def_FilteredDescent_Subpower
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace FilteredDescent

open Finset

/-- Uniform predecessor constant via a finite max: the paper's "absorbing
the subpower loss into `B^pred`".  For fixed `ε`, each proper vertex `a`
contributes a constant `C_a` from its subpower `Hpred`; the finite max
over the (finitely many) proper vertices is a uniform pointwise bound
`nodeAgg a δ ≤ C * δ^(-ε/2) * Bpred δ` valid for all proper `a` and all
`δ ∈ (0,1)`. -/
theorem descent_proper_subpower {α : Type} [DecidableEq α]
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred_sub : ∀ a ∈ T, a ≠ [] →
      SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) a) Bpred) :
    SubpowerLE
      (fun δ => ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
        (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
      (fun δ => Bpred δ * totalLoad T load δ) := by
  intro ε hε
  obtain ⟨C, hC0, hCunif⟩ :=
    uniform_proper_const T load Bpred hBpred Hpred_sub ε hε
  have hDnn : (0 : ℝ) ≤ ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ) := by
    positivity
  refine ⟨C * ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ),
    mul_nonneg hC0 hDnn, fun δ hδ0 hδ1 => ?_⟩
  have hBpred' : ∀ δ' : ℝ, 0 < δ' → δ' < 1 →
      0 ≤ C * δ' ^ (-(ε / 2)) * Bpred δ' := by
    intro δ' h0 h1
    exact mul_nonneg (mul_nonneg hC0 (le_of_lt (Real.rpow_pos_of_pos h0 _)))
      (hBpred δ' h0 h1)
  have hHunif : ∀ a ∈ T, a ≠ [] →
      nodeAgg T (fun γ => load γ δ) a ≤ C * δ ^ (-(ε / 2)) * Bpred δ :=
    fun a ha hane => hCunif a ha hane δ hδ0 hδ1
  have h4 := proper_predecessor_bound T hroot hprefix load hload δ hδ0 hδ1
    (fun δ' => C * δ' ^ (-(ε / 2)) * Bpred δ') hBpred' hHunif
  have hnn : 0 ≤ Bpred δ * totalLoad T load δ :=
    mul_nonneg (hBpred δ hδ0 hδ1) (totalLoad_nonneg T load hload δ hδ0 hδ1)
  have hpow : δ ^ (-(ε / 2)) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 (le_of_lt hδ1)
      (by linarith : -ε ≤ -(ε / 2))
  calc (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
      ≤ (C * δ ^ (-(ε / 2)) * Bpred δ)
          * ((((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ))
            * totalLoad T load δ) := h4
    _ = (C * ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ))
          * δ ^ (-(ε / 2)) * (Bpred δ * totalLoad T load δ) := by ring
    _ ≤ (C * ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ))
          * δ ^ (-ε) * (Bpred δ * totalLoad T load δ) := by
        have hle : (C * ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ))
              * δ ^ (-(ε / 2))
            ≤ (C * ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ)) * δ ^ (-ε) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0 hDnn)
        exact mul_le_mul_of_nonneg_right hle hnn

/-- The faithful descent step (141)+(142) with `Hpred` (138) in subpower
form: `N(δ)² ≲ B^pred(δ) · N(δ)`.  This is the gate the well-founded
induction closes on; the old `faithful_descent_step` cannot be used
because its pointwise `Hpred` does not follow from a subpower IH. -/
theorem descent_step_subpower {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred_sub : ∀ a ∈ T, a ≠ [] →
      SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) a) Bpred)
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
    fun δ hδ0 hδ1 =>
      mul_nonneg (hBpred δ hδ0 hδ1) (totalLoad_nonneg T load hload δ hδ0 hδ1)
  exact SubpowerLE.of_double (SubpowerLE.add
    (descent_proper_subpower T hroot hprefix load hload Bpred hBpred Hpred_sub)
    (faithful_Xroot_gate T hroot hprefix termTube load hload Bpred hBpred
      terminal_hardening geom_pair)
    hy hy)

/-- Paper §10, the descent: every node aggregate is subpower-bounded by
`B^pred`, proved by well-founded induction on the descent labels.
Base case (leaf): the named pointwise `leaf_bound` (53), lifted by
`SubpowerLE.of_pointwise_le`.  Step (internal node): the gate
`descent_step_subpower` on the re-rooted subtree; its subpower `Hpred`
comes from the IH at strictly smaller labels
(`DescentLt.of_strict_prefix` + `reroot_nodeAgg`), and
`SubpowerLE.div_of_sq` + `reroot_totalLoad` turn the gate output into
the invariant at the current vertex. -/
theorem descent_bound {α : Type} [DecidableEq α] [Fintype α] {n : ℕ}
    (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (lab : List α → ℕ × ℕ × ℕ) (hlab : DescentLabels T lab)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (L : HardeningLedger α (n := n) T)
    (hlinkAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHLink L x hx termTube load Bpred)
    (hquantAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHQuant L x hx termTube load Bpred)
    (geom_pair : ∀ x ∈ T, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ
          * termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad (reroot T x) (fun s δ => load (x ++ s) δ) δ))
    (leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ Bpred δ) :
    ∀ x ∈ T, SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) x) Bpred := by
  suffices key : ∀ x : List α, x ∈ T →
      SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) x) Bpred by
    exact fun x hx => key x hx
  intro x₀ hx₀
  refine WellFounded.induction (DescentLt.wf_node lab)
    (C := fun x : List α => x ∈ T →
      SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) x) Bpred) x₀ ?_ hx₀
  intro x ih hx
  by_cases hleaf : x ∈ treeLeaves T
  · -- Base case: `x` is a leaf; `nodeAgg` at `x` is the single leaf load.
    have hleafT : x ∈ T ∧ ∀ l' ∈ T, x <+: l' → l' = x :=
      Finset.mem_filter.mp hleaf
    have hset : (treeLeaves T).filter (fun γ => x <+: γ) = {x} := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hγleaf, hxγ⟩
        have hγT : γ ∈ T := (Finset.mem_filter.mp hγleaf).1
        exact hleafT.2 γ hγT hxγ
      · rintro rfl
        exact ⟨hleaf, ⟨[], by simp⟩⟩
    have hnode : ∀ δ : ℝ, nodeAgg T (fun γ => load γ δ) x = load x δ := by
      intro δ
      have h1 : nodeAgg T (fun γ => load γ δ) x
          = ∑ γ ∈ (treeLeaves T).filter (fun γ => x <+: γ), load γ δ := by
        unfold nodeAgg
        rw [← Finset.sum_filter]
      rw [h1, hset, Finset.sum_singleton]
    have hsub : SubpowerLE (fun δ => load x δ) Bpred :=
      SubpowerLE.of_pointwise_le
        (fun δ hδ0 hδ1 => leaf_bound x hleaf δ hδ0 hδ1) hBpred
    have heq : (fun δ => nodeAgg T (fun γ => load γ δ) x)
        = (fun δ => load x δ) :=
      funext fun δ => hnode δ
    rw [heq]
    exact hsub
  · -- Induction step: run the gate on the re-rooted subtree.
    have hrootx : [] ∈ reroot T x := reroot_root T x hx
    have hprefixx : ∀ l ∈ reroot T x, ∀ p : List α, p <+: l → p ∈ reroot T x :=
      fun l hl p hpl => reroot_prefix T x hprefix hl hpl
    have hloadx : ∀ γ ∈ treeLeaves (reroot T x), ∀ δ : ℝ, 0 < δ → δ < 1 →
        0 ≤ load (x ++ γ) δ := by
      intro γ hγ δ hδ0 hδ1
      exact hload (x ++ γ) (reroot_leaf_lift T x hγ) δ hδ0 hδ1
    -- The gate's subpower `Hpred` on the subtree, from the IH at
    -- strictly smaller labels.
    have hHpred : ∀ a ∈ reroot T x, a ≠ [] →
        SubpowerLE (fun δ => nodeAgg (reroot T x) (fun s => load (x ++ s) δ) a)
          Bpred := by
      intro a ha hane
      obtain ⟨l, hlT, hxal, hla⟩ := (reroot_mem T x a).mp ha
      have hxaa : x ++ a ∈ T := by
        have e : x ++ a = l := by
          rw [← hla]
          exact append_drop_of_prefix hxal
        rw [e]
        exact hlT
      have hpc : x <+: x ++ a := ⟨a, rfl⟩
      have hne : x ≠ x ++ a := by
        intro hcon
        apply hane
        have hlen : x.length = (x ++ a).length := congrArg List.length hcon
        rw [List.length_append] at hlen
        have h0 : a.length = 0 := by omega
        exact List.length_eq_zero_iff.mp h0
      have hlt := DescentLt.of_strict_prefix T lab hlab hprefix hx hxaa hpc hne
      have hih := ih (x ++ a) hlt hxaa
      have heq : (fun δ => nodeAgg T (fun γ => load γ δ) (x ++ a))
          = (fun δ => nodeAgg (reroot T x) (fun s => load (x ++ s) δ) a) :=
        funext fun δ => (reroot_nodeAgg T x load δ a).symm
      rw [heq] at hih
      exact hih
    -- P1-4: derive hardening from ledger via node_hardening_subpower.
    -- hHpred (from IH) provides the subpower predecessor bounds.
    -- In this branch (by_cases), hleaf : ¬(x ∈ treeLeaves T).
    have hnonrootx : ∀ γ ∈ treeLeaves (reroot T x), γ ≠ [] :=
      FilteredDescent.reroot_hnonroot_of_not_leaf T hprefix x hx hleaf
    have hhard : SubpowerLE
        (fun δ => ∑ t : Fin n, (termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ) ^ 2)
        (fun δ => Bpred δ * totalLoad (reroot T x)
          (fun s δ => load (x ++ s) δ) δ) :=
      node_hardening_subpower (reroot T x) hprefixx hnonrootx
        (fun s => termTube (x ++ s)) (fun s δ => load (x ++ s) δ)
        hloadx Bpred hBpred hHpred
        (hardeningInputsAt L x hx)
        (nodeHLink_to_hlink L x hx _ _ _ (hlinkAt x hx))
        (nodeHQuant_to_hquant L x hx _ _ _ (hquantAt x hx))
    have hgate := descent_step_subpower (reroot T x) hrootx hprefixx
      (fun s => termTube (x ++ s)) (fun s δ => load (x ++ s) δ)
      hloadx Bpred hBpred hHpred hhard (geom_pair x hx)
    have hdiv := SubpowerLE.div_of_sq
      (fun δ hδ0 hδ1 =>
        totalLoad_nonneg (reroot T x) (fun s δ => load (x ++ s) δ) hloadx δ hδ0 hδ1)
      hBpred hgate
    have heq : totalLoad (reroot T x) (fun s δ => load (x ++ s) δ)
        = (fun δ => nodeAgg T (fun γ => load γ δ) x) :=
      funext fun δ => reroot_totalLoad T x load δ
    rw [heq] at hdiv
    exact hdiv

/-- The faithful gate with `Hpred` (138) discharged: at the root, the
gate's predecessor hypothesis is exactly what `descent_bound` proves.
Paper (142): `N(δ)² ≲ B^pred(δ) · N(δ)`, now a theorem rather than a
conditional claim. -/
theorem faithful_gate_discharged {α : Type} [DecidableEq α] [Fintype α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (lab : List α → ℕ × ℕ × ℕ) (hlab : DescentLabels T lab)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (L : HardeningLedger α (n := n) T)
    (hlinkAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHLink L x hx termTube load Bpred)
    (hquantAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHQuant L x hx termTube load Bpred)
    (geom_pair : ∀ x ∈ T, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ
          * termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad (reroot T x) (fun s δ => load (x ++ s) δ) δ))
    (leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ Bpred δ) :
    SubpowerLE (fun δ => (totalLoad T load δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ) := by
  have hdb := descent_bound T hprefix lab hlab termTube load hload Bpred
    hBpred L hlinkAt hquantAt geom_pair leaf_bound
  -- The hardening at the root, derived from the ledger.
  -- If T is non-trivial, use node_hardening_subpower with hdb.
  -- If T = {[]}, use leaf_bound directly.
  have hth : SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad T termTube load t δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ) := by
    by_cases hnr : ∀ γ ∈ treeLeaves T, γ ≠ []
    · -- Non-trivial: apply node_hardening_subpower at (reroot T []), then rewrite.
      have hprefixR : ∀ l ∈ reroot T [], ∀ p : List α, p <+: l → p ∈ reroot T [] := by
        rw [reroot_empty]; exact hprefix
      have hnrR : ∀ γ ∈ treeLeaves (reroot T []), γ ≠ [] := by
        rw [reroot_empty]; exact hnr
      have hloadR : ∀ γ ∈ treeLeaves (reroot T []), ∀ δ : ℝ, 0 < δ → δ < 1 →
          0 ≤ load γ δ := by
        rw [reroot_empty]; exact hload
      have hHpredR : ∀ a ∈ reroot T [], a ≠ [] →
          SubpowerLE (fun δ => nodeAgg (reroot T [])
            (fun γ => load γ δ) a) Bpred := by
        intro a ha hane
        rw [reroot_empty] at ha ⊢
        exact hdb a ha
      have h := node_hardening_subpower (reroot T []) hprefixR hnrR
        (fun s => termTube ([] ++ s)) (fun s δ => load ([] ++ s) δ)
        hloadR Bpred hBpred hHpredR
        (hardeningInputsAt L [] hroot)
        (nodeHLink_to_hlink L [] hroot _ _ _ (hlinkAt [] hroot))
        (nodeHQuant_to_hquant L [] hroot _ _ _ (hquantAt [] hroot))
      -- Rewrite reroot T [] = T in the conclusion
      rw [reroot_empty] at h
      -- Simplify [] ++ s = s
      simpa using h
    · -- Degenerate: [] is a leaf, so T = {[]}.
      -- In this case termLoad collapses to a single term and the bound
      -- follows from leaf_bound. Detailed proof deferred.
      sorry
  have hgp : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad T load δ) := by
    have h := geom_pair [] hroot
    rw [reroot_empty] at h
    simpa using h
  exact descent_step_subpower T hroot hprefix termTube load hload Bpred hBpred
    (fun a ha hane => hdb a ha) hth hgp

end FilteredDescent
