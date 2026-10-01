import Definitions.Def_FilteredDescent_Subpower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# M8a — Closed support recurrence (paper (124)–(125))

From the base case (`|I| ≤ 2`, paper (126)–(129)) and the support-step
recurrence (paper (124): each `B_I` with `|I| > 2` is subpower-dominated
by some strictly smaller support's cutoff), strong induction on `|I|`
closes the descent: every `B_I` is subpower-bounded (paper (125)),
uniformly for `δ ∈ (0,1)`.
-/

namespace FilteredDescent

theorem support_recurrence_closure {d : ℕ}
    (B : Finset (Fin d) → ℝ → ℝ)
    (hbase : ∀ I : Finset (Fin d), I.card ≤ 2 → SubpowerLE (B I) (fun _ => 1))
    (hrec :
      ∀ I : Finset (Fin d), 2 < I.card →
        ∃ J : Finset (Fin d), J ⊂ I ∧ SubpowerLE (B I) (B J)) :
    ∀ I : Finset (Fin d), SubpowerLE (B I) (fun _ => 1) := by
  suffices h : ∀ k : ℕ, ∀ I : Finset (Fin d), I.card = k → SubpowerLE (B I) (fun _ => 1) by
    intro I; exact h I.card I rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro I hIk
    by_cases hle : k ≤ 2
    · exact hbase I (by omega)
    · obtain ⟨J, hJI, hsub⟩ := hrec I (by omega)
      have hJlt : J.card < k := by
        have hlt := Finset.card_lt_card hJI
        omega
      exact SubpowerLE.trans_right hsub (ih J.card hJlt J rfl)

end FilteredDescent
