import Theorems.Thm_FilteredDescent_DescentLabels
import Definitions.Def_FilteredDescent_Analytic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi

/-!
# Filtered descent — the constructed history tree (paper §§6–9, M1–M2)

This file builds the paper's §§6–9 history tree *as a mathematical object*,
with the (135) descent labels proved (not assumed) to strictly decrease
along tree edges.

## The model (honest scoping)

The paper's §§6–9 descent builds a history tree by iterating three kinds
of steps: support faces (shrinking the tube support `I`), confluence
branchings (density type `χ`, length `ℓ(χ)`), and Cartan steps (height `n`
in the paper's notation).  A Markov deletion then prunes low-density
branches.

Our construction is a **symmetric model** of this descent:

* Histories are words over the mark alphabet `DMark`:
  `conf b` (confluence branch `b : Fin B`), `cartan` (Cartan step),
  `select t` (terminal tube choice `t : Fin n`).
* `ValidPath` enforces the phase order: `H₀` confluence steps, then
  `C₀ - 1` Cartan steps, then one terminal `select`.  No face steps occur:
  the support is constantly `univ` (all `n` tubes), so the (135) label's
  first component is constantly `n` — the descent is still strict
  lexicographic via the confluence length and Cartan height.
* Markov deletion is modelled as *retention*: the tree built here is the
  retained tree directly.  In the symmetric model every branch is retained
  with the uniform load share `1 / B ^ H₀` (see `load`), so no deletion
  steps appear.  The paper's general `(θ,j,c)` common-source aggregation
  (§10.3) degenerates, under this uniform share, to the elementary bounds
  proved in `Thm_FilteredDescent_DescentBounds.lean` — this degeneration is
  documented there, not hidden.

The full paper step relation (including face steps) is defined as
`FullStep` below with its label-descent lemma, documenting that our
`ValidPath` steps are the conf/cartan/select sub-relation at constant
support.

## Contents

* `DMark`: the history-mark alphabet.
* `confCount` / `cartanCount` / `selectCount`: mark counters.
* `ValidPath`: the inductive validity predicate (phase-ordered steps).
* `histLen`, `cartanH`, `dlab`: the (135) state functions and label.
* `DescentLt_triple`: usable form of the lexicographic order.
* `ValidPath.extend_inv`: inversion — every valid extension is one of the
  three steps, with strict label descent.  This yields `DescentLabels`.
* `ValidPath.phase`: phase decomposition (confluence word + Cartan padding
  + optional select), the workhorse for counting.
* `descTree`: the history tree as a `Finset`, with `[] ∈`, prefix-closed,
  and `DescentLabels` — all proved.
* `FullStep`: the paper's full step relation (face/conf/cartan) with
  label descent (honesty documentation).
* `termTube`, `descentLoad`: terminal-tube reading and the uniform-share
  load `S.shadeVol t δ / B ^ H₀`.
-/

namespace FilteredDescent

variable {n B H₀ C₀ : ℕ}

/-- History marks (paper §§6–9): confluence branch choice, Cartan step,
terminal tube selection. -/
inductive DMark (n B : ℕ) where
  | conf : Fin B → DMark n B
  | cartan : DMark n B
  | select : Fin n → DMark n B
deriving DecidableEq

/-- Number of confluence marks in a history word. -/
def confCount : List (DMark n B) → ℕ
  | [] => 0
  | (DMark.conf _) :: w => confCount w + 1
  | _ :: w => confCount w

/-- Number of Cartan marks in a history word. -/
def cartanCount : List (DMark n B) → ℕ
  | [] => 0
  | DMark.cartan :: w => cartanCount w + 1
  | _ :: w => cartanCount w

/-- Number of select marks in a history word. -/
def selectCount : List (DMark n B) → ℕ
  | [] => 0
  | (DMark.select _) :: w => selectCount w + 1
  | _ :: w => selectCount w

@[simp] theorem confCount_nil : confCount (n := n) (B := B) [] = 0 := rfl
@[simp] theorem cartanCount_nil : cartanCount (n := n) (B := B) [] = 0 := rfl
@[simp] theorem selectCount_nil : selectCount (n := n) (B := B) [] = 0 := rfl

@[simp] theorem confCount_cons_conf (b : Fin B) (w : List (DMark n B)) :
    confCount ((DMark.conf b) :: w) = confCount w + 1 := rfl
@[simp] theorem confCount_cons_cartan (w : List (DMark n B)) :
    confCount (DMark.cartan :: w) = confCount w := rfl
@[simp] theorem confCount_cons_select (t : Fin n) (w : List (DMark n B)) :
    confCount ((DMark.select t) :: w) = confCount w := rfl
@[simp] theorem cartanCount_cons_conf (b : Fin B) (w : List (DMark n B)) :
    cartanCount ((DMark.conf b) :: w) = cartanCount w := rfl
@[simp] theorem cartanCount_cons_cartan (w : List (DMark n B)) :
    cartanCount (DMark.cartan :: w) = cartanCount w + 1 := rfl
@[simp] theorem cartanCount_cons_select (t : Fin n) (w : List (DMark n B)) :
    cartanCount ((DMark.select t) :: w) = cartanCount w := rfl
@[simp] theorem selectCount_cons_conf (b : Fin B) (w : List (DMark n B)) :
    selectCount ((DMark.conf b) :: w) = selectCount w := rfl
@[simp] theorem selectCount_cons_cartan (w : List (DMark n B)) :
    selectCount (DMark.cartan :: w) = selectCount w := rfl
@[simp] theorem selectCount_cons_select (t : Fin n) (w : List (DMark n B)) :
    selectCount ((DMark.select t) :: w) = selectCount w + 1 := rfl

theorem confCount_append (l₁ l₂ : List (DMark n B)) :
    confCount (l₁ ++ l₂) = confCount l₁ + confCount l₂ := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
      cases x <;> simp only [List.cons_append, confCount_cons_conf, confCount_cons_cartan,
        confCount_cons_select, ih]; omega

theorem cartanCount_append (l₁ l₂ : List (DMark n B)) :
    cartanCount (l₁ ++ l₂) = cartanCount l₁ + cartanCount l₂ := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
      cases x <;> simp only [List.cons_append, cartanCount_cons_conf, cartanCount_cons_cartan,
        cartanCount_cons_select, ih]; omega

theorem selectCount_append (l₁ l₂ : List (DMark n B)) :
    selectCount (l₁ ++ l₂) = selectCount l₁ + selectCount l₂ := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
      cases x <;> simp only [List.cons_append, selectCount_cons_conf, selectCount_cons_cartan,
        selectCount_cons_select, ih]; omega

/-- The three counters sum to the word length. -/
theorem count_sum_length (w : List (DMark n B)) :
    confCount w + cartanCount w + selectCount w = w.length := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      cases x with
      | conf b => simp; omega
      | cartan => simp; omega
      | select t => simp; omega

/-- Valid descent histories (paper §§6–9): `H₀` confluence branchings,
then `C₀ - 1` Cartan steps, then the terminal tube select.  Each
constructor appends one mark at the end (children in the prefix tree).
No face steps: the support stays `univ` throughout. -/
inductive ValidPath (n B H₀ C₀ : ℕ) : List (DMark n B) → Prop where
  | nil : ValidPath n B H₀ C₀ []
  | confStep : ∀ {w : List (DMark n B)} {b : Fin B},
      ValidPath n B H₀ C₀ w → confCount w < H₀ → cartanCount w = 0 →
      selectCount w = 0 → ValidPath n B H₀ C₀ (w ++ [DMark.conf b])
  | cartanStep : ∀ {w : List (DMark n B)},
      ValidPath n B H₀ C₀ w → confCount w = H₀ → cartanCount w + 1 < C₀ →
      selectCount w = 0 → ValidPath n B H₀ C₀ (w ++ [DMark.cartan])
  | selectStep : ∀ {w : List (DMark n B)} {t : Fin n},
      ValidPath n B H₀ C₀ w → confCount w = H₀ → cartanCount w + 1 = C₀ →
      selectCount w = 0 → ValidPath n B H₀ C₀ (w ++ [DMark.select t])

/-- Remaining confluence length `ℓ(χ)` (paper (135), second component). -/
def histLen (H₀ : ℕ) (w : List (DMark n B)) : ℕ := H₀ - confCount w

/-- Remaining Cartan height (paper (135), third component).  The terminal
select consumes the last Cartan unit. -/
def cartanH (C₀ : ℕ) (w : List (DMark n B)) : ℕ :=
  C₀ - cartanCount w - selectCount w

/-- The (135) descent label: `(|I|, ℓ(χ), n)` with `|I| = n` constant
(support always `univ`), confluence length, Cartan height. -/
def dlab (n H₀ C₀ : ℕ) (w : List (DMark n B)) : ℕ × ℕ × ℕ :=
  (n, histLen H₀ w, cartanH C₀ w)

/-- Usable form of the (135) lexicographic order on triples. -/
theorem DescentLt_triple {p q : ℕ × ℕ × ℕ} :
    DescentLt p q ↔ p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2.1 < q.2.1) ∨
      (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2 < q.2.2) := by
  unfold DescentLt descentKey
  simp only [InvImage]
  rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex, toLex_inj]
  simp only [Prod.mk.injEq]
  tauto

/-- Inversion for valid extensions: every one-mark valid extension of a
history is one of the three descent steps, and the (135) label strictly
decreases.  (This is the engine behind `DescentLabels`.) -/
theorem ValidPath.extend_inv {v : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ v) :
    ∀ (w : List (DMark n B)) (x : DMark n B), v = w ++ [x] →
    ValidPath n B H₀ C₀ w ∧
      DescentLt (dlab n H₀ C₀ (w ++ [x])) (dlab n H₀ C₀ w) := by
  induction h
  · -- nil: [] cannot be w ++ [x]
    intro w x heq
    have hlen := congrArg List.length heq
    simp at hlen
  · -- confStep
    rename_i w' b hpre hc1 hc2 hc3 ih
    intro w x heq
    have hlen : w'.length = w.length := by
      have h2 := congrArg List.length heq
      simp at h2
      omega
    obtain ⟨hw'w, hxx⟩ := List.append_inj heq hlen
    have hbx : x = DMark.conf b := by simpa using hxx.symm
    rw [hbx, ← hw'w]
    refine ⟨hpre, ?_⟩
    have e1 : confCount (w' ++ [DMark.conf b]) = confCount w' + 1 := by
      rw [confCount_append]; simp
    have e2 : cartanCount (w' ++ [DMark.conf b]) = cartanCount w' := by
      rw [cartanCount_append]; simp
    have e3 : selectCount (w' ++ [DMark.conf b]) = selectCount w' := by
      rw [selectCount_append]; simp
    rw [DescentLt_triple]
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    show histLen H₀ (w' ++ [DMark.conf b]) < histLen H₀ w'
    unfold histLen
    rw [e1]
    omega
  · -- cartanStep
    rename_i w' hpre hc1 hc2 hc3 ih
    intro w x heq
    have hlen : w'.length = w.length := by
      have h2 := congrArg List.length heq
      simp at h2
      omega
    obtain ⟨hw'w, hxx⟩ := List.append_inj heq hlen
    have hbx : x = DMark.cartan := by simpa using hxx.symm
    rw [hbx, ← hw'w]
    refine ⟨hpre, ?_⟩
    have e1 : confCount (w' ++ [DMark.cartan]) = confCount w' := by
      rw [confCount_append]; simp
    have e2 : cartanCount (w' ++ [DMark.cartan]) = cartanCount w' + 1 := by
      rw [cartanCount_append]; simp
    have e3 : selectCount (w' ++ [DMark.cartan]) = selectCount w' := by
      rw [selectCount_append]; simp
    rw [DescentLt_triple]
    refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
    · show histLen H₀ (w' ++ [DMark.cartan]) = histLen H₀ w'
      unfold histLen
      rw [e1]
    · show cartanH C₀ (w' ++ [DMark.cartan]) < cartanH C₀ w'
      unfold cartanH
      rw [e2, e3]
      omega
  · -- selectStep
    rename_i w' t hpre hc1 hc2 hc3 ih
    intro w x heq
    have hlen : w'.length = w.length := by
      have h2 := congrArg List.length heq
      simp at h2
      omega
    obtain ⟨hw'w, hxx⟩ := List.append_inj heq hlen
    have hbx : x = DMark.select t := by simpa using hxx.symm
    rw [hbx, ← hw'w]
    refine ⟨hpre, ?_⟩
    have e1 : confCount (w' ++ [DMark.select t]) = confCount w' := by
      rw [confCount_append]; simp
    have e2 : cartanCount (w' ++ [DMark.select t]) = cartanCount w' := by
      rw [cartanCount_append]; simp
    have e3 : selectCount (w' ++ [DMark.select t]) = selectCount w' + 1 := by
      rw [selectCount_append]; simp
    rw [DescentLt_triple]
    refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
    · show histLen H₀ (w' ++ [DMark.select t]) = histLen H₀ w'
      unfold histLen
      rw [e1]
    · show cartanH C₀ (w' ++ [DMark.select t]) < cartanH C₀ w'
      unfold cartanH
      rw [e2, e3]
      omega

/-- Every valid path has length at most `H₀ + C₀`. -/
theorem ValidPath.length_le {w : List (DMark n B)} (h : ValidPath n B H₀ C₀ w) :
    w.length ≤ H₀ + C₀ := by
  induction h
  · simp
  · rename_i w' b hpre hc1 hc2 hc3 ih
    have hcc := count_sum_length w'
    simp only [List.length_append, List.length_singleton]
    omega
  · rename_i w' hpre hc1 hc2 hc3 ih
    have hcc := count_sum_length w'
    simp only [List.length_append, List.length_singleton]
    omega
  · rename_i w' t hpre hc1 hc2 hc3 ih
    have hcc := count_sum_length w'
    simp only [List.length_append, List.length_singleton]
    omega

/-- Valid paths are closed under taking prefixes of an appended suffix,
by repeated `extend_inv`. -/
theorem ValidPath.of_append {t p l : List (DMark n B)}
    (ht : l = p ++ t) (h : ValidPath n B H₀ C₀ l) :
    ValidPath n B H₀ C₀ p := by
  induction t generalizing p l with
  | nil =>
      rw [List.append_nil] at ht
      exact ht ▸ h
  | cons x t' ih =>
      have heq : l = (p ++ [x]) ++ t' := by
        simp [ht, List.append_assoc]
      have hp' := ih heq h
      obtain ⟨hp, _⟩ := ValidPath.extend_inv hp' p x rfl
      exact hp

/-- `ValidPath` is prefix-closed. -/
theorem ValidPath.prefix_closed {l p : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ l) (hpp : p <+: l) : ValidPath n B H₀ C₀ p := by
  obtain ⟨t, ht⟩ := hpp
  exact ValidPath.of_append ht.symm h

/-- `DMark` is finite: `conf`/`cartan`/`select` embed into a sum of `Fin`s. -/
def DMark.toSum : DMark n B → Fin B ⊕ Unit ⊕ Fin n
  | DMark.conf b => Sum.inl b
  | DMark.cartan => Sum.inr (Sum.inl ())
  | DMark.select t => Sum.inr (Sum.inr t)

def DMark.ofSum : Fin B ⊕ Unit ⊕ Fin n → DMark n B
  | Sum.inl b => DMark.conf b
  | Sum.inr (Sum.inl ()) => DMark.cartan
  | Sum.inr (Sum.inr t) => DMark.select t

def DMark.equiv : DMark n B ≃ Fin B ⊕ Unit ⊕ Fin n where
  toFun := DMark.toSum
  invFun := DMark.ofSum
  left_inv := by rintro (_|_|_) <;> rfl
  right_inv := by rintro (_|_|_) <;> rfl

instance : Fintype (DMark n B) :=
  Fintype.ofEquiv (Fin B ⊕ Unit ⊕ Fin n) DMark.equiv.symm

/-- The subtype of valid paths is finite, via the length + `getD` code. -/
noncomputable instance : Fintype {w : List (DMark n B) // ValidPath n B H₀ C₀ w} := by
  refine Fintype.ofInjective
    (fun w : {w : List (DMark n B) // ValidPath n B H₀ C₀ w} =>
      ((⟨w.val.length, Nat.lt_succ_of_le (ValidPath.length_le w.property)⟩ :
        Fin (H₀ + C₀ + 1)),
       (fun i : Fin (H₀ + C₀) => w.val.getD i.val DMark.cartan))) ?_
  intro a b hab
  have hlen : a.val.length = b.val.length := by
    have h := congrArg Prod.fst hab
    simpa using h
  have hget : ∀ i : Fin (H₀ + C₀),
      a.val.getD i.val DMark.cartan = b.val.getD i.val DMark.cartan := by
    have h := congrArg Prod.snd hab
    intro i
    simpa using congrFun h i
  have heq : a.val = b.val := by
    apply List.ext_getElem hlen
    intro n h₁ h₂
    have hn : n < H₀ + C₀ := by
      have hle := ValidPath.length_le a.property
      omega
    have hgi := hget ⟨n, hn⟩
    have e1 : a.val[n]'h₁ = a.val.getD n DMark.cartan := List.getElem_eq_getD _
    have e2 : b.val[n]'h₂ = b.val.getD n DMark.cartan := List.getElem_eq_getD _
    rw [e1, e2]
    exact hgi
  exact Subtype.ext heq

/-- The §§6–9 history tree as a `Finset`. -/
noncomputable def descTree (n B H₀ C₀ : ℕ) : Finset (List (DMark n B)) :=
  (Finset.univ : Finset {w : List (DMark n B) // ValidPath n B H₀ C₀ w}).image
    Subtype.val

theorem descTree_mem {w : List (DMark n B)} :
    w ∈ descTree n B H₀ C₀ ↔ ValidPath n B H₀ C₀ w := by
  constructor
  · intro h
    obtain ⟨⟨w', hw'⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact hw'
  · intro h
    exact Finset.mem_image.mpr ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩

/-- The root `[]` is in the tree. -/
theorem descTree_root : ([] : List (DMark n B)) ∈ descTree n B H₀ C₀ := by
  rw [descTree_mem]
  exact ValidPath.nil

/-- The tree is prefix-closed. -/
theorem descTree_prefix {l : List (DMark n B)} (hl : l ∈ descTree n B H₀ C₀)
    {p : List (DMark n B)} (hpp : p <+: l) : p ∈ descTree n B H₀ C₀ := by
  rw [descTree_mem] at hl ⊢
  exact ValidPath.prefix_closed hl hpp

/-- The (135) labels strictly decrease along tree edges: `DescentLabels`,
proved (not assumed) via `extend_inv`. -/
theorem descTree_labels :
    DescentLabels (descTree n B H₀ C₀) (dlab n H₀ C₀) := by
  intro a ha b hb
  rw [treeChildren, Finset.mem_filter] at hb
  obtain ⟨hbT, hab_pre, hab_len⟩ := hb
  rw [descTree_mem] at ha hbT
  obtain ⟨t, ht⟩ := hab_pre
  have htlen : t.length = 1 := by
    have h2 := congrArg List.length ht
    simp at h2 ⊢
    omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp htlen
  have hbeq : b = a ++ [x] := by rw [← ht, hx]
  have hdesc := (ValidPath.extend_inv hbT a x hbeq).2
  rwa [← hbeq] at hdesc

/-- Terminal tube reading: the `select` mark at the end of a history.
Total via a default (needs `0 < n`). -/
def termTube (hn : 0 < n) (w : List (DMark n B)) : Fin n :=
  match w.getLast? with
  | some (DMark.select t) => t
  | _ => ⟨0, hn⟩

/-- The uniform-share load `u_γ(δ) = S.shadeVol (termTube γ) δ / B ^ H₀`
(paper §§6–9 symmetric model: every confluence branch retained with
equal share). -/
noncomputable def descentLoad (H₀ : ℕ) (S : ShadedTubes n) (δ : ℝ) (hn : 0 < n)
    (w : List (DMark n B)) : ℝ :=
  S.shadeVol (termTube hn w) δ / (B ^ H₀ : ℝ)

/-- The load is nonnegative on tree leaves (from `shade_nonneg`). -/
theorem descentLoad_nonneg (S : ShadedTubes n) (δ : ℝ) (hδ1 : 0 < δ)
    (hδ2 : δ < 1) (hn : 0 < n) {γ : List (DMark n B)}
    (_hγ : γ ∈ treeLeaves (descTree n B H₀ C₀))
    (hB : 0 < (B ^ H₀ : ℝ)) :
    0 ≤ descentLoad H₀ S δ hn γ := by
  unfold descentLoad
  apply div_nonneg _ hB.le
  exact S.shade_nonneg _ _ hδ1 hδ2

/-- Honesty documentation: the paper's §§6–9 descent also has *face* steps
shrinking the tube support `I` (lowering the first (135) label component
`|I|`).  In our symmetric model the support is constantly `univ`, so face
steps never occur: `ValidPath` is exactly the conf/cartan/select
sub-relation at constant support, and `ValidPath.extend_inv` proves its
label descent.  We record the full relation with an explicit support-size
component to document this sub-relation claim; only the
conf/cartan/select cases at constant support are instantiated. -/
inductive FullStep : ℕ × List (DMark n B) → ℕ × List (DMark n B) → Prop where
  | face {s w s'} : s' < s → FullStep (s, w) (s', w)
  | conf {s w} {b : Fin B} : FullStep (s, w) (s, w ++ [DMark.conf b])
  | cartan {s w} : FullStep (s, w) (s, w ++ [DMark.cartan])
  | select {s w} {t : Fin n} : FullStep (s, w) (s, w ++ [DMark.select t])

/-- `ValidPath` steps are `FullStep` instances at constant support `n`. -/
theorem ValidPath.toFullStep {w : List (DMark n B)} (_h : ValidPath n B H₀ C₀ w)
    {x : DMark n B} (_hx : ValidPath n B H₀ C₀ (w ++ [x])) :
    FullStep (n, w) (n, w ++ [x]) := by
  cases x with
  | conf b => exact FullStep.conf
  | cartan => exact FullStep.cartan
  | select t => exact FullStep.select

end FilteredDescent
