import Theorems.Thm_FilteredDescent_DescentTree
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-!
# Filtered descent — leaf characterization and fiber counting (paper §§6–9)

This file proves the combinatorial heart of the §§6–9 symmetric history-tree
model built in `Thm_FilteredDescent_DescentTree.lean`:

* Normal forms for `ValidPath` words (proved by induction on the *derivation*,
  not by rewriting words — this avoids the rewrite-loop technicalities):
  - `ValidPath.noSelect_form`: a select-free valid word is
    `cb.map conf ++ replicate k cartan` (confluence phase then Cartan phase);
  - `ValidPath.exists_select_split`: a word with `selectCount = 1` ends in
    its (unique) select mark;
  - `ValidPath.select_constraints`: recovering the `selectStep` constraints
    from the word shape.
* Leaf characterization (`leaf_eq_leafWord`): leaves of `descTree` are
  exactly the `leafWord (C₀ := C₀) cb t` words (`H₀` confluence branches, `C₀ - 1`
  Cartan steps, terminal `select t`).
* Fiber counting: the `(x, t)`-fiber (leaves below `x` selecting tube `t`)
  has at most `B ^ H₀` elements (`fiber_card_le`), and exactly `B ^ H₀` at
  the root (`root_fiber_card`).

These feed the quantitative bounds in `Thm_FilteredDescent_DescentBounds.lean`.
-/

namespace FilteredDescent

variable {n B H₀ C₀ : ℕ}

/-- Map a list of confluence branches to their word marks. -/
def confWord (cb : List (Fin B)) : List (DMark n B) := cb.map (DMark.conf (n := n))

/-- A leaf word: `H₀` confluence branches `cb`, then `C₀ - 1` Cartan steps,
then the terminal `select t`. -/
def leafWord (cb : List (Fin B)) (t : Fin n) : List (DMark n B) :=
  confWord (n := n) cb ++ List.replicate (C₀ - 1) (DMark.cartan : DMark n B)
    ++ [DMark.select (n := n) t]

/-- The confluence-branch word of a leaf (inverse of `leafWord` on leaves). -/
def leafConf : List (DMark n B) → List (Fin B)
  | [] => []
  | (DMark.conf b) :: w => b :: leafConf w
  | _ :: w => leafConf w

/-! ## Counter lemmas for the normal forms -/

theorem confWord_nil : confWord (n := n) ([] : List (Fin B)) = [] := rfl

theorem confCount_confWord (cb : List (Fin B)) :
    confCount (confWord (n := n) cb) = cb.length := by
  induction cb with
  | nil => rfl
  | cons b cb' ih =>
      show confCount ((DMark.conf (n := n) b) :: confWord (n := n) cb') = (b :: cb').length
      rw [confCount_cons_conf, ih, List.length_cons]

theorem cartanCount_confWord (cb : List (Fin B)) :
    cartanCount (confWord (n := n) cb) = 0 := by
  induction cb with
  | nil => rfl
  | cons b cb' ih =>
      show cartanCount ((DMark.conf (n := n) b) :: confWord (n := n) cb') = 0
      rw [cartanCount_cons_conf, ih]

theorem selectCount_confWord (cb : List (Fin B)) :
    selectCount (confWord (n := n) cb) = 0 := by
  induction cb with
  | nil => rfl
  | cons b cb' ih =>
      show selectCount ((DMark.conf (n := n) b) :: confWord (n := n) cb') = 0
      rw [selectCount_cons_conf, ih]

theorem confCount_replicate_cartan (k : ℕ) :
    confCount (List.replicate k (DMark.cartan : DMark n B)) = 0 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
      rw [List.replicate_succ, confCount_cons_cartan, ih]

theorem cartanCount_replicate_cartan (k : ℕ) :
    cartanCount (List.replicate k (DMark.cartan : DMark n B)) = k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
      rw [List.replicate_succ, cartanCount_cons_cartan, ih]

theorem selectCount_replicate_cartan (k : ℕ) :
    selectCount (List.replicate k (DMark.cartan : DMark n B)) = 0 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
      rw [List.replicate_succ, selectCount_cons_cartan, ih]

/-- `leafConf` is a left inverse of `confWord`. -/
theorem leafConf_confWord (cb : List (Fin B)) :
    leafConf (confWord (n := n) cb) = cb := by
  induction cb with
  | nil => rfl
  | cons b cb' ih =>
      show b :: leafConf (confWord (n := n) cb') = b :: cb'
      rw [ih]

theorem leafConf_replicate_cartan (k : ℕ) :
    leafConf (List.replicate k (DMark.cartan : DMark n B)) = [] := by
  induction k with
  | zero => rfl
  | succ k' ih =>
      rw [List.replicate_succ]
      show leafConf (List.replicate k' (DMark.cartan : DMark n B)) = []
      exact ih

/-- `leafConf` length equals `confCount`. -/
theorem leafConf_length (w : List (DMark n B)) :
    (leafConf w).length = confCount w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | conf b => simp [leafConf, confCount, ih]
      | cartan => simp [leafConf, confCount, ih]
      | select t => simp [leafConf, confCount, ih]

/-- `leafConf` distributes over append. -/
theorem leafConf_append (l₁ l₂ : List (DMark n B)) :
    leafConf (l₁ ++ l₂) = leafConf l₁ ++ leafConf l₂ := by
  induction l₁ with
  | nil => simp [leafConf]
  | cons x xs ih =>
      cases x with
      | conf b => simp [leafConf, ih]
      | cartan => simp [leafConf, ih]
      | select t => simp [leafConf, ih]

theorem leafConf_leafWord (cb : List (Fin B)) (t : Fin n) :
    leafConf (leafWord (C₀ := C₀) cb t) = cb := by
  have hsel : leafConf [DMark.select (n := n) t] = ([] : List (Fin B)) := rfl
  unfold leafWord
  rw [leafConf_append, leafConf_append, leafConf_confWord,
    leafConf_replicate_cartan, hsel, List.append_nil]
  simp

theorem selectCount_leafWord (cb : List (Fin B)) (t : Fin n) :
    selectCount (leafWord (C₀ := C₀) cb t) = 1 := by
  unfold leafWord
  rw [selectCount_append, selectCount_append, selectCount_confWord,
    selectCount_replicate_cartan]
  simp

theorem termTube_leafWord (hn : 0 < n) (cb : List (Fin B)) (t : Fin n) :
    termTube hn (leafWord (C₀ := C₀) cb t) = t := by
  have hlast : (leafWord (C₀ := C₀) cb t).getLast?
      = some (DMark.select (n := n) t) := by
    unfold leafWord
    rw [List.getLast?_append]
    simp
  unfold termTube
  rw [hlast]


/-! ## Normal forms by induction on the derivation -/

/-- `confWord` distributes over append (single step). -/
theorem confWord_append_singleton (cb : List (Fin B)) (b : Fin B) :
    confWord (n := n) (cb ++ [b])
      = confWord (n := n) cb ++ [DMark.conf (n := n) b] := by
  unfold confWord
  rw [List.map_append]
  rfl

/-- Normal form for select-free valid words: all confluence marks first,
then Cartan marks.  Proved by induction on the `ValidPath` derivation
(not by rewriting the word), using that `confStep` requires
`cartanCount w = 0` so no Cartan mark can precede a confluence mark. -/
theorem ValidPath.noSelect_form {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) (hsel : selectCount w = 0) :
    ∃ cb k, w = confWord (n := n) cb
        ++ List.replicate k (DMark.cartan : DMark n B)
      ∧ cb.length = confCount w ∧ k = cartanCount w := by
  induction h with
  | nil =>
      exact ⟨[], 0, by simp [confWord], rfl, rfl⟩
  | confStep =>
      rename_i w b hvp hconf hcart hselw ih
      obtain ⟨cb, k, rfl, -, hk⟩ := ih hselw
      have hk0 : k = 0 := by rw [hk, hcart]
      subst hk0
      refine ⟨cb ++ [b], 0, ?_, ?_, ?_⟩
      · rw [confWord_append_singleton]
        simp
      · simp [confCount_append, confCount_confWord]
      · simp [cartanCount_append, cartanCount_confWord]
  | cartanStep =>
      rename_i w hvp hconf hcart hselw ih
      obtain ⟨cb, k, rfl, -, -⟩ := ih hselw
      have hr : List.replicate (k + 1) (DMark.cartan : DMark n B)
          = List.replicate k DMark.cartan ++ [DMark.cartan] := by
        rw [List.replicate_add k 1, List.replicate_one]
      refine ⟨cb, k + 1, ?_, ?_, ?_⟩
      · rw [hr, List.append_assoc]
      · rw [confCount_append, confCount_append, confCount_confWord,
          confCount_replicate_cartan]
        simp
      · rw [cartanCount_append, cartanCount_append, cartanCount_confWord,
          cartanCount_replicate_cartan]
        simp
  | selectStep =>
      rename_i w t hvp hconf hcart hselw ih
      exfalso
      rw [selectCount_append] at hsel
      simp at hsel

/-- A valid word with exactly one select ends in its select mark; the
prefix is select-free and carries the full `selectStep` constraints. -/
theorem ValidPath.exists_select_split {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) (h1 : selectCount w = 1) :
    ∃ u t, w = u ++ [DMark.select (n := n) t] ∧ ValidPath n B H₀ C₀ u
      ∧ selectCount u = 0 ∧ confCount u = H₀ ∧ cartanCount u + 1 = C₀ := by
  induction h with
  | nil =>
      exfalso
      simp at h1
  | confStep =>
      rename_i w b hvp hconf hcart hselw ih
      exfalso
      rw [selectCount_append] at h1
      have h0 : selectCount ([DMark.conf (n := n) b] : List (DMark n B)) = 0 := by
        simp
      rw [h0, Nat.add_zero] at h1
      omega
  | cartanStep =>
      rename_i w hvp hconf hcart hselw ih
      exfalso
      rw [selectCount_append] at h1
      have h0 : selectCount ([DMark.cartan] : List (DMark n B)) = 0 := by simp
      rw [h0, Nat.add_zero] at h1
      omega
  | selectStep =>
      rename_i w t hvp hconf hcart hselw ih
      exact ⟨w, t, rfl, hvp, hselw, hconf, hcart⟩

/-- Select-free valid words with full counters are exactly the
confluence/Cartan normal form with `H₀` branches and `C₀ - 1` steps. -/
theorem ValidPath.noSelect_full {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) (hsel : selectCount w = 0)
    (hconf : confCount w = H₀) (hcart : cartanCount w + 1 = C₀) :
    w = confWord (n := n) (leafConf w)
      ++ List.replicate (C₀ - 1) (DMark.cartan : DMark n B) := by
  obtain ⟨cb, k, rfl, -, -⟩ := h.noSelect_form hsel
  have hcart' : cartanCount (confWord (n := n) cb
      ++ List.replicate k (DMark.cartan : DMark n B)) = k := by
    simp [cartanCount_append, cartanCount_confWord, cartanCount_replicate_cartan]
  have hcb : cb = leafConf (confWord (n := n) cb
      ++ List.replicate k (DMark.cartan : DMark n B)) := by
    rw [leafConf_append, leafConf_confWord, leafConf_replicate_cartan,
      List.append_nil]
  have hkC : k = C₀ - 1 := by omega
  subst hkC
  rw [← hcb]

/-! ## Counter bounds by induction on the derivation -/

/-- Every valid path has at most one select mark. -/
theorem ValidPath.selectCount_le_one {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) : selectCount w ≤ 1 := by
  induction h with
  | nil => simp
  | confStep =>
      rename_i w b hvp hconf hcart hselw ih
      rw [selectCount_append]
      have h0 : selectCount ([DMark.conf (n := n) b] : List (DMark n B)) = 0 := by
        simp
      rw [h0, Nat.add_zero]
      exact ih
  | cartanStep =>
      rename_i w hvp hconf hcart hselw ih
      rw [selectCount_append]
      have h0 : selectCount ([DMark.cartan] : List (DMark n B)) = 0 := by simp
      rw [h0, Nat.add_zero]
      exact ih
  | selectStep =>
      rename_i w t hvp hconf hcart hselw ih
      rw [selectCount_append]
      have h1 : selectCount ([DMark.select (n := n) t] : List (DMark n B)) = 1 := by
        simp
      rw [h1]
      omega

/-- Confluence marks never exceed `H₀`. -/
theorem ValidPath.confCount_le {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) : confCount w ≤ H₀ := by
  induction h with
  | nil => simp
  | confStep =>
      rename_i w b hvp hconf hcart hselw ih
      rw [confCount_append]
      have h1 : confCount ([DMark.conf (n := n) b] : List (DMark n B)) = 1 := by
        simp
      rw [h1]
      omega
  | cartanStep =>
      rename_i w hvp hconf hcart hselw ih
      rw [confCount_append]
      have h0 : confCount ([DMark.cartan] : List (DMark n B)) = 0 := by simp
      rw [h0, Nat.add_zero]
      exact hconf.le
  | selectStep =>
      rename_i w t hvp hconf hcart hselw ih
      rw [confCount_append]
      have h0 : confCount ([DMark.select (n := n) t] : List (DMark n B)) = 0 := by
        simp
      rw [h0, Nat.add_zero]
      exact hconf.le

/-- While confluence is incomplete (`confCount < H₀`), no Cartan mark can
have appeared: `confStep` is the only applicable constructor and it
requires `cartanCount = 0`. -/
theorem ValidPath.conf_cartan_excl {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) (hlt : confCount w < H₀) :
    cartanCount w = 0 := by
  induction h with
  | nil => rfl
  | confStep =>
      rename_i w b hvp hconf hcart hselw ih
      rw [cartanCount_append]
      have h0 : cartanCount ([DMark.conf (n := n) b] : List (DMark n B)) = 0 := by
        simp
      rw [h0, Nat.add_zero]
      apply ih
      rw [confCount_append] at hlt
      have h1 : confCount ([DMark.conf (n := n) b] : List (DMark n B)) = 1 := by
        simp
      rw [h1] at hlt
      omega
  | cartanStep =>
      rename_i w hvp hconf hcart hselw ih
      exfalso
      rw [confCount_append] at hlt
      have h0 : confCount ([DMark.cartan] : List (DMark n B)) = 0 := by simp
      rw [h0, Nat.add_zero] at hlt
      omega
  | selectStep =>
      rename_i w t hvp hconf hcart hselw ih
      exfalso
      rw [confCount_append] at hlt
      have h0 : confCount ([DMark.select (n := n) t] : List (DMark n B)) = 0 := by
        simp
      rw [h0, Nat.add_zero] at hlt
      omega

/-- A select-free valid word with full confluence cannot overshoot the
Cartan budget (needs `0 < C₀` for the base case). -/
theorem ValidPath.cartan_le_of_noselect {w : List (DMark n B)}
    (h : ValidPath n B H₀ C₀ w) (hC : 0 < C₀)
    (hsel : selectCount w = 0) (hconf : confCount w = H₀) :
    cartanCount w + 1 ≤ C₀ := by
  induction h with
  | nil =>
      have hcc : cartanCount ([] : List (DMark n B)) = 0 := rfl
      omega
  | confStep =>
      rename_i w b hvp hlt hcart hselw ih
      have hcc : cartanCount (w ++ [DMark.conf (n := n) b]) = 0 := by
        rw [cartanCount_append]
        have h0 : cartanCount ([DMark.conf (n := n) b] : List (DMark n B)) = 0 := by
          simp
        rw [h0, Nat.add_zero]
        exact hcart
      omega
  | cartanStep =>
      rename_i w hvp hlt hcart' hselw ih
      have hcc : cartanCount (w ++ [DMark.cartan]) = cartanCount w + 1 := by
        rw [cartanCount_append]
        have h1 : cartanCount ([DMark.cartan] : List (DMark n B)) = 1 := by simp
        rw [h1]
      omega
  | selectStep =>
      rename_i w t hvp hlt hcart hselw ih
      exfalso
      rw [selectCount_append] at hsel
      simp at hsel

/-! ## Leaf characterization -/

/-- Leaves of the constructed tree are exactly the `leafWord cb t` words:
`H₀` confluence branches, `C₀ - 1` Cartan steps, terminal `select t`.
A select-free valid word can always be extended (confluence / Cartan /
select according to the counters), contradicting maximality; a word with
one select splits and normalizes via `noSelect_full`. -/
theorem leaf_eq_leafWord (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    {γ : List (DMark n B)} (hγ : γ ∈ treeLeaves (descTree n B H₀ C₀)) :
    ∃ cb t, γ = leafWord (C₀ := C₀) cb t ∧ cb.length = H₀ := by
  have hmem : γ ∈ descTree n B H₀ C₀ := Finset.mem_of_mem_filter _ hγ
  have hvp : ValidPath n B H₀ C₀ γ := descTree_mem.mp hmem
  have hmax : ∀ l' ∈ descTree n B H₀ C₀, γ <+: l' → l' = γ :=
    (Finset.mem_filter.mp hγ).2
  have hle : selectCount γ ≤ 1 := hvp.selectCount_le_one
  have h01 : selectCount γ = 0 ∨ selectCount γ = 1 := by omega
  rcases h01 with h0 | h1
  · exfalso
    have hcle : confCount γ ≤ H₀ := hvp.confCount_le
    have hext : ∃ x : DMark n B, ValidPath n B H₀ C₀ (γ ++ [x]) := by
      rcases lt_or_eq_of_le hcle with hlt | heq
      · have hcart0 : cartanCount γ = 0 := hvp.conf_cartan_excl hlt
        exact ⟨DMark.conf ⟨0, hB⟩, ValidPath.confStep hvp hlt hcart0 h0⟩
      · have hcartle : cartanCount γ + 1 ≤ C₀ :=
          hvp.cartan_le_of_noselect hC h0 heq
        rcases lt_or_eq_of_le hcartle with hltC | heqC
        · exact ⟨DMark.cartan, ValidPath.cartanStep hvp heq hltC h0⟩
        · exact ⟨DMark.select ⟨0, hn⟩, ValidPath.selectStep hvp heq heqC h0⟩
    obtain ⟨x, hx⟩ := hext
    have hmem' : γ ++ [x] ∈ descTree n B H₀ C₀ := descTree_mem.mpr hx
    have heq := hmax _ hmem' (List.prefix_append γ [x])
    have hlen := congrArg List.length heq
    simp at hlen
  · obtain ⟨u, t, rfl, hvu, hselu, hconfu, hcartu⟩ :=
      hvp.exists_select_split h1
    have hu := hvu.noSelect_full hselu hconfu hcartu
    refine ⟨leafConf u, t, ?_, ?_⟩
    · conv_lhs => rw [hu]
      rfl
    · rw [leafConf_length, hconfu]

/-! ## Fiber counting -/

/-- Length-`H₀` confluence words are functions `Fin H₀ → Fin B`
(via `List.ofFn_congr` for the cast). -/
def wordFinEquiv : {cb : List (Fin B) // cb.length = H₀} ≃ (Fin H₀ → Fin B) where
  toFun cb i := cb.val.get (Fin.cast cb.property.symm i)
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv cb := by
    apply Subtype.ext
    show List.ofFn (fun i : Fin H₀ => List.get cb.val (Fin.cast cb.property.symm i))
      = cb.val
    rw [← List.ofFn_congr cb.property (List.get cb.val)]
    exact List.ofFn_get cb.val
  right_inv f := by
    funext i
    show List.get (List.ofFn f) (Fin.cast List.length_ofFn.symm i) = f i
    rw [List.get_ofFn f]
    congr 1

/-- The `(x, t)`-fiber: leaves of `descTree` below `x` selecting terminal
tube `t`. -/
noncomputable def fiberFinset (hn : 0 < n) (x : List (DMark n B)) (t : Fin n) :
    Finset (List (DMark n B)) :=
  (treeLeaves (descTree n B H₀ C₀)).filter
    (fun γ => x <+: γ ∧ termTube hn γ = t)

/-- A fiber leaf is its own leaf word. -/
theorem leafWord_of_mem_fiber (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    {x : List (DMark n B)} {t : Fin n}
    {γ : List (DMark n B)} (hγ : γ ∈ fiberFinset (H₀ := H₀) (C₀ := C₀) hn x t) :
    γ = leafWord (C₀ := C₀) (leafConf γ) t := by
  have hmem : γ ∈ treeLeaves (descTree n B H₀ C₀) :=
    Finset.mem_of_mem_filter _ hγ
  have hterm : termTube hn γ = t := (Finset.mem_filter.mp hγ).2.2
  obtain ⟨cb, t', rfl, hlen⟩ := leaf_eq_leafWord hn hB hC hmem
  have htt : t' = t := (termTube_leafWord hn cb t').symm.trans hterm
  subst htt
  rw [leafConf_leafWord]

/-- Fiber leaves have confluence words of length `H₀`. -/
theorem leafConf_length_of_mem_fiber (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    {x : List (DMark n B)} {t : Fin n}
    {γ : List (DMark n B)} (hγ : γ ∈ fiberFinset (H₀ := H₀) (C₀ := C₀) hn x t) :
    (leafConf γ).length = H₀ := by
  have hmem : γ ∈ treeLeaves (descTree n B H₀ C₀) :=
    Finset.mem_of_mem_filter _ hγ
  obtain ⟨cb, t', rfl, hlen⟩ := leaf_eq_leafWord hn hB hC hmem
  rw [leafConf_leafWord]
  exact hlen

/-- Encode a fiber leaf by its confluence word as `Fin H₀ → Fin B`. -/
def fiberEncode (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    {x : List (DMark n B)} {t : Fin n} (γ : fiberFinset (H₀ := H₀) (C₀ := C₀) hn x t) :
    Fin H₀ → Fin B :=
  wordFinEquiv ⟨leafConf γ.val, leafConf_length_of_mem_fiber hn hB hC γ.property⟩

theorem fiberEncode_injective (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    {x : List (DMark n B)} {t : Fin n} :
    Function.Injective (fiberEncode (H₀ := H₀) hn hB hC (x := x) (t := t)) := by
  intro a b hab
  have hab' : wordFinEquiv ⟨leafConf a.val,
        leafConf_length_of_mem_fiber hn hB hC a.property⟩
      = wordFinEquiv ⟨leafConf b.val,
        leafConf_length_of_mem_fiber hn hB hC b.property⟩ := hab
  have hlc : leafConf a.val = leafConf b.val :=
    Subtype.ext_iff.mp (wordFinEquiv.injective hab')
  have ha := leafWord_of_mem_fiber hn hB hC a.property
  have hb := leafWord_of_mem_fiber hn hB hC b.property
  have hval : a.val = b.val := by rw [ha, hb, hlc]
  exact Subtype.ext hval

/-- Each `(x, t)`-fiber has at most `B ^ H₀` leaves. -/
theorem fiber_card_le (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀)
    (x : List (DMark n B)) (t : Fin n) :
    (fiberFinset (H₀ := H₀) (C₀ := C₀) hn x t).card ≤ B ^ H₀ := by
  have hcard := Fintype.card_le_of_injective
    (fiberEncode (H₀ := H₀) hn hB hC (x := x) (t := t))
    (fiberEncode_injective (H₀ := H₀) hn hB hC)
  rw [Fintype.card_coe, Fintype.card_fun] at hcard
  simpa using hcard

/-! ## Leaf words are valid maximal paths -/

/-- `confWord` words are valid, proved by induction on the reversed list so
that each step is a snoc-`confStep`. -/
theorem ValidPath.confWord_valid_aux : ∀ (l : List (Fin B)),
    l.length ≤ H₀ → ValidPath n B H₀ C₀ (confWord (n := n) l.reverse) := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [List.reverse_nil, confWord_nil]
      exact ValidPath.nil
  | cons b l' ih =>
      intro hle
      have hlt : l'.length < H₀ := by
        have h1 : (b :: l').length = l'.length + 1 := rfl
        omega
      have ih' := ih (by omega)
      rw [List.reverse_cons, confWord_append_singleton]
      refine ValidPath.confStep ih' ?_ ?_ ?_
      · rw [confCount_confWord, List.length_reverse]; exact hlt
      · rw [cartanCount_confWord]
      · rw [selectCount_confWord]

theorem ValidPath.confWord_valid (cb : List (Fin B)) (hle : cb.length ≤ H₀) :
    ValidPath n B H₀ C₀ (confWord (n := n) cb) := by
  have h := ValidPath.confWord_valid_aux (n := n) (B := B) (H₀ := H₀) (C₀ := C₀)
    cb.reverse (by rwa [List.length_reverse])
  rwa [List.reverse_reverse] at h

/-- Cartan steps on top of a full confluence word stay valid. -/
theorem ValidPath.confWord_cartan_aux (cb : List (Fin B)) (hcb : cb.length = H₀) :
    ∀ k, k < C₀ → ValidPath n B H₀ C₀
      (confWord (n := n) cb ++ List.replicate k (DMark.cartan : DMark n B)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa using ValidPath.confWord_valid cb hcb.le
  | succ k' ih =>
      intro hlt
      have ih' := ih (by omega)
      have hrep : List.replicate (k' + 1) (DMark.cartan : DMark n B)
          = List.replicate k' (DMark.cartan : DMark n B) ++ [DMark.cartan] := by
        rw [← List.replicate_one, ← List.replicate_add]
      rw [hrep, ← List.append_assoc]
      refine ValidPath.cartanStep ih' ?_ ?_ ?_
      · rw [confCount_append, confCount_confWord, confCount_replicate_cartan]
        omega
      · rw [cartanCount_append, cartanCount_confWord, cartanCount_replicate_cartan]
        omega
      · rw [selectCount_append, selectCount_confWord, selectCount_replicate_cartan]

/-- Every `leafWord cb t` (with `cb.length = H₀`) is a valid path. -/
theorem ValidPath.leafWord_valid (hC : 0 < C₀)
    (cb : List (Fin B)) (hcb : cb.length = H₀) (t : Fin n) :
    ValidPath n B H₀ C₀ (leafWord (C₀ := C₀) cb t) := by
  have hC1 : C₀ - 1 < C₀ := by omega
  have hcart := ValidPath.confWord_cartan_aux (n := n) cb hcb (C₀ - 1) hC1
  have hdef : leafWord (C₀ := C₀) cb t
      = (confWord (n := n) cb ++ List.replicate (C₀ - 1) (DMark.cartan : DMark n B))
        ++ [DMark.select (n := n) t] := rfl
  rw [hdef]
  refine ValidPath.selectStep (t := t) hcart ?_ ?_ ?_
  · rw [confCount_append, confCount_confWord, confCount_replicate_cartan]
    omega
  · rw [cartanCount_append, cartanCount_confWord, cartanCount_replicate_cartan]
    omega
  · rw [selectCount_append, selectCount_confWord, selectCount_replicate_cartan]

/-- Every `leafWord cb t` is a leaf of `descTree`: maximality follows from
the length bound `H₀ + C₀`, which `leafWord` attains. -/
theorem leafWord_mem_treeLeaves (hC : 0 < C₀)
    (cb : List (Fin B)) (hcb : cb.length = H₀) (t : Fin n) :
    leafWord (C₀ := C₀) cb t ∈ treeLeaves (descTree n B H₀ C₀) := by
  have hvp := ValidPath.leafWord_valid hC cb hcb t
  have hmem : leafWord (C₀ := C₀) cb t ∈ descTree n B H₀ C₀ :=
    descTree_mem.mpr hvp
  have hlen_eq : (leafWord (C₀ := C₀) cb t).length = H₀ + C₀ := by
    have hc1 : (confWord (n := n) cb).length = cb.length := by simp [confWord]
    have hdef : leafWord (C₀ := C₀) cb t
        = confWord (n := n) cb ++ List.replicate (C₀ - 1) (DMark.cartan : DMark n B)
          ++ [DMark.select (n := n) t] := rfl
    rw [hdef, List.length_append, List.length_append, hc1, List.length_replicate,
      hcb]
    simp only [List.length_cons, List.length_nil]
    omega
  unfold treeLeaves
  rw [Finset.mem_filter]
  refine ⟨hmem, ?_⟩
  intro l' hl' hpref
  have hvp' : ValidPath n B H₀ C₀ l' := descTree_mem.mp hl'
  have hle := hvp'.length_le
  obtain ⟨s, rfl⟩ := hpref
  have hs : s = [] := by
    have h1 : (leafWord (C₀ := C₀) cb t ++ s).length ≤ H₀ + C₀ := hle
    rw [List.length_append, hlen_eq] at h1
    have h2 : s.length = 0 := by omega
    exact List.length_eq_zero_iff.mp h2
  rw [hs, List.append_nil]

/-- The root `(⟦⟧, t)`-fiber has exactly `B ^ H₀` leaves. -/
theorem root_fiber_card (hn : 0 < n) (hB : 0 < B) (hC : 0 < C₀) (t : Fin n) :
    (fiberFinset (B := B) (H₀ := H₀) (C₀ := C₀) hn [] t).card = B ^ H₀ := by
  have hcard : (Finset.univ : Finset (Fin H₀ → Fin B)).card = B ^ H₀ := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  rw [← hcard, eq_comm]
  apply Finset.card_bij (fun f _ => leafWord (C₀ := C₀) (List.ofFn f) t)
  · intro f _
    unfold fiberFinset
    rw [Finset.mem_filter]
    refine ⟨leafWord_mem_treeLeaves hC (List.ofFn f) List.length_ofFn t, ?_, ?_⟩
    · exact List.nil_prefix
    · exact termTube_leafWord hn _ _
  · intro f₁ _ f₂ _ h12
    have hcc : List.ofFn f₁ = List.ofFn f₂ := by
      have h1 := congrArg leafConf h12
      rwa [leafConf_leafWord, leafConf_leafWord] at h1
    exact List.ofFn_injective hcc
  · intro γ hγ
    have hlen : (leafConf γ).length = H₀ :=
      leafConf_length_of_mem_fiber hn hB hC hγ
    have hγw := leafWord_of_mem_fiber hn hB hC hγ
    refine ⟨wordFinEquiv ⟨leafConf γ, hlen⟩, Finset.mem_univ _, ?_⟩
    have hof : List.ofFn (wordFinEquiv ⟨leafConf γ, hlen⟩) = leafConf γ :=
      congrArg Subtype.val (wordFinEquiv.symm_apply_apply ⟨leafConf γ, hlen⟩)
    show leafWord (C₀ := C₀) (List.ofFn (wordFinEquiv ⟨leafConf γ, hlen⟩)) t = γ
    rw [hof]
    exact hγw.symm

end FilteredDescent
