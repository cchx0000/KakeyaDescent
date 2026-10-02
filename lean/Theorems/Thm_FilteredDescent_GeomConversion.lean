import Definitions.Def_FilteredDescent_Analytic
import Theorems.Thm_FilteredDescent_DescentBounds

/-!
# Hereditary geometric conversion (TODO_GUIDANCE item 6)

Converts the dimension-specific external geometric input (`GeomInput d`,
paper (53)/(177)/(81)) to the per-subtree `geom_pair` needed by the
well-founded descent.

The descent consumes, at each re-rooted subtree `x ∈ T`:
```lean
geom_pair x : SubpowerLE
  (fun δ => ∑ t t', if t ≠ t' then termLoad (reroot T x) ... t δ
                                  * termLoad (reroot T x) ... t' δ else 0)
  (fun δ => Bpred δ * totalLoad (reroot T x) ... δ)
```

The external input gives the pair bound for the *tube family*:
```lean
GeomInput d : SubpowerLE
  (fun δ => ∑ t t', if t ≠ t' then shadeVol t δ * shadeVol t' δ else 0)
  (fun δ => unionVol δ * ∑ t, shadeVol t δ)
```

The conversion is *hereditary*: the pair bound must hold not just at the
root, but at every re-rooted subtree. This requires the tree's terminal
loads to be *source-compatible* with the tube shading — i.e. the subtree
at `x` sees the same geometric configuration, restricted to the tubes
that reach `x`.

## Current status (honest)

The root conversion (`x = []`) is proved below: when the tree's root
terminal load equals the tube shading (`termLoad_root_eq_shadeVol`), the
`GeomInput` directly gives `geom_pair []`.

The full per-subtree hereditary conversion needs TODO_GUIDANCE item 7
(packet/source provenance): to know that the re-rooted subtree at `x`
inherits the geometric configuration from the source ledger, not just
an arbitrary load function. We state the hereditary theorem with the
compatibility hypothesis explicit and defer the proof.
-/

namespace FilteredDescent

/-- Root geometric conversion: `GeomInput d` gives `geom_pair` at `x = []`.

When the tree's root terminal load coincides with the tube shading
(`hcompat`), the external pair bound *is* the required `geom_pair` at
the root. This is the base case of the hereditary conversion. -/
theorem geom_pair_root_of_geomInput {α : Type} [DecidableEq α] {n d : ℕ}
    {S : ShadedTubes n}
    (hgeom : GeomInput d S.shadeVol S.unionVol)
    {T : Finset (List α)} {termTube : List α → Fin n}
    {load : List α → ℝ → ℝ} {Bpred : ℝ → ℝ}
    (hcompat : ∀ δ : ℝ, ∀ t : Fin n,
      termLoad T termTube load t δ = S.shadeVol t δ)
    (hBpred_eq : Bpred = S.unionVol)
    (htotal_eq : ∀ δ : ℝ, totalLoad T load δ = ∑ t, S.shadeVol t δ) :
    SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T []) (fun s => termTube ([] ++ s))
          (fun s δ => load ([] ++ s) δ) t δ
          * termLoad (reroot T []) (fun s => termTube ([] ++ s))
          (fun s δ => load ([] ++ s) δ) t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad (reroot T [])
        (fun s δ => load ([] ++ s) δ) δ) := by
  -- reroot at [] is the identity
  have hrw : reroot T [] = T := reroot_empty T
  rw [hrw]
  -- [] ++ s = s
  -- [] ++ s = s, so the re-rooted functions equal the originals
  have hfun_eq : ∀ s : List α, termTube ([] ++ s) = termTube s := fun s => by rw [List.nil_append]
  have hpair : (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad T (fun s => termTube ([] ++ s))
          (fun s δ => load ([] ++ s) δ) t δ
          * termLoad T (fun s => termTube ([] ++ s))
          (fun s δ => load ([] ++ s) δ) t' δ
        else 0)
      = (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0) := by
    funext δ
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro t' _
    by_cases h : t ≠ t'
    · rw [if_pos h, if_pos h]
      -- termLoad with ([] ++ s) functions equals termLoad with original functions
      have e : ∀ u : Fin n, termLoad T (fun s => termTube ([] ++ s))
          (fun s δ => load ([] ++ s) δ) u δ = termLoad T termTube load u δ := by
        intro u
        have h1 : (fun s : List α => termTube ([] ++ s)) = termTube := by
          funext s
          rw [List.nil_append]
        have h2 : (fun s : List α => fun δ : ℝ => load ([] ++ s) δ) = load := by
          funext s δ
          rw [List.nil_append]
        rw [h1, h2]
      rw [e t, e t', hcompat δ t, hcompat δ t']
    · rw [if_neg h, if_neg h]
  have htot : (fun δ => Bpred δ * totalLoad T (fun s δ => load ([] ++ s) δ) δ)
      = (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    funext δ
    rw [hBpred_eq]
    congr 1
    -- totalLoad T (fun s δ => load ([] ++ s) δ) δ = totalLoad T load δ
    -- because [] ++ s = s
    have : totalLoad T (fun s δ => load ([] ++ s) δ) δ = totalLoad T load δ := by
      unfold totalLoad
      apply Finset.sum_congr rfl
      intro γ _
      show load ([] ++ γ) δ = load γ δ
      rw [List.nil_append]
    rw [this, htotal_eq]
  rw [hpair, htot]
  -- Now extract the SubpowerLE from GeomInput
  cases hgeom with
  | planar h => exact h
  | sticky h => exact h
  | marked4D h => exact h

/-- Hereditary geometric conversion (TODO_GUIDANCE item 6, full version).

Given:
- the dimension-specific external input `GeomInput d`,
- source-compatibility of the subtree data at `x` (the re-rooted
  terminal loads coincide with the tube shading, and the predecessor
  bound matches the union volume),

produces `geom_pair` at the re-rooted subtree `x`.

The compatibility hypothesis `hcompat_sub` is what TODO_GUIDANCE item 7
(packet/source provenance) must discharge: the tree at `x` must be the
deterministic image of the source ledger, so the geometric configuration
is inherited, not arbitrary.

We state the theorem with the compatibility explicit; the proof is
deferred pending item 7. -/
theorem geom_pair_of_geomInput {α : Type} [DecidableEq α] {n d : ℕ}
    {S : ShadedTubes n}
    (hgeom : GeomInput d S.shadeVol S.unionVol)
    {T : Finset (List α)} {termTube : List α → Fin n}
    {load : List α → ℝ → ℝ} {Bpred : ℝ → ℝ}
    (x : List α) (hx : x ∈ T)
    (hcompat_sub : ∀ δ : ℝ, ∀ t : Fin n,
      termLoad (reroot T x) (fun s => termTube (x ++ s))
        (fun s δ => load (x ++ s) δ) t δ = S.shadeVol t δ)
    (hBpred_eq : Bpred = S.unionVol)
    (htotal_sub : ∀ δ : ℝ, totalLoad (reroot T x)
      (fun s δ => load (x ++ s) δ) δ = ∑ t, S.shadeVol t δ) :
    SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ
          * termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad (reroot T x)
        (fun s δ => load (x ++ s) δ) δ) := by
  -- The proof is identical to the root case, using hcompat_sub instead
  -- of the root compatibility. The substantive work (discharging
  -- hcompat_sub from the source ledger) is item 7.
  have hpair : (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ
          * termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t' δ
        else 0)
      = (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0) := by
    funext δ
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro t' _
    by_cases h : t ≠ t'
    · rw [if_pos h, if_pos h, hcompat_sub δ t, hcompat_sub δ t']
    · rw [if_neg h, if_neg h]
  have htot : (fun δ => Bpred δ * totalLoad (reroot T x)
        (fun s δ => load (x ++ s) δ) δ)
      = (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    funext δ
    rw [hBpred_eq, htotal_sub]
  rw [hpair, htot]
  cases hgeom with
  | planar h => exact h
  | sticky h => exact h
  | marked4D h => exact h

end FilteredDescent
