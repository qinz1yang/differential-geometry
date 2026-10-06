/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCutBoundary

set_option autoImplicit false

open Set Topology DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- **P3, topological form.**  `K` a closed combinatorial 3-manifold triangulating `X` by
`h : K.space ≃ₜ X`; `L ⊆ K` a combinatorial 2-manifold complex whose space is the image of
`h ⁻¹' Y` (`Y` = union of the bicollared tori).  `W ⊆ X` closed with `W \ Y ⊆ interior W`
(`hfront`), `Y ∩ W ⊆ closure (W \ Y)` and `Y ∩ W ⊆ closure Wᶜ` (these follow from
`hside : σ p ∈ W ↔ 0 ≤ p.2`, see `sideHyps_of_bicollar_LTP3`).
Conclusion: the image `R` of `h ⁻¹' W` is the space of a finite combinatorial 3-manifold
with boundary exactly the image of `h ⁻¹' (Y ∩ W)`, orientable if `K` is, and every
component of `L` meeting `R` is a boundary component. -/
theorem exists_cut_manifold_of_side_LTP3 {X : Type*} [TopologicalSpace X]
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (h : K.space ≃ₜ X) (hK : IsCombinatorialManifold 3 K) (hL : IsCombinatorialManifold 2 L)
    {Y W : Set X} (hLY : L.space = ((↑) : K.space → E) '' (h ⁻¹' Y))
    (hWc : IsClosed W) (hfront : W \ Y ⊆ interior W)
    (hdense : Y ∩ W ⊆ closure (W \ Y)) (hone : Y ∩ W ⊆ closure Wᶜ) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hfin : R.faces.Finite),
      letI := hfin.to_subtype
      R.space = ((↑) : K.space → E) '' (h ⁻¹' W) ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = ((↑) : K.space → E) '' (h ⁻¹' (Y ∩ W)) ∧
      (IsOrientable 3 K → IsOrientable 3 R) ∧
      ∀ x ∈ R.space ∩ L.space, ∃ c : ConnectedComponents (boundaryComplex 3 R).space,
        (connectedComponentComplex (boundaryComplex 3 R) c).space =
          connectedComponentIn L.space x := by
  set V : K.space → E := ((↑) : K.space → E) with hV
  have hVe : Topology.IsClosedEmbedding V := (isPolyhedron_space K).isClosed.isClosedEmbedding_subtypeVal
  have hKw := hK.isCombinatorialManifoldWithBoundary
  have hB0 : (boundaryComplex 3 K).space = ∅ := by
    change (⋃ t ∈ (boundaryComplex 3 K).faces, convexHull ℝ (t : Set E)) = ∅
    rw [hK.boundaryComplex_faces_eq_empty K]; simp
  have hLK : L.space ⊆ K.space := by
    rw [hLY]; rintro _ ⟨k, -, rfl⟩; exact k.2
  have hB : Disjoint L.space (boundaryComplex 3 K).space := by rw [hB0]; exact disjoint_empty _
  set W' : Set E := V '' (h ⁻¹' W) with hW'
  have hWK : W' ⊆ K.space := by rintro _ ⟨k, -, rfl⟩; exact k.2
  have hWc' : IsClosed W' := hVe.isClosedMap _ (hWc.preimage h.continuous)
  have hLset : ∀ k : K.space, V k ∈ L.space ↔ h k ∈ Y := fun k => by
    rw [hLY]; exact ⟨fun ⟨k', hk', e⟩ => (Subtype.ext e : k' = k) ▸ hk', fun hk => ⟨k, hk, rfl⟩⟩
  have hWset : ∀ k : K.space, V k ∈ W' ↔ h k ∈ W := fun k =>
    ⟨fun ⟨k', hk', e⟩ => (Subtype.ext e : k' = k) ▸ hk', fun hk => ⟨k, hk, rfl⟩⟩
  have hopen : ∀ x ∈ W' \ L.space, W' ∈ 𝓝[K.space] x := by
    rintro _ ⟨⟨k, hk, rfl⟩, hxL⟩
    have hkY : h k ∉ Y := fun hy => hxL ((hLset k).mpr hy)
    have hn : W ∈ 𝓝 (h k) := mem_interior_iff_mem_nhds.mp (hfront ⟨hk, hkY⟩)
    have hn' : h ⁻¹' W ∈ 𝓝 k := h.continuous.continuousAt hn
    have := Filter.image_mem_map (m := V) hn'
    rwa [hVe.isEmbedding.map_nhds_eq, Subtype.range_coe] at this
  have hcl : ∀ (S : Set X) (k : K.space), h k ∈ closure S → V k ∈ closure (V '' (h ⁻¹' S)) := by
    intro S k hk
    have : k ∈ closure (h ⁻¹' S) := by rw [← h.preimage_closure]; exact hk
    exact image_closure_subset_closure_image hVe.continuous ⟨k, this, rfl⟩
  have hdense' : ∀ p ∈ L.space ∩ W', p ∈ closure (W' \ L.space) := by
    rintro _ ⟨hpL, ⟨k, hk, rfl⟩⟩
    have := hcl (W \ Y) k (hdense ⟨(hLset k).mp hpL, hk⟩)
    refine closure_mono ?_ this
    rintro _ ⟨k', hk', rfl⟩
    exact ⟨⟨k', hk'.1, rfl⟩, fun hl => hk'.2 ((hLset k').mp hl)⟩
  have hone' : ∀ p ∈ L.space ∩ W', p ∈ closure (K.space \ W') := by
    rintro _ ⟨hpL, ⟨k, hk, rfl⟩⟩
    have := hcl Wᶜ k (hone ⟨(hLset k).mp hpL, hk⟩)
    refine closure_mono ?_ this
    rintro _ ⟨k', hk', rfl⟩
    exact ⟨k'.2, fun hw => hk' ((hWset k').mp hw)⟩
  obtain ⟨R, hfin, hRW, hman, hbd, horient⟩ :=
    exists_manifold_of_oneSided_LTP3 hKw hL hLK hB hWK hWc' hopen hdense' hone'
  let _ : Finite R.faces := hfin.to_subtype
  refine ⟨R, hfin, hRW, hman, ?_, horient, ?_⟩
  · rw [hbd, hB0, inter_empty, union_empty]
    ext x
    constructor
    · rintro ⟨hxL, ⟨k, hk, rfl⟩⟩
      exact ⟨k, ⟨(hLset k).mp hxL, hk⟩, rfl⟩
    · rintro ⟨k, ⟨hy, hw⟩, rfl⟩
      exact ⟨(hLset k).mpr hy, k, hw, rfl⟩
  · intro x hx
    exact (exists_boundary_component_of_oneSided_LTP3 hKw hL hLK hB
      (hRW ▸ hWK) (hRW ▸ hopen) (hRW ▸ hdense') (hRW ▸ hone') hx.2 hx.1).2

/-- The side hypotheses of `exists_cut_manifold_of_side_LTP3` follow from the bicollar
conditions of LT-P1 (`σ` with source `{-1 < s < 1}`, `hside`, `hfront`), with
`Y = range (fun x => σ (x, 0))`. -/
theorem sideHyps_of_bicollar_LTP3 {X : Type*} [TopologicalSpace X] {ι : Type*}
    {T : Type*} [TopologicalSpace T] [TopologicalSpace ι]
    (σ : OpenPartialHomeomorph ((ι × T) × ℝ) X) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (W : Set X) (hside : ∀ p ∈ σ.source, σ p ∈ W ↔ 0 ≤ p.2) :
    range (fun x : ι × T => σ (x, 0)) ∩ W ⊆ closure (W \ range (fun x : ι × T => σ (x, 0))) ∧
    range (fun x : ι × T => σ (x, 0)) ∩ W ⊆ closure Wᶜ := by
  have hsrc : ∀ x : ι × T, ∀ s : ℝ, -1 < s → s < 1 → (x, s) ∈ σ.source := fun x s h1 h2 => by
    rw [hσ]; exact ⟨h1, h2⟩
  have hnot : ∀ x x' : ι × T, ∀ s : ℝ, -1 < s → s < 1 → s ≠ 0 → σ (x, s) ≠ σ (x', 0) := by
    intro x x' s h1 h2 h0 he
    have := σ.injOn (hsrc x s h1 h2) (hsrc x' 0 (by norm_num) (by norm_num)) he
    exact h0 (Prod.ext_iff.mp this).2
  have hcont : ∀ x : ι × T, Filter.Tendsto (fun s : ℝ => σ (x, s)) (𝓝 0) (𝓝 (σ (x, 0))) := by
    intro x
    have h1 := (σ.continuousAt (hsrc x 0 (by norm_num) (by norm_num)) |>.tendsto)
    exact h1.comp (Continuous.tendsto (by fun_prop : Continuous fun s : ℝ => (x, s)) 0)
  constructor
  · rintro _ ⟨⟨x, rfl⟩, -⟩
    refine mem_closure_of_tendsto ((hcont x).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact ⟨(hside _ (hsrc x s (by linarith [hs.1]) hs.2)).mpr hs.1.le,
      fun ⟨x', hx'⟩ => hnot x x' s (by linarith [hs.1]) hs.2 hs.1.ne' hx'.symm⟩
  · rintro _ ⟨⟨x, rfl⟩, -⟩
    refine mem_closure_of_tendsto ((hcont x).mono_left (nhdsWithin_le_nhds (s := Iio (0:ℝ)))) ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with s hs
    exact fun hw => absurd ((hside _ (hsrc x s hs.1 (by linarith [hs.2]))).mp hw) (not_le.mpr hs.2)

end GC.LongTime.CuspP1
