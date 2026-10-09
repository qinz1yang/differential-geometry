/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_positive_lt_of_point_finite
    {ι X : Type*} (C : ι → Set X) (hfinite : ∀ x, {i | x ∈ C i}.Finite)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : X → ℝ, (∀ x, 0 < ε x) ∧ ∀ i x, x ∈ C i → ε x < δ i := by
  classical
  have hfinset (s : Finset ι) :
      ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e < δ i := by
    induction s using Finset.induction with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨e, he, hes⟩ := ih
        have hmin : 0 < min e (δ a) := lt_min he (hδ a)
        refine ⟨min e (δ a) / 2, div_pos hmin (by norm_num), ?_⟩
        intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with hia | hi
        · subst i
          exact (half_lt_self hmin).trans_le (min_le_right e (δ a))
        · exact (half_lt_self hmin).trans
            ((min_le_left e (δ a)).trans_lt (hes i hi))
  have hx (x : X) :
      ∃ e : ℝ, 0 < e ∧ ∀ i, x ∈ C i → e < δ i := by
    obtain ⟨e, he, hes⟩ := hfinset (hfinite x).toFinset
    exact ⟨e, he, fun i hi => hes i ((hfinite x).mem_toFinset.mpr hi)⟩
  choose ε hε hεδ using hx
  exact ⟨ε, hε, fun i x hxC => hεδ x i hxC⟩

open Classical in
theorem LocallyFinitePLPieceIn.exists_positive_vertex_scale
    {n : ℕ} {X E : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y)
    (δ : T.complex.faces → ℝ) (hδ : ∀ s, 0 < δ s) :
    ∃ ε : T.complex.vertices → ℝ,
      (∀ v, 0 < ε v) ∧
      ∀ (s : T.complex.faces) (v : T.complex.vertices),
        (v : E) ∈ (s : Finset E) → ε v < δ s := by
  let C : T.complex.faces → Set T.complex.space := fun s =>
    (Subtype.val : T.complex.space → E) ⁻¹'
      convexHull ℝ ((s : Finset E) : Set E)
  obtain ⟨e, he, heδ⟩ :=
    exists_positive_lt_of_point_finite C T.locallyFinite.point_finite δ hδ
  let vertexInSpace : T.complex.vertices → T.complex.space := fun v =>
    ⟨v, T.complex.vertices_subset_space v.2⟩
  refine ⟨fun v => e (vertexInSpace v), fun v => he (vertexInSpace v), ?_⟩
  intro s v hvs
  apply heδ s (vertexInSpace v)
  exact subset_convexHull ℝ (s : Set E) hvs

open Classical in
theorem LocallyFinitePLPieceIn.exists_positive_face_error_bound
    {n : ℕ} {X E : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) (φ : X → ℝ)
    (hφ : ContinuousOn φ Y) (hφpos : ∀ x ∈ Y, 0 < φ x) :
    ∃ δ : T.complex.faces → ℝ,
      (∀ s, 0 < δ s) ∧
      ∀ (s : T.complex.faces) (x : E),
        x ∈ convexHull ℝ ((s : Finset E) : Set E) → δ s ≤ φ (T.map x) := by
  have hs (s : T.complex.faces) :
      ∃ d : ℝ, 0 < d ∧ ∀ x : E,
        x ∈ convexHull ℝ ((s : Finset E) : Set E) → d ≤ φ (T.map x) := by
    have hsub : convexHull ℝ ((s : Finset E) : Set E) ⊆ T.complex.space :=
      T.complex.convexHull_subset_space s.2
    have hcont : ContinuousOn (φ ∘ T.map)
        (convexHull ℝ ((s : Finset E) : Set E)) :=
      hφ.comp (T.continuousOn.mono hsub) fun x hx => T.bijOn.mapsTo (hsub hx)
    obtain ⟨d, hd, hdle⟩ :=
      (s.1.finite_toSet.isCompact_convexHull ℝ).exists_forall_le' hcont
        (fun x hx => hφpos (T.map x) (T.bijOn.mapsTo (hsub hx)))
    exact ⟨d, hd, hdle⟩
  choose δ hδ hδle using hs
  exact ⟨δ, hδ, hδle⟩

end DifferentialGeometry.Topology.PiecewiseLinear
