import DifferentialGeometry.Topology.Embedding.CompactFrontier
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Handle.BoundaryEmbedding
import DifferentialGeometry.Topology.Handle.DiffeomorphExtension

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private local instance (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨by simp⟩

theorem exists_partialDiffeomorph_extension_closedCell_sphere (m : ℕ)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
      (Φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
        (EuclideanSpace ℝ (Fin (m + 1)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞),
      Φ.source = Set.univ ∧ Φ.target = {p}ᶜ ∧
      ∀ x : ClosedCell (m + 1), Φ x.val = u x := by
  obtain ⟨p, hp⟩ := exists_stereographic_source_superset_range_closedCell m (m + 1)
    (by simp) hu
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1
  have hchart : chartAt E (-p) = stereographic' (m + 1) p := by
    change stereographic' (m + 1) (-(-p)) = stereographic' (m + 1) p
    rw [neg_neg]
  let e : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) S E ∞ :=
    { toPartialEquiv := (stereographic' (m + 1) p).toPartialEquiv
      open_source := (stereographic' (m + 1) p).open_source
      open_target := (stereographic' (m + 1) p).open_target
      contMDiffOn_toFun := by rw [← hchart]; exact contMDiffOn_chart
      contMDiffOn_invFun := by rw [← hchart]; exact contMDiffOn_chart_symm }
  have he : IsLocalDiffeomorphOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Set.range u) := by
    intro y
    exact PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e
      (hp y.property)
  have himm := hu.isImmersion.isLocalDiffeomorphOn_comp he
  have hinj : Function.Injective (e ∘ u) := by
    intro x y hxy
    apply hu.isEmbedding.injective
    exact e.injOn (hp (Set.mem_range_self x)) (hp (Set.mem_range_self y)) hxy
  have hv : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (e ∘ u) :=
    ⟨himm, (himm.contMDiff.continuous.isClosedEmbedding hinj).isEmbedding⟩
  obtain ⟨D, hD⟩ := exists_diffeomorph_extension_closedCell m hv
  let Φ := D.toPartialDiffeomorph.trans e.symm
  refine ⟨p, Φ, ?_, ?_, ?_⟩
  · change Set.univ ∩ D ⁻¹' (stereographic' (m + 1) p).target = Set.univ
    simp
  · change (stereographic' (m + 1) p).source ∩
      (stereographic' (m + 1) p) ⁻¹' Set.univ = {p}ᶜ
    simp
  · intro x
    change e.symm (D x.val) = u x
    rw [hD x]
    exact e.left_inv (hp (Set.mem_range_self x))

theorem frontier_range_closedCell_sphere (m : ℕ)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    frontier (range u) = range (u ∘ cellBoundaryInclusion (m + 1)) := by
  obtain ⟨p, Φ, hs, _, hΦ⟩ := exists_partialDiffeomorph_extension_closedCell_sphere m hu
  have hΦu : (Φ : EuclideanSpace ℝ (Fin (m + 1)) → _) ∘ Subtype.val = u := funext hΦ
  have hball : Φ '' closedBall 0 1 = range u := by
    rw [← range_closedCell (m + 1), ← range_comp, hΦu]
  have hboundary : Φ '' sphere 0 1 = range (u ∘ cellBoundaryInclusion (m + 1)) := by
    rw [← range_cellBoundary (m + 1), ← range_comp]
    congr 1
    exact funext (fun x => hΦ (cellBoundaryInclusion (m + 1) x))
  have hopen : _root_.Topology.IsOpenEmbedding (Φ : EuclideanSpace ℝ (Fin (m + 1)) → _) :=
    Φ.toOpenPartialHomeomorph.isOpenEmbedding hs
  rw [← hball, ← Embedding.image_frontier_of_isOpenEmbedding_of_isCompact hopen
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
    frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact hboundary

theorem closure_interior_range_closedCell_sphere (m : ℕ)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    closure (interior (range u)) = range u := by
  obtain ⟨p, Φ, hs, _, hΦ⟩ := exists_partialDiffeomorph_extension_closedCell_sphere m hu
  have hΦu : (Φ : EuclideanSpace ℝ (Fin (m + 1)) → _) ∘ Subtype.val = u := funext hΦ
  have hball : Φ '' closedBall 0 1 = range u := by
    rw [← range_closedCell (m + 1), ← range_comp, hΦu]
  have hopen : _root_.Topology.IsOpenEmbedding (Φ : EuclideanSpace ℝ (Fin (m + 1)) → _) :=
    Φ.toOpenPartialHomeomorph.isOpenEmbedding hs
  have hclosed : IsClosed (range u) := (isCompact_range hu.isEmbedding.continuous).isClosed
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  rw [← hball, ← Embedding.image_interior_of_isOpenEmbedding hopen,
    interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0), ← closure_ball _ (one_ne_zero : (1 : ℝ) ≠ 0)]
  exact image_closure_subset_closure_image hopen.continuous


theorem isConnected_interior_range_closedCell_sphere (m : ℕ)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    IsConnected (interior (range u)) := by
  obtain ⟨p, Φ, hs, _, hΦ⟩ := exists_partialDiffeomorph_extension_closedCell_sphere m hu
  have hΦu : (Φ : EuclideanSpace ℝ (Fin (m + 1)) → _) ∘ Subtype.val = u := funext hΦ
  have hball : Φ '' closedBall 0 1 = range u := by
    rw [← range_closedCell (m + 1), ← range_comp, hΦu]
  have hopen : _root_.Topology.IsOpenEmbedding (Φ : EuclideanSpace ℝ (Fin (m + 1)) → _) :=
    Φ.toOpenPartialHomeomorph.isOpenEmbedding hs
  rw [← hball, ← Embedding.image_interior_of_isOpenEmbedding hopen,
    interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).isConnected
    ⟨0, mem_ball_self zero_lt_one⟩ |>.image _ hopen.continuous.continuousOn

theorem isSmoothEmbedding_scaled_closedCell_sphere_chart (m : ℕ)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hs : closedBall 0 R ⊆ φ.source) :
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (fun x : ClosedCell (m + 1) => φ (R • x.val)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + 1))) = (m + 1) + 1) :=
    ⟨by simp⟩
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
  have hb := (closedCellInclusion_isSmoothEmbedding m).continuousLinearEquiv_comp L
  have hball (x : ClosedCell (m + 1)) : R • x.val ∈ closedBall (0 : E) R := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left x.property hR.le).trans_eq (mul_one R)
  have hi : _root_.Manifold.IsImmersion (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (fun x : ClosedCell (m + 1) => φ (R • x.val)) := by
    apply hb.isImmersion.isLocalDiffeomorphOn_comp
    intro y
    obtain ⟨x, hx⟩ := y.property
    exact φ.isLocalDiffeomorphAt _ _ _ (hx ▸ hs (hball x))
  refine ⟨hi, (hi.contMDiff.continuous.isClosedEmbedding ?_).isEmbedding⟩
  intro x y hxy
  apply hb.isEmbedding.injective
  exact φ.injOn (hs (hball x)) (hs (hball y)) hxy

end DifferentialGeometry.Topology.Handle
