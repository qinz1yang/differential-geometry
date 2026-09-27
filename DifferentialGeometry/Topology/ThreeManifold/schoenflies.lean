import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Handle.Embedding

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.ThreeManifold

noncomputable section

private def roundSphereDiffeomorph (c : EuclideanSpace ℝ (Fin 3))
    (r : ℝ) (hr : r ≠ 0) :
    EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := c + r • x
  invFun y := r⁻¹ • (y - c)
  left_inv x := by simp [smul_smul, hr]
  right_inv y := by simp [smul_smul, hr]
  contMDiff_toFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x => c + r • x)
    apply ContDiff.contMDiff
    fun_prop
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y => r⁻¹ • (y - c))
    apply ContDiff.contMDiff
    fun_prop

theorem exists_diffeomorph_image_sphere (c : EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3),
      Φ '' Metric.sphere 0 1 = Metric.sphere c r := by
  refine ⟨roundSphereDiffeomorph c r hr.ne', ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ = 1 := by simpa using hx
    change dist (c + r • x) c = r
    simp [dist_eq_norm, norm_smul, hx', Real.norm_eq_abs, abs_of_pos hr]
  · intro hy
    have hy' : ‖y - c‖ = r := by simpa [dist_eq_norm] using hy
    refine ⟨r⁻¹ • (y - c), ?_, ?_⟩
    · change dist (r⁻¹ • (y - c)) 0 = 1
      simp [dist_eq_norm, norm_smul, hy', Real.norm_eq_abs, abs_of_pos hr, hr.ne']
    · change c + r • (r⁻¹ • (y - c)) = y
      simp [smul_smul, hr.ne']

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_smooth_ball_filling_round_sphere (c : EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) :
    ∃ b : ClosedCell 3 → EuclideanSpace ℝ (Fin 3),
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b ∧
        Set.range (b ∘ cellBoundaryInclusion 3) = Metric.sphere c r := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_image_sphere c hr
  refine ⟨Φ ∘ Subtype.val,
    (Handle.closedCellInclusion_isSmoothEmbedding 2).diffeomorph_comp Φ, ?_⟩
  rw [← hΦ]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, by simpa using x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, by simpa using hx⟩, rfl⟩

end

end DifferentialGeometry.Topology.ThreeManifold
