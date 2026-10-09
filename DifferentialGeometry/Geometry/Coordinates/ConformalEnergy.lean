import DifferentialGeometry.Analysis.InnerProductSpace.ConformalPair
import DifferentialGeometry.Analysis.FunctionalAnalysis.BilinearCoercivity
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

noncomputable section
open Set Filter Bundle Manifold InnerProductSpace
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem continuousOn_coordinateMetric (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) :
    ContinuousOn (pullbackMetricCoefficients g Φ) Φ.source :=
  (contDiffOn_pullback_metric_coefficients g Φ.open_source Φ.contMDiffOn_toFun).continuousOn

omit [FiniteDimensional ℝ E] in
private theorem coordinateMetric_pos (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {x : E} (hx : x ∈ Φ.source)
    {v : E} (hv : v ≠ 0) : 0 < pullbackMetricCoefficients g Φ x v v :=
  pullbackMetricCoefficients_pos g
    ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).injective hv

omit [FiniteDimensional ℝ E] in
private theorem coordinateMetric_posSemidef (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (x : E) :
    LinearMap.IsPosSemidef (pullbackMetricCoefficients g Φ x).toBilinForm :=
  pullbackMetricCoefficients_isPosSemidef g Φ x

private theorem exists_compact_coordinateMetric_bounds (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {K : Set E}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source) :
    ∃ m A : ℝ, 0 < m ∧ m ≤ A ∧ ∀ x ∈ K, ∀ v : E,
      m * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients g Φ x v v ∧ pullbackMetricCoefficients g Φ x v v ≤ A * ‖v‖ ^ 2 := by
  have hc := (continuousOn_coordinateMetric g Φ).mono hKs
  obtain ⟨m, hm, hml⟩ := exists_pos_mul_norm_sq_le_bilinear_of_isCompact hK (pullbackMetricCoefficients g Φ)
    hc (fun x hx v hv => coordinateMetric_pos g Φ (hKs hx) hv)
  have hcq : ContinuousOn (fun p : E × E => pullbackMetricCoefficients g Φ p.1 p.2 p.2)
      (K ×ˢ Metric.closedBall (0 : E) 1) :=
    ((hc.comp continuousOn_fst (fun _ hp => hp.1)).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : E) 1)).exists_bound_of_continuousOn hcq
  refine ⟨m, max m C, hm, le_max_left _ _, fun x hx v => ⟨hml x hx v, ?_⟩⟩
  by_cases hv : v = 0
  · simp [hv]
  let w := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  have hunit : w ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hw] using (le_refl (1 : ℝ))
  have hb : pullbackMetricCoefficients g Φ x w w ≤ max m C :=
    (le_abs_self _).trans ((hC (x, w) ⟨hx, hunit⟩).trans (le_max_right _ _))
  have hrestore : ‖v‖ • w = v := by
    simp only [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  calc
    pullbackMetricCoefficients g Φ x v v = ‖v‖ ^ 2 * pullbackMetricCoefficients g Φ x w w := by
      conv_lhs => rw [← hrestore]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    _ ≤ ‖v‖ ^ 2 * max m C := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = max m C * ‖v‖ ^ 2 := mul_comm _ _

private theorem exists_local_coordinateMetric_bounds (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {x₀ : E} (hx₀ : x₀ ∈ Φ.source) :
    ∃ r m A : ℝ, 0 < r ∧ 0 < m ∧ m ≤ A ∧ Metric.closedBall x₀ r ⊆ Φ.source ∧
      ∀ x ∈ Metric.closedBall x₀ r, ∀ v : E,
        m * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients g Φ x v v ∧ pullbackMetricCoefficients g Φ x v v ≤ A * ‖v‖ ^ 2 := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hx₀)
  have hs : Metric.closedBall x₀ (δ / 2) ⊆ Φ.source :=
    (Metric.closedBall_subset_ball (by linarith : δ / 2 < δ)).trans hsub
  obtain ⟨m, A, hm, hmA, hb⟩ := exists_compact_coordinateMetric_bounds g Φ (isCompact_closedBall _ _) hs
  exact ⟨δ / 2, m, A, half_pos hδ, hm, hmA, hs, hb⟩

omit [FiniteDimensional ℝ E] in
private theorem norm_sq_add_le_transverse_of_conformal
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : LinearMap.IsPosSemidef B.toBilinForm)
    {m A : ℝ} (hm : 0 < m) (hlo : ∀ v : E, m * ‖v‖ ^ 2 ≤ B v v)
    (hhi : ∀ v : E, B v v ≤ A * ‖v‖ ^ 2)
    {u v : E} (ho : B u v = 0) (he : B u u = B v v) (t : E) (a b : ℝ) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ (2 * A / m) * (‖u - a • t‖ ^ 2 + ‖v - b • t‖ ^ 2) := by
  have hb := hB.apply_self_le_sum_sub_smul_of_orthogonal ho he t a b
  change B u u ≤ B (u - a • t) (u - a • t) + B (v - b • t) (v - b • t) at hb
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).mpr
  nlinarith [hlo u, hlo v, hhi (u - a • t), hhi (v - b • t)]

omit [FiniteDimensional ℝ E] in
private theorem coordinateMetric_fderiv (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {U : ℂ → M} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) I U z) (hz : U z ∈ Φ.target) (v w : ℂ) :
    let X := Φ.symm ∘ U
    pullbackMetricCoefficients g Φ (X z) (fderiv ℝ X z v) (fderiv ℝ X z w) =
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v) (mfderiv 𝓘(ℝ, ℂ) I U z w) :=
  pullbackMetricCoefficients_fderiv_symm g Φ hU hz v w

theorem exists_transverse_coordinate_energy_bound (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {x₀ : E} (hx₀ : x₀ ∈ Φ.source)
    :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ Metric.closedBall x₀ r ⊆ Φ.source ∧
      ∀ (t : E) (l : E →L[ℝ] ℝ) (U : ℂ → M) (z : ℂ), MDifferentiableAt 𝓘(ℝ, ℂ) I U z → U z ∈ Φ.target →
        Φ.symm (U z) ∈ Metric.closedBall x₀ r →
        g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0 →
        g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
          g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) →
        let X := Φ.symm ∘ U
        let Y := fun q => X q - l (X q) • t
        ‖fderiv ℝ X z 1‖ ^ 2 + ‖fderiv ℝ X z Complex.I‖ ^ 2 ≤
          C * (‖fderiv ℝ Y z 1‖ ^ 2 + ‖fderiv ℝ Y z Complex.I‖ ^ 2) := by
  obtain ⟨r, m, A, hr, hm, hmA, hrs, hb⟩ := exists_local_coordinateMetric_bounds g Φ hx₀
  have hA : 0 < A := hm.trans_le hmA
  refine ⟨r, 2 * A / m, hr, by positivity, hrs, ?_⟩
  intro t l U z hU hz hball ho he
  let X := Φ.symm ∘ U
  let Y := fun q => X q - l (X q) • t
  have hX : DifferentiableAt ℝ X z := mdifferentiableAt_iff_differentiableAt.mp
    (((Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hz)).mdifferentiableAt
      (by simp)).comp z hU)
  have hY : fderiv ℝ Y z = fderiv ℝ X z - (l.comp (fderiv ℝ X z)).smulRight t := by
    have hl := l.hasFDerivAt.comp z hX.hasFDerivAt
    exact (hX.hasFDerivAt.sub (hl.smul_const t)).fderiv
  have ho' : pullbackMetricCoefficients g Φ (X z) (fderiv ℝ X z 1) (fderiv ℝ X z Complex.I) = 0 := by
    rw [coordinateMetric_fderiv g Φ hU hz]
    exact ho
  have he' : pullbackMetricCoefficients g Φ (X z) (fderiv ℝ X z 1) (fderiv ℝ X z 1) =
      pullbackMetricCoefficients g Φ (X z) (fderiv ℝ X z Complex.I) (fderiv ℝ X z Complex.I) := by
    rw [coordinateMetric_fderiv g Φ hU hz, coordinateMetric_fderiv g Φ hU hz]
    exact he
  have hbound := norm_sq_add_le_transverse_of_conformal (pullbackMetricCoefficients g Φ (X z))
    (coordinateMetric_posSemidef g Φ (X z)) hm
    (fun v => (hb (X z) hball v).1) (fun v => (hb (X z) hball v).2) ho' he' t
    (l (fderiv ℝ X z 1)) (l (fderiv ℝ X z Complex.I))
  change ‖fderiv ℝ X z 1‖ ^ 2 + ‖fderiv ℝ X z Complex.I‖ ^ 2 ≤
    (2 * A / m) * (‖fderiv ℝ Y z 1‖ ^ 2 + ‖fderiv ℝ Y z Complex.I‖ ^ 2)
  rw [hY]
  exact hbound

end DifferentialGeometry.Geometry
