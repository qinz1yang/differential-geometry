import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature
import DifferentialGeometry.Geometry.Curvature.PositiveStability
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Curvature.SectionalOperator
import DifferentialGeometry.Geometry.Curvature.HamiltonIveyRegion
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_normalizedDatum_insertedMetric_core_curvature_pos (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, 2 ≤ k →
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
          (x : insertionBall δ⁻¹), ‖(x : E3)‖ ≤ conformalRadius (-A) →
          let out : SmoothRiemannianMetric (𝓡 3) (insertionBall δ⁻¹) :=
            insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
          (∀ u v : TangentSpace (𝓡 3) x,
            out.inner x u u * out.inner x v v - out.inner x u v ^ 2 ≠ 0 →
              0 < sectionalCurvature out x u v) ∧ 0 < metricScalarAt out x := by
  have hr : conformalRadius (-A) < transitionEnd := by
    simpa only [conformalRadius_zero] using strictMono_conformalRadius (neg_neg_of_pos hA)
  have hK : IsCompact {x : E3 | ‖x‖ ≤ conformalRadius (-A)} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : E3) (conformalRadius (-A))
  have hpos : ∀ x ∈ {x : E3 | ‖x‖ ≤ conformalRadius (-A)},
      ∀ u v : TangentSpace (𝓡 3) x,
      metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2 ≠ 0 →
        0 < sectionalCurvature metric x u v := by
    intro x hx
    exact sectionalCurvature_pos (lt_of_le_of_lt hx hr)
  obtain ⟨ε, hε, hstable⟩ := exists_pos_sectionalCurvature_of_small_metricDerivENormSupOn metric hK hpos
  obtain ⟨δ₀, hδ₀, hδ₀half, hmod⟩ :=
    exists_normalizedDatum_insertedMetric_ball_error_lt A hA 0 (by norm_num) 2 ε hε
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, _, hb⟩ := hmod δ hδ hδle
  refine ⟨hAB, ?_⟩
  intro k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d x hx
  dsimp only
  have hsmall := hb k hk g x₀ d
  have hs := hstable (insertionBall δ⁻¹)
    (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric) ?_ x hx
  · exact ⟨hs, metricScalarAt_pos_of_sectionalCurvature_pos _ x (by simp) hs⟩
  · apply (metricDerivENormSupOn_mono (K := {y : insertionBall δ⁻¹ | ‖(y : E3)‖ ≤ conformalRadius (-A)})
      (fun y hy => (show ‖(y : E3)‖ ≤ conformalRadius (-A) from hy).trans (by simpa using hr.le))
      (le_refl 2) _ _ _).trans_lt hsmall

private theorem core_HamiltonIvey_of_positive {U : Opens E3}
    (out : SmoothRiemannianMetric (𝓡 3) U) (x : U)
    (hs : ∀ u v : TangentSpace (𝓡 3) x,
      out.inner x u u * out.inner x v v - out.inner x u v ^ 2 ≠ 0 →
        0 < sectionalCurvature out x u v) (hR : 0 < metricScalarAt out x) :
    0 ≤ leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x) ∧
      ∀ a L : ℝ, L ≤ 0 →
        (metricScalarAt out x,
          2 * leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x)) ∈
            fixedHamiltonIveyRegion a ∧ L ≤ metricScalarAt out x := by
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt (I := 𝓡 3) out x
    (show Module.finrank ℝ E3 = 3 by simp)
  have hν : 0 ≤ leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x) :=
    leastCurvatureOperatorEigenvalueAt_nonneg_of_sectionalCurvature_nonneg (I := 𝓡 3) out x B hB
      (fun u v hv => (hs u v hv).le)
  refine ⟨hν, ?_⟩
  intro a L hL
  exact ⟨Or.inl (mul_nonneg (by norm_num) hν), hL.trans hR.le⟩

theorem exists_normalizedDatum_insertedMetric_core_HamiltonIvey (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, 2 ≤ k →
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
          (x : insertionBall δ⁻¹), ‖(x : E3)‖ ≤ conformalRadius (-A) →
          let out : SmoothRiemannianMetric (𝓡 3) (insertionBall δ⁻¹) :=
            insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
          0 ≤ leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x) ∧
          ∀ a L : ℝ, L ≤ 0 →
            (metricScalarAt out x,
              2 * leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x)) ∈
              fixedHamiltonIveyRegion a ∧ L ≤ metricScalarAt out x := by
  obtain ⟨δ₀, hδ₀, hδ₀half, hb⟩ := exists_normalizedDatum_insertedMetric_core_curvature_pos A hA
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, hp⟩ := hb δ hδ hδle
  refine ⟨hAB, ?_⟩
  intro k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d x hx
  dsimp only
  let out : SmoothRiemannianMetric (𝓡 3) (insertionBall δ⁻¹) :=
    insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
  obtain ⟨hs, hR⟩ := hp k hk g x₀ d x hx
  exact core_HamiltonIvey_of_positive out x hs hR

end DifferentialGeometry.PDE.RicciFlow.StandardCap
