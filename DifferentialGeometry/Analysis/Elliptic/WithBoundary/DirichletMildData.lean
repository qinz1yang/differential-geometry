import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletHeatSemigroup

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def dirichletSmoothInitialData
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : SmoothScalarDirichlet g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  smoothToLpDirichlet g u₀

omit [T2Space M] in
theorem smoothScalarDirichlet_hasCompactSupport
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : SmoothScalarDirichlet g) :
    HasCompactSupport u₀.toFun :=
  HasCompactSupport.of_compactSpace _

omit [T2Space M] [CompactSpace M] in
theorem smoothScalarDirichlet_contMDiff
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : SmoothScalarDirichlet g) :
    ContMDiff (I_half n) 𝓘(Real, Real) ∞ u₀.toFun :=
  u₀.smooth

omit [T2Space M] [CompactSpace M] in
theorem smoothScalarDirichlet_support_subset_interior
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : SmoothScalarDirichlet g) :
    tsupport u₀.toFun ⊆ (I_half n).interior M :=
  u₀.interior_support

@[simp] theorem dirichletSmoothInitialData_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : SmoothScalarDirichlet g) :
    dirichletSmoothInitialData g u₀ = smoothToLpDirichlet g u₀ :=
  rfl

theorem dirichletHeatSemigroup_initial_data
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    dirichletHeatSemigroup g 0 u₀ = u₀ := by
  rw [dirichletHeatSemigroup_apply]
  have hzero := abstractSpectralSemigroup_apply_zero
    (dirichletLaplacianHilbertBasis g)
    (fun i => dirichletLaplacianEigenvalue_nonneg i)
  have hzero' := congrArg
    (fun L : (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) => L u₀) hzero
  simpa using hzero'

theorem dirichletHeatSemigroup_initial_data_smooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : SmoothScalarDirichlet g) :
    dirichletHeatSemigroup g 0 (dirichletSmoothInitialData g u₀) =
      dirichletSmoothInitialData g u₀ := by
  exact dirichletHeatSemigroup_initial_data g
    (dirichletSmoothInitialData g u₀)

theorem dirichletHeatSemigroup_tendsto_initial_data
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    Tendsto (fun t : ℝ => dirichletHeatSemigroup g t u₀)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 u₀) := by
  change Tendsto
    (fun t : ℝ => abstractSpectralSemigroup
      (dirichletLaplacianHilbertBasis g)
      (fun i => dirichletLaplacianEigenvalue_nonneg i) t u₀)
    (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 u₀)
  exact abstractSpectralSemigroup_continuous_at_zero
    (dirichletLaplacianHilbertBasis g)
    (fun i => dirichletLaplacianEigenvalue_nonneg i) u₀

theorem dirichletHeatDuhamel_initial_data
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (F : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    dirichletHeatDuhamel g u₀ F 0 = u₀ := by
  unfold dirichletHeatDuhamel
  exact QuasiLinear.duhamel_zero
    (dirichletHeatSemigroup g) u₀ F

theorem dirichletHeatDuhamel_zero_forcing
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (t : ℝ) :
    dirichletHeatDuhamel g u₀ (fun _ : ℝ => (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) t =
      dirichletHeatSemigroup g t u₀ := by
  unfold dirichletHeatDuhamel abstractSpectralDuhamel
  unfold DifferentialGeometry.Analysis.Parabolic.QuasiLinear.duhamel
  change abstractSpectralBoundedC0Semigroup
      (dirichletLaplacianHilbertBasis g)
      (fun i => dirichletLaplacianEigenvalue_nonneg i) t u₀ +
      ∫ τ in (0 : ℝ)..t,
        abstractSpectralBoundedC0Semigroup
          (dirichletLaplacianHilbertBasis g)
          (fun i => dirichletLaplacianEigenvalue_nonneg i) (t - τ) 0 =
    abstractSpectralBoundedC0Semigroup
      (dirichletLaplacianHilbertBasis g)
      (fun i => dirichletLaplacianEigenvalue_nonneg i) t u₀
  simp only [map_zero, intervalIntegral.integral_zero, add_zero]

theorem dirichletHeat_mild_solution_exists_unique_on_Icc
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (F : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (hF : Continuous F) :
    ∃ T : ℝ, ∃ u : ℝ →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
      DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution
        (dirichletHeatSemigroup g) u₀ F T u ∧
      ∀ v : ℝ →
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
        DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution
          (dirichletHeatSemigroup g) u₀ F T v →
        Set.EqOn u v (Set.Icc (0 : ℝ) T) := by
  obtain ⟨T, u, hu⟩ := dirichletHeat_mild_solution_exists g u₀ F hF
  refine ⟨T, u, hu, ?_⟩
  intro v hv
  exact dirichletHeat_mild_solution_unique g u₀ F hu hv

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry
