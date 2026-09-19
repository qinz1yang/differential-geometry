import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompactSlab
import DifferentialGeometry.Geometry.Operator.CovariantTensor

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_curvature_first_second_derivative_bounds_on_slab
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a₀ a b R : ℝ} (hbuffer : a₀ < a) (hab : a ≤ b)
    (hslab : Icc a₀ b ⊆ D.carrier) (hreg : Ioc a₀ b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a₀))
    (hR : 0 ≤ R)
    (hcurv : ∀ t ∈ Icc a₀ b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ R) :
    ∃ D₁ D₂ : ℝ, 0 ≤ D₁ ∧ 0 ≤ D₂ ∧
      (∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 5
          (metricNabla0S (I := I) (S.base.metric t)
            (CovariantDerivative.rm04Section (I := I) (S.base.metric t)
              (metricCov (I := I) (S.base.metric t)) (metricCov_smooth (I := I) (S.base.metric t))) x) ≤ D₁) ∧
      (∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 6
          (metricNabla0S (I := I) (S.base.metric t)
            (metricNabla0S (I := I) (S.base.metric t)
              (CovariantDerivative.rm04Section (I := I) (S.base.metric t)
                (metricCov (I := I) (S.base.metric t)) (metricCov_smooth (I := I) (S.base.metric t)))) x) ≤ D₂) := by
  obtain ⟨K, hK, hbound⟩ := shi_curvature_derivative_bound_on_slab
    (I := I) S hS hbuffer hab hslab hreg hcomplete hR hcurv
  refine ⟨K, K, hK, hK, ?_, ?_⟩
  · intro t ht x
    have h := hbound 1 (by omega) t ht x
    have hfield : metricNabla0S (I := I) (S.base.metric t) (S.base.rm04 t) x =
        nablaKRm04Field (I := I) S t 1 x := by
      simp only [metricNabla0S_apply, totalNabla0S_apply, nablaKRm04Field_succ,
        nablaKRm04Field_zero]
      rfl
    change normSq0S (I := I) (S.base.metric t) x 5
      (metricNabla0S (I := I) (S.base.metric t) (S.base.rm04 t) x) ≤ K
    rw [hfield]
    exact h
  · intro t ht x
    have h := hbound 2 le_rfl t ht x
    have hfield : metricNabla0S (I := I) (S.base.metric t)
        (metricNabla0S (I := I) (S.base.metric t) (S.base.rm04 t)) x =
        nablaKRm04Field (I := I) S t 2 x := by
      simp only [metricNabla0S_apply, totalNabla0S_apply, nablaKRm04Field_succ,
        nablaKRm04Field_zero]
      rfl
    change normSq0S (I := I) (S.base.metric t) x 6
      (metricNabla0S (I := I) (S.base.metric t)
        (metricNabla0S (I := I) (S.base.metric t) (S.base.rm04 t)) x) ≤ K
    rw [hfield]
    exact h


end DifferentialGeometry.PDE.RicciFlow
