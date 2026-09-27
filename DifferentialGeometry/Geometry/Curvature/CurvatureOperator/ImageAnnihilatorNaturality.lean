import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem curvatureOperatorImageAnnihilatorAt_map_congrLeft
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    Submodule.map e.toLinearMap
        (curvatureOperatorImageAnnihilatorAt gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A)) =
      curvatureOperatorImageAnnihilatorAt gTarget y A := by
  exact ContinuousAlternatingMap.map_contractionAnnihilator_of_map_eq
    _ _ e.toContinuousLinearEquiv
    (curvatureOperatorImageAt_map_congrLeft gSource gTarget x y e hiso A)

theorem mem_curvatureOperatorImageAnnihilatorAt_congrLeft_iff
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (v : TangentSpace I x) :
    e v ∈ curvatureOperatorImageAnnihilatorAt gTarget y A ↔
      v ∈ curvatureOperatorImageAnnihilatorAt gSource x
        (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) := by
  rw [← curvatureOperatorImageAnnihilatorAt_map_congrLeft
    gSource gTarget x y e hiso A]
  constructor
  · intro hv
    rcases hv with ⟨u, hu, heq⟩
    have : u = v := e.injective heq
    simpa [this] using hu
  · intro hv
    exact ⟨v, hv, rfl⟩

end DifferentialGeometry.Geometry.Curvature
