import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityLocalCross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F] [CompleteSpace F] [NeZero (Module.finrank Real F)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [IsManifold J 1 N] [IsManifold J 2 N]
  [SigmaCompactSpace N] [T2Space N] [J.Boundaryless]

omit [NeZero (Module.finrank Real E)] [NeZero (Module.finrank Real F)]
    [I.Boundaryless] [J.Boundaryless] in
theorem metricCurvatureOperatorRankAt_localPull
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M)
    (hdimM : Module.finrank Real (TangentSpace I x) = 3)
    (hdimN : Module.finrank Real (TangentSpace J (f x)) = 3) :
    metricCurvatureOperatorRankAt (I := I)
        (localPullMetric (I := I) (J := J) g f hf) x hdimM =
      metricCurvatureOperatorRankAt (I := J) g (f x) hdimN := by
  classical
  obtain ⟨basis, horth⟩ :=
    exists_orthonormalBasisAt (I := I)
      (localPullMetric (I := I) (J := J) g f hf) x hdimM
  let e : TangentSpace I x ≃L[Real] TangentSpace J (f x) :=
    hf.mfderivToContinuousLinearEquiv (by simp) x
  let basis' : Module.Basis (Fin 3) Real (TangentSpace J (f x)) :=
    basis.map e.toLinearEquiv
  have horth' : OrthonormalBasisAt (I := J) g (f x) basis' := by
    intro i j
    rw [show basis' i = e (basis i) by simp [basis']]
    rw [show basis' j = e (basis j) by simp [basis']]
    rw [show e (basis i) = mfderiv I J f x (basis i) by rfl]
    rw [show e (basis j) = mfderiv I J f x (basis j) by rfl]
    rw [← localPullMetric_inner (I := I) (J := J) g f hf]
    exact horth i j
  rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := I) (M := M) (localPullMetric (I := I) (J := J) g f hf)
      x hdimM basis horth]
  rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := J) (M := N) g (f x) hdimN basis' horth']
  congr 1
  ext i j
  change metricRm04StdAt (I := I) (M := M)
      (localPullMetric (I := I) (J := J) g f hf) x
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) =
    metricRm04StdAt (I := J) (M := N) g (f x)
        (basis' (bivectorIndex3 i).1) (basis' (bivectorIndex3 i).2)
        (basis' (bivectorIndex3 j).2) (basis' (bivectorIndex3 j).1)
  rw [DifferentialGeometry.Integral.Connection.rm04_localPull]
  simp only [basis', Module.Basis.map_apply]
  rfl

end DifferentialGeometry.Geometry.Curvature.DimensionThree
