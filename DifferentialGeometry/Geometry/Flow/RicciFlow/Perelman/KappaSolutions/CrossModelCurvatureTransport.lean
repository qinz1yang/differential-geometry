import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private local instance crossModelCurvatureSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossModelCurvatureTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem metricRm04_pullbackCross_apply_slots
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v : Fin 4 → TangentSpace I x) :
    metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) x v =
      metricRm04At (I := J) g (Phi x)
        (fun i => mfderiv I J (Phi : M → N) x (v i)) := by
  have hsrc : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> rfl
  have hdst :
      vec4 (mfderiv I J (Phi : M → N) x (v 0))
          (mfderiv I J (Phi : M → N) x (v 1))
          (mfderiv I J (Phi : M → N) x (v 2))
          (mfderiv I J (Phi : M → N) x (v 3)) =
        (fun i : Fin 4 => mfderiv I J (Phi : M → N) x (v i)) := by
    funext i
    fin_cases i <;> rfl
  simpa only [metricRm04StandardAt_apply, hsrc, hdst] using
    metricRm04Standard_pullbackCross (I := I) (J := J) g Phi x
      (v 0) (v 1) (v 2) (v 3)

theorem metricRmNormSq_pullbackCross [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    normSq0S (I := I) (Diffeomorph.pullbackMetricCross g Phi) x 4
        (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) x) =
      normSq0S (I := J) g (Phi x) 4 (metricRm04At (I := J) g (Phi x)) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_orthonormal_basis (I := I) (Diffeomorph.pullbackMetricCross g Phi) x
  exact normSq0S_pullbackCross_eval_of_orthonormal (I := I) (J := J)
    g Phi x 4 basis hON
    (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) x)
    (metricRm04At (I := J) g (Phi x))
    (metricRm04_pullbackCross_apply_slots g Phi x)

section CurvatureOperator

private local instance crossModelCurvatureSourceC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossModelCurvatureTargetC2 : IsManifold J 2 N :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossModelCurvatureSourceC3 : IsManifold I 3 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossModelCurvatureTargetC3 : IsManifold J 3 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metricCurvatureOperatorNonnegative_pullbackCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M)
    (hR : metricAlgebraicCurvatureTensorAt (I := J) g (Phi x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J)) :
    metricAlgebraicCurvatureTensorAt (I := I)
        (Diffeomorph.pullbackMetricCross g Phi) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (I := I) (Diffeomorph.pullbackMetricCross g Phi) x).mpr
  intro n c v w
  have htest :=
    (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := J) g (Phi x)).mp hR n c
        (fun i => mfderiv I J (Phi : M → N) x (v i))
        (fun i => mfderiv I J (Phi : M → N) x (w i))
  simpa only [metricRm04Standard_pullbackCross] using htest

end CurvatureOperator

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
