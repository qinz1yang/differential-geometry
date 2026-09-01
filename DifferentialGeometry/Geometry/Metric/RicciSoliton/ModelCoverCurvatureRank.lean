import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCurvatureRank

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]

theorem solitonModelCovering_metricCurvatureOperatorRankAt_eq
    {h : SmoothRiemannianMetric J N} {Fpot : C^∞⟮J, N; Real⟯}
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {cover : N → M}
    (hπ : solitonModelCovering h Fpot g f cover) (x : N)
    (hdimN : Module.finrank Real (TangentSpace J x) = 3)
    (hdimM : Module.finrank Real (TangentSpace I (cover x)) = 3) :
    metricCurvatureOperatorRankAt (I := J) h x hdimN =
      metricCurvatureOperatorRankAt (I := I) g (cover x) hdimM := by
  rw [solitonModelCovering_metric_eq_localPull hπ]
  exact metricCurvatureOperatorRankAt_localPull
    (I := J) (J := I) g cover
      (solitonModelCovering_isLocalDiffeomorph hπ) x hdimN hdimM

theorem not_solitonModelCovering_gaussian_and_roundThreeSphere
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {gaussianCover : EuclideanSpace Real (Fin 3) → M}
    {sphereCover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M}
    (hGaussian : solitonModelCovering
      (euclideanMetric (E := EuclideanSpace Real (Fin 3)))
      (gaussianPotential (E := EuclideanSpace Real (Fin 3))) g f gaussianCover)
    (hSphere : solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f sphereCover) :
    False := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let xGaussian : EuclideanSpace Real (Fin 3) := 0
  obtain ⟨xSphere, hxSphere⟩ :=
    solitonModelCovering_surjective hSphere (gaussianCover xGaussian)
  have hdimAt (y : M) : Module.finrank Real (TangentSpace I y) = 3 := by
    exact solitonModelCovering_target_tangent_finrank_eq hGaussian (by simp) y
  have hGaussianRank :=
    solitonModelCovering_metricCurvatureOperatorRankAt_eq hGaussian xGaussian
      (by change Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3; simp)
      (hdimAt (gaussianCover xGaussian))
  have hSphereRank :=
    solitonModelCovering_metricCurvatureOperatorRankAt_eq hSphere xSphere
      (by change Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3; simp)
      (hdimAt (sphereCover xSphere))
  have hGaussianTarget :
      metricCurvatureOperatorRankAt (I := I) g
        (gaussianCover xGaussian) (hdimAt (gaussianCover xGaussian)) = 0 := by
    rw [← hGaussianRank]
    exact euclideanMetric_curvatureOperatorRankAt xGaussian (by simp)
  have hSphereTarget :
      metricCurvatureOperatorRankAt (I := I) g
        (sphereCover xSphere) (hdimAt (sphereCover xSphere)) = 3 := by
    rw [← hSphereRank]
    exact roundThreeSphereShrinkerMetric_curvatureOperatorRankAt xSphere
  rw [hxSphere] at hSphereTarget
  omega

theorem not_solitonModelCovering_gaussian_and_roundThreeCylinder
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {gaussianCover : EuclideanSpace Real (Fin 3) → M}
    {cylinderCover :
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hGaussian : solitonModelCovering
      (euclideanMetric (E := EuclideanSpace Real (Fin 3)))
      (gaussianPotential (E := EuclideanSpace Real (Fin 3))) g f gaussianCover)
    (hCylinder : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cylinderCover) :
    False := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let xGaussian : EuclideanSpace Real (Fin 3) := 0
  obtain ⟨xCylinder, hxCylinder⟩ :=
    solitonModelCovering_surjective hCylinder (gaussianCover xGaussian)
  have hdimAt (y : M) : Module.finrank Real (TangentSpace I y) = 3 := by
    exact solitonModelCovering_target_tangent_finrank_eq hGaussian (by simp) y
  have hGaussianRank :=
    solitonModelCovering_metricCurvatureOperatorRankAt_eq hGaussian xGaussian
      (by change Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3; simp)
      (hdimAt (gaussianCover xGaussian))
  have hCylinderRank :=
    solitonModelCovering_metricCurvatureOperatorRankAt_eq
      (I := I) (J := (𝓡 2).prod 𝓘(Real, Real))
      (F := EuclideanSpace Real (Fin 2) × Real)
      (G := ModelProd (EuclideanSpace Real (Fin 2)) Real)
      (N := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      (M := M)
      (h := roundThreeCylinderShrinkerMetric)
      (Fpot := roundThreeCylinderShrinkerPotential)
      (g := g) (f := f) (cover := cylinderCover) hCylinder xCylinder
      (by
        change Module.finrank Real (EuclideanSpace Real (Fin 2) × Real) = 3
        rw [Module.finrank_prod]
        simp)
      (hdimAt (cylinderCover xCylinder))
  have hGaussianTarget :
      metricCurvatureOperatorRankAt (I := I) g
        (gaussianCover xGaussian) (hdimAt (gaussianCover xGaussian)) = 0 := by
    rw [← hGaussianRank]
    exact euclideanMetric_curvatureOperatorRankAt xGaussian (by simp)
  have hCylinderTarget :
      metricCurvatureOperatorRankAt (I := I) g
        (cylinderCover xCylinder) (hdimAt (cylinderCover xCylinder)) = 1 := by
    rw [← hCylinderRank]
    exact roundThreeCylinderShrinkerMetric_curvatureOperatorRankAt xCylinder
  rw [hxCylinder] at hCylinderTarget
  omega

theorem not_solitonModelCovering_roundThreeSphere_and_roundThreeCylinder
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {sphereCover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M}
    {cylinderCover :
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hSphere : solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f sphereCover)
    (hCylinder : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cylinderCover) :
    False := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let xSphere : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
  obtain ⟨xCylinder, hxCylinder⟩ :=
    solitonModelCovering_surjective hCylinder (sphereCover xSphere)
  have hdimAt (y : M) : Module.finrank Real (TangentSpace I y) = 3 := by
    exact solitonModelCovering_target_tangent_finrank_eq hSphere (by simp) y
  have hSphereRank :=
    solitonModelCovering_metricCurvatureOperatorRankAt_eq hSphere xSphere
      (by change Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3; simp)
      (hdimAt (sphereCover xSphere))
  have hCylinderRank :=
    solitonModelCovering_metricCurvatureOperatorRankAt_eq
      (I := I) (J := (𝓡 2).prod 𝓘(Real, Real))
      (F := EuclideanSpace Real (Fin 2) × Real)
      (G := ModelProd (EuclideanSpace Real (Fin 2)) Real)
      (N := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      (M := M)
      (h := roundThreeCylinderShrinkerMetric)
      (Fpot := roundThreeCylinderShrinkerPotential)
      (g := g) (f := f) (cover := cylinderCover) hCylinder xCylinder
      (by
        change Module.finrank Real (EuclideanSpace Real (Fin 2) × Real) = 3
        rw [Module.finrank_prod]
        simp)
      (hdimAt (cylinderCover xCylinder))
  have hSphereTarget :
      metricCurvatureOperatorRankAt (I := I) g
        (sphereCover xSphere) (hdimAt (sphereCover xSphere)) = 3 := by
    rw [← hSphereRank]
    exact roundThreeSphereShrinkerMetric_curvatureOperatorRankAt xSphere
  have hCylinderTarget :
      metricCurvatureOperatorRankAt (I := I) g
        (cylinderCover xCylinder) (hdimAt (cylinderCover xCylinder)) = 1 := by
    rw [← hCylinderRank]
    exact roundThreeCylinderShrinkerMetric_curvatureOperatorRankAt xCylinder
  rw [hxCylinder] at hCylinderTarget
  omega

end DifferentialGeometry.Geometry
