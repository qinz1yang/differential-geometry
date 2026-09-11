import DifferentialGeometry.Analysis.Parabolic.ExteriorSelfAdjointEvolution
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem IsMetricCompatible.hasDerivWithinAt_traceNormalizedCurvatureSelfAdjoint
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
    (hc : cov.IsMetricCompatible) (g : SmoothRiemannianMetric I M)
    (T : ℝ → ∀ y, Bundle.continuousMultilinearMap ℝ 4 F V y)
    (hT : ∀ s y, IsAlgCurvForm (fun a b c d => T s y ![a, b, c, d]))
    (t : ℝ)
    (hTsmooth : ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun y => TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ) y (T t y)))
    (x : M) (J : Set ℝ) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
    letI := P.totalSpaceTopology
    letI := P.fiberBundle
    let A := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism (T s y) (hT s y)
    let R : ℝ → ∀ y, P.fiber y := fun s y =>
      exteriorPower.traceNormalizedCurvatureSelfAdjoint (T s y) (hT s y)
    let Q : P.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
    HasDerivWithinAt (fun s => A s x)
      (rawBundleEndomorphismConnLap g (cov.exteriorPower 2) (A t) x +
        (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) J t →
    HasDerivWithinAt (fun s => R s x)
      (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y) g
        ((cov.exteriorPower 2).selfAdjoint (F := ⋀[ℝ]^2 F)
          (V := fun y => ⋀[ℝ]^2 (V y)) (hc.exteriorPower 2)) (R t) x + Q) J t := by
  dsimp only
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
    (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
  let := P.totalSpaceTopology
  let := P.fiberBundle
  intro h
  let A := Bundle.ExteriorPower.traceNormalizedCurvatureSelfAdjointSection F V (T t) (hT t) hTsmooth
  exact hc.hasDerivWithinAt_exteriorPower_selfAdjoint (F := F) (V := V)
    g 2 (fun s y => exteriorPower.traceNormalizedCurvatureSelfAdjoint (T s y) (hT s y)) t
    A.contMDiff x (curvatureOperatorReactionSelfAdjoint3 (exteriorPower.traceNormalizedCurvatureSelfAdjoint
      (T t x) (hT t x))) J h

end CovariantDerivative
