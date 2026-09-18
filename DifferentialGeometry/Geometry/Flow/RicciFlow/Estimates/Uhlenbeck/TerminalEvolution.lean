import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorEvolution

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_terminal_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι b x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric b).inner x (ι b x v) (ι b x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric b) x (ι b x v)) (Set.Iic b) b) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι b y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric b))
    let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric s) y)).compContinuousLinearMap (ι s y).toContinuousLinearMap)
    HasDerivWithinAt (fun s => R s x)
      (rawBundleEndomorphismConnLap (S.family.metric b) (cov.exteriorPower 2) (R b) x +
        (curvatureOperatorReactionEndomorphism3 (R b x).toLinearMap).toContinuousLinearMap) (Set.Iic b) b := by
  exact traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_evolution S b ι hι hmetric x hdim
    (riemann_tensor_hasDerivWithinAt_terminal_of_solution S hS hab hslab hreg x) hode

theorem traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_terminal_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι b x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric b).inner x (ι b x v) (ι b x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric b) x (ι b x v)) (Set.Iic b) b) :
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
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι b y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric b))
    let hc := CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric b) (ι b) hι₁ hmetric
    let T := fun s y => (S.base.rm04 s y).compContinuousLinearMap
      (fun _ => (ι s y).toContinuousLinearMap)
    let hT := fun s y => (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric s) y))
        |>.compContinuousLinearMap (ι s y).toContinuousLinearMap
    let R : ℝ → ∀ y, P.fiber y := fun s y =>
      exteriorPower.traceNormalizedCurvatureSelfAdjoint (T s y) (hT s y)
    let Q : P.fiber x := curvatureOperatorReactionSelfAdjoint3 (R b x)
    HasDerivWithinAt (fun s => R s x)
      (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        (S.family.metric b)
        ((cov.exteriorPower 2).selfAdjoint
          (F := ⋀[ℝ]^2 F) (V := fun y => ⋀[ℝ]^2 (V y))
          (hc.exteriorPower 2)) (R b) x + Q) (Set.Iic b) b := by
  exact traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_of_evolution S b ι hι hmetric x hdim
    (riemann_tensor_hasDerivWithinAt_terminal_of_solution S hS hab hslab hreg x) hode

end DifferentialGeometry.PDE.RicciFlow
