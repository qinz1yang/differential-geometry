import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.TerminalSections
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.TerminalKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionPositivity

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open CovariantDerivative
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

theorem curvatureOperator_kernel_isCovariantlyInvariant_terminal_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (hdim : Module.finrank ℝ F = 3)
    (hcone : ∀ t ∈ Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric b).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι₀ y).toLinearEquiv)
      (hι₀.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
      (LeviCivita (S.family.metric b))
    let T := fun x => (S.base.rm04 b x).compContinuousLinearMap
      (fun _ => (ι₀ x).toContinuousLinearMap)
    let R := fun x => exteriorPower.traceNormalizedCurvatureEndomorphism (T x)
      (by
        have hT := mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric b) x)
        exact hT.compContinuousLinearMap (ι₀ x).toContinuousLinearMap)
    IsCovariantlyInvariantSubmoduleFamily (cov.exteriorPower 2) (fun x => (R x).ker) := by
  dsimp only
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι₀ y).toLinearEquiv)
    (hι₀.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric b))
  obtain ⟨ι, hinit, A, hA, hpos, hsmooth, hmetric, hevo⟩ :=
    exists_nonnegative_curvatureOperator_sections_terminal_evolution
      (F := F) (V := V) S hS hab hslab hreg hdim hcone ι₀ hι₀ h₀
  let _ : ContMDiffCovariantDerivative (cov.exteriorPower 2) ∞ := hsmooth
  have hinv := PositiveSystem.kernel_isCovariantlyInvariant_at_right_endpoint
    (S.family.metric b) (cov.exteriorPower 2) hmetric A hab hpos
    (fun _ => 0)
    (fun x => (curvatureOperatorReactionEndomorphism3 (A b x).toLinearMap).toContinuousLinearMap)
    (fun x v _ => (curvatureOperatorReactionEndomorphism3_isPositive
      (hpos b ⟨hab.le, le_rfl⟩ x).toLinearMap).inner_nonneg_left v)
    (fun x => by simpa only [map_zero, add_zero] using hevo x)
  simpa only [hA, hinit] using hinv

end DifferentialGeometry.PDE.RicciFlow
