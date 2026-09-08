import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JointRegularity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Tensor.Multilinear.BundleComp

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

omit [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
    [I.Boundaryless] in
private theorem riemann_pullback_isAlgCurvForm
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M)
    (ι : V x ≃L[ℝ] TangentSpace I x) :
    IsAlgCurvForm (fun a b c d =>
      (S.base.rm04 t x).compContinuousLinearMap
        (fun _ => ι.toContinuousLinearMap) ![a, b, c, d]) := by
  have hT := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
  change IsAlgCurvForm (fun a b c d => S.base.rm04 t x ![a, b, c, d]) at hT
  exact hT.compContinuousLinearMap ι.toContinuousLinearMap

theorem traceNormalizedCurvatureEndomorphism_pullback_contMDiffOnSpacetimeEndomorphism
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJD : J ⊆ D.regular)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M))) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    ContMDiffOnSpacetimeEndomorphism (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞)
      (fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
        (riemann_pullback_isAlgCurvForm S t x (ι t x))) (J ×ˢ (Set.univ : Set M)) := by
  apply Bundle.ExteriorPower.contMDiffOnSpacetimeEndomorphism_traceNormalizedCurvatureEndomorphism F V _
    (fun t x => riemann_pullback_isAlgCurvForm S t x (ι t x))
  exact ((rm04_contMDiffOn_regular_of_solution S hS).mono
    (Set.prod_mono hJD Set.Subset.rfl)).multilinear_bundle_comp (fun _ => hι)

omit [I.Boundaryless] in
theorem traceNormalizedCurvatureEndomorphism_pullback_continuousOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJD : J ⊆ D.carrier)
    (hι : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M))) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
        (E := fun x => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) p.2
        (exteriorPower.traceNormalizedCurvatureEndomorphism
          ((S.base.rm04 p.1 p.2).compContinuousLinearMap
            (fun _ => (ι p.1 p.2).toContinuousLinearMap))
          (riemann_pullback_isAlgCurvForm S p.1 p.2 (ι p.1 p.2))))
      (J ×ˢ (Set.univ : Set M)) := by
  have hTzero : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) 0
      (fun p : ℝ × M => (⟨p.2, S.base.rm04 p.1 p.2⟩ :
        TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
          (Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I : M → Type _))))
      (J ×ˢ (Set.univ : Set M)) :=
    contMDiffOn_zero_iff.mpr ((rm04_continuousOn_carrier_of_solution S hS).mono
      (Set.prod_mono hJD Set.Subset.rfl))
  have hιzero : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) 0
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) :=
    contMDiffOn_zero_iff.mpr hι
  have hTpull := hTzero.multilinear_bundle_comp (fun _ => hιzero)
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  intro p hp
  exact (Bundle.ExteriorPower.contMDiffWithinAt_traceNormalizedCurvatureEndomorphism
    (I := I) F V 0 (by simp)
    (fun q : ℝ × M => (S.base.rm04 q.1 q.2).compContinuousLinearMap
      (fun _ => (ι q.1 q.2).toContinuousLinearMap))
    (fun q => riemann_pullback_isAlgCurvForm S q.1 q.2 (ι q.1 q.2))
    (hTpull p hp)).continuousWithinAt

end DifferentialGeometry.PDE.RicciFlow
