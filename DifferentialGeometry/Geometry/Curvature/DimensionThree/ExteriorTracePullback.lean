import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorTrace
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.MetricConjugation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousConstSMul ℝ (V x)]

theorem trace_traceNormalizedCurvatureEndomorphism_metric_pullback
    (g : SmoothRiemannianMetric I M) (h : RiemannianMetric V)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ∀ x v w, g.inner x (ι x v) (ι x w) = h.inner x v w) (x : M)
    (hdim : Module.finrank ℝ (V x) = 3) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      exact mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    letI : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
    letI : RiemannianBundle V := ⟨h⟩
    letI sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
    let Rbar := exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
      (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)
    LinearMap.trace ℝ (⋀[ℝ]^2 (V x)) Rbar.toLinearMap = metricScalarAt g x := by
  intro T hT Rbar
  let _ : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
  let _ : RiemannianBundle V := ⟨h⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (targetNorm y).toSeminormedAddCommGroup
  let _ : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y => Bundle.instInnerProductSpaceReal y
  let e := g.toRiemannianMetric.toLinearIsometryEquiv h id ι hι x
  have hconj := traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate
    (g := g) h ι hι x
  have hdimT : Module.finrank ℝ (TangentSpace I x) = 3 := by
    rw [← (ι x).toLinearEquiv.finrank_eq]
    exact hdim
  have htrace := trace_traceNormalizedCurvatureEndomorphism_metricRm04At g x hdimT
  let F₂ := exteriorPower.mapLinearIsometryEquiv 2 e
  let Rg := exteriorPower.traceNormalizedCurvatureEndomorphism T hT
  have heq : Rbar = F₂.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Rg.comp F₂.toContinuousLinearEquiv.toContinuousLinearMap) := hconj.2.1
  rw [heq]
  change LinearMap.trace ℝ _ (F₂.symm.toLinearEquiv.conj Rg.toLinearMap) = _
  rw [LinearMap.trace_conj']
  exact htrace

theorem trace_curvatureOperatorReactionEndomorphism3_metric_pullback
    (g : SmoothRiemannianMetric I M) (h : RiemannianMetric V)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ∀ x v w, g.inner x (ι x v) (ι x w) = h.inner x v w) (x : M)
    (hdim : Module.finrank ℝ (V x) = 3) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      exact mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    letI : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
    letI : RiemannianBundle V := ⟨h⟩
    letI sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
    let Rbar := exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
      (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)
    LinearMap.trace ℝ (⋀[ℝ]^2 (V x))
      (curvatureOperatorReactionEndomorphism3 Rbar.toLinearMap) =
        2 * Tensor0SBundle.normSq0S g x 2 (metricRicciAt g x) := by
  intro T hT Rbar
  let _ : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
  let _ : RiemannianBundle V := ⟨h⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (targetNorm y).toSeminormedAddCommGroup
  let _ : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y => Bundle.instInnerProductSpaceReal y
  let e := g.toRiemannianMetric.toLinearIsometryEquiv h id ι hι x
  have hconj := traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate
    (g := g) h ι hι x
  have hdimT : Module.finrank ℝ (TangentSpace I x) = 3 := by
    rw [← (ι x).toLinearEquiv.finrank_eq]
    exact hdim
  have htrace := trace_curvatureOperatorReactionEndomorphism3_metricRm04At g x hdimT
  let F₂ := exteriorPower.mapLinearIsometryEquiv 2 e
  let Rg := exteriorPower.traceNormalizedCurvatureEndomorphism T hT
  have heq : Rbar = F₂.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Rg.comp F₂.toContinuousLinearEquiv.toContinuousLinearMap) := hconj.2.1
  rw [heq]
  change LinearMap.trace ℝ _ (curvatureOperatorReactionEndomorphism3
    (F₂.symm.toLinearEquiv.conj Rg.toLinearMap)) = _
  rw [curvatureOperatorReactionEndomorphism3_conj]
  rw [LinearMap.trace_conj']
  exact htrace

end DifferentialGeometry.Geometry.Curvature.DimensionThree
