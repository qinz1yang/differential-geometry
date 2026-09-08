import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorSpectrum
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralBounds
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree
open Bundle
open scoped Manifold ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousConstSMul ℝ (V x)]

theorem traceNormalizedCurvatureEndomorphism_metric_pullback_iInf_rayleighQuotient
    (g : SmoothRiemannianMetric I M) (h : RiemannianMetric V)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ∀ x v w, g.inner x (ι x v) (ι x w) = h.inner x v w) (x : M)
    (hdim : Module.finrank ℝ (V x) = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := (A : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StdAt (A : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        unfold tensor04StdAt
        congr 1
        ext k
        fin_cases k <;> rfl
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp A.property
    letI : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
    letI : RiemannianBundle V := ⟨h⟩
    letI sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
    let Rbar := exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
      (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)
    (⨅ v : {v : ⋀[ℝ]^2 (V x) // v ≠ 0}, Rbar.rayleighQuotient v) =
      2 * leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
  intro T hT Rbar
  let _ : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
  let _ : RiemannianBundle V := ⟨h⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let hRbar : Rbar.toLinearMap.IsSymmetric := exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric
    (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
    (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)
  let hdbar : Module.finrank ℝ (⋀[ℝ]^2 (V x)) = 3 := by
    rw [exteriorPower.finrank_eq, hdim]
    norm_num
  rw [hRbar.iInf_rayleighQuotient_eq_eigenvalues_last (n := 2) hdbar]
  exact traceNormalizedCurvatureEndomorphism_metric_pullback_eigenvalues_last g h ι hι x hdim A

end DifferentialGeometry.Geometry.Curvature.DimensionThree
