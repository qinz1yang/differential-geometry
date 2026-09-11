import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction
import DifferentialGeometry.Geometry.Metric.BundlePullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorConjugation

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

theorem traceNormalizedCurvatureEndomorphism_metric_pullback_eigenvalues_last
    (g : SmoothRiemannianMetric I M) (h : RiemannianMetric V)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ∀ x v w, g.inner x (ι x v) (ι x w) = h.inner x v w) (x : M)
    (hdim : Module.finrank ℝ (V x) = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := (A : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StandardAt (A : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        unfold tensor04StandardAt
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
    let hRbar : Rbar.toLinearMap.IsSymmetric := exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric
      (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
      (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)
    let hdbar : Module.finrank ℝ (⋀[ℝ]^2 (V x)) = 3 := by
      rw [exteriorPower.finrank_eq, hdim]
      norm_num
    hRbar.eigenvalues hdbar 2 =
      2 * leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
  intro T hT Rbar hRbar hdbar
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
  let F₂ := exteriorPower.mapLinearIsometryEquiv 2 e
  let Rg := exteriorPower.traceNormalizedCurvatureEndomorphism T hT
  have heq : Rbar = F₂.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Rg.comp F₂.toContinuousLinearEquiv.toContinuousLinearMap) :=
    exteriorPower.traceNormalizedCurvatureEndomorphism_pullback_eq_conjugate e T hT
  have hdimT : Module.finrank ℝ (TangentSpace I x) = 3 := by
    rw [← (ι x).toLinearEquiv.finrank_eq]
    exact hdim
  let b := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hdimT)
  let B := curvatureBivectorBasis b
  have horth : OrthonormalBasisAt g x b.toBasis := by
    intro i j
    exact b.inner_eq_ite i j
  have hRg := exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric T hT
  have hdg : Module.finrank ℝ (⋀[ℝ]^2 (TangentSpace I x)) = 3 := by
    rw [exteriorPower.finrank_eq, hdimT]
    norm_num
  have heigen : hRbar.eigenvalues hdbar = hRg.eigenvalues hdg := by
    apply (hRbar.eigenvalues_eq_eigenvalues_iff hdbar hRg hdg).mpr
    change Rbar.toLinearMap.charpoly = Rg.toLinearMap.charpoly
    rw [heq]
    change (F₂.symm.toLinearEquiv.conj Rg.toLinearMap).charpoly = _
    exact LinearEquiv.charpoly_conj _ _
  rw [heigen]
  let Rmat := traceNormalizedCurvatureOperatorMatrixAt (I := I) x b.toBasis A
  have hA : Rmat.IsHermitian := traceNormalizedCurvatureOperatorMatrixAt_isHermitian
    (I := I) x b.toBasis A
  have heigenA : hRg.eigenvalues hdg = hA.eigenvalues₀ := by
    apply (hRg.eigenvalues_eq_eigenvalues_iff hdg
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace).mpr
    rw [← Rg.toLinearMap.charpoly_toMatrix B.toBasis, traceNormalizedCurvatureEndomorphism_toMatrix]
    have hmat : (fun i j => 2 * T ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2,
        b (bivectorIndex3 j).2, b (bivectorIndex3 j).1]) = Rmat := by
      ext i j
      change 2 * T _ = 2 * T _
      congr 2
      ext k
      fin_cases k <;> rfl
    rw [hmat]
    exact (Matrix.charpoly_toLin Rmat (PiLp.basisFun 2 ℝ (Fin 3))).symm
  rw [heigenA]
  exact traceNormalizedCurvatureOperatorMatrixAt_least_eigenvalue g x b.toBasis horth _
end DifferentialGeometry.Geometry.Curvature.DimensionThree
