import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ricciTensor_eq_half_scalar_sub_of_unit_curvature_nullity
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x)
    (he : e ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    (hunit : g.inner x e e = 1)
    (v w : TangentSpace I x) :
    ricciTensor g x v w = metricScalarAt g x / 2 *
      (g.inner x v w - g.inner x v e * g.inner x e w) := by
  have hz := tensor04StdAt_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    g x _ he v e w
  change metricRm04StandardAt g x v e e w = 0 at hz
  rw [metricRm04StdAt_eq_ricci3 g x hdim] at hz
  simp only [metricRicciAt_apply_eq_ricciTensor,
    ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt g x he,
    ricciTensor_symm g x v e, hunit, mul_one, zero_mul, add_zero] at hz
  linarith

theorem ricciTensor_eq_half_scalar_of_orthogonal_curvature_nullity
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x)
    (he : e ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    (hunit : g.inner x e e = 1)
    (v w : TangentSpace I x) (hv : g.inner x v e = 0) :
    ricciTensor g x v w = metricScalarAt g x / 2 * g.inner x v w := by
  rw [ricciTensor_eq_half_scalar_sub_of_unit_curvature_nullity hdim g x e he hunit,
    hv, zero_mul, sub_zero]

theorem traceNormalizedMetricCurvatureOperatorMatrixAt_eq_diagonal_of_curvature_nullity
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (he : basis 2 ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) :
    traceNormalizedMetricCurvatureOperatorMatrixAt g x basis =
      Matrix.diagonal ![metricScalarAt g x, 0, 0] := by
  have hdim : Module.finrank ℝ E = 3 := by
    have h := Module.finrank_eq_card_basis basis
    exact h
  have hunit : g.inner x (basis 2) (basis 2) = 1 := horth 2 2
  have hric (i j : Fin 3) : metricRicciAt g x (vec2 (basis i) (basis j)) =
      metricScalarAt g x / 2 * (delta3 i j - delta3 i 2 * delta3 2 j) := by
    rw [metricRicciAt_apply_eq_ricciTensor,
      ricciTensor_eq_half_scalar_sub_of_unit_curvature_nullity hdim g x (basis 2) he hunit,
      horth, horth, horth]
  ext i j
  change 2 * metricRm04StandardAt g x (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
    (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) = _
  rw [metricRm04StdAt_eq_ricci3 g x hdim]
  simp only [hric]
  simp_rw [show ∀ i j, g.inner x (basis i) (basis j) = delta3 i j from horth]
  fin_cases i <;> fin_cases j <;> simp [delta3, bivectorIndex3, Matrix.diagonal]
  all_goals ring

theorem sectionalCurvature_eq_half_scalar_of_orthonormal_curvature_nullity
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (he : basis 2 ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) :
    Riemannian.sectionalCurvature g x (basis 0) (basis 1) = metricScalarAt g x / 2 ∧
      Riemannian.sectionalCurvature g x (basis 0) (basis 2) = 0 ∧
      Riemannian.sectionalCurvature g x (basis 1) (basis 2) = 0 := by
  have hm := traceNormalizedMetricCurvatureOperatorMatrixAt_eq_diagonal_of_curvature_nullity
    g x basis horth he
  have hm0 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 0) hm
  have hm1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 1 1) hm
  have hm2 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 2 2) hm
  change 2 * metricRm04StandardAt g x (basis 0) (basis 1) (basis 1) (basis 0) = metricScalarAt g x at hm0
  change 2 * metricRm04StandardAt g x (basis 0) (basis 2) (basis 2) (basis 0) = 0 at hm1
  change 2 * metricRm04StandardAt g x (basis 1) (basis 2) (basis 2) (basis 1) = 0 at hm2
  simp only [Riemannian.sectionalCurvature_def,
    Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt,
    Riemannian.sectionalCurvatureDenominator_def]
  simp_rw [show ∀ i j, g.inner x (basis i) (basis j) = delta3 i j from horth]
  norm_num [delta3]
  change 2 * metricRm04At g x (vec4 (basis 0) (basis 1) (basis 1) (basis 0)) = _ at hm0
  change 2 * metricRm04At g x (vec4 (basis 0) (basis 2) (basis 2) (basis 0)) = _ at hm1
  change 2 * metricRm04At g x (vec4 (basis 1) (basis 2) (basis 2) (basis 1)) = _ at hm2
  exact ⟨by linarith only [hm0], Or.inl (by linarith only [hm1]), Or.inl (by linarith only [hm2])⟩

theorem traceNormalizedCurvatureEndomorphism_apply_of_curvature_nullity
    (g : SmoothRiemannianMetric I M) (x : M) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) :=
      mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace I x) :=
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : InnerProductSpace ℝ (TangentSpace I x) := Bundle.instInnerProductSpaceReal x
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x)),
      b 2 ∈ curvatureOperatorImageAnnihilatorAt g x
        ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ →
      ∀ i : Fin 3, exteriorPower.traceNormalizedCurvatureEndomorphism T hT
        (exteriorPower.ιMulti ℝ 2 ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2]) =
        (if i = 0 then metricScalarAt g x else 0) •
          exteriorPower.ιMulti ℝ 2 ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2] := by
  intro T hT
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  let _ : InnerProductSpace ℝ (TangentSpace I x) := Bundle.instInnerProductSpaceReal x
  intro b he i
  let B := curvatureBivectorBasis b
  let R := exteriorPower.traceNormalizedCurvatureEndomorphism T hT
  have horth : OrthonormalBasisAt g x b.toBasis := by
    intro i j
    exact b.inner_eq_ite i j
  have hm : LinearMap.toMatrix B.toBasis B.toBasis R.toLinearMap =
      Matrix.diagonal ![metricScalarAt g x, 0, 0] := by
    rw [traceNormalizedCurvatureEndomorphism_toMatrix]
    exact traceNormalizedMetricCurvatureOperatorMatrixAt_eq_diagonal_of_curvature_nullity
      g x b.toBasis horth he
  rw [← curvatureBivectorBasis_apply b i]
  change R (B i) = (if i = 0 then metricScalarAt g x else 0) • B i
  apply B.repr.injective
  ext j
  have hij := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A j i) hm
  rw [LinearMap.toMatrix_apply] at hij
  change B.repr (R (B i)) j = _ at hij
  rw [hij]
  simp only [map_smul, OrthonormalBasis.repr_self]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem metricScalarAt_eq_of_curvatureOperator_eigenvalue_of_curvature_nullity
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (he : basis 2 ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    (lam : ℝ) (hlam : lam ≠ 0)
    (heigen : Module.End.HasEigenvalue
      (traceNormalizedMetricCurvatureOperatorMatrixAt g x basis).toLin' lam) :
    metricScalarAt g x = lam := by
  rw [traceNormalizedMetricCurvatureOperatorMatrixAt_eq_diagonal_of_curvature_nullity
    g x basis horth he, hasEigenvalue_toLin'_diagonal_iff] at heigen
  obtain ⟨i, hi⟩ := heigen
  fin_cases i
  · exact hi
  · exact (hlam hi.symm).elim
  · exact (hlam hi.symm).elim

theorem sectionalCurvature_pos_of_curvatureOperator_rank_one_of_curvature_nullity
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (he : basis 2 ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    (hcone : (⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 1) :
    0 < Riemannian.sectionalCurvature g x (basis 0) (basis 1) := by
  rw [(sectionalCurvature_eq_half_scalar_of_orthonormal_curvature_nullity g x basis horth he).1]
  have hdim : Module.finrank ℝ E = 3 := Module.finrank_eq_card_basis basis
  exact div_pos (metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
    hdim g x hcone hrank) (by norm_num)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
