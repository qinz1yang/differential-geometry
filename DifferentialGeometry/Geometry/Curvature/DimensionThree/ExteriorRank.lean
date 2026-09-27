import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
theorem curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Module.finrank ℝ (curvatureOperatorImageAt g x A) =
      (traceNormalizedCurvatureOperatorMatrixAt x basis A).rank := by
  let b := curvatureTwoFormBasisAt (I := I) basis
  let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
    b.finiteDimensional_of_finite
  let B := curvatureOperatorBilinearAt g x A
  have hmatrix : LinearMap.toMatrix b b.dualBasis B =
      (traceNormalizedCurvatureOperatorMatrixAt x basis A).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
    exact curvatureOperatorPairingAt_curvatureTwoFormBasisAt g x basis horth A j i
  have hrange : Module.finrank ℝ (curvatureOperatorImageAt g x A) =
      Module.finrank ℝ B.range := by
    change Module.finrank ℝ ((twoFormMetricData g x).sharp.toLinearMap.comp B).range = _
    rw [LinearMap.range_comp]
    exact LinearEquiv.finrank_map_eq (twoFormMetricData g x).sharp B.range
  rw [hrange]
  have hmatrixRank := Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b.dualBasis B)
    b.dualBasis b
  rw [Matrix.toLin_toMatrix] at hmatrixRank
  rw [← hmatrixRank, hmatrix, Matrix.rank_transpose]

theorem metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    DimensionThree.metricCurvatureOperatorRankAt g x hdim =
      Module.finrank ℝ (curvatureOperatorImageAt g x
        ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  rw [DimensionThree.metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal g x hdim basis horth,
    curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank g x basis horth]
  symm
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0))


omit [T2Space M] in
theorem traceNormalizedCurvatureEndomorphism_pullback_finrank_range
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ F = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (C : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
      (C : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StandardAt (C : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        unfold tensor04StandardAt
        congr 1
        ext k
        fin_cases k <;> rfl
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp C.property
    Module.finrank ℝ
      (exteriorPower.traceNormalizedCurvatureEndomorphism
        (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
        (hT.compContinuousLinearMap ι.toContinuousLinearMap)).range =
      Module.finrank ℝ (curvatureOperatorImageAt g x C) := by
  intro T hT
  let b := (stdOrthonormalBasis ℝ F).reindex (finCongr hdim)
  let b' := b.toBasis.map ι.toLinearEquiv
  have horth : OrthonormalBasisAt g x b' := by
    intro i j
    simpa only [b', Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
      ContinuousLinearEquiv.coe_toLinearEquiv, delta3] using
      (hmetric (b i) (b j)).trans (b.inner_eq_ite i j)
  let U := T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)
  let hU := hT.compContinuousLinearMap ι.toContinuousLinearMap
  let A := exteriorPower.traceNormalizedCurvatureEndomorphism U hU
  let B := (curvatureBivectorBasis b).toBasis
  have hmatrix : LinearMap.toMatrix B B A.toLinearMap =
      traceNormalizedCurvatureOperatorMatrixAt x b' C := by
    rw [traceNormalizedCurvatureEndomorphism_toMatrix]
    ext i j
    change 2 * (C : Tensor04At (I := I) (M := M) x)
        (fun k => ι (![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2,
          b (bivectorIndex3 j).2, b (bivectorIndex3 j).1] k)) =
      2 * (C : Tensor04At (I := I) (M := M) x)
        (vec4 (ι (b (bivectorIndex3 i).1)) (ι (b (bivectorIndex3 i).2))
          (ι (b (bivectorIndex3 j).2)) (ι (b (bivectorIndex3 j).1)))
    congr 2
    ext k
    fin_cases k <;> rfl
  have hmatrixRank := Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix B B A.toLinearMap) B B
  rw [Matrix.toLin_toMatrix] at hmatrixRank
  change Module.finrank ℝ A.range = _
  rw [← hmatrixRank, hmatrix]
  exact (curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank g x b' horth _).symm

end DifferentialGeometry.Geometry.Curvature
