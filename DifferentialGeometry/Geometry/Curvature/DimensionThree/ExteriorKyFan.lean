import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorSpectrum
import DifferentialGeometry.Analysis.Spectral.LowerKyFan

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem traceNormalizedCurvatureEndomorphism_pullback_lowerKyFanSum_one
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ F = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (C : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫) :
    let T := (C : Tensor04At (I := I) (M := M) x)
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
    let U := T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)
    let hU := hT.compContinuousLinearMap ι.toContinuousLinearMap
    (exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric U hU).lowerKyFanSum 1 =
      2 * leastCurvatureOperatorEigenvalueAt g x C := by
  intro T hT U hU
  let b := (stdOrthonormalBasis ℝ F).reindex (finCongr hdim)
  let b' := b.toBasis.map ι.toLinearEquiv
  have horth : OrthonormalBasisAt g x b' := by
    intro i j
    simpa only [b', Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
      ContinuousLinearEquiv.coe_toLinearEquiv, delta3] using
      (hmetric (b i) (b j)).trans (b.inner_eq_ite i j)
  let A := exteriorPower.traceNormalizedCurvatureEndomorphism U hU
  let B := curvatureBivectorBasis b
  have hmatrix : LinearMap.toMatrix B.toBasis B.toBasis A.toLinearMap =
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
  let hA : A.toLinearMap.IsSymmetric :=
    exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric U hU
  have hdA : Module.finrank ℝ (⋀[ℝ]^2 F) = 3 := by
    rw [exteriorPower.finrank_eq, hdim]
    norm_num
  let Rmat := traceNormalizedCurvatureOperatorMatrixAt x b' C
  have hRmat : Rmat.IsHermitian := traceNormalizedCurvatureOperatorMatrixAt_isHermitian x b' C
  have heigen : hA.eigenvalues hdA = hRmat.eigenvalues₀ := by
    apply (hA.eigenvalues_eq_eigenvalues_iff hdA
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hRmat) finrank_euclideanSpace).mpr
    rw [← A.toLinearMap.charpoly_toMatrix B.toBasis, hmatrix]
    exact (Matrix.charpoly_toLin Rmat (PiLp.basisFun 2 ℝ (Fin 3))).symm
  change hA.lowerKyFanSum 1 = _
  rw [hA.lowerKyFanSum_one_eq_iInf_rayleighQuotient,
    hA.iInf_rayleighQuotient_eq_eigenvalues_last hdA, heigen]
  exact traceNormalizedCurvatureOperatorMatrixAt_least_eigenvalue g x b' horth C

end DifferentialGeometry.Geometry.Curvature.DimensionThree
