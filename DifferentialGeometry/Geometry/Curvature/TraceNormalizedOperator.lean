import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import Mathlib.Analysis.InnerProductSpace.Rayleigh

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff InnerProductSpace BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def traceNormalizedCurvatureOperatorMatrixAt (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (2 : ℝ) • curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x)

def traceNormalizedCurvatureOperatorAt (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) : E3 →L[ℝ] E3 :=
  (traceNormalizedCurvatureOperatorMatrixAt g x B).toEuclideanLin.toContinuousLinearMap

theorem traceNormalizedCurvatureOperatorMatrixAt_apply (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (i j : Fin 3) :
    traceNormalizedCurvatureOperatorMatrixAt g x B i j =
      2 * metricRm04StandardAt g x (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
        (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1) := rfl

theorem traceNormalizedCurvatureOperatorAt_apply (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (v : E3) :
    traceNormalizedCurvatureOperatorAt g x B v =
      (2 : ℝ) • (curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x)).toEuclideanLin v := by
  change Matrix.toEuclideanLin ((2 : ℝ) • _) v = _
  rw [map_smul, LinearMap.smul_apply]

theorem traceNormalizedCurvatureOperatorAt_isSelfAdjoint (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    IsSelfAdjoint (traceNormalizedCurvatureOperatorAt g x B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  change (Matrix.toEuclideanLin ((2 : ℝ) •
    curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x))).IsSymmetric
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((curvatureOperatorMatrixAt_isHermitian x B (metricAlgebraicCurvatureTensorAt g x)).smul
      (by simp : IsSelfAdjoint (2 : ℝ)))

theorem traceNormalizedCurvatureOperatorAt_inner_self (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (v : E3) :
    ⟪traceNormalizedCurvatureOperatorAt g x B v, v⟫_ℝ =
      2 * ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        metricRm04StandardAt g x (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
          (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1) := by
  rw [traceNormalizedCurvatureOperatorAt_apply, real_inner_smul_left]
  congr 1
  exact (curvatureOperatorMatrixAt_quad_eq_inner x B
    (metricAlgebraicCurvatureTensorAt g x) v.ofLp).symm

private theorem rayleigh_lower (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (v : E3) :
    2 * orderedSectionalCurvaturesAt x B (metricAlgebraicCurvatureTensorAt g x) 2 * ‖v‖ ^ 2 ≤
      ⟪traceNormalizedCurvatureOperatorAt g x B v, v⟫_ℝ := by
  have h := curvatureOperatorMatrixAt_rayleigh_lower x B
    (metricAlgebraicCurvatureTensorAt g x) v.ofLp
  rw [curvatureOperatorMatrixAt_quad_eq_inner] at h
  have hn : (∑ i : Fin 3, v.ofLp i ^ 2) = ‖v‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq v).symm
  rw [hn] at h
  change orderedSectionalCurvaturesAt x B (metricAlgebraicCurvatureTensorAt g x) 2 * ‖v‖ ^ 2 ≤
    ⟪(curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x)).toEuclideanLin v, v⟫_ℝ at h
  rw [traceNormalizedCurvatureOperatorAt_apply, real_inner_smul_left]
  nlinarith [h]

private theorem exists_minimizing_vector (g : SmoothRiemannianMetric I M)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    ∃ v : E3, ‖v‖ = 1 ∧ traceNormalizedCurvatureOperatorAt g x B v =
      (2 * orderedSectionalCurvaturesAt x B (metricAlgebraicCurvatureTensorAt g x) 2) • v := by
  let A := curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x)
  let hA := curvatureOperatorMatrixAt_isHermitian x B (metricAlgebraicCurvatureTensorAt g x)
  let T : E3 →ₗ[ℝ] E3 := A.toEuclideanLin
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let hn : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace
  let b := hT.eigenvectorBasis hn
  refine ⟨b 2, b.orthonormal.1 2, ?_⟩
  rw [traceNormalizedCurvatureOperatorAt_apply]
  change (2 : ℝ) • T (b 2) = _
  rw [hT.apply_eigenvectorBasis hn 2, smul_smul]
  rfl

theorem iInf_rayleigh_traceNormalizedCurvatureOperatorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B) :
    (⨅ v : {v : E3 // v ≠ 0}, (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient v) =
      2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) := by
  rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin g x B hB]
  obtain ⟨v, hv, heig⟩ := exists_minimizing_vector g x B
  rw [(traceNormalizedCurvatureOperatorAt g x B).iInf_rayleigh_eq_iInf_rayleigh_sphere
    (by norm_num : (0 : ℝ) < 1)]
  have hval : (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient v =
      2 * orderedSectionalCurvaturesAt x B (metricAlgebraicCurvatureTensorAt g x) 2 := by
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      heig, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, one_pow, mul_one, div_one,
      RCLike.re_to_real]
  rw [← hval]
  apply IsMinOn.iInf_eq (mem_sphere_zero_iff_norm.mpr hv)
  intro w hw
  change (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient v ≤
    (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient w
  rw [hval]
  have h := rayleigh_lower g x B w
  have hn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    hn, one_pow, mul_one, div_one, RCLike.re_to_real] using h

theorem iInf_rayleigh_traceNormalizedCurvatureOperatorAt_basis_independent
    (g : SmoothRiemannianMetric I M) (x : M)
    (B C : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B) (hC : OrthonormalBasisAt g x C) :
    (⨅ v : {v : E3 // v ≠ 0}, (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient v) =
      ⨅ v : {v : E3 // v ≠ 0}, (traceNormalizedCurvatureOperatorAt g x C).rayleighQuotient v := by
  rw [iInf_rayleigh_traceNormalizedCurvatureOperatorAt g x B hB,
    iInf_rayleigh_traceNormalizedCurvatureOperatorAt g x C hC]

theorem sum_sq_traceNormalizedCurvatureOperatorMatrixAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B) :
    (∑ i : Fin 3, ∑ j : Fin 3, (traceNormalizedCurvatureOperatorMatrixAt g x B i j) ^ 2) =
      normSq0S g x 4 (metricRm04 g x) := by
  let A := metricAlgebraicCurvatureTensorAt g x
  have h := inner0S_algebraic_eq_four_mul_operatorInner g x B hB A A
  change normSq0S g x 4 (metricRm04 g x) =
    4 * ∑ i : Fin 3, ∑ j : Fin 3,
      curvatureOperatorMatrixAt x B A i j * curvatureOperatorMatrixAt x B A i j at h
  rw [h]
  change (∑ i : Fin 3, ∑ j : Fin 3, (2 * curvatureOperatorMatrixAt x B A i j) ^ 2) = _
  simp_rw [show ∀ a : ℝ, (2 * a) ^ 2 = 4 * (a * a) by intro a; ring]
  simp only [Finset.mul_sum]

variable [I.Boundaryless] [BoundarylessManifold I M]

theorem trace_traceNormalizedCurvatureOperatorMatrixAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B) :
    (traceNormalizedCurvatureOperatorMatrixAt g x B).trace = metricScalarAt g x := by
  classical
  have hd : Module.finrank ℝ E = 3 := by
    change Module.finrank ℝ (TangentSpace I x) = 3
    simpa using Module.finrank_eq_card_basis B
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hd]; norm_num⟩
  let e : Fin (Module.finrank ℝ E) ≃ Fin 3 := finCongr hd
  have hB' (i j : Fin (Module.finrank ℝ E)) :
      g.inner x (B (e i)) (B (e j)) = if i = j then (1 : ℝ) else 0 := by
    rw [hB]
    simp only [delta3, Equiv.apply_eq_iff_eq]
  have hs := metricScalarAt_eq_sum_metricRm04StandardAt g x (fun i => B (e i)) hB'
  have hsum : (∑ i, ∑ j, metricRm04StandardAt g x (B (e j)) (B (e i)) (B (e i)) (B (e j))) =
      ∑ i : Fin 3, ∑ j : Fin 3, metricRm04StandardAt g x (B j) (B i) (B i) (B j) := by
    calc
      _ = ∑ i, ∑ j : Fin 3, metricRm04StandardAt g x (B j) (B (e i)) (B (e i)) (B j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact e.sum_comp (fun j => metricRm04StandardAt g x (B j) (B (e i)) (B (e i)) (B j))
      _ = _ := e.sum_comp (fun i => ∑ j : Fin 3, metricRm04StandardAt g x (B j) (B i) (B i) (B j))
  rw [hsum] at hs
  let A := metricAlgebraicCurvatureTensorAt g x
  have hdiag (i : Fin 3) : metricRm04StandardAt g x (B i) (B i) (B i) (B i) = 0 := by
    have h := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp A.2).1
      (B i) (B i) (B i) (B i)
    change metricRm04StandardAt g x (B i) (B i) (B i) (B i) =
      -metricRm04StandardAt g x (B i) (B i) (B i) (B i) at h
    linarith
  have hswap (i j : Fin 3) : metricRm04StandardAt g x (B j) (B i) (B i) (B j) =
      metricRm04StandardAt g x (B i) (B j) (B j) (B i) :=
    tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule A.2 (B j) (B i) (B i) (B j)
  rw [hs, Matrix.trace]
  simp only [Matrix.diag, traceNormalizedCurvatureOperatorMatrixAt_apply, Fin.sum_univ_three,
    bivectorIndex3, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  rw [hdiag, hdiag, hdiag, hswap 0 1, hswap 0 2, hswap 1 2]
  ring

end DifferentialGeometry.Geometry.Curvature
