import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Curvature.QuadraticContraction

set_option autoImplicit false

noncomputable section

namespace Matrix

def secondElementarySymmetric {n : Type*} [Fintype n]
    (A : Matrix n n Real) : Real :=
  (A.trace ^ 2 - (A * A).trace) / 2

theorem adjugate_fin_three_eq_sq_sub_trace_smul_add_secondElementarySymmetric
    (A : Matrix (Fin 3) (Fin 3) Real) :
    A.adjugate = A * A - A.trace • A + A.secondElementarySymmetric • 1 := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondElementarySymmetric, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

end Matrix

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

def traceNormalizedCurvatureOperatorMatrix3
    (A : Matrix (Fin 3) (Fin 3) Real) : Matrix (Fin 3) (Fin 3) Real :=
  (2 : Real) • A

theorem traceNormalizedCurvatureOperatorMatrix3_smul_one (k : Real) :
    traceNormalizedCurvatureOperatorMatrix3 (k • (1 : Matrix (Fin 3) (Fin 3) Real)) =
      (2 * k) • 1 := by
  ext i j
  simp [traceNormalizedCurvatureOperatorMatrix3]
  ring

theorem traceNormalizedCurvatureOperatorMatrix3_trace
    (A : Matrix (Fin 3) (Fin 3) Real) :
    (traceNormalizedCurvatureOperatorMatrix3 A).trace = 2 * A.trace := by
  rw [traceNormalizedCurvatureOperatorMatrix3, Matrix.trace_smul]
  rfl

noncomputable def traceNormalizedCurvatureOperatorMatrixAt
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Matrix (Fin 3) (Fin 3) Real :=
  traceNormalizedCurvatureOperatorMatrix3
    (curvatureOperatorMatrixAt (I := I) x basis A)

@[simp] theorem traceNormalizedCurvatureOperatorMatrixAt_apply
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (i j : Fin 3) :
    traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A i j =
      2 * tensor04StdAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) := by
  rfl

theorem traceNormalizedCurvatureOperatorMatrixAt_trace_eq_twice_sectionalSum
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A).trace =
      2 * ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M)
          (A : Tensor04At (I := I) (M := M) x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
  rw [traceNormalizedCurvatureOperatorMatrixAt,
    traceNormalizedCurvatureOperatorMatrix3_trace,
    curvatureOperatorMatrixAt_trace_eq_sectionalSum]

theorem traceNormalizedCurvatureOperatorMatrixAt_isHermitian
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A).IsHermitian :=
  (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).smul (by rfl)

theorem traceNormalizedCurvatureOperatorMatrixAt_eigenvalues
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (traceNormalizedCurvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ =
      (2 : Real) • orderedSectionalCurvaturesAt (I := I) x basis A := by
  exact DifferentialGeometry.Analysis.Convex.eigenvalues₀_smul_of_nonneg
    (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A) (by norm_num)
    (traceNormalizedCurvatureOperatorMatrixAt_isHermitian (I := I) x basis A)

theorem traceNormalizedCurvatureOperatorMatrixAt_least_eigenvalue
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (traceNormalizedCurvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ 2 =
      2 * leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
  rw [traceNormalizedCurvatureOperatorMatrixAt_eigenvalues,
    leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (I := I) g x basis horth]
  rfl

section MetricNormalization

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [T2Space M]

noncomputable def traceNormalizedMetricCurvatureOperatorMatrixAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    Matrix (Fin 3) (Fin 3) Real :=
  traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x)

theorem traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    (traceNormalizedMetricCurvatureOperatorMatrixAt (I := I) (M := M) g x basis).trace =
      metricScalarAt (I := I) (M := M) g x := by
  rw [traceNormalizedMetricCurvatureOperatorMatrixAt,
    traceNormalizedCurvatureOperatorMatrixAt_trace_eq_twice_sectionalSum]
  rw [metricScalarAt_def]
  have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis delta3 hinv]
  let K := metricCurvData (I := I) (M := M) g
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) (M := M) g x)
      (metricRm04 (I := I) (M := M) g x) :=
    rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.rm13Realizes K.rm04Realizes x
  have hTrace : RicciRealizesRm04FirstTraceAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x) delta3 basis := by
    exact ricciFirstTraceAt_of_rm13 (I := I) g basis delta3 hinv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm13At (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x)
      (metricRicciAt_eq_trace (I := I) (M := M) g x) hLower
  simp only [delta3, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  conv_rhs => rw [Fin.sum_univ_three]
  rw [hTrace 0 0, hTrace 1 1, hTrace 2 2]
  simp only [metricAlgebraicCurvatureTensorAt_coe, tensor04StdAt_apply,
    Fin.sum_univ_three, delta3, bivectorIndex3, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, one_mul, zero_mul]
  have hsymm := metricRm04At_mem_algebraicCurvatureTensorSubmodule
    (I := I) (M := M) g x
  have hpair := tensor04StdAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule
    hsymm
  have hcurv := mem_algebraicCurvatureTensorSubmodule.mp hsymm
  have h00 : metricRm04At (I := I) (M := M) g x
      (vec4 (basis 0) (basis 0) (basis 0) (basis 0)) = 0 := by
    have h := hcurv.anti_first (basis 0) (basis 0) (basis 0) (basis 0)
    change metricRm04At (I := I) (M := M) g x
      (vec4 (basis 0) (basis 0) (basis 0) (basis 0)) =
        -metricRm04At (I := I) (M := M) g x
          (vec4 (basis 0) (basis 0) (basis 0) (basis 0)) at h
    linarith
  have h11 : metricRm04At (I := I) (M := M) g x
      (vec4 (basis 1) (basis 1) (basis 1) (basis 1)) = 0 := by
    have h := hcurv.anti_first (basis 1) (basis 1) (basis 1) (basis 1)
    change metricRm04At (I := I) (M := M) g x
      (vec4 (basis 1) (basis 1) (basis 1) (basis 1)) =
        -metricRm04At (I := I) (M := M) g x
          (vec4 (basis 1) (basis 1) (basis 1) (basis 1)) at h
    linarith
  have h22 : metricRm04At (I := I) (M := M) g x
      (vec4 (basis 2) (basis 2) (basis 2) (basis 2)) = 0 := by
    have h := hcurv.anti_first (basis 2) (basis 2) (basis 2) (basis 2)
    change metricRm04At (I := I) (M := M) g x
      (vec4 (basis 2) (basis 2) (basis 2) (basis 2)) =
        -metricRm04At (I := I) (M := M) g x
          (vec4 (basis 2) (basis 2) (basis 2) (basis 2)) at h
    linarith
  have h10 : metricRm04At (I := I) (M := M) g x
      (vec4 (basis 1) (basis 0) (basis 0) (basis 1)) =
        metricRm04At (I := I) (M := M) g x
          (vec4 (basis 0) (basis 1) (basis 1) (basis 0)) := by
    simpa [tensor04StdAt] using hpair (basis 1) (basis 0) (basis 0) (basis 1)
  have h20 : metricRm04At (I := I) (M := M) g x
      (vec4 (basis 2) (basis 0) (basis 0) (basis 2)) =
        metricRm04At (I := I) (M := M) g x
          (vec4 (basis 0) (basis 2) (basis 2) (basis 0)) := by
    simpa [tensor04StdAt] using hpair (basis 2) (basis 0) (basis 0) (basis 2)
  have h21 : metricRm04At (I := I) (M := M) g x
      (vec4 (basis 2) (basis 1) (basis 1) (basis 2)) =
        metricRm04At (I := I) (M := M) g x
          (vec4 (basis 1) (basis 2) (basis 2) (basis 1)) := by
    simpa [tensor04StdAt] using hpair (basis 2) (basis 1) (basis 1) (basis 2)
  rw [h00, h11, h22, h10, h20, h21]
  ring

end MetricNormalization

theorem curvatureOperatorReaction3_traceNormalizedCurvatureOperatorMatrix3
    (A : Matrix (Fin 3) (Fin 3) Real) :
    curvatureOperatorReaction3 (traceNormalizedCurvatureOperatorMatrix3 A) =
      (2 : Real) • hamiltonIveyMatrixReaction A := by
  calc
    curvatureOperatorReaction3 (traceNormalizedCurvatureOperatorMatrix3 A) =
        (4 : Real) • curvatureOperatorReaction3 A := by
      unfold curvatureOperatorReaction3 traceNormalizedCurvatureOperatorMatrix3
      rw [Matrix.adjugate_smul, Matrix.smul_mul, Matrix.mul_smul]
      norm_num [smul_add, smul_smul]
    _ = (2 : Real) • hamiltonIveyMatrixReaction A := by
      have hham : hamiltonIveyMatrixReaction A =
          (2 : Real) • curvatureOperatorReaction3 A := by
        unfold hamiltonIveyMatrixReaction curvatureOperatorReaction3
        norm_num [two_smul]
      rw [hham]
      norm_num [smul_smul]

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Dim3Reaction
open DifferentialGeometry.PDE.RicciFlow
open scoped BigOperators

theorem curvatureOperatorReaction3_apply_eq_negative_b_comp
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hR : AlgebraicCurvatureSymmetries3 R) (i j : Fin 3) :
    curvatureOperatorReaction3
        (fun p q => 2 * R (bivectorIndex3 p).1 (bivectorIndex3 p).2
          (bivectorIndex3 q).2 (bivectorIndex3 q).1) i j =
      let a := (bivectorIndex3 i).1
      let b := (bivectorIndex3 i).2
      let c := (bivectorIndex3 j).2
      let d := (bivectorIndex3 j).1
      4 * ((-bComp delta3 R a b c d) - (-bComp delta3 R a b d c) +
        (-bComp delta3 R a c b d) - (-bComp delta3 R a d b c)) := by
  let Ric := fun p q => -stdRicci3 R p q
  have hRic : ∀ p q, Ric p q = Ric q p := by
    intro p q
    dsimp [Ric, stdRicci3]
    rw [hR.block_symm 0 q 0 p, hR.block_symm 1 q 1 p, hR.block_symm 2 q 2 p]
  have hrep : R = rm Ric := by
    funext a b c d
    rw [stdRiemannFromRicci3D_of_algebraic_curvature_symmetries hR]
    dsimp [stdRiemannFromRicciRhs3, rm, Ric, kd, delta3, sc, stdScalar3]
    ring
  have hB (a b c d : Fin 3) : bComp delta3 R a b c d = Bt Ric a b c d := by
    rw [hrep]
    simp [bComp, delta3, Bt]
  have hnorm := congrFun (congrFun
    (curvatureOperatorReaction3_traceNormalizedCurvatureOperatorMatrix3
      (curvatureOperatorMatrixOfRicci Ric)) i) j
  rw [← curvatureOperatorReactionMatrix_eq_hamiltonIveyMatrixReaction Ric hRic] at hnorm
  change curvatureOperatorReaction3
      (fun p q => 2 * rm Ric (bivectorIndex3 p).1 (bivectorIndex3 p).2
        (bivectorIndex3 q).2 (bivectorIndex3 q).1) i j =
    2 * (-2 * Bsharp Ric (bivectorIndex3 i).1 (bivectorIndex3 i).2
      (bivectorIndex3 j).2 (bivectorIndex3 j).1) at hnorm
  rw [← hrep] at hnorm
  rw [hnorm]
  dsimp only
  rw [hB, hB, hB, hB]
  unfold Bsharp
  ring

end DifferentialGeometry.Geometry.Curvature.DimensionThree
