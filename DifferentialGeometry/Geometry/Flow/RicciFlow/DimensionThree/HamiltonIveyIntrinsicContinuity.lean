import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyIntrinsicTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyRegionInfDist
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyBundleRegion
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators
open scoped Matrix.Norms.Frobenius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable def intrinsicFiberCurvatureOperatorMatrix {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (A : Tensor04At (I := I) (M := M) x) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    tensor04StdAt (I := I) (M := M) A
      (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem intrinsicFiberCurvatureOperatorMatrix_apply {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (A : Tensor04At (I := I) (M := M) x) (i j : Fin 3) :
    intrinsicFiberCurvatureOperatorMatrix (I := I) basis A i j =
      tensor04StdAt (I := I) (M := M) A
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    intrinsicFiberCurvatureOperatorMatrix (I := I) basis
        (A : Tensor04At (I := I) (M := M) x) =
      curvatureOperatorMatrixAt (I := I) x basis A := by
  rfl

noncomputable def intrinsicFiberHamiltonIveyRegion
    (basis : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (K τ : ℝ) (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {A | A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x ∧
    matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basis x) A) ∈
      hamiltonIveyConvexMatrixRegionEuclid K τ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem mem_intrinsicFiberHamiltonIveyRegion
    (basis : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (K τ : ℝ) (x : M) (A : Tensor04At (I := I) (M := M) x) :
    A ∈ intrinsicFiberHamiltonIveyRegion (I := I) basis K τ x ↔
      A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x ∧
        matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basis x) A) ∈
          hamiltonIveyConvexMatrixRegionEuclid K τ := by
  rfl

noncomputable def tensor04FiberNorm (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x) : ℝ :=
  Real.sqrt (normSq0S (I := I) g x 4 A)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberCurvatureOperatorMatrix_sub {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (A B : Tensor04At (I := I) (M := M) x) :
    intrinsicFiberCurvatureOperatorMatrix (I := I) basis (A - B) =
      intrinsicFiberCurvatureOperatorMatrix (I := I) basis A -
        intrinsicFiberCurvatureOperatorMatrix (I := I) basis B := by
  ext i j
  unfold intrinsicFiberCurvatureOperatorMatrix
  change (A - B) (vec4 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1)) =
    A (vec4 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1)) -
    B (vec4 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1))
  exact Tensor0SSpace.sub_apply 4 x A B
    (vec4 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1))

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem tensor04_fiberNormSq_eq_normSq0S
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) g x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
    ‖A‖ ^ 2 = normSq0S (I := I) g x 4 A := by
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  rw [normSq0S]
  rw [← tensor04_fiberInner_eq (I := I) g x A A]
  rw [norm_sq_eq_re_inner (𝕜 := ℝ) A]
  simp

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem tensor04FiberNorm_eq_norm
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) g x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
    tensor04FiberNorm g x A = ‖A‖ := by
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  unfold tensor04FiberNorm
  rw [← tensor04_fiberNormSq_eq_normSq0S (I := I) g x A]
  exact Real.sqrt_sq (norm_nonneg A)

omit [SigmaCompactSpace M] in
theorem pulledRm_normSq_eq_rm_normSq
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    normSq0S (I := I) (S.base.metric 0) x 4 (uhlenbeckPulledRm04At S basisAt iota t x) =
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) := by
  have hinner := fiberInner_compUhlenbeck_isometry (I := I) (M := M) hT S basisAt iota hiota0
    hgram horth0 ht x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x⟩
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x⟩
  unfold normSq0S
  exact hinner

omit [SigmaCompactSpace M] in
theorem pulledRm_norm_eq_rm_norm
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    tensor04FiberNorm (S.base.metric 0) x (uhlenbeckPulledRm04At S basisAt iota t x) =
      tensor04FiberNorm (S.base.metric t) x (S.base.rm04 t x) := by
  unfold tensor04FiberNorm
  congr 1
  exact pulledRm_normSq_eq_rm_normSq (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x

private lemma matrixInner_eq_sum
    (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    inner ℝ (matrixToEuclid M) (matrixToEuclid N) =
      ∑ p : Fin 3, ∑ q : Fin 3, M p q * N p q := by
  rw [inner_matrixToEuclid (matrixToEuclid M) N]
  rw [Fintype.sum_prod_type]
  simp [matrixToEuclid]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_algebraic_eq_four_mul_matrixInner
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)
        (B : Tensor04At (I := I) (M := M) x) =
      4 * inner ℝ
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (A : Tensor04At (I := I) (M := M) x)))
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (B : Tensor04At (I := I) (M := M) x))) := by
  have h1 := inner0S_algebraic_eq_four_mul_operatorInner (I := I) (M := M) g x basis horth A B
  calc
    inner0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)
        (B : Tensor04At (I := I) (M := M) x)
        = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
            curvatureOperatorMatrixAt (I := I) x basis A p q *
              curvatureOperatorMatrixAt (I := I) x basis B p q) := h1
    _ = 4 * inner ℝ
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (A : Tensor04At (I := I) (M := M) x)))
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (B : Tensor04At (I := I) (M := M) x))) := by
          congr 1
          rw [intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt,
            intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt]
          exact (matrixInner_eq_sum
            (curvatureOperatorMatrixAt (I := I) x basis A)
            (curvatureOperatorMatrixAt (I := I) x basis B)).symm

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberDist_eq_two_mul_matrixDist_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) g x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
    dist (A : Tensor04At (I := I) (M := M) x) (B : Tensor04At (I := I) (M := M) x) =
      2 * dist
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (A : Tensor04At (I := I) (M := M) x)))
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (B : Tensor04At (I := I) (M := M) x))) := by
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  let FA : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (A : Tensor04At (I := I) (M := M) x))
  let FB : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (B : Tensor04At (I := I) (M := M) x))
  have hAlg : (A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
    exact Submodule.sub_mem (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A.2 B.2
  have hFA : FA - FB = matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis
      ((A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x))) := by
    dsimp [FA, FB]
    rw [← matrixToEuclid_sub]
    rw [← intrinsicFiberCurvatureOperatorMatrix_sub (I := I) basis
      (A : Tensor04At (I := I) (M := M) x) (B : Tensor04At (I := I) (M := M) x)]
    rfl
  have hnorm : ‖(A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x)‖ ^ 2 =
      (2 * ‖FA - FB‖) ^ 2 := by
    calc
      ‖(A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x)‖ ^ 2
          = normSq0S (I := I) g x 4
              ((A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x)) := by
            exact tensor04_fiberNormSq_eq_normSq0S (I := I) g x
              ((A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x))
      _ = 4 * inner ℝ
            (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis
              ((A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x))))
            (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis
              ((A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x)))) := by
            rw [normSq0S]
            exact inner0S_algebraic_eq_four_mul_matrixInner (I := I) (M := M) g x basis horth
              ⟨(A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x), hAlg⟩
              ⟨(A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x), hAlg⟩
      _ = 4 * inner ℝ (FA - FB) (FA - FB) := by
            rw [hFA]
      _ = (2 * ‖FA - FB‖) ^ 2 := by
            rw [show inner ℝ (FA - FB) (FA - FB) = ‖FA - FB‖ ^ 2 by
              rw [norm_sq_eq_re_inner (𝕜 := ℝ) (FA - FB)]
              simp]
            ring
  rw [dist_eq_norm, dist_eq_norm]
  have h := (sq_eq_sq_iff_abs_eq_abs (‖(A : Tensor04At (I := I) (M := M) x) - (B : Tensor04At (I := I) (M := M) x)‖) (2 * ‖FA - FB‖)).mp hnorm
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg (FA - FB)))] at h
  exact h

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorMatrixAt_eq_zero_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : curvatureOperatorMatrixAt (I := I) x basis A = 0) :
    A = 0 := by
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  have h0 : matrixToEuclid
      (intrinsicFiberCurvatureOperatorMatrix (I := I) basis
        ((0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x)) = 0 := by
    ext ij
    simp [matrixToEuclid]
    rfl
  have hA' : matrixToEuclid
      (intrinsicFiberCurvatureOperatorMatrix (I := I) basis (A : Tensor04At (I := I) (M := M) x)) = 0 := by
    rw [intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt]
    rw [hA]
    simp [matrixToEuclid]
    rfl
  have h := intrinsicFiberDist_eq_two_mul_matrixDist_of_orthonormal (I := I) (M := M) g x basis horth
    A (0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
  rw [hA', h0] at h
  have hdist : dist (A : Tensor04At (I := I) (M := M) x)
      ((0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x) = 0 := by
    rw [h]
    simp
  exact Subtype.ext (dist_eq_zero.mp hdist)




noncomputable def intrinsicFiberBivectorTwoForm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (i : Fin 3) (X Y : TangentSpace I x) : ℝ :=
  (g.inner x X (basis (bivectorIndex3 i).1)) * (g.inner x Y (basis (bivectorIndex3 i).2)) -
    (g.inner x X (basis (bivectorIndex3 i).2)) * (g.inner x Y (basis (bivectorIndex3 i).1))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberBivectorTwoForm_anti
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (i : Fin 3) (X Y : TangentSpace I x) :
    intrinsicFiberBivectorTwoForm (I := I) g basis i X Y =
      -intrinsicFiberBivectorTwoForm (I := I) g basis i Y X := by
  unfold intrinsicFiberBivectorTwoForm
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicFiberBivectorTwoForm_add_left
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (p : Fin 3) (x₁ x₂ y : TangentSpace I x) :
    intrinsicFiberBivectorTwoForm (I := I) g basis p (x₁ + x₂) y =
      intrinsicFiberBivectorTwoForm (I := I) g basis p x₁ y +
        intrinsicFiberBivectorTwoForm (I := I) g basis p x₂ y := by
  unfold intrinsicFiberBivectorTwoForm
  rw [(g.inner x).map_add x₁ x₂]
  simp
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicFiberBivectorTwoForm_add_right
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (p : Fin 3) (X y₁ y₂ : TangentSpace I x) :
    intrinsicFiberBivectorTwoForm (I := I) g basis p X (y₁ + y₂) =
      intrinsicFiberBivectorTwoForm (I := I) g basis p X y₁ +
        intrinsicFiberBivectorTwoForm (I := I) g basis p X y₂ := by
  unfold intrinsicFiberBivectorTwoForm
  rw [(g.inner x).map_add y₁ y₂]
  simp
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicFiberBivectorTwoForm_smul_left
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (p : Fin 3) (a : ℝ) (x₁ y : TangentSpace I x) :
    intrinsicFiberBivectorTwoForm (I := I) g basis p (a • x₁) y =
      a * intrinsicFiberBivectorTwoForm (I := I) g basis p x₁ y := by
  unfold intrinsicFiberBivectorTwoForm
  rw [(g.inner x).map_smul a x₁]
  simp
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicFiberBivectorTwoForm_smul_right
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (p : Fin 3) (a : ℝ) (X y₁ : TangentSpace I x) :
    intrinsicFiberBivectorTwoForm (I := I) g basis p X (a • y₁) =
      a * intrinsicFiberBivectorTwoForm (I := I) g basis p X y₁ := by
  unfold intrinsicFiberBivectorTwoForm
  rw [(g.inner x).map_smul a y₁]
  simp
  ring

noncomputable def intrinsicFiberOperatorTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) : Tensor04At (I := I) (M := M) x :=
  { toMultilinearMap := MultilinearMap.mk' (R := ℝ) (M₁ := fun _ : Fin 4 => TangentSpace I x) (M₂ := ℝ)
      (fun m : Fin 4 → TangentSpace I x =>
        ∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
            intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2))
      (by
        intro m i x y
        fin_cases i
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (x + y) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p x (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p y (m 1) *
                  intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_add_left]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (x + y) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) x *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) y *
                  intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_add_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (x + y)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) x) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                  intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) y)
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_add_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (x + y) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q x (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                  intrinsicFiberBivectorTwoForm (I := I) g basis q y (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_add_left]
          ring)
      (by
        intro m i c x
        fin_cases i
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (c • x) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p x (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_smul_left]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (c • x) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) x *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_smul_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) (c • x)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (m 3) x)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_smul_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q (c • x) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (m 0) (m 1) *
                intrinsicFiberBivectorTwoForm (I := I) g basis q x (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [intrinsicFiberBivectorTwoForm_smul_left]
          ring)
    cont := by
      unfold intrinsicFiberBivectorTwoForm
      fun_prop }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberOperatorTensor_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) (intrinsicFiberOperatorTensor (I := I) g basis Rmat) X Y Z W =
      ∑ p : Fin 3, ∑ q : Fin 3,
        Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p X Y *
          intrinsicFiberBivectorTwoForm (I := I) g basis q W Z := by
  unfold tensor04StdAt intrinsicFiberOperatorTensor
  change (∑ p : Fin 3, ∑ q : Fin 3,
      Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p (vec4 X Y Z W 0) (vec4 X Y Z W 1) *
        intrinsicFiberBivectorTwoForm (I := I) g basis q (vec4 X Y Z W 3) (vec4 X Y Z W 2)) =
    ∑ p : Fin 3, ∑ q : Fin 3,
      Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p X Y *
        intrinsicFiberBivectorTwoForm (I := I) g basis q W Z
  simp [vec4]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberBivectorTwoForm_onBasis
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (p a b : Fin 3) :
    intrinsicFiberBivectorTwoForm (I := I) g basis p (basis a) (basis b) =
      if a = b then 0 else (if (a, b) = bivectorIndex3 p then 1 else if (b, a) = bivectorIndex3 p then -1 else 0) := by
  classical
  have horth' : ∀ i j : Fin 3, g.inner x (basis i) (basis j) = delta3 i j := horth
  fin_cases p <;> fin_cases a <;> fin_cases b <;>
    simp [intrinsicFiberBivectorTwoForm, bivectorIndex3, delta3, horth']

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicFiberCurvatureOperatorMatrix_of_intrinsicFiberOperatorTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) :
    intrinsicFiberCurvatureOperatorMatrix (I := I) basis
        (intrinsicFiberOperatorTensor (I := I) g basis Rmat) = Rmat := by
  classical
  ext i j
  rw [intrinsicFiberCurvatureOperatorMatrix_apply, intrinsicFiberOperatorTensor_apply]
  have horth' : ∀ i j : Fin 3, g.inner x (basis i) (basis j) = delta3 i j := horth
  have h1 : ∀ p : Fin 3,
      intrinsicFiberBivectorTwoForm (I := I) g basis p
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2) = if p = i then 1 else 0 := by
    intro p
    fin_cases p <;> fin_cases i <;>
      simp [intrinsicFiberBivectorTwoForm, bivectorIndex3, delta3, horth']
  have h2 : ∀ q : Fin 3,
      intrinsicFiberBivectorTwoForm (I := I) g basis q
        (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2) = if q = j then 1 else 0 := by
    intro q
    fin_cases q <;> fin_cases j <;>
      simp [intrinsicFiberBivectorTwoForm, bivectorIndex3, delta3, horth']
  simp [h1, h2]


variable [NeZero (Module.finrank ℝ E)]

open DifferentialGeometry.Integral.Measure

private noncomputable def intrinsicChartFrameNormFiber
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  let v : TangentSpace I b := chartBasisVecFiber (I := I) α i b
  let raw : TangentSpace I b :=
    v - ∑ j : Fin i.val,
      (g.inner b v
          (intrinsicChartFrameNormFiber g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        intrinsicChartFrameNormFiber g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩
  (Real.sqrt (g.inner b raw raw))⁻¹ • raw
termination_by i.val
decreasing_by exact j.isLt

noncomputable def intrinsicChartFrameNorm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) : TangentSpace I b :=
  intrinsicChartFrameNormFiber (I := I) g α b i

private noncomputable def intrinsicChartFrameRawFiber
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  chartBasisVecFiber (I := I) α i b -
    ∑ j : Fin i.val,
      (g.inner b (chartBasisVecFiber (I := I) α i b)
          (intrinsicChartFrameNormFiber g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        intrinsicChartFrameNormFiber g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicChartFrame_g_inner_sum_right
    (g : SmoothRiemannianMetric I M) (b : M)
    (v : TangentSpace I b)
    {ι : Type*} (s : Finset ι) (w : ι → TangentSpace I b)
    (c : ι → ℝ) :
    g.inner b v (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * g.inner b v (w k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) v) (c a • w a + ∑ x ∈ s, c x • w x) =
        ((g.inner b) v) (c a • w a) + ((g.inner b) v) (∑ x ∈ s, c x • w x) from by
      rw [map_add]]
    rw [show ((g.inner b) v) (c a • w a) = c a * ((g.inner b) v) (w a) from by
      rw [map_smul]; rfl]
    rw [ih]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicChartFrameNormFiber_eq
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    intrinsicChartFrameNormFiber (I := I) g α b i =
      (Real.sqrt (g.inner b
          (intrinsicChartFrameRawFiber (I := I) g α b i)
          (intrinsicChartFrameRawFiber (I := I) g α b i)))⁻¹ •
        intrinsicChartFrameRawFiber (I := I) g α b i := by
  unfold intrinsicChartFrameNormFiber intrinsicChartFrameRawFiber
  rfl

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicChartFrameRawFiber_at_zero
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    intrinsicChartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  unfold intrinsicChartFrameRawFiber
  simp

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicChartFrameNormFiber_at_zero
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    intrinsicChartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      (Real.sqrt
          (g.inner b
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
        chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  rw [intrinsicChartFrameNormFiber_eq, intrinsicChartFrameRawFiber_at_zero]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma intrinsicChartFrameNormFiber_at_zero_norm
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (intrinsicChartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)
        (intrinsicChartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩) = 1 := by
  classical
  rw [intrinsicChartFrameNormFiber_at_zero]
  set v : TangentSpace I b :=
    chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b with hv_def
  have hv_ne_zero : v ≠ 0 := by
    have hLI := chartBasisFamily_linearIndependent (I := I) α hb
    intro hv0
    have : (1 : ℝ) • v = 0 := by rw [one_smul]; exact hv0
    have h := hLI.ne_zero (i := ⟨0, NeZero.pos _⟩)
    exact h hv0
  have hpos : 0 < g.inner b v v := g.pos b v hv_ne_zero
  set N : ℝ := g.inner b v v with hN_def
  set s : ℝ := Real.sqrt N with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hpos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hexpand :
      g.inner b (s⁻¹ • v) (s⁻¹ • v) = s⁻¹ * (s⁻¹ * N) := by
    have h_outer : g.inner b (s⁻¹ • v) = s⁻¹ • g.inner b v := by
      rw [map_smul]
    rw [h_outer]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show g.inner b v (s⁻¹ • v) = s⁻¹ * g.inner b v v from by
      rw [map_smul]; rfl]
  rw [hexpand]
  have hs_sq : s * s = N := by
    rw [hs_def]; exact Real.mul_self_sqrt (le_of_lt hpos)
  have h1 : s⁻¹ * (s⁻¹ * N) = (s * s)⁻¹ * N := by
    rw [mul_inv]; ring
  rw [h1, hs_sq]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private theorem intrinsicChartFrameNormFiber_orth_strong_aux
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      intrinsicChartFrameRawFiber (I := I) g α b i ≠ 0 ∧
      (∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
        g.inner b
            (intrinsicChartFrameNormFiber (I := I) g α b j)
            (intrinsicChartFrameNormFiber (I := I) g α b i) = 0) ∧
      g.inner b
          (intrinsicChartFrameNormFiber (I := I) g α b i)
          (intrinsicChartFrameNormFiber (I := I) g α b i) = 1 := by
  classical
  have hLI : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) :=
    chartBasisFamily_linearIndependent (I := I) α hb
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := by
      apply Fin.ext
      exact hi_val
    subst hi_eq
    refine ⟨?_, ?_, ?_⟩
    · rw [intrinsicChartFrameRawFiber_at_zero]
      exact hLI.ne_zero ⟨0, NeZero.pos _⟩
    · intro j hj
      simp at hj
    · exact intrinsicChartFrameNormFiber_at_zero_norm (I := I) g α hb
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · have hi_eq : i.val = k + 1 := by omega
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          intrinsicChartFrameRawFiber (I := I) g α b j ≠ 0 ∧
          (∀ j' : Fin (Module.finrank ℝ E), j'.val < j.val →
            g.inner b
                (intrinsicChartFrameNormFiber (I := I) g α b j')
                (intrinsicChartFrameNormFiber (I := I) g α b j) = 0) ∧
          g.inner b
              (intrinsicChartFrameNormFiber (I := I) g α b j)
              (intrinsicChartFrameNormFiber (I := I) g α b j) = 1 := by
        intro j hj
        have hj_le : j.val ≤ k := by omega
        exact ih j hj_le
      have horth_raw : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          g.inner b
              (intrinsicChartFrameNormFiber (I := I) g α b j)
              (intrinsicChartFrameRawFiber (I := I) g α b i) = 0 := by
        intro j hj_lt
        rw [show intrinsicChartFrameRawFiber (I := I) g α b i =
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  intrinsicChartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩ from rfl]
        rw [show ((g.inner b) (intrinsicChartFrameNormFiber (I := I) g α b j))
              (chartBasisVecFiber (I := I) α i b -
                ∑ j' : Fin i.val,
                  (g.inner b (chartBasisVecFiber (I := I) α i b)
                      (intrinsicChartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                    intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
            ((g.inner b) (intrinsicChartFrameNormFiber (I := I) g α b j))
              (chartBasisVecFiber (I := I) α i b) -
            ((g.inner b) (intrinsicChartFrameNormFiber (I := I) g α b j))
              (∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  intrinsicChartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) from by
          rw [map_sub]]
        rw [intrinsicChartFrame_g_inner_sum_right (I := I) g b
            (intrinsicChartFrameNormFiber (I := I) g α b j)
            (Finset.univ : Finset (Fin i.val))
            (fun j' => intrinsicChartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
            (fun j' => g.inner b
              (chartBasisVecFiber (I := I) α i b)
              (intrinsicChartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))]
        have hsum_eq :
            ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                g.inner b
                    (chartBasisVecFiber (I := I) α i b)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                  g.inner b
                    (intrinsicChartFrameNormFiber (I := I) g α b j)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
              g.inner b
                (intrinsicChartFrameNormFiber (I := I) g α b j)
                (chartBasisVecFiber (I := I) α i b) := by
          have hj_in_fin : j.val < i.val := hj_lt
          set j_inFin : Fin i.val := ⟨j.val, hj_in_fin⟩
          have hsingleton :
              ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                  g.inner b
                      (chartBasisVecFiber (I := I) α i b)
                      (intrinsicChartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                    g.inner b
                      (intrinsicChartFrameNormFiber (I := I) g α b j)
                      (intrinsicChartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
                g.inner b
                    (chartBasisVecFiber (I := I) α i b)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩) *
                  g.inner b
                    (intrinsicChartFrameNormFiber (I := I) g α b j)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩) := by
            rw [Finset.sum_eq_single j_inFin]
            · intro j' _ hj'
              have hj'_neq : j'.val ≠ j.val := fun h => hj' (Fin.ext h)
              by_cases hcompare : j'.val < j.val
              · have hIH_j := ih_below j hj_lt
                have hzero := hIH_j.2.1 ⟨j'.val, lt_trans hcompare j.isLt⟩ hcompare
                rw [show (g.inner b
                    (intrinsicChartFrameNormFiber (I := I) g α b j)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) =
                  g.inner b
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans hcompare j.isLt⟩)
                    (intrinsicChartFrameNormFiber (I := I) g α b j) from by
                  rw [g.symm]]
                rw [hzero, mul_zero]
              · have hcompare_le : j.val ≤ j'.val := Nat.le_of_not_lt hcompare
                have hcompare' : j.val < j'.val := lt_of_le_of_ne hcompare_le hj'_neq.symm
                have hj'_in : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
                  Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
                have hIH_j' := ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_in
                have hzero := hIH_j'.2.1 j hcompare'
                rw [hzero, mul_zero]
            · intro h
              exact absurd (Finset.mem_univ j_inFin) h
          rw [hsingleton]
          have hIH_j := ih_below j hj_lt
          have hjj_unit : g.inner b
              (intrinsicChartFrameNormFiber (I := I) g α b j)
              (intrinsicChartFrameNormFiber (I := I) g α b j) = 1 := hIH_j.2.2
          have hj_eq : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ :
              Fin (Module.finrank ℝ E)) = j := by
            apply Fin.ext
            rfl
          rw [hj_eq, hjj_unit, mul_one, g.symm]
        rw [hsum_eq]
        ring
      have hraw_ne : intrinsicChartFrameRawFiber (I := I) g α b i ≠ 0 := by
        intro hraw_zero
        have hv_eq : chartBasisVecFiber (I := I) α i b =
            ∑ j' : Fin i.val,
              (g.inner b (chartBasisVecFiber (I := I) α i b)
                (intrinsicChartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                intrinsicChartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
          have h_eq : chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (intrinsicChartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  intrinsicChartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩ = 0 := by
            simpa [intrinsicChartFrameRawFiber] using hraw_zero
          exact sub_eq_zero.mp h_eq
        have h_e_in_span_v : ∀ k : ℕ, ∀ m : Fin (Module.finrank ℝ E),
            m.val ≤ k → m.val < i.val →
            intrinsicChartFrameNormFiber (I := I) g α b m ∈
              Submodule.span ℝ
                ((fun n : Fin i.val =>
                  chartBasisVecFiber (I := I) α
                    ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                  Set.univ) := by
          intro kk
          induction kk with
          | zero =>
            intro m hm_le hm_lt
            have hm_val : m.val = 0 := Nat.le_zero.mp hm_le
            have hm_eq : m = ⟨0, NeZero.pos _⟩ := by
              apply Fin.ext
              exact hm_val
            subst hm_eq
            rw [intrinsicChartFrameNormFiber_at_zero]
            have h0_in_fin : (0 : ℕ) < i.val := hm_lt
            apply Submodule.smul_mem
            apply Submodule.subset_span
            refine ⟨⟨0, h0_in_fin⟩, ?_, rfl⟩
            exact Set.mem_univ _
          | succ kk ih_kk =>
            intro m hm_le hm_lt
            by_cases hcase : m.val ≤ kk
            · exact ih_kk m hcase hm_lt
            · have hm_eq : m.val = kk + 1 := by omega
              rw [intrinsicChartFrameNormFiber_eq]
              apply Submodule.smul_mem
              unfold intrinsicChartFrameRawFiber
              apply Submodule.sub_mem
              · apply Submodule.subset_span
                refine ⟨⟨m.val, hm_lt⟩, ?_, ?_⟩
                · exact Set.mem_univ _
                · rfl
              · apply Submodule.sum_mem
                intro j _
                apply Submodule.smul_mem
                have hj_in_fin : j.val < i.val := lt_trans j.isLt hm_lt
                have hj_le_kk : j.val ≤ kk := by
                  have : j.val < m.val := j.isLt
                  omega
                have hj_lt_total : j.val < Module.finrank ℝ E :=
                  lt_trans hj_in_fin i.isLt
                exact ih_kk ⟨j.val, hj_lt_total⟩ hj_le_kk hj_in_fin
        have hvi_in_span : chartBasisVecFiber (I := I) α i b ∈
            Submodule.span ℝ
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) := by
          rw [hv_eq]
          apply Submodule.sum_mem
          intro j' _
          apply Submodule.smul_mem
          have hj'_lt : j'.val < i.val := j'.isLt
          have hj'_le_k : j'.val ≤ k := by
            have : j'.val < i.val := j'.isLt
            omega
          exact h_e_in_span_v k ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_le_k hj'_lt
        have hcontra : chartBasisVecFiber (I := I) α i b ∉
            Submodule.span ℝ
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) := by
          have hset_eq :
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) =
              ((fun n : Fin (Module.finrank ℝ E) =>
                chartBasisVecFiber (I := I) α n b) ''
                {n : Fin (Module.finrank ℝ E) | n.val < i.val}) := by
            ext v
            constructor
            · rintro ⟨n, _, rfl⟩
              refine ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
            · rintro ⟨n, hn, rfl⟩
              refine ⟨⟨n.val, hn⟩, ?_, rfl⟩
              exact Set.mem_univ _
          rw [hset_eq]
          have hi_notin : i ∉ {n : Fin (Module.finrank ℝ E) | n.val < i.val} := by
            simp [Set.mem_setOf_eq]
          exact hLI.notMem_span_image hi_notin
        exact hcontra hvi_in_span
      have hgpos : 0 < g.inner b
          (intrinsicChartFrameRawFiber (I := I) g α b i)
          (intrinsicChartFrameRawFiber (I := I) g α b i) :=
        g.pos b (intrinsicChartFrameRawFiber (I := I) g α b i) hraw_ne
      set N : ℝ := g.inner b
          (intrinsicChartFrameRawFiber (I := I) g α b i)
          (intrinsicChartFrameRawFiber (I := I) g α b i) with hN_def
      set s : ℝ := Real.sqrt N with hs_def
      have hs_pos : 0 < s := Real.sqrt_pos.mpr hgpos
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hs_sq : s * s = N := Real.mul_self_sqrt (le_of_lt hgpos)
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        have hei_eq : intrinsicChartFrameNormFiber (I := I) g α b i =
            s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i :=
          intrinsicChartFrameNormFiber_eq (I := I) g α b i
        rw [hei_eq]
        rw [show g.inner b (intrinsicChartFrameNormFiber (I := I) g α b j)
              (s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i) =
            s⁻¹ * g.inner b (intrinsicChartFrameNormFiber (I := I) g α b j)
              (intrinsicChartFrameRawFiber (I := I) g α b i) from by
          rw [map_smul]; rfl]
        rw [horth_raw j hj_lt, mul_zero]
      · have hei_eq : intrinsicChartFrameNormFiber (I := I) g α b i =
            s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i :=
          intrinsicChartFrameNormFiber_eq (I := I) g α b i
        rw [hei_eq]
        have hinner_smul :
            g.inner b (s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i)
                (s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i) =
            s⁻¹ * (s⁻¹ * g.inner b
              (intrinsicChartFrameRawFiber (I := I) g α b i)
              (intrinsicChartFrameRawFiber (I := I) g α b i)) := by
          have h1 : g.inner b (s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i) =
              s⁻¹ • g.inner b (intrinsicChartFrameRawFiber (I := I) g α b i) := by
            rw [map_smul]
          rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [show g.inner b (intrinsicChartFrameRawFiber (I := I) g α b i)
                (s⁻¹ • intrinsicChartFrameRawFiber (I := I) g α b i) =
              s⁻¹ * g.inner b (intrinsicChartFrameRawFiber (I := I) g α b i)
                (intrinsicChartFrameRawFiber (I := I) g α b i) from by
            rw [map_smul]; rfl]
        rw [hinner_smul]
        change s⁻¹ * (s⁻¹ * N) = 1
        have h1 : s⁻¹ * (s⁻¹ * N) = (s * s)⁻¹ * N := by rw [mul_inv]; ring
        rw [h1, hs_sq]
        exact inv_mul_cancel₀ (ne_of_gt hgpos)

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicChartFrameNormFiber_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (intrinsicChartFrameNormFiber (I := I) g α b i)
        (intrinsicChartFrameNormFiber (I := I) g α b j) =
      if i = j then 1 else 0 := by
  classical
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have h := intrinsicChartFrameNormFiber_orth_strong_aux (I := I) g α hb j.val j (le_refl _)
    have horth := h.2.1 i hlt
    have hne : i ≠ j := by
      intro h_eq; rw [h_eq] at hlt; omega
    rw [if_neg hne, horth]
  · have hi_eq_j : i = j := Fin.ext heq
    rw [if_pos hi_eq_j, ← hi_eq_j]
    have h := intrinsicChartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    exact h.2.2
  · have h := intrinsicChartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    have horth_ji := h.2.1 j hgt
    have hne : i ≠ j := by
      intro h_eq; rw [h_eq] at hgt; omega
    rw [if_neg hne]
    rw [g.symm]
    exact horth_ji

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicChartFrameNorm_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (intrinsicChartFrameNorm (I := I) g α i b)
        (intrinsicChartFrameNorm (I := I) g α j b) =
      if i = j then 1 else 0 := by
  unfold intrinsicChartFrameNorm
  exact intrinsicChartFrameNormFiber_orthonormal (I := I) g α hb i j
omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
    [T2Space M] [NeZero (Module.finrank ℝ E)] in
private lemma smoothOrthoOpen_subset_baseSet (α : M) :
    smoothOrthoOpen (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  exact fun b hb =>
    smoothOrthoFrameNbhd_subset_baseSet (I := I) (M := M) α (interior_subset hb)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma continuousOn_section_iff_coord
    {α : M} {s : Set (ℝ × M)}
    (hs : ∀ q : ℝ × M, q ∈ s →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : (q : ℝ × M) → TangentSpace I q.2) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q)) s ↔
      ContinuousOn (fun q : ℝ × M =>
        ((trivializationAt E (TangentSpace I) α) ⟨q.2, v q⟩).2) s := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  let f : (q : ℝ × M) → TotalSpace E (fun x : M => TangentSpace I x) :=
    fun q => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q)
  have hsrc : ∀ q : ℝ × M, q ∈ s → f q ∈ e.source := by
    intro q hq
    rw [e.mem_source]
    exact hs q hq
  constructor
  · intro hf
    have hcomp : ContinuousOn (fun q : ℝ × M => e (f q)) s :=
      e.continuousOn.comp hf hsrc
    have hproj : ContinuousOn (fun q : ℝ × M => (e (f q)).2) s :=
      continuous_snd.comp_continuousOn hcomp
    refine hproj.congr ?_
    intro q hq
    rfl
  · intro hc
    have hpair : ContinuousOn (fun q : ℝ × M =>
        (q.2, ((trivializationAt E (TangentSpace I) α) ⟨q.2, v q⟩).2)) s :=
      (continuous_snd.continuousOn).prodMk hc
    have hmaps : Set.MapsTo (fun q : ℝ × M =>
        (q.2, ((trivializationAt E (TangentSpace I) α) ⟨q.2, v q⟩).2)) s
        (e.baseSet ×ˢ (Set.univ : Set E)) := by
      intro q hq
      exact ⟨hs q hq, trivial⟩
    have hsec : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q)) s := by
      have hcomp := e.continuousOn_symm.comp hpair hmaps
      refine hcomp.congr ?_
      intro q hq
      simpa using (e.symm_apply_apply_mk (hs q hq) (v q)).symm
    exact hsec

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma continuousOn_section_smul
    {α : M} {s : Set (ℝ × M)}
    (hs : ∀ q : ℝ × M, q ∈ s →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (f : ℝ × M → ℝ) (hf : ContinuousOn f s)
    (v : (q : ℝ × M) → TangentSpace I q.2)
    (hv : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q)) s) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (f q • v q)) s := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  apply (continuousOn_section_iff_coord (α := α) hs (fun q => f q • v q)).mpr
  have hc : ContinuousOn (fun q : ℝ × M => (e ⟨q.2, v q⟩).2) s :=
    (continuousOn_section_iff_coord (α := α) hs v).mp hv
  refine (hf.smul hc).congr ?_
  intro q hq
  have hb : q.2 ∈ e.baseSet := hs q hq
  exact (e.linearEquivAt ℝ q.2 hb).map_smul (f q) (v q)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma continuousOn_section_add
    {α : M} {s : Set (ℝ × M)}
    (hs : ∀ q : ℝ × M, q ∈ s →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : (q : ℝ × M) → TangentSpace I q.2)
    (hv : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q)) s)
    (hw : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (w q)) s) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q + w q)) s := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  apply (continuousOn_section_iff_coord (α := α) hs (fun q => v q + w q)).mpr
  have hcv : ContinuousOn (fun q : ℝ × M => (e ⟨q.2, v q⟩).2) s :=
    (continuousOn_section_iff_coord (α := α) hs v).mp hv
  have hcw : ContinuousOn (fun q : ℝ × M => (e ⟨q.2, w q⟩).2) s :=
    (continuousOn_section_iff_coord (α := α) hs w).mp hw
  refine (hcv.add hcw).congr ?_
  intro q hq
  have hb : q.2 ∈ e.baseSet := hs q hq
  exact (e.linearEquivAt ℝ q.2 hb).map_add (v q) (w q)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma continuousOn_section_sub
    {α : M} {s : Set (ℝ × M)}
    (hs : ∀ q : ℝ × M, q ∈ s →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : (q : ℝ × M) → TangentSpace I q.2)
    (hv : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q)) s)
    (hw : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (w q)) s) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v q - w q)) s := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  apply (continuousOn_section_iff_coord (α := α) hs (fun q => v q - w q)).mpr
  have hcv : ContinuousOn (fun q : ℝ × M => (e ⟨q.2, v q⟩).2) s :=
    (continuousOn_section_iff_coord (α := α) hs v).mp hv
  have hcw : ContinuousOn (fun q : ℝ × M => (e ⟨q.2, w q⟩).2) s :=
    (continuousOn_section_iff_coord (α := α) hs w).mp hw
  refine (hcv.sub hcw).congr ?_
  intro q hq
  have hb : q.2 ∈ e.baseSet := hs q hq
  exact (e.linearEquivAt ℝ q.2 hb).map_sub (v q) (w q)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma continuousOn_section_sum
    {α : M} {s : Set (ℝ × M)}
    (hs : ∀ q : ℝ × M, q ∈ s →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {ι : Type*} (t : Finset ι)
    (v : ι → (q : ℝ × M) → TangentSpace I q.2)
    (hv : ∀ i ∈ t, ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (v i q)) s) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
          (∑ i ∈ t, v i q)) s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    apply (continuousOn_section_iff_coord (α := α) hs
      (fun q => (∑ i ∈ (∅ : Finset ι), v i q))).mpr
    have hconst : ContinuousOn (fun q : ℝ × M => (0 : E)) s := by fun_prop
    refine hconst.congr ?_
    intro q hq
    change ((trivializationAt E (TangentSpace I) α) ⟨q.2, (0 : TangentSpace I q.2)⟩).2 = 0
    have hb : q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := hs q hq
    have hlin : TangentSpace I q.2 ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I) α).linearEquivAt ℝ q.2 hb
    change (trivializationAt E (TangentSpace I) α).linearEquivAt ℝ q.2 hb 0 = 0
    exact map_zero _
  | @insert a t hat ih =>
    have hmain : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
          (v a q + ∑ i ∈ t, v i q)) s := by
      exact continuousOn_section_add (I := I) hs
        (v a) (fun q => ∑ i ∈ t, v i q)
        (hv a (by simp))
        (ih (fun i hi => hv i (by simp [hi])))
    refine hmain.congr ?_
    intro q hq
    simp [Finset.sum_insert hat]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)] in
theorem metricInner_continuousOn_param
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {U : Set M}
    (X Y : (q : ℝ × M) → TangentSpace I q.2)
    (hX : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (X q))
      (Set.Icc 0 T ×ˢ U))
    (hY : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2 (Y q))
      (Set.Icc 0 T ×ˢ U)) :
    ContinuousOn (fun q : ℝ × M => (S.base.metric q.1).inner q.2 (X q) (Y q))
      (Set.Icc 0 T ×ˢ U) := by
  classical
  let K : Set ℝ := Set.Icc 0 T
  have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    have hmono : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
        (fun t x => metricTensorField (I := I) (S.family.metric t) x) := by
      exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.smoothMetric.metricTensor_cont (by intro s hs; exact hs)
    refine Tensor0SFamilyContinuousOnSet.congr (I := I) (M := M) hmono ?_
    intro t ht x
    rfl
  rw [continuousOn_iff_continuous_restrict]
  let P := {q : ℝ × M // q.1 ∈ K ∧ q.2 ∈ U}
  have heval := Tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 2)
    (K := K) (A := fun t x => metricTensorField (I := I) (S.base.metric t) x) hA
    (P := P) (τ := fun p : P => p.1.1) (b := fun p : P => p.1.2)
    (continuous_fst.comp continuous_subtype_val) (fun p : P => p.2.1)
    (continuous_snd.comp continuous_subtype_val)
    (v := fun a : Fin 2 => fun p : P => if a = 0 then X p.1 else Y p.1)
    (by
      intro a
      fin_cases a
      · simpa using (continuousOn_iff_continuous_restrict.mp hX)
      · simpa using (continuousOn_iff_continuous_restrict.mp hY))
  refine heval.congr (fun p => ?_)
  change metricTensorField (I := I) (S.base.metric p.1.1) p.1.2
      (fun i : Fin 2 => if i = 0 then X p.1 else Y p.1) =
    (S.base.metric p.1.1).inner p.1.2 (X p.1) (Y p.1)
  rw [metricTensorField_apply]
  simp

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
    [T2Space M] [NeZero (Module.finrank ℝ E)] in
private lemma chartBasisVec_section_continuousOn_param
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
          (chartBasisVecFiber (I := I) α i q.2))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  have hc := (chartBasisVec_contMDiffOn (I := I) α i).continuousOn
  have hmap : ContinuousOn (fun q : ℝ × M => q.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuous_snd.continuousOn
  have hmaps : Set.MapsTo (fun q : ℝ × M => q.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact hq.2
  simpa [chartBasisVec] using hc.comp hmap hmaps

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem intrinsicChartFrameNormFiber_continuousOn_param_strong
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (α : M) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      ContinuousOn (fun q : ℝ × M =>
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
            (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i))
        (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∧
      ContinuousOn (fun q : ℝ × M =>
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
            (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 i))
        (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let U : Set M := smoothOrthoOpen (I := I) (M := M) α
  have hU_base : ∀ q : ℝ × M,
      q ∈ Set.Icc 0 T ×ˢ U →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  have hbasis : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M =>
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
            (chartBasisVecFiber (I := I) α i q.2))
        (Set.Icc 0 T ×ˢ U) := by
    intro i
    exact (chartBasisVec_section_continuousOn_param (I := I) α i).mono (by
      intro q hq
      exact ⟨trivial, hU_base q hq⟩)
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi_val : i.val = 0 := Nat.le_zero.mp hi
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_⟩
    · have hsec_eq : ∀ q : ℝ × M,
          intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 ⟨0, NeZero.pos _⟩ =
            chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2 :=
        fun q => intrinsicChartFrameRawFiber_at_zero (I := I) (S.base.metric q.1) α q.2
      have hT_eq : (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 ⟨0, NeZero.pos _⟩)) =
          (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)) := by
        funext q; rw [hsec_eq q]
      rw [hT_eq]
      exact hbasis ⟨0, NeZero.pos _⟩
    · have hsec_eq : ∀ q : ℝ × M,
          intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 ⟨0, NeZero.pos _⟩ =
            (Real.sqrt ((S.base.metric q.1).inner q.2
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2 :=
        fun q => intrinsicChartFrameNormFiber_at_zero (I := I) (S.base.metric q.1) α q.2
      have hv : ContinuousOn (fun q : ℝ × M =>
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2))
          (Set.Icc 0 T ×ˢ U) := hbasis ⟨0, NeZero.pos _⟩
      have h_inner : ContinuousOn (fun q : ℝ × M =>
          (S.base.metric q.1).inner q.2
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2))
          (Set.Icc 0 T ×ˢ U) := by
        exact metricInner_continuousOn_param (I := I) (M := M) hT S hS
          (fun q => chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
          (fun q => chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2) hv hv
      have h_inner_pos : ∀ q : ℝ × M,
          q ∈ Set.Icc 0 T ×ˢ U →
          0 < (S.base.metric q.1).inner q.2
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2) := by
        intro q hq
        have hLI := chartBasisFamily_linearIndependent (I := I) α (hU_base q hq)
        have hv_ne_zero : chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2 ≠ 0 :=
          hLI.ne_zero ⟨0, NeZero.pos _⟩
        exact (S.base.metric q.1).pos q.2 _ hv_ne_zero
      have h_sqrt : ContinuousOn (fun q : ℝ × M =>
          Real.sqrt ((S.base.metric q.1).inner q.2
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)))
          (Set.Icc 0 T ×ˢ U) := h_inner.sqrt
      have h_sqrt_ne : ∀ q : ℝ × M, q ∈ Set.Icc 0 T ×ˢ U →
          Real.sqrt ((S.base.metric q.1).inner q.2
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)) ≠ 0 := by
        intro q hq
        have := h_inner_pos q hq
        exact ne_of_gt (Real.sqrt_pos.mpr this)
      have h_inv : ContinuousOn (fun q : ℝ × M =>
          (Real.sqrt ((S.base.metric q.1).inner q.2
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)))⁻¹)
          (Set.Icc 0 T ×ˢ U) := h_sqrt.inv₀ h_sqrt_ne
      have h_smul : ContinuousOn (fun q : ℝ × M =>
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
            ((Real.sqrt ((S.base.metric q.1).inner q.2
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2))
          (Set.Icc 0 T ×ˢ U) := continuousOn_section_smul (I := I) hU_base
            (fun q : ℝ × M => (Real.sqrt ((S.base.metric q.1).inner q.2
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)))⁻¹) h_inv
            (fun q => chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2) hv
      have hT_eq : (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 ⟨0, NeZero.pos _⟩)) =
          (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              ((Real.sqrt ((S.base.metric q.1).inner q.2
                  (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)
                  (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)))⁻¹ •
                chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ q.2)) := by
        funext q; rw [hsec_eq q]
      rw [hT_eq]
      exact h_smul
  | succ k ih =>
    intro i hi
    by_cases hcase : i.val ≤ k
    · exact ih i hcase
    · have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 j))
            (Set.Icc 0 T ×ˢ U) := by
        intro j hj
        have hj_le_k : j.val ≤ k := by omega
        exact (ih j hj_le_k).2
      have hbase_i := hbasis i
      have h_j'_small_section : ∀ j' : Fin i.val,
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (Set.Icc 0 T ×ˢ U) := by
        intro j'
        exact ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ j'.isLt
      have h_innerCoef : ∀ j' : Fin i.val,
          ContinuousOn (fun q : ℝ × M =>
            (S.base.metric q.1).inner q.2
              (chartBasisVecFiber (I := I) α i q.2)
              (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (Set.Icc 0 T ×ˢ U) := by
        intro j'
        exact metricInner_continuousOn_param (I := I) (M := M) hT S hS
          (fun q => chartBasisVecFiber (I := I) α i q.2)
          (fun q => intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
          hbase_i (h_j'_small_section j')
      have h_summand : ∀ j' ∈ (Finset.univ : Finset (Fin i.val)),
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              ((S.base.metric q.1).inner q.2
                (chartBasisVecFiber (I := I) α i q.2)
                (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (Set.Icc 0 T ×ˢ U) := by
        intro j' _
        exact continuousOn_section_smul (I := I) hU_base
          (fun q : ℝ × M => (S.base.metric q.1).inner q.2
            (chartBasisVecFiber (I := I) α i q.2)
            (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
          (h_innerCoef j')
          (fun q => intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
          (h_j'_small_section j')
      have h_sum :
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (∑ j' : Fin i.val,
                (S.base.metric q.1).inner q.2
                  (chartBasisVecFiber (I := I) α i q.2)
                  (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (Set.Icc 0 T ×ˢ U) := continuousOn_section_sum (I := I) hU_base
              (Finset.univ : Finset (Fin i.val))
              (fun j' q => (S.base.metric q.1).inner q.2
                (chartBasisVecFiber (I := I) α i q.2)
                (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
              h_summand
      have h_raw : ContinuousOn (fun q : ℝ × M =>
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
            (chartBasisVecFiber (I := I) α i q.2 -
              ∑ j' : Fin i.val,
                (S.base.metric q.1).inner q.2
                  (chartBasisVecFiber (I := I) α i q.2)
                  (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
          (Set.Icc 0 T ×ˢ U) :=
        continuousOn_section_sub (I := I) hU_base
          (fun q => chartBasisVecFiber (I := I) α i q.2)
          (fun q => ∑ j' : Fin i.val,
                (S.base.metric q.1).inner q.2
                  (chartBasisVecFiber (I := I) α i q.2)
                  (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
          hbase_i h_sum
      have h_raw_eq : ∀ q : ℝ × M,
          intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i =
            chartBasisVecFiber (I := I) α i q.2 -
              ∑ j' : Fin i.val,
                (S.base.metric q.1).inner q.2
                  (chartBasisVecFiber (I := I) α i q.2)
                  (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := fun q => by
        unfold intrinsicChartFrameRawFiber; rfl
      have h_raw_section :
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i))
            (Set.Icc 0 T ×ˢ U) := by
        have hT_eq : (fun q : ℝ × M =>
              TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
                (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)) =
            (fun q : ℝ × M =>
              TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
                (chartBasisVecFiber (I := I) α i q.2 -
                  ∑ j' : Fin i.val,
                    (S.base.metric q.1).inner q.2
                      (chartBasisVecFiber (I := I) α i q.2)
                      (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                    intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) := by
          funext q; rw [h_raw_eq q]
        rw [hT_eq]
        exact h_raw
      have h_inner_raw :
          ContinuousOn (fun q : ℝ × M =>
            (S.base.metric q.1).inner q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i))
            (Set.Icc 0 T ×ˢ U) :=
        metricInner_continuousOn_param (I := I) (M := M) hT S hS
          (fun q => intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
          (fun q => intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
          h_raw_section h_raw_section
      have h_inner_raw_pos : ∀ q : ℝ × M,
          q ∈ Set.Icc 0 T ×ˢ U →
          0 < (S.base.metric q.1).inner q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i) := by
        intro q hq
        have h_aux := intrinsicChartFrameNormFiber_orth_strong_aux
          (I := I) (S.base.metric q.1) α (hU_base q hq) i.val i (le_refl _)
        have hraw_ne : intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i ≠ 0 := h_aux.1
        exact (S.base.metric q.1).pos q.2 _ hraw_ne
      have h_sqrt_ne : ∀ q : ℝ × M, q ∈ Set.Icc 0 T ×ˢ U →
          Real.sqrt ((S.base.metric q.1).inner q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)) ≠ 0 := by
        intro q hq
        have := h_inner_raw_pos q hq
        exact ne_of_gt (Real.sqrt_pos.mpr this)
      have h_sqrt :
          ContinuousOn (fun q : ℝ × M => Real.sqrt
            ((S.base.metric q.1).inner q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)))
            (Set.Icc 0 T ×ˢ U) := h_inner_raw.sqrt
      have h_inv :
          ContinuousOn (fun q : ℝ × M =>
            (Real.sqrt ((S.base.metric q.1).inner q.2
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
              (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)))⁻¹)
            (Set.Icc 0 T ×ˢ U) := h_sqrt.inv₀ h_sqrt_ne
      have h_smul :
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              ((Real.sqrt ((S.base.metric q.1).inner q.2
                (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
                (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)))⁻¹ •
                intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i))
            (Set.Icc 0 T ×ˢ U) :=
        continuousOn_section_smul (I := I) hU_base
          (fun q : ℝ × M => (Real.sqrt ((S.base.metric q.1).inner q.2
            (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
            (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)))⁻¹)
          h_inv
          (fun q => intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
          h_raw_section
      have h_norm_eq : ∀ q : ℝ × M,
          intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 i =
            (Real.sqrt ((S.base.metric q.1).inner q.2
                (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
                (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)))⁻¹ •
              intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i := fun q =>
        intrinsicChartFrameNormFiber_eq (I := I) (S.base.metric q.1) α q.2 i
      have h_norm_section :
          ContinuousOn (fun q : ℝ × M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
              (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 i))
            (Set.Icc 0 T ×ˢ U) := by
        have hT_eq : (fun q : ℝ × M =>
              TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
                (intrinsicChartFrameNormFiber (S.base.metric q.1) α q.2 i)) =
            (fun q : ℝ × M =>
              TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
                ((Real.sqrt ((S.base.metric q.1).inner q.2
                    (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)
                    (intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)))⁻¹ •
                  intrinsicChartFrameRawFiber (S.base.metric q.1) α q.2 i)) := by
          funext q; rw [h_norm_eq q]
        rw [hT_eq]
        exact h_smul
      exact ⟨h_raw_section, h_norm_section⟩

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem intrinsicChartFrameNorm_continuousOn_param
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) q.2
          (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α i q.2))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  unfold intrinsicChartFrameNorm
  exact (intrinsicChartFrameNormFiber_continuousOn_param_strong (I := I) (M := M) hT S hS α
    i.val i (le_refl _)).2

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem intrinsicChartFrameNorm_linearIndependent
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) =>
      intrinsicChartFrameNorm (I := I) g α i b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hpair :
      g.inner b (∑ j, c j • intrinsicChartFrameNorm (I := I) g α j b)
        (intrinsicChartFrameNorm (I := I) g α i b) = 0 := by
    rw [hc]
    simp
  rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      intrinsicChartFrameNorm_orthonormal (I := I) g α hb i i,
      if_pos rfl, smul_eq_mul, mul_one] at hpair
    exact hpair
  · intro j _ hji
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      intrinsicChartFrameNorm_orthonormal (I := I) g α hb j i,
      if_neg (by simpa using hji), smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
private theorem normSq0S_eq_four_mul_matrixNormSq_of_frame
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (e : Fin 3 → TangentSpace I x)
    (horth : ∀ i j : Fin 3, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    normSq0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x) =
      4 * ‖matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1))‖ ^ 2 := by
  classical
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hpair : g.inner x (∑ j, c j • e j) (e i) = 0 := by
      rw [hc]; simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        horth i i, if_pos rfl, smul_eq_mul, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        horth j i, if_neg (by simpa using hji), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hdim]
  have hsp : Submodule.span ℝ (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  let basis : Module.Basis (Fin 3) ℝ (TangentSpace I x) :=
    Module.Basis.mk hli hsp.symm.le
  have hbasis_eq : (basis : Fin 3 → TangentSpace I x) = e := by
    funext i
    exact Module.Basis.mk_apply hli hsp.symm.le i
  have horthB : OrthonormalBasisAt (I := I) g x basis := by
    intro i j
    rw [hbasis_eq]
    exact horth i j
  have hmain := inner0S_algebraic_eq_four_mul_matrixInner (I := I) (M := M) g x basis horthB A A
  have hmat : intrinsicFiberCurvatureOperatorMatrix (I := I) basis
        (A : Tensor04At (I := I) (M := M) x) =
      fun i j : Fin 3 =>
      tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
        (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
        (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1) := by
    ext i j
    simp [hbasis_eq]
  rw [normSq0S]
  rw [hmain]
  rw [hmat]
  rw [show inner ℝ (matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1)))
      (matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1))) =
      ‖matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1))‖ ^ 2 by
    rw [norm_sq_eq_re_inner (𝕜 := ℝ) (matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (e (bivectorIndex3 i).1) (e (bivectorIndex3 i).2)
          (e (bivectorIndex3 j).2) (e (bivectorIndex3 j).1)))]
    simp]

omit [SigmaCompactSpace M] in
private lemma normSq0S_rm04_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) :
    ContinuousOn (fun q : ℝ × M =>
        normSq0S (I := I) (S.base.metric q.1) q.2 4 (S.base.rm04 q.1 q.2))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let U : Set M := smoothOrthoOpen (I := I) (M := M) α
  have hU_base : ∀ q : ℝ × M,
      q ∈ Set.Icc 0 T ×ˢ U →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  have hfe (x : M) : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := by
    have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H x
    exact ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hx).finrank_eq.symm
  let idx (x : M) (a : Fin 3) : Fin (Module.finrank ℝ E) :=
    ⟨a.val, by rw [hfe x, hdim x]; exact a.isLt⟩
  let e (a : Fin 3) (q : ℝ × M) : TangentSpace I q.2 :=
    intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 a) q.2
  have he_cont : ∀ a : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 (e a q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a
    have hmain := intrinsicChartFrameNorm_continuousOn_param (I := I) (M := M) hT S hS α (idx α a)
    refine hmain.congr ?_
    intro q hq
    change TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 a) q.2) =
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α (idx α a) q.2)
    apply congrArg (fun i : Fin (Module.finrank ℝ E) =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α i q.2))
    apply Fin.ext
    rfl
  have he_orth : ∀ a b : Fin 3, ∀ q : ℝ × M,
      q ∈ Set.Icc 0 T ×ˢ U →
      (S.base.metric q.1).inner q.2 (e a q) (e b q) = if a = b then 1 else 0 := by
    intro a b q hq
    have horth := intrinsicChartFrameNorm_orthonormal (I := I) (S.base.metric q.1) α
      (hU_base q hq) (idx q.2 a) (idx q.2 b)
    have hidx : idx q.2 a = idx q.2 b ↔ a = b := by
      constructor
      · intro h
        apply Fin.ext
        simpa using (congrArg (fun i : Fin (Module.finrank ℝ E) => i.val) h)
      · intro h
        rw [h]
    change (S.base.metric q.1).inner q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 a) q.2)
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α (idx q.2 b) q.2) =
      if a = b then 1 else 0
    rw [horth]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab])]
    · rw [if_neg hab, if_neg (fun h => hab (hidx.mp h))]
  have hentry4 : ∀ a b c d : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e a q) (e b q) (e c q) (e d q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b c d
    have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc 0 T)
        (fun t x => S.base.rm04 t x) := by
      exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    rw [continuousOn_iff_continuous_restrict]
    let P := {q : ℝ × M // q.1 ∈ Set.Icc 0 T ∧ q.2 ∈ U}
    have heval := Tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := Set.Icc 0 T) (A := fun t x => S.base.rm04 t x) hA
      (P := P) (τ := fun p : P => p.1.1) (b := fun p : P => p.1.2)
      (continuous_fst.comp continuous_subtype_val) (fun p : P => p.2.1)
      (continuous_snd.comp continuous_subtype_val)
      (v := fun i : Fin 4 => fun p : P =>
        if i = 0 then e a p.1 else if i = 1 then e b p.1 else if i = 2 then e c p.1 else e d p.1)
      (by
        intro i
        fin_cases i
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont a))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont b))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont c))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont d)))
    refine heval.congr (fun p => ?_)
    change (S.base.rm04 p.1.1 p.1.2)
        (fun i : Fin 4 => if i = 0 then e a p.1 else if i = 1 then e b p.1 else if i = 2 then e c p.1 else e d p.1) =
      tensor04StdAt (I := I) (M := M) (S.base.rm04 p.1.1 p.1.2)
        (e a p.1) (e b p.1) (e c p.1) (e d p.1)
    rw [tensor04StdAt]
    congr 1
  have hentry : ∀ a b : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b
    exact hentry4 (bivectorIndex3 a).1 (bivectorIndex3 a).2 (bivectorIndex3 b).2 (bivectorIndex3 b).1
  have hsum_cont : ContinuousOn (fun q : ℝ × M =>
      4 * (∑ a : Fin 3, ∑ b : Fin 3,
        (tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2))
      (Set.Icc 0 T ×ˢ U) := by
    have hsum : ContinuousOn (fun q : ℝ × M =>
        ∑ a : Fin 3, ∑ b : Fin 3,
          (tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
            (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
            (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2)
        (Set.Icc 0 T ×ˢ U) := by
      refine continuousOn_finset_sum Finset.univ ?_
      intro a _
      refine continuousOn_finset_sum Finset.univ ?_
      intro b _
      exact (hentry a b).pow 2
    exact (continuousOn_const.mul hsum)
  refine hsum_cont.congr ?_
  intro q hq
  change normSq0S (I := I) (S.base.metric q.1) q.2 4
      ((⟨S.base.rm04 q.1 q.2, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric q.1) q.2⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) q.2) :
        Tensor04At (I := I) (M := M) q.2) =
    4 * (∑ a : Fin 3, ∑ b : Fin 3,
        (tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2)
  have hframe := normSq0S_eq_four_mul_matrixNormSq_of_frame (I := I) (M := M)
    (S.base.metric q.1) q.2 (hdim q.2) (fun a => e a q)
    (by intro a b; exact he_orth a b q hq)
    ⟨S.base.rm04 q.1 q.2, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric q.1) q.2⟩
  have hnorm : ‖matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))‖ ^ 2 =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
          (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2 := by
    have hsum := matrixInner_eq_sum
      (fun i j : Fin 3 => tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))
      (fun i j : Fin 3 => tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))
    calc
      ‖matrixToEuclid (fun i j : Fin 3 =>
          tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
            (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
            (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))‖ ^ 2
          = inner ℝ (matrixToEuclid (fun i j : Fin 3 =>
              tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
                (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
                (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))
              (matrixToEuclid (fun i j : Fin 3 =>
              tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
                (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
                (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q))) := by
            rw [norm_sq_eq_re_inner (𝕜 := ℝ) (matrixToEuclid (fun i j : Fin 3 =>
              tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
                (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
                (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))]
            simp
      _ = ∑ a : Fin 3, ∑ b : Fin 3,
            (tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
              (e (bivectorIndex3 a).1 q) (e (bivectorIndex3 a).2 q)
              (e (bivectorIndex3 b).2 q) (e (bivectorIndex3 b).1 q)) ^ 2 := by
            rw [hsum]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _
            rw [pow_two]
  rw [hframe]
  rw [hnorm]

omit [SigmaCompactSpace M] in
theorem tensor04FiberNorm_rm04_continuousOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3) :
    ContinuousOn (fun q : ℝ × M =>
        tensor04FiberNorm (S.base.metric q.1) q.2 (S.base.rm04 q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  intro q hq
  let α : M := q.2
  have hlocal := normSq0S_rm04_continuousOn_local (I := I) (M := M) hT S hS hdim α
  have hsq : ContinuousOn (fun r : ℝ × M =>
      Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := hlocal.sqrt
  have hqL : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
    exact ⟨hq.1, mem_smoothOrthoOpen (I := I) (M := M) α⟩
  have hL : ContinuousWithinAt
      (fun r : ℝ × M => Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) q :=
    hsq.continuousWithinAt hqL
  have hmem_nhds : (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∈
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (smoothOrthoOpen_open (I := I) (M := M) α)
    · exact ⟨trivial, mem_smoothOrthoOpen (I := I) (M := M) α⟩
    · intro r hr
      have hEq : (Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∩
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) =
          Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
        rw [Set.prod_inter_prod]
        simp
      exact (hEq ▸ hr)
  have heq : 𝓝[(Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)] q =
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    apply le_antisymm
    · exact nhdsWithin_mono q (by
        intro r hr
        exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hr).1, trivial⟩)
    · exact (nhdsWithin_le_iff (s := (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
        (t := (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)) (x := q)).mpr hmem_nhds
  have hT' : ContinuousWithinAt
      (fun r : ℝ × M => Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) q := by
    change Tendsto (fun r : ℝ × M =>
        Real.sqrt (normSq0S (I := I) (S.base.metric r.1) r.2 4 (S.base.rm04 r.1 r.2)))
      (𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q)
      (𝓝 (Real.sqrt (normSq0S (I := I) (S.base.metric q.1) q.2 4 (S.base.rm04 q.1 q.2))))
    rw [← heq]
    exact hL
  simpa [tensor04FiberNorm] using hT'


omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem exists_pulledRm_norm_bound
    {T : ℝ} (hT : 0 < T) [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
        (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      ‖uhlenbeckPulledRm04At S basisAt iota t x‖ ≤ R := by
  classical
  let s : Set (ℝ × M) := Set.Icc 0 T ×ˢ (Set.univ : Set M)
  let f : ℝ × M → ℝ := fun q =>
    tensor04FiberNorm (S.base.metric q.1) q.2 (S.base.rm04 q.1 q.2)
  have hf_cont : ContinuousOn f s := by
    simpa [f, s] using tensor04FiberNorm_rm04_continuousOn (I := I) (M := M) hT S hS hdim
  have hs_compact : IsCompact s := by
    dsimp [s]
    exact isCompact_Icc.prod (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set M))
  rcases (hs_compact.bddAbove_image hf_cont) with ⟨R, hR⟩
  let R' : ℝ := max R 0
  refine ⟨R', ?_, ?_⟩
  · dsimp [R']
    exact le_max_right _ _
  · intro t ht x
    have hx : (t, x) ∈ s := by simp [s, ht]
    have hle : f (t, x) ≤ R := hR (Set.mem_image_of_mem f hx)
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
    have heq : ‖uhlenbeckPulledRm04At S basisAt iota t x‖ = f (t, x) := by
      have h1 := tensor04FiberNorm_eq_norm (I := I) (S.base.metric 0) x
        (uhlenbeckPulledRm04At S basisAt iota t x)
      rw [← h1]
      dsimp [f]
      exact pulledRm_norm_eq_rm_norm (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x
    calc
      ‖uhlenbeckPulledRm04At S basisAt iota t x‖ = f (t, x) := heq
      _ ≤ R := hle
      _ ≤ max R 0 := le_max_left _ _

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
private theorem intrinsicFiberBivectorArray_antisymm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (X Y Z W : TangentSpace I x) :
    ∀ p q : Fin 3,
      intrinsicFiberBivectorTwoForm (I := I) g basis p X Y *
            intrinsicFiberBivectorTwoForm (I := I) g basis q W Z +
          intrinsicFiberBivectorTwoForm (I := I) g basis p Y Z *
            intrinsicFiberBivectorTwoForm (I := I) g basis q W X +
          intrinsicFiberBivectorTwoForm (I := I) g basis p Z X *
            intrinsicFiberBivectorTwoForm (I := I) g basis q W Y +
          intrinsicFiberBivectorTwoForm (I := I) g basis q X Y *
            intrinsicFiberBivectorTwoForm (I := I) g basis p W Z +
          intrinsicFiberBivectorTwoForm (I := I) g basis q Y Z *
            intrinsicFiberBivectorTwoForm (I := I) g basis p W X +
          intrinsicFiberBivectorTwoForm (I := I) g basis q Z X *
            intrinsicFiberBivectorTwoForm (I := I) g basis p W Y = 0 := by
  intro p q
  fin_cases p <;> fin_cases q <;>
    simp [intrinsicFiberBivectorTwoForm, bivectorIndex3] <;> ring

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
private theorem intrinsicFiberOperatorTensor_mem_algebraicCurvatureTensorSubmodule_of_symm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : ∀ i j : Fin 3, Rmat i j = Rmat j i) :
    intrinsicFiberOperatorTensor (I := I) g basis Rmat ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  classical
  rw [mem_algebraicCurvatureTensorSubmodule_iff_symmetries]
  constructor
  · intro X Y Z W
    rw [intrinsicFiberOperatorTensor_apply, intrinsicFiberOperatorTensor_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _
    rw [intrinsicFiberBivectorTwoForm_anti (I := I) g basis p X Y]
    ring
  constructor
  · intro X Y Z W
    rw [intrinsicFiberOperatorTensor_apply, intrinsicFiberOperatorTensor_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _
    rw [intrinsicFiberBivectorTwoForm_anti (I := I) g basis q W Z]
    ring
  · intro X Y Z W
    have hanti := intrinsicFiberBivectorArray_antisymm (I := I) g basis X Y Z W
    let f : Fin 3 → Fin 3 → ℝ := fun p q =>
      intrinsicFiberBivectorTwoForm (I := I) g basis p X Y *
          intrinsicFiberBivectorTwoForm (I := I) g basis q W Z +
        intrinsicFiberBivectorTwoForm (I := I) g basis p Y Z *
          intrinsicFiberBivectorTwoForm (I := I) g basis q W X +
        intrinsicFiberBivectorTwoForm (I := I) g basis p Z X *
          intrinsicFiberBivectorTwoForm (I := I) g basis q W Y
    have hf : ∀ p q : Fin 3, f p q + f q p = 0 := by
      intro p q
      dsimp [f]
      linarith [hanti p q]
    let h : Fin 3 → Fin 3 → ℝ := fun p q => Rmat p q * f p q
    have hantisymm : ∀ p q : Fin 3, h q p = -h p q := by
      intro p q
      dsimp [h]
      have hf' : f q p = -f p q := by linarith [hf p q]
      rw [hR q p]
      rw [hf']
      ring
    have hmain : (∑ p : Fin 3, ∑ q : Fin 3, h p q) = 0 := by
      have hpair : (∑ p : Fin 3, ∑ q : Fin 3, h p q) +
            (∑ p : Fin 3, ∑ q : Fin 3, h q p) = 0 := by
        calc
          (∑ p, ∑ q, h p q) + (∑ p, ∑ q, h q p)
              = ∑ p, ∑ q, (h p q + h q p) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro p _
                rw [← Finset.sum_add_distrib]
          _ = 0 := by
                exact Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => by
                  rw [hantisymm p q]
                  ring))
      have hswap : (∑ p : Fin 3, ∑ q : Fin 3, h p q) =
          ∑ p : Fin 3, ∑ q : Fin 3, h q p := by
        rw [Finset.sum_comm]
      have hzz : (∑ p : Fin 3, ∑ q : Fin 3, h p q) +
            (∑ p : Fin 3, ∑ q : Fin 3, h p q) = 0 := by
        rw [← hswap] at hpair
        exact hpair
      linarith
    have hsplit : (∑ p : Fin 3, ∑ q : Fin 3, h p q) =
        (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p X Y *
            intrinsicFiberBivectorTwoForm (I := I) g basis q W Z) +
        (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p Y Z *
            intrinsicFiberBivectorTwoForm (I := I) g basis q W X) +
        (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * intrinsicFiberBivectorTwoForm (I := I) g basis p Z X *
            intrinsicFiberBivectorTwoForm (I := I) g basis q W Y) := by
      simp [h, f, mul_add, mul_assoc, Finset.sum_add_distrib]
    rw [intrinsicFiberOperatorTensor_apply, intrinsicFiberOperatorTensor_apply,
      intrinsicFiberOperatorTensor_apply]
    rw [← hsplit]
    exact hmain

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFiberHamiltonIveyRegion_matrixImage_eq_regionEuclid
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (K τ : ℝ) :
    (fun A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
      matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis
        (A : Tensor04At (I := I) (M := M) x))) ''
      ((fun A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
        (A : Tensor04At (I := I) (M := M) x)) ⁻¹'
        intrinsicFiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x)
    = hamiltonIveyConvexMatrixRegionEuclid K τ := by
  classical
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [Set.mem_preimage] at hA
    rw [mem_intrinsicFiberHamiltonIveyRegion] at hA
    exact hA.2
  · intro hq
    have hmat_mem : euclidToMatrix q ∈ hamiltonIveyConvexMatrixRegion K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff] at hq
      simpa [euclidToMatrix_matrixToEuclid] using hq
    have hherm : (euclidToMatrix q).IsHermitian := by
      rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hmat_mem
      exact hmat_mem.1
    have hsymm : ∀ i j : Fin 3, (euclidToMatrix q) i j = (euclidToMatrix q) j i := by
      intro i j
      have h := congrFun (congrFun hherm i) j
      simpa [Matrix.conjTranspose, star_trivial] using h.symm
    let A₀ : Tensor04At (I := I) (M := M) x :=
      intrinsicFiberOperatorTensor (I := I) g basis (euclidToMatrix q)
    have hA₀ : A₀ ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
      intrinsicFiberOperatorTensor_mem_algebraicCurvatureTensorSubmodule_of_symm
        (I := I) g basis (euclidToMatrix q) hsymm
    have hmat : intrinsicFiberCurvatureOperatorMatrix (I := I) basis A₀ = euclidToMatrix q := by
      exact intrinsicFiberCurvatureOperatorMatrix_of_intrinsicFiberOperatorTensor
        (I := I) g basis horth (euclidToMatrix q)
    refine ⟨⟨A₀, hA₀⟩, ?_, ?_⟩
    · rw [Set.mem_preimage]
      rw [mem_intrinsicFiberHamiltonIveyRegion]
      constructor
      · exact hA₀
      · rw [hmat]
        rw [matrixToEuclid_euclidToMatrix]
        exact hq
    · change matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis A₀) = q
      rw [hmat]
      exact matrixToEuclid_euclidToMatrix q

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem fiberInfDist_eq_two_mul_matrixInfDist
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (A : Tensor04At (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) g x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
    letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
        inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
    Metric.infDist A (intrinsicFiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x) =
      2 * Metric.infDist (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis A))
        (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
  classical
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  let C : Set (Tensor04At (I := I) (M := M) x) :=
    intrinsicFiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x
  let S : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) :=
    hamiltonIveyConvexMatrixRegionEuclid K τ
  let m : Tensor04At (I := I) (M := M) x → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun B => matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) basis B)
  have himg : (fun B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
        m (B : Tensor04At (I := I) (M := M) x)) ''
      ((fun B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
        (B : Tensor04At (I := I) (M := M) x)) ⁻¹' C) = S := by
    simpa [C, S, m] using intrinsicFiberHamiltonIveyRegion_matrixImage_eq_regionEuclid
      (I := I) g x basis horth K τ
  have hdist : ∀ (B : Tensor04At (I := I) (M := M) x),
      B ∈ C → dist A B = 2 * dist (m A) (m B) := by
    intro B hB
    have hB' : B ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
      (mem_intrinsicFiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x B).mp hB |>.1
    have hd := intrinsicFiberDist_eq_two_mul_matrixDist_of_orthonormal (I := I) (M := M)
      g x basis horth ⟨A, hA⟩ ⟨B, hB'⟩
    simpa [m] using hd
  have hS_ne : S.Nonempty := nonempty_hamiltonIveyConvexMatrixRegionEuclid hK hτ
  have hC_ne : C.Nonempty := by
    refine ⟨(0 : Tensor04At (I := I) (M := M) x), ?_⟩
    rw [mem_intrinsicFiberHamiltonIveyRegion]
    constructor
    · exact Submodule.zero_mem _
    · have hz : intrinsicFiberCurvatureOperatorMatrix (I := I) basis (0 : Tensor04At (I := I) (M := M) x) = 0 := by
        ext i j
        simp
      rw [hz]
      exact zero_mem_hamiltonIveyConvexMatrixRegionEuclid hK hτ
  apply le_antisymm
  · have hle : ∀ q : EuclideanSpace ℝ (Fin 3 × Fin 3), q ∈ S →
        Metric.infDist A C ≤ 2 * dist (m A) q := by
      intro q hq
      have hq' : q ∈ (fun B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
            m (B : Tensor04At (I := I) (M := M) x)) ''
          ((fun B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
            (B : Tensor04At (I := I) (M := M) x)) ⁻¹' C) := by
        rwa [← himg] at hq
      rcases hq' with ⟨B, hBpre, hBq⟩
      have hBmem : (B : Tensor04At (I := I) (M := M) x) ∈ C := Set.mem_preimage.mp hBpre
      have hd := hdist (B : Tensor04At (I := I) (M := M) x) hBmem
      have hd' : dist A (B : Tensor04At (I := I) (M := M) x) = 2 * dist (m A) q := by
        simpa [hBq] using hd
      have h1 : Metric.infDist A C ≤ dist A (B : Tensor04At (I := I) (M := M) x) :=
        Metric.infDist_le_dist_of_mem hBmem
      have h1' : Metric.infDist A C ≤ 2 * dist (m A) q := by
        simpa [hd'] using h1
      exact h1'
    have h2 : (Metric.infDist A C) / 2 ≤ Metric.infDist (m A) S := by
      exact (Metric.le_infDist hS_ne).mpr (by
        intro q hq
        have hle' := hle q hq
        exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa [mul_comm] using hle'))
    nlinarith
  · have hle : ∀ (B : Tensor04At (I := I) (M := M) x), B ∈ C →
        2 * Metric.infDist (m A) S ≤ dist A B := by
      intro B hB
      have hBsub : B ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        (mem_intrinsicFiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x B).mp hB |>.1
      have hBm : m B ∈ S := by
        exact (mem_intrinsicFiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x B).mp hB |>.2
      have hd := hdist B hB
      have h1 : Metric.infDist (m A) S ≤ dist (m A) (m B) :=
        Metric.infDist_le_dist_of_mem hBm
      nlinarith
    exact (Metric.le_infDist hC_ne).mpr hle

noncomputable def intrinsicFiberInfDist
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (K τ : ℝ) (x : M) : ℝ :=
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  Metric.infDist (uhlenbeckPulledRm04At S basisAt iota τ x)
    (intrinsicFiberHamiltonIveyRegion basisAt K τ x)

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem pulledRmMatrixEuclid_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota_cont : ContinuousOn (fun q : ℝ × M => iota q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hbasis_cont : ∀ a : Fin 3, Continuous (fun x : M =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (basisAt x a)))
    (α : M) :
    ContinuousOn (fun q : ℝ × M =>
      matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
          (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
          (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let U : Set M := smoothOrthoOpen (I := I) (M := M) α
  have hU_base : ∀ q : ℝ × M, q ∈ Set.Icc 0 T ×ˢ U →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  let e (a : Fin 3) (q : ℝ × M) : TangentSpace I q.2 :=
    uhlenbeckEndomorphismAt (basisAt q.2) iota q.1 (basisAt q.2 a)
  have he_cont : ∀ a : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 (e a q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a
    have hb : ∀ k : Fin 3, ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 (basisAt q.2 k))
        (Set.Icc 0 T ×ˢ U) := by
      intro k
      exact ContinuousOn.mono
        ((hbasis_cont k).comp continuous_snd).continuousOn
        (Set.subset_univ (s := (Set.Icc 0 T ×ˢ U)))
    have hc : ∀ k : Fin 3, ContinuousOn (fun q : ℝ × M => iota q.1 q.2 a k)
        (Set.Icc 0 T ×ˢ U) := by
      intro k
      have h1 : ContinuousOn (fun q : ℝ × M => iota q.1 q.2) (Set.Icc 0 T ×ˢ U) :=
        hiota_cont.mono (by intro q hq; exact ⟨hq.1, trivial⟩)
      exact ((continuous_apply (i := k)).comp (continuous_apply (i := a))).comp_continuousOn h1
    have hsmul : ∀ k : Fin 3, ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
          (iota q.1 q.2 a k • basisAt q.2 k))
        (Set.Icc 0 T ×ˢ U) := by
      intro k
      exact continuousOn_section_smul (I := I) hU_base (fun q => iota q.1 q.2 a k) (hc k)
        (fun q => basisAt q.2 k) (hb k)
    have hsum : ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
          (∑ k : Fin 3, iota q.1 q.2 a k • basisAt q.2 k))
        (Set.Icc 0 T ×ˢ U) :=
      continuousOn_section_sum (I := I) hU_base (Finset.univ : Finset (Fin 3))
        (fun k q => iota q.1 q.2 a k • basisAt q.2 k)
        (by intro k _; exact hsmul k)
    refine hsum.congr ?_
    intro q hq
    apply congrArg (fun v : TangentSpace I q.2 =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 v)
    exact uhlenbeckEndomorphism_apply_basis (basisAt q.2) iota q.1 a
  have hentry : ∀ a b c d : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e a q) (e b q) (e c q) (e d q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b c d
    have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc 0 T)
        (fun t x => S.base.rm04 t x) := by
      exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    rw [continuousOn_iff_continuous_restrict]
    let P := {q : ℝ × M // q.1 ∈ Set.Icc 0 T ∧ q.2 ∈ U}
    have heval := Tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := Set.Icc 0 T) (A := fun t x => S.base.rm04 t x) hA
      (P := P) (τ := fun p : P => p.1.1) (b := fun p : P => p.1.2)
      (continuous_fst.comp continuous_subtype_val) (fun p : P => p.2.1)
      (continuous_snd.comp continuous_subtype_val)
      (v := fun n : Fin 4 => fun p : P =>
        if n = 0 then e a p.1 else if n = 1 then e b p.1 else if n = 2 then e c p.1 else e d p.1)
      (by
        intro n
        fin_cases n
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont a))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont b))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont c))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont d)))
    refine heval.congr (fun p => ?_)
    change (S.base.rm04 p.1.1 p.1.2)
        (fun n : Fin 4 => if n = 0 then e a p.1 else if n = 1 then e b p.1 else if n = 2 then e c p.1 else e d p.1) =
      tensor04StdAt (I := I) (M := M) (S.base.rm04 p.1.1 p.1.2)
        (e a p.1) (e b p.1) (e c p.1) (e d p.1)
    rw [tensor04StdAt]
    congr 1
  have hmat_local : ContinuousOn (fun q : ℝ × M =>
      matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))
      (Set.Icc 0 T ×ˢ U) := by
    have hfun : ContinuousOn (fun q : ℝ × M =>
        fun ij : Fin 3 × Fin 3 =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 ij.1).1 q) (e (bivectorIndex3 ij.1).2 q)
          (e (bivectorIndex3 ij.2).2 q) (e (bivectorIndex3 ij.2).1 q))
        (Set.Icc 0 T ×ˢ U) := by
      rw [continuousOn_iff_continuous_restrict]
      let P := {q : ℝ × M // q.1 ∈ Set.Icc 0 T ∧ q.2 ∈ U}
      exact continuous_pi (by
        intro ij
        simpa using (continuousOn_iff_continuous_restrict.mp (hentry (bivectorIndex3 ij.1).1
          (bivectorIndex3 ij.1).2 (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1)))
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 × Fin 3 => ℝ)).comp_continuousOn hfun
  refine hmat_local.congr ?_
  intro q hq
  change matrixToEuclid (fun i j : Fin 3 =>
      tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
        (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
        (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)) =
    matrixToEuclid (fun i j : Fin 3 =>
      tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
        (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1))
  have heqfun : (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)) =
      fun i j : Fin 3 =>
      tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
        (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1) := by
    funext i j
    have h := uhlenbeckPulledRm04At_apply (I := I) (M := M) S basisAt iota q.1 q.2
      (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
      (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)
    simpa [e] using h.symm
  rw [heqfun]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem pulledRmMatrixEuclid_continuousOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota_cont : ContinuousOn (fun q : ℝ × M => iota q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hbasis_cont : ∀ a : Fin 3, Continuous (fun x : M =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (basisAt x a))) :
    ContinuousOn (fun q : ℝ × M =>
      matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
          (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
          (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  intro q hq
  let α : M := q.2
  have hlocal := pulledRmMatrixEuclid_continuousOn_local (I := I) (M := M) hT S hS basisAt iota
    hiota_cont hbasis_cont α
  have hqL : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
    exact ⟨hq.1, mem_smoothOrthoOpen (I := I) (M := M) α⟩
  have hL : ContinuousWithinAt
      (fun r : ℝ × M =>
        matrixToEuclid (fun i j : Fin 3 =>
          tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota r.1 r.2)
            (basisAt r.2 (bivectorIndex3 i).1) (basisAt r.2 (bivectorIndex3 i).2)
            (basisAt r.2 (bivectorIndex3 j).2) (basisAt r.2 (bivectorIndex3 j).1)))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) q :=
    hlocal.continuousWithinAt hqL
  have hmem_nhds : (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∈
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (smoothOrthoOpen_open (I := I) (M := M) α)
    · exact ⟨trivial, mem_smoothOrthoOpen (I := I) (M := M) α⟩
    · intro r hr
      have hEq : (Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∩
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) =
          Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
        rw [Set.prod_inter_prod]
        simp
      exact (hEq ▸ hr)
  have heq : 𝓝[(Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)] q =
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    apply le_antisymm
    · exact nhdsWithin_mono q (by
        intro r hr
        exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hr).1, trivial⟩)
    · exact (nhdsWithin_le_iff (s := (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
        (t := (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)) (x := q)).mpr hmem_nhds
  have hT' : ContinuousWithinAt
      (fun r : ℝ × M =>
        matrixToEuclid (fun i j : Fin 3 =>
          tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota r.1 r.2)
            (basisAt r.2 (bivectorIndex3 i).1) (basisAt r.2 (bivectorIndex3 i).2)
            (basisAt r.2 (bivectorIndex3 j).2) (basisAt r.2 (bivectorIndex3 j).1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) q := by
    change Tendsto (fun r : ℝ × M =>
        matrixToEuclid (fun i j : Fin 3 =>
          tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota r.1 r.2)
            (basisAt r.2 (bivectorIndex3 i).1) (basisAt r.2 (bivectorIndex3 i).2)
            (basisAt r.2 (bivectorIndex3 j).2) (basisAt r.2 (bivectorIndex3 j).1)))
      (𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q)
      (𝓝 (matrixToEuclid (fun i j : Fin 3 =>
          tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
            (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
            (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1))))
    rw [← heq]
    exact hL
  exact hT'

omit [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFiberInfDist_eq_two_mul_matrixInfDist
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (K : ℝ) {q : ℝ × M}
    (hq : q ∈ Set.Icc 0 T ×ˢ (Set.univ : Set M))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (hK : 0 < K) :
    intrinsicFiberInfDist hT S basisAt iota K q.1 q.2 =
      2 * Metric.infDist (matrixToEuclid (fun i j : Fin 3 =>
          tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
            (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
            (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)))
        (hamiltonIveyConvexMatrixRegionEuclid K q.1) := by
  letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) q.2) :=
    (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
  letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) q.2) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) q.2)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
  letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) q.2) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) q.2)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore.toCore
  change Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
      (intrinsicFiberHamiltonIveyRegion basisAt K q.1 q.2) =
    2 * Metric.infDist (matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
          (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
          (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1)))
      (hamiltonIveyConvexMatrixRegionEuclid K q.1)
  have hqτ : 0 ≤ q.1 := hq.1.1
  have hm : uhlenbeckPulledRm04At S basisAt iota q.1 q.2 ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) q.2 :=
    uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) S basisAt iota q.1 q.2
  exact fiberInfDist_eq_two_mul_matrixInfDist (I := I) (M := M)
    (S.base.metric 0) q.2 (basisAt q.2) (horth0 q.2) hK hqτ
    (uhlenbeckPulledRm04At S basisAt iota q.1 q.2) hm

omit [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem fiberInfDist_continuousOn
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota_cont : ContinuousOn (fun q : ℝ × M => iota q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hbasis_cont : ∀ a : Fin 3, Continuous (fun x : M =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (basisAt x a)))
    {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M =>
      intrinsicFiberInfDist hT S basisAt iota K q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  let m : ℝ × M → EuclideanSpace ℝ (Fin 3 × Fin 3) := fun q =>
    matrixToEuclid (fun i j : Fin 3 =>
      tensor04StdAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (basisAt q.2 (bivectorIndex3 i).1) (basisAt q.2 (bivectorIndex3 i).2)
        (basisAt q.2 (bivectorIndex3 j).2) (basisAt q.2 (bivectorIndex3 j).1))
  have hm_cont : ContinuousOn m (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    simpa [m] using pulledRmMatrixEuclid_continuousOn (I := I) (M := M) hT S hS basisAt iota
      hiota_cont hbasis_cont
  have hg : ContinuousOn (fun r : ℝ × (EuclideanSpace ℝ (Fin 3 × Fin 3)) =>
      Metric.infDist r.2 (hamiltonIveyConvexMatrixRegionEuclid K r.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))) :=
    continuousOn_infDist_hamiltonIveyRegion hK
  have hh : ContinuousOn (fun q : ℝ × M => (q.1, m q))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) :=
    (continuous_fst.continuousOn).prodMk hm_cont
  have hmaps : Set.MapsTo (fun q : ℝ × M => (q.1, m q))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))) := by
    intro q hq
    exact ⟨hq.1, trivial⟩
  have hcomp : ContinuousOn (fun q : ℝ × M =>
      Metric.infDist ((q.1, m q)).2 (hamiltonIveyConvexMatrixRegionEuclid K ((q.1, m q)).1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) :=
    hg.comp' hh hmaps
  have htwo : ContinuousOn (fun q : ℝ × M =>
      2 * Metric.infDist ((q.1, m q)).2 (hamiltonIveyConvexMatrixRegionEuclid K ((q.1, m q)).1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) :=
    (continuousOn_const.mul hcomp)
  refine htwo.congr ?_
  intro q hq
  simpa [m] using intrinsicFiberInfDist_eq_two_mul_matrixInfDist (I := I) (M := M) hT S basisAt iota K
    (q := q) hq horth0 hK

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem inner_basis_repr3
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (X : TangentSpace I x) (k : Fin 3) :
    g.inner x X (basis k) = basis.repr X k := by
  classical
  rw [inner_eq_sum_repr3 (I := I) horth X (basis k)]
  have hsingle : ∀ i : Fin 3, basis.repr (basis k) i = if i = k then 1 else 0 := by
    intro i
    rw [basis.repr_self k, Finsupp.single_apply]
    by_cases h : k = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hi => h hi.symm)]
  calc
    (∑ i : Fin 3, basis.repr X i * basis.repr (basis k) i) =
        ∑ i : Fin 3, basis.repr X i * (if i = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsingle i]
    _ = basis.repr X k := by
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
        simp
      · intro i _ hik
        rw [if_neg hik]
        simp
      · intro hk
        exact absurd (Finset.mem_univ k) hk

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFiberBivectorTwoForm_eq_repr
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (p : Fin 3) (X Y : TangentSpace I x) :
    intrinsicFiberBivectorTwoForm (I := I) g basis p X Y =
      basis.repr X (bivectorIndex3 p).1 * basis.repr Y (bivectorIndex3 p).2 -
        basis.repr X (bivectorIndex3 p).2 * basis.repr Y (bivectorIndex3 p).1 := by
  unfold intrinsicFiberBivectorTwoForm
  rw [inner_basis_repr3 (I := I) g basis horth X (bivectorIndex3 p).1]
  rw [inner_basis_repr3 (I := I) g basis horth X (bivectorIndex3 p).2]
  rw [inner_basis_repr3 (I := I) g basis horth Y (bivectorIndex3 p).1]
  rw [inner_basis_repr3 (I := I) g basis horth Y (bivectorIndex3 p).2]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M]
    [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
    [NeZero (Module.finrank ℝ E)] in
private lemma bivectorSum_prod_eq
    (a b c d : Fin 3 → ℝ) :
    (∑ p : Fin 3,
        (a (bivectorIndex3 p).1 * b (bivectorIndex3 p).2 - a (bivectorIndex3 p).2 * b (bivectorIndex3 p).1) *
          (c (bivectorIndex3 p).1 * d (bivectorIndex3 p).2 - c (bivectorIndex3 p).2 * d (bivectorIndex3 p).1)) =
      (∑ k : Fin 3, a k * c k) * (∑ k : Fin 3, b k * d k) -
        (∑ k : Fin 3, a k * d k) * (∑ k : Fin 3, b k * c k) := by
  classical
  rw [Fin.sum_univ_three]
  rw [show (∑ k : Fin 3, a k * c k) = a 0 * c 0 + a 1 * c 1 + a 2 * c 2 by rw [Fin.sum_univ_three]]
  rw [show (∑ k : Fin 3, b k * d k) = b 0 * d 0 + b 1 * d 1 + b 2 * d 2 by rw [Fin.sum_univ_three]]
  rw [show (∑ k : Fin 3, a k * d k) = a 0 * d 0 + a 1 * d 1 + a 2 * d 2 by rw [Fin.sum_univ_three]]
  rw [show (∑ k : Fin 3, b k * c k) = b 0 * c 0 + b 1 * c 1 + b 2 * c 2 by rw [Fin.sum_univ_three]]
  simp [bivectorIndex3]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFiberBivectorTwoForm_sum_pair
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (X Y Z W : TangentSpace I x) :
    (∑ p : Fin 3,
        intrinsicFiberBivectorTwoForm (I := I) g basis p X Y *
          intrinsicFiberBivectorTwoForm (I := I) g basis p Z W) =
      g.inner x X Z * g.inner x Y W - g.inner x X W * g.inner x Y Z := by
  classical
  simp_rw [intrinsicFiberBivectorTwoForm_eq_repr (I := I) g basis horth]
  rw [inner_eq_sum_repr3 (I := I) horth X Z, inner_eq_sum_repr3 (I := I) horth Y W,
    inner_eq_sum_repr3 (I := I) horth X W, inner_eq_sum_repr3 (I := I) horth Y Z]
  exact bivectorSum_prod_eq (basis.repr X) (basis.repr Y) (basis.repr Z) (basis.repr W)

omit [E : Type*] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [H : Type*] [TopologicalSpace H] [I : ModelWithCorners ℝ E H]
    [M : Type*] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M]
    [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem delta3_bivector_mul
    (i j : Fin 3) :
    delta3 (bivectorIndex3 i).1 (bivectorIndex3 j).1 *
        delta3 (bivectorIndex3 i).2 (bivectorIndex3 j).2 -
      delta3 (bivectorIndex3 i).1 (bivectorIndex3 j).2 *
        delta3 (bivectorIndex3 i).2 (bivectorIndex3 j).1 = delta3 i j := by
  fin_cases i <;> fin_cases j <;> simp [bivectorIndex3, delta3]

noncomputable def intrinsicFrameChangeMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun p i => intrinsicFiberBivectorTwoForm (I := I) g b p
    (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFrameChangeMatrix_orthogonal
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (hb' : OrthonormalBasisAt (I := I) g x b') :
    intrinsicFrameChangeMatrix (I := I) g b b' *
        (intrinsicFrameChangeMatrix (I := I) g b b').transpose = 1 := by
  classical
  let O : Matrix (Fin 3) (Fin 3) ℝ := intrinsicFrameChangeMatrix (I := I) g b b'
  have hOtO : O.transpose * O = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ p : Fin 3, intrinsicFrameChangeMatrix (I := I) g b b' p i *
          intrinsicFrameChangeMatrix (I := I) g b b' p j) =
        if i = j then 1 else 0
    simp only [intrinsicFrameChangeMatrix]
    rw [intrinsicFiberBivectorTwoForm_sum_pair (I := I) g b hb
      (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
      (b' (bivectorIndex3 j).1) (b' (bivectorIndex3 j).2)]
    rw [hb' (bivectorIndex3 i).1 (bivectorIndex3 j).1, hb' (bivectorIndex3 i).2 (bivectorIndex3 j).2,
      hb' (bivectorIndex3 i).1 (bivectorIndex3 j).2, hb' (bivectorIndex3 i).2 (bivectorIndex3 j).1]
    simpa [delta3] using delta3_bivector_mul i j
  exact matrixTransposeMul_orthogonal (O := O.transpose) (by simpa [Matrix.transpose_transpose] using hOtO)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
private lemma matrix_conj_dot
    (M O : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (O.transpose * M * O) i j = ∑ p : Fin 3, ∑ q : Fin 3, M p q * O p i * O q j := by
  classical
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFiberCurvatureOperatorMatrix_conj_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    intrinsicFiberCurvatureOperatorMatrix (I := I) b' (A : Tensor04At x) =
      (intrinsicFrameChangeMatrix (I := I) g b b').transpose *
        intrinsicFiberCurvatureOperatorMatrix (I := I) b (A : Tensor04At x) *
        intrinsicFrameChangeMatrix (I := I) g b b' := by
  classical
  let Mat : Matrix (Fin 3) (Fin 3) ℝ := intrinsicFiberCurvatureOperatorMatrix (I := I) b (A : Tensor04At x)
  let O : Matrix (Fin 3) (Fin 3) ℝ := intrinsicFrameChangeMatrix (I := I) g b b'
  have hsymm : ∀ i j : Fin 3, Mat i j = Mat j i := by
    intro i j
    have hM : (curvatureOperatorMatrixAt (I := I) x b A).IsHermitian :=
      curvatureOperatorMatrixAt_isHermitian (I := I) x b A
    have h := congrFun (congrFun hM i) j
    simpa [Mat, Matrix.conjTranspose, star_trivial] using h.symm
  have hTensor_mem : intrinsicFiberOperatorTensor (I := I) g b Mat ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    intrinsicFiberOperatorTensor_mem_algebraicCurvatureTensorSubmodule_of_symm (I := I) g b Mat hsymm
  have hTensor_map : intrinsicFiberCurvatureOperatorMatrix (I := I) b
      (intrinsicFiberOperatorTensor (I := I) g b Mat) = Mat :=
    intrinsicFiberCurvatureOperatorMatrix_of_intrinsicFiberOperatorTensor (I := I) g b hb Mat
  have hA_eq : intrinsicFiberOperatorTensor (I := I) g b Mat = (A : Tensor04At x) := by
    have hzero : (⟨intrinsicFiberOperatorTensor (I := I) g b Mat, hTensor_mem⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) - A = 0 := by
      apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal (I := I) (M := M) g x b hb
      change intrinsicFiberCurvatureOperatorMatrix (I := I) b
          (intrinsicFiberOperatorTensor (I := I) g b Mat - (A : Tensor04At x)) = 0
      rw [intrinsicFiberCurvatureOperatorMatrix_sub]
      rw [hTensor_map]
      change Mat - Mat = 0
      simp
    exact congrArg (fun Y : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
      (Y : Tensor04At (I := I) (M := M) x)) (sub_eq_zero.mp hzero)
  ext i j
  calc
    intrinsicFiberCurvatureOperatorMatrix (I := I) b' (A : Tensor04At x) i j
        = tensor04StdAt (I := I) (M := M) (A : Tensor04At x)
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1) := rfl
    _ = tensor04StdAt (I := I) (M := M) (intrinsicFiberOperatorTensor (I := I) g b Mat)
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1) := by rw [hA_eq]
    _ = ∑ p : Fin 3, ∑ q : Fin 3,
          Mat p q * intrinsicFiberBivectorTwoForm (I := I) g b p (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2) *
            intrinsicFiberBivectorTwoForm (I := I) g b q (b' (bivectorIndex3 j).1) (b' (bivectorIndex3 j).2) :=
          intrinsicFiberOperatorTensor_apply (I := I) g b Mat
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1)
    _ = (O.transpose * Mat * O) i j := by
          rw [show (O.transpose * Mat * O) i j = ∑ p : Fin 3, ∑ q : Fin 3,
              Mat p q * O p i * O q j from matrix_conj_dot Mat O i j]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          simp only [O, intrinsicFrameChangeMatrix]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem infDist_matrixToEuclid_orthogonal_conj
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (A O : Matrix (Fin 3) (Fin 3) ℝ) (hOorth : O * O.transpose = 1) :
    Metric.infDist (matrixToEuclid A) (hamiltonIveyConvexMatrixRegionEuclid K τ) =
    Metric.infDist (matrixToEuclid (O.transpose * A * O)) (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
  classical
  let T : EuclideanSpace ℝ (Fin 3 × Fin 3) → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun v => matrixToEuclid (O.transpose * euclidToMatrix v * O)
  let U : EuclideanSpace ℝ (Fin 3 × Fin 3) → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun v => matrixToEuclid (O * euclidToMatrix v * O.transpose)
  let S : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) := hamiltonIveyConvexMatrixRegionEuclid K τ
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  have hT_inner : ∀ v w, inner ℝ (T v) (T w) = inner ℝ v w := by
    intro v w
    have h := inner_matrixToEuclid_orthogonal_conj (euclidToMatrix v) (euclidToMatrix w) O hOorth
    simpa [T, matrixToEuclid_euclidToMatrix] using h.symm
  have hU_inner : ∀ v w, inner ℝ (U v) (U w) = inner ℝ v w := by
    intro v w
    have h := inner_matrixToEuclid_orthogonal_conj (euclidToMatrix v) (euclidToMatrix w) O.transpose hOorth2
    simpa [U, matrixToEuclid_euclidToMatrix] using h.symm
  have hT_sub : ∀ v, v ∈ S → T v ∈ S := by
    intro v hv
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    change euclidToMatrix (matrixToEuclid (O.transpose * euclidToMatrix v * O)) ∈
      hamiltonIveyConvexMatrixRegion K τ
    rw [euclidToMatrix_matrixToEuclid]
    have hvmat : euclidToMatrix v ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ v).1 hv
    exact (hamiltonIveyConvexMatrixRegion_orthogonal_conj (K := K) (τ := τ)
      (A := euclidToMatrix v) (Q := O) hOorth2 hOorth).1 hvmat
  have hU_sub : ∀ v, v ∈ S → U v ∈ S := by
    intro v hv
    rw [mem_hamiltonIveyConvexMatrixRegionEuclid_iff]
    change euclidToMatrix (matrixToEuclid (O * euclidToMatrix v * O.transpose)) ∈
      hamiltonIveyConvexMatrixRegion K τ
    rw [euclidToMatrix_matrixToEuclid]
    have hvmat : euclidToMatrix v ∈ hamiltonIveyConvexMatrixRegion K τ :=
      (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ v).1 hv
    exact (hamiltonIveyConvexMatrixRegion_orthogonal_conj (K := K) (τ := τ)
      (A := euclidToMatrix v) (Q := O.transpose) hOorth hOorth2).1 hvmat
  have hTU : ∀ v, T (U v) = v := by
    intro v
    dsimp [T, U]
    rw [euclidToMatrix_matrixToEuclid]
    have hmm : O.transpose * (O * euclidToMatrix v * O.transpose) * O = euclidToMatrix v := by
      rw [show O.transpose * (O * euclidToMatrix v * O.transpose) * O =
          (O.transpose * O) * euclidToMatrix v * (O.transpose * O) by
        repeat rw [Matrix.mul_assoc]]
      rw [hOorth2]
      simp
    rw [hmm]
    exact matrixToEuclid_euclidToMatrix v
  have hnormT : ∀ u, ‖T u‖ = ‖u‖ := by
    intro u
    have hsq : ‖T u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℝ) (T u), norm_sq_eq_re_inner (𝕜 := ℝ) u]
      simpa using (hT_inner u u)
    have h := (sq_eq_sq_iff_abs_eq_abs (‖T u‖) (‖u‖)).mp hsq
    rw [abs_of_nonneg (norm_nonneg (T u)), abs_of_nonneg (norm_nonneg u)] at h
    exact h
  have hdistT : ∀ v w, dist (T v) (T w) = dist v w := by
    intro v w
    rw [dist_eq_norm, dist_eq_norm]
    have hsq : ‖T v - T w‖ ^ 2 = ‖v - w‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℝ) (T v - T w), norm_sq_eq_re_inner (𝕜 := ℝ) (v - w)]
      calc
        inner ℝ (T v - T w) (T v - T w)
            = inner ℝ (T v) (T v) - inner ℝ (T v) (T w) - inner ℝ (T w) (T v) + inner ℝ (T w) (T w) := by
              rw [inner_sub_left (T v) (T w) (T v - T w)]
              rw [inner_sub_right (T v) (T v) (T w)]
              rw [inner_sub_right (T w) (T v) (T w)]
              ring
        _ = inner ℝ v v - inner ℝ v w - inner ℝ w v + inner ℝ w w := by
              rw [hT_inner v v, hT_inner v w, hT_inner w v, hT_inner w w]
        _ = inner ℝ (v - w) (v - w) := by
              rw [inner_sub_left v w (v - w)]
              rw [inner_sub_right v v w]
              rw [inner_sub_right w v w]
              ring
    have h := (sq_eq_sq_iff_abs_eq_abs (‖T v - T w‖) (‖v - w‖)).mp hsq
    rw [abs_of_nonneg (norm_nonneg (T v - T w)), abs_of_nonneg (norm_nonneg (v - w))] at h
    exact h
  have hne : S.Nonempty := nonempty_hamiltonIveyConvexMatrixRegionEuclid hK hτ
  have hle1 : Metric.infDist (T (matrixToEuclid A)) S ≤ Metric.infDist (matrixToEuclid A) S := by
    apply (Metric.le_infDist hne).mpr
    intro y hy
    have hyT : T y ∈ S := hT_sub y hy
    have h1 : Metric.infDist (T (matrixToEuclid A)) S ≤ dist (T (matrixToEuclid A)) (T y) :=
      Metric.infDist_le_dist_of_mem hyT
    calc
      Metric.infDist (T (matrixToEuclid A)) S ≤ dist (T (matrixToEuclid A)) (T y) := h1
      _ = dist (matrixToEuclid A) y := hdistT (matrixToEuclid A) y
  have hle2 : Metric.infDist (matrixToEuclid A) S ≤ Metric.infDist (T (matrixToEuclid A)) S := by
    apply (Metric.le_infDist hne).mpr
    intro y hy
    have hyU : U y ∈ S := hU_sub y hy
    have h1 : Metric.infDist (matrixToEuclid A) S ≤ dist (matrixToEuclid A) (U y) :=
      Metric.infDist_le_dist_of_mem hyU
    have h2 : dist (matrixToEuclid A) (U y) = dist (T (matrixToEuclid A)) y := by
      have hd := hdistT (matrixToEuclid A) (U y)
      rw [hTU y] at hd
      exact hd.symm
    calc
      Metric.infDist (matrixToEuclid A) S ≤ dist (matrixToEuclid A) (U y) := h1
      _ = dist (T (matrixToEuclid A)) y := h2
  simpa [T, S, euclidToMatrix_matrixToEuclid] using le_antisymm hle2 hle1

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem curvatureOperatorMatrixEuclid_infDist_eq_of_orthonormalBases
    (g : SmoothRiemannianMetric I M) (x : M)
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (hb' : OrthonormalBasisAt (I := I) g x b')
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    Metric.infDist (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) b (A : Tensor04At x)))
      (hamiltonIveyConvexMatrixRegionEuclid K τ) =
    Metric.infDist (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) b' (A : Tensor04At x)))
      (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
  classical
  let Mat : Matrix (Fin 3) (Fin 3) ℝ := intrinsicFiberCurvatureOperatorMatrix (I := I) b (A : Tensor04At x)
  let O : Matrix (Fin 3) (Fin 3) ℝ := intrinsicFrameChangeMatrix (I := I) g b b'
  have hconj : intrinsicFiberCurvatureOperatorMatrix (I := I) b' (A : Tensor04At x) = O.transpose * Mat * O := by
    simpa [Mat, O] using intrinsicFiberCurvatureOperatorMatrix_conj_of_orthonormal (I := I) (M := M) g b b' hb A
  have hOorth : O * O.transpose = 1 := by
    simpa [O] using intrinsicFrameChangeMatrix_orthogonal (I := I) (M := M) g b b' hb hb'
  calc
    Metric.infDist (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) b (A : Tensor04At x)))
        (hamiltonIveyConvexMatrixRegionEuclid K τ)
        = Metric.infDist (matrixToEuclid Mat) (hamiltonIveyConvexMatrixRegionEuclid K τ) := by rfl
    _ = Metric.infDist (matrixToEuclid (O.transpose * Mat * O)) (hamiltonIveyConvexMatrixRegionEuclid K τ) := by
          exact infDist_matrixToEuclid_orthogonal_conj hK hτ Mat O hOorth
    _ = Metric.infDist (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) b' (A : Tensor04At x)))
          (hamiltonIveyConvexMatrixRegionEuclid K τ) := by rw [hconj]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)] in
theorem intrinsicFiberHamiltonIveyRegion_eq_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (K τ : ℝ) (x : M) :
    intrinsicFiberHamiltonIveyRegion (I := I) basisAt K τ x =
      fiberHamiltonIveyRegion basisAt K τ x := by
  ext A
  rw [mem_intrinsicFiberHamiltonIveyRegion]
  constructor
  · intro hA
    refine ⟨hA.1, ?_⟩
    have hX : intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A =
        curvatureOperatorMatrixAt (I := I) x (basisAt x)
          (⟨A, hA.1⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
      (intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt (I := I) (basisAt x)
        (⟨A, hA.1⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).symm
    rw [← hX]
    have h1 := (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ
      (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x)
        (⟨A, hA.1⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)))).1 hA.2
    rwa [euclidToMatrix_matrixToEuclid] at h1
  · rintro ⟨h, hmat⟩
    constructor
    · exact h
    · have hX : intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt x) A =
          curvatureOperatorMatrixAt (I := I) x (basisAt x)
            (⟨A, h⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
        (intrinsicFiberCurvatureOperatorMatrix_eq_curvatureOperatorMatrixAt (I := I) (basisAt x)
          (⟨A, h⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).symm
      rw [hX]
      exact (mem_hamiltonIveyConvexMatrixRegionEuclid_iff K τ
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x (basisAt x)
          (⟨A, h⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)))).2 (by simpa using hmat)


omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
    [NeZero (Module.finrank ℝ E)] in
noncomputable def intrinsicFrameIndex
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (x : M) (a : Fin 3) : Fin (Module.finrank ℝ E) :=
  ⟨a.val, by
    have hfe : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := by
      have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact mem_chart_source H x
      exact ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x hx).finrank_eq.symm
    rw [hfe, hdim x]
    exact a.isLt⟩

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
noncomputable def intrinsicFlowFrame
    (g : SmoothRiemannianMetric I M)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) (q : ℝ × M) (a : Fin 3) : TangentSpace I q.2 :=
  intrinsicChartFrameNorm (I := I) g α (intrinsicFrameIndex (I := I) hdim q.2 a) q.2

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
noncomputable def flowFrameOperatorMatrix
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) (q : ℝ × M) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 i).1)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 i).2)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 j).2)
      (intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q (bivectorIndex3 j).1)

omit [SigmaCompactSpace M] in
theorem intrinsicFiberInfDist_eq_two_mul_flowFrameMatrixInfDist
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) {K : ℝ} (hK : 0 < K) {q : ℝ × M}
    (hq : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :
    intrinsicFiberInfDist hT S basisAt iota K q.1 q.2 =
      2 * Metric.infDist (matrixToEuclid (flowFrameOperatorMatrix (I := I) hT S hdim α q))
        (hamiltonIveyConvexMatrixRegionEuclid K q.1) := by
  classical
  let gτ : SmoothRiemannianMetric I M := S.base.metric q.1
  let e : Fin 3 → TangentSpace I q.2 :=
    fun a => intrinsicFlowFrame (I := I) gτ hdim α q a
  have hU : q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  have hidx_inj : Function.Injective (intrinsicFrameIndex (I := I) hdim q.2) := by
    intro a b h
    apply Fin.ext
    simpa using (congrArg (fun i : Fin (Module.finrank ℝ E) => i.val) h)
  have horth_e : ∀ a b : Fin 3, gτ.inner q.2 (e a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have horth := intrinsicChartFrameNorm_orthonormal (I := I) gτ α hU
      (intrinsicFrameIndex (I := I) hdim q.2 a) (intrinsicFrameIndex (I := I) hdim q.2 b)
    change gτ.inner q.2
        (intrinsicChartFrameNorm (I := I) gτ α (intrinsicFrameIndex (I := I) hdim q.2 a) q.2)
        (intrinsicChartFrameNorm (I := I) gτ α (intrinsicFrameIndex (I := I) hdim q.2 b) q.2) =
      if a = b then 1 else 0
    rw [horth]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab])]
    · rw [if_neg hab, if_neg (fun h => hab (hidx_inj h))]
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hpair : gτ.inner q.2 (∑ j, c j • e j) (e i) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        horth_e i i, if_pos rfl, smul_eq_mul, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        horth_e j i, if_neg (by simpa using hji), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace I q.2) := by
    rw [Fintype.card_fin, hdim q.2]
  have hsp : Submodule.span ℝ (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  let gsb : Module.Basis (Fin 3) ℝ (TangentSpace I q.2) := Module.Basis.mk hli hsp.symm.le
  have hgsb : (gsb : Fin 3 → TangentSpace I q.2) = e := by
    funext a
    exact Module.Basis.mk_apply hli hsp.symm.le a
  have horth_gsb : OrthonormalBasisAt (I := I) gτ q.2 gsb := by
    intro i j
    rw [hgsb]
    simpa [delta3] using horth_e i j
  have ht : q.1 ∈ Set.Icc 0 T := hq.1
  let mov : Module.Basis (Fin 3) ℝ (TangentSpace I q.2) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram q.1 ht q.2
  have horth_mov : OrthonormalBasisAt (I := I) gτ q.2 mov := by
    simpa [mov, gτ] using uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
      hT S basisAt iota hiota0 hgram q.2 (horth0 q.2) ht
  have hstep1 : intrinsicFiberInfDist hT S basisAt iota K q.1 q.2 =
      2 * Metric.infDist
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt q.2)
          (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)))
        (hamiltonIveyConvexMatrixRegionEuclid K q.1) := by
    simpa using intrinsicFiberInfDist_eq_two_mul_matrixInfDist (I := I) (M := M) hT S basisAt iota K
      (q := q) (by exact ⟨hq.1, trivial⟩) horth0 hK
  have hstep2 : intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt q.2)
        (uhlenbeckPulledRm04At S basisAt iota q.1 q.2) =
      intrinsicFiberCurvatureOperatorMatrix (I := I) mov (S.base.rm04 q.1 q.2) := by
    simpa [mov] using (curvatureOperatorMatrixAt_pulledTensor_eq_original_moving (I := I) (M := M)
      hT S basisAt iota hiota0 hgram ht q.2)
  have hstep3 : Metric.infDist
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) mov (S.base.rm04 q.1 q.2)))
        (hamiltonIveyConvexMatrixRegionEuclid K q.1) =
      Metric.infDist
        (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) gsb (S.base.rm04 q.1 q.2)))
        (hamiltonIveyConvexMatrixRegionEuclid K q.1) :=
    curvatureOperatorMatrixEuclid_infDist_eq_of_orthonormalBases (I := I) (M := M) gτ q.2 mov gsb
      horth_mov horth_gsb
      ⟨S.base.rm04 q.1 q.2, metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) gτ q.2⟩
      hK hq.1.1
  have hstep4 : intrinsicFiberCurvatureOperatorMatrix (I := I) gsb (S.base.rm04 q.1 q.2) =
      flowFrameOperatorMatrix (I := I) hT S hdim α q := by
    ext i j
    simp [flowFrameOperatorMatrix, hgsb, e, gτ]
  calc
    intrinsicFiberInfDist hT S basisAt iota K q.1 q.2
        = 2 * Metric.infDist
            (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) (basisAt q.2)
              (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)))
            (hamiltonIveyConvexMatrixRegionEuclid K q.1) := hstep1
    _ = 2 * Metric.infDist
            (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) mov (S.base.rm04 q.1 q.2)))
            (hamiltonIveyConvexMatrixRegionEuclid K q.1) := by rw [hstep2]
    _ = 2 * Metric.infDist
            (matrixToEuclid (intrinsicFiberCurvatureOperatorMatrix (I := I) gsb (S.base.rm04 q.1 q.2)))
            (hamiltonIveyConvexMatrixRegionEuclid K q.1) := by rw [hstep3]
    _ = 2 * Metric.infDist (matrixToEuclid (flowFrameOperatorMatrix (I := I) hT S hdim α q))
            (hamiltonIveyConvexMatrixRegionEuclid K q.1) := by rw [hstep4]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private lemma flowFrameOperatorMatrix_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (α : M) :
    ContinuousOn (fun q : ℝ × M =>
      matrixToEuclid (flowFrameOperatorMatrix (I := I) hT S hdim α q))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let U : Set M := smoothOrthoOpen (I := I) (M := M) α
  have hU_base : ∀ q : ℝ × M, q ∈ Set.Icc 0 T ×ˢ U →
      q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    exact smoothOrthoOpen_subset_baseSet (I := I) (M := M) α hq.2
  let e (a : Fin 3) (q : ℝ × M) : TangentSpace I q.2 :=
    intrinsicFlowFrame (I := I) (S.base.metric q.1) hdim α q a
  have he_cont : ∀ a : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2 (e a q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a
    have hmain := intrinsicChartFrameNorm_continuousOn_param (I := I) (M := M) hT S hS α
      (intrinsicFrameIndex (I := I) hdim α a)
    refine hmain.congr ?_
    intro q hq
    change TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α
          (intrinsicFrameIndex (I := I) hdim q.2 a) q.2) =
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α
          (intrinsicFrameIndex (I := I) hdim α a) q.2)
    apply congrArg (fun i : Fin (Module.finrank ℝ E) =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) q.2
        (intrinsicChartFrameNorm (I := I) (S.base.metric q.1) α i q.2))
    apply Fin.ext
    rfl
  have hentry4 : ∀ a b c d : Fin 3,
      ContinuousOn (fun q : ℝ × M =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e a q) (e b q) (e c q) (e d q))
        (Set.Icc 0 T ×ˢ U) := by
    intro a b c d
    have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc 0 T)
        (fun t x => S.base.rm04 t x) := by
      exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    rw [continuousOn_iff_continuous_restrict]
    let P := {q : ℝ × M // q.1 ∈ Set.Icc 0 T ∧ q.2 ∈ U}
    have heval := Tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := Set.Icc 0 T) (A := fun t x => S.base.rm04 t x) hA
      (P := P) (τ := fun p : P => p.1.1) (b := fun p : P => p.1.2)
      (continuous_fst.comp continuous_subtype_val) (fun p : P => p.2.1)
      (continuous_snd.comp continuous_subtype_val)
      (v := fun n : Fin 4 => fun p : P =>
        if n = 0 then e a p.1 else if n = 1 then e b p.1 else if n = 2 then e c p.1 else e d p.1)
      (by
        intro n
        fin_cases n
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont a))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont b))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont c))
        · simp
          simpa using (continuousOn_iff_continuous_restrict.mp (he_cont d)))
    refine heval.congr (fun p => ?_)
    change (S.base.rm04 p.1.1 p.1.2)
        (fun n : Fin 4 => if n = 0 then e a p.1 else if n = 1 then e b p.1 else if n = 2 then e c p.1 else e d p.1) =
      tensor04StdAt (I := I) (M := M) (S.base.rm04 p.1.1 p.1.2)
        (e a p.1) (e b p.1) (e c p.1) (e d p.1)
    rw [tensor04StdAt]
    congr 1
  have hmat_local : ContinuousOn (fun q : ℝ × M =>
      matrixToEuclid (fun i j : Fin 3 =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 i).1 q) (e (bivectorIndex3 i).2 q)
          (e (bivectorIndex3 j).2 q) (e (bivectorIndex3 j).1 q)))
      (Set.Icc 0 T ×ˢ U) := by
    have hfun : ContinuousOn (fun q : ℝ × M =>
        fun ij : Fin 3 × Fin 3 =>
        tensor04StdAt (I := I) (M := M) (S.base.rm04 q.1 q.2)
          (e (bivectorIndex3 ij.1).1 q) (e (bivectorIndex3 ij.1).2 q)
          (e (bivectorIndex3 ij.2).2 q) (e (bivectorIndex3 ij.2).1 q))
        (Set.Icc 0 T ×ˢ U) := by
      rw [continuousOn_iff_continuous_restrict]
      let P := {q : ℝ × M // q.1 ∈ Set.Icc 0 T ∧ q.2 ∈ U}
      exact continuous_pi (by
        intro ij
        simpa using (continuousOn_iff_continuous_restrict.mp (hentry4 (bivectorIndex3 ij.1).1
          (bivectorIndex3 ij.1).2 (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1)))
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 × Fin 3 => ℝ)).comp_continuousOn hfun
  simpa [flowFrameOperatorMatrix, e] using hmat_local

omit [SigmaCompactSpace M] in
private lemma fiberInfDist_continuousOn_local
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (α : M) {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M => intrinsicFiberInfDist hT S basisAt iota K q.1 q.2)
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
  classical
  let m : ℝ × M → EuclideanSpace ℝ (Fin 3 × Fin 3) := fun q =>
    matrixToEuclid (flowFrameOperatorMatrix (I := I) hT S hdim α q)
  have hm_cont : ContinuousOn m (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) := by
    simpa [m] using flowFrameOperatorMatrix_continuousOn_local (I := I) (M := M) hT S hS hdim α
  have hg : ContinuousOn (fun r : ℝ × (EuclideanSpace ℝ (Fin 3 × Fin 3)) =>
      Metric.infDist r.2 (hamiltonIveyConvexMatrixRegionEuclid K r.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))) :=
    continuousOn_infDist_hamiltonIveyRegion hK
  have hh : ContinuousOn (fun q : ℝ × M => (q.1, m q))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :=
    (continuous_fst.continuousOn).prodMk hm_cont
  have hmaps : Set.MapsTo (fun q : ℝ × M => (q.1, m q))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)))) := by
    intro q hq
    exact ⟨hq.1, trivial⟩
  have hcomp : ContinuousOn (fun q : ℝ × M =>
      Metric.infDist ((q.1, m q)).2 (hamiltonIveyConvexMatrixRegionEuclid K ((q.1, m q)).1))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :=
    hg.comp' hh hmaps
  have htwo : ContinuousOn (fun q : ℝ × M =>
      2 * Metric.infDist ((q.1, m q)).2 (hamiltonIveyConvexMatrixRegionEuclid K ((q.1, m q)).1))
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) :=
    (continuousOn_const.mul hcomp)
  refine htwo.congr ?_
  intro q hq
  simpa [m] using intrinsicFiberInfDist_eq_two_mul_flowFrameMatrixInfDist (I := I) (M := M)
    hT S basisAt iota hiota0 hgram horth0 hdim α hK (q := q) hq

omit [SigmaCompactSpace M] in
theorem fiberInfDist_continuousOn'
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M => intrinsicFiberInfDist hT S basisAt iota K q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  intro q hq
  let α : M := q.2
  have hlocal := fiberInfDist_continuousOn_local (I := I) (M := M) hT S hS hdim basisAt horth0 iota
    hiota0 hgram α hK
  have hqL : q ∈ Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
    exact ⟨hq.1, mem_smoothOrthoOpen (I := I) (M := M) α⟩
  have hL : ContinuousWithinAt
      (fun r : ℝ × M => intrinsicFiberInfDist hT S basisAt iota K r.1 r.2)
      (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) q :=
    hlocal.continuousWithinAt hqL
  have hmem_nhds : (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∈
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (smoothOrthoOpen_open (I := I) (M := M) α)
    · exact ⟨trivial, mem_smoothOrthoOpen (I := I) (M := M) α⟩
    · intro r hr
      have hEq : (Set.univ ×ˢ smoothOrthoOpen (I := I) (M := M) α) ∩
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) =
          Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α := by
        rw [Set.prod_inter_prod]
        simp
      exact (hEq ▸ hr)
  have heq : 𝓝[(Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)] q =
      𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q := by
    apply le_antisymm
    · exact nhdsWithin_mono q (by
        intro r hr
        exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hr).1, trivial⟩)
    · exact (nhdsWithin_le_iff (s := (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
        (t := (Set.Icc 0 T ×ˢ smoothOrthoOpen (I := I) (M := M) α)) (x := q)).mpr hmem_nhds
  change Tendsto (fun r : ℝ × M =>
      intrinsicFiberInfDist hT S basisAt iota K r.1 r.2)
    (𝓝[(Set.Icc 0 T ×ˢ (Set.univ : Set M))] q)
    (𝓝 (intrinsicFiberInfDist hT S basisAt iota K q.1 q.2))
  rw [← heq]
  exact hL

omit [SigmaCompactSpace M] in
theorem fiberInfDist_continuousOn_regionFile
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {K : ℝ} (hK : 0 < K) :
    ContinuousOn (fun q : ℝ × M =>
      letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) q.2) :=
        (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) q.2) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) q.2)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) q.2) :=
        @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) q.2)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) q.2 4).toCore.toCore
      Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (fiberHamiltonIveyRegion basisAt K q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  have h := fiberInfDist_continuousOn' (I := I) (M := M) hT S hS hdim basisAt horth0 iota hiota0 hgram hK
  refine h.congr ?_
  intro q hq
  simp [intrinsicFiberInfDist, intrinsicFiberHamiltonIveyRegion_eq_fiberHamiltonIveyRegion (I := I) basisAt K q.1 q.2]
end DifferentialGeometry.PDE.RicciFlow

end
