import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.RegionDistance
import DifferentialGeometry.Geometry.Curvature.DimensionThree.AlgebraicCurvatureOperatorMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

def fiberBivectorTwoForm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (i : Fin 3) (X Y : TangentSpace I x) : Real :=
  (g.inner x X (basis (bivectorIndex3 i).1)) * (g.inner x Y (basis (bivectorIndex3 i).2)) -
    (g.inner x X (basis (bivectorIndex3 i).2)) * (g.inner x Y (basis (bivectorIndex3 i).1))

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_add_left
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (x₁ x₂ y : TangentSpace I x) :
    fiberBivectorTwoForm g basis p (x₁ + x₂) y =
      fiberBivectorTwoForm g basis p x₁ y + fiberBivectorTwoForm g basis p x₂ y := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_add x₁ x₂]
  simp
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_add_right
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (X y₁ y₂ : TangentSpace I x) :
    fiberBivectorTwoForm g basis p X (y₁ + y₂) =
      fiberBivectorTwoForm g basis p X y₁ + fiberBivectorTwoForm g basis p X y₂ := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_add y₁ y₂]
  simp
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_smul_left
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (a : ℝ) (x₁ y : TangentSpace I x) :
    fiberBivectorTwoForm g basis p (a • x₁) y = a * fiberBivectorTwoForm g basis p x₁ y := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_smul a x₁]
  simp
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_smul_right
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (a : ℝ) (X y₁ : TangentSpace I x) :
    fiberBivectorTwoForm g basis p X (a • y₁) = a * fiberBivectorTwoForm g basis p X y₁ := by
  unfold fiberBivectorTwoForm
  rw [(g.inner x).map_smul a y₁]
  simp
  ring

noncomputable def fiberOperatorTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) : Tensor04At (I := I) (M := M) x :=
  { toMultilinearMap := MultilinearMap.mk' (R := ℝ) (M₁ := fun _ : Fin 4 => TangentSpace I x) (M₂ := ℝ)
      (fun m : Fin 4 → TangentSpace I x =>
        ∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
            fiberBivectorTwoForm g basis q (m 3) (m 2))
      (by
        intro m i x y
        fin_cases i
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (x + y) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p x (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p y (m 1) *
                  fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_left]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (x + y) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) x *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p (m 0) y *
                  fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (x + y)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) x) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                  fiberBivectorTwoForm g basis q (m 3) y)
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (x + y) (m 2)) =
            (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q x (m 2)) +
              (∑ p : Fin 3, ∑ q : Fin 3,
                Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                  fiberBivectorTwoForm g basis q y (m 2))
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_add_left]
          ring)
      (by
        intro m i c x
        fin_cases i
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (c • x) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p x (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_left]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (c • x) *
                fiberBivectorTwoForm g basis q (m 3) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) x *
                fiberBivectorTwoForm g basis q (m 3) (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) (c • x)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (m 3) x)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_right]
          ring
        · change (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q (c • x) (m 2)) =
            c * (∑ p : Fin 3, ∑ q : Fin 3,
              Rmat p q * fiberBivectorTwoForm g basis p (m 0) (m 1) *
                fiberBivectorTwoForm g basis q x (m 2))
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q hq
          rw [fiberBivectorTwoForm_smul_left]
          ring)
    cont := by
      unfold fiberBivectorTwoForm
      fun_prop }

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberOperatorTensor_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) (fiberOperatorTensor g basis Rmat) X Y Z W =
      ∑ p : Fin 3, ∑ q : Fin 3,
        Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z := by
  unfold tensor04StdAt fiberOperatorTensor
  change (∑ p : Fin 3, ∑ q : Fin 3,
      Rmat p q * fiberBivectorTwoForm g basis p (vec4 X Y Z W 0) (vec4 X Y Z W 1) *
        fiberBivectorTwoForm g basis q (vec4 X Y Z W 3) (vec4 X Y Z W 2)) =
    ∑ p : Fin 3, ∑ q : Fin 3,
      Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z
  simp [vec4]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberOperatorTensor_apply_basis
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3, (g.inner x (basis i) (basis j)) = if i = j then 1 else 0)
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    tensor04StdAt (I := I) (M := M) (fiberOperatorTensor g basis Rmat)
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) =
      Rmat i j := by
  classical
  rw [fiberOperatorTensor_apply]
  have hα : ∀ p : Fin 3, fiberBivectorTwoForm g basis p
      (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2) = if p = i then 1 else 0 := by
    intro p
    unfold fiberBivectorTwoForm
    fin_cases p <;> fin_cases i <;> simp [bivectorIndex3, horth]
  have hβ : ∀ q : Fin 3, fiberBivectorTwoForm g basis q
      (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2) = if q = j then 1 else 0 := by
    intro q
    unfold fiberBivectorTwoForm
    fin_cases q <;> fin_cases j <;> simp [bivectorIndex3, horth]
  simp [hα, hβ]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem tensor04CurvatureOperatorMatrixAt_fiberOperatorTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (Rmat : Matrix (Fin 3) (Fin 3) ℝ) :
    tensor04CurvatureOperatorMatrixAt (I := I) basis
        (fiberOperatorTensor g basis Rmat) = Rmat := by
  ext i j
  exact fiberOperatorTensor_apply_basis g basis horth Rmat i j

def fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {A | ∃ h : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
    curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, h⟩ ∈ hamiltonIveyConvexMatrixRegion K τ}

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem mem_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) (A : Tensor04At (I := I) (M := M) x) :
    A ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∃ h : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
        curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, h⟩ ∈
          hamiltonIveyConvexMatrixRegion K τ := by
  rfl

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveyRegion_eq_inter_preimage_euclidean
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) :
    fiberHamiltonIveyRegion basisAt K τ x =
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x :
          Set (Tensor04At (I := I) (M := M) x)) ∩
        (fun A : Tensor04At (I := I) (M := M) x =>
          matrixToEuclidean
            (tensor04CurvatureOperatorMatrixAt (I := I) (basisAt x) A)) ⁻¹'
          hamiltonIveyConvexMatrixRegionEuclidean K τ := by
  ext A
  rw [Set.mem_inter_iff, Set.mem_preimage, mem_fiberHamiltonIveyRegion]
  constructor
  · rintro ⟨hA, hmat⟩
    refine ⟨hA, ?_⟩
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff,
      euclideanToMatrix_matrixToEuclidean,
      tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt
        (I := I) (basisAt x)
          (⟨A, hA⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)]
    exact hmat
  · rintro ⟨hA, hmat⟩
    refine ⟨hA, ?_⟩
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff,
      euclideanToMatrix_matrixToEuclidean,
      tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt
        (I := I) (basisAt x)
          (⟨A, hA⟩ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)] at hmat
    exact hmat

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem convex_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M) :
    Convex ℝ (fiberHamiltonIveyRegion basisAt K τ x) := by
  let f : Tensor04At (I := I) (M := M) x →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    { toFun := fun A =>
        matrixToEuclidean
          (tensor04CurvatureOperatorMatrixAt (I := I) (basisAt x) A)
      map_add' := by
        intro A B
        ext ij
        simp [matrixToEuclidean, tensor04CurvatureOperatorMatrixAt]
      map_smul' := by
        intro c A
        ext ij
        simp [matrixToEuclidean, tensor04CurvatureOperatorMatrixAt] }
  rw [fiberHamiltonIveyRegion_eq_inter_preimage_euclidean]
  exact (Submodule.convex
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).inter
      (Convex.linear_preimage
        (convex_hamiltonIveyConvexMatrixRegionEuclidean hK hτ) f)

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem zero_mem_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M) :
    (0 : Tensor04At (I := I) (M := M) x) ∈
      fiberHamiltonIveyRegion basisAt K τ x := by
  refine (mem_fiberHamiltonIveyRegion basisAt K τ x 0).2 ⟨by simp, ?_⟩
  simpa [curvatureOperatorMatrixAt] using
    (zero_mem_hamiltonIveyConvexMatrixRegion hK hτ)

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem nonempty_fiberHamiltonIveyRegion
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M) :
    (fiberHamiltonIveyRegion basisAt K τ x).Nonempty := by
  exact ⟨0, zero_mem_fiberHamiltonIveyRegion basisAt hK hτ x⟩

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem isClosed_fiberHamiltonIveyRegion
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (x : M) :
    @IsClosed (Tensor04At (I := I) (M := M) x)
      (@InnerProductSpace.Core.toNormedAddCommGroup ℝ
        (Tensor04At (I := I) (M := M) x) _ _ _
          (tensor0SMetricData (I := I) g x 4).toCore).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fiberHamiltonIveyRegion basisAt K τ x) := by
  let metricNorm : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ
      (Tensor04At (I := I) (M := M) x) _ _ _
        (tensor0SMetricData (I := I) g x 4).toCore
  let metricTopology : TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
    metricNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let L : Tensor04At (I := I) (M := M) x →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    { toFun := fun A =>
        matrixToEuclidean
          (tensor04CurvatureOperatorMatrixAt (I := I) (basisAt x) A)
      map_add' := by
        intro A B
        ext ij
        simp [matrixToEuclidean, tensor04CurvatureOperatorMatrixAt]
      map_smul' := by
        intro c A
        ext ij
        simp [matrixToEuclidean, tensor04CurvatureOperatorMatrixAt] }
  have hAlgebraic : @IsClosed (Tensor04At (I := I) (M := M) x) metricTopology
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x :
        Set (Tensor04At (I := I) (M := M) x)) := by
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) g x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := metricNorm
    letI : NormedSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      InnerProductSpace.Core.toNormedSpace
    letI : IsBoundedSMul ℝ (Tensor04At (I := I) (M := M) x) := inferInstance
    letI : ContinuousSMul ℝ (Tensor04At (I := I) (M := M) x) := inferInstance
    exact @Submodule.closed_of_finiteDimensional ℝ
      (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
        metricTopology inferInstance inferInstance inferInstance inferInstance
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) inferInstance
  have hL : @Continuous (Tensor04At (I := I) (M := M) x)
      (EuclideanSpace ℝ (Fin 3 × Fin 3)) metricTopology inferInstance L := by
    letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
      (tensor0SMetricData (I := I) g x 4).toCore
    letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) := metricNorm
    letI : NormedSpace ℝ (Tensor04At (I := I) (M := M) x) :=
      InnerProductSpace.Core.toNormedSpace
    letI : IsBoundedSMul ℝ (Tensor04At (I := I) (M := M) x) := inferInstance
    letI : ContinuousSMul ℝ (Tensor04At (I := I) (M := M) x) := inferInstance
    exact @LinearMap.continuous_of_finiteDimensional ℝ inferInstance
      (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance metricTopology inferInstance inferInstance
      (EuclideanSpace ℝ (Fin 3 × Fin 3))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance L
  rw [fiberHamiltonIveyRegion_eq_inter_preimage_euclidean]
  exact hAlgebraic.inter
    ((isClosed_hamiltonIveyConvexMatrixRegionEuclidean hK).preimage hL)

def fiberHamiltonIveyNormalDirections
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {ν | ∃ h : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
    (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩))).eigenvalues₀ 0 < 0 ∨
      euclideanMatrixSymmetrization (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩)) = 0}

noncomputable def fiberHamiltonIveySupport
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) : ℝ := by
  classical
  exact if h : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x then
    4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
      (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩))
  else 0

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_anti
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p : Fin 3) (X Y : TangentSpace I x) :
    fiberBivectorTwoForm g basis p X Y = -fiberBivectorTwoForm g basis p Y X := by
  unfold fiberBivectorTwoForm
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberBivectorTwoForm_cyclic_antisymm
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (p q : Fin 3) (X Y Z W : TangentSpace I x) :
    (fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
      fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X +
      fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y) +
    (fiberBivectorTwoForm g basis q X Y * fiberBivectorTwoForm g basis p W Z +
      fiberBivectorTwoForm g basis q Y Z * fiberBivectorTwoForm g basis p W X +
      fiberBivectorTwoForm g basis q Z X * fiberBivectorTwoForm g basis p W Y) = 0 := by
  unfold fiberBivectorTwoForm
  fin_cases p <;> fin_cases q <;> simp [bivectorIndex3] <;> ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberBivectorTwoForm_continuous
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) (i : Fin 3) :
    Continuous (fun q : TangentSpace I x × TangentSpace I x =>
      fiberBivectorTwoForm g basis i q.1 q.2) := by
  unfold fiberBivectorTwoForm
  have hinner (e : TangentSpace I x) :
      Continuous (fun q : TangentSpace I x × TangentSpace I x => g.inner x q.1 e) := by
    fun_prop
  have hinner' (e : TangentSpace I x) :
      Continuous (fun q : TangentSpace I x × TangentSpace I x => g.inner x q.2 e) := by
    fun_prop
  exact ((hinner (basis (bivectorIndex3 i).1)).mul (hinner' (basis (bivectorIndex3 i).2))).sub
    ((hinner (basis (bivectorIndex3 i).2)).mul (hinner' (basis (bivectorIndex3 i).1)))

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberOperatorTensor_mem_algebraic
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    {Rmat : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rmat.IsSymm) :
    fiberOperatorTensor g basis Rmat ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  rw [mem_algebraicCurvatureTensorSubmodule_iff_symmetries]
  constructor
  · intro X Y Z W
    rw [fiberOperatorTensor_apply, fiberOperatorTensor_apply]
    have hzero : (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z) +
        (∑ p : Fin 3, ∑ q : Fin 3,
          Rmat p q * fiberBivectorTwoForm g basis p Y X * fiberBivectorTwoForm g basis q W Z) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro p hp
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro q hq
      rw [fiberBivectorTwoForm_anti g basis _ X Y]
      ring
    linarith
  · constructor
    · intro X Y Z W
      rw [fiberOperatorTensor_apply, fiberOperatorTensor_apply]
      have hzero : (∑ p : Fin 3, ∑ q : Fin 3,
            Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z) +
          (∑ p : Fin 3, ∑ q : Fin 3,
            Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q Z W) = 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro p hp
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro q hq
        rw [fiberBivectorTwoForm_anti g basis _ W Z]
        ring
      linarith
    · intro X Y Z W
      rw [fiberOperatorTensor_apply, fiberOperatorTensor_apply, fiberOperatorTensor_apply]
      simp only [← Finset.sum_add_distrib]
      let D : Fin 3 → Fin 3 → ℝ := fun p q =>
        fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
          fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X +
          fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y
      have hRsym : ∀ i j : Fin 3, Rmat i j = Rmat j i := by
        intro i j
        have h := congrFun (congrFun hR i) j
        simpa [Matrix.transpose_apply] using h.symm
      have hD : ∀ p q : Fin 3, D p q = -D q p := by
        intro p q
        have h := fiberBivectorTwoForm_cyclic_antisymm g basis p q X Y Z W
        linarith
      have hsum : ∀ p q : Fin 3,
          ((Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
              Rmat p q * fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X) +
            Rmat p q * fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y) =
          Rmat p q * D p q := by
        intro p q
        unfold D
        ring
      have hDsum : (∑ p : Fin 3, ∑ q : Fin 3,
            ((Rmat p q * fiberBivectorTwoForm g basis p X Y * fiberBivectorTwoForm g basis q W Z +
                Rmat p q * fiberBivectorTwoForm g basis p Y Z * fiberBivectorTwoForm g basis q W X) +
              Rmat p q * fiberBivectorTwoForm g basis p Z X * fiberBivectorTwoForm g basis q W Y)) =
          (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) := by
        apply Finset.sum_congr rfl; intro p hp
        apply Finset.sum_congr rfl; intro q hq
        exact hsum p q
      rw [hDsum]
      have hzero : (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) +
          (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) = 0 := by
        have hswap : (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) =
            ∑ p : Fin 3, ∑ q : Fin 3, Rmat q p * D q p := by
          have h1 : (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q) =
              ∑ ij : Fin 3 × Fin 3, Rmat ij.1 ij.2 * D ij.1 ij.2 := by
            rw [Fintype.sum_prod_type]
          have h2 : (∑ p : Fin 3, ∑ q : Fin 3, Rmat q p * D q p) =
              ∑ ij : Fin 3 × Fin 3, Rmat ij.2 ij.1 * D ij.2 ij.1 := by
            rw [Fintype.sum_prod_type]
          calc
            (∑ p : Fin 3, ∑ q : Fin 3, Rmat p q * D p q)
                = ∑ ij : Fin 3 × Fin 3, Rmat ij.1 ij.2 * D ij.1 ij.2 := h1
            _ = ∑ ij : Fin 3 × Fin 3, Rmat ij.2 ij.1 * D ij.2 ij.1 := by
                rw [sum_pair_swap (fun ij : Fin 3 × Fin 3 => Rmat ij.1 ij.2 * D ij.1 ij.2)]
            _ = ∑ p : Fin 3, ∑ q : Fin 3, Rmat q p * D q p := h2.symm
        nth_rewrite 2 [hswap]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro p hp
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero; intro q hq
        rw [show D p q = -D q p from hD p q]
        rw [show Rmat q p = Rmat p q from hRsym q p]
        ring
      linarith

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberOperatorTensor_curvatureOperatorMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3, g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    {Rmat : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rmat.IsSymm) :
    curvatureOperatorMatrixAt (I := I) x basis
        ⟨fiberOperatorTensor g basis Rmat, fiberOperatorTensor_mem_algebraic g basis hR⟩ = Rmat := by
  ext i j
  exact fiberOperatorTensor_apply_basis g basis horth Rmat i j

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner0S_algebraic_eq_four_inner_matrixToEuclidean
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)
        (B : Tensor04At (I := I) (M := M) x) =
      4 * inner ℝ (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x basis B))
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x basis A)) := by
  have h4 := inner0S_algebraic_eq_four_mul_operatorInner g x basis horth A B
  rw [h4]
  congr 1
  rw [inner_matrixToEuclidean]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro q hq
  change curvatureOperatorMatrixAt (I := I) x basis A p q * curvatureOperatorMatrixAt (I := I) x basis B p q =
    curvatureOperatorMatrixAt (I := I) x basis B p q * curvatureOperatorMatrixAt (I := I) x basis A p q
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma euclideanMatrixSymmetrization_isSymm (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    (euclideanMatrixSymmetrization v).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  simp [euclideanMatrixSymmetrization, Matrix.transpose_apply]
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma isSymm_of_isHermitian_real {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) :
    A.IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.conjTranspose, Matrix.transpose_apply] using h

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma euclideanToMatrix_isHermitian_of_mem_hamiltonIveyConvexMatrixRegionEuclidean
    {K τ : ℝ} {c : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hc : c ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    (euclideanToMatrix c).IsHermitian := by
  have hcm : euclideanToMatrix c ∈ hamiltonIveyConvexMatrixRegion K τ :=
    (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ c).mp hc
  rw [hamiltonIveyConvexMatrixRegion] at hcm
  exact hcm.1

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean
    {K τ : ℝ} {c : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hc : c ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    (euclideanToMatrix c).IsSymm :=
  isSymm_of_isHermitian_real (euclideanToMatrix_isHermitian_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean
    {K τ : ℝ} {w : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (c : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (hc : c ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ) :
    inner ℝ w c = inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization w)) c := by
  have hcherm := euclideanToMatrix_isHermitian_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc
  have h := inner_matrixToEuclidean_symm w (euclideanToMatrix c) hcherm
  simpa [matrixToEuclidean_euclideanToMatrix] using h

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma euclideanMatrixSymmetrization_euclideanMatrixSymmetrization_matrixToEuclidean
    (v : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    euclideanMatrixSymmetrization (matrixToEuclidean (euclideanMatrixSymmetrization v)) = euclideanMatrixSymmetrization v := by
  unfold euclideanMatrixSymmetrization
  rw [euclideanToMatrix_matrixToEuclidean]
  ext i j
  simp [Matrix.transpose_apply]
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma finiteSupportDirections_of_euclideanMatrixSymmetrization_eq
    {K τ : ℝ} {v w : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hv : v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ))
    (h : euclideanMatrixSymmetrization v = euclideanMatrixSymmetrization w) :
    w ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
  unfold finiteSupportDirections
  rcases hv with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  calc
    inner ℝ w c = inner ℝ v c := by
      rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean (w := w) c hc]
      rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean (w := v) c hc]
      rw [← h]
    _ ≤ B := hB ⟨c, hc, rfl⟩

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_of_euclideanMatrixSymmetrization_eq
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    {v w : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hv : v ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ))
    (h : euclideanMatrixSymmetrization v = euclideanMatrixSymmetrization w) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ v =
      hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w := by
  have hw : w ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) :=
    finiteSupportDirections_of_euclideanMatrixSymmetrization_eq hv h
  have h1 := hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction_of_finiteSupportDirections
    hK hτ v hv
  have h2 := hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction_of_finiteSupportDirections
    hK hτ w hw
  rw [h1, h2]
  unfold supportFunction
  apply congrArg sSup
  ext x
  constructor <;> rintro ⟨c, hc, rfl⟩ <;> refine ⟨c, hc, ?_⟩
  · rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean (w := v) c hc]
    rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean (w := w) c hc]
    rw [h]
  · rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean (w := w) c hc]
    rw [inner_eq_symm_inner_of_mem_hamiltonIveyConvexMatrixRegionEuclidean (w := v) c hc]
    rw [← h]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma fiberHamiltonIveySupport_eq
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    fiberHamiltonIveySupport basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) := by
  unfold fiberHamiltonIveySupport
  rw [dif_pos hν]

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner0S_fiberOperatorTensor_eq
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {Rmat : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rmat.IsSymm) :
    inner0S (I := I) g x 4 A (fiberOperatorTensor g basis Rmat) =
      4 * inner ℝ (matrixToEuclidean Rmat)
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x basis ⟨A, hA⟩)) := by
  have h4 := inner0S_algebraic_eq_four_inner_matrixToEuclidean g x basis horth
    ⟨A, hA⟩ ⟨fiberOperatorTensor g basis Rmat, fiberOperatorTensor_mem_algebraic g basis hR⟩
  rw [h4]
  congr 1
  congr 1
  congr 1
  exact fiberOperatorTensor_curvatureOperatorMatrix g basis
    (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth i j) hR

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma sSup_mul_image
    {s : Set ℝ} (hs : BddAbove s) (hsne : s.Nonempty) :
    sSup {x : ℝ | ∃ y ∈ s, x = 4 * y} = 4 * sSup s := by
  have hLUB : IsLUB s (sSup s) := isLUB_csSup hsne hs
  have hLUB' : IsLUB {x : ℝ | ∃ y ∈ s, x = 4 * y} (4 * sSup s) := by
    constructor
    · rintro x ⟨y, hy, rfl⟩
      exact mul_le_mul_of_nonneg_left (hLUB.1 hy) (by norm_num)
    · intro u hu
      have hdiv : ∀ y ∈ s, y ≤ u / 4 := by
        intro y hy
        have hy' : 4 * y ≤ u := hu ⟨y, hy, rfl⟩
        exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr hy'
      have hsup_le : sSup s ≤ u / 4 := hLUB.2 hdiv
      exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mp hsup_le
  exact hLUB'.csSup_eq (by
    rcases hsne with ⟨y, hy⟩
    exact ⟨4 * y, ⟨y, hy, rfl⟩⟩)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private lemma inner0S_sub_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 A (B - C) = inner0S (I := I) g x 4 A B - inner0S (I := I) g x 4 A C := by
  unfold inner0S MetricFiberData.inner
  exact map_sub ((tensor0SMetricData (I := I) g x 4).flat A) B C

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveyRegion_mem_iff_forall_support_le
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    (A : Tensor04At (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    A ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ fiberHamiltonIveyNormalDirections basisAt x →
          inner0S (I := I) g x 4 A ν ≤ fiberHamiltonIveySupport basisAt K τ x ν := by
  constructor
  · intro hAregion ν hν
    rcases hAregion with ⟨hAlg, hmat⟩
    rcases hν with ⟨hν, hcond⟩
    let matA := curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hAlg⟩
    let matν := curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩
    have hν' : matrixToEuclidean matν ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
      rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
      exact hcond
    have hmatA' : matrixToEuclidean matA ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
      simpa [matA, euclideanToMatrix_matrixToEuclidean] using hmat
    have hmain := (hamiltonIveyConvexMatrixRegionEuclidean_mem_iff_forall_support_le hK hτ (matrixToEuclidean matA)).mp
      hmatA' (matrixToEuclidean matν) hν'
    have hinner : inner0S (I := I) g x 4 A ν =
        4 * inner ℝ (matrixToEuclidean matν) (matrixToEuclidean matA) :=
      inner0S_algebraic_eq_four_inner_matrixToEuclidean g x (basisAt x) (horth0 x) ⟨A, hAlg⟩ ⟨ν, hν⟩
    have hsup : fiberHamiltonIveySupport basisAt K τ x ν =
        4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean matν) :=
      fiberHamiltonIveySupport_eq basisAt K τ x hν
    calc
      inner0S (I := I) g x 4 A ν = 4 * inner ℝ (matrixToEuclidean matν) (matrixToEuclidean matA) := hinner
      _ ≤ 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean matν) := by
        nlinarith [hmain]
      _ = fiberHamiltonIveySupport basisAt K τ x ν := hsup.symm
  · intro hle
    have hmatAherm : (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩).IsHermitian :=
      curvatureOperatorMatrixAt_isHermitian x (basisAt x) ⟨A, hA⟩
    have hmatA' : matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩) ∈
        hamiltonIveyConvexMatrixRegionEuclidean K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
      refine (hamiltonIveyConvexMatrixRegionEuclidean_mem_iff_forall_support_le hK hτ
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩))).mpr ?_
      intro w hw
      let w' : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclidean (euclideanMatrixSymmetrization w)
      have hsymm : euclideanMatrixSymmetrization w = euclideanMatrixSymmetrization w' := by
        change euclideanMatrixSymmetrization w = euclideanMatrixSymmetrization (matrixToEuclidean (euclideanMatrixSymmetrization w))
        exact (euclideanMatrixSymmetrization_euclideanMatrixSymmetrization_matrixToEuclidean w).symm
      have hw' : w' ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) :=
        finiteSupportDirections_of_euclideanMatrixSymmetrization_eq hw hsymm
      let νT : Tensor04At (I := I) (M := M) x := fiberOperatorTensor g (basisAt x) (euclideanMatrixSymmetrization w)
      have hνTalg : νT ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberOperatorTensor_mem_algebraic g (basisAt x) (euclideanMatrixSymmetrization_isSymm w)
      have hνTN : νT ∈ fiberHamiltonIveyNormalDirections basisAt x := by
        unfold fiberHamiltonIveyNormalDirections
        refine ⟨hνTalg, ?_⟩
        have hfs' : matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨νT, hνTalg⟩) ∈
            finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
          rw [show matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨νT, hνTalg⟩) = w' by
            dsimp [νT]
            rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
              (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j) (euclideanMatrixSymmetrization_isSymm w)]]
          exact hw'
        exact (mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ
          (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨νT, hνTalg⟩))).mp hfs'
      have hieq : inner0S (I := I) g x 4 A νT =
          4 * inner ℝ w' (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) := by
        have h4 := inner0S_fiberOperatorTensor_eq g (basisAt x) (horth0 x) hA (euclideanMatrixSymmetrization_isSymm w)
        rw [h4]
      have hsup' : fiberHamiltonIveySupport basisAt K τ x νT =
          4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w' := by
        rw [fiberHamiltonIveySupport_eq basisAt K τ x hνTalg]
        congr 1
        rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
          (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j) (euclideanMatrixSymmetrization_isSymm w)]
      have hmain := hle νT hνTN
      rw [hieq, hsup'] at hmain
      have hwle : inner ℝ w' (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) ≤
          hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w' := by
        nlinarith
      have hsupEq : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w' =
          hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w :=
        (hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_of_euclideanMatrixSymmetrization_eq hK hτ (v := w) (w := w') hw hsymm).symm
      have hinnerEq : inner ℝ w (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) =
          inner ℝ w' (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩)) := by
        rw [inner_matrixToEuclidean_symm w (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩) hmatAherm]
      rw [hinnerEq]
      rwa [← hsupEq]
    exact ⟨hA, by
      simpa [euclideanToMatrix_matrixToEuclidean] using
        (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ
          (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨A, hA⟩))).mp hmatA'⟩

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveySupport_eq_sSup
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ fiberHamiltonIveyNormalDirections basisAt x) :
    fiberHamiltonIveySupport basisAt K τ x ν =
      sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
  rcases hν with ⟨hνalg, hcond⟩
  let matν := curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hνalg⟩
  let ν' : EuclideanSpace ℝ (Fin 3 × Fin 3) := matrixToEuclidean matν
  have hν' : ν' ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
    rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
    exact hcond
  have hsup : fiberHamiltonIveySupport basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ ν' := by
    rw [fiberHamiltonIveySupport_eq basisAt K τ x hνalg]
  have hEq := hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_supportFunction_of_finiteSupportDirections
    hK hτ ν' hν'
  unfold supportFunction at hEq
  have hset : {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} =
      {x : ℝ | ∃ c : EuclideanSpace ℝ (Fin 3 × Fin 3),
        c ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ x = 4 * inner ℝ ν' c} := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqalg, hqmat⟩
      let c : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
        matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨q, hqalg⟩)
      refine ⟨c, ?_, ?_⟩
      · rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
        simpa [c, euclideanToMatrix_matrixToEuclidean] using hqmat
      · have h4 := inner0S_algebraic_eq_four_inner_matrixToEuclidean g x (basisAt x) (horth0 x)
          ⟨q, hqalg⟩ ⟨ν, hνalg⟩
        simpa [ν', c] using h4
    · rintro ⟨c, hc, rfl⟩
      let q := fiberOperatorTensor g (basisAt x) (euclideanToMatrix c)
      have hqalg : q ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberOperatorTensor_mem_algebraic g (basisAt x)
          (euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)
      refine ⟨q, ⟨hqalg, ?_⟩, ?_⟩
      · rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
          (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
          (euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)]
        exact (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ c).mp hc
      · have h4 := inner0S_algebraic_eq_four_inner_matrixToEuclidean g x (basisAt x) (horth0 x)
          ⟨q, hqalg⟩ ⟨ν, hνalg⟩
        rw [h4]
        congr 1
        rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
          (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
          (euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)]
        rw [matrixToEuclidean_euclideanToMatrix]
  calc
    fiberHamiltonIveySupport basisAt K τ x ν = 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ ν' := hsup
    _ = 4 * sSup {x : ℝ | ∃ c : EuclideanSpace ℝ (Fin 3 × Fin 3),
          c ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ x = inner ℝ ν' c} := by
      rw [hEq]
    _ = sSup {x : ℝ | ∃ c : EuclideanSpace ℝ (Fin 3 × Fin 3),
          c ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ∧ x = 4 * inner ℝ ν' c} := by
      rw [← sSup_mul_image hν' (⟨(0 : ℝ), ⟨(0 : EuclideanSpace ℝ (Fin 3 × Fin 3)),
        ⟨zero_mem_hamiltonIveyConvexMatrixRegionEuclidean hK hτ, by simp⟩⟩⟩)]
      apply congrArg sSup
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨c, hc, rfl⟩
        exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        refine ⟨inner ℝ ν' c, ?_⟩
        constructor
        · exact ⟨c, hc, rfl⟩
        · rfl
    _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
      rw [hset]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem mem_fiberHamiltonIveyNormalDirections_iff
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {ν : Tensor04At (I := I) (M := M) x} :
    ν ∈ fiberHamiltonIveyNormalDirections basisAt x ↔
      ∃ h : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
        matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, h⟩) ∈
          finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
  unfold fiberHamiltonIveyNormalDirections
  constructor <;> rintro ⟨hν, hc⟩ <;> refine ⟨hν, ?_⟩
  · rwa [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
  · rwa [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ] at hc

omit [CompleteSpace E] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveyRegion_normal
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {p : Tensor04At (I := I) (M := M) x}
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hnormal : ∀ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x → inner0S (I := I) g x 4 ν (q - p) ≤ 0) :
    ν ∈ fiberHamiltonIveyNormalDirections basisAt x := by
  unfold fiberHamiltonIveyNormalDirections
  refine ⟨hν, ?_⟩
  rw [← mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ]
  have hbdd : BddAbove {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 ν q} := by
    refine ⟨inner0S (I := I) g x 4 ν p, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    have hqle : inner0S (I := I) g x 4 ν q - inner0S (I := I) g x 4 ν p ≤ 0 := by
      have h := hnormal q hq
      rw [inner0S_sub_right g x ν q p] at h
      linarith
    linarith
  unfold finiteSupportDirections
  refine ⟨inner0S (I := I) g x 4 ν p / 4, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  let q := fiberOperatorTensor g (basisAt x) (euclideanToMatrix c)
  have hqalg : q ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberOperatorTensor_mem_algebraic g (basisAt x)
      (euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)
  have hqregion : q ∈ fiberHamiltonIveyRegion basisAt K τ x := by
    refine ⟨hqalg, ?_⟩
    rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
      (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
      (euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)]
    exact (mem_hamiltonIveyConvexMatrixRegionEuclidean_iff K τ c).mp hc
  have hle : inner0S (I := I) g x 4 ν q ≤ inner0S (I := I) g x 4 ν p := by
    have hqle : inner0S (I := I) g x 4 ν q - inner0S (I := I) g x 4 ν p ≤ 0 := by
      have h := hnormal q hqregion
      rw [inner0S_sub_right g x ν q p] at h
      linarith
    linarith
  have h4 : 4 * inner ℝ (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) c =
      inner0S (I := I) g x 4 ν q := by
    have h4' := inner0S_algebraic_eq_four_inner_matrixToEuclidean g x (basisAt x) (horth0 x)
      ⟨ν, hν⟩ ⟨q, hqalg⟩
    rw [h4']
    congr 1
    rw [fiberOperatorTensor_curvatureOperatorMatrix g (basisAt x)
      (fun i j => by simpa [OrthonormalBasisAt, delta3] using horth0 x i j)
      (euclideanToMatrix_isSymm_of_mem_hamiltonIveyConvexMatrixRegionEuclidean hc)]
    rw [matrixToEuclidean_euclideanToMatrix]
    rw [real_inner_comm]
  have hle4 : 4 * inner ℝ (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) c ≤
      inner0S (I := I) g x 4 ν p := by
    rw [h4]
    exact hle
  exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr hle4

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberHamiltonIveyRegion_matrixImage_eq_regionEuclidean_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (K τ : ℝ) :
    (fun A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
      matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x))) ''
      ((fun A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
        (A : Tensor04At (I := I) (M := M) x)) ⁻¹'
        fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x)
    = hamiltonIveyConvexMatrixRegionEuclidean K τ := by
  classical
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [Set.mem_preimage] at hA
    rw [fiberHamiltonIveyRegion_eq_inter_preimage_euclidean] at hA
    exact hA.2
  · intro hq
    have hmat_mem : euclideanToMatrix q ∈ hamiltonIveyConvexMatrixRegion K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff] at hq
      simpa [euclideanToMatrix_matrixToEuclidean] using hq
    have hherm : (euclideanToMatrix q).IsHermitian := by
      rw [hamiltonIveyConvexMatrixRegion] at hmat_mem
      exact hmat_mem.1
    have hsymm : (euclideanToMatrix q).IsSymm := by
      rw [Matrix.IsSymm]
      ext i j
      have h := congrFun (congrFun hherm i) j
      simpa [Matrix.conjTranspose, Matrix.transpose_apply, star_trivial] using h
    let A₀ : Tensor04At (I := I) (M := M) x :=
      fiberOperatorTensor (I := I) g basis (euclideanToMatrix q)
    have hA₀ : A₀ ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
      fiberOperatorTensor_mem_algebraic (I := I) g basis hsymm
    have hmat : tensor04CurvatureOperatorMatrixAt (I := I) basis A₀ = euclideanToMatrix q := by
      exact tensor04CurvatureOperatorMatrixAt_fiberOperatorTensor
        (I := I) g basis horth (euclideanToMatrix q)
    refine ⟨⟨A₀, hA₀⟩, ?_, ?_⟩
    · rw [Set.mem_preimage]
      rw [fiberHamiltonIveyRegion_eq_inter_preimage_euclidean]
      constructor
      · exact hA₀
      · change matrixToEuclidean
          (tensor04CurvatureOperatorMatrixAt (I := I) basis A₀) ∈
            hamiltonIveyConvexMatrixRegionEuclidean K τ
        rw [hmat]
        rw [matrixToEuclidean_euclideanToMatrix]
        exact hq
    · change matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) basis A₀) = q
      rw [hmat]
      exact matrixToEuclidean_euclideanToMatrix q

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem infDist_fiberHamiltonIveyRegion_eq_two_mul_matrixInfDist_of_orthonormal
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
    Metric.infDist A (fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x) =
      2 * Metric.infDist (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) basis A))
        (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
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
    fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x
  let S : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) :=
    hamiltonIveyConvexMatrixRegionEuclidean K τ
  let m : Tensor04At (I := I) (M := M) x → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun B => matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) basis B)
  have himg : (fun B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
        m (B : Tensor04At (I := I) (M := M) x)) ''
      ((fun B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
        (B : Tensor04At (I := I) (M := M) x)) ⁻¹' C) = S := by
    simpa [C, S, m] using fiberHamiltonIveyRegion_matrixImage_eq_regionEuclidean_of_orthonormal
      (I := I) g x basis horth K τ
  have hdist : ∀ (B : Tensor04At (I := I) (M := M) x),
      B ∈ C → dist A B = 2 * dist (m A) (m B) := by
    intro B hB
    have hBmem := hB
    change B ∈ fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x at hBmem
    rw [fiberHamiltonIveyRegion_eq_inter_preimage_euclidean] at hBmem
    have hB' : B ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := hBmem.1
    have hd := dist_algebraicCurvatureTensor_eq_two_mul_matrixDist_of_orthonormal (I := I) (M := M)
      g x basis horth ⟨A, hA⟩ ⟨B, hB'⟩
    simpa [m] using hd
  have hS_ne : S.Nonempty := nonempty_hamiltonIveyConvexMatrixRegionEuclidean hK hτ
  have hC_ne : C.Nonempty := by
    exact nonempty_fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) hK hτ x
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
        (mem_fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x B).mp hB |>.1
      have hBm : m B ∈ S := by
        exact (mem_fiberHamiltonIveyRegion (I := I) (fun _ : M => basis) K τ x B).mp hB |>.2
      have hd := hdist B hB
      have h1 : Metric.infDist (m A) S ≤ dist (m A) (m B) :=
        Metric.infDist_le_dist_of_mem hBm
      nlinarith
    exact (Metric.le_infDist hC_ne).mpr hle

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
private lemma inner_basis_eq_repr3
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
    [SigmaCompactSpace M] [T2Space M] in
theorem fiberBivectorTwoForm_eq_repr
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (p : Fin 3) (X Y : TangentSpace I x) :
    fiberBivectorTwoForm (I := I) g basis p X Y =
      basis.repr X (bivectorIndex3 p).1 * basis.repr Y (bivectorIndex3 p).2 -
        basis.repr X (bivectorIndex3 p).2 * basis.repr Y (bivectorIndex3 p).1 := by
  unfold fiberBivectorTwoForm
  rw [inner_basis_eq_repr3 (I := I) g basis horth X (bivectorIndex3 p).1]
  rw [inner_basis_eq_repr3 (I := I) g basis horth X (bivectorIndex3 p).2]
  rw [inner_basis_eq_repr3 (I := I) g basis horth Y (bivectorIndex3 p).1]
  rw [inner_basis_eq_repr3 (I := I) g basis horth Y (bivectorIndex3 p).2]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M]
    [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M]
    in
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
    [SigmaCompactSpace M] [T2Space M] in
theorem fiberBivectorTwoForm_sum_pair
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (X Y Z W : TangentSpace I x) :
    (∑ p : Fin 3,
        fiberBivectorTwoForm (I := I) g basis p X Y *
          fiberBivectorTwoForm (I := I) g basis p Z W) =
      g.inner x X Z * g.inner x Y W - g.inner x X W * g.inner x Y Z := by
  classical
  simp_rw [fiberBivectorTwoForm_eq_repr (I := I) g basis horth]
  rw [inner_eq_sum_repr3 (I := I) horth X Z, inner_eq_sum_repr3 (I := I) horth Y W,
    inner_eq_sum_repr3 (I := I) horth X W, inner_eq_sum_repr3 (I := I) horth Y Z]
  exact bivectorSum_prod_eq (basis.repr X) (basis.repr Y) (basis.repr Z) (basis.repr W)

omit [E : Type*] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [H : Type*] [TopologicalSpace H] [I : ModelWithCorners ℝ E H]
    [M : Type*] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M]
    [T2Space M] in
private lemma delta3_bivector_mul
    (i j : Fin 3) :
    delta3 (bivectorIndex3 i).1 (bivectorIndex3 j).1 *
        delta3 (bivectorIndex3 i).2 (bivectorIndex3 j).2 -
      delta3 (bivectorIndex3 i).1 (bivectorIndex3 j).2 *
        delta3 (bivectorIndex3 i).2 (bivectorIndex3 j).1 = delta3 i j := by
  fin_cases i <;> fin_cases j <;> simp [bivectorIndex3, delta3]

noncomputable def bivectorFrameChangeMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun p i => fiberBivectorTwoForm (I := I) g b p
    (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem bivectorFrameChangeMatrix_mul_transpose_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (hb' : OrthonormalBasisAt (I := I) g x b') :
    bivectorFrameChangeMatrix (I := I) g b b' *
        (bivectorFrameChangeMatrix (I := I) g b b').transpose = 1 := by
  classical
  let O : Matrix (Fin 3) (Fin 3) ℝ := bivectorFrameChangeMatrix (I := I) g b b'
  have hOtO : O.transpose * O = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ p : Fin 3, bivectorFrameChangeMatrix (I := I) g b b' p i *
          bivectorFrameChangeMatrix (I := I) g b b' p j) =
        if i = j then 1 else 0
    simp only [bivectorFrameChangeMatrix]
    rw [fiberBivectorTwoForm_sum_pair (I := I) g b hb
      (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
      (b' (bivectorIndex3 j).1) (b' (bivectorIndex3 j).2)]
    rw [hb' (bivectorIndex3 i).1 (bivectorIndex3 j).1, hb' (bivectorIndex3 i).2 (bivectorIndex3 j).2,
      hb' (bivectorIndex3 i).1 (bivectorIndex3 j).2, hb' (bivectorIndex3 i).2 (bivectorIndex3 j).1]
    simpa [delta3] using delta3_bivector_mul i j
  exact matrixTransposeMul_orthogonal (O := O.transpose) (by simpa [Matrix.transpose_transpose] using hOtO)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
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

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem tensor04CurvatureOperatorMatrixAt_conj_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x) =
      (bivectorFrameChangeMatrix (I := I) g b b').transpose *
        tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x) *
        bivectorFrameChangeMatrix (I := I) g b b' := by
  classical
  let Mat : Matrix (Fin 3) (Fin 3) ℝ := tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x)
  let O : Matrix (Fin 3) (Fin 3) ℝ := bivectorFrameChangeMatrix (I := I) g b b'
  have hsymm : Mat.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    have hM : (curvatureOperatorMatrixAt (I := I) x b A).IsHermitian :=
      curvatureOperatorMatrixAt_isHermitian (I := I) x b A
    have h := congrFun (congrFun hM i) j
    simpa [Mat, Matrix.conjTranspose, Matrix.transpose_apply, star_trivial] using h
  have hTensor_mem : fiberOperatorTensor (I := I) g b Mat ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    fiberOperatorTensor_mem_algebraic (I := I) g b hsymm
  have hTensor_map : tensor04CurvatureOperatorMatrixAt (I := I) b
      (fiberOperatorTensor (I := I) g b Mat) = Mat :=
    tensor04CurvatureOperatorMatrixAt_fiberOperatorTensor (I := I) g b hb Mat
  have hA_eq : fiberOperatorTensor (I := I) g b Mat = (A : Tensor04At x) := by
    have hzero : (⟨fiberOperatorTensor (I := I) g b Mat, hTensor_mem⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) - A = 0 := by
      apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal (I := I) (M := M) g x b hb
      change tensor04CurvatureOperatorMatrixAt (I := I) b
          (fiberOperatorTensor (I := I) g b Mat - (A : Tensor04At x)) = 0
      rw [tensor04CurvatureOperatorMatrixAt_sub]
      rw [hTensor_map]
      change Mat - Mat = 0
      simp
    exact congrArg (fun Y : algebraicCurvatureTensorSubmodule (I := I) (M := M) x =>
      (Y : Tensor04At (I := I) (M := M) x)) (sub_eq_zero.mp hzero)
  ext i j
  calc
    tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x) i j
        = tensor04StdAt (I := I) (M := M) (A : Tensor04At x)
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1) := rfl
    _ = tensor04StdAt (I := I) (M := M) (fiberOperatorTensor (I := I) g b Mat)
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1) := by rw [hA_eq]
    _ = ∑ p : Fin 3, ∑ q : Fin 3,
          Mat p q * fiberBivectorTwoForm (I := I) g b p (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2) *
            fiberBivectorTwoForm (I := I) g b q (b' (bivectorIndex3 j).1) (b' (bivectorIndex3 j).2) :=
          fiberOperatorTensor_apply (I := I) g b Mat
            (b' (bivectorIndex3 i).1) (b' (bivectorIndex3 i).2)
            (b' (bivectorIndex3 j).2) (b' (bivectorIndex3 j).1)
    _ = (O.transpose * Mat * O) i j := by
          rw [show (O.transpose * Mat * O) i j = ∑ p : Fin 3, ∑ q : Fin 3,
              Mat p q * O p i * O q j from matrix_conj_dot Mat O i j]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          simp only [O, bivectorFrameChangeMatrix]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorMatrixEuclidean_infDist_eq_of_orthonormal_bases
    (g : SmoothRiemannianMetric I M) (x : M)
    (b b' : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb : OrthonormalBasisAt (I := I) g x b)
    (hb' : OrthonormalBasisAt (I := I) g x b')
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    Metric.infDist (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x)))
      (hamiltonIveyConvexMatrixRegionEuclidean K τ) =
    Metric.infDist (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x)))
      (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
  classical
  let Mat : Matrix (Fin 3) (Fin 3) ℝ := tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x)
  let O : Matrix (Fin 3) (Fin 3) ℝ := bivectorFrameChangeMatrix (I := I) g b b'
  have hconj : tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x) = O.transpose * Mat * O := by
    simpa [Mat, O] using tensor04CurvatureOperatorMatrixAt_conj_of_orthonormal (I := I) (M := M) g b b' hb A
  have hOorth : O * O.transpose = 1 := by
    simpa [O] using bivectorFrameChangeMatrix_mul_transpose_of_orthonormal (I := I) (M := M) g b b' hb hb'
  calc
    Metric.infDist (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) b (A : Tensor04At x)))
        (hamiltonIveyConvexMatrixRegionEuclidean K τ)
        = Metric.infDist (matrixToEuclidean Mat) (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by rfl
    _ = Metric.infDist (matrixToEuclidean (O.transpose * Mat * O)) (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
          exact infDist_matrixToEuclidean_orthogonal_conj hK hτ Mat O hOorth
    _ = Metric.infDist (matrixToEuclidean (tensor04CurvatureOperatorMatrixAt (I := I) b' (A : Tensor04At x)))
          (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by rw [hconj]
end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
