import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Convex.Bundle
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.RegionTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.TensorInnerLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.CurvatureEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.FixedFrameEvolution
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Radial.TensorExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Analysis.Calculus.Inverse.MatrixSmoothness
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators
open scoped Matrix.Norms.Frobenius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]

section IntrinsicRegionData

variable {T : ℝ} (hT : 0 < T)

private noncomputable def regionProjMatrix
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (ν : Tensor04At (I := I) (M := M) x) : Matrix (Fin 3) (Fin 3) Real :=
  curvatureOperatorMatrixAt (I := I) x basis (algebraicCurvatureTensorProjection (I := I) g x ν)

private noncomputable def regionSupport
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
    (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν))

private noncomputable def regionSupportDeriv
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K : ℝ} (hK : 0 < K) (τ : ℝ) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK τ
    (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν))

private noncomputable def regionSource
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (p ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  4 * inner ℝ
    (hamiltonIveyMatrixReactionEuclidean (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) p)))
    (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν))

private def regionNormalDirections
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  {ν | (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν))).eigenvalues₀ 0 < 0 ∨
    euclideanMatrixSymmetrization (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)) = 0}

end IntrinsicRegionData

section RegionMatrixLemmas

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionProjMatrix_eq_curvatureOperatorMatrixAt
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    regionProjMatrix (I := I) g basis A =
      curvatureOperatorMatrixAt (I := I) x basis ⟨A, hA⟩ := by
  unfold regionProjMatrix
  have heq : algebraicCurvatureTensorProjection (I := I) g x A = ⟨A, hA⟩ := by
    apply Subtype.ext
    exact algebraicCurvatureTensorProjection_eq_self (I := I) g x hA
  rw [heq]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem inner0S_eq_four_mul_inner_regionProjMatrix
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    {q : Tensor04At (I := I) (M := M) x}
    (hq : q ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 q ν =
      4 * inner ℝ (matrixToEuclidean (regionProjMatrix (I := I) g basis ν))
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x basis ⟨q, hq⟩)) := by
  have hpq := algebraicCurvatureTensorProjection_inner (I := I) g x ν ⟨q, hq⟩
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    algebraicCurvatureTensorProjection (I := I) g x ν
  have h4 : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) q =
      4 * inner ℝ (matrixToEuclidean (regionProjMatrix (I := I) g basis ν))
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x basis ⟨q, hq⟩)) := by
    have hmain := inner0S_algebraic_eq_four_mul_matrixInner (I := I) g x basis horth pν ⟨q, hq⟩
    rw [tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt,
      tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt] at hmain
    have hreg : regionProjMatrix (I := I) g basis ν =
        curvatureOperatorMatrixAt (I := I) x basis pν := by
      rfl
    rw [hreg]
    exact hmain
  calc
    inner0S (I := I) g x 4 q ν
        = inner0S (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) := by
          rw [inner0S, inner0S]
          rw [MetricFiberData.inner_comm (tensor0SMetricData (I := I) g x 4) q ν]
          rw [MetricFiberData.inner_comm (tensor0SMetricData (I := I) g x 4) q (pν : Tensor04At (I := I) (M := M) x)]
          simpa [pν, inner0S] using hpq.symm
    _ = inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) q := by
          rw [inner0S, inner0S]
          exact MetricFiberData.inner_comm (tensor0SMetricData (I := I) g x 4) q (pν : Tensor04At (I := I) (M := M) x)
    _ = 4 * inner ℝ (matrixToEuclidean (regionProjMatrix (I := I) g basis ν))
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x basis ⟨q, hq⟩)) := by
          simpa [pν, regionProjMatrix] using h4

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupport_eq_of_mem_algebraic
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    regionSupport (I := I) g basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) := by
  unfold regionSupport
  congr 1
  congr 1
  rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fiberHamiltonIveySupport_eq_of_mem_algebraic
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    fiberHamiltonIveySupport basisAt K τ x ν =
      4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
        (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩)) := by
  unfold fiberHamiltonIveySupport
  rw [dif_pos hν]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupport_eq_fiberHamiltonIveySupport_of_mem_algebraic
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K τ : ℝ) (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    regionSupport (I := I) g basisAt K τ x ν =
      fiberHamiltonIveySupport basisAt K τ x ν := by
  rw [regionSupport_eq_of_mem_algebraic (I := I) g basisAt K τ x hν,
    fiberHamiltonIveySupport_eq_of_mem_algebraic (I := I) basisAt K τ x hν]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem mem_regionNormalDirections_iff_mem_fiberNormalDirections
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    ν ∈ regionNormalDirections (I := I) g basisAt x ↔
      ν ∈ fiberHamiltonIveyNormalDirections basisAt x := by
  constructor
  · intro h
    rw [fiberHamiltonIveyNormalDirections]
    simp only [Set.mem_ofPred_eq]
    refine ⟨hν, ?_⟩
    rcases h with hlt | hz
    · left
      simpa [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hlt
    · right
      simpa [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hz
  · intro h
    rw [fiberHamiltonIveyNormalDirections] at h
    simp only [Set.mem_ofPred_eq] at h
    rcases h with ⟨hν', hlt⟩
    rw [regionNormalDirections]
    simp only [Set.mem_ofPred_eq]
    rcases hlt with hlt | hz
    · left
      have hw : curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν'⟩ =
          curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩ := by
        apply curvatureOperatorMatrixAt_independent_of_membership_proof
      simpa [hw, regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hlt
    · right
      have hw : curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν'⟩ =
          curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨ν, hν⟩ := by
        apply curvatureOperatorMatrixAt_independent_of_membership_proof
      simpa [hw, regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν] using hz

end RegionMatrixLemmas

section RegionCharacterization

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_mem_iff_forall_normalDirections_of_mem_algebraicCurvatureTensorSubmodule
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    (p : Tensor04At (I := I) (M := M) x)
    (hp : p ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    p ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) g basisAt x →
          inner0S (I := I) g x 4 ν p ≤ regionSupport (I := I) g basisAt K τ x ν := by
  constructor
  · intro hpC ν hν
    let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
      matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)
    have hinner : inner0S (I := I) g x 4 ν p =
        4 * inner ℝ w (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩)) := by
      calc
        inner0S (I := I) g x 4 ν p = inner0S (I := I) g x 4 p ν := by
          exact inner0S_symm (I := I) (s := 4) g x ν p
        _ = 4 * inner ℝ w (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩)) := by
          simpa [w] using (inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) (horth0 x) hp ν)
    have hsupport : regionSupport (I := I) g basisAt K τ x ν =
        4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w := by
      rfl
    have hwfs : w ∈ finiteSupportDirections (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
      rw [mem_finiteSupportDirections_hamiltonIvey_region_iff hK hτ w]
      exact hν
    rcases hpC with ⟨hAlg, hmat⟩
    have hpmat : matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩) ∈
        hamiltonIveyConvexMatrixRegionEuclidean K τ := by
      rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
      have hw : curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hAlg⟩ =
          curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩ := by
        apply curvatureOperatorMatrixAt_independent_of_membership_proof
      rwa [hw]
    have hmain := (hamiltonIveyConvexMatrixRegionEuclidean_mem_iff_forall_support_le hK hτ
      (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩))).mp
      hpmat w hwfs
    calc
      inner0S (I := I) g x 4 ν p
          = 4 * inner ℝ w (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hp⟩)) := hinner
      _ ≤ 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w := by
            nlinarith [hmain]
      _ = regionSupport (I := I) g basisAt K τ x ν := hsupport.symm
  · intro hle
    have hback := (fiberHamiltonIveyRegion_mem_iff_forall_support_le (I := I) g basisAt horth0 hK hτ x p hp).mpr
    apply hback
    intro ν hν
    rcases hν with ⟨hνalg, hc⟩
    have hνN : ν ∈ regionNormalDirections (I := I) g basisAt x := by
      exact (mem_regionNormalDirections_iff_mem_fiberNormalDirections (I := I) g basisAt x hνalg).mpr ⟨hνalg, hc⟩
    have hle' := hle ν hνN
    have hsup : regionSupport (I := I) g basisAt K τ x ν =
        fiberHamiltonIveySupport basisAt K τ x ν := by
      exact regionSupport_eq_fiberHamiltonIveySupport_of_mem_algebraic (I := I) g basisAt K τ x hνalg
    rw [inner0S_symm (I := I) (s := 4) g x ν p] at hle'
    rw [← hsup]
    exact hle'

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupport_eq_sSup
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {ν : Tensor04At (I := I) (M := M) x}
    (hν : ν ∈ regionNormalDirections (I := I) g basisAt x) :
    regionSupport (I := I) g basisAt K τ x ν =
      sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
  have hν₀alg : (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    (algebraicCurvatureTensorProjection (I := I) g x ν).2
  have hreg : regionProjMatrix (I := I) g (basisAt x)
        (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
      regionProjMatrix (I := I) g (basisAt x) ν := by
    unfold regionProjMatrix
    have hself : algebraicCurvatureTensorProjection (I := I) g x
          (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
        algebraicCurvatureTensorProjection (I := I) g x ν := by
      apply Subtype.ext
      exact algebraicCurvatureTensorProjection_eq_self (I := I) g x (algebraicCurvatureTensorProjection (I := I) g x ν).2
    rw [hself]
  have hν₀N : (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x) ∈
      fiberHamiltonIveyNormalDirections basisAt x := by
    exact (mem_regionNormalDirections_iff_mem_fiberNormalDirections (I := I) g basisAt x hν₀alg).mp
      (by
        change
          (euclideanMatrixSymmetrization_isHermitian
            (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x)
              (algebraicCurvatureTensorProjection (I := I) g x ν)))).eigenvalues₀ 0 < 0 ∨
            euclideanMatrixSymmetrization
              (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x)
                (algebraicCurvatureTensorProjection (I := I) g x ν))) = 0
        change
          (euclideanMatrixSymmetrization_isHermitian
            (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν))).eigenvalues₀ 0 < 0 ∨
            euclideanMatrixSymmetrization
              (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)) = 0 at hν
        rw [hreg]
        exact hν)
  have hmain := fiberHamiltonIveySupport_eq_sSup (I := I) g basisAt horth0 hK hτ x hν₀N
  have hsup : fiberHamiltonIveySupport basisAt K τ x
        (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x) =
      regionSupport (I := I) g basisAt K τ x ν := by
    unfold regionSupport fiberHamiltonIveySupport
    rw [dif_pos hν₀alg]
    rw [← hreg]
    rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hν₀alg]
  calc
    regionSupport (I := I) g basisAt K τ x ν
        = fiberHamiltonIveySupport basisAt K τ x
            (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x) := hsup.symm
    _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧
            r = inner0S (I := I) g x 4 q (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x)} := hmain
    _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberHamiltonIveyRegion basisAt K τ x ∧ r = inner0S (I := I) g x 4 q ν} := by
          congr 1
          ext r
          constructor <;> rintro ⟨q, hq, rfl⟩ <;> refine ⟨q, hq, ?_⟩
          · rw [inner0S_symm (I := I) (s := 4) g x q ν]
            rw [inner0S_symm (I := I) (s := 4) g x q
              (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x)]
            rcases hq with ⟨hqalg, hqmat⟩
            exact algebraicCurvatureTensorProjection_inner (I := I) g x ν ⟨q, hqalg⟩
          · rw [inner0S_symm (I := I) (s := 4) g x q
              (algebraicCurvatureTensorProjection (I := I) g x ν : Tensor04At (I := I) (M := M) x)]
            rw [inner0S_symm (I := I) (s := 4) g x q ν]
            rcases hq with ⟨hqalg, hqmat⟩
            exact (algebraicCurvatureTensorProjection_inner (I := I) g x ν ⟨q, hqalg⟩).symm

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem regionNormalDirections_of_normal
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    {p : Tensor04At (I := I) (M := M) x}
    (hp : p ∈ fiberHamiltonIveyRegion basisAt K τ x)
    {ν : Tensor04At (I := I) (M := M) x}
    (hnormal : ∀ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x → inner0S (I := I) g x 4 ν (q - p) ≤ 0) :
    ν ∈ regionNormalDirections (I := I) g basisAt x := by
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    algebraicCurvatureTensorProjection (I := I) g x ν
  have hν₀alg : (pν : Tensor04At (I := I) (M := M) x) ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    pν.2
  have hnormal' : ∀ q : Tensor04At (I := I) (M := M) x,
      q ∈ fiberHamiltonIveyRegion basisAt K τ x → inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (q - p) ≤ 0 := by
    intro q hq
    have h1 := hnormal q hq
    rcases hq with ⟨hqalg, hqmat⟩
    rcases hp with ⟨hpalg, hpmat⟩
    have h2 : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (q - p) =
        inner0S (I := I) g x 4 ν (q - p) := by
      exact algebraicCurvatureTensorProjection_inner (I := I) g x ν
        ⟨(q - p), Submodule.sub_mem (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) hqalg hpalg⟩
    rwa [h2]
  have hν₀N : (pν : Tensor04At (I := I) (M := M) x) ∈ fiberHamiltonIveyNormalDirections basisAt x :=
    fiberHamiltonIveyRegion_normal (I := I) g basisAt horth0 hK hτ x hν₀alg hnormal'
  have hν₀R : (pν : Tensor04At (I := I) (M := M) x) ∈ regionNormalDirections (I := I) g basisAt x :=
    (mem_regionNormalDirections_iff_mem_fiberNormalDirections (I := I) g basisAt x hν₀alg).mpr hν₀N
  rw [regionNormalDirections] at hν₀R ⊢
  simp only [Set.mem_ofPred_eq] at hν₀R ⊢
  have hreg : regionProjMatrix (I := I) g (basisAt x) (pν : Tensor04At (I := I) (M := M) x) =
      regionProjMatrix (I := I) g (basisAt x) ν := by
    unfold regionProjMatrix
    have hself : algebraicCurvatureTensorProjection (I := I) g x (pν : Tensor04At (I := I) (M := M) x) = pν := by
      apply Subtype.ext
      exact algebraicCurvatureTensorProjection_eq_self (I := I) g x pν.2
    rw [hself]
  simpa [hreg] using hν₀R

end RegionCharacterization

section RegionSupportTime

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupport_continuousOn_time
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K T : ℝ} (hK : 0 < K) (x : M) (ν : Tensor04At (I := I) (M := M) x) :
    ContinuousOn (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) (Set.Icc 0 T) := by
  let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)
  by_cases hlt : (euclideanMatrixSymmetrization_isHermitian w).eigenvalues₀ 0 < 0
  · have hmain := hamiltonIveyConvexMatrixRegionSupportEuclidean_continuousOn (K := K) (T := T) hK w hlt
    have hmain4 : ContinuousOn (fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w)
        (Set.Icc 0 T) := hmain.const_mul 4
    have hfun : (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) =
        fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w := by
      funext τ
      simp [regionSupport, w]
    simpa [hfun] using hmain4
  · have hconst : ∀ τ : ℝ, regionSupport (I := I) g basisAt K τ x ν = 0 := by
      intro τ
      unfold regionSupport hamiltonIveyConvexMatrixRegionSupportEuclidean
      rw [if_neg hlt]
      simp
    have hconst0 : (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) =
        fun _ : ℝ => 0 := by
      funext τ
      exact hconst τ
    simpa [hconst0] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 T))

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupport_hasDerivAt_time
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : 0 < t) (x : M) (ν : Tensor04At (I := I) (M := M) x) :
    HasDerivAt (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν)
      (regionSupportDeriv (I := I) g basisAt hK t x ν) t := by
  let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)
  by_cases hlt : (euclideanMatrixSymmetrization_isHermitian w).eigenvalues₀ 0 < 0
  · have hmain := hamiltonIveyConvexMatrixRegionSupportEuclidean_hasDerivAt hK ht w
    have hmain4 : HasDerivAt (fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w)
        (4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w) t := hmain.const_mul 4
    have hfun : (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) =
        fun τ : ℝ => 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K τ w := by
      funext τ
      simp [regionSupport, w]
    have hmain4' : HasDerivAt (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν)
        (4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w) t := by
      simpa [hfun] using hmain4
    simpa [regionSupportDeriv, w] using hmain4'
  · have hnot : ¬ (euclideanMatrixSymmetrization_isHermitian w).eigenvalues₀ 0 < 0 := hlt
    have hconst : ∀ τ : ℝ, regionSupport (I := I) g basisAt K τ x ν = 0 := by
      intro τ
      unfold regionSupport hamiltonIveyConvexMatrixRegionSupportEuclidean
      rw [if_neg hlt]
      simp
    have hmain : HasDerivAt (fun τ : ℝ => regionSupport (I := I) g basisAt K τ x ν) 0 t := by
      simpa [hconst] using (hasDerivAt_const (x := t) (c := (0 : ℝ)))
    have hz : regionSupportDeriv (I := I) g basisAt hK t x ν = 0 := by
      unfold regionSupportDeriv hamiltonIveyConvexMatrixRegionSupportDeriv
      rw [if_neg hnot]
      simp
    simpa [hz] using hmain

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSource_le_regionSupportDeriv_of_tangent
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (x : M)
    {p ν : Tensor04At (I := I) (M := M) x}
    (hp : p ∈ fiberHamiltonIveyRegion basisAt K t x)
    (hν : ν ∈ regionNormalDirections (I := I) g basisAt x)
    (htangent : regionSupport (I := I) g basisAt K t x ν = inner0S (I := I) g x 4 ν p) :
    regionSource (I := I) g basisAt x p ν ≤
      regionSupportDeriv (I := I) g basisAt hK t x ν := by
  rcases hp with ⟨hpalg, hpmat⟩
  let w : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)
  let A : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hpalg⟩)
  have hA : A ∈ hamiltonIveyConvexMatrixRegionEuclidean K t := by
    rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
    simpa [A, euclideanToMatrix_matrixToEuclidean] using hpmat
  have hinner : inner0S (I := I) g x 4 ν p = 4 * inner ℝ w A := by
    calc
      inner0S (I := I) g x 4 ν p = inner0S (I := I) g x 4 p ν := by
        exact inner0S_symm (I := I) (s := 4) g x ν p
      _ = 4 * inner ℝ (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν))
          (matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) ⟨p, hpalg⟩)) := by
        exact inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) (horth0 x) hpalg ν
  have hsupport : regionSupport (I := I) g basisAt K t x ν = 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K t w := by
    rfl
  have htouching : hamiltonIveyConvexMatrixRegionSupportEuclidean K t w = inner ℝ w A := by
    have h4 : 4 * hamiltonIveyConvexMatrixRegionSupportEuclidean K t w = 4 * inner ℝ w A := by
      rw [← hsupport, ← hinner]
      exact htangent
    nlinarith
  rcases hν with hlt | hz
  · have hmain := hamiltonIveyConvexMatrixRegionSupportEuclidean_reaction_le_deriv hK (le_of_lt ht) w hlt A hA htouching
      (hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w)
      (hamiltonIveyConvexMatrixRegionSupportEuclidean_hasDerivAt hK ht w)
    have hsource : regionSource (I := I) g basisAt x p ν =
        4 * inner ℝ (hamiltonIveyMatrixReactionEuclidean A) w := by
      unfold regionSource
      rw [regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hpalg]
    have hderiv : regionSupportDeriv (I := I) g basisAt hK t x ν =
        4 * hamiltonIveyConvexMatrixRegionSupportDeriv K hK t w := by
      rfl
    rw [hsource, hderiv]
    exact mul_le_mul_of_nonneg_left hmain (by norm_num)
  · have hsymm0 : euclideanMatrixSymmetrization w = 0 := by
      change euclideanMatrixSymmetrization (matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)) = 0
      exact hz
    have hw0 : w = 0 := by
      have hwreg : euclideanToMatrix w = regionProjMatrix (I := I) g (basisAt x) ν := by
        rw [euclideanToMatrix_matrixToEuclidean]
      have hM : (euclideanToMatrix w).IsSymm := by
        rw [hwreg]
        have hherm : (curvatureOperatorMatrixAt (I := I) x (basisAt x)
            (algebraicCurvatureTensorProjection (I := I) g x ν)).IsHermitian := by
          exact curvatureOperatorMatrixAt_isHermitian x (basisAt x) (algebraicCurvatureTensorProjection (I := I) g x ν)
        exact Matrix.IsSymm.ext (fun i j => by
          have hh := congrFun (congrFun hherm i) j
          change curvatureOperatorMatrixAt (I := I) x (basisAt x)
              (algebraicCurvatureTensorProjection (I := I) g x ν) j i =
            curvatureOperatorMatrixAt (I := I) x (basisAt x)
              (algebraicCurvatureTensorProjection (I := I) g x ν) i j
          exact hh)
      have hzeroM : euclideanToMatrix w = 0 := by
        have h := euclideanMatrixSymmetrization_matrixToEuclidean_symm (M := euclideanToMatrix w) hM
        rw [matrixToEuclidean_euclideanToMatrix] at h
        rw [hsymm0] at h
        exact h.symm
      rw [← matrixToEuclidean_euclideanToMatrix w, hzeroM]
      ext ij
      simp [matrixToEuclidean]
    have hsource0 : regionSource (I := I) g basisAt x p ν = 0 := by
      rw [regionSource]
      rw [show matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν) = w from rfl, hw0]
      simp
    have hderiv0 : regionSupportDeriv (I := I) g basisAt hK t x ν = 0 := by
      rw [regionSupportDeriv]
      rw [show matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν) = w from rfl]
      rw [hamiltonIveyConvexMatrixRegionSupportDeriv_eq_zero_of_symm_zero hK t w hsymm0]
      simp
    rw [hsource0, hderiv0]

end RegionSupportTime

section PulledScalarization

private noncomputable def regionSupportVector
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (ν : Tensor04At (I := I) (M := M) x) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) ν)

private noncomputable def pulledRmComp
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) : FourComp M (Fin 3) :=
  fun t x a b c d => tensor04StandardAt (uhlenbeckPulledRm04At S basisAt iota t x)
    (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)

private noncomputable def uhlenbeckPullbackTensorAt
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (A : Tensor04At (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x :=
  A.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem pulledMatrix_eq_curvatureOperatorMatrixAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (hAlg : uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x =
      matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPulledRm04At S basisAt iota t x, hAlg⟩) := by
  have hmain := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basisAt x)
    (A := ⟨uhlenbeckPulledRm04At S basisAt iota t x, hAlg⟩)
    (pulledRm := pulledRmComp S basisAt iota) (t := t)
    (by intro a b c d; rfl)
  rw [← hmain]
  unfold matrixToEuclidean uhlenbeckCurvatureOperatorMatrixAsMatrix
    uhlenbeckCurvatureOperatorMatrix pulledRmComp
  rfl

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem pulledScalarization_eq
    (g : SmoothRiemannianMetric I M)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (horth : OrthonormalBasisAt (I := I) g x (basisAt x))
    (hAlg : uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (uhlenbeckPulledRm04At S basisAt iota t x) ν =
      4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x)
        (regionSupportVector g basisAt x ν) := by
  have hmain := inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) horth hAlg ν
  rw [← pulledMatrix_eq_curvatureOperatorMatrixAt (I := I) (M := M) S basisAt iota t x hAlg] at hmain
  rw [real_inner_comm] at hmain
  simpa [regionSupportVector] using hmain

omit [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem regionSource_at_pulled_eq
    (g : SmoothRiemannianMetric I M)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (hAlg : uhlenbeckPulledRm04At S basisAt iota t x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    regionSource g basisAt x (uhlenbeckPulledRm04At S basisAt iota t x) ν =
      4 * inner ℝ (hamiltonIveyMatrixReactionEuclidean
        (uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x))
        (regionSupportVector g basisAt x ν) := by
  have hreg : regionProjMatrix (I := I) g (basisAt x) (uhlenbeckPulledRm04At S basisAt iota t x) =
      curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPulledRm04At S basisAt iota t x, hAlg⟩ :=
    regionProjMatrix_eq_curvatureOperatorMatrixAt (I := I) g (basisAt x) hAlg
  unfold regionSource
  rw [hreg]
  rw [← pulledMatrix_eq_curvatureOperatorMatrixAt (I := I) (M := M) S basisAt iota t x hAlg]
  simp [regionSupportVector]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupportVector_norm_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x (basisAt x))
    (ν : Tensor04At (I := I) (M := M) x) :
    ‖regionSupportVector g basisAt x ν‖ ≤ tensor04FiberNorm (I := I) g x ν / 2 := by
  let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := algebraicCurvatureTensorProjection (I := I) g x ν
  have hmain := inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) horth pν.2
    (pν : Tensor04At (I := I) (M := M) x)
  have hid : algebraicCurvatureTensorProjection (I := I) g x (pν : Tensor04At (I := I) (M := M) x) = pν :=
    algebraicCurvatureTensorProjection_coe (I := I) g x pν
  have hreg : matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) (pν : Tensor04At (I := I) (M := M) x)) =
      matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) pν) := by
    unfold regionProjMatrix
    rw [hid]
  have hw : matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x) pν) =
      regionSupportVector g basisAt x ν := by
    unfold regionSupportVector
    rw [regionProjMatrix]
  have h4 : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) =
      4 * ‖regionSupportVector g basisAt x ν‖ ^ 2 := by
    have hA : matrixToEuclidean (regionProjMatrix (I := I) g (basisAt x) (pν : Tensor04At (I := I) (M := M) x)) =
        regionSupportVector g basisAt x ν := hreg.trans hw
    rw [hA, hw] at hmain
    simpa [norm_sq_eq_re_inner] using hmain
  have hsqrt : ‖regionSupportVector g basisAt x ν‖ =
      Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / 2 := by
    have hnn : 0 ≤ inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) :=
      MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x 4) (pν : Tensor04At (I := I) (M := M) x)
    have hsq : ‖regionSupportVector g basisAt x ν‖ ^ 2 =
        inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) / 4 := by
      linarith [h4]
    have hsqrt' : Real.sqrt (‖regionSupportVector g basisAt x ν‖ ^ 2) = ‖regionSupportVector g basisAt x ν‖ :=
      Real.sqrt_sq (norm_nonneg (regionSupportVector g basisAt x ν))
    calc
      ‖regionSupportVector g basisAt x ν‖ = Real.sqrt (‖regionSupportVector g basisAt x ν‖ ^ 2) := hsqrt'.symm
      _ = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x) / 4) := by rw [hsq]
      _ = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / Real.sqrt 4 := by
            rw [Real.sqrt_div hnn (4 : ℝ)]
      _ = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / 2 := by norm_num
  calc
    ‖regionSupportVector g basisAt x ν‖
        = Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) / 2 := hsqrt
    _ ≤ tensor04FiberNorm (I := I) g x ν / 2 := by
      have hle : tensor04FiberNorm (I := I) g x (pν : Tensor04At (I := I) (M := M) x) ≤
          tensor04FiberNorm (I := I) g x ν := algebraicCurvatureTensorProjection_norm_le (I := I) g x ν
      have hle' : Real.sqrt (inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) (pν : Tensor04At (I := I) (M := M) x)) ≤
          tensor04FiberNorm (I := I) g x ν := by
        unfold tensor04FiberNorm at hle ⊢
        exact hle
      exact div_le_div_of_nonneg_right hle' (by norm_num)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSupportVector_sub
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (ν₁ ν₂ : Tensor04At (I := I) (M := M) x) :
    regionSupportVector g basisAt x (ν₁ - ν₂) =
      regionSupportVector g basisAt x ν₁ - regionSupportVector g basisAt x ν₂ := by
  unfold regionSupportVector regionProjMatrix
  have hsub' : algebraicCurvatureTensorProjection (I := I) g x (ν₁ - ν₂) =
      algebraicCurvatureTensorProjection (I := I) g x ν₁ - algebraicCurvatureTensorProjection (I := I) g x ν₂ :=
    (algebraicCurvatureTensorProjection (I := I) g x).map_sub ν₁ ν₂
  rw [hsub']
  ext ij
  simp only [matrixToEuclidean, curvatureOperatorMatrixAt]
  exact Tensor0SSpace.sub_apply 4 x (algebraicCurvatureTensorProjection (I := I) g x ν₁ : Tensor04At (I := I) (M := M) x)
    (algebraicCurvatureTensorProjection (I := I) g x ν₂ : Tensor04At (I := I) (M := M) x)
    (vec4 (basisAt x (bivectorIndex3 ij.1).1) (basisAt x (bivectorIndex3 ij.1).2)
      (basisAt x (bivectorIndex3 ij.2).2) (basisAt x (bivectorIndex3 ij.2).1))

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem regionSource_lipschitzOn_closedBall_uniform
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ L : NNReal, ∀ x : M, ∀ ν : Tensor04At (I := I) (M := M) x,
      letI : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
        (tensor0SMetricData (I := I) g x 4).toCore
      letI : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
      letI : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
      LipschitzOnWith (L * ‖ν‖₊)
        (fun p : Tensor04At (I := I) (M := M) x => regionSource g basisAt x p ν)
        (Metric.closedBall 0 (2 * R)) := by
  classical
  rcases hamiltonIveyMatrixReactionEuclidean_lipschitzOn_closedBall R hR with ⟨Lst, hLst⟩
  refine ⟨Lst, ?_⟩
  intro x ν
  let : InnerProductSpace.Core ℝ (Tensor04At (I := I) (M := M) x) :=
    (tensor0SMetricData (I := I) g x 4).toCore
  let : NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore
  let : InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) g x 4).toCore.toCore
  have hnorm_eq : ∀ A : Tensor04At (I := I) (M := M) x,
      tensor04FiberNorm (I := I) g x A = ‖A‖ := tensor0SFiberNorm_eq_norm (I := I) g x
  have hw : ∀ A : Tensor04At (I := I) (M := M) x,
      ‖regionSupportVector g basisAt x A‖ ≤ ‖A‖ / 2 := by
    intro A
    have h := regionSupportVector_norm_le (I := I) g x basisAt (horth x) A
    rwa [hnorm_eq A] at h
  have hAball : ∀ A : Tensor04At (I := I) (M := M) x,
      A ∈ Metric.closedBall 0 (2 * R) →
        regionSupportVector g basisAt x A ∈ Metric.closedBall 0 R := by
    intro A hA
    have hA' : ‖A‖ ≤ 2 * R := by
      simpa [dist_eq_norm, sub_zero] using (Metric.mem_closedBall.mp hA)
    have hle := hw A
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero]
    nlinarith
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro p hp q hq
  rw [dist_eq_norm, dist_eq_norm]
  let Ap : EuclideanSpace ℝ (Fin 3 × Fin 3) := regionSupportVector g basisAt x p
  let Aq : EuclideanSpace ℝ (Fin 3 × Fin 3) := regionSupportVector g basisAt x q
  let wν : EuclideanSpace ℝ (Fin 3 × Fin 3) := regionSupportVector g basisAt x ν
  have hsrc : regionSource g basisAt x p ν - regionSource g basisAt x q ν =
      4 * inner ℝ (hamiltonIveyMatrixReactionEuclidean Ap -
        hamiltonIveyMatrixReactionEuclidean Aq) wν := by
    dsimp [Ap, Aq, wν]
    unfold regionSource
    simp only [regionSupportVector]
    rw [← mul_sub]
    congr 1
    rw [← inner_sub_left]
  have h1 : |inner ℝ (hamiltonIveyMatrixReactionEuclidean Ap -
      hamiltonIveyMatrixReactionEuclidean Aq) wν| ≤
      ‖hamiltonIveyMatrixReactionEuclidean Ap - hamiltonIveyMatrixReactionEuclidean Aq‖ * ‖wν‖ := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (hamiltonIveyMatrixReactionEuclidean Ap -
      hamiltonIveyMatrixReactionEuclidean Aq) wν
    simpa [Real.norm_eq_abs] using h
  have h2 : ‖hamiltonIveyMatrixReactionEuclidean Ap - hamiltonIveyMatrixReactionEuclidean Aq‖ ≤
      (Lst : ℝ) * ‖Ap - Aq‖ := by
    have hLip := hLst.dist_le_mul Ap (hAball p hp) Aq (hAball q hq)
    simpa [dist_eq_norm, Ap, Aq] using hLip
  have h3 : ‖wν‖ ≤ ‖ν‖ / 2 := by
    dsimp [wν]
    exact hw ν
  have h4 : ‖Ap - Aq‖ ≤ ‖p - q‖ / 2 := by
    have hsub : regionSupportVector g basisAt x (p - q) =
        regionSupportVector g basisAt x p - regionSupportVector g basisAt x q :=
      regionSupportVector_sub (I := I) g basisAt x p q
    have h := hw (p - q)
    rwa [hsub] at h
  have habs : |regionSource g basisAt x p ν - regionSource g basisAt x q ν| ≤ (Lst : ℝ) * ‖ν‖ * ‖p - q‖ := by
    rw [hsrc]
    calc
      |4 * inner ℝ (hamiltonIveyMatrixReactionEuclidean Ap -
          hamiltonIveyMatrixReactionEuclidean Aq) wν|
          = 4 * |inner ℝ (hamiltonIveyMatrixReactionEuclidean Ap -
              hamiltonIveyMatrixReactionEuclidean Aq) wν| := by
            rw [abs_mul]
            norm_num
      _ ≤ 4 * (‖hamiltonIveyMatrixReactionEuclidean Ap -
          hamiltonIveyMatrixReactionEuclidean Aq‖ * ‖wν‖) := by
            exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 4 * (((Lst : ℝ) * ‖Ap - Aq‖) * (‖ν‖ / 2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _)
              (mul_nonneg (NNReal.coe_nonneg Lst) (norm_nonneg _))) (by norm_num)
      _ ≤ 4 * (((Lst : ℝ) * (‖p - q‖ / 2)) * (‖ν‖ / 2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left h4 (NNReal.coe_nonneg Lst))
              le_rfl (by positivity) (by positivity)) (by norm_num)
      _ = (Lst : ℝ) * ‖ν‖ * ‖p - q‖ := by ring
  have hcoef : (Lst : ℝ) * ‖ν‖ = ((Lst * ‖ν‖₊ : NNReal) : ℝ) := by
    rw [NNReal.coe_mul]
    simp
  rw [Real.norm_eq_abs]
  calc
    |regionSource g basisAt x p ν - regionSource g basisAt x q ν| ≤ (Lst : ℝ) * ‖ν‖ * ‖p - q‖ := habs
    _ = ((Lst * ‖ν‖₊ : NNReal) : ℝ) * ‖p - q‖ := by rw [hcoef]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_mem_iff_forall_normalDirections
    (g : SmoothRiemannianMetric I M)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) g x (basisAt x))
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) (x : M)
    (p : Tensor04At (I := I) (M := M) x) :
    p ∈ fiberHamiltonIveyRegion basisAt K τ x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) g basisAt x →
          inner0S (I := I) g x 4 ν p ≤ regionSupport (I := I) g basisAt K τ x ν := by
  constructor
  · intro hpC ν hν
    exact (fiberRegion_mem_iff_forall_normalDirections_of_mem_algebraicCurvatureTensorSubmodule (I := I) g basisAt horth0 hK hτ x p hpC.1).mp hpC ν hν
  · intro hle
    let pν : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := algebraicCurvatureTensorProjection (I := I) g x p
    let q : Tensor04At (I := I) (M := M) x := p - (pν : Tensor04At (I := I) (M := M) x)
    have hqW : ∀ r : Tensor04At (I := I) (M := M) x,
        r ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x →
          inner0S (I := I) g x 4 q r = 0 := by
      intro r hr
      have h1 := algebraicCurvatureTensorProjection_inner (I := I) g x p ⟨r, hr⟩
      have hsub : inner0S (I := I) g x 4 q r =
          inner0S (I := I) g x 4 p r - inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) r := by
        dsimp [q]
        rw [inner0S_sub_left]
      rw [hsub]
      have h1' : inner0S (I := I) g x 4 (pν : Tensor04At (I := I) (M := M) x) r =
          inner0S (I := I) g x 4 p r := by
        simpa using h1
      rw [h1']
      ring
    have hqproj : (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x) = 0 := by
      have hself : inner0S (I := I) g x 4
          (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x)
          (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x) = 0 := by
        have h := algebraicCurvatureTensorProjection_inner (I := I) g x q (algebraicCurvatureTensorProjection (I := I) g x q)
        have h' : inner0S (I := I) g x 4
            (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x)
            (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x) =
            inner0S (I := I) g x 4 q
              (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x) := by
          simpa using h
        rw [h']
        exact hqW (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x) (algebraicCurvatureTensorProjection (I := I) g x q).2
      change (tensor0SMetricData (I := I) g x 4).inner
          (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x)
          (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x) = 0 at hself
      exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff
        (algebraicCurvatureTensorProjection (I := I) g x q : Tensor04At (I := I) (M := M) x)).mp hself
    have hqproj0 : algebraicCurvatureTensorProjection (I := I) g x q = 0 := by
      apply Subtype.ext
      simpa using hqproj
    have hregq : regionProjMatrix (I := I) g (basisAt x) q = 0 := by
      unfold regionProjMatrix
      rw [hqproj0]
      ext i j
      change tensor04StandardAt (I := I) (M := M)
        ((0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x)
        (basisAt x (bivectorIndex3 i).1) (basisAt x (bivectorIndex3 i).2)
        (basisAt x (bivectorIndex3 j).2) (basisAt x (bivectorIndex3 j).1) = 0
      have hz : ((0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Tensor04At (I := I) (M := M) x) = 0 := by
        rfl
      rw [hz]
      simp
    have hqN : q ∈ regionNormalDirections (I := I) g basisAt x := by
      rw [regionNormalDirections]
      right
      rw [hregq]
      unfold euclideanMatrixSymmetrization
      ext i j
      simp [euclideanToMatrix, matrixToEuclidean, smul_eq_mul]
    have hsupp : regionSupport (I := I) g basisAt K τ x q = 0 := by
      have hz : hamiltonIveyConvexMatrixRegionSupportEuclidean K τ
          (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) = 0 :=
        hamiltonIveyConvexMatrixRegionSupportEuclidean_eq_zero_of_symm_zero (K := K) (τ := τ)
          (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) (by
            unfold euclideanMatrixSymmetrization
            ext i j
            simp [euclideanToMatrix, smul_eq_mul])
      unfold regionSupport
      rw [hregq]
      have hme : matrixToEuclidean (0 : Matrix (Fin 3) (Fin 3) ℝ) =
          (0 : EuclideanSpace ℝ (Fin 3 × Fin 3)) := by
        ext ij
        simp [matrixToEuclidean]
      rw [hme]
      simp [hz]
    have hle' := hle q hqN
    have hqp : inner0S (I := I) g x 4 q p = inner0S (I := I) g x 4 q q := by
      have h1 : inner0S (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) = 0 :=
        hqW (pν : Tensor04At (I := I) (M := M) x) pν.2
      calc
        inner0S (I := I) g x 4 q p
            = inner0S (I := I) g x 4 q ((pν : Tensor04At (I := I) (M := M) x) + q) := by
              congr 2
              dsimp [q]
              abel
        _ = inner0S (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) + inner0S (I := I) g x 4 q q := by
              exact inner0S_add_right (I := I) g x 4 q (pν : Tensor04At (I := I) (M := M) x) q
        _ = inner0S (I := I) g x 4 q q := by
              rw [h1]
              simp
    have hqq : inner0S (I := I) g x 4 q q ≤ 0 := by
      rw [hsupp] at hle'
      rwa [hqp] at hle'
    have hqzero : q = 0 := by
      have hnonneg : 0 ≤ inner0S (I := I) g x 4 q q :=
        MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x 4) q
      have hz : inner0S (I := I) g x 4 q q = 0 := le_antisymm hqq hnonneg
      exact ((tensor0SMetricData (I := I) g x 4).inner_self_eq_zero_iff q).mp hz
    have hpW : p ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
      have hpeq : p = (pν : Tensor04At (I := I) (M := M) x) := by
        have hz : p - (pν : Tensor04At (I := I) (M := M) x) = 0 := by
          simpa [q] using hqzero
        exact sub_eq_zero.mp hz
      rw [hpeq]
      exact pν.2
    exact (fiberRegion_mem_iff_forall_normalDirections_of_mem_algebraicCurvatureTensorSubmodule (I := I) g basisAt horth0 hK hτ x p hpW).mpr hle

end PulledScalarization

section FiberRegionFlatPredicate

private noncomputable def fiberRegionFlat
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (t : ℝ) (x₀ : M) (ν : (x : M) → Tensor04At (I := I) (M := M) x) : Prop :=
  ∃ (η : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (nablaη : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (nabla2η : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x₀)),
    OrthonormalBasisAt (I := I) (S.base.metric t) x₀ basis ∧
    (∀ᶠ y in 𝓝 x₀, ν y = uhlenbeckPullbackTensorAt (I := I) basisAt iota t y (η y)) ∧
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
      (S.base.connection t) η nablaη ∧
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
      (S.base.connection t) nablaη nabla2η ∧
    nablaη x₀ = 0 ∧
    metricTrace0S2TensorInBasis (I := I) (basis := basis)
      (identityInvMetric (Idx := Fin 3)) (nabla2η x₀) = 0

end FiberRegionFlatPredicate

section FiberMaximumPrinciple

open DifferentialGeometry.Analysis.Parabolic

variable {T : ℝ} (hT : 0 < T) [I.Boundaryless]
variable (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
variable (hS : IsSolutionOn (I := I) S)
variable (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
variable (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
variable (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
variable (iota : MatrixComp M (Fin 3))
variable (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
variable (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)

private noncomputable def intrinsicUhlenbeckIota
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x)) :
    MatrixComp M (Fin 3) :=
  Classical.choose (uhlenbeckIotaOfSolution (I := I) (M := M) hT S
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_time (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun a k : Fin 3 => if a = k then 1 else 0))

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem intrinsicUhlenbeckIota_spec :
    (∀ x : M, ∀ a k : Fin 3,
      intrinsicUhlenbeckIota hT S hS basisAt 0 x a k = if a = k then 1 else 0) ∧
    (∀ x : M, ContinuousOn (fun t : ℝ => intrinsicUhlenbeckIota hT S hS basisAt t x)
      (Set.Icc 0 T)) ∧
    FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (intrinsicUhlenbeckIota hT S hS basisAt)
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) ∧
    (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (intrinsicUhlenbeckIota hT S hS basisAt) t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (intrinsicUhlenbeckIota hT S hS basisAt) 0 x a b) := by
  classical
  let iota : MatrixComp M (Fin 3) := intrinsicUhlenbeckIota hT S hS basisAt
  have hraw := Classical.choose_spec (uhlenbeckIotaOfSolution (I := I) (M := M) hT S
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_time (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun a k : Fin 3 => if a = k then 1 else 0))
  have hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0 := hraw.1
  have hiota_cont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T) := hraw.2.1
  have hiota_deriv : ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ x : M, ∀ a k : Fin 3,
      HasDerivWithinAt (fun s : ℝ => iota s x a k)
        (∑ l : Fin 3, uhlenbeckRupOfSolution (I := I) S
          (solutionInverseMetricComponents S basisAt) (fun a x => basisAt x a) t x l k *
            iota t x a l)
        (Set.Ici 0) t := hraw.2.2
  have hframeODE : FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) := by
    intro t x a k
    have hderiv := hiota_deriv (t : ℝ) ⟨le_of_lt t.2.1, t.2.2⟩ x a k
    have hnhds : Set.Ici 0 ∈ 𝓝 (t : ℝ) := by
      have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 (t : ℝ) := Ioi_mem_nhds t.2.1
      exact Filter.mem_of_superset hpos (by intro s hs; exact le_of_lt (show (0 : ℝ) < s from hs))
    exact (hderiv.hasDerivAt hnhds).hasDerivWithinAt
  have hgram' : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b := by
    let gInv : Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3) :=
      solutionInverseMetricComponents (I := I) (M := M) S basisAt
    have hcompat : RicciEndomorphismCompatibleInFrame
        (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (ricciCompInFrame (I := I) S (fun a x => basisAt x a))
        (uhlenbeckRupOfSolution (I := I) S gInv (fun a x => basisAt x a)) := by
      exact ricciOneUpCompatible_of_inverseMetric (I := I) (M := M) S gInv (fun a x => basisAt x a)
        (by intro t x i j; exact solutionInverseMetricComponents_mul_metric (I := I) (M := M) S basisAt t x i j)
        (by intro t x i j; exact solutionInverseMetricComponents_symm (I := I) (M := M) S basisAt t x i j)
    have hmetric : MetricCompRicciFlowInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
        (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (ricciCompInFrame (I := I) S (fun a x => basisAt x a)) := by
      intro τ x i j
      exact metricCompInFrame_timeDeriv (I := I) S hS (fun a x => basisAt x a) τ x i j
    have hgram_cont : ∀ x : M, ∀ a b : Fin 3,
        ContinuousOn (fun s : ℝ =>
          movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota s x a b)
          (Set.Icc 0 T) := by
      intro x a b
      exact movingFrameGram_continuousOn_of_metricFamily (I := I) (M := M) hT S hS
        iota hiota_cont (fun a x => basisAt x a) a b
    intro t ht x a b
    exact movingFrameGramInFrame_eq_initial_of_ricci_flow
      (D := RealTimeInterval.closed 0 T hT.le) (T := T)
      (metricCompInFrame (I := I) S (fun a x => basisAt x a))
      (ricciCompInFrame (I := I) S (fun a x => basisAt x a))
      iota (uhlenbeckRupOfSolution (I := I) S gInv (fun a x => basisAt x a))
      hmetric hframeODE hcompat (by
        intro s hs
        change s ∈ Set.Ioo 0 T
        exact hs)
      hgram_cont ht x a b
  constructor
  · intro x a k
    simpa [iota] using hiota0 x a k
  · constructor
    · simpa [iota] using hiota_cont
    · constructor
      · simpa [iota] using hframeODE
      · intro t ht x a b
        simpa [iota] using hgram' t ht x a b

private def fiberRegionSet
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K t : ℝ) (x : M) : Set (Tensor04At (I := I) (M := M) x) :=
  fiberHamiltonIveyRegion basisAt K (max t 0) x

private def fiberRegionSupport
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (K t : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  regionSupport (I := I) (S.base.metric 0) basisAt K (max t 0) x ν

private def fiberRegionSupportDeriv
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {K : ℝ} (hK : 0 < K) (t : ℝ) (x : M)
    (ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  regionSupportDeriv (I := I) (S.base.metric 0) basisAt hK t x ν

private def fiberRegionSource
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (x : M) (p ν : Tensor04At (I := I) (M := M) x) : ℝ :=
  regionSource (I := I) (S.base.metric 0) basisAt x p ν

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem fiberRegionPropagationOn_of_flatSupport
    {T : ℝ} (hT : 0 < T) [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank ℝ E)]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {K : ℝ} (hK : 0 < K)
    (hinit : ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota 0 x ∈ fiberHamiltonIveyRegion basisAt K 0 x)
    (hsol : by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun x => inferInstance
      exact IsBundleHeatReactionOn
        (V := fun x : M => Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (RealTimeInterval.closed 0 T hT.le) (flowG (I := I) S)
        (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
        (uhlenbeckPulledRm04At S basisAt iota))
    (hflat : by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun x => inferInstance
      exact HasFlatSupportSectionsOn (I := I) (Set.Icc 0 T)
        (V := fun x : M => Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (regionNormalDirections (I := I) (S.base.metric 0) basisAt)
        (fiberRegionSupport hT (I := I) (M := M) S basisAt K)) :
    ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈ fiberHamiltonIveyRegion basisAt K t x := by
  classical
  let : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  let : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  let : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
    fun x => inferInstance
  rcases exists_pulledRm_norm_bound (I := I) (M := M) hT S hS hdim basisAt iota hiota0 hgram horth0 with
    ⟨R, hRge, hbound⟩
  rcases regionSource_lipschitzOn_closedBall_uniform (I := I) (S.base.metric 0) basisAt horth0 hRge with
    ⟨L, hL⟩
  let hCclosed : ∀ t x, @IsClosed (Tensor04At (I := I) (M := M) x)
      (@InnerProductSpace.Core.toNormedAddCommGroup ℝ
        (Tensor04At (I := I) (M := M) x) _ _ _
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fiberRegionSet (I := I) (M := M) basisAt K t x) := by
    intro t x
    exact isClosed_fiberHamiltonIveyRegion (I := I) (S.base.metric 0)
      basisAt (τ := max t 0) hK x
  let hCconvex : ∀ t x, Convex ℝ (fiberRegionSet (I := I) (M := M) basisAt K t x) := by
    intro t x
    exact convex_fiberHamiltonIveyRegion (I := I) basisAt hK (le_max_right t 0) x
  let hCne : ∀ t x, (fiberRegionSet (I := I) (M := M) basisAt K t x).Nonempty := by
    intro t x
    exact nonempty_fiberHamiltonIveyRegion (I := I) basisAt hK (le_max_right t 0) x
  let hCzero : ∀ t x, (0 : Tensor04At (I := I) (M := M) x) ∈ fiberRegionSet (I := I) (M := M) basisAt K t x := by
    intro t x
    exact zero_mem_fiberHamiltonIveyRegion (I := I) basisAt hK (le_max_right t 0) x
  let hsupp : ∀ t x p, p ∈ fiberRegionSet (I := I) (M := M) basisAt K t x ↔
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x →
          inner ℝ ν p ≤ fiberRegionSupport hT (I := I) (M := M) S basisAt K t x ν := by
    intro t x p
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hmain := fiberRegion_mem_iff_forall_normalDirections (I := I) (S.base.metric 0)
      basisAt horth0 hK hτ x p
    constructor
    · intro hp ν hν
      have hle := (hmain.mp hp) ν hν
      have hin : inner ℝ ν p = inner0S (I := I) (S.base.metric 0) x 4 ν p :=
        tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x ν p
      rw [fiberRegionSupport, hin]
      exact hle
    · intro hle
      apply hmain.mpr
      intro ν hν
      have hle' := hle ν hν
      have hin : inner0S (I := I) (S.base.metric 0) x 4 ν p = inner ℝ ν p :=
        (tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x ν p).symm
      dsimp [fiberRegionSupport] at hle'
      rwa [← hin] at hle'
  let hsupport_sup : ∀ t x ν,
      ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x →
      fiberRegionSupport hT (I := I) (M := M) S basisAt K t x ν =
        sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
          q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x ∧ r = inner ℝ q ν} := by
    intro t x ν hν
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hmain := regionSupport_eq_sSup (I := I) (S.base.metric 0) basisAt horth0 hK hτ x hν
    rw [fiberRegionSupport]
    calc
      regionSupport (I := I) (S.base.metric 0) basisAt K (max t 0) x ν
          = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
              q ∈ fiberHamiltonIveyRegion basisAt K (max t 0) x ∧
                r = inner0S (I := I) (S.base.metric 0) x 4 q ν} := hmain
      _ = sSup {r : ℝ | ∃ q : Tensor04At (I := I) (M := M) x,
              q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x ∧ r = inner ℝ q ν} := by
            apply congrArg sSup
            ext r
            constructor
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q, by simpa [fiberRegionSet] using hq, ?_⟩
              exact tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x q ν
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q, by simpa [fiberRegionSet] using hq, ?_⟩
              exact (tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x q ν).symm
  let hNnormal : ∀ t x, ∀ p : Tensor04At (I := I) (M := M) x,
      p ∈ fiberRegionSet (I := I) (M := M) basisAt K t x → ∀ ν : Tensor04At (I := I) (M := M) x,
      (∀ q : Tensor04At (I := I) (M := M) x, q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x →
        inner ℝ ν (q - p) ≤ 0) → ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x := by
    intro t x p hp ν hnormal
    have hτ : 0 ≤ max t 0 := le_max_right t 0
    have hp' : p ∈ fiberHamiltonIveyRegion basisAt K (max t 0) x := by
      simpa [fiberRegionSet] using hp
    have hnormal' : ∀ q : Tensor04At (I := I) (M := M) x,
        q ∈ fiberHamiltonIveyRegion basisAt K (max t 0) x →
          inner0S (I := I) (S.base.metric 0) x 4 ν (q - p) ≤ 0 := by
      intro q hq
      have hq' : q ∈ fiberRegionSet (I := I) (M := M) basisAt K t x := by
        simpa [fiberRegionSet] using hq
      have hle := hnormal q hq'
      have hin : inner0S (I := I) (S.base.metric 0) x 4 ν (q - p) = inner ℝ ν (q - p) :=
        (tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x ν (q - p)).symm
      rwa [← hin] at hle
    exact regionNormalDirections_of_normal (I := I) (S.base.metric 0) basisAt horth0 hK hτ x hp' hnormal'
  let hCdist_cont : ContinuousOn
      (fun q : ℝ × M => Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)
        (fiberRegionSet (I := I) (M := M) basisAt K q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    have h := continuousOn_infDist_uhlenbeckPulledRm04At_fiberHamiltonIveyRegion
      (I := I) (M := M) hT S hS hdim basisAt horth0 iota
      hiota0 hgram hK
    refine h.congr ?_
    intro q hq
    exact congrArg (Metric.infDist (uhlenbeckPulledRm04At S basisAt iota q.1 q.2)) (by
      dsimp [fiberRegionSet]
      rw [max_eq_left (show (0 : ℝ) ≤ q.1 from hq.1.1)])
  let hsupport_cont : ∀ ν : (x : M) → Tensor04At (I := I) (M := M) x, ∀ x : M,
      ContinuousOn (fun t : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K t x (ν x))
        (Set.Icc 0 T) := by
    intro ν x
    have h := regionSupport_continuousOn_time (I := I) (S.base.metric 0) basisAt (T := T) hK x (ν x)
    refine h.congr ?_
    intro t ht
    dsimp [fiberRegionSupport]
    rw [max_eq_left ht.1]
  let hsupport_time : ∀ ν : (x : M) → Tensor04At (I := I) (M := M) x,
      ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      HasDerivAt (fun s : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K s x (ν x))
        (fiberRegionSupportDeriv hT (I := I) (M := M) S basisAt hK t x (ν x)) t := by
    intro ν t ht htpos x
    have hmain := regionSupport_hasDerivAt_time (I := I) (S.base.metric 0) basisAt hK htpos x (ν x)
    have heq : (fun s : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K s x (ν x)) =ᶠ[𝓝 t]
        fun τ : ℝ => regionSupport (I := I) (S.base.metric 0) basisAt K τ x (ν x) := by
      have hpos : Set.Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (half_lt_self htpos)
      filter_upwards [hpos] with s hs
      dsimp [fiberRegionSupport]
      have hmax : max s 0 = s := max_eq_left (le_of_lt (lt_trans (by positivity : (0 : ℝ) < t / 2) hs))
      rw [hmax]
    have hmain' : HasDerivAt (fun s : ℝ => fiberRegionSupport hT (I := I) (M := M) S basisAt K s x (ν x))
        (regionSupportDeriv (I := I) (S.base.metric 0) basisAt hK t x (ν x)) t :=
      hmain.congr_of_eventuallyEq heq
    simpa [fiberRegionSupportDeriv] using hmain'
  let htangent : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M, ∀ p : Tensor04At (I := I) (M := M) x,
      p ∈ fiberRegionSet (I := I) (M := M) basisAt K t x →
      ∀ ν : Tensor04At (I := I) (M := M) x,
        ν ∈ regionNormalDirections (I := I) (S.base.metric 0) basisAt x →
        fiberRegionSupport hT (I := I) (M := M) S basisAt K t x ν = inner ℝ ν p →
        fiberRegionSource hT (I := I) (M := M) S basisAt x p ν ≤
          fiberRegionSupportDeriv hT (I := I) (M := M) S basisAt hK t x ν := by
    intro t ht htpos x p hp ν hν htangent
    have hmax : max t 0 = t := max_eq_left ht.1
    have hp' : p ∈ fiberHamiltonIveyRegion basisAt K t x := by
      dsimp [fiberRegionSet] at hp
      rwa [hmax] at hp
    have hin : inner ℝ ν p = inner0S (I := I) (S.base.metric 0) x 4 ν p :=
      tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x ν p
    have hsup' : regionSupport (I := I) (S.base.metric 0) basisAt K t x ν =
        inner0S (I := I) (S.base.metric 0) x 4 ν p := by
      dsimp [fiberRegionSupport] at htangent
      rw [hmax] at htangent
      rw [hin] at htangent
      exact htangent
    exact regionSource_le_regionSupportDeriv_of_tangent (I := I) (S.base.metric 0) basisAt horth0 hK
      htpos x hp' hν hsup'
  have hres : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈ fiberRegionSet (I := I) (M := M) basisAt K t x :=
    bundle_closed_convex_time_dependent_heat_reaction_mem_of_support_tangent
      (V := fun x : M => Tensor04At (I := I) (M := M) x)
      (flowG (I := I) S) hT
      (fiberRegionFlat (I := I) (M := M) S basisAt iota)
      (fun t x => fiberRegionSet (I := I) (M := M) basisAt K t x)
      (regionNormalDirections (I := I) (S.base.metric 0) basisAt)
      (fiberRegionSupport hT (I := I) (M := M) S basisAt K)
      (fiberRegionSupportDeriv hT (I := I) (M := M) S basisAt hK)
      hCclosed hCconvex hCne hsupp hsupport_sup hNnormal
      (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
      (uhlenbeckPulledRm04At S basisAt iota)
      hsol R hbound hCzero L (fun t ht x ν => by simpa [fiberRegionSource] using hL x ν)
      hCdist_cont hflat hsupport_cont hsupport_time htangent (fun x => by simpa [fiberRegionSet] using hinit x)
  intro t ht x
  have hmem := hres t ht x
  have hmax : max t 0 = t := max_eq_left ht.1
  rwa [fiberRegionSet, hmax] at hmem

end FiberMaximumPrinciple

section FiberHeatReactionSolution

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Dim3Reaction

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem basis_repr_uhlenbeckEndomorphism_apply_basis
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (a j : Fin 3) :
    basis.repr (uhlenbeckEndomorphismAt basis iota t (basis a)) j =
      iota t x a j := by
  rw [uhlenbeckEndomorphism_apply_basis]
  rw [Module.Basis.repr_sum_self basis (fun k : Fin 3 => iota t x a k)]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem sum_fin4_eq_sum_i_j_k_l (F : (Fin 4 → Fin 3) → ℝ) :
    (∑ J : Fin 4 → Fin 3, F J) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  let e : (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) :=
    { toFun := fun f => (((f 0, f 1), f 2), f 3)
      invFun := fun p => slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
      left_inv := by
        intro f
        funext a
        fin_cases a <;> simp [slots4]
      right_inv := by
        intro p
        rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
        simp [slots4] }
  rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
    (fun x => congrArg F (e.left_inv x).symm)]
  · repeat rw [Fintype.sum_prod_type]
    rfl

variable {T : ℝ} (hT : 0 < T) [I.Boundaryless]
variable (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
variable (hS : IsSolutionOn (I := I) S)
variable (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
variable (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
variable (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [I.Boundaryless] in
private theorem compUhlenbeck_mem_algebraicCurvatureTensorSubmodule
    {x : M}
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : Real)
    (X : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  have hform : IsAlgCurvForm (tensor04StandardAt (I := I) (M := M) (X : Tensor04At (I := I) (M := M) x)) :=
    (mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)).mp X.2
  rw [show (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      IsAlgCurvForm (tensor04StandardAt (I := I) (M := M)
        ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))) from
    mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)]
  change IsAlgCurvForm (fun v y z w =>
    tensor04StandardAt (I := I) (M := M)
      ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) v y z w)
  simp_rw [tensor04StandardAt_compContinuousLinearMap]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [map_add (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [map_smul (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    exact hform.anti_first _ _ _ _
  · intro u v y z
    exact hform.anti_last _ _ _ _
  · intro u v y z
    exact hform.bianchi _ _ _ _

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] in
private theorem curvatureOperatorMatrixAt_compU_eq_moving
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨(A : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t),
          compUhlenbeck_mem_algebraicCurvatureTensorSubmodule basisAt iota t A⟩ =
      curvatureOperatorMatrixAt (I := I) x
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x) A := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  ext p q
  unfold curvatureOperatorMatrixAt
  rw [tensor04StandardAt_compContinuousLinearMap (A : Tensor04At (I := I) (M := M) x)
    (uhlenbeckEndomorphismAt (basisAt x) iota t)]
  simp [uhlenbeckMovingBasis_apply]

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem tangentSection_cont_constBase_of_fiber_cont
    {x : M} {P : Type*} [TopologicalSpace P] {w : P → TangentSpace I x}
    (hw : Continuous w) :
    Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (w p)) := by
  classical
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hlin : Continuous (fun p : P => e.linearMapAt ℝ x (w p)) := by
    have h1 : e.linearMapAt ℝ x = e.linearEquivAt ℝ x hx := e.linearMapAt_def_of_mem hx
    rw [h1]
    exact (e.linearEquivAt ℝ x hx).toLinearMap.continuous_of_finiteDimensional.comp hw
  have hpair : ContinuousOn (fun p : P => (x, e.linearMapAt ℝ x (w p))) univ := by
    exact ContinuousOn.prodMk continuousOn_const hlin.continuousOn
  have hsec : ContinuousOn (fun p : P =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (e.symm x (e.linearMapAt ℝ x (w p)))) univ := by
    have hc := e.continuousOn_symm.comp hpair (by intro p _; exact ⟨hx, trivial⟩)
    exact hc
  have hcont : Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (e.symm x (e.linearMapAt ℝ x (w p)))) :=
    continuousOn_univ.mp hsec
  refine hcont.congr ?_
  intro p
  congr 1
  rw [e.linearMapAt_apply, if_pos hx]
  rw [e.symm_apply_apply_mk hx (w p)]

end FiberHeatReactionSolution

section FiberHeatReactionSolutionProof

open DifferentialGeometry.Tensor.Coordinates

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private def succPerm {s : ℕ} (e : Equiv.Perm (Fin s)) : Equiv.Perm (Fin (s + 1)) where
  toFun := fun i => Fin.cases (0 : Fin (s + 1)) (fun i' : Fin s => Fin.succ (e i')) i
  invFun := fun i => Fin.cases (0 : Fin (s + 1)) (fun i' : Fin s => Fin.succ (e.symm i')) i
  left_inv := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i' => simp
  right_inv := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i' => simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fin_cons_comp_succPerm {s : ℕ} {V : Type*} (u : V) (f : Fin s → V)
    (e : Equiv.Perm (Fin s)) :
    (Fin.cons u f) ∘ succPerm e = Fin.cons u (f ∘ e) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [succPerm]
  | succ i' => simp [succPerm, Function.comp_def]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fin_cons_tail {s : ℕ} {V : Type*} (f : Fin (s + 1) → V) :
    Fin.cons (f 0) (fun i : Fin s => f (i.succ)) = f := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i' => simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem update_comp_perm {s : ℕ} {V : Type*} (e : Equiv.Perm (Fin s))
    (slots : Fin s → V) (a : Fin s) (w : V) :
    Function.update (fun b : Fin s => slots (e b)) a w =
      (Function.update slots (e a) w) ∘ e := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp [Function.update]
  · have hne : e b ≠ e a := fun h => hb (e.injective h)
    simp [Function.update, hb, hne]

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private def finCycle012 : Equiv.Perm (Fin 4) where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else 3
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else 3
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_swap01 {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots (Equiv.swap (0 : Fin 4) (1 : Fin 4) a)) =
      vec4 (slots 1) (slots 0) (slots 2) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4, Equiv.swap_apply_def]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4, Equiv.swap_apply_def]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_swap23 {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots (Equiv.swap (2 : Fin 4) (3 : Fin 4) a)) =
      vec4 (slots 0) (slots 1) (slots 3) (slots 2) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4, Equiv.swap_apply_def]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4, Equiv.swap_apply_def]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_cycle012 {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots (finCycle012 a)) =
      vec4 (slots 1) (slots 2) (slots 0) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4, finCycle012]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4, finCycle012]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4, finCycle012]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4, finCycle012]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_comp_cycle012_sq {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots ((finCycle012.trans finCycle012) a)) =
      vec4 (slots 2) (slots 0) (slots 1) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4, finCycle012]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4, finCycle012]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4, finCycle012]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4, finCycle012]
              | succ a3 => exact Fin.elim0 a3

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem metricTraceInput_eq_cons_cons {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    metricTraceInput (I := I) X Y tail = Fin.cons X (Fin.cons Y tail) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem mvfderiv_zero_at {x : M} (v : TangentSpace I x) :
    mvfderiv (I := I) (fun _ : M => (0 : Real)) x v = 0 := by
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv (I := I) (fun _ : M => (0 : Real)) x v]
  simp

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem mdiffAt_const_mul {f : M → ℝ} {x : M} (c : ℝ)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    MDifferentiableAt I 𝓘(Real, Real) (fun p : M => c * f p) x := by
  have hfun : (fun p : M => c * f p) = f * (fun _ : M => c) := by
    funext p
    simp [Pi.mul_apply, mul_comm]
  rw [hfun]
  exact hf.mul (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := c) (x := x))

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem TotalNabla0SRealizes.deriv_linear_combination {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov α nablaAlpha)
    {ι : Type*} [Fintype ι]
    (perms : ι → Equiv.Perm (Fin s)) (c : ι → ℝ)
    (hid : ∀ p : M, ∀ slots : Fin s → TangentSpace I p,
      (∑ k : ι, c k * α p (fun a : Fin s => slots (perms k a))) = 0)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    (∑ k : ι, c k * nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V (perms k a) x))) = 0 := by
  classical
  have hEV : ∀ k : ι,
      nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V (perms k a) x)) =
        mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x) -
          ∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x))) := by
    intro k
    exact TotalNabla0SRealizes.eval_smooth_slots (I := I) h X (fun a : Fin s => V (perms k a)) x
  have hgdiff : ∀ k : ι, MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x := by
    intro k
    exact (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α
      (fun a : Fin s => V (perms k a)) x).mdifferentiableAt (by simp)
  have hgzero : (fun p : M => ∑ k : ι, c k * α p (fun a : Fin s => V (perms k a) p)) =ᶠ[𝓝 x]
      fun _ : M => (0 : Real) := by
    filter_upwards with p
    exact hid p (fun a : Fin s => V a p)
  have hExt : (∑ k : ι, c k * mvfderiv (I := I)
      (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x)) = 0 := by
    calc
      (∑ k : ι, c k * mvfderiv (I := I)
          (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x))
          = ∑ k : ι, mvfderiv (I := I)
              (fun p : M => c k * α p (fun a : Fin s => V (perms k a) p)) x (X x) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mvfderiv_const_mul_apply (I := I) (c k) (X x) (hgdiff k)]
      _ = mvfderiv (I := I)
            (fun p : M => ∑ k : ι, c k * α p (fun a : Fin s => V (perms k a) p)) x (X x) := by
          have hfun : (fun p : M => ∑ k : ι, c k * α p (fun a : Fin s => V (perms k a) p)) =
              Finset.univ.sum (fun k : ι => fun p : M => c k * α p (fun a : Fin s => V (perms k a) p)) := by
            funext p
            simp [Finset.sum_apply]
          rw [hfun]
          rw [mvfderiv_finset_sum (I := I) (t := Finset.univ)
            (f := fun k : ι => fun p : M => c k * α p (fun a : Fin s => V (perms k a) p))
            (x := x) (v := X x) (by
              intro k _
              exact mdiffAt_const_mul (c k) (hgdiff k))]
      _ = 0 := by
          rw [mvfderiv_congr_eventually (I := I) (v := X x) hgzero]
          exact mvfderiv_zero_at (I := I) (X x)
  have hreindex : ∀ k : ι,
      (∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
          ((cov (fun p : M => V (perms k a) p) x) (X x)))) =
        ∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
    intro k
    calc
      (∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
          ((cov (fun p : M => V (perms k a) p) x) (X x))))
          = ∑ a' : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) ((perms k).symm a')
              ((cov (fun p : M => V a' p) x (X x)))) := by
            rw [← Equiv.sum_comp (perms k).symm (fun a : Fin s =>
              α x (Function.update (fun b : Fin s => V (perms k b) x) a
                ((cov (fun p : M => V (perms k a) p) x (X x)))))]
            refine Finset.sum_congr rfl ?_
            intro a' _
            congr 1
            simp [Equiv.apply_symm_apply]
      _ = ∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
              ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
            refine Finset.sum_congr rfl ?_
            intro a' _
            rw [update_comp_perm (perms k) (fun b : Fin s => V b x) ((perms k).symm a')
              (cov (fun p : M => V a' p) x (X x))]
            simp [Equiv.apply_symm_apply, Function.comp_def]
  have hCorrection : (∑ k : ι, c k * (∑ a : Fin s, α x
      (Function.update (fun b : Fin s => V (perms k b) x) a
        ((cov (fun p : M => V (perms k a) p) x) (X x))))) = 0 := by
    calc
      (∑ k : ι, c k * (∑ a : Fin s, α x
          (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x)))))
          = ∑ k : ι, c k * (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
              ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k))) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [hreindex k]
      _ = ∑ a' : Fin s, ∑ k : ι, c k * α x ((Function.update (fun b : Fin s => V b x) a'
              ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
            have hmul : (∑ k : ι, c k * (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
                  ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)))) =
                ∑ k : ι, ∑ a' : Fin s, c k * α x ((Function.update (fun b : Fin s => V b x) a'
                  ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              calc
                c k * (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
                      ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)))
                    = (∑ a' : Fin s, α x ((Function.update (fun b : Fin s => V b x) a'
                          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k))) * c k := by
                        rw [mul_comm]
                _ = ∑ a' : Fin s, (α x ((Function.update (fun b : Fin s => V b x) a'
                          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k))) * c k := by
                        rw [Finset.sum_mul]
                _ = ∑ a' : Fin s, c k * α x ((Function.update (fun b : Fin s => V b x) a'
                          ((cov (fun p : M => V a' p) x) (X x))) ∘ (perms k)) := by
                        refine Finset.sum_congr rfl ?_
                        intro a' _
                        rw [mul_comm]
            rw [hmul]
            rw [Finset.sum_comm]
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro a' _
            simpa [Function.comp_def] using
              (hid x (Function.update (fun b : Fin s => V b x) a'
                ((cov (fun p : M => V a' p) x) (X x))))
  calc
    (∑ k : ι, c k * nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V (perms k a) x)))
        = ∑ k : ι, c k * (mvfderiv (I := I)
            (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x) -
          ∑ a : Fin s, α x (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x)))) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hEV k]
    _ = (∑ k : ι, c k * mvfderiv (I := I)
          (fun p : M => α p (fun a : Fin s => V (perms k a) p)) x (X x)) -
        (∑ k : ι, c k * (∑ a : Fin s, α x
          (Function.update (fun b : Fin s => V (perms k b) x) a
            ((cov (fun p : M => V (perms k a) p) x) (X x))))) := by
          simp [Finset.sum_sub_distrib, mul_sub]
    _ = 0 := by
          rw [hExt, hCorrection]
          ring

end FiberHeatReactionSolutionProof

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_self {x : M} (slots : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => slots a) = vec4 (slots 0) (slots 1) (slots 2) (slots 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4]
              | succ a3 => exact Fin.elim0 a3

section RoughLapAlgebraic

variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
private theorem nablaKRm04Field_one_anti12_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose
  have hV : ∀ a : Fin 4, V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose_spec
  let perms : Bool → Equiv.Perm (Fin 4) :=
    fun k => if k then Equiv.swap (0 : Fin 4) (1 : Fin 4) else 1
  let c : Bool → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s : Fin 4 → TangentSpace I p,
      (∑ k : Bool, c k * (S.base.rm04 t p) (fun a : Fin 4 => s (perms k a))) = 0 := by
    intro p s
    have hA : (S.base.rm04 t p) = metricRm04At (I := I) (M := M) (S.base.metric t) p := by
      rfl
    have hform := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)).1
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) p)
    have h1 := hform.1 (s 0) (s 1) (s 2) (s 3)
    rw [Fintype.sum_bool]
    change (1 : ℝ) * (S.base.rm04 t p)
          (fun a : Fin 4 => s (Equiv.swap (0 : Fin 4) (1 : Fin 4) a)) +
      (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s a) = 0
    simp only [one_mul]
    rw [vec4_comp_swap01 s, vec4_self s, hA]
    change tensor04StandardAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 1) (s 0) (s 2) (s 3) +
      tensor04StandardAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 0) (s 1) (s 2) (s 3) = 0
    rw [h1]
    ring
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 4) (cov := S.family.connection t)
    (α := S.base.rm04 t) (nablaAlpha := nablaKRm04Field (I := I) S t 1)
    (h := nablaKRm04Field_realizes (I := I) S t 0)
    (perms := perms) (c := c)
    (hid := hhid) X V x
  have hsum' : (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x)) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 := by
    rw [Fintype.sum_bool] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 at hmain
    simpa using hmain
  have hVat : (fun a : Fin 4 => V a x) = slots := by
    funext a
    exact hV a
  have hswapV : (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x) =
      slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4) := by
    funext a
    exact hV (Equiv.swap (0 : Fin 4) (1 : Fin 4) a)
  calc
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (0 : Fin 4) (1 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots)
        = (nablaKRm04Field (I := I) S t 1 x)
            (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (0 : Fin 4) (1 : Fin 4) a) x)) +
          (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) := by
          rw [← hswapV, ← hVat]
    _ = 0 := hsum'

omit [SigmaCompactSpace M] in
private theorem nablaKRm04Field_one_anti34_cond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (u : TangentSpace I x) (slots : Fin 4 → TangentSpace I x) :
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots) = 0 := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose
  have hX : X x = u :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose
  have hV : ∀ a : Fin 4, V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose_spec
  let perms : Bool → Equiv.Perm (Fin 4) :=
    fun k => if k then Equiv.swap (2 : Fin 4) (3 : Fin 4) else 1
  let c : Bool → ℝ := fun _ => 1
  have hhid : ∀ p : M, ∀ s : Fin 4 → TangentSpace I p,
      (∑ k : Bool, c k * (S.base.rm04 t p) (fun a : Fin 4 => s (perms k a))) = 0 := by
    intro p s
    have hA : (S.base.rm04 t p) = metricRm04At (I := I) (M := M) (S.base.metric t) p := by
      rfl
    have hform := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)).1
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) p)
    have h1 := hform.2.1 (s 0) (s 1) (s 2) (s 3)
    rw [Fintype.sum_bool]
    change (1 : ℝ) * (S.base.rm04 t p)
          (fun a : Fin 4 => s (Equiv.swap (2 : Fin 4) (3 : Fin 4) a)) +
      (1 : ℝ) * (S.base.rm04 t p) (fun a : Fin 4 => s a) = 0
    simp only [one_mul]
    rw [vec4_comp_swap23 s, vec4_self s, hA]
    change tensor04StandardAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 0) (s 1) (s 3) (s 2) +
      tensor04StandardAt (I := I) (M := M) (metricRm04At (I := I) (M := M) (S.base.metric t) p)
        (s 0) (s 1) (s 2) (s 3) = 0
    rw [h1]
    ring
  have hmain := TotalNabla0SRealizes.deriv_linear_combination
    (I := I) (s := 4) (cov := S.family.connection t)
    (α := S.base.rm04 t) (nablaAlpha := nablaKRm04Field (I := I) S t 1)
    (h := nablaKRm04Field_realizes (I := I) S t 0)
    (perms := perms) (c := c)
    (hid := hhid) X V x
  have hsum' : (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x)) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 := by
    rw [Fintype.sum_bool] at hmain
    rw [hX] at hmain
    change (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x)) +
      (1 : ℝ) * (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) = 0 at hmain
    simpa using hmain
  have hVat : (fun a : Fin 4 => V a x) = slots := by
    funext a
    exact hV a
  have hswapV : (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x) =
      slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4) := by
    funext a
    exact hV (Equiv.swap (2 : Fin 4) (3 : Fin 4) a)
  calc
    (nablaKRm04Field (I := I) S t 1 x)
        (Fin.cons u (slots ∘ Equiv.swap (2 : Fin 4) (3 : Fin 4))) +
      (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u slots)
        = (nablaKRm04Field (I := I) S t 1 x)
            (Fin.cons u (fun a : Fin 4 => V (Equiv.swap (2 : Fin 4) (3 : Fin 4) a) x)) +
          (nablaKRm04Field (I := I) S t 1 x) (Fin.cons u (fun a : Fin 4 => V a x)) := by
          rw [← hswapV, ← hVat]
    _ = 0 := hsum'

omit [CompleteSpace E] [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec4_self_refl {x : M} (s : Fin 4 → TangentSpace I x) :
    (fun a : Fin 4 => s ((Equiv.refl (Fin 4)) a)) = vec4 (s 0) (s 1) (s 2) (s 3) := by
  funext a
  cases a using Fin.cases with
  | zero => simp [vec4]
  | succ a0 =>
      cases a0 using Fin.cases with
      | zero => simp [vec4]
      | succ a1 =>
          cases a1 using Fin.cases with
          | zero => simp [vec4]
          | succ a2 =>
              cases a2 using Fin.cases with
              | zero => simp [vec4]
              | succ a3 => exact Fin.elim0 a3

omit [SigmaCompactSpace M] in
private theorem rm04BianchiCond'
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (p : M)
    (s : Fin 4 → TangentSpace I p) :
    tensor04StandardAt (I := I) (M := M) (S.base.rm04 t p) (s 0) (s 1) (s 2) (s 3) +
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 t p) (s 1) (s 2) (s 0) (s 3) +
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 t p) (s 2) (s 0) (s 1) (s 3) = 0 := by
  have hmem : (S.base.rm04 t p) ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) p :=
    metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) p
  have hform := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries (I := I) (M := M)).1 hmem
  exact hform.2.2 (s 0) (s 1) (s 2) (s 3)

omit [SigmaCompactSpace M] in
private theorem rm04BianchiCond
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (p : M)
    (s : Fin 4 → TangentSpace I p) :
    (S.base.rm04 t p) (fun a : Fin 4 => s ((Equiv.refl (Fin 4)) a)) +
      (S.base.rm04 t p) (fun a : Fin 4 => s (finCycle012 a)) +
        (S.base.rm04 t p) (fun a : Fin 4 => s ((finCycle012.trans finCycle012) a)) = 0 := by
  rw [vec4_self_refl s]
  rw [vec4_comp_cycle012 s, vec4_comp_cycle012_sq s]
  have h1 := rm04BianchiCond' S t p s
  rw [show tensor04StandardAt (I := I) (M := M) (S.base.rm04 t p) (s 0) (s 1) (s 2) (s 3) =
      (S.base.rm04 t p) (vec4 (I := I) (s 0) (s 1) (s 2) (s 3)) by rfl,
    show tensor04StandardAt (I := I) (M := M) (S.base.rm04 t p) (s 1) (s 2) (s 0) (s 3) =
      (S.base.rm04 t p) (vec4 (I := I) (s 1) (s 2) (s 0) (s 3)) by rfl,
    show tensor04StandardAt (I := I) (M := M) (S.base.rm04 t p) (s 2) (s 0) (s 1) (s 3) =
      (S.base.rm04 t p) (vec4 (I := I) (s 2) (s 0) (s 1) (s 3)) by rfl] at h1
  nlinarith

end RoughLapAlgebraic

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Dim3Reaction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]
variable {T : ℝ} (hT : 0 < T) [I.Boundaryless]
variable (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
variable (hS : IsSolutionOn (I := I) S)
variable (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
variable (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
variable (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
variable (iota : MatrixComp M (Fin 3))
variable (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
variable (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
  movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)


section Helpers

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem fiberInner_compUhlenbeck_isometry_tensor
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (X Y : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) (S.base.metric 0) x 4
        (X.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        (Y.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) =
      inner0S (I := I) (S.base.metric t) x 4 X Y := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have hmovingOrth : ∀ i j : Fin 3,
      (S.base.metric t).inner x (moving i) (moving j) = delta3 i j := by
    intro i j
    dsimp [moving]
    exact uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht i j
  have hinv0 : MetricInverseInBasis (I := I) (S.base.metric 0) x (basisAt x)
      (identityInvMetric (Idx := Fin 3)) := by
    have h := Tensor0SBundle.metricInverseInBasis_identity_of_orthonormal (I := I)
      (S.base.metric 0) (basisAt x) (by
        intro i j
        simpa [delta3] using horth0 x i j)
    exact h
  have hinvT : MetricInverseInBasis (I := I) (S.base.metric t) x moving
      (identityInvMetric (Idx := Fin 3)) := by
    have h := Tensor0SBundle.metricInverseInBasis_identity_of_orthonormal (I := I)
      (S.base.metric t) moving hmovingOrth
    exact h
  have hU : ∀ a : Fin 3,
      uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x a) = moving a := by
    intro a
    exact (uhlenbeckMovingBasis_apply (I := I) (M := M) hT S basisAt iota hiota0 hgram t ht x a).symm
  let Xc : Tensor04At (I := I) (M := M) x :=
    X.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)
  let Yc : Tensor04At (I := I) (M := M) x :=
    Y.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)
  have hleft : inner0S (I := I) (S.base.metric 0) x 4 Xc Yc =
      coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) Xc Yc (basisAt x) := by
    exact inner0S_eq_coord (I := I) (S.base.metric 0) x 4 (basisAt x)
      (identityInvMetric (Idx := Fin 3)) hinv0 Xc Yc
  have hright : inner0S (I := I) (S.base.metric t) x 4 X Y =
      coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) X Y moving := by
    exact inner0S_eq_coord (I := I) (S.base.metric t) x 4 moving
      (identityInvMetric (Idx := Fin 3)) hinvT X Y
  have hXcomp : ∀ I0 : Fin 4 → Fin 3,
      tensor0SComponent (I := I) Xc (fun i : Fin 3 => basisAt x i) I0 =
        tensor0SComponent (I := I) X (fun i : Fin 3 => moving i) I0 := by
    intro I0
    change (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (I0 a))) =
      (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => moving (I0 a))
    have harg : (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (I0 a))) =
        fun a : Fin 4 => moving (I0 a) := by
      funext a
      exact hU (I0 a)
    rw [harg]
  have hYcomp : ∀ J0 : Fin 4 → Fin 3,
      tensor0SComponent (I := I) Yc (fun i : Fin 3 => basisAt x i) J0 =
        tensor0SComponent (I := I) Y (fun i : Fin 3 => moving i) J0 := by
    intro J0
    change (Y : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (J0 a))) =
      (Y : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (fun a : Fin 4 => moving (J0 a))
    have harg : (fun a : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t (basisAt x (J0 a))) =
        fun a : Fin 4 => moving (J0 a) := by
      funext a
      exact hU (J0 a)
    rw [harg]
  calc
    inner0S (I := I) (S.base.metric 0) x 4 Xc Yc
        = coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) Xc Yc (basisAt x) := hleft
    _ = coordInner0S (I := I) (x := x) 4 (identityInvMetric (Idx := Fin 3)) X Y moving := by
          unfold coordInner0S
          apply Finset.sum_congr rfl
          intro I0 _
          apply Finset.sum_congr rfl
          intro J0 _
          rw [hXcomp I0, hYcomp J0]
    _ = inner0S (I := I) (S.base.metric t) x 4 X Y := hright.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma fiberRegion_tensor_sum_antiPair
    {n : ℕ} {x : M}
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) n x)
    (s d : Fin n → TangentSpace I x)
    (σ : Fin n → Fin n)
    (hσinv : ∀ a : Fin n, σ (σ a) = a)
    (hβ : ∀ u : Fin n → TangentSpace I x, β u + β (u ∘ σ) = 0) :
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ σ) a (d (σ a)))) = 0 := by
  classical
  have hupdate : ∀ a : Fin n,
      Function.update (s ∘ σ) (σ a) (d a) = (Function.update s a (d a)) ∘ σ := by
    intro a
    funext b
    by_cases h : b = σ a
    · have hb : σ b = a := by
        rw [h]
        exact hσinv a
      simp [Function.update, h, hσinv a]
    · have hb : σ b ≠ a := by
        intro hb
        apply h
        have hσb : σ (σ b) = σ a := congrArg σ hb
        rwa [hσinv b] at hσb
      simp [Function.update, h, hb]
  have hreindex : (∑ a : Fin n, β (Function.update (s ∘ σ) a (d (σ a)))) =
      ∑ a : Fin n, β (Function.update (s ∘ σ) (σ a) (d a)) := by
    refine Finset.sum_bij (fun a _ => σ a) ?_ ?_ ?_ ?_
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      have h' := congrArg σ h
      rwa [hσinv a₁, hσinv a₂] at h'
    · intro b hb
      refine ⟨σ b, by simp, ?_⟩
      exact hσinv b
    · intro a ha
      rw [hσinv a]
  calc
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ σ) a (d (σ a))))
        = (∑ a : Fin n, β (Function.update s a (d a))) +
            (∑ a : Fin n, β (Function.update (s ∘ σ) (σ a) (d a))) := by
          rw [hreindex]
    _ = (∑ a : Fin n, (β (Function.update s a (d a)) +
          β (Function.update (s ∘ σ) (σ a) (d a)))) := by
          simp [Finset.sum_add_distrib]
    _ = 0 := by
          simp [hupdate, hβ]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma fiberRegion_tensor_sum_cyclePair
    {n : ℕ} {x : M}
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) n x)
    (s d : Fin n → TangentSpace I x)
    (τ : Fin n → Fin n)
    (hτ3id : ∀ a : Fin n, τ (τ (τ a)) = a)
    (hβ : ∀ u : Fin n → TangentSpace I x, β u + β (u ∘ τ) + β (u ∘ τ ∘ τ) = 0) :
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ) a (d (τ a)))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a))))) = 0 := by
  classical
  have hupdate1 : ∀ a : Fin n,
      Function.update (s ∘ τ) (τ (τ a)) (d a) = (Function.update s a (d a)) ∘ τ := by
    intro a
    funext b
    by_cases h : b = τ (τ a)
    · have hb : τ b = a := by
        rw [h]
        exact hτ3id a
      simp [Function.update, h, hτ3id a]
    · have hb : τ b ≠ a := by
        intro hb
        apply h
        have hτb : τ (τ (τ b)) = τ (τ a) := congrArg τ (congrArg τ hb)
        rwa [hτ3id b] at hτb
      simp [Function.update, h, hb]
  have hupdate2 : ∀ a : Fin n,
      Function.update (s ∘ τ ∘ τ) (τ a) (d a) = (Function.update s a (d a)) ∘ τ ∘ τ := by
    intro a
    funext b
    by_cases h : b = τ a
    · have hb : τ (τ b) = a := by
        rw [h]
        exact hτ3id a
      simp [Function.update, h, hτ3id a]
    · have hb : τ (τ b) ≠ a := by
        intro hb
        apply h
        have hτb : τ (τ (τ b)) = τ a := congrArg τ hb
        rwa [hτ3id b] at hτb
      simp [Function.update, h, hb]
  have hreindex1 : (∑ a : Fin n, β (Function.update (s ∘ τ) a (d (τ a)))) =
      ∑ a : Fin n, β (Function.update (s ∘ τ) (τ (τ a)) (d a)) := by
    refine Finset.sum_bij (fun a _ => τ a) ?_ ?_ ?_ ?_
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      have h' := congrArg τ (congrArg τ h)
      rwa [hτ3id a₁, hτ3id a₂] at h'
    · intro b hb
      refine ⟨τ (τ b), by simp, ?_⟩
      exact hτ3id b
    · intro a ha
      rw [hτ3id a]
  have hreindex2 : (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a))))) =
      ∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) (τ a) (d a)) := by
    refine Finset.sum_bij (fun a _ => τ (τ a)) ?_ ?_ ?_ ?_
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      have h' := congrArg τ h
      rwa [hτ3id a₁, hτ3id a₂] at h'
    · intro b hb
      refine ⟨τ b, by simp, ?_⟩
      exact hτ3id b
    · intro a ha
      rw [hτ3id a]
  calc
    (∑ a : Fin n, β (Function.update s a (d a))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ) a (d (τ a)))) +
        (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a)))))
        = (∑ a : Fin n, β (Function.update s a (d a))) +
            (∑ a : Fin n, β (Function.update (s ∘ τ) (τ (τ a)) (d a))) +
            (∑ a : Fin n, β (Function.update (s ∘ τ ∘ τ) (τ a) (d a))) := by
          rw [hreindex1, hreindex2]
    _ = (∑ a : Fin n, (β (Function.update s a (d a)) +
          β (Function.update (s ∘ τ) (τ (τ a)) (d a)) +
          β (Function.update (s ∘ τ ∘ τ) (τ a) (d a)))) := by
          simp [Finset.sum_add_distrib]
    _ = 0 := by
          simp [hupdate1, hupdate2, hβ]

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
private lemma fiberRegion_nabla_of_algCurvForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (nablaα : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 cov α nablaα)
    (hAlg : ∀ y : M, IsAlgCurvForm
      (fun X Y Z W : TangentSpace I y => tensor04StandardAt (I := I) (M := M) (α y) X Y Z W))
    (x : M) :
    ∀ u X Y Z W : TangentSpace I x,
      nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 Y X Z W)) ∧
      nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 X Y W Z)) ∧
      nablaα x (Fin.cons u (vec4 X Y Z W)) + nablaα x (Fin.cons u (vec4 Y Z X W)) +
        nablaα x (Fin.cons u (vec4 Z X Y W)) = 0 := by
  classical
  intro u X Y Z W
  let U : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u).choose
  have hU : U x = u :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose
  have hV : ∀ a : Fin 4, V a x = vec4 X Y Z W a := fun a =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose_spec
  let s : Fin 4 → TangentSpace I x := fun b => V b x
  let d : Fin 4 → TangentSpace I x := fun a => (cov (fun p : M => V a p) x) (U x)
  let f : M → ℝ := fun p => α p (fun a : Fin 4 => V a p)
  have hslots : (fun a : Fin 4 => V a x) = vec4 X Y Z W := by
    funext a
    exact hV a
  have hderiv : nablaα x (Fin.cons u (vec4 X Y Z W)) =
      mvfderiv (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a)) := by
    have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V x
    simpa [hU, s, d, f, hslots] using h
  have hmdiff_f : MDifferentiableAt I 𝓘(Real, Real) f x :=
    ContMDiffAt.mdifferentiableAt
      (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α V x)
      (by simp)
  have hderiv_perm : ∀ (Wp : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (hW : (fun a : Fin 4 => Wp a x) = vec4 Y X Z W),
      nablaα x (Fin.cons u (vec4 Y X Z W)) =
        mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => Wp a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => Wp b x) a
            ((cov (fun p : M => Wp a p) x) (U x))) := by
    intro Wp hW
    have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U Wp x
    simpa [hU, hW] using h
  have hanti1 : nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 Y X Z W)) := by
    let σ01 : Fin 4 → Fin 4 := fun a => if a = 0 then 1 else if a = 1 then 0 else a
    let V01 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (σ01 a)
    have hV01 : (fun a : Fin 4 => V01 a x) = vec4 Y X Z W := by
      funext a
      fin_cases a <;> simp [V01, σ01, hV, vec4]
    have hderiv01 : nablaα x (Fin.cons u (vec4 Y X Z W)) =
        mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V01 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V01 b x) a
            ((cov (fun p : M => V01 a p) x) (U x))) := hderiv_perm V01 hV01
    have hfun01 : (fun p : M => α p (fun a : Fin 4 => V01 a p)) =
        fun p : M => -α p (fun a : Fin 4 => V a p) := by
      funext p
      have hrec1 : (fun a : Fin 4 => V01 a p) = vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [V01, σ01, vec4]
      have hrec2 : (fun a : Fin 4 => V a p) = vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [vec4]
      calc
        α p (fun a : Fin 4 => V01 a p)
            = tensor04StandardAt (I := I) (M := M) (α p) (V 1 p) (V 0 p) (V 2 p) (V 3 p) := by
              rw [hrec1]
              rfl
        _ = -tensor04StandardAt (I := I) (M := M) (α p) (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
              exact (hAlg p).anti_first (V 1 p) (V 0 p) (V 2 p) (V 3 p)
        _ = -α p (fun a : Fin 4 => V a p) := by
              rw [hrec2]
              rfl
    have hext01 : mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V01 a p)) x (U x) =
        -mvfderiv (I := I) f x (U x) := by
      have hneg : mvfderiv (I := I) (fun p : M => -α p (fun a : Fin 4 => V a p)) x (U x) =
          -mvfderiv (I := I) f x (U x) :=
        DifferentialGeometry.Tensor.RicciIdentity.mvfderiv_neg_at (I := I) (f := f) (x := x) (U x) hmdiff_f
      rw [← hfun01] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 4 → TangentSpace I x, α x v + α x (v ∘ σ01) = 0 := by
      intro v
      have h1 : α x v = tensor04StandardAt (I := I) (M := M) (α x) (v 0) (v 1) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [vec4]
      have h2 : α x (v ∘ σ01) = tensor04StandardAt (I := I) (M := M) (α x) (v 1) (v 0) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [σ01, vec4]
      have hanti := (hAlg x).anti_first (v 0) (v 1) (v 2) (v 3)
      rw [h1, h2, hanti]
      ring
    have hsum01 : (∑ a : Fin 4, α x (Function.update s a (d a))) =
        -(∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V01 b x) a
          ((cov (fun p : M => V01 a p) x) (U x)))) := by
      have hpair := fiberRegion_tensor_sum_antiPair (α x) s d σ01
        (by intro a; fin_cases a <;> simp [σ01]) hβ
      have hsimpa : (∑ a : Fin 4, α x (Function.update (s ∘ σ01) a (d (σ01 a)))) =
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V01 b x) a
            ((cov (fun p : M => V01 a p) x) (U x))) := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
      linarith [hpair, hsimpa]
    calc
      nablaα x (Fin.cons u (vec4 X Y Z W))
          = mvfderiv (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a)) := hderiv
      _ = -nablaα x (Fin.cons u (vec4 Y X Z W)) := by
            rw [hderiv01]
            rw [hext01, hsum01]
            ring
  have hanti2 : nablaα x (Fin.cons u (vec4 X Y Z W)) = -nablaα x (Fin.cons u (vec4 X Y W Z)) := by
    let σ23 : Fin 4 → Fin 4 := fun a => if a = 2 then 3 else if a = 3 then 2 else a
    let V23 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (σ23 a)
    have hV23 : (fun a : Fin 4 => V23 a x) = vec4 X Y W Z := by
      funext a
      fin_cases a <;> simp [V23, σ23, hV, vec4]
    have hderiv23 : nablaα x (Fin.cons u (vec4 X Y W Z)) =
        mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V23 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V23 b x) a
            ((cov (fun p : M => V23 a p) x) (U x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V23 x
      simpa [hU, hV23] using h
    have hfun23 : (fun p : M => α p (fun a : Fin 4 => V23 a p)) =
        fun p : M => -α p (fun a : Fin 4 => V a p) := by
      funext p
      have hrec1 : (fun a : Fin 4 => V23 a p) = vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p) := by
        funext a
        fin_cases a <;> simp [V23, σ23, vec4]
      have hrec2 : (fun a : Fin 4 => V a p) = vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [vec4]
      calc
        α p (fun a : Fin 4 => V23 a p)
            = tensor04StandardAt (I := I) (M := M) (α p) (V 0 p) (V 1 p) (V 3 p) (V 2 p) := by
              rw [hrec1]
              rfl
        _ = -tensor04StandardAt (I := I) (M := M) (α p) (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
              exact (hAlg p).anti_last (V 0 p) (V 1 p) (V 3 p) (V 2 p)
        _ = -α p (fun a : Fin 4 => V a p) := by
              rw [hrec2]
              rfl
    have hext23 : mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V23 a p)) x (U x) =
        -mvfderiv (I := I) f x (U x) := by
      have hneg : mvfderiv (I := I) (fun p : M => -α p (fun a : Fin 4 => V a p)) x (U x) =
          -mvfderiv (I := I) f x (U x) :=
        DifferentialGeometry.Tensor.RicciIdentity.mvfderiv_neg_at (I := I) (f := f) (x := x) (U x) hmdiff_f
      rw [← hfun23] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 4 → TangentSpace I x, α x v + α x (v ∘ σ23) = 0 := by
      intro v
      have h1 : α x v = tensor04StandardAt (I := I) (M := M) (α x) (v 0) (v 1) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [vec4]
      have h2 : α x (v ∘ σ23) = tensor04StandardAt (I := I) (M := M) (α x) (v 0) (v 1) (v 3) (v 2) := by
        congr 1
        funext b
        fin_cases b <;> simp [σ23, vec4]
      have hanti := (hAlg x).anti_last (v 0) (v 1) (v 2) (v 3)
      rw [h1, h2, hanti]
      ring
    have hsum23 : (∑ a : Fin 4, α x (Function.update s a (d a))) =
        -(∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V23 b x) a
          ((cov (fun p : M => V23 a p) x) (U x)))) := by
      have hpair := fiberRegion_tensor_sum_antiPair (α x) s d σ23
        (by intro a; fin_cases a <;> simp [σ23]) hβ
      have hsimpa : (∑ a : Fin 4, α x (Function.update (s ∘ σ23) a (d (σ23 a)))) =
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V23 b x) a
            ((cov (fun p : M => V23 a p) x) (U x))) := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
      linarith [hpair, hsimpa]
    calc
      nablaα x (Fin.cons u (vec4 X Y Z W))
          = mvfderiv (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a)) := hderiv
      _ = -nablaα x (Fin.cons u (vec4 X Y W Z)) := by
            rw [hderiv23]
            rw [hext23, hsum23]
            ring
  have hbianchi : nablaα x (Fin.cons u (vec4 X Y Z W)) + nablaα x (Fin.cons u (vec4 Y Z X W)) +
      nablaα x (Fin.cons u (vec4 Z X Y W)) = 0 := by
    let τ : Fin 4 → Fin 4 := fun a => if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 0 else a
    let V2 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (τ a)
    let V3 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (τ (τ a))
    have hV2 : (fun a : Fin 4 => V2 a x) = vec4 Y Z X W := by
      funext a
      fin_cases a <;> simp [V2, τ, hV, vec4]
    have hV3 : (fun a : Fin 4 => V3 a x) = vec4 Z X Y W := by
      funext a
      fin_cases a <;> simp [V3, τ, hV, vec4]
    have hderiv2 : nablaα x (Fin.cons u (vec4 Y Z X W)) =
        mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V2 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (U x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V2 x
      simpa [hU, hV2] using h
    have hderiv3 : nablaα x (Fin.cons u (vec4 Z X Y W)) =
        mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V3 a p)) x (U x) -
          ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
            ((cov (fun p : M => V3 a p) x) (U x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA U V3 x
      simpa [hU, hV3] using h
    have hfun2 : (fun p : M => α p (fun a : Fin 4 => V2 a p)) =
        fun p : M => α p (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) := by
      funext p
      congr 1
      funext a
      fin_cases a <;> simp [V2, τ, vec4]
    have hfun3 : (fun p : M => α p (fun a : Fin 4 => V3 a p)) =
        fun p : M => α p (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
      funext p
      congr 1
      funext a
      fin_cases a <;> simp [V3, τ, vec4]
    have hfun : (fun p : M => α p (fun a : Fin 4 => V a p)) +
        (fun p : M => α p (fun a : Fin 4 => V2 a p)) +
        (fun p : M => α p (fun a : Fin 4 => V3 a p)) = 0 := by
      funext p
      have hrec1 : (fun a : Fin 4 => V a p) = vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p) := by
        funext a
        fin_cases a <;> simp [vec4]
      have hb := (hAlg p).bianchi (V 0 p) (V 1 p) (V 2 p) (V 3 p)
      have h2p : α p (fun a : Fin 4 => V2 a p) = α p (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) := by
        congr 1
        funext a
        fin_cases a <;> simp [V2, τ, vec4]
      have h3p : α p (fun a : Fin 4 => V3 a p) = α p (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
        congr 1
        funext a
        fin_cases a <;> simp [V3, τ, vec4]
      calc
        α p (fun a : Fin 4 => V a p) + α p (fun a : Fin 4 => V2 a p) + α p (fun a : Fin 4 => V3 a p)
            = α p (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) +
                α p (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) +
                α p (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
              rw [hrec1, h2p, h3p]
        _ = 0 := hb
    have hext2 : mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V2 a p)) x (U x) =
        -mvfderiv (I := I) f x (U x) - mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V3 a p)) x (U x) := by
      let f2 : M → ℝ := fun p => α p (fun a : Fin 4 => V2 a p)
      let f3 : M → ℝ := fun p => α p (fun a : Fin 4 => V3 a p)
      have h1 : mvfderiv (I := I) (f + f2 + f3) x (U x) = 0 := by
        have hzero : f + f2 + f3 = 0 := hfun
        simp [hzero]
      have hmd1 : MDifferentiableAt I 𝓘(Real, Real) f x := hmdiff_f
      have hmd2 : MDifferentiableAt I 𝓘(Real, Real) f2 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α V2 x)
          (by simp)
      have hmd3 : MDifferentiableAt I 𝓘(Real, Real) f3 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α V3 x)
          (by simp)
      have h12 := mvfderiv_add (I := I) (g := f) (g' := f2) (x := x) hmd1 hmd2
      have h123 := mvfderiv_add (I := I) (g := f + f2) (g' := f3) (x := x) (hmd1.add hmd2) hmd3
      have hsum_deriv : mvfderiv (I := I) (f + f2 + f3) x (U x) =
          mvfderiv (I := I) f x (U x) + mvfderiv (I := I) f2 x (U x) +
            mvfderiv (I := I) f3 x (U x) := by
        calc
          mvfderiv (I := I) (f + f2 + f3) x (U x)
              = mvfderiv (I := I) (f + f2) x (U x) + mvfderiv (I := I) f3 x (U x) := by
                simpa [add_apply] using congr(($(h123) : _) (U x))
          _ = (mvfderiv (I := I) f x (U x) + mvfderiv (I := I) f2 x (U x)) +
                mvfderiv (I := I) f3 x (U x) := by
                have happ : mvfderiv (I := I) (f + f2) x (U x) =
                    mvfderiv (I := I) f x (U x) + mvfderiv (I := I) f2 x (U x) := by
                  simpa [add_apply] using congr(($(h12) : _) (U x))
                rw [happ]
          _ = mvfderiv (I := I) f x (U x) + mvfderiv (I := I) f2 x (U x) +
                mvfderiv (I := I) f3 x (U x) := by
                simp [add_assoc]
      have htotal : mvfderiv (I := I) f x (U x) + mvfderiv (I := I) f2 x (U x) +
            mvfderiv (I := I) f3 x (U x) = 0 := by
        rwa [hsum_deriv] at h1
      linarith
    have hβ : ∀ v : Fin 4 → TangentSpace I x, α x v + α x (v ∘ τ) + α x (v ∘ τ ∘ τ) = 0 := by
      intro v
      have h1 : α x v = tensor04StandardAt (I := I) (M := M) (α x) (v 0) (v 1) (v 2) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [vec4]
      have h2 : α x (v ∘ τ) = tensor04StandardAt (I := I) (M := M) (α x) (v 1) (v 2) (v 0) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [τ, vec4]
      have h3 : α x (v ∘ τ ∘ τ) = tensor04StandardAt (I := I) (M := M) (α x) (v 2) (v 0) (v 1) (v 3) := by
        congr 1
        funext b
        fin_cases b <;> simp [τ, vec4]
      have hb := (hAlg x).bianchi (v 0) (v 1) (v 2) (v 3)
      rw [h1, h2, h3]
      exact hb
    have hsum2 : (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
          ((cov (fun p : M => V2 a p) x) (U x)))) =
        ∑ a : Fin 4, α x (Function.update (s ∘ τ) a (d (τ a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
    have hsum3 : (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
          ((cov (fun p : M => V3 a p) x) (U x)))) =
        ∑ a : Fin 4, α x (Function.update (s ∘ τ ∘ τ) a (d (τ (τ a)))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
    have hpair := fiberRegion_tensor_sum_cyclePair (α x) s d τ
      (by intro a; fin_cases a <;> simp [τ]) hβ
    have hS : (∑ a : Fin 4, α x (Function.update s a (d a))) +
        (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
          ((cov (fun p : M => V2 a p) x) (U x)))) +
        (∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
          ((cov (fun p : M => V3 a p) x) (U x)))) = 0 := by
      simpa [hsum2, hsum3] using hpair
    calc
      nablaα x (Fin.cons u (vec4 X Y Z W)) + nablaα x (Fin.cons u (vec4 Y Z X W)) +
          nablaα x (Fin.cons u (vec4 Z X Y W))
          = (mvfderiv (I := I) f x (U x) - ∑ a : Fin 4, α x (Function.update s a (d a))) +
              (mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V2 a p)) x (U x) -
                ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V2 b x) a
                  ((cov (fun p : M => V2 a p) x) (U x)))) +
              (mvfderiv (I := I) (fun p : M => α p (fun a : Fin 4 => V3 a p)) x (U x) -
                ∑ a : Fin 4, α x (Function.update (fun b : Fin 4 => V3 b x) a
                  ((cov (fun p : M => V3 a p) x) (U x)))) := by
            rw [hderiv, hderiv2, hderiv3]
      _ = 0 := by
            rw [hext2]
            linarith [hS]
  exact ⟨hanti1, hanti2, hbianchi⟩

private def fiberRegion_fin5_cons {α : Type*} (a0 : α) (f : Fin 4 → α) : Fin 5 → α :=
  fun a => Fin.cases (motive := fun _ : Fin 5 => α) a0 f a

@[simp] private lemma fiberRegion_fin5_cons_zero {α : Type*} (a0 : α) (f : Fin 4 → α) :
    fiberRegion_fin5_cons a0 f 0 = a0 := by
  change Fin.cases (motive := fun _ : Fin 5 => α) a0 f 0 = a0
  simp

@[simp] private lemma fiberRegion_fin5_cons_succ {α : Type*} (a0 : α) (f : Fin 4 → α) (i : Fin 4) :
    fiberRegion_fin5_cons a0 f i.succ = f i := by
  change Fin.cases (motive := fun _ : Fin 5 => α) a0 f i.succ = f i
  simp

@[simp] private lemma fiberRegion_fin5_cons_apply {α : Type*} (a0 : α) (f : Fin 4 → α) :
    fiberRegion_fin5_cons a0 f 1 = f 0 ∧
      fiberRegion_fin5_cons a0 f 2 = f 1 ∧
      fiberRegion_fin5_cons a0 f 3 = f 2 ∧
      fiberRegion_fin5_cons a0 f 4 = f 3 := by
  constructor
  · simpa using (fiberRegion_fin5_cons_succ a0 f (0 : Fin 4))
  · constructor
    · simpa using (fiberRegion_fin5_cons_succ a0 f (1 : Fin 4))
    · constructor
      · simpa using (fiberRegion_fin5_cons_succ a0 f (2 : Fin 4))
      · simpa using (fiberRegion_fin5_cons_succ a0 f (3 : Fin 4))

private lemma fiberRegion_fin5_cons_eq_cons {α : Type*} (a0 : α) (f : Fin 4 → α) :
    fiberRegion_fin5_cons a0 f = Fin.cons a0 f := by
  funext b
  cases b using Fin.cases with
  | zero => rfl
  | succ i => rfl

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
private lemma fiberRegion_nabla2_of_algCurvForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (nablaα : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5)
    (nabla2α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 6)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 cov α nablaα)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 cov nablaα nabla2α)
    (hAlg : ∀ y : M, IsAlgCurvForm
      (fun X Y Z W : TangentSpace I y => tensor04StandardAt (I := I) (M := M) (α y) X Y Z W))
    (x : M) :
    ∀ u1 u2 X Y Z W : TangentSpace I x,
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
          -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) ∧
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
          -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) ∧
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W))) = 0 := by
  classical
  have hSym5 : ∀ y : M, ∀ u X Y Z W : TangentSpace I y,
      nablaα y (Fin.cons u (vec4 X Y Z W)) = -nablaα y (Fin.cons u (vec4 Y X Z W)) ∧
      nablaα y (Fin.cons u (vec4 X Y Z W)) = -nablaα y (Fin.cons u (vec4 X Y W Z)) ∧
      nablaα y (Fin.cons u (vec4 X Y Z W)) + nablaα y (Fin.cons u (vec4 Y Z X W)) +
        nablaα y (Fin.cons u (vec4 Z X Y W)) = 0 :=
    fun y => fiberRegion_nabla_of_algCurvForm (I := I) cov α nablaα hA hAlg y
  intro u1 u2 X Y Z W
  let U1 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u1).choose
  have hU1 : U1 x = u1 :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u1).choose_spec
  let U2 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u2).choose
  have hU2 : U2 x = u2 :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u2).choose_spec
  let V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose
  have hV : ∀ a : Fin 4, V a x = vec4 X Y Z W a := fun a =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (vec4 X Y Z W a)).choose_spec
  let W2 : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fiberRegion_fin5_cons U2 V
  let s5 : Fin 5 → TangentSpace I x := fun b => W2 b x
  let d5 : Fin 5 → TangentSpace I x := fun a => (cov (fun p : M => W2 a p) x) (U1 x)
  let f : M → ℝ := fun p => nablaα p (fun a : Fin 5 => W2 a p)
  have hslots : (fun a : Fin 5 => W2 a x) = fiberRegion_fin5_cons u2 (vec4 X Y Z W) := by
    funext a
    fin_cases a <;> simp [W2, hU2, hV, vec4]
  have hderiv : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
      mvfderiv (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a)) := by
    have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2 x
    simpa [hU1, s5, d5, f, hslots] using h
  have hmdiff_f : MDifferentiableAt I 𝓘(Real, Real) f x :=
    ContMDiffAt.mdifferentiableAt
      (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) nablaα W2 x)
      (by simp)
  have hrec5 : ∀ v : Fin 5 → TangentSpace I x,
      v = fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)) := by
    intro v
    funext b
    fin_cases b <;> simp [vec4]
  have hanti1 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
      -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) := by
    let σ12 : Fin 5 → Fin 5 := fun a => if a = 1 then 2 else if a = 2 then 1 else a
    let V01 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 0 then 1 else if a = 1 then 0 else a)
    have hV01 : ∀ a : Fin 4, V01 a x = vec4 Y X Z W a := by
      intro a
      fin_cases a <;> simp [V01, hV, vec4]
    let W2' : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V01
    have hslots01 : (fun a : Fin 5 => W2' a x) = fiberRegion_fin5_cons u2 (vec4 Y X Z W) := by
      funext a
      fin_cases a <;> simp [W2', hU2, hV01, vec4]
    have hderiv01 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) =
        mvfderiv (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2' a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2' b x) a
            ((cov (fun p : M => W2' a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2' x
      simpa [hU1, hslots01] using h
    have hfun01 : (fun p : M => nablaα p (fun a : Fin 5 => W2' a p)) =
        fun p : M => -nablaα p (fun a : Fin 5 => W2 a p) := by
      funext p
      have hrec1 : (fun a : Fin 5 => W2' a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2' a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2']
        · intro i
          change V01 i p = (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [V01, vec4]
      have hrec2 : (fun a : Fin 5 => W2 a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2 a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2]
        · intro i
          change V i p = (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [vec4]
      have hsym := (hSym5 p (U2 p) (V 1 p) (V 0 p) (V 2 p) (V 3 p)).1
      calc
        nablaα p (fun a : Fin 5 => W2' a p)
            = nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 0 p) (V 2 p) (V 3 p))) := by
              rw [hrec1]
        _ = -nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p))) := hsym
        _ = -nablaα p (fun a : Fin 5 => W2 a p) := by
              rw [hrec2]
    have hext01 : mvfderiv (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2' a p)) x (U1 x) =
        -mvfderiv (I := I) f x (U1 x) := by
      have hneg : mvfderiv (I := I) (fun p : M => -nablaα p (fun a : Fin 5 => W2 a p)) x (U1 x) =
          -mvfderiv (I := I) f x (U1 x) :=
        DifferentialGeometry.Tensor.RicciIdentity.mvfderiv_neg_at (I := I) (f := f) (x := x) (U1 x) hmdiff_f
      rw [← hfun01] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 5 → TangentSpace I x, nablaα x v + nablaα x (v ∘ σ12) = 0 := by
      intro v
      have h1 : nablaα x v = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) := by
        rw [← hrec5 v]
      have h2 : nablaα x (v ∘ σ12) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ σ12) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [σ12]
        · intro i
          change v (σ12 i.succ) = (vec4 (v 2) (v 1) (v 3) (v 4)) i
          fin_cases i <;> simp [σ12, vec4]
      have hsym := (hSym5 x (v 0) (v 1) (v 2) (v 3) (v 4)).1
      calc
        nablaα x v + nablaα x (v ∘ σ12)
            = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4))) := by
              rw [h1, h2]
        _ = 0 := by
              rw [fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 2) (v 1) (v 3) (v 4))]
              rw [hsym]
              ring
    have hpair : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
        (∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ12) a (d5 (σ12 a)))) = 0 :=
      fiberRegion_tensor_sum_antiPair (nablaα x) s5 d5 σ12
        (by intro a; fin_cases a <;> simp [σ12]) hβ
    have hW2' : ∀ a : Fin 5, (fun p : M => W2' a p) = fun p : M => W2 (σ12 a) p := by
      intro a
      funext p
      fin_cases a <;> simp [W2, W2', V01, σ12]
    have hsimpa : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2' b x) a
          ((cov (fun p : M => W2' a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ12) a (d5 (σ12 a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp only [s5, d5]
      rw [hW2' a]
      congr 1
      funext b
      change W2' b x = W2 (σ12 b) x
      exact congrFun (hW2' b) x
    have hsum01 : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) =
        -(∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2' b x) a
          ((cov (fun p : M => W2' a p) x) (U1 x)))) := by
      rw [hsimpa]
      linarith [hpair]
    calc
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W)))
          = mvfderiv (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a)) := hderiv
      _ = -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y X Z W))) := by
            rw [hderiv01]
            rw [hext01, hsum01]
            ring
  have hanti2 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) =
      -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) := by
    let σ34 : Fin 5 → Fin 5 := fun a => if a = 3 then 4 else if a = 4 then 3 else a
    let V02 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 2 then 3 else if a = 3 then 2 else a)
    have hV02 : ∀ a : Fin 4, V02 a x = vec4 X Y W Z a := by
      intro a
      fin_cases a <;> simp [V02, hV, vec4]
    let W2'' : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V02
    have hslots02 : (fun a : Fin 5 => W2'' a x) = fiberRegion_fin5_cons u2 (vec4 X Y W Z) := by
      funext a
      fin_cases a <;> simp [W2'', hU2, hV02, vec4]
    have hderiv02 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) =
        mvfderiv (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2'' a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2'' b x) a
            ((cov (fun p : M => W2'' a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2'' x
      simpa [hU1, hslots02] using h
    have hfun02 : (fun p : M => nablaα p (fun a : Fin 5 => W2'' a p)) =
        fun p : M => -nablaα p (fun a : Fin 5 => W2 a p) := by
      funext p
      have hrec1 : (fun a : Fin 5 => W2'' a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2'' a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2'']
        · intro i
          change V02 i p = (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p)) i
          fin_cases i <;> simp [V02, vec4]
      have hrec2 : (fun a : Fin 5 => W2 a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2 a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2]
        · intro i
          change V i p = (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [vec4]
      have hsym := (hSym5 p (U2 p) (V 0 p) (V 1 p) (V 3 p) (V 2 p)).2.1
      calc
        nablaα p (fun a : Fin 5 => W2'' a p)
            = nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 3 p) (V 2 p))) := by
              rw [hrec1]
        _ = -nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p))) := hsym
        _ = -nablaα p (fun a : Fin 5 => W2 a p) := by
              rw [hrec2]
    have hext02 : mvfderiv (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2'' a p)) x (U1 x) =
        -mvfderiv (I := I) f x (U1 x) := by
      have hneg : mvfderiv (I := I) (fun p : M => -nablaα p (fun a : Fin 5 => W2 a p)) x (U1 x) =
          -mvfderiv (I := I) f x (U1 x) :=
        DifferentialGeometry.Tensor.RicciIdentity.mvfderiv_neg_at (I := I) (f := f) (x := x) (U1 x) hmdiff_f
      rw [← hfun02] at hneg
      simpa [f] using hneg
    have hβ : ∀ v : Fin 5 → TangentSpace I x, nablaα x v + nablaα x (v ∘ σ34) = 0 := by
      intro v
      have h1 : nablaα x v = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) := by
        rw [← hrec5 v]
      have h2 : nablaα x (v ∘ σ34) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ σ34) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [σ34]
        · intro i
          change v (σ34 i.succ) = (vec4 (v 1) (v 2) (v 4) (v 3)) i
          fin_cases i <;> simp [σ34, vec4]
      have hsym := (hSym5 x (v 0) (v 1) (v 2) (v 3) (v 4)).2.1
      calc
        nablaα x v + nablaα x (v ∘ σ34)
            = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3))) := by
              rw [h1, h2]
        _ = 0 := by
              rw [fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 4) (v 3))]
              rw [hsym]
              ring
    have hpair : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
        (∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ34) a (d5 (σ34 a)))) = 0 :=
      fiberRegion_tensor_sum_antiPair (nablaα x) s5 d5 σ34
        (by intro a; fin_cases a <;> simp [σ34]) hβ
    have hW2'' : ∀ a : Fin 5, (fun p : M => W2'' a p) = fun p : M => W2 (σ34 a) p := by
      intro a
      funext p
      fin_cases a <;> simp [W2, W2'', V02, σ34]
    have hsimpa : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2'' b x) a
          ((cov (fun p : M => W2'' a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ σ34) a (d5 (σ34 a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp only [s5, d5]
      rw [hW2'' a]
      congr 1
      funext b
      change W2'' b x = W2 (σ34 b) x
      exact congrFun (hW2'' b) x
    have hsum02 : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) =
        -(∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2'' b x) a
          ((cov (fun p : M => W2'' a p) x) (U1 x)))) := by
      rw [hsimpa]
      linarith [hpair]
    calc
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W)))
          = mvfderiv (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a)) := hderiv
      _ = -nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y W Z))) := by
            rw [hderiv02]
            rw [hext02, hsum02]
            ring
  have hbianchi : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) +
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) +
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W))) = 0 := by
    let τ : Fin 5 → Fin 5 := fun a => if a = 1 then 2 else if a = 2 then 3 else if a = 3 then 1 else a
    let V2 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 0 else a)
    let V3 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fun a => V (if a = 0 then 2 else if a = 1 then 0 else if a = 2 then 1 else a)
    have hV2 : ∀ a : Fin 4, V2 a x = vec4 Y Z X W a := by
      intro a
      fin_cases a <;> simp [V2, hV, vec4]
    have hV3 : ∀ a : Fin 4, V3 a x = vec4 Z X Y W a := by
      intro a
      fin_cases a <;> simp [V3, hV, vec4]
    let W2b : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V2
    let W2c : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
      fiberRegion_fin5_cons U2 V3
    have hslots2 : (fun a : Fin 5 => W2b a x) = fiberRegion_fin5_cons u2 (vec4 Y Z X W) := by
      funext a
      fin_cases a <;> simp [W2b, hU2, hV2, vec4]
    have hslots3 : (fun a : Fin 5 => W2c a x) = fiberRegion_fin5_cons u2 (vec4 Z X Y W) := by
      funext a
      fin_cases a <;> simp [W2c, hU2, hV3, vec4]
    have hderiv2 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) =
        mvfderiv (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2b a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
            ((cov (fun p : M => W2b a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2b x
      simpa [hU1, hslots2] using h
    have hderiv3 : nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W))) =
        mvfderiv (I := I) (fun p : M => nablaα p (fun a : Fin 5 => W2c a p)) x (U1 x) -
          ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
            ((cov (fun p : M => W2c a p) x) (U1 x))) := by
      have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) h2A U1 W2c x
      simpa [hU1, hslots3] using h
    let f2 : M → ℝ := fun p => nablaα p (fun a : Fin 5 => W2b a p)
    let f3 : M → ℝ := fun p => nablaα p (fun a : Fin 5 => W2c a p)
    have hfun : f + f2 + f3 = 0 := by
      funext p
      have hrec1 : (fun a : Fin 5 => W2 a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2 a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2]
        · intro i
          change V i p = (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p)) i
          fin_cases i <;> simp [vec4]
      have hrec2 : (fun a : Fin 5 => W2b a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2b a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2b]
        · intro i
          change V2 i p = (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p)) i
          fin_cases i <;> simp [V2, vec4]
      have hrec3 : (fun a : Fin 5 => W2c a p) = fiberRegion_fin5_cons (U2 p) (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) := by
        funext a
        refine Fin.cases (motive := fun a => W2c a p =
            (fiberRegion_fin5_cons (U2 p) (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) : Fin 5 → TangentSpace I p) a) ?_ ?_ a
        · simp [W2c]
        · intro i
          change V3 i p = (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p)) i
          fin_cases i <;> simp [V3, vec4]
      have hsym := (hSym5 p (U2 p) (V 0 p) (V 1 p) (V 2 p) (V 3 p)).2.2
      calc
        nablaα p (fun a : Fin 5 => W2 a p) + nablaα p (fun a : Fin 5 => W2b a p) +
            nablaα p (fun a : Fin 5 => W2c a p)
            = nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 0 p) (V 1 p) (V 2 p) (V 3 p))) +
                nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 1 p) (V 2 p) (V 0 p) (V 3 p))) +
                nablaα p (fiberRegion_fin5_cons (U2 p) (vec4 (V 2 p) (V 0 p) (V 1 p) (V 3 p))) := by
              rw [hrec1, hrec2, hrec3]
        _ = 0 := hsym
    have hext2 : mvfderiv (I := I) f2 x (U1 x) =
        -mvfderiv (I := I) f x (U1 x) - mvfderiv (I := I) f3 x (U1 x) := by
      have h1 : mvfderiv (I := I) (f + f2 + f3) x (U1 x) = 0 := by
        have hzero : f + f2 + f3 = 0 := hfun
        simp [hzero]
      have hmd1 : MDifferentiableAt I 𝓘(Real, Real) f x := hmdiff_f
      have hmd2 : MDifferentiableAt I 𝓘(Real, Real) f2 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) nablaα W2b x)
          (by simp)
      have hmd3 : MDifferentiableAt I 𝓘(Real, Real) f3 x :=
        ContMDiffAt.mdifferentiableAt
          (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) nablaα W2c x)
          (by simp)
      have h12 := mvfderiv_add (I := I) (g := f) (g' := f2) (x := x) hmd1 hmd2
      have h123 := mvfderiv_add (I := I) (g := f + f2) (g' := f3) (x := x) (hmd1.add hmd2) hmd3
      have hsum_deriv : mvfderiv (I := I) (f + f2 + f3) x (U1 x) =
          mvfderiv (I := I) f x (U1 x) + mvfderiv (I := I) f2 x (U1 x) +
            mvfderiv (I := I) f3 x (U1 x) := by
        calc
          mvfderiv (I := I) (f + f2 + f3) x (U1 x)
              = mvfderiv (I := I) (f + f2) x (U1 x) + mvfderiv (I := I) f3 x (U1 x) := by
                simpa [add_apply] using congr(($(h123) : _) (U1 x))
          _ = (mvfderiv (I := I) f x (U1 x) + mvfderiv (I := I) f2 x (U1 x)) +
                mvfderiv (I := I) f3 x (U1 x) := by
                have happ : mvfderiv (I := I) (f + f2) x (U1 x) =
                    mvfderiv (I := I) f x (U1 x) + mvfderiv (I := I) f2 x (U1 x) := by
                  simpa [add_apply] using congr(($(h12) : _) (U1 x))
                rw [happ]
          _ = mvfderiv (I := I) f x (U1 x) + mvfderiv (I := I) f2 x (U1 x) +
                mvfderiv (I := I) f3 x (U1 x) := by
                simp [add_assoc]
      have htotal : mvfderiv (I := I) f x (U1 x) + mvfderiv (I := I) f2 x (U1 x) +
            mvfderiv (I := I) f3 x (U1 x) = 0 := by
        rwa [hsum_deriv] at h1
      linarith
    have hβ : ∀ v : Fin 5 → TangentSpace I x,
        nablaα x v + nablaα x (v ∘ τ) + nablaα x (v ∘ τ ∘ τ) = 0 := by
      intro v
      have h1 : nablaα x v = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) := by
        rw [← hrec5 v]
      have h2 : nablaα x (v ∘ τ) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ τ) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [τ]
        · intro i
          change v (τ i.succ) = (vec4 (v 2) (v 3) (v 1) (v 4)) i
          fin_cases i <;> simp [τ, vec4]
      have h3 : nablaα x (v ∘ τ ∘ τ) = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4))) := by
        congr 1
        funext b
        refine Fin.cases (motive := fun b => (v ∘ τ ∘ τ) b =
            (fiberRegion_fin5_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4)) : Fin 5 → TangentSpace I x) b) ?_ ?_ b
        · simp [τ]
        · intro i
          change v (τ (τ i.succ)) = (vec4 (v 3) (v 1) (v 2) (v 4)) i
          fin_cases i <;> simp [τ, vec4]
      have hsym := (hSym5 x (v 0) (v 1) (v 2) (v 3) (v 4)).2.2
      calc
        nablaα x v + nablaα x (v ∘ τ) + nablaα x (v ∘ τ ∘ τ)
            = nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4))) +
                nablaα x (fiberRegion_fin5_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4))) := by
              rw [h1, h2, h3]
        _ = 0 := by
              rw [fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 1) (v 2) (v 3) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 2) (v 3) (v 1) (v 4)),
                fiberRegion_fin5_cons_eq_cons (v 0) (vec4 (v 3) (v 1) (v 2) (v 4))]
              exact hsym
    have hW2b : ∀ a : Fin 5, (fun p : M => W2b a p) = fun p : M => W2 (τ a) p := by
      intro a
      funext p
      fin_cases a <;> simp [W2b, W2, V2, τ]
    have hW2c : ∀ a : Fin 5, (fun p : M => W2c a p) = fun p : M => W2 (τ (τ a)) p := by
      intro a
      funext p
      fin_cases a <;> simp [W2c, W2, V3, τ]
    have hupd2 : ∀ a : Fin 5,
        Function.update (fun b : Fin 5 => W2b b x) a ((cov (fun p : M => W2b a p) x) (U1 x)) =
          Function.update (s5 ∘ τ) a (d5 (τ a)) := by
      intro a
      apply funext
      intro b
      rcases eq_or_ne b a with rfl | hb
      · rw [hW2b b]
        simp [Function.update, d5]
      · have hf : W2b b x = (s5 ∘ τ) b := by
          fin_cases b <;> simp [s5, W2, W2b, V2, τ, hV, vec4]
        simp [Function.update, hb, hf]
    have hupd3 : ∀ a : Fin 5,
        Function.update (fun b : Fin 5 => W2c b x) a ((cov (fun p : M => W2c a p) x) (U1 x)) =
          Function.update (s5 ∘ τ ∘ τ) a (d5 (τ (τ a))) := by
      intro a
      apply funext
      intro b
      rcases eq_or_ne b a with rfl | hb
      · rw [hW2c b]
        simp [Function.update, d5]
      · have hf : W2c b x = (s5 ∘ τ ∘ τ) b := by
          fin_cases b <;> simp [s5, W2, W2c, V3, τ, hV, vec4]
        simp [Function.update, hb, hf]
    have hsum2 : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
          ((cov (fun p : M => W2b a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ τ) a (d5 (τ a))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hupd2 a]
    have hsum3 : (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
          ((cov (fun p : M => W2c a p) x) (U1 x)))) =
        ∑ a : Fin 5, nablaα x (Function.update (s5 ∘ τ ∘ τ) a (d5 (τ (τ a)))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hupd3 a]
    have hpair := fiberRegion_tensor_sum_cyclePair (nablaα x) s5 d5 τ
      (by intro a; fin_cases a <;> simp [τ]) hβ
    have hS : (∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
        (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
          ((cov (fun p : M => W2b a p) x) (U1 x)))) +
        (∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
          ((cov (fun p : M => W2c a p) x) (U1 x)))) = 0 := by
      simpa [hsum2, hsum3] using hpair
    calc
      nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 X Y Z W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Y Z X W))) +
          nabla2α x (Fin.cons u1 (fiberRegion_fin5_cons u2 (vec4 Z X Y W)))
          = (mvfderiv (I := I) f x (U1 x) - ∑ a : Fin 5, nablaα x (Function.update s5 a (d5 a))) +
              (mvfderiv (I := I) f2 x (U1 x) -
                ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2b b x) a
                  ((cov (fun p : M => W2b a p) x) (U1 x)))) +
              (mvfderiv (I := I) f3 x (U1 x) -
                ∑ a : Fin 5, nablaα x (Function.update (fun b : Fin 5 => W2c b x) a
                  ((cov (fun p : M => W2c a p) x) (U1 x)))) := by
            rw [hderiv, hderiv2, hderiv3]
      _ = 0 := by
            rw [hext2]
            linarith [hS]
  exact ⟨hanti1, hanti2, hbianchi⟩

omit [SigmaCompactSpace M] [I.Boundaryless] in
private theorem fiberRegion_roughLapRm04_mem_algebraicCurvatureTensorSubmodule
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (t : ℝ) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
        (nablaKRm04Field (I := I) S t 2 x) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  classical
  have hA1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
      (S.base.connection t) (S.base.rm04 t) (nablaKRm04Field (I := I) S t 1) := by
    simpa [nablaKRm04Field_zero] using (nablaKRm04Field_realizes (I := I) S t 0)
  have hA2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
      (S.base.connection t) (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2) := by
    simpa using (nablaKRm04Field_realizes (I := I) S t 1)
  have hAlg : ∀ y : M, IsAlgCurvForm
      (fun X Y Z W : TangentSpace I y => tensor04StandardAt (I := I) (M := M) (S.base.rm04 t y) X Y Z W) := by
    intro y
    exact mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) y)
  have hSym6 : ∀ u1 u2 X Y Z W : TangentSpace I x,
      nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y Z W))) =
          -nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 Y X Z W))) ∧
      nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y Z W))) =
          -nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y W Z))) ∧
      nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 X Y Z W))) +
          nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 Y Z X W))) +
          nablaKRm04Field (I := I) S t 2 x (Fin.cons u1 (Fin.cons u2 (vec4 Z X Y W))) = 0 :=
    fiberRegion_nabla2_of_algCurvForm (I := I) (S.base.connection t) (S.base.rm04 t)
      (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2) hA1 hA2 hAlg x
  let T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 6 x :=
    nablaKRm04Field (I := I) S t 2 x
  let R : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3)) T
  have hRapply : ∀ tail : Fin 4 → TangentSpace I x,
      R tail = ∑ i : Fin 3, ∑ j : Fin 3,
        identityInvMetric (Idx := Fin 3) i j * T (metricTraceInput (I := I) (basis i) (basis j) tail) := by
    intro tail
    rw [metricTrace0S2TensorInBasis_apply]
    rfl
  have hcons : ∀ (u1 u2 : TangentSpace I x) (tail : Fin 4 → TangentSpace I x),
      metricTraceInput (I := I) u1 u2 tail = Fin.cons u1 (Fin.cons u2 tail) := by
    intro u1 u2 tail
    rfl
  rw [mem_algebraicCurvatureTensorSubmodule_iff_symmetries]
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z W
    have hsym_per : ∀ i j : Fin 3,
        T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) =
          -T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y X Z W)) := by
      intro i j
      have h := (hSym6 (basis i) (basis j) X Y Z W).1
      simpa [T, hcons] using h
    calc
      tensor04StandardAt (I := I) (M := M) R X Y Z W
          = ∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) := by
            simpa [R] using hRapply (vec4 X Y Z W)
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y X Z W)) := by
            simp_rw [hsym_per]
            simp [Finset.sum_neg_distrib, mul_neg]
      _ = -tensor04StandardAt (I := I) (M := M) R Y X Z W := by
            rw [← hRapply (vec4 Y X Z W)]
            rfl
  · intro X Y Z W
    have hsym_per : ∀ i j : Fin 3,
        T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) =
          -T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y W Z)) := by
      intro i j
      have h := (hSym6 (basis i) (basis j) X Y Z W).2.1
      simpa [T, hcons] using h
    calc
      tensor04StandardAt (I := I) (M := M) R X Y Z W
          = ∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) := by
            simpa [R] using hRapply (vec4 X Y Z W)
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y W Z)) := by
            simp_rw [hsym_per]
            simp [Finset.sum_neg_distrib, mul_neg]
      _ = -tensor04StandardAt (I := I) (M := M) R X Y W Z := by
            rw [← hRapply (vec4 X Y W Z)]
            rfl
  · intro X Y Z W
    have hsym_per : ∀ i j : Fin 3,
        T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
            T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
            T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)) = 0 := by
      intro i j
      have h := (hSym6 (basis i) (basis j) X Y Z W).2.2
      simpa [T, hcons] using h
    calc
      tensor04StandardAt (I := I) (M := M) R X Y Z W +
          tensor04StandardAt (I := I) (M := M) R Y Z X W +
          tensor04StandardAt (I := I) (M := M) R Z X Y W
          = (∑ i : Fin 3, ∑ j : Fin 3,
              identityInvMetric (Idx := Fin 3) i j *
                T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W))) +
              (∑ i : Fin 3, ∑ j : Fin 3,
                identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W))) +
              (∑ i : Fin 3, ∑ j : Fin 3,
                identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))) := by
            rw [show tensor04StandardAt (I := I) (M := M) R X Y Z W =
                ∑ i : Fin 3, ∑ j : Fin 3, identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) from by
              simpa [R] using hRapply (vec4 X Y Z W)]
            rw [show tensor04StandardAt (I := I) (M := M) R Y Z X W =
                ∑ i : Fin 3, ∑ j : Fin 3, identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) from by
              simpa [R] using hRapply (vec4 Y Z X W)]
            rw [show tensor04StandardAt (I := I) (M := M) R Z X Y W =
                ∑ i : Fin 3, ∑ j : Fin 3, identityInvMetric (Idx := Fin 3) i j *
                  T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)) from by
              simpa [R] using hRapply (vec4 Z X Y W)]
      _ = 0 := by
            have hper2 : ∀ i j : Fin 3,
                identityInvMetric (Idx := Fin 3) i j *
                    T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                  identityInvMetric (Idx := Fin 3) i j *
                    T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                  identityInvMetric (Idx := Fin 3) i j *
                    T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)) = 0 := by
              intro i j
              have h := hsym_per i j
              calc
                identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))
                    = identityInvMetric (Idx := Fin 3) i j *
                        (T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))) := by
                      ring
                _ = 0 := by
                      rw [h]
                      ring
            calc
              (∑ i : Fin 3, ∑ j : Fin 3,
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W))) +
                  (∑ i : Fin 3, ∑ j : Fin 3,
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W))) +
                  (∑ i : Fin 3, ∑ j : Fin 3,
                    identityInvMetric (Idx := Fin 3) i j *
                      T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W)))
                  = ∑ i : Fin 3, ∑ j : Fin 3,
                      (identityInvMetric (Idx := Fin 3) i j *
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 X Y Z W)) +
                        identityInvMetric (Idx := Fin 3) i j *
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Y Z X W)) +
                        identityInvMetric (Idx := Fin 3) i j *
                          T (metricTraceInput (I := I) (basis i) (basis j) (vec4 Z X Y W))) := by
                    rw [← Finset.sum_add_distrib]
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [← Finset.sum_add_distrib]
                    rw [← Finset.sum_add_distrib]
              _ = 0 := by
                    apply Finset.sum_eq_zero
                    intro i _
                    apply Finset.sum_eq_zero
                    intro j _
                    exact hper2 i j

omit [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
private theorem fiberRegion_roughLapRm04_component_eq
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    {t : ℝ} (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hOrth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (a b c d : Fin 3) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
        (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)) =
      tensor04StandardAt (I := I) (M := M)
        (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
          (nablaKRm04Field (I := I) S t 2 x))
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
  have hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin 3)) := by
    exact Tensor0SBundle.metricInverseInBasis_identity_of_orthonormal (I := I)
      (S.base.metric t) basis (by
        intro i j
        simpa [delta3] using hOrth i j)
  rw [← metricTrace0S2InBasis_eq_metricTrace (I := I) (S.base.metric t) basis
    (identityInvMetric (Idx := Fin 3)) hinv (nablaKRm04Field (I := I) S t 2 x)
    (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))]
  rw [← metricTrace0S2TensorInBasis_apply]
  rfl

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
private theorem pulledRmComp_pullback
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) :
    UhlenbeckPullbackRmComponents iota
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
      (pulledRmComp S basisAt iota) := by
  intro t x a b c d
  change tensor04StandardAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota t x)
      (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
    uhlenbeckPullbackRmInFrame iota
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) t x a b c d
  convert uhlenbeckPulledRm04At_apply_basis
    (I := I) (M := M) S basisAt iota t x a b c d using 1 ; rfl

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [I.Boundaryless] in
private lemma fiberRegion_pulledComponent_continuousOn_time
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiotaCont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T))
    (x : M) (a b c d : Fin 3) :
    ContinuousOn (fun s : ℝ => tensor04StandardAt (I := I) (M := M)
        (uhlenbeckPulledRm04At S basisAt iota s x)
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
      (Set.Icc 0 T) := by
  classical
  have hiota_comp : ∀ a k : Fin 3, ContinuousOn (fun s : ℝ => iota s x a k) (Set.Icc 0 T) := by
    intro a k
    have h1 : ContinuousOn (fun s : ℝ => iota s x a) (Set.Icc 0 T) := (continuousOn_pi.mp (hiotaCont x)) a
    exact (continuousOn_pi.mp h1) k
  have hrm04_comp : ∀ v w y z : TangentSpace I x,
      ContinuousOn (fun s : ℝ => tensor04StandardAt (I := I) (M := M) (S.base.rm04 s x) v w y z)
        (Set.Icc 0 T) := by
    intro v w y z
    rw [continuousOn_iff_continuous_domRestrict]
    let P : Set ℝ := Set.Icc 0 T
    have hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 P
        (fun t x => S.base.rm04 t x) := by
      exact tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.rm04Cont (by intro s hs; exact hs)
    have heval := tensor0SFamilyContinuousOnSet.eval_continuous (I := I) (M := M) (s := 4)
      (K := P) (A := fun t x => S.base.rm04 t x) hA
      (P := {q : ℝ // q ∈ P}) (τ := fun p : {q : ℝ // q ∈ P} => p.1)
      (b := fun p : {q : ℝ // q ∈ P} => x)
      continuous_subtype_val (fun p : {q : ℝ // q ∈ P} => p.2) continuous_const
      (v := fun i : Fin 4 => fun p : {q : ℝ // q ∈ P} =>
        if i = 0 then v else if i = 1 then w else if i = 2 then y else z)
      (by
        intro i
        fin_cases i
        · exact continuous_const
        · exact continuous_const
        · exact continuous_const
        · exact continuous_const)
    have hmain : Continuous (fun p : {q : ℝ // q ∈ P} =>
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 p.1 x) v w y z) := by
      refine heval.congr (fun p => ?_)
      rfl
    change Continuous (fun p : {q : ℝ // q ∈ Set.Icc 0 T} =>
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 p.1 x) v w y z)
    simpa only [P] using hmain
  have hpoly : ∀ s : ℝ,
      tensor04StandardAt (I := I) (M := M) (uhlenbeckPulledRm04At S basisAt iota s x)
          (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          iota s x a i * iota s x b j * iota s x c k * iota s x d l *
            tensor04StandardAt (I := I) (M := M) (S.base.rm04 s x)
              (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l) := by
    intro s
    have h := uhlenbeckPulledRm04At_apply_basis (I := I) (M := M) S basisAt iota s x a b c d
    convert h using 1 ; rfl
  rw [continuousOn_congr (fun s hs => hpoly s)]
  refine continuousOn_finsetSum Finset.univ ?_
  intro i _
  refine continuousOn_finsetSum Finset.univ ?_
  intro j _
  refine continuousOn_finsetSum Finset.univ ?_
  intro k _
  refine continuousOn_finsetSum Finset.univ ?_
  intro l _
  have hmul :=
    ((((hiota_comp a i).mul (hiota_comp b j)).mul (hiota_comp c k)).mul (hiota_comp d l)).mul
      (hrm04_comp (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))
  rw [show (fun s ↦ iota s x a i * iota s x b j * iota s x c k * iota s x d l *
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 s x)
        (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l)) =
    (fun s ↦ (((iota s x a i * iota s x b j) * iota s x c k) * iota s x d l) *
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 s x)
        (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l)) by rfl]
  exact hmul

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_pullbackTensorAt_apply
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (A : Tensor04At (I := I) (M := M) x) (X Y Z W : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M) (uhlenbeckPullbackTensorAt basisAt iota t x A) X Y Z W =
      tensor04StandardAt (I := I) (M := M) A
        (uhlenbeckEndomorphismAt (basisAt x) iota t X)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Y)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Z)
        (uhlenbeckEndomorphismAt (basisAt x) iota t W) := by
  change (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 =>
        uhlenbeckEndomorphismAt (basisAt x) iota t (vec4 X Y Z W i)) =
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (vec4 (uhlenbeckEndomorphismAt (basisAt x) iota t X)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Y)
        (uhlenbeckEndomorphismAt (basisAt x) iota t Z)
        (uhlenbeckEndomorphismAt (basisAt x) iota t W))
  congr 1
  funext i
  fin_cases i <;> simp [vec4]


omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_sum4_factor (A B C D : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, A i * B j * C k * D l) =
      (∑ i : Fin 3, A i) * (∑ j : Fin 3, B j) * (∑ k : Fin 3, C k) * (∑ l : Fin 3, D l) := by
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, A i * B j * C k * D l)
        = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, A i * B j * C k * (∑ l : Fin 3, D l) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (A i * B j) * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [show (∑ k : Fin 3, A i * B j * C k * (∑ l : Fin 3, D l)) =
              ∑ k : Fin 3, (A i * B j) * (C k * (∑ l : Fin 3, D l)) by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_assoc]]
          rw [← Finset.mul_sum]
    _ = ∑ i : Fin 3, A i * (∑ j : Fin 3, B j * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (∑ j : Fin 3, (A i * B j) * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l))) =
              ∑ j : Fin 3, A i * (B j * (∑ k : Fin 3, C k * (∑ l : Fin 3, D l))) by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← mul_assoc]]
          rw [← Finset.mul_sum]
    _ = (∑ i : Fin 3, A i) * ((∑ j : Fin 3, B j) * ((∑ k : Fin 3, C k) * (∑ l : Fin 3, D l))) := by
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
    _ = (∑ i : Fin 3, A i) * (∑ j : Fin 3, B j) * (∑ k : Fin 3, C k) * (∑ l : Fin 3, D l) := by
          rw [mul_assoc, mul_assoc]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_sum5_swap
    (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → (Fin 4 → Fin 3) → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3, F i j k l I0) =
      ∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 := by
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3, F i j k l I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ l : Fin 3, F i j k l I0 by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ l : Fin 3, F i j k l I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0) =
      ∑ i : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin 3, ∑ I0 : Fin 4 → Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0) =
      ∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F i j k l I0 by
    rw [Finset.sum_comm]]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_compU_mem_algebraicCurvatureTensorSubmodule
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (A : Tensor04At (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    uhlenbeckPullbackTensorAt basisAt iota t x A ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  rw [mem_algebraicCurvatureTensorSubmodule]
  have hform : IsAlgCurvForm (tensor04StandardAt (I := I) (M := M) A) :=
    mem_algebraicCurvatureTensorSubmodule.mp hA
  change IsAlgCurvForm (fun X Y Z W =>
    tensor04StandardAt (uhlenbeckPullbackTensorAt basisAt iota t x A) X Y Z W)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A (x₁ + x₂) y z w,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A x₁ y z w,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A x₂ y z w]
    rw [show uhlenbeckEndomorphismAt (basisAt x) iota t (x₁ + x₂) =
        uhlenbeckEndomorphismAt (basisAt x) iota t x₁ +
          uhlenbeckEndomorphismAt (basisAt x) iota t x₂ from by simp]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A (a • u) y z w,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u y z w]
    rw [show uhlenbeckEndomorphismAt (basisAt x) iota t (a • u) =
        a • uhlenbeckEndomorphismAt (basisAt x) iota t u from by simp]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v y z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A v u y z]
    exact hform.anti_first _ _ _ _
  · intro u v y z
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v y z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v z y]
    exact hform.anti_last _ _ _ _
  · intro u v y z
    rw [fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A u v y z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A v y u z,
      fiberRegion_pullbackTensorAt_apply (I := I) (M := M) basisAt iota t x A y u v z]
    exact hform.bianchi _ _ _ _

omit [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem fiberRegion_pulledTensor_scalarization_eq
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (x : M)
    (horth : OrthonormalBasisAt (I := I) g x (basisAt x))
    (A : Tensor04At (I := I) (M := M) x)
    (hAlg : uhlenbeckPullbackTensorAt basisAt iota t x A ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ν : Tensor04At (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (uhlenbeckPullbackTensorAt basisAt iota t x A) ν =
      4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix
        (fun t' x' a b c d => tensor04StandardAt (I := I) (M := M)
          (uhlenbeckPullbackTensorAt basisAt iota t' x' A)
          (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x)
        (regionSupportVector g basisAt x ν) := by
  have hmat : uhlenbeckCurvatureOperatorMatrix
        (fun t' x' a b c d => tensor04StandardAt (I := I) (M := M)
          (uhlenbeckPullbackTensorAt basisAt iota t' x' A)
          (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x =
      matrixToEuclidean (curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨uhlenbeckPullbackTensorAt basisAt iota t x A, hAlg⟩) := by
    have hmain := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
      (I := I) (M := M) (x := x) (basis := basisAt x)
      (A := ⟨uhlenbeckPullbackTensorAt basisAt iota t x A, hAlg⟩)
      (pulledRm := fun t' x' a b c d => tensor04StandardAt (I := I) (M := M)
        (uhlenbeckPullbackTensorAt basisAt iota t' x' A)
        (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d))
      (t := t)
      (by intro a b c d; rfl)
    rw [← hmain]
    unfold matrixToEuclidean uhlenbeckCurvatureOperatorMatrixAsMatrix uhlenbeckCurvatureOperatorMatrix
    rfl
  have hmain := inner0S_eq_four_mul_inner_regionProjMatrix (I := I) g x (basisAt x) horth hAlg ν
  rw [← hmat] at hmain
  rw [real_inner_comm] at hmain
  simpa [regionSupportVector] using hmain

omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem fiberRegion_pulledRmComp_eq_rm
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    ∀ a b c d : Fin 3,
      pulledRmComp S basisAt iota t x a b c d =
        rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I)
          (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x i)
          (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x j))) a b c d := by
  intro a b c d
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have hmovingOrth : ∀ i j : Fin 3, (S.base.metric t).inner x (moving i) (moving j) = kd i j := by
    intro i j
    dsimp [moving]
    exact uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht i j
  calc
    pulledRmComp S basisAt iota t x a b c d
        = tensor04StandardAt (uhlenbeckPulledRm04At S basisAt iota t x)
            (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := rfl
    _ = tensor04StandardAt (S.base.rm04 t x) (moving a) (moving b) (moving c) (moving d) := by
          rw [uhlenbeckPulledRm04At_apply]
          simp [moving, uhlenbeckMovingBasis_apply]
    _ = S.base.rm04 t x (vec4 (I := I) (moving a) (moving b) (moving c) (moving d)) := rfl
    _ = rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))) a b c d := by
          have h := rm04Comp_ortho_eq_rm (I := I) S t (hdim x) moving hmovingOrth (slots4 a b c d)
          have hslots : (fun p : Fin 4 =>
              moving (if p = 0 then a else if p = 1 then b else if p = 2 then c else d)) =
              vec4 (I := I) (moving a) (moving b) (moving c) (moving d) := by
            funext p
            fin_cases p <;> rfl
          rw [← hslots]
          exact h

omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem fiberRegion_pulledBTensor_eq_bTensorDown
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) (a b c d : Fin 3) :
    uhlenbeckPullbackRmInFrame iota
        (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
        t x a b c d =
      bTensorDown (fun a' b' c' d' => pulledRmComp S basisAt iota t x a' b' c' d') a b c d := by
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  let e : Fin 3 → TangentSpace I x := fun a => basisAt x a
  let P : Fin 3 → Fin 3 → ℝ := fun j i => moving.repr (basisAt x i) j
  have hP : ∀ i j : Fin 3, P j i = moving.repr (basisAt x i) j := by
    intro i j
    rfl
  have hmovingOrth : ∀ i j : Fin 3, (S.base.metric t).inner x (moving i) (moving j) = kd i j := by
    intro i j
    dsimp [moving]
    exact uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht i j
  have hginv : ∀ i j : Fin 3,
      (∑ k : Fin 3, solutionInverseMetricComponents S basisAt t x i k *
        (S.base.metric t).inner x (basisAt x k) (basisAt x j)) = kd i j := by
    intro i j
    have h := solutionInverseMetricComponents_mul_metric (I := I) (M := M) S basisAt t x i j
    simpa [metricCompInFrame, kd] using h
  have hiotaP : ∀ u v : Fin 3, (∑ i : Fin 3, iota t x u i * P v i) = kd u v := by
    intro u v
    calc
      (∑ i : Fin 3, iota t x u i * P v i)
          = moving.repr (∑ i : Fin 3, iota t x u i • basisAt x i) v := by
            rw [map_sum]
            simp [P, smul_eq_mul]
      _ = moving.repr (moving u) v := by
            congr 1
            rw [uhlenbeckMovingBasis_apply, uhlenbeckEndomorphism_apply_basis]
      _ = kd u v := by
            rw [moving.repr_self u, Finsupp.single_apply]
            simp [kd]
  let Rf : Fin 3 → Fin 3 → ℝ := fun i j => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))
  have hBpull : uhlenbeckPullbackRmInFrame iota
        (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
        t x a b c d =
      Bt Rf a b c d := by
    calc
      uhlenbeckPullbackRmInFrame iota
          (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
          t x a b c d
          = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                  (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
                  t x i j k l := rfl
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                (∑ I0 : Fin 4 → Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            have h := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S t (hdim x)
              (fun a => basisAt x a) moving P (solutionInverseMetricComponents S basisAt)
              hP hmovingOrth hginv i j k l
            have hval : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                  (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
                  t x i j k l =
                (∑ I0 : Fin 4 → Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) := by
              calc
                uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                    (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
                    t x i j k l
                    = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
                        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a))
                        t x i j k l := by
                      unfold uhlenbeckBTensorInFrame
                      refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ =>
                        Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
                      simp [solutionRm04CompInFrame, rm04Comp, e]
                _ = (∑ I0 : Fin 4 → Fin 3,
                      (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) := by
                      simpa [Rf] using h
            rw [hval]
      _ = ∑ I0 : Fin 4 → Fin 3,
              Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) := by
            have hstep1 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∑ I0 : Fin 4 → Fin 3,
                      (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))) =
                ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun I0 _ => ?_
              ring
            have hstep2 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ I0 : Fin 4 → Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) =
                ∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) := by
              exact fiberRegion_sum5_swap (fun i j k l I0 =>
                iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                  (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))
            have hstep3 : (∑ I0 : Fin 4 → Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) =
                ∑ I0 : Fin 4 → Fin 3,
                  Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                        (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) := by
              refine Finset.sum_congr rfl fun I0 _ => ?_
              rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                      (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3)) =
                  Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                        (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) by
                calc
                  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                        (∏ p : Fin 4, P (I0 p) (slots4 i j k l p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))
                      = Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                          (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                            iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                              (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) := by
                        simp only [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
                        ring]
            exact (hstep1.trans hstep2).trans hstep3
      _ = ∑ I0 : Fin 4 → Fin 3,
              Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                ((∑ i : Fin 3, iota t x a i * P (I0 0) i) *
                  (∑ j : Fin 3, iota t x b j * P (I0 1) j) *
                  (∑ k : Fin 3, iota t x c k * P (I0 2) k) *
                  (∑ l : Fin 3, iota t x d l * P (I0 3) l)) := by
            refine Finset.sum_congr rfl fun I0 _ => ?_
            rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                  iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                    (∏ p : Fin 4, P (I0 p) (slots4 i j k l p))) =
                (∑ i : Fin 3, iota t x a i * P (I0 0) i) *
                  (∑ j : Fin 3, iota t x b j * P (I0 1) j) *
                  (∑ k : Fin 3, iota t x c k * P (I0 2) k) *
                  (∑ l : Fin 3, iota t x d l * P (I0 3) l) by
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
                      (P (I0 0) i * P (I0 1) j * P (I0 2) k * P (I0 3) l)) =
                  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                    (iota t x a i * P (I0 0) i) * (iota t x b j * P (I0 1) j) *
                      (iota t x c k * P (I0 2) k) * (iota t x d l * P (I0 3) l)) by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                  Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
                ring]
              exact fiberRegion_sum4_factor (fun i => iota t x a i * P (I0 0) i)
                (fun j => iota t x b j * P (I0 1) j)
                (fun k => iota t x c k * P (I0 2) k)
                (fun l => iota t x d l * P (I0 3) l)]
      _ = ∑ I0 : Fin 4 → Fin 3,
              Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                (kd a (I0 0) * kd b (I0 1) * kd c (I0 2) * kd d (I0 3)) := by
            refine Finset.sum_congr rfl fun I0 _ => ?_
            rw [hiotaP a (I0 0), hiotaP b (I0 1), hiotaP c (I0 2), hiotaP d (I0 3)]
      _ = Bt Rf a b c d := by
            rw [Finset.sum_eq_single (slots4 a b c d)]
            · simp [slots4, kd]
            · intro I0 _ hI0
              have hne : ∃ p : Fin 4, I0 p ≠ slots4 a b c d p := by
                by_contra h
                apply hI0
                funext p
                by_contra hne
                exact h ⟨p, hne⟩
              rcases hne with ⟨p, hp⟩
              have hzero : kd (slots4 a b c d p) (I0 p) = 0 := by
                rw [kd, if_neg]
                exact hp.symm
              calc
                Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                    (kd a (I0 0) * kd b (I0 1) * kd c (I0 2) * kd d (I0 3))
                    = Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) *
                        (∏ q : Fin 4, kd (slots4 a b c d q) (I0 q)) := by
                      simp [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                _ = Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) * 0 := by
                      rw [Finset.prod_eq_zero (f := fun q : Fin 4 => kd (slots4 a b c d q) (I0 q)) (by simp) hzero]
                _ = 0 := by ring
            · intro h
              exact absurd (Finset.mem_univ (slots4 a b c d)) h
  calc
    uhlenbeckPullbackRmInFrame iota
        (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
        t x a b c d
        = Bt Rf a b c d := hBpull
    _ = bTensorDown (fun a' b' c' d' => pulledRmComp S basisAt iota t x a' b' c' d') a b c d := by
          have hrm : ∀ u v w z : Fin 3,
              pulledRmComp S basisAt iota t x u v w z =
                rm Rf u v w z := by
            intro u v w z
            have h := fiberRegion_pulledRmComp_eq_rm (I := I) (M := M) hT S basisAt iota hiota0 hgram
              hdim horth0 ht x u v w z
            simpa [Rf, moving] using h
          unfold Bt bTensorDown
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
          change rm Rf a e b f * rm Rf c e d f =
            pulledRmComp S basisAt iota t x a e b f * pulledRmComp S basisAt iota t x c e d f
          rw [hrm a e b f, hrm c e d f]

omit [I.Boundaryless] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
private theorem fiberRegion_reaction_eq_reactionState
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    uhlenbeckCurvatureOperatorReaction
        (fun t' x' a b c d => uhlenbeckPullbackRmInFrame iota
          (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
          t' x' a b c d)
        t x =
      hamiltonIveyMatrixReactionEuclidean
        (uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x) := by
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  let Rf : Fin 3 → Fin 3 → ℝ := fun i j => S.ricciAt t x (vec2 (I := I) (moving i) (moving j))
  have hR : ∀ i j : Fin 3, Rf i j = Rf j i := by
    intro i j
    unfold Rf
    exact ricciAt_symm (I := I) (M := M) S t x (moving i) (moving j)
  have hrm : ∀ a b c d : Fin 3,
      pulledRmComp S basisAt iota t x a b c d = rm Rf a b c d := by
    intro a b c d
    have h := fiberRegion_pulledRmComp_eq_rm (I := I) (M := M) hT S basisAt iota hiota0 hgram
      hdim horth0 ht x a b c d
    simpa [Rf, moving] using h
  have hB : ∀ a b c d : Fin 3,
      uhlenbeckPullbackRmInFrame iota
          (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
          t x a b c d =
        bTensorDown (fun a' b' c' d' => pulledRmComp S basisAt iota t x a' b' c' d') a b c d := by
    intro a b c d
    exact fiberRegion_pulledBTensor_eq_bTensorDown (I := I) (M := M) hT S basisAt iota hiota0 hgram
      hdim horth0 ht x a b c d
  exact uhlenbeckReaction_eq_reactionState_at (pulledRm := pulledRmComp S basisAt iota)
    (B := fun t' x' a b c d => uhlenbeckPullbackRmInFrame iota
      (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
      t' x' a b c d)
    t x Rf hR hrm hB

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma fiberRegion_continuousMultilinearMap_update_sum
    {ι : Type*} [Fintype ι] {x : M}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
    (m : Fin 4 → TangentSpace I x) (i : Fin 4)
    (c : ι → ℝ) (v : ι → TangentSpace I x) :
    f (Function.update m i (∑ p : ι, c p • v p)) =
      ∑ p : ι, c p * f (Function.update m i (v p)) := by
  classical
  have hsum : (∑ p : ι, c p • v p) = ∑ p ∈ Finset.univ, c p • v p := by simp
  have hsum2 : (∑ p : ι, c p * f (Function.update m i (v p))) =
      ∑ p ∈ Finset.univ, c p * f (Function.update m i (v p)) := by
    simp
  rw [hsum, hsum2]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [← zero_smul ℝ (0 : TangentSpace I x)]
      rw [ContinuousMultilinearMap.map_update_smul f m i (0 : ℝ) (0 : TangentSpace I x)]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [ContinuousMultilinearMap.map_update_add f m i (c a • v a) (∑ p ∈ s, c p • v p)]
      rw [ContinuousMultilinearMap.map_update_smul f m i (c a) (v a)]
      rw [ih]
      simp [Finset.sum_insert ha, smul_eq_mul]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma fiberRegion_pulledTensor_apply_basis
    {x : M} (Q : Tensor04At (I := I) (M := M) x)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : ℝ) (a b c d : Fin 3) :
    tensor04StandardAt (I := I) (M := M)
        (Q.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) =
      uhlenbeckPullbackRmInFrame iota
        (fun _s x a b c d => tensor04StandardAt (I := I) (M := M) Q
          (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
        t x a b c d := by
  classical
  change (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 =>
        uhlenbeckEndomorphismAt (basisAt x) iota t
          (vec4 (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) i)) =
    uhlenbeckPullbackRmInFrame iota
      (fun s x a b c d => tensor04StandardAt (I := I) (M := M) Q
        (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
      t x a b c d
  simp only [uhlenbeckPullbackRmInFrame, tensor04StandardAt_apply]
  let g : Fin 4 → TangentSpace I x := fun _ => 0
  have harg : (fun i : Fin 4 =>
      uhlenbeckEndomorphismAt (basisAt x) iota t
        (vec4 (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) i)) =
      Function.update (Function.update (Function.update (Function.update g 3
        (∑ l : Fin 3, iota t x d l • basisAt x l)) 2 (∑ k : Fin 3, iota t x c k • basisAt x k))
        1 (∑ j : Fin 3, iota t x b j • basisAt x j)) 0 (∑ i : Fin 3, iota t x a i • basisAt x i) := by
    funext i
    fin_cases i <;> simp [g, vec4, uhlenbeckEndomorphism_apply_basis]
  rw [harg]
  let m0 : Fin 4 → TangentSpace I x :=
    Function.update (Function.update (Function.update g 3
      (∑ l : Fin 3, iota t x d l • basisAt x l)) 2 (∑ k : Fin 3, iota t x c k • basisAt x k))
      1 (∑ j : Fin 3, iota t x b j • basisAt x j)
  have h0 : (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (Function.update m0 0 (∑ p : Fin 3, iota t x a p • basisAt x p)) =
      ∑ p : Fin 3, iota t x a p * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update m0 0 (basisAt x p)) := by
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q) m0 (0 : Fin 4)
      (fun p : Fin 3 => iota t x a p) (fun p : Fin 3 => basisAt x p)
    with_unfolding_all exact h
  rw [h0]
  have h1 : ∀ p : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update m0 0 (basisAt x p)) =
      ∑ j : Fin 3, iota t x b j * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) := by
    intro p
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q)
      (Function.update m0 0 (basisAt x p)) (1 : Fin 4)
      (fun j : Fin 3 => iota t x b j) (fun j : Fin 3 => basisAt x j)
    have hself : (Function.update (Function.update m0 0 (basisAt x p)) 1
        (∑ j : Fin 3, iota t x b j • basisAt x j)) = Function.update m0 0 (basisAt x p) := by
      funext n
      by_cases hn : n = 1
      · subst hn
        simp [m0]
      · simp [hn]
    simp only [hself] at h
    with_unfolding_all exact h
  have h2 : ∀ p q : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) =
      ∑ k : Fin 3, iota t x c k * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
          (basisAt x k)) := by
    intro p q
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q)
      (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) (2 : Fin 4)
      (fun k : Fin 3 => iota t x c k) (fun k : Fin 3 => basisAt x k)
    have hself : (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2
        (∑ k : Fin 3, iota t x c k • basisAt x k)) =
        Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q) := by
      funext n
      by_cases hn : n = 2
      · subst hn
        simp [m0]
      · simp [hn]
    simp only [hself] at h
    with_unfolding_all exact h
  have h3 : ∀ p q r : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) =
      ∑ l : Fin 3, iota t x d l * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) := by
    intro p q r
    have h := fiberRegion_continuousMultilinearMap_update_sum (f := Q)
      (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
        (basisAt x q)) 2 (basisAt x r)) (3 : Fin 4)
      (fun l : Fin 3 => iota t x d l) (fun l : Fin 3 => basisAt x l)
    have hself : (Function.update (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
          (basisAt x q)) 2 (basisAt x r)) 3
        (∑ l : Fin 3, iota t x d l • basisAt x l)) =
        Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x q)) 2 (basisAt x r) := by
      funext n
      by_cases hn : n = 3
      · subst hn
        simp [m0]
      · simp [hn]
    simp only [hself] at h
    with_unfolding_all exact h
  have hbase : ∀ p q r l : Fin 3,
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update (Function.update (Function.update (Function.update m0 0
          (basisAt x p)) 1 (basisAt x q)) 2 (basisAt x r)) 3 (basisAt x l)) =
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (vec4 (basisAt x p) (basisAt x q) (basisAt x r) (basisAt x l)) := by
    intro p q r l
    congr 1
    funext n
    fin_cases n <;> simp [m0, vec4]
  calc
    ∑ p : Fin 3, iota t x a p * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
        (Function.update m0 0 (basisAt x p))
        = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j *
            (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (Function.update (Function.update m0 0 (basisAt x p)) 1 (basisAt x j))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [h1 p]
    _ = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j * (∑ k : Fin 3, iota t x c k *
            (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (Function.update (Function.update (Function.update m0 0 (basisAt x p)) 1
                (basisAt x j)) 2 (basisAt x k)))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [h2 p j]
    _ = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j * (∑ k : Fin 3, iota t x c k * (∑ l : Fin 3,
            iota t x d l * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (Function.update (Function.update (Function.update
                (Function.update m0 0 (basisAt x p)) 1 (basisAt x j)) 2 (basisAt x k)) 3 (basisAt x l))))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [h3 p j k]
    _ = ∑ p : Fin 3, iota t x a p * (∑ j : Fin 3, iota t x b j * (∑ k : Fin 3, iota t x c k * (∑ l : Fin 3,
            iota t x d l * (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (vec4 (basisAt x p) (basisAt x j) (basisAt x k) (basisAt x l))))) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro j hj
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro k hk
          apply congrArg
          refine Finset.sum_congr rfl ?_
          intro l hl
          rw [hbase p j k l]
    _ = ∑ p : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          iota t x a p * iota t x b j * iota t x c k * iota t x d l *
            (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
              (vec4 (basisAt x p) (basisAt x j) (basisAt x k) (basisAt x l)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

omit [SigmaCompactSpace M] in
private theorem fiber_region_heat_reaction_on
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (hiotaCont : ∀ x : M, ContinuousOn (fun t : ℝ => iota t x) (Set.Icc 0 T))
    (hiotaODE : BundleIsomorphismODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a))) :
    (by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
        fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun x => inferInstance
      exact IsBundleHeatReactionOn
        (V := fun x : M => Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (RealTimeInterval.closed 0 T hT.le) (flowG (I := I) S)
        (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
        (uhlenbeckPulledRm04At S basisAt iota)) := by
  classical
  let : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.Core.toNormedAddCommGroup ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  let : ∀ x : M, InnerProductSpace ℝ (Tensor04At (I := I) (M := M) x) :=
    fun x => @InnerProductSpace.ofCore ℝ (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  let : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
    fun x => inferInstance
  classical
  let D : RealTimeInterval := RealTimeInterval.closed 0 T hT.le
  let u : Real → (x : M) → Tensor04At (I := I) (M := M) x := uhlenbeckPulledRm04At S basisAt iota
  let A : Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    fun t x => uhlenbeckCurvatureOperatorMatrix (pulledRmComp S basisAt iota) t x
  let w (x : M) (ν : Tensor04At (I := I) (M := M) x) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    regionSupportVector (I := I) (S.base.metric 0) basisAt x ν
  have hAlg : ∀ (t : ℝ) (x : M), u t x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
    intro t x
    exact uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) S basisAt iota t x
  have hscalar_eq : ∀ (s : ℝ) (x : M) (ν : Tensor04At (I := I) (M := M) x),
      inner ℝ (u s x) ν = 4 * inner ℝ (A s x) (w x ν) := by
    intro s x ν
    rw [tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x (u s x) ν]
    have hmain := pulledScalarization_eq (I := I) (S.base.metric 0) S basisAt iota s x (horth0 x)
      (hAlg s x) ν
    simpa [A, w, u] using hmain
  let roughLapRm04 : FourComp M (Fin 3) := fun t x a b c d =>
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
      (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d))
  let Borig : FourComp M (Fin 3) :=
    uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
  have hrm := solutionRm04CompInFrame_fixed_frame_evolution T hT S hS hdim basisAt
  let roughLapD : FourComp M (Fin 3) := fun t x a b c d =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l * roughLapRm04 t x i j k l
  let Bpull : FourComp M (Fin 3) := fun t x a b c d =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l * Borig t x i j k l
  have hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD := by
    intro t x a b c d
    rfl
  have hB : UhlenbeckPullbackBComponents iota Borig Bpull := by
    intro t x a b c d
    rfl
  have hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D)
      (pulledRmComp S basisAt iota) roughLapD Bpull := by
    exact uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow (D := D) iota
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
      (pulledRmComp S basisAt iota) roughLapRm04 roughLapD Borig Bpull
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a))
      hiotaODE (pulledRmComp_pullback (I := I) (M := M) hT S basisAt iota) hlap hB hrm
  have hU_deriv : ∀ (t : ℝ) (ht : t ∈ D.regular) (x : M) (a b c d : Fin 3),
      HasDerivAt (fun s : ℝ => pulledRmComp S basisAt iota s x a b c d)
        (uhlenbeckCurvatureEvolutionRHSInFrame roughLapD Bpull t x a b c d) t := by
    intro t ht x a b c d
    have h := hU ⟨t, ht⟩ x a b c d
    exact h.hasDerivAt (D.regular_mem_nhds ht)
  refine ⟨?scalarTimeContinuousWithinAt, ?scalarSliceSmooth, ?equation⟩
  · intro ν t ht x hflat
    have hAcomp : ∀ ij : Fin 3 × Fin 3,
        ContinuousOn (fun s : ℝ => (A s x).ofLp ij) (Set.Icc 0 T) := by
      intro ij
      have h := fiberRegion_pulledComponent_continuousOn_time (I := I) (M := M) hT S hS basisAt iota
        hiotaCont x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2 (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1
      change ContinuousOn
        (fun s : ℝ ↦ pulledRmComp S basisAt iota s x
          (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1) (Set.Icc 0 T)
      exact h
    have hsum : ContinuousOn (fun s : ℝ => ∑ ij : Fin 3 × Fin 3,
        (A s x).ofLp ij * (w x (ν x)).ofLp ij) (Set.Icc 0 T) := by
      refine continuousOn_finsetSum Finset.univ ?_
      intro ij _
      exact (hAcomp ij).mul continuousOn_const
    have hinner_cont : ContinuousOn (fun s : ℝ => inner ℝ (A s x) (w x (ν x))) (Set.Icc 0 T) := by
      have hEq : (fun s : ℝ => inner ℝ (A s x) (w x (ν x))) =
          fun s : ℝ => ∑ ij : Fin 3 × Fin 3, (A s x).ofLp ij * (w x (ν x)).ofLp ij := by
        funext s
        rw [PiLp.inner_apply]
        simp [inner, mul_comm]
      simpa [hEq] using hsum
    have hmain : ContinuousOn (fun s : ℝ => bundleInnerScalarization u ν s x) (Set.Icc 0 T) := by
      have hfun : (fun s : ℝ => bundleInnerScalarization u ν s x) =
          fun s : ℝ => 4 * inner ℝ (A s x) (w x (ν x)) := by
        funext s
        unfold bundleInnerScalarization
        rw [hscalar_eq s x (ν x)]
      rw [hfun]
      exact hinner_cont.const_mul 4
    change ContinuousWithinAt (fun s : ℝ ↦ bundleInnerScalarization u ν s x)
      (Set.Icc 0 T) t
    exact hmain.continuousWithinAt ht
  · intro ν t ht x hflat
    rcases hflat with ⟨η, nablaη, nabla2η, basis, hOrth, heqν, hη, h2η, hflat1, hflat2⟩
    have hlocal : (fun y : M => bundleInnerScalarization u ν t y) =ᶠ[𝓝 x]
        fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y) := by
      filter_upwards [heqν] with y hy
      unfold bundleInnerScalarization
      rw [tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) y (u t y) (ν y)]
      have hiso := fiberInner_compUhlenbeck_isometry_tensor (I := I) (M := M) hT S basisAt iota hiota0 hgram
        horth0 ht y (S.base.rm04 t y) (η y)
      have hu : u t y = (S.base.rm04 t y).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt y) iota t) := rfl
      rw [hu, hy]
      simpa [uhlenbeckPullbackTensorAt] using hiso
    have hsm : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y)) x :=
      (inner0S_contMDiff (I := I) (S.base.metric t) (S.base.rm04 t) η).contMDiffAt
    exact hsm.congr_of_eventuallyEq hlocal
  · intro ν t ht x hflat
    rcases hflat with ⟨η, nablaη, nabla2η, basis, hOrth, heqν, hη, h2η, hflat1, hflat2⟩
    let wv : EuclideanSpace ℝ (Fin 3 × Fin 3) := w x (ν x)
    have hscalar_fun : (fun s : ℝ => bundleInnerScalarization u ν s x) =
        fun s : ℝ => 4 * inner ℝ (A s x) wv := by
      funext s
      unfold bundleInnerScalarization
      rw [tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x (u s x) (ν x)]
      have hmain := pulledScalarization_eq (I := I) (S.base.metric 0) S basisAt iota s x (horth0 x)
        (hAlg s x) (ν x)
      simpa [A, w, wv, u] using hmain
    have hAderiv_comp : ∀ ij : Fin 3 × Fin 3,
        HasDerivAt (fun s : ℝ => (A s x).ofLp ij)
          ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
            (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) t := by
      intro ij
      let a : Fin 3 := (bivectorIndex3 ij.1).1
      let b : Fin 3 := (bivectorIndex3 ij.1).2
      let c : Fin 3 := (bivectorIndex3 ij.2).2
      let d : Fin 3 := (bivectorIndex3 ij.2).1
      have hd := hU_deriv t ht x a b c d
      have hA : (fun s : ℝ => (A s x).ofLp ij) = fun s : ℝ => pulledRmComp S basisAt iota s x a b c d := by
        funext s
        simp [A, uhlenbeckCurvatureOperatorMatrix, a, b, c, d]
      have hrhs : uhlenbeckCurvatureEvolutionRHSInFrame roughLapD Bpull t x a b c d =
          (uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
            (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij := by
        simp [uhlenbeckCurvatureEvolutionRHSInFrame, uhlenbeckCurvatureOperatorMatrix,
          uhlenbeckCurvatureOperatorReaction, a, b, c, d]
        ring
      rw [hA]
      exact hd.congr_deriv hrhs
    have hscalar_deriv : HasDerivAt (fun s : ℝ => 4 * inner ℝ (A s x) wv)
        (4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
            uhlenbeckCurvatureOperatorReaction Bpull t x) wv) t := by
      have hinner : HasDerivAt (fun s : ℝ => inner ℝ (A s x) wv)
          (inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
            uhlenbeckCurvatureOperatorReaction Bpull t x) wv) t := by
        have hsum : HasDerivAt (fun s : ℝ => ∑ ij : Fin 3 × Fin 3, (A s x).ofLp ij * wv.ofLp ij)
            (∑ ij : Fin 3 × Fin 3,
              ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
                (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) * wv.ofLp ij) t := by
          have hraw : HasDerivAt (fun s : ℝ => ∑ ij ∈ (Finset.univ : Finset (Fin 3 × Fin 3)),
                (A s x).ofLp ij * wv.ofLp ij)
              (∑ ij ∈ (Finset.univ : Finset (Fin 3 × Fin 3)),
                ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
                  (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) * wv.ofLp ij) t := by
            exact HasDerivAt.sum (u := Finset.univ) (fun ij hij => (hAderiv_comp ij).mul_const (wv.ofLp ij))
          simpa using hraw
        have hinner_eq : (fun s : ℝ => inner ℝ (A s x) wv) =
            fun s : ℝ => ∑ ij : Fin 3 × Fin 3, (A s x).ofLp ij * wv.ofLp ij := by
          funext s
          rw [PiLp.inner_apply]
          simp [inner, mul_comm]
        have hderiv_eq : (∑ ij : Fin 3 × Fin 3,
              ((uhlenbeckCurvatureOperatorMatrix roughLapD t x).ofLp ij +
                (uhlenbeckCurvatureOperatorReaction Bpull t x).ofLp ij) * wv.ofLp ij) =
            inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
              uhlenbeckCurvatureOperatorReaction Bpull t x) wv := by
          rw [PiLp.inner_apply]
          simp [inner, mul_comm]
        simpa [hinner_eq, hderiv_eq] using hsum
      simpa [mul_add] using hinner.const_mul 4
    have hlapAt : laplacianAt (I := I) (flowG (I := I) S) t
          (bundleInnerScalarization u ν t) x =
        4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x) wv := by
      have hlocal : (fun y : M => bundleInnerScalarization u ν t y) =ᶠ[𝓝 x]
          fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y) := by
        filter_upwards [heqν] with y hy
        unfold bundleInnerScalarization
        rw [tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) y (u t y) (ν y)]
        have hiso := fiberInner_compUhlenbeck_isometry_tensor (I := I) (M := M) hT S basisAt iota hiota0 hgram
          horth0 (D.regular_subset ht) y (S.base.rm04 t y) (η y)
        have hu : u t y = (S.base.rm04 t y).compContinuousLinearMap
            (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt y) iota t) := rfl
        rw [hu, hy]
        simpa [uhlenbeckPullbackTensorAt] using hiso
      have hsm : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y)) x :=
        (inner0S_contMDiff (I := I) (S.base.metric t) (S.base.rm04 t) η).contMDiffAt
      have hsm' : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (bundleInnerScalarization u ν t) x := hsm.congr_of_eventuallyEq hlocal
      have hlap0 : laplacian (I := I) ((flowG (I := I) S).connection t) ((flowG (I := I) S).metric t)
            (fun y : M => inner0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) (η y)) x =
          inner0S (I := I) (S.base.metric t) x 4
            (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S t 2 x)) (η x) := by
        have hA1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
            (S.base.connection t) (S.base.rm04 t) (nablaKRm04Field (I := I) S t 1) := by
          simpa [nablaKRm04Field_zero] using (nablaKRm04Field_realizes (I := I) S t 0)
        have hA2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
            (S.base.connection t) (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2) := by
          simpa using (nablaKRm04Field_realizes (I := I) S t 1)
        have hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis
            (identityInvMetric (Idx := Fin 3)) := by
          exact Tensor0SBundle.metricInverseInBasis_identity_of_orthonormal (I := I)
            (S.base.metric t) basis (by
              intro i j
              simpa [delta3] using hOrth i j)
        have hlap1 := laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat (I := I) (M := M) S
          (S.base.rm04 t) (nablaKRm04Field (I := I) S t 1) (nablaKRm04Field (I := I) S t 2)
          η nablaη nabla2η hA1 hA2 hη h2η basis (identityInvMetric (Idx := Fin 3)) hinv
          hflat1 hflat2
        simpa [laplacianAt] using hlap1
      have hlap1 : laplacian (I := I) ((flowG (I := I) S).connection t) ((flowG (I := I) S).metric t)
          (bundleInnerScalarization u ν t) x =
          inner0S (I := I) (S.base.metric t) x 4
            (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S t 2 x)) (η x) := by
        exact laplacian_congr_of_eventuallyEq (I := I) ((flowG (I := I) S).connection t)
          ((flowG (I := I) S).metric t) hsm' hsm hlocal |>.trans hlap0
      let R : Tensor04At (I := I) (M := M) x :=
        metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
          (nablaKRm04Field (I := I) S t 2 x)
      have hR : R ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberRegion_roughLapRm04_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) hT S t x basis
      have hcomp : ∀ a b c d : Fin 3,
          roughLapD t x a b c d = tensor04StandardAt (I := I) (M := M)
            (uhlenbeckPullbackTensorAt basisAt iota t x R)
            (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
        intro a b c d
        calc
          roughLapD t x a b c d
              = uhlenbeckPullbackRmInFrame iota roughLapRm04 t x a b c d := rfl
          _ = uhlenbeckPullbackRmInFrame iota
                (fun s y a' b' c' d' =>
                  metricTraceFirstTwo0SAt (I := I) (S.base.metric s) (nablaKRm04Field (I := I) S s 2 y)
                    (vec4 (I := I) (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d')))
                t x a b c d := rfl
          _ = uhlenbeckPullbackRmInFrame iota
                (fun s y a' b' c' d' =>
                  tensor04StandardAt (I := I) (M := M)
                    (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
                      (nablaKRm04Field (I := I) S s 2 y))
                    (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d'))
                t x a b c d := by
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro j _
                apply Finset.sum_congr rfl; intro k _
                apply Finset.sum_congr rfl; intro l _
                simpa using (congrArg (fun z : ℝ => iota t x a i * iota t x b j * iota t x c k * iota t x d l * z)
                  (fiberRegion_roughLapRm04_component_eq (I := I) (M := M) hT S basisAt x basis hOrth i j k l))
          _ = tensor04StandardAt (I := I) (M := M) (uhlenbeckPullbackTensorAt basisAt iota t x R)
                (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d) := by
                rw [show uhlenbeckPullbackRmInFrame iota
                      (fun s y a' b' c' d' =>
                        tensor04StandardAt (I := I) (M := M)
                          (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
                            (nablaKRm04Field (I := I) S s 2 y))
                          (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d'))
                      t x a b c d =
                    uhlenbeckPullbackRmInFrame iota
                      (fun s y a' b' c' d' =>
                        tensor04StandardAt (I := I) (M := M) R
                          (basisAt y a') (basisAt y b') (basisAt y c') (basisAt y d'))
                      t x a b c d by
                    unfold uhlenbeckPullbackRmInFrame
                    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
                    simp [R]]
                exact (fiberRegion_pulledTensor_apply_basis (I := I) (M := M) R basisAt iota t a b c d).symm
      have hRalg : uhlenbeckPullbackTensorAt basisAt iota t x R ∈
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
        fiberRegion_compU_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) basisAt iota t x R hR
      have hiso := fiberInner_compUhlenbeck_isometry_tensor (I := I) (M := M) hT S basisAt iota hiota0 hgram
        horth0 (D.regular_subset ht) x R (η x)
      have hνx : ν x = uhlenbeckPullbackTensorAt basisAt iota t x (η x) := by
        exact heqν.self_of_nhds
      have hscal := fiberRegion_pulledTensor_scalarization_eq (I := I) (M := M)
        basisAt (S.base.metric 0) iota t x (horth0 x) R hRalg (ν x)
      have hmat : uhlenbeckCurvatureOperatorMatrix
            (fun t' x' a b c d => tensor04StandardAt (I := I) (M := M)
              (uhlenbeckPullbackTensorAt basisAt iota t' x' R)
              (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x =
          uhlenbeckCurvatureOperatorMatrix roughLapD t x := by
        unfold uhlenbeckCurvatureOperatorMatrix
        apply congrArg
        funext ij
        exact (hcomp (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2 (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1).symm
      calc
        laplacianAt (I := I) (flowG (I := I) S) t (bundleInnerScalarization u ν t) x
            = inner0S (I := I) (S.base.metric t) x 4 R (η x) := hlap1
        _ = inner0S (I := I) (S.base.metric 0) x 4 (uhlenbeckPullbackTensorAt basisAt iota t x R) (ν x) := by
              calc
                inner0S (I := I) (S.base.metric t) x 4 R (η x)
                    = inner0S (I := I) (S.base.metric 0) x 4
                        (uhlenbeckPullbackTensorAt basisAt iota t x R)
                        (uhlenbeckPullbackTensorAt basisAt iota t x (η x)) := by
                          simpa [uhlenbeckPullbackTensorAt] using hiso.symm
                _ = inner0S (I := I) (S.base.metric 0) x 4
                      (uhlenbeckPullbackTensorAt basisAt iota t x R) (ν x) := by
                      rw [hνx]
        _ = 4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix
              (fun t' x' a b c d => tensor04StandardAt (I := I) (M := M)
                (uhlenbeckPullbackTensorAt basisAt iota t' x' R)
                (basisAt x' a) (basisAt x' b) (basisAt x' c) (basisAt x' d)) t x)
              (regionSupportVector (I := I) (S.base.metric 0) basisAt x (ν x)) := hscal
        _ = 4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x) wv := by
              rw [hmat]
    have hsource : fiberRegionSource hT (I := I) (M := M) S basisAt x (u t x) (ν x) =
        4 * inner ℝ (hamiltonIveyMatrixReactionEuclidean (A t x)) wv := by
      unfold fiberRegionSource
      have hmain := regionSource_at_pulled_eq (I := I) (S.base.metric 0) S basisAt iota t x
        (hAlg t x) (ν x)
      simpa [A, w, wv, u] using hmain
    have hreaction : uhlenbeckCurvatureOperatorReaction Bpull t x =
        hamiltonIveyMatrixReactionEuclidean (A t x) := by
      simpa [A, Bpull, Borig, uhlenbeckPullbackRmInFrame] using
        (fiberRegion_reaction_eq_reactionState (I := I) (M := M) hT S basisAt iota
          hiota0 hgram hdim horth0 (D.regular_subset ht) x)
    have htarget : laplacianAt (I := I) (flowG (I := I) S) t (bundleInnerScalarization u ν t) x +
          fiberRegionSource hT (I := I) (M := M) S basisAt x (u t x) (ν x) =
        4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
          hamiltonIveyMatrixReactionEuclidean (A t x)) wv := by
      rw [hlapAt, hsource]
      simp [inner_add_left, mul_add]
    have hfun : (fun s : ℝ => bundleInnerScalarization u ν s x) =
        fun s : ℝ => 4 * inner ℝ (A s x) wv := by
      funext s
      unfold bundleInnerScalarization
      rw [hscalar_eq s x (ν x)]
    have hderiv' : HasDerivAt (fun s : ℝ => 4 * inner ℝ (A s x) wv)
        (4 * inner ℝ (uhlenbeckCurvatureOperatorMatrix roughLapD t x +
          hamiltonIveyMatrixReactionEuclidean (A t x)) wv) t := by
      simpa [hreaction] using hscalar_deriv
    simpa [u, hfun] using (hderiv'.congr_deriv htarget.symm)
end Helpers

section FlatSectionHelpers

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem hamiltonIveyConvexMatrixRegionSupportEuclidean_conj
    (K τ : ℝ) (M O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O * O.transpose = 1) :
    hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean (O.transpose * M * O)) =
      hamiltonIveyConvexMatrixRegionSupportEuclidean K τ (matrixToEuclidean M) := by
  unfold hamiltonIveyConvexMatrixRegionSupportEuclidean
  have heig := euclideanMatrixSymmetrization_matrixToEuclidean_orthogonal_conj_eigenvalues₀ M O hO
  simp_rw [heig]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem regionNormalDirections_conj_scale_condition
    {M O : Matrix (Fin 3) (Fin 3) ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hO : O * O.transpose = 1)
    (hM : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ 0 < 0 ∨
      euclideanMatrixSymmetrization (matrixToEuclidean M) = 0) :
    (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (ρ • (O.transpose * M * O)))).eigenvalues₀ 0 < 0 ∨
      euclideanMatrixSymmetrization (matrixToEuclidean (ρ • (O.transpose * M * O))) = 0 := by
  have hSM : euclideanMatrixSymmetrization (matrixToEuclidean (ρ • (O.transpose * M * O))) =
      ρ • (O.transpose * euclideanMatrixSymmetrization (matrixToEuclidean M) * O) := by
    calc
      euclideanMatrixSymmetrization (matrixToEuclidean (ρ • (O.transpose * M * O)))
          = ρ • euclideanMatrixSymmetrization (matrixToEuclidean (O.transpose * M * O)) := by
              exact euclideanMatrixSymmetrization_matrixToEuclidean_smul ρ (O.transpose * M * O)
      _ = ρ • (O.transpose * euclideanMatrixSymmetrization (matrixToEuclidean M) * O) := by
              rw [euclideanMatrixSymmetrization_matrixToEuclidean_conj]
  rcases hM with hneg | hzero
  · by_cases hρ₀ : ρ = 0
    · subst ρ
      right
      rw [hSM]
      simp
    · left
      have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρ₀)
      have hB : (O.transpose * euclideanMatrixSymmetrization (matrixToEuclidean M) * O).IsHermitian := by
        have hc : (O.conjTranspose * euclideanMatrixSymmetrization (matrixToEuclidean M) * O).IsHermitian :=
          Matrix.isHermitian_conjTranspose_mul_mul O (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M))
        simpa using hc
      have hρB : (ρ • (O.transpose * euclideanMatrixSymmetrization (matrixToEuclidean M) * O)).IsHermitian := by
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul]
        rw [hB]
        simp [star_trivial]
      have hMain1 : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (ρ • (O.transpose * M * O)))).eigenvalues₀ =
          hρB.eigenvalues₀ := by
        exact eigenvalues₀_eq_of_charpoly_eq_real
          (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (ρ • (O.transpose * M * O)))) hρB
          (by
            rw [hSM])
      have hMain2 : hρB.eigenvalues₀ = ρ • hB.eigenvalues₀ :=
        eigenvalues₀_smul_of_nonneg (hS := hB) hρ hρB
      have hMain3 : ρ • hB.eigenvalues₀ =
          ρ • (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ := by
        have hconj : hB.eigenvalues₀ = (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ :=
          eigenvalues₀_orthogonal_conj (S := euclideanMatrixSymmetrization (matrixToEuclidean M))
            (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)) hO
        rw [show hB.eigenvalues₀ = (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ from hconj]
      have hMain : (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (ρ • (O.transpose * M * O)))).eigenvalues₀ =
          ρ • (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ :=
        hMain1.trans (hMain2.trans hMain3)
      rw [hMain]
      have hlt : ρ * (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ 0 < 0 :=
        mul_neg_of_pos_of_neg hρpos hneg
      simpa using hlt
  · right
    rw [hSM, hzero]
    simp

end FlatSectionHelpers
section FlatSectionProjection

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem algebraicCurvatureTensorProjection_compUhlenbeck_commute
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    (algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) x
        (A.compContinuousLinearMap (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
      : Tensor04At (I := I) (M := M) x) =
      ContinuousMultilinearMap.compContinuousLinearMap
        (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) := by
  classical
  let U : TangentSpace I x →L[ℝ] TangentSpace I x := uhlenbeckEndomorphismAt (basisAt x) iota t
  let compU : Tensor04At (I := I) (M := M) x → Tensor04At (I := I) (M := M) x :=
    fun B => (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x).symm
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x B).compContinuousLinearMap
        (fun _ : Fin 4 => U))
  let e : TangentSpace I x ≃ₗ[ℝ] TangentSpace I x :=
    LinearEquiv.ofBijective U.toLinearMap (uhlenbeckEndomorphism_invertible hT S basisAt iota hiota0 hgram ht x)
  let Uinv : TangentSpace I x →L[ℝ] TangentSpace I x := e.symm.toContinuousLinearMap
  let compUinv : Tensor04At (I := I) (M := M) x → Tensor04At (I := I) (M := M) x :=
    fun B => (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x).symm
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x B).compContinuousLinearMap
        (fun _ : Fin 4 => Uinv))
  have hUinvU : ∀ v : TangentSpace I x, Uinv (U v) = v := by
    intro v
    change e.symm (e v) = v
    exact e.symm_apply_apply v
  have hcompUinv : ∀ B : Tensor04At (I := I) (M := M) x, compU (compUinv B) = B := by
    intro B
    apply tensor0SSpace_ext 4 x
    intro v
    change Tensor0SSpace.eval (compU (compUinv B)) v = Tensor0SSpace.eval B v
    dsimp [compU, compUinv]
    rw [Tensor0SSpace.eval_fiber_equiv_symm,
      ContinuousLinearEquiv.apply_symm_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact hUinvU (v i)
  have hchar : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      inner0S (I := I) (S.base.metric 0) x 4
        (algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) x
          (A.compContinuousLinearMap (fun _ : Fin 4 => U))) q =
      inner0S (I := I) (S.base.metric 0) x 4
        (ContinuousMultilinearMap.compContinuousLinearMap
          (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
          (fun _ : Fin 4 => U)) q := by
    intro q
    let q' : Tensor04At (I := I) (M := M) x :=
      ContinuousMultilinearMap.compContinuousLinearMap
        (q : Tensor04At (I := I) (M := M) x) (fun _ : Fin 4 => Uinv)
    have hq' : q' ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
      exact compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule (I := I) Uinv
        ⟨q, q.2⟩
    have hqU : q'.compContinuousLinearMap (fun _ : Fin 4 => U) = (q : Tensor04At (I := I) (M := M) x) := by
      dsimp [q']
      exact hcompUinv (q : Tensor04At (I := I) (M := M) x)
    have hiso := fiberInner_compUhlenbeck_isometry_tensor hT S basisAt iota hiota0 hgram horth0 ht x A q'
    calc
      inner0S (I := I) (S.base.metric 0) x 4
          (algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) x
            (A.compContinuousLinearMap (fun _ : Fin 4 => U))) q
          = inner0S (I := I) (S.base.metric 0) x 4
              (A.compContinuousLinearMap (fun _ : Fin 4 => U)) q := by
              exact algebraicCurvatureTensorProjection_inner (I := I) (S.base.metric 0) x
                (A.compContinuousLinearMap (fun _ : Fin 4 => U)) q
      _ = inner0S (I := I) (S.base.metric 0) x 4
              (A.compContinuousLinearMap (fun _ : Fin 4 => U))
              (q'.compContinuousLinearMap (fun _ : Fin 4 => U)) := by
              rw [hqU]
      _ = inner0S (I := I) (S.base.metric t) x 4 A q' := by
              exact hiso
      _ = inner0S (I := I) (S.base.metric t) x 4
              (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A) q' := by
              rw [algebraicCurvatureTensorProjection_inner (I := I) (S.base.metric t) x A ⟨q', hq'⟩]
      _ = inner0S (I := I) (S.base.metric 0) x 4
              (ContinuousMultilinearMap.compContinuousLinearMap
                (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
                (fun _ : Fin 4 => U)) q := by
              have hiso' := fiberInner_compUhlenbeck_isometry_tensor hT S basisAt iota hiota0 hgram horth0 ht x
                (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x) q'
              rw [← hqU]
              exact hiso'.symm
  let p : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) x
      (A.compContinuousLinearMap (fun _ : Fin 4 => U))
  let u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := ⟨
    ContinuousMultilinearMap.compContinuousLinearMap
      (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
      (fun _ : Fin 4 => U),
    compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule (I := I) U
      (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A)⟩
  have hdiff : ∀ q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x,
      inner0S (I := I) (S.base.metric 0) x 4 ((p - u) : Tensor04At (I := I) (M := M) x) q = 0 := by
    intro q
    have h1 := hchar q
    have h2 : inner0S (I := I) (S.base.metric 0) x 4 u q =
        inner0S (I := I) (S.base.metric 0) x 4
          (ContinuousMultilinearMap.compContinuousLinearMap
            (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A : Tensor04At (I := I) (M := M) x)
            (fun _ : Fin 4 => U)) q := by
      rfl
    have hsub : inner0S (I := I) (S.base.metric 0) x 4 ((p - u) : Tensor04At (I := I) (M := M) x) q =
        inner0S (I := I) (S.base.metric 0) x 4 (p : Tensor04At (I := I) (M := M) x) q -
          inner0S (I := I) (S.base.metric 0) x 4 (u : Tensor04At (I := I) (M := M) x) q := by
      change (tensor0SMetricData (I := I) (S.base.metric 0) x 4).flat
          ((p : Tensor04At (I := I) (M := M) x) - u) (q : Tensor04At (I := I) (M := M) x) =
        (tensor0SMetricData (I := I) (S.base.metric 0) x 4).flat
          (p : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x) -
        (tensor0SMetricData (I := I) (S.base.metric 0) x 4).flat
          (u : Tensor04At (I := I) (M := M) x) (q : Tensor04At (I := I) (M := M) x)
      simp [map_sub]
    rw [hsub]
    rw [h2] at h1
    linarith
  have hself : inner0S (I := I) (S.base.metric 0) x 4
      ((p - u) : Tensor04At (I := I) (M := M) x) (p - u) = 0 := by
    simpa using hdiff ⟨(p - u : Tensor04At (I := I) (M := M) x), by
      exact Submodule.sub_mem (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) p.2 u.2⟩
  have hzero : (p - u : Tensor04At (I := I) (M := M) x) = 0 := by
    change (tensor0SMetricData (I := I) (S.base.metric 0) x 4).inner
        ((p - u : Tensor04At (I := I) (M := M) x)) (p - u) = 0 at hself
    exact ((tensor0SMetricData (I := I) (S.base.metric 0) x 4).inner_self_eq_zero_iff
      (p - u : Tensor04At (I := I) (M := M) x)).mp hself
  have hpeq : p = u := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  simpa [p, u] using congrArg Subtype.val hpeq

omit [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem regionProjMatrix_uhlenbeckPullback_eq_moving
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    regionProjMatrix (I := I) (S.base.metric 0) (basisAt x)
        (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x A) =
      regionProjMatrix (I := I) (S.base.metric t)
        (uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x) A := by
  unfold regionProjMatrix
  let pt : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A
  let p0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) x
      (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x A)
  let u : algebraicCurvatureTensorSubmodule (I := I) (M := M) x := ⟨
    ContinuousMultilinearMap.compContinuousLinearMap
      (pt : Tensor04At (I := I) (M := M) x)
      (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t),
    compUhlenbeck_mem_algebraicCurvatureTensorSubmodule basisAt iota t pt⟩
  have hproj := algebraicCurvatureTensorProjection_compUhlenbeck_commute
    (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x A
  have hpu : p0 = u := by
    apply Subtype.ext
    simpa [p0, u, pt, uhlenbeckPullbackTensorAt] using hproj
  change curvatureOperatorMatrixAt (I := I) x (basisAt x) p0 = _
  rw [hpu]
  simpa [u, pt] using curvatureOperatorMatrixAt_compU_eq_moving
    (I := I) (M := M) hT S basisAt iota hiota0 hgram ht x
      (algebraicCurvatureTensorProjection (I := I) (S.base.metric t) x A)

end FlatSectionProjection

section RadialTransportLinear

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection

variable [NeZero (Module.finrank ℝ E)]
variable [T2Space (TangentBundle I M)]

section TensorTransport

omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem radialTransportTensorExtension_regionProjMatrix_eq_conj
    (g : SmoothRiemannianMetric I M) (p : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I p))
    (horth : OrthonormalBasisAt (I := I) g p basis)
    (η₀ : Tensor04At (I := I) (M := M) p)
    (χ : SmoothBumpFunction I p)
    (W : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hsupport : tsupport (χ : M → Real) ⊆ radialTransportSectionDomain (I := I) g p)
    (hW : ∀ i y, W i y = χ y • radialTransportSection (I := I) g p (basis i) y)
    (y : M) (hy : y ∈ radialTransportSectionDomain (I := I) g p)
    (basis' : Module.Basis (Fin 3) Real (TangentSpace I y))
    (horth' : OrthonormalBasisAt (I := I) g y basis') :
    ∃ O : Matrix (Fin 3) (Fin 3) Real,
      O * O.transpose = 1 ∧
      regionProjMatrix (I := I) g basis'
          (radialTransportTensorExtension g p basis η₀ W y) =
        (χ y) ^ 4 •
          (O.transpose * regionProjMatrix (I := I) g basis η₀ * O) := by
  classical
  let Tlin : TangentSpace I p →ₗ[Real] TangentSpace I y := radialTransportLinearMapAt g p y
  have hTbij : Function.Bijective Tlin := by
    have hTinj : Function.Injective Tlin := by
      intro a b hab
      exact radialTransportSection_injective (I := I) g p y hy
        (by simpa [Tlin, radialTransportLinearMapAt] using hab)
    have hTsurj : Function.Surjective Tlin :=
      radialTransportLinearMapAt_surjective (I := I) g p y hy
    exact ⟨hTinj, hTsurj⟩
  let e : TangentSpace I p ≃ₗ[Real] TangentSpace I y := LinearEquiv.ofBijective Tlin hTbij
  let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) := basis.map e
  have horthY : OrthonormalBasisAt (I := I) g y basisY := by
    intro a b
    have hinner := radialTransportSection_inner_eq (I := I) g p (basis a) (basis b) y hy
    have hTa : (basisY a : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis a) y := by
      dsimp [basisY]
      change (e (basis a) : TangentSpace I y) = _
      rfl
    have hTb : (basisY b : TangentSpace I y) =
        radialTransportSection (I := I) g p (basis b) y := by
      dsimp [basisY]
      change (e (basis b) : TangentSpace I y) = _
      rfl
    rw [hTa, hTb]
    simpa [horth a b] using hinner
  let O : Matrix (Fin 3) (Fin 3) Real :=
    bivectorFrameChangeMatrix (I := I) g basisY basis'
  have hO : O * O.transpose = 1 :=
    bivectorFrameChangeMatrix_mul_transpose_of_orthonormal
      (I := I) (M := M) g basisY basis' horthY horth'
  refine ⟨O, hO, ?_⟩
  let A₀ : algebraicCurvatureTensorSubmodule (I := I) (M := M) p :=
    algebraicCurvatureTensorProjection (I := I) g p η₀
  let AY : algebraicCurvatureTensorSubmodule (I := I) (M := M) y :=
    algebraicCurvatureTensorProjection (I := I) g y (radialTransportSectionTensor g p η₀ y)
  have hAY : (AY : Tensor04At (I := I) (M := M) y) =
      radialTransportSectionTensor g p
        (A₀ : Tensor04At (I := I) (M := M) p) y := by
    exact algebraicCurvatureTensorProjection_radialTransport_commute (I := I) g p
      (Module.finrank_eq_card_basis basis) η₀ y hy
  have hmatrixY : curvatureOperatorMatrixAt (I := I) y basisY AY =
      curvatureOperatorMatrixAt (I := I) p basis A₀ := by
    ext i j
    rw [show curvatureOperatorMatrixAt (I := I) y basisY AY i j =
        tensor04CurvatureOperatorMatrixAt (I := I) basisY
          (AY : Tensor04At (I := I) (M := M) y) i j by rfl]
    rw [hAY]
    simp only [tensor04CurvatureOperatorMatrixAt_apply]
    rw [radialTransportSectionTensor, dif_pos hy]
    change (A₀ : Tensor04At (I := I) (M := M) p)
        (fun a ↦ radialTransportInverseAt g p y hy
          (vec4 (basisY (bivectorIndex3 i).1) (basisY (bivectorIndex3 i).2)
            (basisY (bivectorIndex3 j).2) (basisY (bivectorIndex3 j).1) a)) =
      (A₀ : Tensor04At (I := I) (M := M) p)
        (vec4 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1))
    congr 1
    funext a
    fin_cases a <;>
      change radialTransportInverseAt g p y hy
        (radialTransportLinearMapAt g p y _) = _ <;>
      exact radialTransportInverseAt_left_inverse (I := I) g p y hy _
  have hconj : curvatureOperatorMatrixAt (I := I) y basis' AY =
      O.transpose * curvatureOperatorMatrixAt (I := I) y basisY AY * O := by
    rw [← tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt
      (I := I) basis' AY]
    rw [← tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt
      (I := I) basisY AY]
    simpa only [O] using tensor04CurvatureOperatorMatrixAt_conj_of_orthonormal
      (I := I) (M := M) g basisY basis' horthY AY
  rw [radialTransportTensorExtension_eq_smul g p basis horth η₀ χ W hsupport hW y]
  unfold regionProjMatrix
  have hproj := congrArg Subtype.val
    ((algebraicCurvatureTensorProjection (I := I) g y).map_smul
      ((χ y) ^ 4) (radialTransportSectionTensor g p η₀ y))
  ext i j
  change tensor04StandardAt (I := I) (M := M)
      (algebraicCurvatureTensorProjection (I := I) g y
        ((χ y) ^ 4 • radialTransportSectionTensor g p η₀ y) :
          Tensor04At (I := I) (M := M) y) _ _ _ _ = _
  rw [hproj]
  change (χ y) ^ 4 * curvatureOperatorMatrixAt (I := I) y basis' AY i j = _
  rw [hconj, hmatrixY]
  rfl


omit [IsManifold I 3 M] [SigmaCompactSpace M] [NeZero (Module.finrank Real E)]
  [T2Space (TangentBundle I M)] [I.Boundaryless] in
private theorem fiberRegion_hasFlatSupportSectionsOn
    {T : Real} (hT : 0 < T) [I.Boundaryless]
    [T2Space (TangentBundle I M)]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota 0 x a b)
    (K : Real) :
    (by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.Core.toNormedAddCommGroup Real
          (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace Real (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.ofCore Real (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun _ ↦ inferInstance
      exact HasFlatSupportSectionsOn (I := I) (Set.Icc 0 T)
        (V := fun x : M ↦ Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (regionNormalDirections (I := I) (S.base.metric 0) basisAt)
        (fiberRegionSupport hT (I := I) (M := M) S basisAt K)) := by
  classical
  let : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
    fun x ↦ @InnerProductSpace.Core.toNormedAddCommGroup Real
      (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
  let : ∀ x : M, InnerProductSpace Real (Tensor04At (I := I) (M := M) x) :=
    fun x ↦ @InnerProductSpace.ofCore Real (Tensor04At (I := I) (M := M) x)
      inferInstance inferInstance inferInstance
      (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
  let : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
    fun _ ↦ inferInstance
  refine ⟨?_⟩
  intro t ht x₀ ν' hν'
  let U : TangentSpace I x₀ →L[Real] TangentSpace I x₀ :=
    uhlenbeckEndomorphismAt (basisAt x₀) iota t
  let e : TangentSpace I x₀ ≃ₗ[Real] TangentSpace I x₀ :=
    LinearEquiv.ofBijective U.toLinearMap
      (uhlenbeckEndomorphism_invertible hT S basisAt iota hiota0 hgram ht x₀)
  let Uinv : TangentSpace I x₀ →L[Real] TangentSpace I x₀ :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hUinvU : ∀ v : TangentSpace I x₀, Uinv (U v) = v := by
    intro v
    change e.symm (e v) = v
    exact e.symm_apply_apply v
  let η₀ : Tensor04At (I := I) (M := M) x₀ :=
    ν'.compContinuousLinearMap (fun _ : Fin 4 ↦ Uinv)
  have hpull : uhlenbeckPullbackTensorAt (I := I) basisAt iota t x₀ η₀ = ν' := by
    apply tensor0SSpace_ext 4 x₀
    intro v
    change ν' (fun a ↦ Uinv (U (v a))) = ν' v
    congr 1
    funext a
    exact hUinvU (v a)
  let basis : Module.Basis (Fin 3) Real (TangentSpace I x₀) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x₀
  have horth : OrthonormalBasisAt (I := I) (S.base.metric t) x₀ basis :=
    uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
      hT S basisAt iota hiota0 hgram x₀ (horth0 x₀) ht
  obtain ⟨χ, W, hsupport, hW, _⟩ :=
    exists_localized_radial_transport_sections (I := I) (S.base.metric t) x₀
      (fun i ↦ basis i)
  let η : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
    radialTransportTensorExtension (S.base.metric t) x₀ basis η₀ W
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.base.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let d : CanonicalSpatialDerivs0S (I := I) (M := M) (S.base.connection t) η :=
    CanonicalSpatialDerivs0S.ofSmoothConnection
      (E := E) (H := H) (I := I) (M := M) (S.base.connection t) hcov η
  let ν : (x : M) → Tensor04At (I := I) (M := M) x := fun y ↦
    uhlenbeckPullbackTensorAt (I := I) basisAt iota t y (η y)
  refine ⟨ν, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨η, d.nablaA, d.nabla2A, basis, horth, ?_, d.first, d.second, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · exact radialTransportTensorExtension_nabla_center_zero
        (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW d
    · exact radialTransportTensorExtension_metricTrace_center_zero
        (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW d
  · dsimp [ν, η]
    rw [radialTransportTensorExtension_initial
      (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW]
    exact hpull
  · intro y
    by_cases hχ : χ y = 0
    · have hηy : η y = 0 := by
        dsimp [η]
        rw [radialTransportTensorExtension_eq_smul
          (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW y]
        simp [hχ]
      have hνy : ν y = 0 := by
        dsimp [ν]
        rw [hηy]
        apply tensor0SSpace_ext 4 y
        intro v
        rfl
      rw [hνy, regionNormalDirections]
      right
      have hproj0 : (algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) y
          (0 : Tensor04At (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) = 0 := by
        exact congrArg Subtype.val
          ((algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) y).map_zero)
      unfold regionProjMatrix
      rw [show algebraicCurvatureTensorProjection (I := I) (S.base.metric 0) y
          (0 : Tensor04At (I := I) (M := M) y) = 0 by
        apply Subtype.ext
        exact hproj0]
      have hmatrix0 : curvatureOperatorMatrixAt (I := I) y (basisAt y)
          (0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) = 0 := by
        ext i j
        rfl
      rw [hmatrix0]
      ext i j
      simp [euclideanMatrixSymmetrization, matrixToEuclidean, euclideanToMatrix]
    · have hy : y ∈ radialTransportSectionDomain (I := I) (S.base.metric t) x₀ :=
        hsupport (subset_closure (show y ∈ Function.support (χ : M → Real) from hχ))
      let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) :=
        uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht y
      have horthY : OrthonormalBasisAt (I := I) (S.base.metric t) y basisY :=
        uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
          hT S basisAt iota hiota0 hgram y (horth0 y) ht
      obtain ⟨O, hO, hmatrix⟩ :=
        radialTransportTensorExtension_regionProjMatrix_eq_conj
          (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW y hy basisY horthY
      have hpullY := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht y (η y)
      have hcenter := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x₀ η₀
      have hcenterEq : regionProjMatrix (I := I) (S.base.metric t) basis η₀ =
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' := by
        rw [← hpull]
        simpa [basis] using hcenter.symm
      have hmatrixTotal :
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt y) (ν y) =
            (χ y) ^ 4 •
              (O.transpose *
                regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' * O) := by
        calc
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt y) (ν y) =
              regionProjMatrix (I := I) (S.base.metric t) basisY (η y) := by
                simpa [ν, basisY] using hpullY
          _ = (χ y) ^ 4 •
                (O.transpose * regionProjMatrix (I := I) (S.base.metric t) basis η₀ * O) :=
              hmatrix
          _ = (χ y) ^ 4 •
                (O.transpose *
                  regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' * O) := by
              rw [hcenterEq]
      rw [regionNormalDirections] at hν' ⊢
      simp only [Set.mem_ofPred_eq] at hν' ⊢
      have hρ : 0 ≤ (χ y) ^ 4 := pow_nonneg (χ.nonneg : 0 ≤ χ y) 4
      have hmain := regionNormalDirections_conj_scale_condition
        (M := regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν')
        (O := O) (ρ := (χ y) ^ 4) hρ hO hν'
      simpa only [hmatrixTotal] using hmain
  · intro y
    have hisoY := fiberInner_compUhlenbeck_isometry_tensor
      (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht y (η y) (η y)
    have hrad := radialTransportTensorExtension_inner_self_le
      (I := I) (S.base.metric t) x₀ (hdim x₀) basis horth η₀ χ W hsupport hW y
    have hiso0 := fiberInner_compUhlenbeck_isometry_tensor
      (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x₀ η₀ η₀
    have hinner : inner Real (ν y) (ν y) ≤ inner Real ν' ν' := by
      rw [tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) y (ν y) (ν y)]
      rw [show inner0S (I := I) (S.base.metric 0) y 4 (ν y) (ν y) =
          inner0S (I := I) (S.base.metric t) y 4 (η y) (η y) by
        simpa [ν, uhlenbeckPullbackTensorAt] using hisoY]
      apply hrad.trans_eq
      calc
        inner0S (I := I) (S.base.metric t) x₀ 4 η₀ η₀ =
            inner0S (I := I) (S.base.metric 0) x₀ 4
              (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x₀ η₀)
              (uhlenbeckPullbackTensorAt (I := I) basisAt iota t x₀ η₀) := by
                simpa [uhlenbeckPullbackTensorAt] using hiso0.symm
        _ = inner0S (I := I) (S.base.metric 0) x₀ 4 ν' ν' := by rw [hpull]
        _ = inner Real ν' ν' :=
          (tensor0S_inner_eq_inner0S (I := I) (S.base.metric 0) x₀ ν' ν').symm
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
    nlinarith [norm_nonneg (ν y), norm_nonneg ν']
  · have hevent : ∀ᶠ y in nhds x₀,
        fiberRegionSupport hT (I := I) (M := M) S basisAt K t y (ν y) =
          fiberRegionSupport hT (I := I) (M := M) S basisAt K t x₀ ν' := by
      have hdomain : radialTransportSectionDomain (I := I) (S.base.metric t) x₀ ∈ nhds x₀ :=
        (radialTransportSectionDomain_isOpen (I := I) (S.base.metric t) x₀).mem_nhds
          (mem_radialTransportSectionDomain_self (I := I) (S.base.metric t) x₀)
      filter_upwards [χ.eventuallyEq_one, hdomain] with y hχ hy
      simp only [Pi.one_apply] at hχ
      let basisY : Module.Basis (Fin 3) Real (TangentSpace I y) :=
        uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht y
      have horthY : OrthonormalBasisAt (I := I) (S.base.metric t) y basisY :=
        uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M)
          hT S basisAt iota hiota0 hgram y (horth0 y) ht
      obtain ⟨O, hO, hmatrix⟩ :=
        radialTransportTensorExtension_regionProjMatrix_eq_conj
          (I := I) (S.base.metric t) x₀ basis horth η₀ χ W hsupport hW y hy basisY horthY
      have hpullY := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht y (η y)
      have hcenter := regionProjMatrix_uhlenbeckPullback_eq_moving
        (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 ht x₀ η₀
      unfold fiberRegionSupport regionSupport
      rw [show regionProjMatrix (I := I) (S.base.metric 0) (basisAt y) (ν y) =
          regionProjMatrix (I := I) (S.base.metric t) basisY (η y) by
        simpa [ν, basisY] using hpullY]
      rw [hmatrix, hχ, one_pow, one_smul]
      rw [show regionProjMatrix (I := I) (S.base.metric t) basis η₀ =
          regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν' by
        rw [← hpull]
        simpa [basis] using hcenter.symm]
      rw [hamiltonIveyConvexMatrixRegionSupportEuclidean_conj K (max t 0)
        (regionProjMatrix (I := I) (S.base.metric 0) (basisAt x₀) ν') O hO]
    have hset : {y : M |
        fiberRegionSupport hT (I := I) (M := M) S basisAt K t y (ν y) =
          fiberRegionSupport hT (I := I) (M := M) S basisAt K t x₀ ν'} ∈ nhds x₀ :=
      hevent
    obtain ⟨V, hVsub, hVopen, hx₀V⟩ := mem_nhds_iff.mp hset
    exact ⟨V, hVopen, hx₀V, fun y hy ↦ hVsub hy⟩

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)] [I.Boundaryless]
    [SigmaCompactSpace M] in
private theorem fiberRegionPropagationOn_of_bundleMaximumPrinciple
    {T : Real} (hT : 0 < T) [I.Boundaryless] [CompactSpace M]
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a)) iota 0 x a b)
    {K : Real} (hK : 0 < K)
    (hinit : ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota 0 x ∈ fiberHamiltonIveyRegion basisAt K 0 x)
    (hsol : by
      letI : ∀ x : M, NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.Core.toNormedAddCommGroup Real
          (Tensor04At (I := I) (M := M) x) inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore
      letI : ∀ x : M, InnerProductSpace Real (Tensor04At (I := I) (M := M) x) :=
        fun x ↦ @InnerProductSpace.ofCore Real (Tensor04At (I := I) (M := M) x)
          inferInstance inferInstance inferInstance
          (tensor0SMetricData (I := I) (S.base.metric 0) x 4).toCore.toCore
      letI : ∀ x : M, CompleteSpace (Tensor04At (I := I) (M := M) x) :=
        fun _ ↦ inferInstance
      exact IsBundleHeatReactionOn
        (V := fun x : M ↦ Tensor04At (I := I) (M := M) x)
        (fiberRegionFlat (I := I) (M := M) S basisAt iota)
        (RealTimeInterval.closed 0 T hT.le) (flowG (I := I) S)
        (fun _ => fiberRegionSource hT (I := I) (M := M) S basisAt)
        (uhlenbeckPulledRm04At S basisAt iota)) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota t x ∈ fiberHamiltonIveyRegion basisAt K t x := by
  apply fiberRegionPropagationOn_of_flatSupport
    (I := I) (M := M) hT S hS hdim basisAt horth0 iota hiota0 hgram hK hinit hsol
  exact fiberRegion_hasFlatSupportSectionsOn
    (I := I) (M := M) hT S hdim basisAt horth0 iota hiota0 hgram K

end TensorTransport


end RadialTransportLinear

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem curvatureOperatorRegionPropagationOn_zero
    {T : Real} (hT : 0 < T) [I.Boundaryless] [CompactSpace M] [Nonempty M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    {K : Real} (hK : 0 < K)
    (hinit : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric 0) x
        ⟨S.base.rm04 0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric 0) x⟩ K) :
    curvatureOperatorRegionPropagationOn (I := I) (M := M) S K 0 T := by
  classical
  let : NeZero (Module.finrank Real E) := ⟨by
    intro hzero
    have hthree := hdim (Classical.choice (inferInstance : Nonempty M))
    have hthree' : Module.finrank Real E = 3 := by
      with_unfolding_all exact hthree
    omega⟩
  let basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x) :=
    fun x ↦ Classical.choose
      (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  have horth0 : ∀ x : M,
      OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x) := by
    intro x
    exact Classical.choose_spec
      (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  let iota : MatrixComp M (Fin 3) := intrinsicUhlenbeckIota hT S hS basisAt
  have hspec := intrinsicUhlenbeckIota_spec (I := I) (M := M) hT S hS basisAt
  have hiota0 : ∀ x : M, ∀ a k : Fin 3,
      iota 0 x a k = if a = k then 1 else 0 := by
    simpa [iota] using hspec.1
  have hiotaCont : ∀ x : M,
      ContinuousOn (fun t : Real ↦ iota t x) (Set.Icc 0 T) := by
    simpa [iota] using hspec.2.1
  have hiotaODE : BundleIsomorphismODEInFrameOn
      (D := RealTimeInterval.closed 0 T hT.le) iota
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x ↦ basisAt x a)) := by
    change FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (ricciOneUpCompInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x ↦ basisAt x a))
    change FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x ↦ basisAt x a))
    simpa only [iota] using hspec.2.2.1
  have hgram : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a))
          iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x ↦ basisAt x a))
          iota 0 x a b := by
    simpa [iota] using hspec.2.2.2
  have hsol := fiber_region_heat_reaction_on (I := I) (M := M) hT S hS hdim
    basisAt horth0 iota hiota0 hgram hiotaCont hiotaODE
  have hinitFiber : ∀ x : M,
      uhlenbeckPulledRm04At S basisAt iota 0 x ∈
        fiberHamiltonIveyRegion basisAt K 0 x := by
    intro x
    exact uhlenbeckPulledRm04At_initial_mem_fiberHamiltonIveyRegion
      (I := I) (M := M) hT S basisAt iota
      hiota0 horth0 hK x (hinit x)
  have hfiber := fiberRegionPropagationOn_of_bundleMaximumPrinciple
    (I := I) (M := M) hT S hS hdim basisAt horth0 iota hiota0 hgram hK hinitFiber hsol
  have hprop := curvatureOperatorRegionPropagationOn_of_fiberRegion_mem
    (I := I) (M := M) hT S basisAt iota hiota0 hgram horth0 hfiber
  simpa [curvatureOperatorRegionPropagationOn] using hprop

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem curvatureOperatorRegionPropagationOn_of_initial_lower_bound_aux
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K : Real} (hT : 0 < T) (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    curvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hM =>
      let := hM
      intro t ht x
      exact isEmptyElim x
  | inr hM =>
      let := hM
      have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
        intro x
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim
      let Sshift : SolutionOn (I := I) (M := M) (D.timeShift t0) := S.timeShift t0
      let D0 : RealTimeInterval := RealTimeInterval.closed 0 T hT.le
      let S0 : SolutionOn (I := I) (M := M) D0 := Sshift.timeRestrict D0
      have hSshift : IsSolutionOn (I := I) Sshift := by
        exact isSolutionOn_timeShift (I := I) hS t0
      have hS0 : IsSolutionOn (I := I) S0 := by
        apply isSolutionOn_timeRestrict (I := I) hSshift
        · intro t ht
          change t + t0 ∈ D.carrier
          exact hslab ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · intro t ht
          change t + t0 ∈ D.regular
          exact hreg ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hinit0 : ∀ x : M,
          curvatureOperatorLowerBoundAt (I := I) (S0.base.metric 0) x
            ⟨S0.base.rm04 0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S0.base.metric 0) x⟩ K := by
        intro x
        simpa [S0, Sshift, SolutionOn.timeRestrict, SolutionOn.timeShift,
          SolutionFamily.timeShift, SolutionFamily.rm04] using hinit x
      have hprop0 := curvatureOperatorRegionPropagationOn_zero
        (I := I) (M := M) hT S0 hS0 hdimT hK hinit0
      have hpropShift : curvatureOperatorRegionPropagationOn
          (I := I) (M := M) Sshift K 0 T := by
        unfold curvatureOperatorRegionPropagationOn at hprop0 ⊢
        exact hprop0
      exact curvatureOperatorRegionPropagationOn_timeShift
        (I := I) (M := M) S hpropShift

end DifferentialGeometry.PDE.RicciFlow

end


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K : Real} (hT : 0 ≤ T) (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    curvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T := by
  rcases hT.eq_or_lt with hTzero | hTpos
  · subst T
    exact curvatureOperatorRegionPropagationOn_initial
      (I := I) (M := M) S hK hdim hinit
  · let : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    let : IsManifold I 2 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    let : IsManifold I 3 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    let : SigmaCompactSpace M := CompactSpace.sigmaCompact
    exact curvatureOperatorRegionPropagationOn_of_initial_lower_bound_aux
      (I := I) (M := M) S hS hTpos hK hslab hreg hdim hinit

theorem hamilton_ivey_pinching
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K : Real} (hT : 0 ≤ T) (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ < 0 →
        S.scalar t x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩) *
            (Real.log ((-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩) / K) +
            Real.log (1 + 2 * K * (t - t0)) - 3)) := by
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    (I := I) (M := M) S hS hT hK hslab hreg hdim hinit
  exact hamilton_ivey_pinching_of_curvatureOperatorRegionPropagationOn
    (I := I) (M := M) S hprop

theorem hamilton_ivey_pinching_k_one
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T : Real} (hT : 0 ≤ T)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ 1) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 / (1 + 4 * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ < 0 →
        S.scalar t x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩) *
            (Real.log (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩) +
            Real.log (1 + 2 * (t - t0)) - 3)) := by
  have hmain := hamilton_ivey_pinching (I := I) (M := M) S hS hT
    (by norm_num : 0 < (1 : Real)) hslab hreg hdim hinit
  constructor
  · intro t ht x
    have h := hmain.1 t ht x
    norm_num at h ⊢
    simpa [one_mul] using h
  · intro t ht x hneg
    have h := hmain.2 t ht x hneg
    norm_num at h ⊢
    simpa [one_mul] using h

theorem hamilton_ivey_asymptotic_pinching
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K delta : Real} (hT : 0 ≤ T) (hK : 0 < K) (hdelta : 0 < delta)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M,
      curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ K) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩) ≤
        delta * S.scalar t x +
          2 * delta * K * Real.exp (2 + (2 * delta)⁻¹) /
            (1 + 2 * K * (t - t0)) := by
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    (I := I) (M := M) S hS hT hK hslab hreg hdim hinit
  exact hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagationOn
    (I := I) (M := M) S hK hdelta hprop

end DifferentialGeometry.PDE.RicciFlow

end
