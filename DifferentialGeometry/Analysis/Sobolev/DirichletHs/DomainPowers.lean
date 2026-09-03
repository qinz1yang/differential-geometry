import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletDomainPowers
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Domain

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure

private theorem one_le_two_mul_succ_cast (k : ℕ) :
    (1 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) := by
  exact_mod_cast (show 1 ≤ 2 * (k + 1) by omega)

private theorem dirichletHsToL2_even_coeff
    {g : SmoothRiemannianMetric (I_half n) M} (k : ℕ)
    (u : dirichletHs g ((2 * (k + 1) : ℕ) : ℝ))
    (i : DirichletLaplacianEigenindex g) :
    ⟪dirichletLaplacianHilbertBasis g i,
        dirichletHsToL2
          (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u⟫_ℝ =
      u.coeff i := by
  rw [← HilbertBasis.repr_apply_apply]
  change dirichletL2Coeff
      (dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u) i =
    u.coeff i
  exact dirichletHs.dirichletL2Coeff_dirichletHsToL2 _ u i

private theorem dirichletHs_even_weighted_coeff_summable
    {g : SmoothRiemannianMetric (I_half n) M} (k : ℕ)
    (u : dirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * (k + 1)) *
        ⟪dirichletLaplacianHilbertBasis g i,
          dirichletHsToL2
            (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u⟫_ℝ ^ 2) := by
  have heq : (fun i : DirichletLaplacianEigenindex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * (k + 1)) *
        ⟪dirichletLaplacianHilbertBasis g i,
          dirichletHsToL2
            (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u⟫_ℝ ^ 2) =
      fun i => dirichletSobolevWeight i ((2 * (k + 1) : ℕ) : ℝ) *
        (u.coeff i) ^ 2 := by
    funext i
    rw [dirichletHsToL2_even_coeff]
    unfold dirichletSobolevWeight
    rw [Real.rpow_natCast]
  rw [heq]
  exact u.weighted_summable

private theorem H1ComplDirichletToLp_even_realization
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : dirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    H1ComplDirichletToLp g
        (dirichletHsOneEquivH1Compl g
          (dirichletHsInclusion
            (one_le_two_mul_succ_cast k) u)) =
      dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u := by
  rw [H1ComplDirichletToLp_dirichletHsOneEquivH1Compl]
  apply (dirichletLaplacianHilbertBasis g).repr.injective
  ext i
  change dirichletL2Coeff
      (dirichletHsZeroEquivL2 g
        (dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num)
          (dirichletHsInclusion
            (one_le_two_mul_succ_cast k) u))) i =
    dirichletL2Coeff
      (dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u) i
  rw [dirichletHs.dirichletHsZeroEquivL2_dirichletL2Coeff,
    dirichletHs.dirichletHsInclusion_coeff,
    dirichletHs.dirichletHsInclusion_coeff,
    dirichletHs.dirichletL2Coeff_dirichletHsToL2]

theorem dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomainPow_succ
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : dirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion
          (one_le_two_mul_succ_cast k) u) ∈
      dirichletLaplacianDomainPow g (k + 1) := by
  obtain ⟨u_h, hu_h, hu_l2⟩ :=
    exists_dirichletLaplacianDomainPow_succ_lift_of_weighted_coeff_summable
      g
      (dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u)
      k (dirichletHs_even_weighted_coeff_summable k u)
  have heq : dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion
          (one_le_two_mul_succ_cast k) u) =
      u_h := by
    apply H1ComplDirichletToLp_injective g
    rw [H1ComplDirichletToLp_even_realization, hu_l2]
  rw [heq]
  exact hu_h

def dirichletHsToLaplacianDomainPowSucc
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    dirichletHs g ((2 * (k + 1) : ℕ) : ℝ) →L[ℝ]
      dirichletLaplacianDomainPow g (k + 1) :=
  ((dirichletHsOneEquivH1Compl g).toLinearIsometry.toContinuousLinearMap.comp
      (dirichletHsInclusion
        (one_le_two_mul_succ_cast k))).codRestrict
    (dirichletLaplacianDomainPow g (k + 1))
    (dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomainPow_succ g k)

@[simp] theorem coe_dirichletHsToLaplacianDomainPowSucc
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : dirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    ((dirichletHsToLaplacianDomainPowSucc g k u :
        dirichletLaplacianDomainPow g (k + 1)) : H1ComplDirichlet g) =
      dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion
          (one_le_two_mul_succ_cast k) u) :=
  rfl

theorem H1ComplDirichletToLp_coe_dirichletHsToLaplacianDomainPowSucc
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : dirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    H1ComplDirichletToLp g
        (dirichletHsToLaplacianDomainPowSucc g k u : H1ComplDirichlet g) =
      dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u := by
  rw [coe_dirichletHsToLaplacianDomainPowSucc,
    H1ComplDirichletToLp_even_realization]

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
