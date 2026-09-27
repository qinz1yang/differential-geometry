import DifferentialGeometry.Analysis.Sobolev.DirichletHs.EnergyDuality

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

private theorem dirichletSobolevWeight_one_eq_inv
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i 1 = i.1.1⁻¹ := by
  rw [dirichletSobolevWeight, Real.rpow_one,
    one_add_dirichletLaplacianEigenvalue_eq_inv]

theorem resolventDirichlet_dirichletHsOneSubLaplacian
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : DirichletHs g 2) :
    resolventDirichlet g
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacian g 0
            (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u))) =
      dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) := by
  apply (dirichletH1HilbertBasis g).repr.injective
  ext i
  rw [dirichletHsOneEquivH1Compl_repr]
  change ((dirichletH1HilbertBasis g).repr
      (resolventDirichlet g
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacian g 0
            (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u))))) i =
    (DirichletHs.rescaleEquivL2
      (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u)) i
  rw [HilbertBasis.repr_apply_apply, real_inner_comm,
    resolventDirichlet_inner_eq_lpFunctional,
    dirichletH1HilbertBasis_apply,
    (H1ComplDirichletToLp g).map_smul,
    H1ComplDirichletToLp_dirichletLaplacianEigenvector,
    real_inner_smul_left,
    DirichletHs.rescaleEquivL2_apply]
  change Real.sqrt i.1.1 *
      inner ℝ (dirichletLaplacianHilbertBasis g i)
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacian g 0
            (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u))) =
    Real.sqrt (dirichletSobolevWeight i 1) *
      (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u).coeff i
  rw [DirichletHs.dirichletHsInclusion_coeff]
  rw [← (dirichletLaplacianHilbertBasis g).repr_apply_apply]
  change Real.sqrt i.1.1 *
      dirichletL2Coeff
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacian g 0
            (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u))) i =
    Real.sqrt (dirichletSobolevWeight i 1) * u.coeff i
  rw [DirichletHs.dirichletHsZeroEquivL2_dirichletL2Coeff,
    dirichletHsOneSubLaplacian_coeff,
    DirichletHs.dirichletHsInclusion_coeff,
    one_add_dirichletLaplacianEigenvalue_eq_inv,
    dirichletSobolevWeight_one_eq_inv,
    Real.sqrt_inv]
  have hmu : 0 < i.1.1 :=
    resolvent_eigenvalue_pos g i.1.property
  have hsqrt : Real.sqrt i.1.1 ≠ 0 :=
    (Real.sqrt_pos.mpr hmu).ne'
  field_simp [hsqrt, (ne_of_gt (resolvent_eigenvalue_pos g i.1.property))]
  rw [Real.sq_sqrt hmu.le]

theorem dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : DirichletHs g 2) :
    dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) ∈
      dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomain_mem_iff]
  exact ⟨dirichletHsZeroEquivL2 g
      (dirichletHsOneSubLaplacian g 0
            (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u)),
    (resolventDirichlet_dirichletHsOneSubLaplacian g u).symm⟩

def dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M) :
    DirichletHs g 2 →L[ℝ] dirichletLaplacianDomain g :=
  ((dirichletHsOneEquivH1Compl g).toLinearIsometry.toContinuousLinearMap.comp
      (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num))).codRestrict
    (dirichletLaplacianDomain g)
    (dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomain g)

@[simp] theorem coe_dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : DirichletHs g 2) :
    ((dirichletHsTwoToLaplacianDomain g u :
        dirichletLaplacianDomain g) : H1ComplDirichlet g) =
      dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) :=
  rfl

theorem dirichletResolventEquiv_symm_dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : DirichletHs g 2) :
    (dirichletResolventEquiv g).symm
        (dirichletHsTwoToLaplacianDomain g u) =
      dirichletHsZeroEquivL2 g
        (dirichletHsOneSubLaplacian g 0
            (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u)) := by
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_dirichletResolventEquiv_symm,
    coe_dirichletHsTwoToLaplacianDomain]
  exact (resolventDirichlet_dirichletHsOneSubLaplacian g u).symm

theorem dirichletLaplacian_dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : DirichletHs g 2) :
    dirichletLaplacian g (dirichletHsTwoToLaplacianDomain g u) =
      dirichletHsZeroEquivL2 g (dirichletHsLaplacian g 0
        (dirichletHsInclusion (show (0 : ℝ) + 2 ≤ 2 by norm_num) u)) := by
  rw [dirichletLaplacian_apply,
    coe_dirichletHsTwoToLaplacianDomain,
    dirichletResolventEquiv_symm_dirichletHsTwoToLaplacianDomain,
    H1ComplDirichletToLp_dirichletHsOneEquivH1Compl,
    ← (dirichletHsZeroEquivL2 g).map_sub]
  congr 1
  ext i
  simp only [DirichletHs.sub_coeff, DirichletHs.dirichletHsInclusion_coeff,
    dirichletHsOneSubLaplacian_coeff,
    DirichletHs.dirichletHsInclusion_coeff,
    dirichletHsLaplacian_coeff]
  ring

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
