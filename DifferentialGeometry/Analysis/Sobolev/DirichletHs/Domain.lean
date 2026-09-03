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
    (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i 1 = i.1.val⁻¹ := by
  rw [dirichletSobolevWeight, Real.rpow_one,
    one_add_dirichletLaplacianEigenvalue_eq_inv]

theorem resolventDirichlet_dirichletHsOneSubLaplacian
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 2) :
    resolventDirichlet g
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacianL2 g u)) =
      dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) := by
  apply (dirichletH1HilbertBasis g).repr.injective
  ext i
  rw [dirichletHsOneEquivH1Compl_repr]
  change ((dirichletH1HilbertBasis g).repr
      (resolventDirichlet g
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacianL2 g u)))) i =
    (dirichletHs.rescaleEquivL2
      (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u)) i
  rw [HilbertBasis.repr_apply_apply, real_inner_comm,
    resolventDirichlet_inner_eq_lpFunctional,
    dirichletH1HilbertBasis_apply,
    (H1ComplDirichletToLp g).map_smul,
    H1ComplDirichletToLp_dirichletLaplacianEigenfunction,
    real_inner_smul_left,
    dirichletHs.rescaleEquivL2_apply]
  change Real.sqrt i.1.val *
      inner ℝ (dirichletLaplacianHilbertBasis g i)
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacianL2 g u)) =
    Real.sqrt (dirichletSobolevWeight i 1) *
      (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u).coeff i
  rw [dirichletHs.dirichletHsInclusion_coeff]
  rw [← (dirichletLaplacianHilbertBasis g).repr_apply_apply]
  change Real.sqrt i.1.val *
      dirichletL2Coeff
        (dirichletHsZeroEquivL2 g
          (dirichletHsOneSubLaplacianL2 g u)) i =
    Real.sqrt (dirichletSobolevWeight i 1) * u.coeff i
  rw [dirichletHs.dirichletHsZeroEquivL2_dirichletL2Coeff,
    dirichletHsOneSubLaplacianL2_coeff,
    one_add_dirichletLaplacianEigenvalue_eq_inv,
    dirichletSobolevWeight_one_eq_inv,
    Real.sqrt_inv]
  have hmu : 0 < i.1.val :=
    nonzeroDirichletResolventEigenvalue_pos i.1
  have hsqrt : Real.sqrt i.1.val ≠ 0 :=
    (Real.sqrt_pos.mpr hmu).ne'
  field_simp [hsqrt, i.1.val_ne_zero]
  rw [Real.sq_sqrt hmu.le]

theorem dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 2) :
    dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) ∈
      dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomain_mem_iff]
  exact ⟨dirichletHsZeroEquivL2 g
      (dirichletHsOneSubLaplacianL2 g u),
    (resolventDirichlet_dirichletHsOneSubLaplacian g u).symm⟩

def dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g 2 →L[ℝ] dirichletLaplacianDomain g :=
  ((dirichletHsOneEquivH1Compl g).toLinearIsometry.toContinuousLinearMap.comp
      (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num))).codRestrict
    (dirichletLaplacianDomain g)
    (dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomain g)

@[simp] theorem coe_dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 2) :
    ((dirichletHsTwoToLaplacianDomain g u :
        dirichletLaplacianDomain g) : H1ComplDirichlet g) =
      dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) :=
  rfl

theorem dirichletLaplacianDomain_preimage_dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 2) :
    dirichletLaplacianDomain.preimage g
        (dirichletHsTwoToLaplacianDomain g u) =
      dirichletHsZeroEquivL2 g
        (dirichletHsOneSubLaplacianL2 g u) := by
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_preimage_eq,
    coe_dirichletHsTwoToLaplacianDomain]
  exact (resolventDirichlet_dirichletHsOneSubLaplacian g u).symm

theorem dirichletLaplacian_dirichletHsTwoToLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 2) :
    dirichletLaplacian g (dirichletHsTwoToLaplacianDomain g u) =
      dirichletHsZeroEquivL2 g (dirichletHsLaplacianL2 g u) := by
  rw [dirichletLaplacian_apply,
    coe_dirichletHsTwoToLaplacianDomain,
    dirichletLaplacianDomain_preimage_dirichletHsTwoToLaplacianDomain,
    H1ComplDirichletToLp_dirichletHsOneEquivH1Compl,
    ← (dirichletHsZeroEquivL2 g).map_sub]
  congr 1
  ext i
  simp only [dirichletHs.sub_coeff, dirichletHs.dirichletHsInclusion_coeff,
    dirichletHsOneSubLaplacianL2_coeff,
    dirichletHsLaplacianL2_coeff]
  ring

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
