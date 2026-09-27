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
    (u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ))
    (i : DirichletLaplacianEigenIndex g) :
    ⟪dirichletLaplacianHilbertBasis g i,
        dirichletHsToL2
          (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u⟫_ℝ =
      u.coeff i := by
  rw [← HilbertBasis.repr_apply_apply]
  change dirichletL2Coeff
      (dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u) i =
    u.coeff i
  exact DirichletHs.dirichletL2Coeff_dirichletHsToL2 _ u i

private theorem dirichletHs_even_weighted_coeff_summable
    {g : SmoothRiemannianMetric (I_half n) M} (k : ℕ)
    (u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    Summable (fun i : DirichletLaplacianEigenIndex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * (k + 1)) *
        ⟪dirichletLaplacianHilbertBasis g i,
          dirichletHsToL2
            (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u⟫_ℝ ^ 2) := by
  have heq : (fun i : DirichletLaplacianEigenIndex g =>
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
    (u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
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
  rw [DirichletHs.dirichletHsZeroEquivL2_dirichletL2Coeff,
    DirichletHs.dirichletHsInclusion_coeff,
    DirichletHs.dirichletHsInclusion_coeff,
    DirichletHs.dirichletL2Coeff_dirichletHsToL2]

theorem dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomainPow_succ
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
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
    DirichletHs g ((2 * (k + 1) : ℕ) : ℝ) →L[ℝ]
      dirichletLaplacianDomainPow g (k + 1) :=
  ((dirichletHsOneEquivH1Compl g).toLinearIsometry.toContinuousLinearMap.comp
      (dirichletHsInclusion
        (one_le_two_mul_succ_cast k))).codRestrict
    (dirichletLaplacianDomainPow g (k + 1))
    (dirichletHsOneEquivH1Compl_mem_dirichletLaplacianDomainPow_succ g k)

@[simp] theorem coe_dirichletHsToLaplacianDomainPowSucc
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    ((dirichletHsToLaplacianDomainPowSucc g k u :
        dirichletLaplacianDomainPow g (k + 1)) : H1ComplDirichlet g) =
      dirichletHsOneEquivH1Compl g
        (dirichletHsInclusion
          (one_le_two_mul_succ_cast k) u) :=
  rfl

theorem H1ComplDirichletToLp_coe_dirichletHsToLaplacianDomainPowSucc
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ)) :
    H1ComplDirichletToLp g
        (dirichletHsToLaplacianDomainPowSucc g k u : H1ComplDirichlet g) =
      dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u := by
  rw [coe_dirichletHsToLaplacianDomainPowSucc,
    H1ComplDirichletToLp_even_realization]

private theorem exists_dirichletHs_of_mem_dirichletLaplacianDomainPow_succ
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    {v : H1ComplDirichlet g}
    (hv : v ∈ dirichletLaplacianDomainPow g (k + 1)) :
    ∃ u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ),
      dirichletHsOneEquivH1Compl g
          (dirichletHsInclusion (one_le_two_mul_succ_cast k) u) = v := by
  rw [dirichletLaplacianDomainPow_succ_mem_iff] at hv
  obtain ⟨f, rfl⟩ := hv
  let fHs : DirichletHs g 0 := (dirichletHsZeroEquivL2 g).symm f
  have hfSummable : Summable (fun i : DirichletLaplacianEigenIndex g =>
      (dirichletL2Coeff f i) ^ 2) := by
    simpa only [fHs, dirichletSobolevWeight_zero, one_mul,
      DirichletHs.dirichletHsZeroEquivL2_symm_coeff] using
        fHs.weighted_summable
  have hweighted : Summable (fun i : DirichletLaplacianEigenIndex g =>
      dirichletSobolevWeight i ((2 * (k + 1) : ℕ) : ℝ) *
        (i.1.1 ^ (k + 1) * dirichletL2Coeff f i) ^ 2) := by
    rw [show (fun i : DirichletLaplacianEigenIndex g =>
        dirichletSobolevWeight i ((2 * (k + 1) : ℕ) : ℝ) *
          (i.1.1 ^ (k + 1) * dirichletL2Coeff f i) ^ 2) =
        fun i => (dirichletL2Coeff f i) ^ 2 by
      funext i
      unfold dirichletSobolevWeight
      rw [Real.rpow_natCast, one_add_dirichletLaplacianEigenvalue_eq_inv]
      rw [mul_pow, ← pow_mul]
      rw [show 2 * (k + 1) = (k + 1) * 2 by omega]
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt (resolvent_eigenvalue_pos g i.1.property)),
        one_pow, one_mul]]
    exact hfSummable
  let u : DirichletHs g ((2 * (k + 1) : ℕ) : ℝ) :=
    ⟨fun i => i.1.1 ^ (k + 1) * dirichletL2Coeff f i, hweighted⟩
  refine ⟨u, ?_⟩
  apply H1ComplDirichletToLp_injective g
  rw [H1ComplDirichletToLp_even_realization]
  apply (dirichletLaplacianHilbertBasis g).repr.injective
  ext i
  change dirichletL2Coeff
      (dirichletHsToL2
        (show (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) by positivity) u) i =
    dirichletL2Coeff
      (H1ComplDirichletToLp g
        (resolventDirichlet g (((resolventDirichletL2 g) ^ k) f))) i
  rw [DirichletHs.dirichletL2Coeff_dirichletHsToL2]
  change i.1.1 ^ (k + 1) * dirichletL2Coeff f i = _
  rw [← resolventDirichletL2_apply,
    ← mul_apply_eq_comp, ← pow_succ']
  simpa only [dirichletL2Coeff, HilbertBasis.repr_apply_apply] using
    (inner_dirichletLaplacianHilbertBasis_resolventDirichletL2_pow
      g (k + 1) f i).symm

theorem dirichletHsToLaplacianDomainPowSucc_surjective
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    Function.Surjective (dirichletHsToLaplacianDomainPowSucc g k) := by
  intro v
  obtain ⟨u, hu⟩ :=
    exists_dirichletHs_of_mem_dirichletLaplacianDomainPow_succ
      g k v.property
  refine ⟨u, Subtype.ext ?_⟩
  exact hu

theorem dirichletHsToLaplacianDomainPowSucc_injective
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    Function.Injective (dirichletHsToLaplacianDomainPowSucc g k) := by
  intro u v huv
  have hcoe := congrArg
    (fun w : dirichletLaplacianDomainPow g (k + 1) =>
      (w : H1ComplDirichlet g)) huv
  change dirichletHsOneEquivH1Compl g
      (dirichletHsInclusion (one_le_two_mul_succ_cast k) u) =
    dirichletHsOneEquivH1Compl g
      (dirichletHsInclusion (one_le_two_mul_succ_cast k) v) at hcoe
  exact DirichletHs.dirichletHsInclusion_injective (one_le_two_mul_succ_cast k)
    ((dirichletHsOneEquivH1Compl g).injective hcoe)

theorem dirichletHsToLaplacianDomainPowSucc_bijective
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    Function.Bijective (dirichletHsToLaplacianDomainPowSucc g k) :=
  ⟨dirichletHsToLaplacianDomainPowSucc_injective g k,
    dirichletHsToLaplacianDomainPowSucc_surjective g k⟩

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
