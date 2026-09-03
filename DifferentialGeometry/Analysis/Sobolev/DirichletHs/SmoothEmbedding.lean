import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1EigenBasis
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Inclusion

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

open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem dirichletL2Coeff_oneSubLaplacian
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g)
    (i : DirichletLaplacianEigenindex g) :
    dirichletL2Coeff (smoothToLpDirichlet g u.oneSubLaplacian) i =
      (1 + dirichletLaplacianEigenvalue i) *
        dirichletL2Coeff (smoothToLpDirichlet g u) i := by
  change dirichletL2Coeff (smoothToLpInterior g u.oneSubLaplacian) i = _
  rw [u.smoothToLpInterior_oneSubLaplacian]
  unfold dirichletL2Coeff
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  calc
    ⟪dirichletLaplacianHilbertBasis g i, u.oneSubLapClassicalLp⟫_ℝ =
        ⟪H1ComplDirichletToLp g
            (dirichletLaplacianEigenfunction g i : H1ComplDirichlet g),
          u.oneSubLapClassicalLp⟫_ℝ := by
            rw [H1ComplDirichletToLp_dirichletLaplacianEigenfunction]
    _ = ⟪resolventDirichlet g u.oneSubLapClassicalLp,
          (dirichletLaplacianEigenfunction g i : H1ComplDirichlet g)⟫_ℝ := by
            rw [resolventDirichlet_inner_eq_lpFunctional]
    _ = ⟪(dirichletLaplacianEigenfunction g i : H1ComplDirichlet g),
          resolventDirichlet g u.oneSubLapClassicalLp⟫_ℝ := real_inner_comm _ _
    _ = ⟪(dirichletLaplacianEigenfunction g i : H1ComplDirichlet g),
          smoothToH1ComplDirichlet g u⟫_ℝ := by
            rw [smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap]
    _ = i.1.val⁻¹ *
          ⟪H1ComplDirichletToLp g (smoothToH1ComplDirichlet g u),
            dirichletLaplacianHilbertBasis g i⟫_ℝ :=
          inner_dirichletLaplacianEigenfunction g i
            (smoothToH1ComplDirichlet g u)
    _ = i.1.val⁻¹ *
          ⟪smoothToLpDirichlet g u,
            dirichletLaplacianHilbertBasis g i⟫_ℝ := by
          rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    _ = (1 + dirichletLaplacianEigenvalue i) *
          ⟪dirichletLaplacianHilbertBasis g i,
            smoothToLpDirichlet g u⟫_ℝ := by
          rw [one_add_dirichletLaplacianEigenvalue_eq_inv]
          congr 1
          exact real_inner_comm _ _

private def smoothScalarDirichletOneSubLaplacianIterate
    {g : SmoothRiemannianMetric (I_half n) M}
    (m : ℕ) (u : SmoothScalarDirichlet g) : SmoothScalarDirichlet g :=
  (InteriorSmoothScalar.oneSubLaplacian (g := g))^[m] u

private theorem dirichletL2Coeff_oneSubLaplacianIterate
    {g : SmoothRiemannianMetric (I_half n) M}
    (m : ℕ) (u : SmoothScalarDirichlet g)
    (i : DirichletLaplacianEigenindex g) :
    dirichletL2Coeff
        (smoothToLpDirichlet g
          (smoothScalarDirichletOneSubLaplacianIterate m u)) i =
      (1 + dirichletLaplacianEigenvalue i) ^ m *
        dirichletL2Coeff (smoothToLpDirichlet g u) i := by
  induction m with
  | zero => simp [smoothScalarDirichletOneSubLaplacianIterate]
  | succ m ih =>
      rw [smoothScalarDirichletOneSubLaplacianIterate,
        Function.iterate_succ_apply']
      rw [dirichletL2Coeff_oneSubLaplacian]
      change (1 + dirichletLaplacianEigenvalue i) *
          dirichletL2Coeff
            (smoothToLpDirichlet g
              (smoothScalarDirichletOneSubLaplacianIterate m u)) i = _
      rw [ih, pow_succ]
      ring

private theorem smoothScalarDirichlet_even_weighted_summable
    {g : SmoothRiemannianMetric (I_half n) M}
    (m : ℕ) (u : SmoothScalarDirichlet g) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i ((2 * m : ℕ) : ℝ) *
        (dirichletL2Coeff (smoothToLpDirichlet g u) i) ^ 2) := by
  let v : dirichletHs g 0 :=
    (dirichletHsZeroEquivL2 g).symm
      (smoothToLpDirichlet g
        (smoothScalarDirichletOneSubLaplacianIterate m u))
  have hv := v.weighted_summable
  rw [show (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i ((2 * m : ℕ) : ℝ) *
        (dirichletL2Coeff (smoothToLpDirichlet g u) i) ^ 2) =
      (fun i => dirichletSobolevWeight i 0 * (v.coeff i) ^ 2) by
    funext i
    rw [dirichletHs.dirichletHsZeroEquivL2_symm_coeff,
      dirichletL2Coeff_oneSubLaplacianIterate,
      dirichletSobolevWeight_zero, one_mul]
    unfold dirichletSobolevWeight
    rw [Real.rpow_natCast, mul_pow, ← pow_mul]
    congr 2
    omega]
  exact hv

theorem smoothScalarDirichlet_weighted_summable
    {g : SmoothRiemannianMetric (I_half n) M}
    (σ : ℝ) (u : SmoothScalarDirichlet g) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i σ *
        (dirichletL2Coeff (smoothToLpDirichlet g u) i) ^ 2) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (σ / 2)
  have hσm : σ ≤ ((2 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  let T : dirichletHs g ((2 * m : ℕ) : ℝ) :=
    ⟨fun i => dirichletL2Coeff (smoothToLpDirichlet g u) i,
      smoothScalarDirichlet_even_weighted_summable m u⟩
  exact dirichletHs.weighted_summable_of_le hσm T

def smoothToDirichletHs
    (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ)
    (u : SmoothScalarDirichlet g) : dirichletHs g σ where
  coeff i := dirichletL2Coeff (smoothToLpDirichlet g u) i
  weighted_summable := smoothScalarDirichlet_weighted_summable σ u

@[simp] theorem smoothToDirichletHs_coeff
    {g : SmoothRiemannianMetric (I_half n) M}
    (σ : ℝ) (u : SmoothScalarDirichlet g)
    (i : DirichletLaplacianEigenindex g) :
    (smoothToDirichletHs g σ u).coeff i =
      dirichletL2Coeff (smoothToLpDirichlet g u) i := rfl

theorem dirichletHsInclusion_smoothToDirichletHs
    {g : SmoothRiemannianMetric (I_half n) M}
    {τ σ : ℝ} (hτσ : τ ≤ σ) (u : SmoothScalarDirichlet g) :
    dirichletHsInclusion (g := g) hτσ (smoothToDirichletHs g σ u) =
      smoothToDirichletHs g τ u := by
  ext i
  simp only [dirichletHs.dirichletHsInclusion_coeff,
    smoothToDirichletHs_coeff]

theorem dirichletHsZeroEquivL2_smoothToDirichletHs
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    dirichletHsZeroEquivL2 g (smoothToDirichletHs g 0 u) =
      smoothToLpDirichlet g u := by
  apply (dirichletLaplacianHilbertBasis g).repr.injective
  ext i
  change dirichletL2Coeff
      (dirichletHsZeroEquivL2 g (smoothToDirichletHs g 0 u)) i =
    dirichletL2Coeff (smoothToLpDirichlet g u) i
  rw [dirichletHs.dirichletHsZeroEquivL2_dirichletL2Coeff,
    smoothToDirichletHs_coeff]

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
