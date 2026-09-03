import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Inclusion
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Laplacian
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1EigenBasis
import Mathlib.Analysis.InnerProductSpace.Dual

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

def dirichletHsOneEquivH1Compl
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g 1 ≃ₗᵢ[ℝ] H1ComplDirichlet g :=
  (dirichletHs.rescaleEquivL2 (g := g) (σ := 1)).trans
    (dirichletH1HilbertBasis g).repr.symm

@[simp] theorem dirichletHsOneEquivH1Compl_repr
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 1) :
    (dirichletH1HilbertBasis g).repr
        (dirichletHsOneEquivH1Compl g u) =
      dirichletHs.rescaleEquivL2 u := by
  rw [dirichletHsOneEquivH1Compl, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

def dirichletHsNegOneRieszEquivH1Compl
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g (-1) ≃ₗᵢ[ℝ] H1ComplDirichlet g :=
  (dirichletHs.rescaleEquivL2 (g := g) (σ := -1)).trans
    (dirichletH1HilbertBasis g).repr.symm

@[simp] theorem dirichletHsNegOneRieszEquivH1Compl_repr
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g (-1)) :
    (dirichletH1HilbertBasis g).repr
        (dirichletHsNegOneRieszEquivH1Compl g u) =
      dirichletHs.rescaleEquivL2 u := by
  rw [dirichletHsNegOneRieszEquivH1Compl,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

def dirichletHsNegOneEquivH1Dual
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g (-1) ≃L[ℝ] (H1ComplDirichlet g →L[ℝ] ℝ) :=
  (dirichletHsNegOneRieszEquivH1Compl g).toContinuousLinearEquiv.trans
    (InnerProductSpace.toDual ℝ
      (H1ComplDirichlet g)).toContinuousLinearEquiv

def dirichletEnergyForm
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ :=
  let L := H1ComplDirichletToLp g
  (innerSL ℝ :
      H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ) -
    (innerSL ℝ).bilinearComp L L

@[simp] theorem dirichletEnergyForm_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : H1ComplDirichlet g) :
    dirichletEnergyForm g u v =
      inner ℝ u v - inner ℝ
        (H1ComplDirichletToLp g u) (H1ComplDirichletToLp g v) :=
  rfl

@[simp] theorem dirichletHsNegOneEquivH1Dual_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g (-1)) (v : H1ComplDirichlet g) :
    dirichletHsNegOneEquivH1Dual g u v =
      inner ℝ (dirichletHsNegOneRieszEquivH1Compl g u) v :=
  rfl

theorem dirichletHsNegOneEquivH1Dual_norm
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g (-1)) :
    ‖dirichletHsNegOneEquivH1Dual g u‖ = ‖u‖ := by
  calc
    ‖dirichletHsNegOneEquivH1Dual g u‖ =
        ‖dirichletHsNegOneRieszEquivH1Compl g u‖ :=
      (InnerProductSpace.toDual ℝ
        (H1ComplDirichlet g)).norm_map _
    _ = ‖u‖ :=
      (dirichletHsNegOneRieszEquivH1Compl g).norm_map u

def dirichletBilinearFormToHs
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ) :
    dirichletHs g 1 →L[ℝ] dirichletHs g (-1) :=
  (dirichletHsNegOneEquivH1Dual g).symm.toContinuousLinearMap.comp
    (B.comp
      (dirichletHsOneEquivH1Compl g).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem dirichletBilinearFormToHs_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ)
    (u : dirichletHs g 1) :
    dirichletBilinearFormToHs g B u =
      (dirichletHsNegOneEquivH1Dual g).symm
        (B (dirichletHsOneEquivH1Compl g u)) :=
  rfl

theorem dirichletHsNegOneEquivH1Dual_bilinearFormToHs
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ)
    (u : dirichletHs g 1) :
    dirichletHsNegOneEquivH1Dual g
        (dirichletBilinearFormToHs g B u) =
      B (dirichletHsOneEquivH1Compl g u) := by
  rw [dirichletBilinearFormToHs_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem dirichletBilinearFormToHs_norm_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ) :
    ‖dirichletBilinearFormToHs g B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro u
  rw [dirichletBilinearFormToHs_apply]
  have hdual :
      ‖(dirichletHsNegOneEquivH1Dual g).symm
          (B (dirichletHsOneEquivH1Compl g u))‖ =
        ‖B (dirichletHsOneEquivH1Compl g u)‖ := by
    have h := dirichletHsNegOneEquivH1Dual_norm g
      ((dirichletHsNegOneEquivH1Dual g).symm
        (B (dirichletHsOneEquivH1Compl g u)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hdual]
  calc
    ‖B (dirichletHsOneEquivH1Compl g u)‖ ≤
        ‖B‖ * ‖dirichletHsOneEquivH1Compl g u‖ :=
      B.le_opNorm _
    _ = ‖B‖ * ‖u‖ := by
      rw [(dirichletHsOneEquivH1Compl g).norm_map]

def dirichletL2BilinearFormToHs
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : Lp ℝ 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g →L[ℝ] ℝ) :
    dirichletHs g 0 →L[ℝ] dirichletHs g (-1) :=
  (dirichletHsNegOneEquivH1Dual g).symm.toContinuousLinearMap.comp
    (B.comp
      (dirichletHsZeroEquivL2 g).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem dirichletL2BilinearFormToHs_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : Lp ℝ 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g →L[ℝ] ℝ)
    (u : dirichletHs g 0) :
    dirichletL2BilinearFormToHs g B u =
      (dirichletHsNegOneEquivH1Dual g).symm
        (B (dirichletHsZeroEquivL2 g u)) :=
  rfl

theorem dirichletHsNegOneEquivH1Dual_l2BilinearFormToHs
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : Lp ℝ 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g →L[ℝ] ℝ)
    (u : dirichletHs g 0) :
    dirichletHsNegOneEquivH1Dual g
        (dirichletL2BilinearFormToHs g B u) =
      B (dirichletHsZeroEquivL2 g u) := by
  rw [dirichletL2BilinearFormToHs_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem dirichletL2BilinearFormToHs_norm_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (B : Lp ℝ 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g →L[ℝ] ℝ) :
    ‖dirichletL2BilinearFormToHs g B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro u
  rw [dirichletL2BilinearFormToHs_apply]
  have hdual :
      ‖(dirichletHsNegOneEquivH1Dual g).symm
          (B (dirichletHsZeroEquivL2 g u))‖ =
        ‖B (dirichletHsZeroEquivL2 g u)‖ := by
    have h := dirichletHsNegOneEquivH1Dual_norm g
      ((dirichletHsNegOneEquivH1Dual g).symm
        (B (dirichletHsZeroEquivL2 g u)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hdual]
  calc
    ‖B (dirichletHsZeroEquivL2 g u)‖ ≤
        ‖B‖ * ‖dirichletHsZeroEquivL2 g u‖ :=
      B.le_opNorm _
    _ = ‖B‖ * ‖u‖ := by
      rw [(dirichletHsZeroEquivL2 g).norm_map]

private theorem dirichletEnergyForm_apply_basis
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : H1ComplDirichlet g) (i : DirichletLaplacianEigenindex g) :
    dirichletEnergyForm g u (dirichletH1HilbertBasis g i) =
      (1 - i.1.val) * inner ℝ u (dirichletH1HilbertBasis g i) := by
  have hres := resolventDirichlet_inner_eq_lpFunctional g
    (H1ComplDirichletToLp g (dirichletH1HilbertBasis g i)) u
  rw [resolventDirichlet_H1ComplDirichletToLp_dirichletH1HilbertBasis,
    real_inner_smul_left] at hres
  rw [dirichletEnergyForm_apply, ← hres, real_inner_comm]
  ring

private theorem dirichletSobolevWeight_one_eq_resolvent_eigenvalue_inv
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i (1 : ℝ) = i.1.val⁻¹ := by
  unfold dirichletSobolevWeight dirichletLaplacianEigenvalue
  rw [Real.rpow_one]
  field_simp [i.1.val_ne_zero]
  ring

private theorem dirichletSobolevWeight_neg_one_eq_resolvent_eigenvalue
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i (-1 : ℝ) = i.1.val := by
  unfold dirichletSobolevWeight dirichletLaplacianEigenvalue
  rw [Real.rpow_neg_one]
  have h : (1 + (1 - i.1.val) / i.1.val) = i.1.val⁻¹ := by
    field_simp [i.1.val_ne_zero]
    ring
  rw [h, inv_inv]

theorem H1ComplDirichletToLp_dirichletHsOneEquivH1Compl
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 1) :
    H1ComplDirichletToLp g (dirichletHsOneEquivH1Compl g u) =
      dirichletHsZeroEquivL2 g
        (dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) u) := by
  apply (dirichletLaplacianHilbertBasis g).repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply]
  change _ = dirichletL2Coeff
    (dirichletHsZeroEquivL2 g
      (dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) u)) i
  rw [dirichletHs.dirichletHsZeroEquivL2_dirichletL2Coeff,
    dirichletHs.dirichletHsInclusion_coeff]
  rw [real_inner_comm]
  have hcoord := congrArg
    (fun q : lp (fun _ : DirichletLaplacianEigenindex g ↦ ℝ) 2 =>
      (q : DirichletLaplacianEigenindex g → ℝ) i)
    (dirichletHsOneEquivH1Compl_repr g u)
  rw [HilbertBasis.repr_apply_apply,
    dirichletHs.rescaleEquivL2_apply,
    dirichletH1HilbertBasis_apply,
    real_inner_smul_left,
    inner_dirichletLaplacianEigenfunction] at hcoord
  have hmu : 0 < i.1.val :=
    nonzeroDirichletResolventEigenvalue_pos i.1
  have hsqrt : Real.sqrt i.1.val ≠ 0 :=
    (Real.sqrt_pos.mpr hmu).ne'
  change Real.sqrt i.1.val *
      (i.1.val⁻¹ * inner ℝ
        (H1ComplDirichletToLp g (dirichletHsOneEquivH1Compl g u))
        (dirichletLaplacianHilbertBasis g i)) =
    Real.sqrt (dirichletSobolevWeight i 1) * u.coeff i at hcoord
  rw [dirichletSobolevWeight_one_eq_resolvent_eigenvalue_inv,
    Real.sqrt_inv] at hcoord
  field_simp [hsqrt, i.1.val_ne_zero, Real.sq_sqrt hmu.le] at hcoord
  rw [Real.sq_sqrt hmu.le] at hcoord
  exact mul_left_cancel₀ i.1.val_ne_zero hcoord

private theorem dirichletBilinearFormToHs_neg_energyForm_coeff
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 1) (i : DirichletLaplacianEigenindex g) :
    (dirichletBilinearFormToHs g (-dirichletEnergyForm g) u).coeff i =
      -dirichletLaplacianEigenvalue i * u.coeff i := by
  let y := dirichletBilinearFormToHs g (-dirichletEnergyForm g) u
  have hdual := DFunLike.congr_fun
    (dirichletHsNegOneEquivH1Dual_bilinearFormToHs
      g (-dirichletEnergyForm g) u)
    (dirichletH1HilbertBasis g i)
  change inner ℝ (dirichletHsNegOneRieszEquivH1Compl g y)
      (dirichletH1HilbertBasis g i) =
    -dirichletEnergyForm g (dirichletHsOneEquivH1Compl g u)
      (dirichletH1HilbertBasis g i) at hdual
  rw [real_inner_comm,
    ← (dirichletH1HilbertBasis g).repr_apply_apply,
    dirichletHsNegOneRieszEquivH1Compl_repr,
    dirichletHs.rescaleEquivL2_apply,
    dirichletEnergyForm_apply_basis,
    real_inner_comm,
    ← (dirichletH1HilbertBasis g).repr_apply_apply,
    dirichletHsOneEquivH1Compl_repr,
    dirichletHs.rescaleEquivL2_apply] at hdual
  simp only at hdual
  change Real.sqrt (dirichletSobolevWeight i (-1)) * y.coeff i =
    -((1 - i.1.val) *
      (Real.sqrt (dirichletSobolevWeight i 1) * u.coeff i)) at hdual
  change y.coeff i = -dirichletLaplacianEigenvalue i * u.coeff i
  have hμ : 0 < i.1.val := nonzeroDirichletResolventEigenvalue_pos i.1
  have hsqrt : Real.sqrt i.1.val ≠ 0 := (Real.sqrt_pos.mpr hμ).ne'
  apply mul_left_cancel₀ hsqrt
  rw [dirichletSobolevWeight_neg_one_eq_resolvent_eigenvalue,
    dirichletSobolevWeight_one_eq_resolvent_eigenvalue_inv,
    Real.sqrt_inv] at hdual
  rw [hdual]
  unfold dirichletLaplacianEigenvalue
  field_simp [hsqrt, i.1.val_ne_zero]
  rw [Real.sq_sqrt hμ.le]
  ring

theorem dirichletBilinearFormToHs_neg_energyForm_eq_laplacian
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletBilinearFormToHs g (-dirichletEnergyForm g) =
      dirichletHsLaplacianNegOne g := by
  apply ContinuousLinearMap.ext
  intro u
  apply dirichletHs.ext
  funext i
  rw [dirichletBilinearFormToHs_neg_energyForm_coeff,
    dirichletHsLaplacianNegOne_coeff]

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
