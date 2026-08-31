import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Inclusion
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

@[simp] theorem dirichletHsNegOneEquivH1Dual_bilinearFormToHs
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

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
