import DifferentialGeometry.Analysis.Sobolev.DirichletHs.HeatSemigroup

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

def dirichletHeatSemigroupHsExt (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ) (t : ℝ) :
    dirichletHs g σ →L[ℝ] dirichletHs g σ :=
  if h : 0 < t then
    dirichletHeatSemigroupHs (g := g) h (a := σ) (b := σ)
  else
    ContinuousLinearMap.id ℝ (dirichletHs g σ)

@[simp] theorem dirichletHeatSemigroupHsExt_zero (g : SmoothRiemannianMetric (I_half n) M)
    (σ : ℝ) :
    dirichletHeatSemigroupHsExt g σ 0 =
      ContinuousLinearMap.id ℝ (dirichletHs g σ) := by
  unfold dirichletHeatSemigroupHsExt
  simp

theorem dirichletHeatSemigroupHsExt_of_pos {g : SmoothRiemannianMetric (I_half n) M}
    {σ : ℝ} {t : ℝ} (ht : 0 < t) :
    dirichletHeatSemigroupHsExt g σ t =
      dirichletHeatSemigroupHs (g := g) ht (a := σ) (b := σ) := by
  unfold dirichletHeatSemigroupHsExt
  simp [ht]

theorem dirichletHeatSemigroupHsExt_of_neg {g : SmoothRiemannianMetric (I_half n) M}
    {σ : ℝ} {t : ℝ} (ht : t < 0) :
    dirichletHeatSemigroupHsExt g σ t =
      ContinuousLinearMap.id ℝ (dirichletHs g σ) := by
  unfold dirichletHeatSemigroupHsExt
  have : ¬ 0 < t := not_lt.mpr ht.le
  simp [this]

theorem dirichletHeatSemigroupHsExt_of_nonpos {g : SmoothRiemannianMetric (I_half n) M}
    {σ : ℝ} {t : ℝ} (ht : t ≤ 0) :
    dirichletHeatSemigroupHsExt g σ t =
      ContinuousLinearMap.id ℝ (dirichletHs g σ) := by
  unfold dirichletHeatSemigroupHsExt
  have : ¬ 0 < t := not_lt.mpr ht
  simp [this]

theorem dirichletHeatSemigroupHsExt_add {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    dirichletHeatSemigroupHsExt g σ (t + s) =
      (dirichletHeatSemigroupHsExt g σ t).comp
        (dirichletHeatSemigroupHsExt g σ s) := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    simp [dirichletHeatSemigroupHsExt_zero]
  · rcases eq_or_lt_of_le hs with hs_eq | hs_pos
    · subst hs_eq
      simp [dirichletHeatSemigroupHsExt_zero]
    · have hts : 0 < t + s := by linarith
      rw [dirichletHeatSemigroupHsExt_of_pos (g := g) (σ := σ) hts,
          dirichletHeatSemigroupHsExt_of_pos (g := g) (σ := σ) ht_pos,
          dirichletHeatSemigroupHsExt_of_pos (g := g) (σ := σ) hs_pos]
      exact dirichletHeatSemigroupHs_add (g := g) ht_pos hs_pos (a := σ)

theorem dirichletHeatSemigroupHsExt_opNorm_le_one {g : SmoothRiemannianMetric (I_half n) M}
    {σ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ‖dirichletHeatSemigroupHsExt g σ t‖ ≤ 1 := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    rw [dirichletHeatSemigroupHsExt_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [dirichletHeatSemigroupHsExt_of_pos (g := g) (σ := σ) ht_pos]
    exact dirichletHeatSemigroupHs_opNorm_le_one (g := g) ht_pos

theorem dirichletHeatSemigroupHsExt_coeff {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}
    {t : ℝ} (ht : 0 ≤ t) (T : dirichletHs g σ)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHeatSemigroupHsExt g σ t T).coeff i =
      Real.exp (-(dirichletLaplacianEigenvalue i) * t) * T.coeff i := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    rw [dirichletHeatSemigroupHsExt_zero]
    change T.coeff i = _
    rw [mul_zero, Real.exp_zero, one_mul]
  · rw [dirichletHeatSemigroupHsExt_of_pos (g := g) (σ := σ) ht_pos]
    exact dirichletHeatSemigroupHs_coeff (g := g) ht_pos T i

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
