import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.LocalDiffeomorph


noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def closedCellChartMap
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) (r : ℝ) : ClosedCell (m + 1) → M :=
  fun x => Φ (c + r • x.val)

@[simp]
theorem closedCellChartMap_apply
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) (r : ℝ) (x : ClosedCell (m + 1)) :
    closedCellChartMap Φ c r x = Φ (c + r • x.val) := rfl

private theorem closedCellChartMap_argument_mem_source
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 ≤ r)
    (hsource : Metric.closedBall c r ⊆ Φ.source) (x : ClosedCell (m + 1)) :
    c + r • x.val ∈ Φ.source := by
  apply hsource
  change dist (c + r • x.val) c ≤ r
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left x.property hr).trans_eq (mul_one r)

theorem contMDiff_closedCellChartMap
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 ≤ r)
    (hsource : Metric.closedBall c r ⊆ Φ.source) :
    ContMDiff (𝓡∂ (m + 1)) I ∞ (closedCellChartMap Φ c r) := by
  have hinc := (isSmoothEmbedding_closedCell_inclusion m).contMDiff
  have haff : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) => c + r • z) :=
    (by fun_prop : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) => c + r • z)).contMDiff
  have hmap := haff.comp hinc
  intro x
  exact (Φ.contMDiffOn_toFun.contMDiffAt
    (Φ.open_source.mem_nhds (closedCellChartMap_argument_mem_source Φ c hr hsource x))).comp x
    (hmap x)

theorem injective_mfderiv_closedCellChartMap
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source) :
    ∀ x : ClosedCell (m + 1),
      Function.Injective
        (mfderiv (𝓡∂ (m + 1)) I (closedCellChartMap Φ c r) x) := by
  let A : Diffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin (m + 1))) ∞ :=
    { toEquiv :=
        { toFun := fun y => c + r • y
          invFun := fun y => r⁻¹ • (y - c)
          left_inv := fun y => by
            simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
          right_inv := fun y => by
            simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
            abel }
      contMDiff_toFun :=
        (by fun_prop : ContDiff ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (m + 1)) => c + r • y)).contMDiff
      contMDiff_invFun :=
        (by fun_prop : ContDiff ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (m + 1)) => r⁻¹ • (y - c))).contMDiff }
  let ι : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) := Subtype.val
  have hι : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ ι :=
    isSmoothEmbedding_closedCell_inclusion m
  have hAι : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (A ∘ ι) :=
    A.contMDiff.comp hι.contMDiff
  have hmem (x : ClosedCell (m + 1)) : A (ι x) ∈ Φ.source :=
    closedCellChartMap_argument_mem_source Φ c hr.le hsource x
  have hΦ (x : ClosedCell (m + 1)) :
      ContMDiffAt (𝓡 (m + 1)) I ∞ Φ (A (ι x)) :=
    Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hmem x))
  intro x
  have hιd : MDifferentiableAt (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι x :=
    (hι.contMDiff x).mdifferentiableAt (by simp)
  have hAd : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1)) A (ι x) :=
    (A.contMDiff (ι x)).mdifferentiableAt (by simp)
  have hAinj : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) A (ι x)) :=
    (A.mfderivToContinuousLinearEquiv (by simp) (ι x)).injective
  have hιinj : Function.Injective (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι x) :=
    (hι.isImmersion.isImmersionAt x).injective_mfderiv (by simp)
  have hAιinj : Function.Injective
      (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (A ∘ ι) x) := by
    rw [mfderiv_comp x hAd hιd]
    exact hAinj.comp hιinj
  have hΦinj : Function.Injective
      (mfderiv (𝓡 (m + 1)) I Φ (A (ι x))) :=
    ((Φ.isLocalDiffeomorphAt (𝓡 (m + 1)) I ∞ (hmem x)).mfderivToContinuousLinearEquiv
      (by simp)).injective
  change Function.Injective
    (mfderiv (𝓡∂ (m + 1)) I (Φ ∘ (A ∘ ι)) x)
  rw [mfderiv_comp x ((hΦ x).mdifferentiableAt (by simp))
    ((hAι x).mdifferentiableAt (by simp))]
  exact hΦinj.comp hAιinj

end DifferentialGeometry.Topology.Manifold
