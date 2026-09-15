import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import DifferentialGeometry.Geometry.Metric.Euclidean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import DifferentialGeometry.Geometry.Metric.Construction.OpenCoefficients
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_complete_metric_extension_of_lower_bound
    (U : Opens E) (gU : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {B r c : ℝ} (hB : 0 < B) (hBr : B < r) (hc : 0 < c)
    (hball : Metric.closedBall (0 : E) r ⊆ (U : Set E))
    (hlower : ∀ z : U, ∀ v : E, c * ‖v‖ ^ 2 ≤ gU.inner z v v) :
    ∃ gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      RiemannianMetricComplete gExt ∧
      (∀ z : E, ∀ v : E, min c 1 * ‖v‖ ^ 2 ≤ gExt.inner z v v) ∧
      ∀ z : E, ∀ hz : ‖z‖ ≤ B, ∀ v w : E,
        gExt.inner z v w = gU.inner
          ⟨z, hball (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz.trans hBr.le))⟩
          v w := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let : SigmaCompactSpace U := inferInstance
  let χ : ContDiffBump (0 : E) := ⟨B, r, hB, hBr⟩
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ := contMDiff_iff_contDiff.mpr χ.contDiff
  have hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := fun _ => ⟨χ.nonneg, χ.le_one⟩
  have hχsupp : tsupport χ ⊆ (U : Set E) := by
    rw [χ.tsupport_eq]
    exact hball
  let gExt := (euclideanMetric (E := E)).bumpExtendOpen U gU χ hχ hχ01 hχsupp
  have heuc (z v : E) : (euclideanMetric (E := E)).inner z v v = ‖v‖ ^ 2 := by
    change inner ℝ v v = ‖v‖ ^ 2
    exact real_inner_self_eq_norm_sq v
  have hlow : ∀ z : E, ∀ v : E, min c 1 * ‖v‖ ^ 2 ≤ gExt.inner z v v := by
    intro z v
    by_cases hz : z ∈ U
    · rw [show gExt.inner z v v = _ from bumpExtendOpen_inner_of_mem
        euclideanMetric U gU χ hχ hχ01 hχsupp z hz v v]
      rw [heuc]
      simp only [smul_eq_mul]
      have hpart := mul_le_mul_of_nonneg_left (hlower ⟨z, hz⟩ v) (χ.nonneg (x := z))
      have hminc : min c 1 * ‖v‖ ^ 2 ≤ c * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      have hminone : min c 1 * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        exact (mul_le_mul_of_nonneg_right (min_le_right c 1) (sq_nonneg ‖v‖)).trans_eq
          (one_mul _)
      have hm0 := mul_le_mul_of_nonneg_left hminc (χ.nonneg (x := z))
      have hm1 := mul_le_mul_of_nonneg_left hminone (sub_nonneg.mpr (χ.le_one (x := z)))
      nlinarith
    · have hns : z ∉ tsupport χ := fun h => hz (hχsupp h)
      rw [show gExt.inner z v v = _ from bumpExtendOpen_inner_of_notMem_tsupport
        euclideanMetric U gU χ hχ hχ01 hχsupp z hns v v]
      rw [heuc]
      exact (mul_le_mul_of_nonneg_right (min_le_right c 1) (sq_nonneg ‖v‖)).trans_eq
        (one_mul _)
  refine ⟨gExt, ?_, hlow, ?_⟩
  · apply RiemannianMetricComplete.of_lower euclideanMetric_complete (lt_min hc zero_lt_one)
    intro z v
    change min c 1 * (euclideanMetric (E := E)).inner z (show E from v) (show E from v) ≤
      gExt.inner z (show E from v) (show E from v)
    rw [heuc]
    exact hlow z v
  · intro z hz v w
    have hzU : z ∈ U := hball (Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using hz.trans hBr.le))
    have hzχ : χ z = 1 := χ.one_of_mem_closedBall
      (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz))
    rw [show gExt.inner z v w = _ from bumpExtendOpen_inner_of_mem
      euclideanMetric U gU χ hχ hχ01 hχsupp z hzU v w, hzχ]
    simp only [one_smul, sub_self, zero_smul, add_zero]

end DifferentialGeometry

end

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_complete_metric_extension_of_contDiffOn_bilinearField
    (U : Opens E) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, x ∈ U → ∀ v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiffOn ℝ ∞ B U)
    {R r c : ℝ} (hR : 0 < R) (hRr : R < r) (hc : 0 < c)
    (hball : Metric.closedBall (0 : E) r ⊆ (U : Set E))
    (hlower : ∀ z ∈ U, ∀ v : E, c * ‖v‖ ^ 2 ≤ B z v v) :
    ∃ gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      RiemannianMetricComplete gExt ∧
      (∀ z : E, ∀ v : E, min c 1 * ‖v‖ ^ 2 ≤ gExt.inner z v v) ∧
      ∀ z : E, ∀ _hz : ‖z‖ ≤ R, ∀ v w : E,
        gExt.inner z v w = B z v w := by
  obtain ⟨gU, hgU⟩ := exists_smoothMetric_of_contDiffOn_bilinearField U B hsymm hpos hB
  obtain ⟨gExt, hcomplete, hglobal, heq⟩ :=
    DifferentialGeometry.exists_complete_metric_extension_of_lower_bound U gU hR hRr hc hball
      (fun z v => by simpa [hgU z v v] using hlower z z.property v)
  refine ⟨gExt, hcomplete, hglobal, ?_⟩
  intro z hz v w
  rw [heq z hz v w]
  exact hgU _ _ _

end DifferentialGeometry.Geometry

end

section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_complete_metric_extension_of_contDiffOn_bilinearField_on_closedBall
    (U : Opens E) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, x ∈ U → ∀ v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiffOn ℝ ∞ B U)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : Metric.closedBall (0 : E) R ⊆ (U : Set E)) :
    ∃ gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      RiemannianMetricComplete gExt ∧
      (∃ c : ℝ, 0 < c ∧ ∀ z v : E, c * ‖v‖ ^ 2 ≤ gExt.inner z v v) ∧
      ∀ z : E, ‖z‖ ≤ r → ∀ v w : E, gExt.inner z v w = B z v w := by
  obtain ⟨C, hC, hb⟩ := (hB.continuousOn.mono hball).exists_uniform_bilin_quadratic_bounds
    (isCompact_closedBall (0 : E) R) (fun z hz => hpos z (hball hz))
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let V : Opens E := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
  have hVU : (V : Set E) ⊆ (U : Set E) := fun _ hz => hball (Metric.ball_subset_closedBall hz)
  have hcut : r < (r + R) / 2 := by linarith
  have hcutR : (r + R) / 2 < R := by linarith
  obtain ⟨gExt, hcomplete, hglobal, heq⟩ :=
    exists_complete_metric_extension_of_contDiffOn_bilinearField V B
      (fun z hz => hsymm z (hVU hz)) (fun z hz => hpos z (hVU hz)) (hB.mono hVU)
      hr hcut (inv_pos.mpr hCpos)
      (Metric.closedBall_subset_ball hcutR)
      (fun z hz v => (hb z (Metric.ball_subset_closedBall hz) v).1)
  exact ⟨gExt, hcomplete, ⟨min C⁻¹ 1, lt_min (inv_pos.mpr hCpos) zero_lt_one, hglobal⟩, heq⟩

theorem exists_complete_metric_extension_of_contDiffOn_bilinearField_on_ball
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hsymm : ∀ x ∈ Metric.ball (0 : E) R, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ Metric.ball (0 : E) R, ∀ v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) R)) :
    ∃ gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      RiemannianMetricComplete gExt ∧
      (∃ c : ℝ, 0 < c ∧ ∀ z v : E, c * ‖v‖ ^ 2 ≤ gExt.inner z v v) ∧
      ∀ z : E, ‖z‖ ≤ r → ∀ v w : E, gExt.inner z v w = B z v w := by
  exact exists_complete_metric_extension_of_contDiffOn_bilinearField_on_closedBall
    ⟨Metric.ball 0 R, Metric.isOpen_ball⟩ B hsymm hpos hB hr
    (show r < (r + R) / 2 by linarith)
    (Metric.closedBall_subset_ball (show (r + R) / 2 < R by linarith))

end DifferentialGeometry.Geometry

end
