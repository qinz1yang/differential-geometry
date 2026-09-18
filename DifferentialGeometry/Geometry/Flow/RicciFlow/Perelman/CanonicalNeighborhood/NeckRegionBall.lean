import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem StrongNeck.ball_subset_region {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    riemannianBallOf (S.base.metric t) x
      (10 * Real.sqrt (1 - eps) / Real.sqrt (S.scalar t x)) ⊆ nk.region := by
  have hminus : 0 < 1 - eps := by linarith [nk.eps_small]
  have hsqrt : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr hminus
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-10 : ℝ) 10 ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hi : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      (by linarith [nk.eps_small])
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  have hball : riemannianClosedBallOf (nk.cylinder.metric 0) (nk.center, 0) 10 ⊆
      univ ×ˢ Icc (-10 : ℝ) 10 := by
    simpa only [zero_sub, zero_add] using
      nk.cylinder.closedBall_subset_slab (nk.center, 0) (by norm_num : (0 : ℝ) ≤ 10)
  have hcapture := ball_subset_image_of_metric_lower_crossModel (nk.cylinder.metric 0)
    (rescaledMetric S t (S.scalar t x) nk.Q_pos 0) nk.map (nk.center, 0)
    (L := (Real.sqrt (1 - eps))⁻¹) (by norm_num : (0 : ℝ) < 10) (inv_pos.mpr hsqrt)
    (nk.cylinder.isCompact_closedBall (nk.center, 0) (by norm_num : (0 : ℝ) ≤ 10))
    (hball.trans (hslab.trans nk.domain)) (by
      intro y hy v
      have he := (nk.comparison.equivalence 0 (by norm_num) y (hslab (hball hy)) v).1
      rw [nk.comparison.pullback_eq 0 y (hslab (hball hy)) (fun _ => v)] at he
      have hh := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hminus.le)
      rw [← mul_assoc, inv_mul_cancel₀ hminus.ne', one_mul] at hh
      simpa only [inv_pow, Real.sq_sqrt hminus.le] using hh)
  have hscaled := hcapture.trans (image_mono hball)
  rw [div_inv_eq_mul, nk.center_eq] at hscaled
  have hQ := Real.sqrt_pos.mpr nk.Q_pos
  have heq := riemannianBallOf_scaleMetric (S.scalar t x) nk.Q_pos (S.base.metric t) x
    (10 * Real.sqrt (1 - eps) / Real.sqrt (S.scalar t x))
  rw [mul_div_cancel₀ _ hQ.ne'] at heq
  simpa only [rescaledMetric, parabolicTime_zero, heq, StrongNeck.region] using hscaled

theorem StrongNeck.closedBall_subset_region {eps r : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t)
    (hr : r < 10 * Real.sqrt (1 - eps) / Real.sqrt (S.scalar t x)) :
    riemannianClosedBallOf (S.base.metric t) x r ⊆ nk.region := by
  intro y hy
  apply nk.ball_subset_region
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
    have hminus : 0 < 1 - eps := by linarith [nk.eps_small]
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hminus))
      (Real.sqrt_pos.mpr nk.Q_pos))).mpr hr)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
