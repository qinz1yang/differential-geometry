import DifferentialGeometry.Analysis.Calculus.Taylor.QuadraticBound
import DifferentialGeometry.Geometry.Metric.TruncatedRange
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem hausdorffDist_graph_tangent_closedBall_le (Φ : E → H) (P : H →L[ℝ] E)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hgraph : ∀ u, P (Φ u) = u)
    (X : Set H) (x : H) (hx : x ∈ X) {R B e : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hreg : ∀ u ∈ closedBall (P x) R, ContDiffAt ℝ 2 Φ u)
    (hsecond : ∀ u ∈ closedBall (P x) R, ‖iteratedFDeriv ℝ 2 Φ u‖ ≤ B)
    (hforward : ∀ y ∈ X ∩ closedBall x R, dist y (Φ (P y)) ≤ e)
    (hbackward : ∀ u ∈ closedBall (P x) R, ∃ y ∈ X, dist y (Φ u) ≤ e) :
    hausdorffDist (X ∩ closedBall x R)
      ((fun v => x + fderiv ℝ Φ (P x) v) '' (univ : Set E) ∩ closedBall x R) ≤
        3 * (2 * e + B * R ^ 2 / 2) := by
  let u₀ := P x
  let T := fderiv ℝ Φ u₀
  have hcenter : u₀ ∈ closedBall u₀ R := mem_closedBall_self hR.le
  have hdΦ : DifferentiableAt ℝ Φ u₀ := (hreg u₀ hcenter).differentiableAt (by norm_num)
  have hPT : P.comp T = ContinuousLinearMap.id ℝ E := by
    have hh : P ∘ Φ = id := funext hgraph
    have hh' := fderiv_comp u₀ P.differentiableAt hdΦ
    simpa [hh, T] using hh'.symm
  have hT (v : E) : ‖v‖ ≤ ‖T v‖ := by
    have hh : P (T v) = v := congrArg (fun A : E →L[ℝ] E => A v) hPT
    simpa only [hh] using hP (T v)
  have htaylor {u : E} (hu : u ∈ closedBall u₀ R) :
      dist (Φ u) (Φ u₀ + T (u - u₀)) ≤ B * R ^ 2 / 2 := by
    have hh := DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le
      (fun t ht => hreg _ ((convex_closedBall u₀ R).add_smul_sub_mem hcenter hu ht))
      (fun t ht => hsecond _ ((convex_closedBall u₀ R).add_smul_sub_mem hcenter hu ht))
    have hn : ‖u - u₀‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hu
    have hn2 : ‖u - u₀‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hmul := mul_le_mul_of_nonneg_left hn2 hB
    rw [dist_eq_norm, sub_add_eq_sub_sub]
    change ‖Φ u - Φ u₀ - fderiv ℝ Φ u₀ (u - u₀)‖ ≤ _
    nlinarith
  have hbase : dist x (Φ u₀) ≤ e := hforward x ⟨hx, mem_closedBall_self hR.le⟩
  have hnear {y : H} {u : E} (hu : u ∈ closedBall u₀ R) (hy : dist y (Φ u) ≤ e) :
      dist y (x + T (u - u₀)) ≤ 2 * e + B * R ^ 2 / 2 := by
    have h1 := dist_triangle y (Φ u) (Φ u₀ + T (u - u₀))
    have h2 := dist_triangle y (Φ u₀ + T (u - u₀)) (x + T (u - u₀))
    rw [dist_add_right] at h2
    have hb : dist (Φ u₀) x ≤ e := by simpa only [dist_comm] using hbase
    linarith [htaylor hu]
  apply hausdorffDist_truncated_range_le T hT X x hx hR (by positivity)
  · intro y hy
    have hu : P y ∈ closedBall u₀ R := by
      have hh := hP (y - x)
      rw [map_sub] at hh
      have hyR : ‖y - x‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hy.2
      simpa only [mem_closedBall, dist_eq_norm, u₀] using hh.trans hyR
    exact ⟨P y - u₀, hnear hu (hforward y hy)⟩
  · intro v hv
    have hu : u₀ + v ∈ closedBall u₀ R := by simpa [mem_closedBall, dist_eq_norm] using hv
    obtain ⟨y, hy, hyd⟩ := hbackward (u₀ + v) hu
    refine ⟨y, hy, ?_⟩
    simpa only [add_sub_cancel_left] using hnear hu hyd

theorem graph_coverage_relative_error_le {σ Γ r B e : ℝ}
    (hσ : 0 < σ) (hΓ : 0 < Γ) (hB : 0 ≤ B)
    (hrlow : σ / 2 ≤ r) (hrhigh : r ≤ 2 * σ)
    (he : e ≤ Γ * σ / 24) (hcurv : B * σ ≤ Γ ^ 3 / 6) :
    3 * (2 * e + B * (r / Γ) ^ 2 / 2) / r ≤ Γ := by
  have hr : 0 < r := by linarith
  have h1 := mul_le_mul_of_nonneg_left hrlow hΓ.le
  have hv : 6 * e ≤ Γ * r / 2 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hrhigh hB
  have hc : 3 * B * r ≤ Γ ^ 3 := by nlinarith
  have hΓ2 : 0 < Γ ^ 2 := sq_pos_of_pos hΓ
  have h3 := mul_le_mul_of_nonneg_right hv hΓ2.le
  have h4 := mul_le_mul_of_nonneg_right hc hr.le
  apply (div_le_iff₀ hr).mpr
  have heq : 3 * (2 * e + B * (r / Γ) ^ 2 / 2) =
      (6 * e * Γ ^ 2 + (3 / 2 : ℝ) * B * r ^ 2) / Γ ^ 2 := by
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ hΓ2).mpr
  nlinarith

end GC.MetricGeometry
