import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint
import DifferentialGeometry.Geometry.Metric.Approximation.StripChart

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry

universe u v
variable {X : Type u} [mX : MetricSpace X]

theorem isEdgePoint.exists_local_half_plane_model {p : X} {Δ b s S : ℝ}
    (h : isEdgePoint.{u, v} p Δ b s)
    (hbuffer : S + 10 * (b + s) < min b⁻¹ s⁻¹) :
    ∃ W : X → WithLp 2 (ℝ × ℝ), W p = 0 ∧
      (∀ x, 0 ≤ (W x).snd) ∧
      ∀ x ∈ ball p S, ∀ y ∈ ball p S, |dist (W x) (W y) - dist x y| ≤ b + s := by
  obtain ⟨Y, mY, q, C, hC, _, ⟨F⟩, ⟨G⟩⟩ := h
  let := mY
  exact ⟨F.stripMap G, F.stripMap_basepoint (hC := hC) G,
    fun x => (F.stripMap_height (hC := hC) G x).1, (F.stripMap_estimates (hC := hC) G hbuffer).1⟩

theorem isEdgePoint.exists_local_half_plane_model_rescale {p : X} {Δ b s r c : ℝ}
    (hc : 0 < c)
    (h : @isEdgePoint.{u, v} X (mX.rescale c hc) p Δ b s)
    (hbuffer : c * r + 10 * (b + s) < min b⁻¹ s⁻¹) :
    ∃ W : X → WithLp 2 (ℝ × ℝ), W p = 0 ∧
      (∀ x, 0 ≤ (W x).snd) ∧
      ∀ x ∈ ball p r, ∀ y ∈ ball p r, |dist (W x) (W y) - dist x y| ≤ (b + s) / c := by
  obtain ⟨W, hWp, hWheight, hWdist⟩ := isEdgePoint.exists_local_half_plane_model (mX := mX.rescale c hc) h hbuffer
  refine ⟨fun x => c⁻¹ • W x, by change c⁻¹ • W p = 0; rw [hWp, smul_zero], ?_, ?_⟩
  · intro x
    change 0 ≤ c⁻¹ * (W x).snd
    exact mul_nonneg (inv_pos.mpr hc).le (hWheight x)
  · intro x hx y hy
    have hx' : @dist X (mX.rescale c hc).toDist x p < c * r :=
      mul_lt_mul_of_pos_left hx hc
    have hy' : @dist X (mX.rescale c hc).toDist y p < c * r :=
      mul_lt_mul_of_pos_left hy hc
    have hh := hWdist x hx' y hy'
    change |dist (W x) (W y) - c * dist x y| ≤ b + s at hh
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    have hid : c⁻¹ * dist (W x) (W y) - dist x y =
        (dist (W x) (W y) - c * dist x y) / c := by field_simp
    rw [hid, abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right hh hc.le

end GC.MetricGeometry
