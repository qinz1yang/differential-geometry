import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

/-- A fine raw cap retains the scale bound of its actual original cutoff record. -/
theorem GeometricCutoffRecord.raw_scale_gt_of_recent_nominal_bound
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    {fixed : StaticCapScaffold} {Dbig ζ : ℝ} {m : ℕ}
    {b : (H.event i).RetainedBoundaryIndex}
    (raw : (H.event i).PresentedStaticCap fixed Dbig m ζ b)
    (hmatch : raw.neck.scale = (R.static b).neck.scale)
    (C Q r : ℝ) (hC : 1 ≤ C) (hQ : 0 < Q) (hr : 0 < r)
    (herror : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hnominal : ∀ h, R.nominalRadius h ≤ (1 / Real.sqrt (72 * C)) * r)
    (hceiling : Q ≤ (r ^ 2)⁻¹) :
    18 * C * Q < raw.neck.scale := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hnom := R.nominal_pos ⟨b.val.1⟩
  have hnom2 : (R.nominalRadius ⟨b.val.1⟩) ^ 2 ≤
      ((1 / Real.sqrt (72 * C)) * r) ^ 2 :=
    pow_le_pow_left₀ hnom.le (hnominal ⟨b.val.1⟩) 2
  have hsqrt2 : Real.sqrt (72 * C) ^ 2 = 72 * C :=
    Real.sq_sqrt (by positivity)
  have hnormalize : 72 * C * ((1 / Real.sqrt (72 * C)) * r) ^ 2 = r ^ 2 := by
    rw [mul_pow, one_div_pow, hsqrt2, ← mul_assoc,
      mul_one_div_cancel (by positivity : 72 * C ≠ 0), one_mul]
  have hscaled : 72 * C * (R.nominalRadius ⟨b.val.1⟩) ^ 2 ≤ r ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hnom2 (by positivity : 0 ≤ 72 * C)
    simpa only [hnormalize] using h
  have hQr : Q * r ^ 2 ≤ 1 := by
    rw [inv_eq_one_div] at hceiling
    exact (le_div_iff₀ (sq_pos_of_pos hr)).mp hceiling
  have hbudget : 72 * C * Q * (R.nominalRadius ⟨b.val.1⟩) ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hscaled hQ.le
    nlinarith only [h, hQr]
  have hscale : 72 * C * Q ≤ (R.neck b.val.1).scale := by
    rw [R.scale_eq, inv_eq_one_div]
    exact (le_div_iff₀ (sq_pos_of_pos hnom)).mpr hbudget
  have hlocalError : p.recenterConstant * R.delta b.val.1 ≤ 1 / 2 := by
    have hc : 0 ≤ p.recenterConstant := le_trans (by norm_num) p.recenterConstant_ge_four
    exact (mul_le_mul_of_nonneg_left (R.delta_le _) hc).trans herror
  have hcomp := (abs_le.mp (R.recenter_scale_comparison b)).1
  have hratio : 1 / 2 ≤ (R.static b).neck.scale / (R.neck b.val.1).scale := by
    linarith only [hcomp, hlocalError]
  have hlow := (le_div_iff₀ (R.neck b.val.1).scale_pos).mp hratio
  rw [hmatch]
  nlinarith only [hscale, hlow, mul_pos hCpos hQ]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
