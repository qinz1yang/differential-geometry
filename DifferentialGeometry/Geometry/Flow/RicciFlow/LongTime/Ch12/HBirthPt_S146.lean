import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HBirthReduce_S134

/-!
# CH12-S146, group 1b: the per-point P2 half of `hbirth_of_hsurv_S134`

`hbirth_pt_S146`: if a point `A.point first` of a forward trace ending at `yf` has scalar bounded below by
`c₀ q` (`q` = the neck scale of a cap window) and `scalar · (s.time - time first) ≤ 1`, and the end `yf` has scalar
`≤ C0/ρ²` with `ρ ≤ neckRadius s.time`, then `q ≤ (1+Ctime) max C0 1 / c₀ / ρ²`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

theorem hbirth_pt_S146 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) {ρ C0 c₀ q : ℝ} (hρ : 0 < ρ) (hc₀ : 0 < c₀) (hq : 0 < q)
    (hρN : ρ ≤ Hp.parameters.neckRadius s.time)
    (first : Fin ((sliceHistoryR_O3 F s).eventCount + 1))
    (hle : first ≤ Fin.last (sliceHistoryR_O3 F s).eventCount) (yf : s.stage.Carrier)
    (hyf : metricScalarAt s.metric yf ≤ C0 / ρ ^ 2)
    (A : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory first
      (Fin.last (sliceHistoryR_O3 F s).eventCount) hle yf)
    (hlow : c₀ * q ≤ metricScalarAt ((sliceHistoryR_O3 F s).initialMetric first) (A.point first le_rfl hle))
    (haT : metricScalarAt ((sliceHistoryR_O3 F s).initialMetric first) (A.point first le_rfl hle) *
      (s.time - (sliceHistoryR_O3 F s).time first) ≤ 1) :
    q ≤ (1 + Ctime) * max C0 1 / c₀ / ρ ^ 2 := by
  have hnr : 0 < Hp.parameters.neckRadius s.time := Hp.parameters.neckRadius_pos _ s.positive.le
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hm : 0 < max C0 1 := lt_max_of_lt_right one_pos
  have hq₀ : 0 < max C0 1 / ρ ^ 2 := by positivity
  have hqth : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ max C0 1 / ρ ^ 2 := by
    calc (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (ρ ^ 2)⁻¹ :=
          inv_anti₀ hρ2 (pow_le_pow_left₀ hρ.le hρN 2)
      _ = 1 / ρ ^ 2 := (one_div _).symm
      _ ≤ max C0 1 / ρ ^ 2 := by gcongr; exact le_max_right _ _
  have hfwd := fwd_scalar_lower_S134 Hp s Ctime hP2 hq₀ hqth first hle yf A
  set a : ℝ := metricScalarAt ((sliceHistoryR_O3 F s).initialMetric first) (A.point first le_rfl hle)
    with ha
  have hapos : 0 < a := lt_of_lt_of_le (mul_pos hc₀ hq) hlow
  have hml := maxlower_S134 (q₀ := max C0 1 / ρ ^ 2) hapos hq₀ Ctime.coe_nonneg haT hfwd
  have hmax : max (max C0 1 / ρ ^ 2) (metricScalarAt s.metric yf) ≤ max C0 1 / ρ ^ 2 :=
    max_le le_rfl (hyf.trans (by gcongr; exact le_max_left _ _))
  have hfin : a ≤ (1 + Ctime) * (max C0 1 / ρ ^ 2) := by
    have := hml.trans hmax
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  have hc : c₀ * q ≤ (1 + Ctime) * (max C0 1 / ρ ^ 2) := hlow.trans hfin
  rw [le_div_iff₀ hρ2, le_div_iff₀ hc₀]
  have e2 : (1 + (Ctime : ℝ)) * max C0 1 = (1 + Ctime) * (max C0 1 / ρ ^ 2) * ρ ^ 2 := by
    field_simp
  rw [e2]
  have := mul_le_mul_of_nonneg_right hc hρ2.le
  nlinarith only [this]

end GC.LongTime.Ch12
