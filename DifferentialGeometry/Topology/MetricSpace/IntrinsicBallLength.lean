import DifferentialGeometry.Topology.MetricSpace.IntrinsicVariation
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallTopology

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace Metric

theorem intrinsicBallMetricSpace_arbitrarily_short_curves
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) (a b : ball o L) {ε : ℝ} (hε : 0 < ε) :
    let m := intrinsicBallMetricSpace hcurves o hL
    ∃ c : unitInterval → ball o L,
      @Continuous unitInterval (ball o L) inferInstance
        m.toUniformSpace.toTopologicalSpace c ∧ c 0 = a ∧ c 1 = b ∧
      @eVariationOn unitInterval inferInstance (ball o L)
        m.toUniformSpace.toTopologicalSpace
        (@PseudoEMetricSpace.toWeakPseudoEMetricSpace (ball o L)
          m.toPseudoEMetricSpace) c univ <
        ENNReal.ofReal (@dist (ball o L) m.toDist a b + ε) := by
  dsimp only
  have hfinite : intrinsicEDist a b ≠ ⊤ :=
    (intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves hcurves o hL a b).ne
  have hnear : intrinsicEDist a b <
      ENNReal.ofReal ((intrinsicEDist a b).toReal + ε) := by
    calc
      intrinsicEDist a b = ENNReal.ofReal (intrinsicEDist a b).toReal :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ < ENNReal.ofReal ((intrinsicEDist a b).toReal + ε) := by
        exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hnear
  refine ⟨γ, ?_, γ.source, γ.target, ?_⟩
  · rw [intrinsicBallMetricSpace_toTopology hcurves o hL]
    exact γ.continuous
  · rw [intrinsicBallMetricSpace_dist]
    change @eVariationOn unitInterval inferInstance (ball o L)
      (intrinsicMetricSpace (ball o L) _).toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace (ball o L)
        (intrinsicMetricSpace (ball o L) _).toPseudoEMetricSpace) γ univ < _
    rw [intrinsicMetricSpace_eVariationOn _ γ.continuous]
    exact hγ

end Metric
