import DifferentialGeometry.Topology.LoopSpace.Lipschitz



noncomputable section

open scoped NNReal ENNReal

namespace DifferentialGeometry.Topology

variable {Q : Type*} [PseudoEMetricSpace Q]



theorem cylinder_lipschitz_of_lift {F : ℝ × loopCircle → Q} {K : ℝ≥0}
    (hF : LipschitzWith K (fun p : ℝ × ℝ => F (p.1, (p.2 : loopCircle)))) :
    LipschitzWith (K + K) F := by
  have htime (θ : loopCircle) : LipschitzWith K (fun v : ℝ => F (v, θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    intro v w
    simpa only [Prod.edist_eq, edist_self, max_eq_left (show (0 : ℝ≥0∞) ≤ edist v w from bot_le)] using hF (v, t) (w, t)
  have hcircle (v : ℝ) : LipschitzWith K (fun θ : loopCircle => F (v, θ)) := by
    apply loop_lipschitz_of_lift
    intro s t
    simpa only [Prod.edist_eq, edist_self, max_eq_right (show (0 : ℝ≥0∞) ≤ edist s t from bot_le)] using hF (v, s) (v, t)
  exact LipschitzWith.uncurry htime hcircle

end DifferentialGeometry.Topology
