import DifferentialGeometry.Geometry.Comparison.CenteredPairedChart
import DifferentialGeometry.Topology.MetricSpace.CompactChart

set_option autoImplicit false

open Set Metric Real
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_compact_closedBall_in_open_set
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω O : Set X} (hcomp : fourPointComparison 1 Ω) (hOΩ : O ⊆ Ω)
    (hO : IsOpen O) (hOne : O.Nonempty)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH Ω ≤ n) :
    ∃ q ∈ O, ∃ s : ℝ, 0 < s ∧ closedBall q s ⊆ O ∧ IsCompact (closedBall q s) := by
  obtain ⟨m, _, _, q, hq, _, _, r, hr, hBO, U, _, e, _, _, hlo, hhi⟩ :=
    exists_centered_distance_chart_in_open_set hcurves hcomp hOΩ hO hOne hcomplete hn hdim
  obtain ⟨R, hR, hRc⟩ := hcomplete q (hOΩ hq)
  let s := min (r / 2) R
  have hs : 0 < s := lt_min (half_pos hr) hR
  have hsr : s < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hsR : s ≤ R := min_le_right _ _
  have hsc : IsComplete (closedBall q s) := by
    intro f hf hfs
    obtain ⟨x, _, hfx⟩ := hRc f hf (hfs.trans (Filter.principal_mono.mpr (closedBall_subset_closedBall hsR)))
    exact ⟨x, isClosed_iff_clusterPt.mp isClosed_closedBall x
      (hf.1.mono (le_inf hfx hfs)), hfx⟩
  let f : ball q r → PiLp 2 (fun _ : Fin m => ℝ) := fun x => e x
  let L : ℝ≥0 := ⟨pairedChartDistortion n, (pairedChartDistortion_pos n).le⟩
  have hfLip : LipschitzWith L f := LipschitzWith.of_dist_le_mul hhi
  refine ⟨q, hq, s, hs, (closedBall_subset_ball hsr).trans hBO, ?_⟩
  exact isCompact_closedBall_of_chart hsr hsc (ε := L⁻¹)
    (inv_pos.mpr (show 0 < L from pairedChartDistortion_pos n)) hfLip hlo

end DifferentialGeometry.Geometry.Comparison.Toponogov
