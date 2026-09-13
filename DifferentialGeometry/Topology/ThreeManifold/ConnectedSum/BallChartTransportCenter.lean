import DifferentialGeometry.Analysis.ODE.Flow.Planar.LinearGermRealization
import DifferentialGeometry.Topology.Manifold.BallChartScale
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransitionDet

set_option autoImplicit false
noncomputable section
open Set Metric Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3}

theorem ballChartTransport_of_center_eq (c c' : OrientedBallChart M)
    (hc : c.chart (0 : E3) = c'.chart (0 : E3)) :
    Manifold.BallChartTransport c.toBallChart c'.toBallChart := by
  have h0 : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have h0' : (0 : E3) ∈ c'.chart.source :=
    c'.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hdet : 0 < (fderiv ℝ (fun x : E3 => c.chart.symm (c'.chart x)) (0 : E3)).det :=
    det_fderiv_chartTransition_pos c' c hc.symm
  let Q : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ := c'.chart.trans c.chart.symm
  have hQfun : Q.toFun = fun x : E3 => c.chart.symm (c'.chart x) := rfl
  have hQ0 : (0 : E3) ∈ Q.source := by
    change (0 : E3) ∈ (c'.chart.toOpenPartialHomeomorph.trans
      c.chart.symm.toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨h0', ?_⟩
    change c'.chart (0 : E3) ∈ c.chart.target
    rw [← hc]
    exact c.chart.map_source h0
  have hQsource : Q.source ⊆ c'.chart.source := by
    intro x hx
    change x ∈ (c'.chart.toOpenPartialHomeomorph.trans
      c.chart.symm.toOpenPartialHomeomorph).source at hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx.1
  have hUopen : IsOpen (Q.source ∩ Metric.ball (0 : E3) 1) :=
    Q.open_source.inter isOpen_ball
  have hU0 : (0 : E3) ∈ Q.source ∩ Metric.ball (0 : E3) 1 :=
    ⟨hQ0, Metric.mem_ball_self (by norm_num)⟩
  have hcont : ContDiffOn ℝ ∞ (fun x : E3 => c.chart.symm (c'.chart x))
      (Q.source ∩ Metric.ball (0 : E3) 1) :=
    (Q.contMDiffOn_toFun.mono inter_subset_left).contDiffOn
  have hψ0 : (fun x : E3 => c.chart.symm (c'.chart x)) 0 = 0 := by
    change c.chart.symm (c'.chart (0 : E3)) = (0 : E3)
    rw [← hc]
    exact c.chart.left_inv h0
  obtain ⟨K, hKU, hR⟩ :=
    DifferentialGeometry.Analysis.exists_realizesGerm_of_contDiffOn_det_pos (n := 3)
      hUopen hU0 hcont hψ0 hdet
  obtain ⟨-, hKcomp, D, hDc, hDic, hD0, hDg, hDfix⟩ := hR
  have hfix : ∀ z ∉ (Metric.closedBall (0 : E3) 2 ∪ K),
      (D 1) z = z ∧ (D 1).symm z = z := fun z hz => hDfix 1 z hz
  have hKt : Metric.closedBall (0 : E3) 2 ∪ K ⊆ c'.chart.source := by
    rintro z (hz | hz)
    · exact c'.closedBall_subset_source hz
    · exact hQsource (hKU hz).1
  have hnhds : {z : E3 | (D 1) z = (fun x : E3 => c.chart.symm (c'.chart x)) z} ∈ 𝓝 0 :=
    hDg
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have htarget : c'.chart.target ∈ 𝓝 (c.chart (0 : E3)) := by
    have h := c'.chart.open_target.mem_nhds (c'.chart.map_source h0')
    rw [← hc] at h
    exact h
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := exists_pos_image_ball_subset c.toBallChart htarget
  have hchart0 : c'.chart (0 : E3) = c.chart (0 : E3) := hc.symm
  have hφ0 : c'.chart.symm (c.chart (0 : E3)) = (0 : E3) := by
    rw [hc]
    exact c'.chart.left_inv h0'
  have hφcont : ContinuousAt (fun x : E3 => c'.chart.symm (c.chart x)) 0 := by
    have h1 : ContinuousAt (fun y : M.Carrier => c'.chart.symm y) (c.chart (0 : E3)) :=
      c'.chart.contMDiffOn_invFun.continuousOn.continuousAt
        (c'.chart.open_target.mem_nhds (by rw [hc]; exact c'.chart.map_source h0'))
    have h2 : ContinuousAt (fun x : E3 => c.chart x) (0 : E3) :=
      c.chart.contMDiffOn_toFun.continuousOn.continuousAt (c.chart.open_source.mem_nhds h0)
    exact h1.comp h2
  obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ :=
    exists_pos_image_ball_subset_of_continuousAt hφcont hφ0 hδpos
  let ρ : ℝ := min (min ρ₁ ρ₂) 1
  have hρpos : 0 < ρ := lt_min (lt_min hρ₁pos hρ₂pos) (by norm_num)
  have hρ₁ : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ₂ : ρ ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hover : ∀ x ∈ Metric.ball (0 : E3) ρ, c.chart x ∈ c'.chart.target :=
    fun x hx => hρ₁sub ⟨x, Metric.ball_subset_ball hρ₁ hx, rfl⟩
  have hact : ∀ x ∈ Metric.ball (0 : E3) ρ, (D 1) (c'.chart.symm (c.chart x)) = x := by
    intro x hx
    have hz : c'.chart.symm (c.chart x) ∈ Metric.ball (0 : E3) δ :=
      hρ₂sub ⟨x, Metric.ball_subset_ball hρ₂ hx, rfl⟩
    have hx1 : x ∈ Metric.ball (0 : E3) 1 := Metric.ball_subset_ball hρ1 hx
    rw [hδsub hz]
    change c.chart.symm (c'.chart (c'.chart.symm (c.chart x))) = x
    erw [c'.chart.right_inv' (hover x hx)]
    exact c.chart.left_inv (c.ball_subset_source hx1)
  obtain ⟨Φ, hΦ⟩ :=
    exists_diffeomorph_eqOn_of_modelDiffeomorph (c := c.toBallChart) (c' := c'.toBallChart)
      (D := D 1) (K := Metric.closedBall (0 : E3) 2 ∪ K) (S := Metric.ball (0 : E3) ρ)
      hKcomp hKt hfix hover hact
  let a : ℝ := min (ρ / 4) (1 / 2)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have ha1 : a ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have ha2 : 2 * a < ρ := by
    have h1 : a ≤ ρ / 4 := min_le_left _ _
    linarith
  refine Manifold.BallChartTransport.trans
    (Manifold.BallChartTransport.trans (ballChartTransport_scale c.toBallChart a ha ha1) ?_)
    (ballChartTransport_scale c'.toBallChart a ha ha1).symm
  refine ⟨Φ, fun x hx => ?_⟩
  have hxmem : a • x ∈ Metric.ball (0 : E3) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    nlinarith
  rw [BallChart.scale_apply', hΦ (a • x) hxmem, BallChart.scale_apply']

end DifferentialGeometry.Topology
