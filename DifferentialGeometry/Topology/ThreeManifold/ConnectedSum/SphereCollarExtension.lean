import DifferentialGeometry.Topology.Manifold.SphereRadialSuspension
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BoundaryAttachmentCollarExtension
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected

set_option autoImplicit false

noncomputable section

open Set Metric Manifold Filter Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u v

theorem sphereCollarExtension_holds (N : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart N.toClosedOrientedManifold) : SphereCollarExtension N d := by
  intro f hf hiso
  obtain ⟨Jiso, hJiso, hJisoi, hJiso0, hJiso1⟩ := hiso
  let A : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      BoundaryAttachmentSphere BoundaryAttachmentSphere ∞ := fun t => Jiso (1 - t)
  have htime : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (1 - q.1, q.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hA : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => A q.1 q.2) :=
    hJiso.comp htime
  have hAi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (A q.1).symm q.2) :=
    hJisoi.comp htime
  have hA0 : A 0 = Diffeomorph.refl (𝓡 2) BoundaryAttachmentSphere ∞ := by
    change Jiso (1 - 0) = Diffeomorph.refl (𝓡 2) BoundaryAttachmentSphere ∞
    rw [sub_zero]
    exact hJiso1
  have hA1 : A 1 = f := by
    change Jiso (1 - 1) = f
    rw [sub_self]
    exact hJiso0
  obtain ⟨F, hFnrm, hFsmall, hFlarge, hFsphere⟩ :=
    Manifold.exists_sphereRadialSuspension (n := 2) (E := EuclideanSpace ℝ (Fin 3))
      A hA hAi hA0
  let e : OpenPartialHomeomorph N.Carrier (EuclideanSpace ℝ (Fin 3)) :=
    d.toBallChart.chart.symm.toOpenPartialHomeomorph
  have he : ContMDiffOn (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ e e.source :=
    d.toBallChart.chart.contMDiffOn_invFun
  have hei : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞ e.symm e.target :=
    d.toBallChart.chart.contMDiffOn_toFun
  have he_symm : ∀ z : EuclideanSpace ℝ (Fin 3), e.symm z = d.toBallChart.chart z :=
    fun _ => rfl
  have hD : ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => F q.2) :=
    (contMDiff_iff_contDiff.mp F.contMDiff).comp contDiff_snd
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => F.symm q.2) :=
    (contMDiff_iff_contDiff.mp F.symm.contMDiff).comp contDiff_snd
  have hK : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 2)) :=
    isCompact_closedBall 0 (3 / 2)
  have hKt : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 2) ⊆ e.target :=
    fun z hz => d.toBallChart.closedBall_subset_source
      (Metric.closedBall_subset_closedBall (by norm_num) hz)
  have hfix : ∀ p z, z ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 2) →
      (fun _ : ℝ => F) p z = z ∧ ((fun _ : ℝ => F) p).symm z = z := by
    intro p z hz
    have hlt : (3 : ℝ) / 2 < ‖z‖ := by
      by_contra hle
      exact hz (by rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.mp hle)
    refine ⟨hFlarge z (le_of_lt hlt), ?_⟩
    calc F.symm z = F.symm (F z) := by rw [hFlarge z (le_of_lt hlt)]
      _ = z := Diffeomorph.symm_apply_apply F z
  obtain ⟨Jf, -, -, hJfeq, -, -, -⟩ :=
    Manifold.exists_diffeomorph_extension_of_partial_chart_family (P := ℝ) e he hei
      (fun _ : ℝ => F) hD hDi hK hKt hfix
  have hEval : ∀ z ∈ e.target, (Jf 0) (e.symm z) = e.symm (F z) := by
    intro z hz
    rw [(hJfeq 0 (e.symm z)).1, Manifold.extendChartById, if_pos (e.map_target hz),
      e.right_inv hz]
  have hcenter : (0 : EuclideanSpace ℝ (Fin 3)) ∈ e.target :=
    d.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hnbhd : ∀ᶠ x in 𝓝 (e.symm 0), x ∈ e.source ∧ ‖e x‖ < 1 / 2 := by
    have hcont : ContinuousAt e (e.symm 0) :=
      e.continuousOn_toFun.continuousAt (e.open_source.mem_nhds (e.map_target hcenter))
    have hlt : ‖e (e.symm 0)‖ < 1 / 2 := by
      rw [e.right_inv hcenter]
      norm_num
    filter_upwards [e.open_source.mem_nhds (e.map_target hcenter),
      hcont.preimage_mem_nhds (isOpen_lt continuous_norm continuous_const |>.mem_nhds hlt)]
      with x hx1 hx2
    exact ⟨hx1, hx2⟩
  have hΨid : (Jf 0) =ᶠ[𝓝 (e.symm 0)] id := by
    filter_upwards [hnbhd] with x hx
    rw [(hJfeq 0 x).1, Manifold.extendChartById, if_pos hx.1,
      hFsmall (e x) (le_of_lt hx.2), e.left_inv hx.1]
    rfl
  have hball : (Jf 0) '' (d.toBallChart.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      = d.toBallChart.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have hzcb : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
        Metric.closedBall_subset_closedBall (show (1 : ℝ) ≤ 2 by norm_num)
          (Metric.ball_subset_closedBall hz)
      refine ⟨F z, ?_, ?_⟩
      · simpa [Metric.mem_ball, dist_zero_right, hFnrm] using hz'
      · exact (hEval z (d.toBallChart.closedBall_subset_source hzcb)).symm
    · rintro ⟨z, hz, rfl⟩
      have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have hsymmnrm : ‖F.symm z‖ = ‖z‖ := by
        rw [← hFnrm (F.symm z), Diffeomorph.apply_symm_apply]
      have hz2 : ‖F.symm z‖ < 1 := by rw [hsymmnrm]; exact hz'
      have hzball : F.symm z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz2
      have hzcb : F.symm z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
        Metric.closedBall_subset_closedBall (show (1 : ℝ) ≤ 2 by norm_num)
          (Metric.ball_subset_closedBall hzball)
      refine ⟨d.toBallChart.chart (F.symm z), ⟨F.symm z, hzball, rfl⟩, ?_⟩
      rw [← he_symm (F.symm z), hEval (F.symm z) (d.toBallChart.closedBall_subset_source hzcb),
        Diffeomorph.apply_symm_apply, he_symm z]
  have hsphere : ∀ v : BoundaryAttachmentSphere,
      (Jf 0) (d.toBallChart.chart (v : EuclideanSpace ℝ (Fin 3))) =
        d.toBallChart.chart ((f v : BoundaryAttachmentSphere) : EuclideanSpace ℝ (Fin 3)) := by
    intro v
    have hv : (v : EuclideanSpace ℝ (Fin 3)) ∈ e.target :=
      d.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right, norm_eq_of_mem_sphere v]
        norm_num)
    rw [← he_symm (v : EuclideanSpace ℝ (Fin 3)),
      hEval (v : EuclideanSpace ℝ (Fin 3)) hv, hFsphere v, hA1, he_symm _]
  exact ⟨Jf 0, Diffeomorph.preservesOrientation_of_eventuallyEq_id (Jf 0) hΨid, hball, hsphere⟩

theorem boundaryAttachmentCollarExtension_holds (N : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment)
    (hiso : BoundaryAttachmentIsotopic a a') :
    BoundaryAttachmentCollarExtension N d a a' :=
  boundaryAttachmentCollarExtension_of_sphereCollarExtension (sphereCollarExtension_holds N d) hiso

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_boundaryAttachmentCollarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment)
    (haa : BoundaryAttachmentIsotopic a a')
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c d) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c d a').toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  hsmooth a a' (boundaryAttachmentCollarExtension_holds N d a a' haa)

end DifferentialGeometry.Topology
