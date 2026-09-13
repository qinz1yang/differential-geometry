import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportCenter
import DifferentialGeometry.Topology.Manifold.BallChartPalaisTransport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedChartPullback

set_option autoImplicit false
noncomputable section
open Set Metric Manifold Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

theorem preservesOrientation_of_eventuallyEq_id {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [PreconnectedSpace M] {o : DifferentialGeometry.ManifoldOrientation (𝓡 3) M 3}
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) {x₀ : M} (h : Φ =ᶠ[𝓝 x₀] id) :
    Φ.preservesOrientation o o := by
  obtain ⟨s, hs, hse⟩ := h.exists_mem
  have hx₀ : Φ x₀ = x₀ := hse (mem_of_mem_nhds hs)
  refine preservesOrientation_of_eq_at Φ o o x₀ ?_
  have heq : (Φ.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
      = LinearEquiv.refl ℝ (TangentSpace (𝓡 3) x₀) := by
    ext v
    change mfderiv (𝓡 3) (𝓡 3) (⇑Φ) x₀ v = v
    rw [Filter.EventuallyEq.mfderiv_eq h, mfderiv_id]
    rfl
  rw [heq, hx₀]
  exact congrArg (fun q => q (o.orientation x₀))
    (Orientation.map_refl (ι := Fin 3) (R := ℝ) (M := TangentSpace (𝓡 3) x₀))

end Diffeomorph

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_preservesOrientation_diffeomorph_apply_eq_of_mem_nhds {M : Type*}
    [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    [PreconnectedSpace M] (o : ManifoldOrientation (𝓡 3) M 3) (x : M) :
    ∃ t ∈ 𝓝 x, ∀ z ∈ t, ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
      Φ.preservesOrientation o o ∧ Φ x = z := by
  let φ : PartialDiffeomorph (𝓡 3) 𝓘(ℝ, E3) M E3 ∞ :=
    DifferentialGeometry.PartialDiffeomorph.extChartAt (𝓡 3) ∞ x
  let e : OpenPartialHomeomorph M E3 := φ.toOpenPartialHomeomorph
  have hxsrc : x ∈ e.source := by
    dsimp only [e, φ, DifferentialGeometry.PartialDiffeomorph.extChartAt]
    exact mem_extChartAt_source x
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ Metric.closedBall (e x) R ⊆ e.target := by
    obtain ⟨ρ, hρpos, hρsub⟩ :=
      Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hxsrc))
    exact ⟨ρ / 2, by linarith,
      fun y hy => hρsub (Metric.closedBall_subset_ball (by linarith) hy)⟩
  have hroom : ∃ y₀ ∈ e.target, y₀ ∉ Metric.closedBall (e x) R := by
    obtain ⟨v, hv⟩ : ∃ v : E3, v ≠ 0 := ⟨EuclideanSpace.single 0 1, by simp⟩
    have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E3 := (‖v‖)⁻¹ • v
    have hwn : ‖w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvn),
        inv_mul_cancel₀ (ne_of_gt hvn)]
    have hnorm (s : ℝ) (hs : 0 < s) : ‖s • w‖ = s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hwn, mul_one]
    have hs : e x + R • w ∈ Metric.closedBall (e x) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h : e x + R • w - e x = R • w := by abel
      rw [h, hnorm R hRpos]
    have hst : e x + R • w ∈ e.target := hRsub hs
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hst)
    refine ⟨e x + R • w + (δ / 2) • w, hδsub ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h : e x + R • w + (δ / 2) • w - (e x + R • w) = (δ / 2) • w := by abel
      rw [h, hnorm (δ / 2) (by linarith)]
      linarith
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : e x + R • w + (δ / 2) • w - e x = R • w + (δ / 2) • w := by abel
      have h2 : R • w + (δ / 2) • w = (R + δ / 2) • w := (add_smul R (δ / 2) w).symm
      rw [h1, h2, hnorm (R + δ / 2) (by linarith)]
      linarith
  obtain ⟨y₀, hy₀t, hy₀K⟩ := hroom
  have hx₀ : e.symm y₀ ∉ e.symm '' Metric.closedBall (e x) R := by
    rintro ⟨y, hyK, hyy⟩
    have hyt : y ∈ e.target := hRsub hyK
    have heq : y = y₀ := by
      have h1 : e.symm y = e.symm y₀ := by rw [hyy]
      calc y = e (e.symm y) := (e.right_inv' hyt).symm
        _ = e (e.symm y₀) := by rw [h1]
        _ = y₀ := e.right_inv' hy₀t
    exact hy₀K (heq ▸ hyK)
  let t : Set M := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have htopen : IsOpen t := by simpa only [t] using e.isOpen_inter_preimage isOpen_ball
  have hxt : x ∈ t := ⟨hxsrc, Metric.mem_ball_self hRpos⟩
  refine ⟨t, htopen.mem_nhds hxt, ?_⟩
  rintro z ⟨hzsrc, hzball⟩
  have hznorm : ‖e z - e x‖ < R := by
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hzball
    exact hzball
  obtain ⟨D, hmove, hfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_translate_on_closedBall
      (e x) (e z) (r := 0) (R := R) le_rfl (by simpa using hznorm)
  have hD0 : D (e x) = e z := by
    have h := hmove (e x) (Metric.mem_closedBall_self le_rfl)
    simpa using h
  obtain ⟨J, -, -, hJ, hJK, -, hJfix⟩ :=
    Manifold.exists_diffeomorph_extension_of_partial_chart_family e φ.contMDiffOn_toFun
      φ.contMDiffOn_invFun (fun _ : ℝ => D)
      (D.contDiff.comp contDiff_snd) (D.symm.contDiff.comp contDiff_snd)
      (isCompact_closedBall (e x) R) hRsub (fun _ y hy => hfix y hy)
  have hJx : J 1 x = z := by
    rw [(hJ 1 x).1, Manifold.extendChartById, if_pos hxsrc, hD0, e.left_inv hzsrc]
  have hJeq : (J 1) =ᶠ[𝓝 (e.symm y₀)] id := by
    have hopen : IsOpen (e.symm '' Metric.closedBall (e x) R)ᶜ := hJK.isClosed.isOpen_compl
    exact Filter.eventually_of_mem (hopen.mem_nhds hx₀) fun y hy => (hJfix 1 y hy).1
  exact ⟨J 1, Diffeomorph.preservesOrientation_of_eventuallyEq_id (J 1) hJeq, hJx⟩

theorem exists_preservesOrientation_diffeomorph_apply_eq {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M] [ConnectedSpace M]
    (o : ManifoldOrientation (𝓡 3) M 3) (a b : M) :
    ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞, Φ.preservesOrientation o o ∧ Φ a = b := by
  let S : Set M := {y | ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
    Φ.preservesOrientation o o ∧ Φ a = y}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨t, ht, ht'⟩ := exists_preservesOrientation_diffeomorph_apply_eq_of_mem_nhds o y
    refine Filter.mem_of_superset ht ?_
    rintro z hz
    obtain ⟨Ψ, hΨo, hΨ⟩ := ht' z hz
    obtain ⟨Φ, hΦo, hΦ⟩ := hy
    exact ⟨Φ.trans Ψ, Diffeomorph.preservesOrientation_trans hΦo hΨo, by
      rw [Diffeomorph.coe_trans, Function.comp_apply, hΦ, hΨ]⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨t, ht, ht'⟩ := exists_preservesOrientation_diffeomorph_apply_eq_of_mem_nhds o y
    refine Filter.mem_of_superset ht ?_
    rintro z hz hzS
    obtain ⟨Ψ, hΨo, hΨ⟩ := ht' z hz
    obtain ⟨Φ, hΦo, hΦ⟩ := hzS
    exact hy ⟨Φ.trans Ψ.symm,
      Diffeomorph.preservesOrientation_trans hΦo (Diffeomorph.preservesOrientation_symm hΨo),
      by rw [Diffeomorph.coe_trans, Function.comp_apply, hΦ, ← hΨ,
        Diffeomorph.symm_apply_apply]⟩
  have huniv : S = Set.univ := by
    rcases isClopen_iff.mp (⟨hSclosed, hSopen⟩ : IsClopen S) with h | h
    · exfalso
      have ha : a ∈ S := ⟨Diffeomorph.refl (𝓡 3) M ∞,
        Diffeomorph.preservesOrientation_refl o, rfl⟩
      rw [h] at ha
      exact ha
    · exact h
  have hb : b ∈ S := huniv ▸ Set.mem_univ b
  exact hb

theorem ballChartTransport_of_orientedBallCharts (M : ConnectedClosedOrientedManifold.{u} 3)
    (c c' : OrientedBallChart M.toClosedOrientedManifold) :
    Manifold.BallChartTransport c.toBallChart c'.toBallChart := by
  obtain ⟨Φ₀, hΦ₀o, hΦ₀⟩ := exists_preservesOrientation_diffeomorph_apply_eq
    M.toClosedOrientedManifold.orientation (c.chart (0 : E3)) (c'.chart (0 : E3))
  obtain ⟨c'', hc''⟩ :=
    exists_orientedBallChart_pullback_of_preservesOrientation c' Φ₀ hΦ₀o
  have hcenter : c''.chart (0 : E3) = c.chart (0 : E3) := by
    have h1 := hc'' 0 (Metric.mem_closedBall_self (by norm_num))
    have h2 : c''.chart (0 : E3) = Φ₀.symm (c'.chart (0 : E3)) := by
      rw [← h1, Diffeomorph.symm_apply_apply]
    rw [h2, ← hΦ₀, Diffeomorph.symm_apply_apply]
  exact (ballChartTransport_of_center_eq c c'' hcenter.symm).trans ⟨Φ₀, hc''⟩

theorem connectedBallChartTransport_holds : connectedBallChartTransport.{u} :=
  fun M c c' => ballChartTransport_of_orientedBallCharts M c c'

theorem selfTransport_holds : SelfTransport.{u} :=
  selfTransport_of_connectedBallChartTransport connectedBallChartTransport_holds

theorem connectedSum_unorientedTransport_holds : connectedSumUnorientedTransport.{u} :=
  connectedSum_unorientedTransport_of_selfTransport selfTransport_holds

theorem connectedSum_transport_right_holds (M P P' : ConnectedClosedOrientedManifold.{u} 3)
    (Ψ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΨ : Ψ.preservesOrientation P.orientation P'.orientation) :
    Nonempty ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) :=
  connectedSum_transport_right_of_orientedPullback selfTransport_holds orientedBallChartPullback
    M P P' Ψ hΨ

theorem connectedSum_transport_left_holds (M M' Q : ConnectedClosedOrientedManifold.{u} 3)
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    Nonempty ((connectedSum M Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M' Q).toClosedOrientedManifold.Carrier) :=
  connectedSum_transport_left_of_orientedPullback selfTransport_holds orientedBallChartPullback
    M M' Q Φ hΦ

end DifferentialGeometry.Topology
