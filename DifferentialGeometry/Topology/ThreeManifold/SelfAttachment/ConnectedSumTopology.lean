import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumCommutation
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.PositiveModel
import DifferentialGeometry.Topology.Manifold.OrientedChartInOpen
import DifferentialGeometry.Topology.Manifold.OrientedBallChartMap
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

universe u

variable (M : ConnectedClosedOrientedManifold.{u} 3)

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_sphere_right
    (m : OrientedBallChart M.toClosedOrientedManifold)
    (e : OrientedBallChart standardThreeSphere.toClosedOrientedManifold) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M standardThreeSphere m e boundaryAttachment).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      M.toClosedOrientedManifold) := by
  obtain ⟨h₁⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts m (orientedBallChart M)
    e (orientedBallChart standardThreeSphere) boundaryAttachment
  have hsphere : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M standardThreeSphere).toClosedOrientedManifold M.toClosedOrientedManifold) := by
    obtain ⟨h⟩ := nonempty_orientedDiffeomorph_connectedSum_sphere_right_unit M
    let eLift : ClosedOrientedManifold.OrientedDiffeomorph standardThreeSphere.toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold :=
      ClosedOrientedManifold.uliftOrientedDiffeomorph standardThreeSphere.toClosedOrientedManifold
    let dl := orientedBallChart standardThreeSphereLift.{u}
    let d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold :=
      { chart := compPartialDiffeomorph dl.chart eLift.val.symm
        closedBall_subset_source := dl.closedBall_subset_source
        preserves_orientation := preservesOrientation_compPartialDiffeomorph dl.chart
          standardThreeSphereLift.orientation standardThreeSphere.orientation eLift.val.symm
          (Diffeomorph.preservesOrientation_symm eLift.property) dl.preserves_orientation }
    have hd (x : E3) (_hx : x ∈ Metric.closedBall (0 : E3) 2) : eLift.val (d.chart x) = dl.chart x :=
      eLift.val.apply_symm_apply _
    obtain ⟨h₀⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart
      (orientedBallChart M) (orientedBallChart standardThreeSphere) d boundaryAttachment
    obtain ⟨h₁'⟩ := csTransport_diffeomorph_preservesOrientation
      (orientedBallChart M) (orientedBallChart M) d (orientedBallChart standardThreeSphereLift.{u})
      boundaryAttachment (Diffeomorph.refl (𝓡 3) M.Carrier ∞) eLift.val
      (fun _ _ => rfl) hd (Diffeomorph.preservesOrientation_refl M.orientation)
    let h' := h₀.trans h₁'
    exact ⟨h'.trans h⟩
  obtain ⟨h₂⟩ := hsphere
  exact ⟨h₁.trans h₂⟩


theorem nonempty_selfAttachment_homeomorph_connectedSum_sphereProduct
    (p q : OrientedBallChart M.toClosedOrientedManifold)
    (hpq : Disjoint (p.chart '' Metric.closedBall 0 2) (q.chart '' Metric.closedBall 0 2)) :
    Nonempty (SelfAttachment.Quotient p.toBallChart q.toBallChart hpq
      Manifold.antipodalAttachment.toHomeomorph ≃ₜ (connectedSum M sphereTwoTimesCircleLift).Carrier) := by
  let P : S3 := Classical.choice (inferInstance : Nonempty S3)
  obtain ⟨c, d, hcd, D, hI, h0, h1, B, hc, hd, O, F, hmark⟩ := exists_positive_sphere_selfAttachment_model P
  let R := Manifold.sphereSelfAttachmentManifold P Manifold.antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl Manifold.sphereMappingTorusIsotopyRefl_target O
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let Q := R.pullback H
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd
      Manifold.antipodalAttachment.toHomeomorph) := Q.charts
  let _ : IsManifold (𝓡 3) ∞ Q.Carrier := Q.smooth
  obtain ⟨e, hec, hed⟩ := exists_orientedBallChart_disjoint_pair standardThreeSphere c d hcd
  have heavoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1 := by
    intro x hx h
    rcases h with h | h
    · exact Set.disjoint_left.mp hec ⟨x, hx, rfl⟩
        (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) h)
    · exact Set.disjoint_left.mp hed ⟨x, hx, rfl⟩
        (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) h)
  obtain ⟨eP, heP⟩ := hmark e heavoid
  obtain ⟨eQ, heQ⟩ := exists_orientedBallChart_pullback_of_preservesOrientation eP F.val F.property
  have heQcore : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
        eQ.chart x = SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd
          Manifold.antipodalAttachment.toHomeomorph ⟨e.chart x, hx⟩ := by
    intro x hx
    obtain ⟨hx', hmap⟩ := heP x hx
    refine ⟨hx', F.val.injective ?_⟩
    exact (heQ x hx).trans hmap
  let m := orientedBallChart M
  obtain ⟨cS, dS, hcS, hdS, hcdS⟩ := ConnectedSumQuotient.exists_orientedBallChart_pair_inr
    m e boundaryAttachment c d
    (hec.symm.mono_right (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))))
    (hed.symm.mono_right (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)))) hcd
  let S := (smoothConnectedSum M standardThreeSphere m e boundaryAttachment).toConnectedClosedOrientedManifold
  obtain ⟨U⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_sphere_right M m e
  let cM := cS.map U
  let dM := dS.map U
  have hcdM := cS.disjoint_map_closedBall dS U hcdS
  obtain ⟨V, hV, hVp, hVq⟩ := exists_oriented_diffeomorph_ballPair p q cM dM hpq hcdM
  let E := V.trans U.val.symm
  have hEp (x : E3) (hx : x ∈ Metric.closedBall (0 : E3) 2) : E (p.chart x) = cS.chart x := by
    change U.val.symm (V (p.chart x)) = _
    rw [hVp x hx]
    exact U.val.symm_apply_apply _
  have hEq (x : E3) (hx : x ∈ Metric.closedBall (0 : E3) 2) : E (q.chart x) = dS.chart x := by
    change U.val.symm (V (q.chart x)) = _
    rw [hVq x hx]
    exact U.val.symm_apply_apply _
  let H₁ := SelfAttachment.homeomorphOfChartTransport p.toBallChart q.toBallChart cS.toBallChart dS.toBallChart
    hpq hcdS E.toHomeomorph hEp hEq Manifold.antipodalAttachment.toHomeomorph
  let H₂ := selfAttachmentConnectedSumHomeomorph m e c d boundaryAttachment hec hed hcd cS dS hcS hdS hcdS
    Manifold.antipodalAttachment.toHomeomorph eQ.toBallChart heQcore
  obtain ⟨G⟩ := csTransport_diffeomorph_preservesOrientation m m eQ eP boundaryAttachment
    (Diffeomorph.refl (𝓡 3) M.Carrier ∞) F.val (fun _ _ => rfl) heQ
    (Diffeomorph.preservesOrientation_refl M.orientation)
  obtain ⟨K⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts m (orientedBallChart M)
    eP (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment
  exact ⟨((H₁.trans H₂).trans G.val.toHomeomorph).trans K.val.toHomeomorph⟩

end DifferentialGeometry.Topology
