import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumTopology
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.PositiveSmoothModel
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumSmooth
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.SmoothTransport
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.RetainedChart

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

variable (M : ConnectedClosedOrientedManifold.{u} 3)
  (p q : OrientedBallChart M.toClosedOrientedManifold)
  (hpq : Disjoint (p.chart '' Metric.closedBall 0 2) (q.chart '' Metric.closedBall 0 2))

theorem exists_smoothSelfAttachment_orientedDiffeomorph :
    ∃ s : SmoothSelfAttachment p q hpq boundaryAttachment,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold) := by
  let P : S3 := Classical.choice (inferInstance : Nonempty S3)
  obtain ⟨c, d, hcd, s₀, ⟨F₀⟩⟩ := exists_positive_sphere_smoothSelfAttachment P
  let Q := s₀.toConnectedClosedOrientedManifold
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd boundaryAttachment.val.toHomeomorph) := s₀.charts
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
  obtain ⟨eQ, heQcore⟩ := s₀.exists_orientedBallChart_core e heavoid
  let eP := eQ.map F₀
  have heQ (x : E3) (_hx : x ∈ Metric.closedBall (0 : E3) 2) : F₀.val (eQ.chart x) = eP.chart x := rfl
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
  let E : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold S.toClosedOrientedManifold :=
    ClosedOrientedManifold.OrientedDiffeomorph.trans
      (⟨V, hV⟩ : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold M.toClosedOrientedManifold) U.symm
  have hEp (x : E3) (hx : x ∈ Metric.closedBall (0 : E3) 2) : E.val (p.chart x) = cS.chart x := by
    change U.val.symm (V (p.chart x)) = _
    rw [hVp x hx]
    exact U.val.symm_apply_apply _
  have hEq (x : E3) (hx : x ∈ Metric.closedBall (0 : E3) 2) : E.val (q.chart x) = dS.chart x := by
    change U.val.symm (V (q.chart x)) = _
    rw [hVq x hx]
    exact U.val.symm_apply_apply _
  let s₁ := smoothSelfAttachmentConnectedSum m e c d boundaryAttachment boundaryAttachment hec hed hcd cS dS hcS hdS hcdS s₀ eQ heQcore
  let s := SmoothSelfAttachment.pullback p q cS dS hpq hcdS boundaryAttachment E hEp hEq s₁
  let H₁ := SmoothSelfAttachment.pullbackEquiv p q cS dS hpq hcdS boundaryAttachment E hEp hEq s₁
  let H₂ := smoothSelfAttachmentConnectedSumEquiv m e c d boundaryAttachment boundaryAttachment hec hed hcd cS dS hcS hdS hcdS s₀ eQ heQcore
  obtain ⟨G⟩ := csTransport_diffeomorph_preservesOrientation m m eQ eP boundaryAttachment
    (Diffeomorph.refl (𝓡 3) M.Carrier ∞) F₀.val (fun _ _ => rfl) heQ
    (Diffeomorph.preservesOrientation_refl M.orientation)
  obtain ⟨K⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts m (orientedBallChart M)
    eP (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment
  exact ⟨s, ⟨((H₁.trans H₂).trans G).trans K⟩⟩

theorem exists_smoothSelfAttachment_orientedDiffeomorph_retaining_charts :
    ∃ s : SmoothSelfAttachment p q hpq boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold,
      ∀ {ι : Type*} (e : ι → OrientedBallChart M.toClosedOrientedManifold),
      (∀ i x, x ∈ Metric.closedBall (0 : E3) 2 →
        (e i).chart x ∉ p.chart '' Metric.closedBall 0 1 ∪ q.chart '' Metric.closedBall 0 1) →
      ∃ e' : ι → OrientedBallChart (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold,
        ∀ i x, x ∈ Metric.closedBall (0 : E3) 2 →
          ∃ hx : (e i).chart x ∈ (p.chart '' Metric.ball 0 1 ∪ q.chart '' Metric.ball 0 1)ᶜ,
            (e' i).chart x = F.val (SelfAttachment.coreInclusion p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph
              ⟨(e i).chart x, hx⟩) := by
  obtain ⟨s, ⟨F⟩⟩ := exists_smoothSelfAttachment_orientedDiffeomorph M p q hpq
  refine ⟨s, F, ?_⟩
  intro ι e he
  obtain ⟨e₀, he₀⟩ := s.exists_orientedBallChart_core_image e he
  refine ⟨fun i => (e₀ i).map F, ?_⟩
  intro i x hx
  obtain ⟨hx', hmap⟩ := he₀ i x hx
  exact ⟨hx', congrArg F.val hmap⟩

end DifferentialGeometry.Topology
