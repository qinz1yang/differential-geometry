import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.Manifold.BallChartTransport

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

def SelfTransport : Prop :=
  ∀ {M : ConnectedClosedOrientedManifold.{u} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold),
    OrientedBallChartTransport c c'

def OrientedBallChartPullback : Prop :=
  ∀ {M M' : ClosedOrientedManifold.{u} 3}
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (c' : OrientedBallChart M'),
    Φ.preservesOrientation M.orientation M'.orientation →
    ∃ c : OrientedBallChart M,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.toBallChart.chart x) = c'.toBallChart.chart x

theorem connectedSumQuotient_diffeomorph_of_selfTransport (h : SelfTransport.{u})
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{u} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    letI := ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
  nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport c c' d d' a
    (h c c') (h d d')

theorem connectedSum_diffeomorph_of_ballChartTransport
    (M : ConnectedClosedOrientedManifold.{u} 3) (P P' : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart P.toClosedOrientedManifold)
    (d' : OrientedBallChart P'.toClosedOrientedManifold)
    (hP : Manifold.BallChartTransport (orientedBallChart P).toBallChart d.toBallChart)
    (hP' : Manifold.BallChartTransport (orientedBallChart P').toBallChart d'.toBallChart)
    (Ψ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΨ : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      Ψ (d.toBallChart.chart x) = d'.toBallChart.chart x) :
    Nonempty ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) := by
  have hcanon : Manifold.BallChartTransport
      (orientedBallChart M).toBallChart (orientedBallChart M).toBallChart :=
    Manifold.BallChartTransport.refl _
  let W : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum M P (orientedBallChart M) d boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  let W' : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum M P' (orientedBallChart M) d' boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  have step1 : Nonempty
      ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      (orientedBallChart M) (orientedBallChart M) (orientedBallChart P) d boundaryAttachment
      hcanon hP
  have step2 : Nonempty (W.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W'.Carrier) :=
    csTransportDiffeomorph (orientedBallChart M) (orientedBallChart M) d d'
      boundaryAttachment (Diffeomorph.refl (𝓡 3) M.Carrier ∞) Ψ (fun _ _ => rfl) hΨ
  have step3 : Nonempty (W'.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      (orientedBallChart M) (orientedBallChart M) d' (orientedBallChart P') boundaryAttachment
      hcanon (Manifold.BallChartTransport.symm hP')
  exact step1.elim fun f => step2.elim fun g => step3.elim fun k => ⟨f.trans (g.trans k)⟩

theorem connectedSum_diffeomorph_of_ballChartTransport_left
    (Q : ConnectedClosedOrientedManifold.{u} 3) (P P' : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart P.toClosedOrientedManifold)
    (c' : OrientedBallChart P'.toClosedOrientedManifold)
    (hP : Manifold.BallChartTransport (orientedBallChart P).toBallChart c.toBallChart)
    (hP' : Manifold.BallChartTransport (orientedBallChart P').toBallChart c'.toBallChart)
    (Φ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΦ : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      Φ (c.toBallChart.chart x) = c'.toBallChart.chart x) :
    Nonempty ((connectedSum P Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum P' Q).toClosedOrientedManifold.Carrier) := by
  have hcanon : Manifold.BallChartTransport
      (orientedBallChart Q).toBallChart (orientedBallChart Q).toBallChart :=
    Manifold.BallChartTransport.refl _
  let W : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum P Q c (orientedBallChart Q) boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  let W' : ConnectedClosedOrientedManifold.{u} 3 :=
    (smoothConnectedSum P' Q c' (orientedBallChart Q) boundaryAttachment)
      |>.toConnectedClosedOrientedManifold
  have step1 : Nonempty
      ((connectedSum P Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      (orientedBallChart P) c (orientedBallChart Q) (orientedBallChart Q) boundaryAttachment
      hP hcanon
  have step2 : Nonempty (W.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ W'.Carrier) :=
    csTransportDiffeomorph c c' (orientedBallChart Q) (orientedBallChart Q)
      boundaryAttachment Φ (Diffeomorph.refl (𝓡 3) Q.Carrier ∞) hΦ (fun _ _ => rfl)
  have step3 : Nonempty (W'.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum P' Q).toClosedOrientedManifold.Carrier) :=
    nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
      c' (orientedBallChart P') (orientedBallChart Q) (orientedBallChart Q) boundaryAttachment
      (Manifold.BallChartTransport.symm hP') hcanon
  exact step1.elim fun f => step2.elim fun g => step3.elim fun k => ⟨f.trans (g.trans k)⟩

theorem connectedSum_transport_right_of_orientedPullback
    (hself : SelfTransport.{u}) (hpull : OrientedBallChartPullback.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (P P' : ConnectedClosedOrientedManifold.{u} 3)
    (Ψ : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ P'.Carrier)
    (hΨ : Ψ.preservesOrientation P.orientation P'.orientation) :
    Nonempty ((connectedSum M P).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M P').toClosedOrientedManifold.Carrier) := by
  obtain ⟨d, hd⟩ := hpull Ψ (orientedBallChart P') hΨ
  exact connectedSum_diffeomorph_of_ballChartTransport M P P' d (orientedBallChart P')
    (hself (orientedBallChart P) d).toBallChartTransport (Manifold.BallChartTransport.refl _) Ψ hd

theorem connectedSum_transport_left_of_orientedPullback
    (hself : SelfTransport.{u}) (hpull : OrientedBallChartPullback.{u})
    (M M' : ConnectedClosedOrientedManifold.{u} 3) (Q : ConnectedClosedOrientedManifold.{u} 3)
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    Nonempty ((connectedSum M Q).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum M' Q).toClosedOrientedManifold.Carrier) := by
  obtain ⟨c, hc⟩ := hpull Φ (orientedBallChart M') hΦ
  exact connectedSum_diffeomorph_of_ballChartTransport_left Q M M' c (orientedBallChart M')
    (hself (orientedBallChart M) c).toBallChartTransport (Manifold.BallChartTransport.refl _) Φ hc

end DifferentialGeometry.Topology
