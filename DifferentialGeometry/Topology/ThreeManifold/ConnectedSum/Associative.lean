import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Filter Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_orientedDiffeomorph_right
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {N N' : ConnectedClosedOrientedManifold.{u} 3}
    (Ψ : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N'.Carrier)
    (hΨo : Ψ.preservesOrientation N.orientation N'.orientation)
    (c : OrientedBallChart M.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c (orientedBallChart N) a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N' c (orientedBallChart N') a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨d, hd⟩ := orientedBallChartPullback Ψ (orientedBallChart N') hΨo
  obtain ⟨f⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart c d
    (orientedBallChart N) a
  obtain ⟨g⟩ := csTransport_diffeomorph_preservesOrientation c c d (orientedBallChart N') a
    (Diffeomorph.refl (𝓡 3) M.Carrier ∞) Ψ
    (fun _ _ => rfl) (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hd x hx)
    (Diffeomorph.preservesOrientation_refl M.orientation)
  exact ⟨f.symm.trans g⟩

def ConnectedSumFlatteningIso : Prop :=
  ∀ (X Y Z : ConnectedClosedOrientedManifold.{u} 3)
    (δ dY' : OrientedBallChart Y.toClosedOrientedManifold)
    (f : OrientedBallChart
      (smoothConnectedSum X Y (orientedBallChart X) δ boundaryAttachment
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (g : OrientedBallChart
      (smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum
        (smoothConnectedSum X Y (orientedBallChart X) δ boundaryAttachment
          ).toConnectedClosedOrientedManifold
        Z f (orientedBallChart Z) boundaryAttachment
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum X
        (smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment
          ).toConnectedClosedOrientedManifold
        (orientedBallChart X) g boundaryAttachment
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem connectedSumAssociative_of_flatteningIso (h : ConnectedSumFlatteningIso.{u}) :
    connectedSumAssociative.{u} := by
  intro X Y Z
  obtain ⟨dY', δ, h1, h2⟩ := exists_disjointOrientedBallChart_closedBall (orientedBallChart Y)
  let A := (smoothConnectedSum X Y (orientedBallChart X) δ boundaryAttachment
    ).toConnectedClosedOrientedManifold
  let B := (smoothConnectedSum Y Z dY' (orientedBallChart Z) boundaryAttachment
    ).toConnectedClosedOrientedManifold
  let f : OrientedBallChart A.toClosedOrientedManifold :=
    Classical.choose
      (exists_orientedBallChart_inr (orientedBallChart X) δ boundaryAttachment dY' h1)
  let g : OrientedBallChart B.toClosedOrientedManifold :=
    Classical.choose
      (exists_orientedBallChart_inl dY' (orientedBallChart Z) boundaryAttachment δ h2)
  obtain ⟨Ψd, hΨdo, hΨd⟩ := selfTransport_holds (orientedBallChart Y) δ
  obtain ⟨hAB⟩ := csTransport_diffeomorph_preservesOrientation (orientedBallChart X)
    (orientedBallChart X) (orientedBallChart Y) δ boundaryAttachment
    (Diffeomorph.refl (𝓡 3) X.Carrier ∞) Ψd (fun _ _ => rfl)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΨd x hx)
    (Diffeomorph.preservesOrientation_refl X.orientation)
  obtain ⟨Ψd', hΨd'o, hΨd'⟩ := selfTransport_holds (orientedBallChart Y) dY'
  obtain ⟨hBQ⟩ := csTransport_diffeomorph_preservesOrientation (orientedBallChart Y) dY'
    (orientedBallChart Z) (orientedBallChart Z) boundaryAttachment Ψd'
    (Diffeomorph.refl (𝓡 3) Z.Carrier ∞)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΨd' x hx)
    (fun _ _ => rfl) hΨd'o
  obtain ⟨Φ₁, hΦ₁o⟩ := hAB
  obtain ⟨Φ₂, hΦ₂o⟩ := hBQ
  obtain ⟨step1⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_orientedDiffeomorph
    Φ₁ hΦ₁o (orientedBallChart Z) boundaryAttachment
  obtain ⟨step2⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart
    (orientedBallChart A) f (orientedBallChart Z) boundaryAttachment
  obtain ⟨step3⟩ := h X Y Z δ dY' f g
  obtain ⟨step4⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart
    (orientedBallChart X) g (orientedBallChart B) boundaryAttachment
  obtain ⟨step5⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_orientedDiffeomorph_right
    Φ₂.symm (Diffeomorph.preservesOrientation_symm hΦ₂o) (orientedBallChart X)
    boundaryAttachment
  exact ⟨step1.trans (step2.trans (step3.trans (step4.trans step5)))⟩

end DifferentialGeometry.Topology
