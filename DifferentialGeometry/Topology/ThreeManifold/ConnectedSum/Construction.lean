import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar
import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Manifold.SphereOrientation

open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

structure OrientedBallChart (M : ClosedOrientedManifold.{u} 3)
    extends BallChart 3 (𝓡 3) M.Carrier where
  preserves_orientation : ∀ x, ∀ hx : x ∈ chart.source,
    Orientation.map (Fin 3)
      (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ chart hx) (by simp)).toLinearEquiv
      (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
      M.orientation.orientation (chart x)

abbrev BoundaryAttachment :=
  {a : Diffeomorph (𝓡 2) (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ //
    a.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)).opposite}

structure SmoothConnectedSum {M : ClosedOrientedManifold.{u} 3}
    {N : ClosedOrientedManifold.{v} 3} (c : OrientedBallChart M) (d : OrientedBallChart N)
    (a : BoundaryAttachment) where
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3))
    (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph)]
  [smooth : IsManifold (𝓡 3) ∞
    (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph)]
  [hausdorff : T2Space (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph)]
  [compact : CompactSpace (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph)]
  [connected : ConnectedSpace (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph)]
  orientation : ManifoldOrientation (𝓡 3)
    (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) 3
  interiorLeft_localDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1)
  interiorRight_localDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1)
  collar_localDiffeomorph : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1)
  interiorLeft_preserves_orientation : ∀ x,
    Orientation.map (Fin 3)
      (interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (M.orientation.orientation x) =
      orientation.orientation (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x)
  interiorRight_preserves_orientation : ∀ x,
    Orientation.map (Fin 3)
      (interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (N.orientation.orientation x) =
      orientation.orientation (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x)

namespace SmoothConnectedSum

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
  {c : OrientedBallChart M} {d : OrientedBallChart N} {a : BoundaryAttachment}

def toConnectedClosedOrientedManifold (s : SmoothConnectedSum c d a) :
    ConnectedClosedOrientedManifold.{max u v} 3 where
  Carrier := ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph
  topology := inferInstance
  charts := s.charts
  smooth := s.smooth
  hausdorff := s.hausdorff
  compact := s.compact
  connected := s.connected
  orientation := s.orientation

def inl (s : SmoothConnectedSum c d a) :
    c.toBallChart.Punctured → s.toConnectedClosedOrientedManifold.Carrier :=
  ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph

def inr (s : SmoothConnectedSum c d a) :
    d.toBallChart.Punctured → s.toConnectedClosedOrientedManifold.Carrier :=
  ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph

theorem boundary_eq (s : SmoothConnectedSum c d a)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    s.inl (c.toBallChart.boundaryMap z) = s.inr (d.toBallChart.boundaryMap (a.1 z)) :=
  ConnectedSumQuotient.boundary_eq c.toBallChart d.toBallChart a.1.toHomeomorph z

end SmoothConnectedSum

theorem exists_oriented_ball_chart (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (OrientedBallChart M.toClosedOrientedManifold) := by
  sorry

theorem exists_boundary_attachment : Nonempty BoundaryAttachment := by
  exact ⟨Topology.Manifold.sphereAntipodalDiffeomorph,
    sphereAntipodalDiffeomorph_preservesOrientation_opposite⟩

theorem exists_smooth_connected_sum (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (SmoothConnectedSum c d a) := by
  sorry

def orientedBallChart (M : ConnectedClosedOrientedManifold.{u} 3) :
    OrientedBallChart M.toClosedOrientedManifold :=
  Classical.choice (exists_oriented_ball_chart M)

def boundaryAttachment : BoundaryAttachment := Classical.choice exists_boundary_attachment

def smoothConnectedSum (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    SmoothConnectedSum (orientedBallChart M) (orientedBallChart N) boundaryAttachment :=
  Classical.choice (exists_smooth_connected_sum M N (orientedBallChart M)
    (orientedBallChart N) boundaryAttachment)

def connectedSum (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) : ConnectedClosedOrientedManifold.{max u v} 3 :=
  (smoothConnectedSum M N).toConnectedClosedOrientedManifold

@[simp]
theorem connectedSum_carrier (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSum M N).Carrier = ConnectedSumQuotient (orientedBallChart M).toBallChart
      (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph := rfl

theorem connectedSum_choice_independent {M : ClosedOrientedManifold.{u} 3}
    {N : ClosedOrientedManifold.{v} 3} (c c' : OrientedBallChart M)
    (d d' : OrientedBallChart N) (a a' : BoundaryAttachment)
    (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  sorry

end DifferentialGeometry.Topology
