import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
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

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem orientation_map_trans {A F G : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (e : A ≃ₗ[ℝ] F) (f : F ≃ₗ[ℝ] G) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) (e.trans f) o = Orientation.map (Fin 3) f (Orientation.map (Fin 3) e o) := by
  induction o using Module.Ray.ind with | h v hv => rfl

theorem orientation_map_symm_map {M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (e : M ≃ₗ[ℝ] N) (o : Orientation ℝ M (Fin 3)) :
    Orientation.map (Fin 3) e.symm (Orientation.map (Fin 3) e o) = o := by
  rw [← orientation_map_trans e e.symm o, LinearEquiv.self_trans_symm,
    Orientation.map_refl]
  rfl

theorem orientation_map_smulOfNeZero_pos (c : ℝ) (hc : 0 < c) (x : Orientation ℝ E3 (Fin 3)) :
    Orientation.map (Fin 3) (LinearEquiv.smulOfNeZero ℝ E3 c (ne_of_gt hc)) x = x := by
  rw [Orientation.map_eq_iff_det_pos x _ (by simp : Fintype.card (Fin 3) = Module.finrank ℝ E3)]
  have hlm : ((LinearEquiv.smulOfNeZero ℝ E3 c (ne_of_gt hc) : E3 ≃ₗ[ℝ] E3) : E3 →ₗ[ℝ] E3)
      = c • (LinearMap.id : E3 →ₗ[ℝ] E3) := by
    ext v
    simp [LinearEquiv.smulOfNeZero_apply]
  rw [hlm, LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact pow_pos hc _
end DifferentialGeometry.Topology
