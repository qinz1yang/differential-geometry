import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallCollar_S82
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Component

set_option autoImplicit false

/-!
# CH12-S98 / G2a: the ball `ball(2R)` is open and its closed ball is compact (connected complete `H`)
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology Set TopologicalSpace Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

theorem isOpen_ball_S98 (H : FiniteVolumeHyperbolicModel.{u}) (ρ : ℝ) :
    IsOpen (riemannianBallOf H.metric H.basepoint ρ) :=
  isOpen_lt (by
    unfold riemannianEDistOf
    exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist H.metric H.basepoint) continuous_const

theorem isCompact_closedBall_S98 (H : FiniteVolumeHyperbolicModel.{u}) (ρ : ℝ) :
    IsCompact {x : H.Carrier | riemannianEDistOf H.metric H.basepoint x ≤ ENNReal.ofReal ρ} := by
  have : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have hc := DifferentialGeometry.Geometry.RiemannianMetricComplete.isCompact_intrinsicClosedBall_connectedComponent
    H.metric H.complete.1 H.basepoint (connectedComponentPoint (I := 𝓡 3) H.basepoint) ρ
  have himg := hc.image continuous_subtype_val
  convert himg using 1
  ext x
  have hx : x ∈ (connectedComponentOpen (I := 𝓡 3) H.basepoint : Set H.Carrier) := by
    simp [connectedComponentOpen]
  simp only [Set.mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

end GC.LongTime.Ch12
