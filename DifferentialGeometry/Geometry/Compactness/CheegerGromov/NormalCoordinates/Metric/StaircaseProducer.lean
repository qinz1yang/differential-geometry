import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BallGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.BallBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.BallBounds

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem SeqBallGeometry.basepoint_curv_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallGeometry (I := I) X) {q j : Nat} (hqj : q ≤ j) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (X.obj j).M := (X.obj j).t2
    letI : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
    curvDerivNorm (I := I) q (X.obj j).metric (X.obj j).basepoint ≤ h.C 0 q := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (X.obj j).M := (X.obj j).t2
  let : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
  refine h.bound 0 q j (by simpa only [Nat.zero_add] using hqj) (X.obj j).basepoint ?_
  rw [riemannianEDistOf_self]
  exact bot_le

end CheegerGromovCompactness
end DifferentialGeometry
