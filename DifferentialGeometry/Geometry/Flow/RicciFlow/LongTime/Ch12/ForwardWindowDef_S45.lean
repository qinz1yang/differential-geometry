import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyCoresPost_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps

set_option autoImplicit false

/-!
# CH12-S45 / G1: the C^k pullback-error functional used by the `hLTF04` window

`ckErr_S45 H g' c f k p` is the real number `|∇^k (c • f^*g' - h)|_h (p)`, i.e. the same
expression as the `metric_error` field of `PersistentHyperbolicCores`.  It is an ℝ-valued
helper (not a `Prop`, no hypothesis), allowed by lead decision D4 of `sheet-H3H5.md`; it is
definitionally the scratch stand-in `ckErr_O15s` of `SheetH3H5_O15.lean`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

/-- C^k pullback error `|∇^k (c • f^*g' - h)|_h` at `p` (same expression as `metric_error`). -/
def ckErr_S45 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (k : ℕ)
    (p : H.Carrier) : ℝ :=
  tensor0SFiberNorm H.metric p (2 + k)
    (iteratedMetricCovariantDerivative H.metric 2
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f q - H.metric.inner q)).uncurryLeft) k p)

end GC.LongTime.Ch12
