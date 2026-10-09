import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyCoresPost_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps

/-!
# CH12-O19: the `C^k` pullback error `ckErr_O19`

`ckErr_O19 H g' c f k p = |∇^k (c • f^*g' - h)|_h (p)`, verbatim the `metric_error` expression of
the H3 statement sheet (`ckErr_O15s`).  An `ℝ`-valued helper (lead 14:41: allowed).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- `C^k` pullback error `|∇^k (c • f^*g' - h)|_h` at `p` (same expression as `metric_error`). -/
def ckErr_O19 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (k : ℕ)
    (p : H.Carrier) : ℝ :=
  tensor0SFiberNorm H.metric p (2 + k)
    (iteratedMetricCovariantDerivative H.metric 2
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f q - H.metric.inner q)).uncurryLeft) k p)

end GC.LongTime.Ch12
