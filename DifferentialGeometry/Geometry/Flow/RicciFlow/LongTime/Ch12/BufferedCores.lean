import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- CH12-R1 §5.1 (verbatim, D-R1-5): persistent cores with a factor-two buffer. -/
structure BufferedPersistentCores
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    extends PersistentHyperbolicCores F K where
  buffer_domain :
    ∀ i t, start ≤ t →
      riemannianBallOf (model i).metric (model i).basepoint
        (2 * (accuracy t)⁻¹) ⊆ domain i t
  buffer_error :
    ∀ i t (ht : start ≤ t),
      let h := (model i).metric
      let error := fun p : (model i).Carrier =>
        ((continuousMultilinearCurryFin1 ℝ
            (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          ((t⁻¹ : ℝ) •
              localPullInner (postMetric F.observation t)
                (map i t ht) p
            - h.inner p)).uncurryLeft
      ∀ k : ℕ, k ≤ max K ⌈(accuracy t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf h (model i).basepoint
          (2 * (accuracy t)⁻¹),
          tensor0SFiberNorm h p (2 + k)
            (iteratedMetricCovariantDerivative h 2 error k p)
              < accuracy t

def BufferedPersistentCores.toCores
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (B : BufferedPersistentCores F K) :
    PersistentHyperbolicCores F K :=
  B.toPersistentHyperbolicCores

end GC.LongTime.Ch12
