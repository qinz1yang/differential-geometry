import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Topology.MetricSpace.ContinuousDistance
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open Set

namespace Metric

def ConeAnnulus (a b : ℝ) (Y : Type*) := Icc a b × Y

instance ConeAnnulus.instTopologicalSpace (a b : ℝ) (Y : Type*) [TopologicalSpace Y] :
    TopologicalSpace (ConeAnnulus a b Y) := inferInstanceAs (TopologicalSpace (Icc a b × Y))

instance ConeAnnulus.instCompactSpace (a b : ℝ) (Y : Type*) [TopologicalSpace Y]
    [CompactSpace Y] : CompactSpace (ConeAnnulus a b Y) :=
  inferInstanceAs (CompactSpace (Icc a b × Y))

end Metric
