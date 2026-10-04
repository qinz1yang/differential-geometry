import DifferentialGeometry.Geometry.Thurston.NonnegativeClassificationUnconditional

/-!
# PORT567 import shim for the discharge of `closed_nonnegative_sectional_classification`

The frozen skeleton file `Geometry/Thurston/NonnegativeClassification.lean` imports this module
instead of importing `NonnegativeClassificationUnconditional` directly.

The producer's import closure (Seifert blocks for the flat case, the Poincaré route and Plateau
regularity for the spherical case) makes two integration names visible, for the first time, to the
modules downstream of `NonnegativeClassification`:

* `GC.Topology.Torus` (`Topology/ThreeManifold/TorusCut/TorusCylinder.lean`): in namespace
  `GC.LongTime`, a module opening both `GC.Endpoint` and `GC.Topology` would read `Torus` as
  ambiguous between it and `GC.Endpoint.Torus`;
* `DifferentialGeometry.Geometry.RiemannianMetricComplete`
  (`Geometry/Metric/Completeness/PseudoEMetric.lean`): inside `DifferentialGeometry.Geometry.Collapse`
  it would shadow `DifferentialGeometry.RiemannianMetricComplete` (the innermost enclosing namespace
  wins in name resolution).

The two `export` aliases below restore, for exactly these two namespaces, the resolution that the
downstream modules had before the discharge. They declare nothing: each identifier still elaborates
to the same constant as before (`GC.Endpoint.Torus`, `DifferentialGeometry.RiemannianMetricComplete`).
-/

set_option autoImplicit false

namespace GC.LongTime

export GC.Endpoint (Torus)

end GC.LongTime

namespace DifferentialGeometry.Geometry.Collapse

export DifferentialGeometry (RiemannianMetricComplete)

end DifferentialGeometry.Geometry.Collapse
