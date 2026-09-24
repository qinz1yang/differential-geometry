import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartPointPushing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassExistenceReduction

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

theorem exists_unique_fundamentalClass_sphereThree
    (o : TangentOrientationSection SphereThree) :
    ∃! z : IntegralHomology SphereThree 3, ∀ x : SphereThree,
      absoluteToRelative SphereThree ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_sphereThree_of_localClassTransport o
    (localClassTransport_of_preconnectedSpace o)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
