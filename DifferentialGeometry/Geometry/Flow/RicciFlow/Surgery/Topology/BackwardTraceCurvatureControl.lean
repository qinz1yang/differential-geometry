import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall

/-!
# S-CH11-SHIM shim (not a copy of the astra file)

Split-out module `Surgery.Topology.BackwardTraceCurvatureControl`.

Jui-Hui's chapter-11 branch (`gc/juihuichung/chapter11-astra-20261005`) split this
module out of the fat W8 module(s) below.  In this tree the host module(s) still
contain every public declaration of the astra file with the same signature, so this
shim only re-exports them: the import lines are those of the astra file verbatim,
plus an import of the host.  Modules copied verbatim from astra that import this
path then compile unchanged, without duplicate declarations.
No `set_option` and no new public declaration here.

Host module(s) (prefix `DifferentialGeometry.Geometry.Flow.RicciFlow.` omitted):
  `Surgery.Topology.HistoryParabolicBall`
-/
