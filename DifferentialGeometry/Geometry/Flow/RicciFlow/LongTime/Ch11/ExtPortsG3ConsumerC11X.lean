import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.LipschitzImage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffVolumeNonincrease

/-!
# ExtPortsG3ConsumerC11X（S-CH11-EXT1 G3 consumer：port + verbatim 搬入）

* `LipschitzImagePortC11X`（原路径 `…Measure.Riemannian.LipschitzImage` 是只含 import 的 shim）：
  它依赖 EXT2 的 `DensityComparisonC11X` 里新增的 `paramDensity_le_of_inner_mfderiv_le`，
  这里经由 shim 路径 import 它，并引用 `riemannianVolumeMeasure_image_le_of_locally_nonexpanding`；
* `GeometricCutoffVolumeNonincrease`（donor verbatim，import 的是 shim 路径）：引用它的主定理
  `GeometricCutoffRecord.volume_le_collapseBandHull`。
-/

set_option autoImplicit false

namespace DifferentialGeometry

example := @Integral.Measure.riemannianVolumeMeasure_image_le_of_locally_nonexpanding

example := @PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.volume_le_collapseBandHull

end DifferentialGeometry
