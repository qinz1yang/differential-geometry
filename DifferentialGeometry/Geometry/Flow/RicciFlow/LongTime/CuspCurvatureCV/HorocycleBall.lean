import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.Horocycle
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.CurvatureAssembly

/-!
# IMS04 / O2 consumer（O-W-CURV, suffix `_CV`）：BOUNDARY 的 (I2) 形状

`↥ball` 上 `h_B = cores.refMetric_BD`、`β_B = M.sliceBall_BD t ht`：
`|D^{h_B} β_B'|_{h_B} = ½ |β_B'|²_{h_B}`（`horocycle_acceleration_restrictOpen_CV` 的实例化）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **(I2)**：`√h_B(Dβ_B', Dβ_B') = ½ h_B(β_B', β_B')`（`D = covDerivAlong h_B β_B β_B'`）。 -/
theorem PrescribedCuspMeridian.sliceBall_acceleration_CV (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ) :
    Real.sqrt ((cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
        (covDerivAlong (cores.refMetric_BD M.model t) (M.sliceBall_BD t ht)
          (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) r 1) s)
        (covDerivAlong (cores.refMetric_BD M.model t) (M.sliceBall_BD t ht)
          (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) r 1) s)) =
      1 / 2 * (cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1) :=
  horocycle_acceleration_restrictOpen_CV (cores.ballOpen_BD M.model t) M.smooth M.geodesic
    (M.slice_mem_ball_BD t ht) s

end GC.LongTime
