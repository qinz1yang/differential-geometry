import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.CurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BallPerturbationTopWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.FinalAssemblyTopWA

/-!
# IMS04 / G3 Top 版（O-W-CURV, suffix `_CV`）：`PrescribedCuspMeridianTop_CPQ` 上的曲率界

O-W-ASSEMBLY G5 把 BOUNDARY 的定理搬到 Top 对象（`_TBD`）。这里给 Top 版的 (I2)、`≤ 1` 曲率界，
并实例化 `boundary_integral_lt_pi_TBD` 的 `hcurv`：**无条件**的 `|∫ density| < π`（t 够大）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint
open scoped Manifold ContDiff Real
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **(I2) Top 版**：`√(h_B(Dβ_B', Dβ_B')) = ½ h_B(β_B', β_B')`（`β_B = M.sliceBall_TBD t ht`）。 -/
theorem PrescribedCuspMeridianTop_CPQ.sliceBall_acceleration_CV
    (M : PrescribedCuspMeridianTop_CPQ cores) (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ) :
    Real.sqrt ((cores.refMetric_BD M.model t).inner (M.sliceBall_TBD t ht s)
        (covDerivAlong (cores.refMetric_BD M.model t) (M.sliceBall_TBD t ht)
          (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_TBD t ht) r 1) s)
        (covDerivAlong (cores.refMetric_BD M.model t) (M.sliceBall_TBD t ht)
          (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_TBD t ht) r 1) s)) =
      1 / 2 * (cores.refMetric_BD M.model t).inner (M.sliceBall_TBD t ht s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_TBD t ht) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_TBD t ht) s 1) :=
  horocycle_acceleration_restrictOpen_CV (cores.ballOpen_BD M.model t) M.smooth M.geodesic
    (M.slice_mem_ball_TBD t ht) s

/-- **G3 Top 版**：`acc t ≤ 1/12` ⇒ `|κ_{ĝ_t}(β_B)(s)|_{ĝ_t} ≤ 1`。 -/
theorem PrescribedCuspMeridianTop_CPQ.curvature_bound_of_metric_error_CV
    (M : PrescribedCuspMeridianTop_CPQ cores) (t : ℝ) (ht : M.exterior.start ≤ t)
    (hacc : cores.accuracy t < 1) (h12 : cores.accuracy t ≤ 1 / 12) (s : ℝ) :
    Real.sqrt ((cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc).inner
        (M.sliceBall_TBD t ht s)
        (riemannianCurveCurvature
          (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
          (M.sliceBall_TBD t ht) s)
        (riemannianCurveCurvature
          (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
          (M.sliceBall_TBD t ht) s)) ≤ 1 := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have hpos : 0 < cores.accuracy t := cores.accuracy_pos t ht'
  have hA : 0 ≤ 3 / 2 * (1 + 2 * cores.accuracy t) ^ 3 * cores.accuracy t := by positivity
  refine (M.sqrt_curvature_pulled_le_TBD t ht hacc hA
    (fun x u w => cores.connection_difference_ball_CV M.model t ht' hacc (by linarith) x u w)
    (fun r => (M.sliceBall_acceleration_CV t ht r).le) s).trans ?_
  exact curvature_constant_le_one_CV hpos h12

/-- **G3 consumer（Top，无条件边界项 `< π`）**：`boundary_integral_lt_pi_TBD` 的 `hcurv` 由 G3 实例化。 -/
theorem PrescribedCuspMeridianTop_CPQ.boundary_integral_lt_pi_unconditional_CV
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ T : ℝ, ∀ (t : ℝ) (ht : M.exterior.start ≤ t), T ≤ t →
      ∀ (U : ℂ → (postStage F.observation t).Carrier) {s : Set ℂ}, IsOpen s →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U s → Metric.closedBall (0 : ℂ) 1 ⊆ s →
      (∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (postMetric F.observation t) U q) →
      ∀ {φ : ℝ → ℝ}, ContDiff ℝ ∞ φ → Monotone φ → φ π = φ (-π) + 1 →
      U ∘ circleMap 0 1 = loopLift (M.transported t ht) ∘ φ →
      |∫ θ in -π..π, diskMapTraceBoundaryDensity (postMetric F.observation t) U
        (loopLift (M.transported t ht)) φ θ| < π :=
  M.boundary_integral_lt_pi_TBD fun t ht hacc h12 x =>
    (M.curvature_bound_of_metric_error_CV t ht hacc h12.le x).trans (by norm_num)

end GC.LongTime.CuspP1
