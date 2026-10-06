import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.HorocycleBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.ConnectionErrorBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BallPerturbation

/-!
# IMS04 / G3（O-W-CURV, suffix `_CV`）：`↥ball` 上 `|κ_{ĝ_t}(β_B)|_{ĝ_t} ≤ 1`（`acc t ≤ 1/12`）

(I1)（G2 `connection_difference_ball_CV`，`A = 3/2 (1+2acc)³ acc`）+ (I2)（G1
`sliceBall_acceleration_CV`，`W = ½ V²`）喂给 BOUNDARY 的 `sqrt_curvature_pulled_le_BD`：

`|κ_{ĝ_t}(β_B)|_{ĝ_t} ≤ √(1+acc)(½ + A)/(1 - acc) ≤ 1`（`0 < acc ≤ 1/12`；真值 `½(1 + O(acc))`）。

再经 `sqrt_curvature_transported_eq_BD`：stage 上 `|κ_{g(t)}(γ_t)|_{g(t)} ≤ (√t)⁻¹`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

/-- 数值：`0 < a ≤ 1/12` ⇒ `√(1+a)(½ + 3/2 (1+2a)³ a)/(1 - a) ≤ 1`。 -/
theorem curvature_constant_le_one_CV {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 12) :
    Real.sqrt (1 + a) * (1 / 2 + 3 / 2 * (1 + 2 * a) ^ 3 * a) / (1 - a) ≤ 1 := by
  have h1a : 0 < 1 - a := by linarith
  rw [div_le_one h1a]
  have hs : Real.sqrt (1 + a) ≤ 1 + a := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : (1 + 2 * a) ^ 3 ≤ 343 / 216 := by
    have h : 1 + 2 * a ≤ 7 / 6 := by linarith
    calc (1 + 2 * a) ^ 3 ≤ (7 / 6) ^ 3 := pow_le_pow_left₀ (by linarith) h 3
      _ = 343 / 216 := by norm_num
  have hB : 0 ≤ 1 / 2 + 3 / 2 * (1 + 2 * a) ^ 3 * a := by positivity
  have hB' : 1 / 2 + 3 / 2 * (1 + 2 * a) ^ 3 * a ≤ 1 / 2 + 343 / 144 * a := by nlinarith
  calc Real.sqrt (1 + a) * (1 / 2 + 3 / 2 * (1 + 2 * a) ^ 3 * a)
      ≤ (1 + a) * (1 / 2 + 343 / 144 * a) :=
        mul_le_mul hs hB' hB (by linarith)
    _ ≤ 1 - a := by nlinarith

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G3 主定理（↥ball）**：`acc t ≤ 1/12` ⇒ `|κ_{ĝ_t}(β_B)(s)|_{ĝ_t} ≤ 1`
（`ĝ_t = cores.pulledMetric_BD`，`β_B = M.sliceBall_BD t ht`）。 -/
theorem PrescribedCuspMeridian.curvature_bound_of_metric_error_CV
    (M : PrescribedCuspMeridian cores) (t : ℝ) (ht : M.exterior.start ≤ t)
    (hacc : cores.accuracy t < 1) (h12 : cores.accuracy t ≤ 1 / 12) (s : ℝ) :
    Real.sqrt ((cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc).inner
        (M.sliceBall_BD t ht s)
        (riemannianCurveCurvature
          (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
          (M.sliceBall_BD t ht) s)
        (riemannianCurveCurvature
          (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
          (M.sliceBall_BD t ht) s)) ≤ 1 := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have hpos : 0 < cores.accuracy t := cores.accuracy_pos t ht'
  have hA : 0 ≤ 3 / 2 * (1 + 2 * cores.accuracy t) ^ 3 * cores.accuracy t := by positivity
  refine (M.sqrt_curvature_pulled_le_BD t ht hacc hA
    (fun x u w => cores.connection_difference_ball_CV M.model t ht' hacc (by linarith) x u w)
    (fun r => (M.sliceBall_acceleration_CV t ht r).le) s).trans ?_
  exact curvature_constant_le_one_CV hpos h12

/-- **G3 consumer（stage 上）**：`acc t ≤ 1/12` ⇒ `|κ_{g(t)}(γ_t)(s)|_{g(t)} ≤ (√t)⁻¹`
（`γ_t = loopLift (M.transported t ht)`，BOUNDARY 的 √t 缩放 `sqrt_curvature_transported_eq_BD`）。 -/
theorem PrescribedCuspMeridian.curvature_transported_le_CV
    (M : PrescribedCuspMeridian cores) (t : ℝ) (ht : M.exterior.start ≤ t)
    (h12 : cores.accuracy t ≤ 1 / 12) (s : ℝ) :
    Real.sqrt ((postMetric F.observation t).inner (loopLift (M.transported t ht) s)
        (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) s)
        (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht))
          s)) ≤ (Real.sqrt t)⁻¹ := by
  have hacc : cores.accuracy t < 1 := h12.trans_lt (by norm_num)
  rw [M.sqrt_curvature_transported_eq_BD t ht hacc s]
  calc _ ≤ (Real.sqrt t)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (M.curvature_bound_of_metric_error_CV t ht hacc h12 s)
          (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (Real.sqrt t)⁻¹ := mul_one _

end GC.LongTime
