import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.Transported
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BoundaryIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.CurvatureKernel

/-!
# IMS04 / G5b（S-A10-BOUNDARY, suffix `_BD`）：Gauss–Bonnet 边界项的组装

把 G5a（`∫ diskMapTraceBoundaryDensity ≤ K · ∫_0^1 |γ'|`）、G2（`|γ_t'|_{g(t)} ≤ √(t(1+acc))·L`）、
G4d（`γ_t` 光滑 / 周期 / 正则）合成到 S-A10-GAUSS G4 冻结的对象
`∫_{-π..π} diskMapTraceBoundaryDensity (postMetric F.observation t) U γ_t φ θ dθ`：

`|∫ …| ≤ Kc · (√(t(1+acc t)) · L)`，其中 `Kc ≥ sup_x |κ_{g(t)}(γ_t)(x)|_{g(t)}`。

`Kc` 的曲率估计（`Kc ≲ t^{-1/2}`）是 G4 的内容，见 `CurvatureKernel`（kernel）与 DELIVERIES 的
obstruction 备注；这里 `Kc` 是纯数值参数（性质 `hK`），不是新结构。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff Real
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G5b 主定理**：边界项 `|∫ diskMapTraceBoundaryDensity| ≤ Kc · (√(t(1+acc t)) · L)`。 -/
theorem PrescribedCuspMeridian.boundary_integral_le_BD (M : PrescribedCuspMeridian cores) :
    ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ (t : ℝ) (ht : M.exterior.start ≤ t), cores.accuracy t < 1 →
      ∀ (U : ℂ → (postStage F.observation t).Carrier) {s : Set ℂ}, IsOpen s →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U s → Metric.closedBall (0 : ℂ) 1 ⊆ s →
      (∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (postMetric F.observation t) U q) →
      ∀ {φ : ℝ → ℝ}, ContDiff ℝ ∞ φ → Monotone φ → φ π = φ (-π) + 1 →
      U ∘ circleMap 0 1 = loopLift (M.transported t ht) ∘ φ → ∀ {Kc : ℝ},
      (∀ x, Real.sqrt ((postMetric F.observation t).inner (loopLift (M.transported t ht) x)
        (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) x)
        (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) x))
        ≤ Kc) →
      |∫ θ in -π..π, diskMapTraceBoundaryDensity (postMetric F.observation t) U
        (loopLift (M.transported t ht)) φ θ| ≤
        Kc * (Real.sqrt (t * (1 + cores.accuracy t)) * L) := by
  obtain ⟨L, hL0, hL1, hsp⟩ := M.speed_transported_le_BD
  refine ⟨L, hL0, hL1, fun t ht hacc U s hs hU hDs hconf φ hφ hmono hdeg htrace Kc hK => ?_⟩
  have hγ := M.transported_contMDiff_BD t ht
  have hi := M.transported_velocity_ne_zero_BD t ht hacc
  have h1 := abs_integral_diskMapTraceBoundaryDensity_le_BD (postMetric F.observation t) hs hU
    hDs hconf hγ hi (M.transported_periodic_BD t ht) hφ hmono hdeg htrace hK
  have hKc : 0 ≤ Kc := (Real.sqrt_nonneg _).trans (hK 0)
  have hcont : Continuous (riemannianCurveSpeed (postMetric F.observation t)
      (loopLift (M.transported t ht))) := (contDiff_riemannianCurveSpeed _ hγ hi).continuous
  have h2 : ∫ x in (0 : ℝ)..1, riemannianCurveSpeed (postMetric F.observation t)
      (loopLift (M.transported t ht)) x ≤ Real.sqrt (t * (1 + cores.accuracy t)) * L := by
    have := intervalIntegral.integral_mono_on (μ := volume) (zero_le_one' ℝ)
      (hcont.intervalIntegrable (μ := volume) 0 1)
      (intervalIntegrable_const (μ := volume) (c := Real.sqrt (t * (1 + cores.accuracy t)) * L))
      (fun x _ => hsp t ht x)
    simpa using this
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hKc)

end GC.LongTime
