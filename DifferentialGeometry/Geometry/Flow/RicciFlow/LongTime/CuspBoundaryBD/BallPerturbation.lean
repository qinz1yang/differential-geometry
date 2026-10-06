import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.CurvatureAssembly

/-!
# IMS04 / G6'（S-A10-BOUNDARY, suffix `_BD`）：`(I1) 联络差 + (I2) 模型加速度 ⇒ ĝ_t`-曲率界

O-W-CURV 若分两项交付（I1：`difference (metricCov ĝ_t) (metricCov h_B)` 的 `h_B`-范数 `≤ A`；
I2：模型 horocycle 加速度 `|D^{h_B} β_B'|_{h_B} ≤ ½ |β_B'|²_{h_B}`），本文件用
`CurvatureKernel.sqrt_curvature_perturbation_BD`（`g := h_B`，`ĝ := ĝ_t`）+
`pulledMetric_comparison_BD` 拼出 `|κ_{ĝ_t}(β_B)|_{ĝ_t} ≤ √(1+acc)(1/2 + A)/(1 - acc)`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set TopologicalSpace
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **(I1)+(I2) ⇒ 曲率界**。 -/
theorem PrescribedCuspMeridian.sqrt_curvature_pulled_le_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (hacc : cores.accuracy t < 1) {A : ℝ} (hA : 0 ≤ A)
    (hconn : ∀ (x : ↥(cores.ballOpen_BD M.model t)) (u w : TangentSpace (𝓡 3) x),
      Real.sqrt ((cores.refMetric_BD M.model t).inner x
        (CovariantDerivative.difference
          (metricCov (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc))
          (metricCov (cores.refMetric_BD M.model t)) x u w)
        (CovariantDerivative.difference
          (metricCov (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc))
          (metricCov (cores.refMetric_BD M.model t)) x u w)) ≤
        A * Real.sqrt ((cores.refMetric_BD M.model t).inner x u u) *
          Real.sqrt ((cores.refMetric_BD M.model t).inner x w w))
    (hmodel : ∀ s, Real.sqrt ((cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
      (covDerivAlong (cores.refMetric_BD M.model t) (M.sliceBall_BD t ht)
        (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1) s)
      (covDerivAlong (cores.refMetric_BD M.model t) (M.sliceBall_BD t ht)
        (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1) s)) ≤
      (1 / 2) * (cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)) (s : ℝ) :
    Real.sqrt ((cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc).inner
        (M.sliceBall_BD t ht s)
        (riemannianCurveCurvature
          (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
          (M.sliceBall_BD t ht) s)
        (riemannianCurveCurvature
          (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
          (M.sliceBall_BD t ht) s)) ≤
      Real.sqrt (1 + cores.accuracy t) * (1 / 2 + A) / (1 - cores.accuracy t) := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have hβ := M.sliceBall_contMDiff_BD t ht
  have hi := M.sliceBall_velocity_ne_zero_BD t ht
  have hhpos := (cores.refMetric_BD M.model t).pos (M.sliceBall_BD t ht s) _ (hi s)
  have hcomp := cores.pulledMetric_comparison_BD M.model t ht' hacc (M.sliceBall_BD t ht s)
  have hv0 := hcomp (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
  have hΛ : 0 ≤ 1 + cores.accuracy t := by
    linarith [cores.accuracy_pos t ht']
  have hkern := sqrt_curvature_perturbation_BD (cores.refMetric_BD M.model t)
    (cores.pulledMetric_BD M.model t ht' hacc) hβ hi s (Λ := 1 + cores.accuracy t) (A := A)
    (V := Real.sqrt ((cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)))
    (W := (1 / 2) * (cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1))
    hΛ hA (fun z => (cores.pulledMetric_comparison_BD M.model t ht' hacc _ z).2) (hconn _)
    le_rfl (hmodel s)
  refine hkern.trans ?_
  set hv := (cores.refMetric_BD M.model t).inner (M.sliceBall_BD t ht s)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1) with hhv
  have hacc0 := cores.accuracy_pos t ht'
  have h1a : 0 < 1 - cores.accuracy t := by linarith
  have hsq : riemannianCurveSpeed (cores.pulledMetric_BD M.model t ht' hacc) (M.sliceBall_BD t ht)
      s ^ 2 = (cores.pulledMetric_BD M.model t ht' hacc).inner (M.sliceBall_BD t ht s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1) :=
    Real.sq_sqrt (metric_inner_self_nonneg _ _ _)
  have hVV : Real.sqrt hv * Real.sqrt hv = hv := Real.mul_self_sqrt hhpos.le
  have hden : (1 - cores.accuracy t) * hv ≤ riemannianCurveSpeed
      (cores.pulledMetric_BD M.model t ht' hacc) (M.sliceBall_BD t ht) s ^ 2 := by
    rw [hsq]
    exact hv0.1
  have hAV : A * Real.sqrt hv * Real.sqrt hv = A * hv := by rw [mul_assoc, hVV]
  have hnum : 0 ≤ Real.sqrt (1 + cores.accuracy t) *
      (1 / 2 * hv + A * Real.sqrt hv * Real.sqrt hv) := by
    rw [hAV]
    positivity
  calc Real.sqrt (1 + cores.accuracy t) * (1 / 2 * hv + A * Real.sqrt hv * Real.sqrt hv) /
        riemannianCurveSpeed (cores.pulledMetric_BD M.model t ht' hacc) (M.sliceBall_BD t ht)
          s ^ 2
      ≤ Real.sqrt (1 + cores.accuracy t) * (1 / 2 * hv + A * Real.sqrt hv * Real.sqrt hv) /
        ((1 - cores.accuracy t) * hv) :=
        div_le_div_of_nonneg_left hnum (mul_pos h1a hhpos) hden
    _ = Real.sqrt (1 + cores.accuracy t) * (1 / 2 + A) / (1 - cores.accuracy t) := by
      rw [hAV]
      field_simp

end GC.LongTime
