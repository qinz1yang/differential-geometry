import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BallNaturality
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
# IMS04 / O4c（S-A10-BOUNDARY, suffix `_BD`）：stage 上 `γ_t` 的曲率 = 模型 ball 上 `β_B` 在 `ĝ_t` 下的曲率

`β_B : ℝ → ↥ball`、`f_t|ball ∘ β_B = γ_t`。结合 `BallNaturality`（local isometry naturality）与
`CurvatureKernel`（缩放）：

`|κ_{g(t)}(γ_t)(s)|_{g(t)} = (√t)⁻¹ · |κ_{ĝ_t}(β_B)(s)|_{ĝ_t}`，`ĝ_t = t⁻¹ (f_t|ball)^* g(t)`。

于是 IMS04 的曲率界归结为 `↥ball` 上 `(h_B, ĝ_t, β_B)` 的曲率界（O-W-CURV）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Hyperbolic TopologicalSpace Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- `β_B s = cuspMap port (loop s, halfZero)`，作为 `↥ball` 里的曲线。 -/
def PrescribedCuspMeridian.sliceBall_BD (M : PrescribedCuspMeridian cores) (t : ℝ)
    (ht : M.exterior.start ≤ t) (s : ℝ) : ↥(cores.ballOpen_BD M.model t) :=
  ⟨(M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero),
    M.slice_mem_ball_BD t ht s⟩

theorem PrescribedCuspMeridian.sliceBall_contMDiff_BD (M : PrescribedCuspMeridian cores) (t : ℝ)
    (ht : M.exterior.start ≤ t) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (M.sliceBall_BD t ht) :=
  (isLocalDiffeomorph_subtype_val (I := 𝓡 3)
    (cores.ballOpen_BD M.model t)).contMDiff_of_continuous_of_comp
    (h := M.sliceBall_BD t ht) (m := ∞)
    (continuous_induced_rng.mpr M.slice_contMDiff_BD.continuous) M.slice_contMDiff_BD le_rfl

/-- `f_t|ball ∘ β_B = γ_t`。 -/
theorem PrescribedCuspMeridian.mapBall_comp_sliceBall_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) :
    cores.mapBall_BD M.model t (M.exterior.after_cores.trans ht) ∘ M.sliceBall_BD t ht =
      ⇑(loopLift (M.transported t ht)) := by
  rw [M.transported_eq_comp_BD t ht]
  rfl

/-- `β = cuspMap ∘ (loop, halfZero)` 的速度非零（`loop` 正则 + `torusMetric` 与模型度量一致）。 -/
theorem PrescribedCuspMeridian.slice_velocity_ne_zero_BD (M : PrescribedCuspMeridian cores)
    (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => (M.exterior.truncation M.model).cuspMap
      M.port (loopLift M.loop s, halfZero)) s 1 ≠ 0 := by
  intro h0
  have h2 := truncation_slice_inner_eq_BD (M.exterior.truncation M.model) M.port M.loop M.smooth s
  rw [h0] at h2
  have h3 : ((M.exterior.truncation M.model).cusp M.port).torusMetric.inner
      (loopLift M.loop s) (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1)
      (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1) = 0 := by
    rw [← h2]
    simp
  exact (((M.exterior.truncation M.model).cusp M.port).torusMetric.pos _ _
    (M.loop_velocity_ne_zero_BD s)).ne' h3

/-- `β_B` 的速度非零。 -/
theorem PrescribedCuspMeridian.sliceBall_velocity_ne_zero_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s 1 ≠ 0 := by
  intro h0
  apply M.slice_velocity_ne_zero_BD s
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : ↥(cores.ballOpen_BD M.model t) →
      (cores.model M.model).Carrier) (M.sliceBall_BD t ht s) :=
    (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  have hβ := (M.sliceBall_contMDiff_BD t ht s).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3) (I'' := 𝓡 3) s hval hβ
  change (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (Subtype.val ∘ M.sliceBall_BD t ht) s) 1 = 0
  rw [hcomp]
  change (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : ↥(cores.ballOpen_BD M.model t) →
      (cores.model M.model).Carrier) (M.sliceBall_BD t ht s))
    ((mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (M.sliceBall_BD t ht) s) 1) = 0
  rw [h0]
  exact map_zero _

/-- **O4c 主定理**：stage 上 `γ_t` 在 `g(t)` 下的曲率范数 `= (√t)⁻¹ ·` 模型 ball 上 `β_B` 在
`ĝ_t = t⁻¹ f_t^* g(t)` 下的曲率范数。 -/
theorem PrescribedCuspMeridian.sqrt_curvature_transported_eq_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (hacc : cores.accuracy t < 1) (s : ℝ) :
    Real.sqrt ((postMetric F.observation t).inner (loopLift (M.transported t ht) s)
        (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) s)
        (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) s))
      = (Real.sqrt t)⁻¹ *
        Real.sqrt ((cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc).inner
          (M.sliceBall_BD t ht s)
          (riemannianCurveCurvature
            (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
            (M.sliceBall_BD t ht) s)
          (riemannianCurveCurvature
            (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
            (M.sliceBall_BD t ht) s)) := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have htpos : 0 < t := cores.start_pos.trans_le ht'
  have hld := cores.isLocalDiffeomorph_mapBall_BD M.model t ht' hacc
  have hβ := M.sliceBall_contMDiff_BD t ht
  have hκ := riemannianCurveCurvature_comp_localPull_BD (postMetric F.observation t) hld hβ
    (M.sliceBall_velocity_ne_zero_BD t ht) s
  rw [← M.mapBall_comp_sliceBall_BD t ht]
  have h1 := sqrt_curvature_comp_localPull_BD (postMetric F.observation t) hld s hκ
  have h2 := sqrt_curvature_scaleMetric_BD t⁻¹ (inv_pos.mpr htpos)
    (localPullMetric (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
      (cores.mapBall_BD M.model t ht') hld) (M.sliceBall_BD t ht) s
  have hdef : cores.pulledMetric_BD M.model t ht' hacc =
      scaleMetric t⁻¹ (inv_pos.mpr htpos)
        (localPullMetric (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
          (cores.mapBall_BD M.model t ht') hld) := rfl
  rw [h1, hdef, h2, Real.sqrt_inv, inv_inv, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr htpos).ne', one_mul]

end GC.LongTime
