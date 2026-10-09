import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.CurvatureBoundTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.FluxIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.VelocityPostTopWA

/-!
# IMS04 / G4（O-W-CURV, suffix `_CV`）：Top 对象上 `∫k − f < π`（`hbdry` 的合成）

S-A10-DERIV G6″ / O-W-ASSEMBLY `hbarW` 的边界前提：对 Morrey 盘的光滑共形延拓 `Q`（迹
`(val ∘ Q) ∘ c = γU ∘ φ`，`φ` degree one）

`∫ diskMapTraceBoundaryDensity − ∫ (Gw t₀)(W θ, ν_in)·√coef < π`，`W θ = ∂_r Φ_r(Q(e^{iθ}))|_{t₀}`。

* `∫k`：G3 的 `curvature_bound_of_metric_error_CV`（`↥ball` 上曲率 `≤ 1`）喂 BOUNDARY Top 版
  `boundary_integral_le_of_ball_curvature_TBD` ⇒ `|∫k| ≤ √(1+acc)·L₁`；
* `f`：`abs_integral_flux_le_CV`（G4a）+ BOUNDARY 的 speed 界 `speed_transported_le_TBD`
  （`|γ'| ≤ √(t(1+acc))·L₂`）+ **显式前提 `hvel`**（`Φ` 在 `γ_{t₀}` 上的 `t₀`-速度 `·√t₀ < acc t₀`，形状见
  state-O-W-CURV §接口；由 S-A14-STATIC-2 的 `window_data_flux_of_no_event_ST` 提供）⇒
  `|f| ≤ acc·√(1+acc)·L₂`；
* `acc t₀ < 1/12`（`accuracy_decay`）⇒ `√(1+acc)(L₁ + acc L₂) < 1.05·(1 + 1/12) < π`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff Real
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G4 主定理（Top，`hvel` 显式）**：`t₀` 够大时，对任意 window `(Gw, Φ)`（`Gw t₀ = g(t₀)`）满足
`hvel`，以及任意开集 `Uo` 中迹为 `γ_{t₀}` 的光滑共形盘 `Q`、degree-one 单调 `φ`：
`∫k − f < π`（`f` 的形状与 DERIV G6″ / ASSEMBLY `hbarW` 逐字一致）。 -/
theorem PrescribedCuspMeridianTop_CPQ.boundary_sub_flux_lt_pi_CV
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ →
      ∀ (Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        Gw t₀ = postMetric F.observation t₀ →
        (∀ s : ℝ,
          Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀) s)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀) s)) t₀ 1)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀) s))
                t₀ 1)) * Real.sqrt t₀ < cores.accuracy t₀) →
        ∀ (Uo : TopologicalSpace.Opens (postStage F.observation t₀).Carrier) (γU : freeLoop Uo)
          (Q : ℂ → Uo) (φ : ℝ → ℝ) (N : Set ℂ), IsOpen N → Metric.closedBall (0 : ℂ) 1 ⊆ N →
          ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (Subtype.val ∘ Q) N →
          (⟨Subtype.val, continuous_subtype_val⟩ : C(Uo, (postStage F.observation t₀).Carrier)).comp
            γU = M.transported t₀ ht₀ →
          ContDiff ℝ ∞ φ → Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
          (Subtype.val ∘ Q) ∘ circleMap 0 1 =
            (fun s : ℝ => ((γU (s : loopCircle) : Uo) : (postStage F.observation t₀).Carrier)) ∘
              φ →
          (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
            DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z) →
          (∫ θ in -Real.pi..Real.pi,
              diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
                (fun s : ℝ => ((γU (s : loopCircle) : Uo) : (postStage F.observation t₀).Carrier))
                φ θ) -
            (∫ θ in -Real.pi..Real.pi,
              (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
                (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                  (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
                (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                  Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                    (circleMap 0 1 θ))) < Real.pi := by
  obtain ⟨L₁, hL₁0, hL₁1, hfin⟩ := M.boundary_integral_le_of_ball_curvature_TBD
  obtain ⟨L₂, hL₂0, hL₂1, hsp⟩ := M.speed_transported_le_TBD
  obtain ⟨T, hT⟩ := cores.accuracy_decay (1 / 12) (by norm_num)
  refine ⟨max M.exterior.start T, le_max_left _ _, ?_⟩
  intro t₀ ht₀ hT₁ Gw Φ hG₀ hvel Uo γU Q φ N hN hDN hQ hγγ hφ hmono hper htrace hconf
  have h12 : cores.accuracy t₀ < 1 / 12 := hT t₀ ((le_max_right _ _).trans hT₁)
  have hacc : cores.accuracy t₀ < 1 := h12.trans (by norm_num)
  have hpos : 0 < cores.accuracy t₀ :=
    cores.accuracy_pos t₀ (M.exterior.after_cores.trans ht₀)
  have hcurve : (fun s : ℝ => ((γU (s : loopCircle) : Uo) :
      (postStage F.observation t₀).Carrier)) = loopLift (M.transported t₀ ht₀) := by
    funext s
    rw [loopLift_apply, ← hγγ]
    rfl
  rw [hcurve] at htrace ⊢
  have hdeg : φ π = φ (-π) + 1 := by
    have h := hper (-π)
    rwa [show -π + 2 * π = π by ring] at h
  -- 边界曲率项
  have hk := hfin t₀ ht₀ hacc (Subtype.val ∘ Q) hN hQ hDN hconf hφ hmono hdeg htrace (κ₁ := 1)
    (fun x => M.curvature_bound_of_metric_error_CV t₀ ht₀ hacc h12.le x)
  -- flux 项
  rw [hG₀]
  have hcirc : ∀ θ : ℝ, circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := fun θ => by
    simp [Metric.mem_closedBall, dist_zero_right]
  have hUd : ∀ θ, MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 3) (Subtype.val ∘ Q) (circleMap 0 1 θ) :=
    fun θ => ((hQ _ (hDN (hcirc θ))).contMDiffAt (hN.mem_nhds (hDN (hcirc θ)))).mdifferentiableAt
      (by simp)
  have hγd : ∀ x, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (loopLift (M.transported t₀ ht₀)) x :=
    fun x => ((M.transported_contMDiff_TBD t₀ ht₀) x).mdifferentiableAt (by simp)
  have hB : ∀ θ : ℝ, Real.sqrt ((postMetric F.observation t₀).inner
        ((Subtype.val ∘ Q) (circleMap 0 1 θ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)) *
      riemannianCurveSpeed (postMetric F.observation t₀) (loopLift (M.transported t₀ ht₀)) (φ θ) ≤
      cores.accuracy t₀ * (Real.sqrt (1 + cores.accuracy t₀) * L₂) := by
    intro θ
    have hp : (Subtype.val ∘ Q) (circleMap 0 1 θ) = loopLift (M.transported t₀ ht₀) (φ θ) :=
      congrFun htrace θ
    rw [hp]
    have hs := hsp t₀ ht₀ (φ θ)
    have htpos : 0 < t₀ := cores.start_pos.trans_le (M.exterior.after_cores.trans ht₀)
    rw [Real.sqrt_mul htpos.le, mul_assoc] at hs
    exact mul_le_of_scaled_TBD (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hL₂0.le) (hvel (φ θ)) hs
  have hf := abs_integral_flux_le_CV (postMetric F.observation t₀) hUd
    (fun θ => hconf _ (hcirc θ)) hγd (hφ.of_le (by simp)) hmono hdeg htrace
    (fun θ => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
    hB
  -- 数值
  have hsq : Real.sqrt (1 + cores.accuracy t₀) < 1.05 := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith
  have hsq0 := Real.sqrt_nonneg (1 + cores.accuracy t₀)
  have hpi := Real.pi_gt_three
  set Ik := ∫ θ in -Real.pi..Real.pi,
    diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
      (loopLift (M.transported t₀ ht₀)) φ θ with hIk
  set If := ∫ θ in -Real.pi..Real.pi,
    (postMetric F.observation t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
      (diskMapInwardConormal (postMetric F.observation t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
      Real.sqrt (diskMapConformalCoefficient (postMetric F.observation t₀) (Subtype.val ∘ Q)
        (circleMap 0 1 θ)) with hIf
  have h1 : Ik ≤ Real.sqrt (1 + cores.accuracy t₀) * L₁ := by
    have := (le_abs_self Ik).trans hk
    linarith
  have h2 : -If ≤ cores.accuracy t₀ * (Real.sqrt (1 + cores.accuracy t₀) * L₂) :=
    (neg_le_abs If).trans hf
  have h3 : Real.sqrt (1 + cores.accuracy t₀) * L₁ < 1.05 := by nlinarith
  have h4 : cores.accuracy t₀ * (Real.sqrt (1 + cores.accuracy t₀) * L₂) < 1 / 12 * 1.05 := by
    have : Real.sqrt (1 + cores.accuracy t₀) * L₂ < 1.05 := by nlinarith
    nlinarith
  linarith

end GC.LongTime.CuspP1
