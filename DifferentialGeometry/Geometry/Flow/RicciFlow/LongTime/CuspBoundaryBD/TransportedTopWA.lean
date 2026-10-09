import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.LengthTopWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.LoopRegularTopWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop

/-!
# IMS04 / G4d（S-A10-BOUNDARY, suffix `_BD`）：`γ_t = loopLift (M.transported t ht)` 光滑、周期、正则

曲率估计与边界积分（G5）需要 `γ_t` 是 `ContMDiff ∞`、周期 1、速度处处非零：

* `transported_contMDiff_TBD`：`γ_t = cores.map ∘ cuspMap ∘ (loop, halfZero)`，`cores.map` 在开集
  `domain` 上光滑，slice 点落在 `domain`（`ball ⊆ domain`）；
* `transported_periodic_TBD`：`γ_t (x + 1) = γ_t x`（`loopLift_add_intCast`）；
* `transported_velocity_ne_zero_TBD`：`accuracy t < 1` 时速度处处非零（G4c `loop` 正则 + 切线
  `cuspIsometry` + G1 的 `pullback_inner_pos_BD`）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- `β = cuspMap ∘ (loop, halfZero)` 光滑。 -/
theorem PrescribedCuspMeridianTop_CPQ.slice_contMDiff_TBD
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun s : ℝ => (M.exterior.truncation M.model).cuspMap M.port
      (loopLift M.loop s, halfZero)) :=
  ((M.exterior.truncation M.model).cuspEmbedding M.port).contMDiff.comp
    (M.smooth.prodMk contMDiff_const)

/-- `γ_t` 光滑。 -/
theorem PrescribedCuspMeridianTop_CPQ.transported_contMDiff_TBD
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (loopLift (M.transported t ht)) := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  rw [M.transported_eq_comp_TBD t ht]
  exact (cores.smooth M.model t ht').comp_contMDiff M.slice_contMDiff_TBD
    (fun s => cores.advertised_ball M.model t ht' (M.slice_mem_ball_TBD t ht s))

/-- `γ_t` 周期 `1`。 -/
theorem PrescribedCuspMeridianTop_CPQ.transported_periodic_TBD
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (x : ℝ) :
    loopLift (M.transported t ht) (x + 1) = loopLift (M.transported t ht) x := by
  have := loopLift_add_intCast (M.transported t ht) x 1
  rwa [Int.cast_one] at this

/-- `accuracy t < 1` 时 `γ_t` 的速度处处非零。 -/
theorem PrescribedCuspMeridianTop_CPQ.transported_velocity_ne_zero_TBD
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (hacc : cores.accuracy t < 1) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (loopLift (M.transported t ht)) s 1 ≠ 0 := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have hball := M.slice_mem_ball_TBD t ht s
  have hdomain := cores.advertised_ball M.model t ht' hball
  have hdf : MDifferentiableAt (𝓡 3) (𝓡 3) (cores.map M.model t ht')
      ((M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)) :=
    ((cores.smooth M.model t ht').mdifferentiableOn (by simp)).mdifferentiableAt
      ((cores.domain M.model t).isOpen.mem_nhds hdomain)
  have hdβ := (M.slice_contMDiff_TBD s).mdifferentiableAt (by simp)
  rw [M.transported_eq_comp_TBD t ht, mfderiv_comp s hdf hdβ]
  have hβ0 : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => (M.exterior.truncation M.model).cuspMap M.port
      (loopLift M.loop s, halfZero)) s 1 ≠ 0 := by
    intro h0
    have h2 := truncation_slice_inner_eq_TBD (M.exterior.truncation M.model) M.port M.loop
      M.smooth s
    rw [h0] at h2
    have h3 : ((M.exterior.truncation M.model).cusp M.port).torusMetric.inner
        (loopLift M.loop s) (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1)
        (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1) = 0 := by
      rw [← h2]
      simp
    exact (((M.exterior.truncation M.model).cusp M.port).torusMetric.pos _ _
      (M.loop_velocity_ne_zero_TBD s)).ne' h3
  intro h0
  have hpos := cores.pullback_inner_pos_BD M.model t ht' hacc hball _ hβ0
  have h4 : (mfderiv (𝓡 3) (𝓡 3) (cores.map M.model t ht')
      ((M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)))
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => (M.exterior.truncation M.model).cuspMap M.port
        (loopLift M.loop s, halfZero)) s) 1) = 0 := h0
  rw [h4] at hpos
  simp at hpos

end GC.LongTime.CuspP1
