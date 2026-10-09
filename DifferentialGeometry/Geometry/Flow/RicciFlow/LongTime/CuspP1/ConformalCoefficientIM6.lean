import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Ims05HC2ReadyIM6
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient

/-!
# S-W-STAB-2 的 `λ = diskMapConformalCoefficient G Q` ↔ 本车道 `diskConformalFactor_IM6 g (ι ∘ q)`
（O-W-IMS06 G15，后缀 `_IM6`）

S-W-STAB-2 G3（`exists_planar_stability_nu_free_HC_WS2`）的共形因子是开子流形 `U` 上度量 `G` 下的
`diskMapConformalCoefficient G Q`；c3（G7/G9）用 ambient `diskConformalFactor_IM6 g (ι ∘ q)`。
`_HC2` 的 locality（`G = g` near `q`）+ 开盘内 `diskExtension (ι ∘ q) =ᶠ ι ∘ Q` ⇒ 两者在开盘内相等。
* `coefficient_eq_diskConformalFactor_IM6`：逐点相等（`z ∈ ball`）。
* **`hstab_of_coefficient_IM6`**：STAB-2 单积分稳定性（权 `diskMapConformalCoefficient G Q · VJ`）⇒
  G7/G9 的 `hstab`（权 `diskConformalFactor_IM6 g (ι ∘ q) · VJ`），对任意 `Ω ⊆ ball`（不要求可测：
  `volume.restrict Ω ≤ volume.restrict ball`，ae 相等经绝对连续传过去）。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open GC.LongTime
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X]

theorem coefficient_eq_diskConformalFactor_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {q : C(closedDisk, U)} {Q : ℂ → U} (hQ : SmoothDiskExtension (E := E) q Q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    diskMapConformalCoefficient G Q z =
      diskConformalFactor_IM6 g ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z := by
  have hev : diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) =ᶠ[𝓝 z]
      (Subtype.val ∘ Q) :=
    diskExtension_eventuallyEq_of_extension_IM6 (fun w => congrArg Subtype.val (hQ.1 w)) hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
  have hGz : G.inner (Q z) = (g.restrictOpen U).inner (Q z) := by
    have h := (hloc ⟨z, hz'⟩).self_of_nhds
    rwa [← hQ.1 ⟨z, hz'⟩] at h
  have hpt : diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z =
      ((Q z : U) : X) := hev.eq_of_nhds
  have hd : diskMapPartial (E := E) (diskExtension
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)) z 1 =
      diskMapPartial (E := E) Q z 1 := by
    have h2 := diskMapPartial_open_inclusion (E := E) U Q z 1
    unfold diskMapPartial at h2 ⊢
    rw [hev.mfderiv_eq]
    exact h2
  unfold diskConformalFactor_IM6 diskMapConformalCoefficient
  rw [hGz]
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  rw [hd, hpt]
/-- **STAB-2 权 ⇒ 本车道权**：`diskMapConformalCoefficient G Q` 换成 `diskConformalFactor_IM6 g (ι ∘ q)`。 -/
theorem hstab_of_coefficient_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {q : C(closedDisk, U)} {Q : ℂ → U} (hQ : SmoothDiskExtension (E := E) q Q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    (VJ : ℂ → ℝ)
    (h : ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient G Q x * VJ x * ψ x ^ 2)) :
    ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + diskConformalFactor_IM6 g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) x * VJ x * ψ x ^ 2) := by
  intro Ω hΩ ψ hψ hc hs
  refine (h Ω hΩ ψ hψ hc hs).trans_eq (integral_congr_ae ?_)
  have hball : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℂ) 1)),
      ‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient G Q x * VJ x * ψ x ^ 2 =
        ‖fderiv ℝ ψ x‖ ^ 2 + diskConformalFactor_IM6 g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) x * VJ x * ψ x ^ 2 :=
    ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun x hx => by
      rw [coefficient_eq_diskConformalFactor_IM6 g G hQ hloc hx]
  exact (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hΩ le_rfl)).ae_le hball

end GC.LongTime.CuspP1
