import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Ims05RadiusHC2IM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PlanarStabilityFormIM6

/-!
# c3 在 `_HC2` 盘上就绪：只剩 S-W-STAB-2 的 `VJ` 数据（O-W-IMS06 G9，后缀 `_IM6`）

把 G7 的 `ims05_radius_bound_of_normStability_IM6`（通用盘）落到 `_HC2` 形 Morrey 盘的 ambient 像
`ι ∘ q`：开盘内光滑（G1）、共形（G1，经 locality）、`diskExtension (ι ∘ q)` 的 `mfderiv` 单射
（由 K16b 对光滑延拓 `Q` 的单射：开盘内 `diskExtension (ι ∘ q) =ᶠ ι ∘ Q`，`mfderiv_subtypeVal_comp`）。
于是 c3 对 `_HC2` 盘只剩 `VJ`、`hVJ`、`hVJle`、`hstab`（S-W-STAB-2 G3 的 `_HC2` 实例 + 平面曲率换写）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open GC.LongTime
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.CuspP1

/-- 开盘内 `diskExtension u` 与光滑延拓 `U` 局部相等。 -/
theorem diskExtension_eventuallyEq_of_extension_IM6 {Y : Type*} [TopologicalSpace Y]
    {u : C(closedDisk, Y)} {U : ℂ → Y} (hU : ∀ w : closedDisk, U w = u w) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    diskExtension u =ᶠ[𝓝 z] U := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  have hy' : y ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hy
  have h := diskExtension_coe u ⟨y, hy'⟩
  change diskExtension u y = u ⟨y, hy'⟩ at h
  rw [h, ← hU ⟨y, hy'⟩]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X] in
/-- K16b 形的内部浸入（对光滑延拓 `Q : ℂ → U`）⇒ `diskExtension (ι ∘ q)` 的 `mfderiv` 单射。 -/
theorem injective_mfderiv_diskExtension_comp_val_IM6 {U : TopologicalSpace.Opens X}
    {q : C(closedDisk, U)} {Q : ℂ → U} (hQ : SmoothDiskExtension (E := E) q Q) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)) z) := by
  have hev : diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) =ᶠ[𝓝 z]
      (Subtype.val ∘ Q) :=
    diskExtension_eventuallyEq_of_extension_IM6 (fun w => congrArg Subtype.val (hQ.1 w)) hz
  rw [hev.mfderiv_eq, DifferentialGeometry.Topology.mfderiv_subtypeVal_comp]
  exact hinj

/-- **c3 在 `_HC2` 盘上（G9 主定理）**：`IsMorreyDisk G γU q` + locality + 光滑延拓 `Q` 的内部浸入（K16b）
+ `VJ` 数据（S-W-STAB-2 形）⇒ 对一切 `σ > 0`，`ι ∘ q` 的 S-W-NECK G4 形 `hIMS05`。 -/
theorem ims05_radius_bound_HC2_of_normStability_IM6 [CompleteSpace E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) X) {U : TopologicalSpace.Opens X}
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {γU : freeLoop U} {q : C(closedDisk, U)}
    (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    {Q : ℂ → U} (hQ : SmoothDiskExtension (E := E) q Q)
    (himm : ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (VJ : ℂ → ℝ) (hVJ : ContDiffOn ℝ (⊤ : ℕ∞) VJ (Metric.ball (0 : ℂ) 1))
    (hVJle : ∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤
      -Laplacian.laplacian (fun p => Real.log (diskConformalFactor_IM6 g
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) p)) z /
        (2 * diskConformalFactor_IM6 g ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)
          z) - metricScalarAt g
            (diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z) / 2)
    (hstab : ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + diskConformalFactor_IM6 g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) x * VJ x * ψ x ^ 2))
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) :=
  ims05_radius_bound_of_normStability_IM6 g (diskSmoothInterior_comp_val_IM6 hMor.smoothInterior)
    (fun z hz => diskMapConformalAt_comp_val_IM6 g G hloc (hMor.conformal z hz))
    (fun z hz => injective_mfderiv_diskExtension_comp_val_IM6 hQ hz (himm z hz)) hσ VJ hVJ hVJle
    hstab

section Top

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint

universe u

variable {P : OrientedThreeStage.{u}} {g₀ : P.Metric} {F : GC.Interface.RawSurgery P g₀} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- consumer：Top meridian 的 K16b 版 `_HC2` 盘，ambient 盘 `ι ∘ q` 的 `diskExtension` 在开盘内是浸入
（c3 的 `himm` 输入）。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (t : ℝ), T₀ ≤ t →
      ∃ (U : TopologicalSpace.Opens (postStage F.observation t).Carrier) (q : C(closedDisk, U)),
        range (((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier))).comp q) ⊆ M.exterior.region t ∧
        ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3)
          (diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U, (postStage F.observation t).Carrier)).comp q)) z) := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun t ht => ?_⟩
  obtain ⟨ρ, hρ, -, -, -, γU, q, -, -, -, hrange, -, -, -, -, -, ⟨Q, hQ⟩, himm⟩ :=
    hH T₀ le_rfl t ht
  exact ⟨_, q, hrange, fun z hz =>
    injective_mfderiv_diskExtension_comp_val_IM6 hQ hz (himm Q hQ z hz)⟩

end Top

end GC.LongTime.CuspP1
