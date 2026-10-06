import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurvivorConfinementHC2IM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckMiddleSphereNK

/-!
# HT-L 判据 ⇐ c3 + IMS06′（S-W-NECK G4，已交付）+ c5（O-W-IMS06 G3 第 2 部分，后缀 `_IM6`）

`ht_left_at_event_IM6` 的 left packet 里有一个 confinement 判据："每个 `_HC2` 形 Morrey 盘（子句：
光滑嵌入边界环、`IsMorreyDisk G γU q`、locality、弱 Jordan 迹、`⊆ W`、内部在 `interior W`、
内部浸入）的像 `⊆ K₀`"。本文件把它归约到：

* `hlamP`：共形 IMS05′（σ = 1/2，`lam` 形，逐盘）——S-W-STAB G2/G3 + S-W-EIG G2 + O-W-GEO-MIN G1–G3 合成；
* neck band 数据（逐 neck `b`，与盘无关）：`N b` 开、`Z b` 在 `N b` 上 `C¹`、band 闭包 `⊆ N b`、
  `|dZ|² ≤ 4g`、`R ≥ 1/2`——S-W-NECK G5（c4，
  `IncomingBackwardNeck.slice_band_estimates_half_NK`）给 slice 版；
* `hγband`：边界环 `γ` 不进 band 闭包（`_HC2` confined + band 远离 core collar）；
* R3：`M_s ∖ ⋃ Σ_b ⊆ Us ∪ V`、`Us V` 开不交、`Us ⊆ K₀`、`γ ⊆ Us`——S-A14-SURGERY 认领。

收缩记录：G2 的 `hNECK`（逐盘 "`hIMS05` ⇒ 不碰中间球面"）已由 S-W-NECK G4
`not_mem_middle_sphere_of_stability_bound_NK` 消去（`confined_of_neck_bands_HC2_IM6`），
`htrace` 由 `hγband` + 弱 Jordan 迹得到（`diskTrace_not_mem_of_weakTrace_IM6`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.CuspP1

/-- 弱 Jordan 迹：`γ` 不碰 `B` ⇒ 盘的迹 `diskTrace v` 不碰 `B`（`diskTrace v = γ ∘ σ`）。 -/
theorem diskTrace_not_mem_of_weakTrace_IM6 {Y : Type*} [TopologicalSpace Y] {γ : freeLoop Y}
    {v : C(closedDisk, Y)} (htr : DiskWeakJordanTrace γ v) {B : Set Y} (hγ : ∀ θ, γ θ ∉ B)
    (θ : loopCircle) : diskTrace v θ ∉ B := by
  obtain ⟨σ, -, hσ⟩ := htr
  have h : diskTrace v θ = γ (σ θ) := congrArg (fun c : freeLoop Y => c θ) hσ
  rw [h]
  exact hγ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X]

/-- **G2 的收缩版**（`hNECK` 由 S-W-NECK G4 消去）：`_HC2` 形 Morrey 盘 + `hlam` + neck band 数据 +
`γ` 不进 band 闭包 + R3 ⇒ `range (ι ∘ q) ⊆ K₀`。 -/
theorem confined_of_neck_bands_HC2_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {γU : freeLoop U} {q : C(closedDisk, U)} (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    (hlam : ∀ (d : ℂ → ℝ≥0∞) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      0 < (1 / 2 : ℝ) → d z₀ = 0 →
      (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, d y ≤ d x +
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) (x + t • (y - x))) *
            ‖y - x‖)) →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, d z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))))
    {ι : Type*} (N : ι → Set X) (Z : ι → X → ℝ) (hN : ∀ b, IsOpen (N b))
    (hZ : ∀ b, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (Z b) (N b))
    (hcl : ∀ b, closure {p : X | p ∈ N b ∧ |Z b p| < 20} ⊆ N b)
    (hdz : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (Z b) p w) ^ 2 ≤ 4 * g.inner p w w)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 1 / 2 ≤ metricScalarAt g p)
    {γ : freeLoop X} (htr : DiskWeakJordanTrace γ
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q))
    (hγband : ∀ b θ, γ θ ∉ closure {p : X | p ∈ N b ∧ |Z b p| < 20})
    {Us V K₀ : Set X} (hUs : IsOpen Us) (hV : IsOpen V) (hUV : Disjoint Us V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ N b ∧ Z b x = 0)) → x ∈ Us ∪ V) (hUK : Us ⊆ K₀)
    (hγ : ∀ θ, γ θ ∈ Us) :
    range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ K₀ :=
  confined_of_ims05_HC2_IM6 g G hMor hloc hlam N Z
    (fun b h => not_mem_middle_sphere_of_stability_bound_NK g
      (diskSmoothInterior_comp_val_IM6 hMor.smoothInterior) (hN b) (hZ b) (hcl b) (hdz b) (hR b)
      (diskTrace_not_mem_of_weakTrace_IM6 htr (hγband b)) h)
    hUs hV hUV hsep hUK hγ htr

/-- **HT-L 的 confinement 判据**（`ht_left_at_event_IM6` 的 `hpkt` 最后一个合取项，`X`/`g`/`γ`/`W`
一般化）⇐ 逐盘 `hlamP` + neck band 数据 + `hγband` + R3。 -/
theorem hconf_of_neck_bands_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X) (γ : freeLoop X)
    (W : Set X)
    (hlamP : ∀ (U : TopologicalSpace.Opens X) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
      (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y) →
      DiskWeakJordanTrace γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) →
      range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ W →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z ∈ interior W) →
      (∀ Q : ℂ → U, SmoothDiskExtension (E := E) q Q →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) →
      ∀ (d : ℂ → ℝ≥0∞) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
        0 < (1 / 2 : ℝ) → d z₀ = 0 →
        (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, d y ≤ d x +
          ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g
            ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) (x + t • (y - x))) *
              ‖y - x‖)) →
        IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ ENNReal.ofReal r} →
        (∃ z ∈ Metric.ball (0 : ℂ) 1, d z = ENNReal.ofReal r) →
        (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ ENNReal.ofReal r →
          ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension
            ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) w)) →
        r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))))
    {ι : Type*} (N : ι → Set X) (Z : ι → X → ℝ) (hN : ∀ b, IsOpen (N b))
    (hZ : ∀ b, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (Z b) (N b))
    (hcl : ∀ b, closure {p : X | p ∈ N b ∧ |Z b p| < 20} ⊆ N b)
    (hdz : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (Z b) p w) ^ 2 ≤ 4 * g.inner p w w)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 1 / 2 ≤ metricScalarAt g p)
    (hγband : ∀ b θ, γ θ ∉ closure {p : X | p ∈ N b ∧ |Z b p| < 20})
    {Us V K₀ : Set X} (hUs : IsOpen Us) (hV : IsOpen V) (hUV : Disjoint Us V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ N b ∧ Z b x = 0)) → x ∈ Us ∪ V) (hUK : Us ⊆ K₀)
    (hγ : ∀ θ, γ θ ∈ Us) :
    ∀ (U : TopologicalSpace.Opens X) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
      (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y) →
      DiskWeakJordanTrace γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) →
      range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ W →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z ∈ interior W) →
      (∀ Q : ℂ → U, SmoothDiskExtension (E := E) q Q →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) →
      range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ K₀ :=
  fun U G γU q hsm hMor hloc htr hW hint himm =>
    confined_of_neck_bands_HC2_IM6 g G hMor hloc (hlamP U G γU q hsm hMor hloc htr hW hint himm)
      N Z hN hZ hcl hdz hR htr hγband hUs hV hUV hsep hUK hγ

universe u

variable {P : OrientedThreeStage.{u}} {g₀ : P.Metric} {F : GC.Interface.RawSurgery P g₀} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- consumer：Top meridian 的 `_HC2` 盘（K16b 版）在晚期时刻 `t` 满足判据的全部子句，所以
`hconf_of_neck_exclusion_IM6` 的输出直接给 `range (ι ∘ q) ⊆ K₀`。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ (t : ℝ) (ht : T₀ ≤ t),
      ∃ (U : TopologicalSpace.Opens (postStage F.observation t).Carrier) (q : C(closedDisk, U)),
        ∀ K₀ : Set (postStage F.observation t).Carrier,
        (∀ (U' : TopologicalSpace.Opens (postStage F.observation t).Carrier)
          (G : SmoothRiemannianMetric (𝓡 3) U') (γU : freeLoop U') (q' : C(closedDisk, U')),
          IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU → IsMorreyDisk G γU q' →
          (∀ z : closedDisk, ∀ᶠ y : U' in 𝓝 (q' z),
            G.inner y = ((postMetric F.observation t).restrictOpen U').inner y) →
          DiskWeakJordanTrace (M.transported t (h₀.trans ht))
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U', (postStage F.observation t).Carrier)).comp q') →
          range ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U', (postStage F.observation t).Carrier)).comp q') ⊆ M.exterior.region t →
          (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U', (postStage F.observation t).Carrier)).comp q') z ∈
              interior (M.exterior.region t)) →
          (∀ Q : ℂ → U', SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q' Q →
            ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
          range ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U', (postStage F.observation t).Carrier)).comp q') ⊆ K₀) →
        range ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier)).comp q) ⊆ K₀ := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun t ht => ?_⟩
  obtain ⟨ρ, hρ, -, -, -, γU, q, -, hsm, hMor, hrange, hint, -, -, hweak, hloc, -, himm⟩ :=
    hH T₀ le_rfl t ht
  exact ⟨_, q, fun K₀ hcrit => hcrit _ _ γU q hsm hMor (fun z => (hloc z).mono fun y hy => hy.1)
    hweak hrange hint himm⟩

end GC.LongTime.CuspP1
