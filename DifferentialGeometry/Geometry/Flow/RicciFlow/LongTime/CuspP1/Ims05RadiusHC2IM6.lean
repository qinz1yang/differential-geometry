import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.DiskConformalLengthIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.InteriorImmersionHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricLocality_GB

/-!
# c3：IMS05′ 在 `_HC2` Morrey 盘上的实例化（O-W-IMS06 G1，后缀 `_IM6`）

`_HC2`（S-MIRRORS G4 + S-K16B-PORT G_final）给出开子流形 `U = {ρ < a}` 上的 Morrey 盘
`q : C(closedDisk, U)`（`IsMorreyDisk G γU q`，`G` = canonical positive-domain metric），以及
"`G = g` 在 `q` 的像的邻域上"的 locality 子句。本文件把 `DiskConformalLengthIM6` 的通用 c3
搬到 ambient 盘 `ι ∘ q`（`ι = Subtype.val`，度量 `g = postMetric t`）：

* `diskSmoothInterior_comp_val_IM6`、`diskMapConformalAt_comp_val_IM6`：`ι ∘ q` 在开盘内光滑、
  对 `g` 共形（`diskMapConformalAt_congr_of_metric_GB` + `diskMapConformalAt_restrictOpen`）；
* `ims05_radius_bound_HC2_IM6`（G1 主定理）：`_HC2` 子句 + 共形 IMS05′（`lam` 形，显式前提 `hlam`，
  未到的 STAB/EIG/GEO-MIN/GEO 合成）⇒ S-W-NECK G4 的 `hIMS05`（`σ` 一般，`d_q = diskEDist_NK g (ι ∘ q)`）。
* consumer：对 Top meridian 的 `_HC2` 盘逐字实例化（σ = 1/2 即 NECK G4 的参数形状）。

`hlam` 是尚未到的输入（显式 ∀-前提；S-W-STAB G2/G3、S-W-EIG G2、O-W-GEO-MIN G3 到后收缩）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.CuspP1

universe u

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X]

omit [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X] in
/-- `ι ∘ q` 在开盘内光滑（`ι = Subtype.val`）。 -/
theorem diskSmoothInterior_comp_val_IM6 {U : TopologicalSpace.Opens X} {q : C(closedDisk, U)}
    (hq : DiskSmoothInterior (E := E) q) :
    DiskSmoothInterior (E := E)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) :=
  contMDiff_subtype_val.comp_contMDiffOn hq

/-- `G = g` 在 `q` 的像的邻域上 + `q` 对 `G` 共形 ⇒ `ι ∘ q` 对 `g` 共形。 -/
theorem diskMapConformalAt_comp_val_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) X) {U : TopologicalSpace.Opens X}
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {q : C(closedDisk, U)}
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    {z : ℂ} (hz : DiskMapConformalAt G (diskExtension q) z) :
    DiskMapConformalAt g
      (diskExtension ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)) z := by
  have hpt : ∀ v w : TangentSpace 𝓘(ℝ, E) (diskExtension q z),
      G.inner (diskExtension q z) v w = (g.restrictOpen U).inner (diskExtension q z) v w := by
    intro v w
    have h := (hloc (diskRetraction z)).self_of_nhds
    exact congrArg (fun A => A v w) h
  exact (diskMapConformalAt_restrictOpen g U (diskExtension q) z).mp
    ((diskMapConformalAt_congr_of_metric_GB G (g.restrictOpen U) hpt).mp hz)

/-- **c3（G1 主定理）**：Morrey 盘 `q`（对开子流形 `U` 上的 `G`）+ locality `G = g` near `q` ⇒
对 ambient 盘 `ι ∘ q`：共形 IMS05′（`lam` 形 `hlam`）⇒ S-W-NECK G4 的 `hIMS05`（`σ` 版）。 -/
theorem ims05_radius_bound_HC2_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) X) {U : TopologicalSpace.Opens X}
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {γU : freeLoop U} {q : C(closedDisk, U)}
    (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    {σ : ℝ} (hσ : 0 < σ)
    (hlam : ∀ (d : ℂ → ℝ≥0∞) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r → 0 < σ →
      d z₀ = 0 →
      (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, d y ≤ d x +
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) (x + t • (y - x))) *
            ‖y - x‖)) →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, d z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) :
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
  ims05_radius_bound_of_conformal_IM6 g (diskSmoothInterior_comp_val_IM6 hMor.smoothInterior)
    (fun z hz => diskMapConformalAt_comp_val_IM6 g G hloc (hMor.conformal z hz)) hσ hlam

end Generic

section Top

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- consumer：Top meridian 的 `_HC2` 盘（K16b 版）在每个晚期时刻 `t` 满足 c3：
`hlam(ι ∘ q, σ) ⇒ hIMS05(ι ∘ q, σ)`；`σ = 1/2` 时右边逐字是 S-W-NECK G4 的显式参数。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (U : TopologicalSpace.Opens (postStage F.observation t).Carrier)
        (q : C(closedDisk, U)),
        range (((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier))).comp q) ⊆ M.exterior.region t ∧
        ∀ σ : ℝ, 0 < σ →
        (∀ (d : ℂ → ℝ≥0∞) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r → 0 < σ →
          d z₀ = 0 →
          (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, d y ≤ d x +
            ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6
              (postMetric F.observation t)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
                C(U, (postStage F.observation t).Carrier)).comp q) (x + s • (y - x))) *
                ‖y - x‖)) →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ ENNReal.ofReal r} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1, d z = ENNReal.ofReal r) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ ENNReal.ofReal r →
            ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation t) (diskExtension
              ((⟨Subtype.val, continuous_subtype_val⟩ :
                C(U, (postStage F.observation t).Carrier)).comp q) w)) →
          r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) →
        ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK (postMetric F.observation t)
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation t).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation t)
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation t).Carrier)).comp q) z₀ z = ENNReal.ofReal r) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation t)
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation t).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r →
            ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation t) (diskExtension
              ((⟨Subtype.val, continuous_subtype_val⟩ :
                C(U, (postStage F.observation t).Carrier)).comp q) w)) →
          r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, -, -, -, γU, q, -, -, hMor, hrange, -, -, -, -, hloc, -, -⟩ := hH T h t ht
  refine ⟨_, q, hrange, fun σ hσ hlam => ?_⟩
  exact ims05_radius_bound_HC2_IM6 (postMetric F.observation t) _ hMor
    (fun z => (hloc z).mono fun y hy => hy.1) hσ hlam

end Top

end GC.LongTime.CuspP1
