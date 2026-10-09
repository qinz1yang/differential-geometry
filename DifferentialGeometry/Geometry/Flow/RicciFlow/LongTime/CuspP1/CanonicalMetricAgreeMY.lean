import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget

/-!
# O-A08 G0′（Route W）：canonical positive-domain metric 在 `{ρ ≤ a/2}` 上等于原度量

`_HC`（`P2AdapterImportedMorreyHC.lean`）与 `_HC2` 的 Morrey disk 生活在 open target
`U = {ρ < a}` 上，度量是 `G = canonicalPositiveDomainMetric_P2A g hδ U hU`
`= exp (2 F) • g.restrictOpen U`，`F = -log (cutoff_P2A a ρ)`。因为 `cutoff_P2A a r = 1`
当 `r ≤ a/2`，所以在 `{ρ ≤ a/2}`（包含 region `W = {ρ ≤ 0}` 及其开邻域 `{ρ < a/2}`）上
`G.inner = (g.restrictOpen U).inner`——这是**由定义**得到的整片等式，不只是 `_HC` 结论里
沿 Morrey disk 像点的 local metric clause。

* `cutoff_eq_one_of_le_half_MY`：`r ≤ a/2 → cutoff_P2A a r = 1`；
* `canonicalPositiveDomainMetric_inner_eq_of_le_half_MY`：`ρ x ≤ a/2 → G.inner x = g|_U.inner x`；
* `canonicalPositiveDomainMetric_inner_eq_of_nonpos_MY`：`ρ x ≤ 0` 的特例（region `W` 上）；
* `canonicalPositiveDomainMetric_inner_eventuallyEq_MY`：`ρ x ≤ 0 → ∀ᶠ y in 𝓝 x, G.inner y = …`
  （开集 `{ρ < a/2}` 上相等，供 conformality / tension 等导数级量的 transfer）；
* consumer `riemannianDiskArea_canonicalPositiveDomainMetric_eq_MY`：range 在 `{ρ ≤ a/2}` 里的
  盘 `u : closedDisk → U`，`riemannianDiskArea G u = riemannianDiskArea g (Subtype.val ∘ u)`
  （Route W 的 A′ 等号与 MY 路线 IMS03 `hmetric` 都要这一步）。

只 import sorry-free 的 `P2AdapterImportedDefs`（IMS03 定义的逐字拷贝）与
`Measure/Area/OpenTarget`；不 import 任何 sorry mirror。无新结构 / 新 Prop。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set TopologicalSpace Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

/-- `cutoff_P2A a r = 1` 当 `r ≤ a/2`（`smoothTransition` 在非正参数处为 `0`）。 -/
theorem cutoff_eq_one_of_le_half_MY {a r : ℝ} (ha : 0 < a) (hr : r ≤ a / 2) :
    cutoff_P2A a r = 1 := by
  have h : 2 * r / a - 1 ≤ 0 := by
    have h2 : 2 * r / a ≤ 1 := by
      rw [div_le_one ha]
      linarith
    linarith
  simp only [cutoff_P2A, Real.smoothTransition.zero_of_nonpos h, sub_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- 在 `{ρ ≤ a/2}` 上 canonical positive-domain metric 与 `g.restrictOpen U` 逐点相等。 -/
theorem canonicalPositiveDomainMetric_inner_eq_of_le_half_MY
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a : ℝ} (ha : 0 < a)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ := (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x := fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    ∀ x : U, ρ (x : M) ≤ a / 2 →
      (canonicalPositiveDomainMetric_P2A g hδ U hU).inner x =
        (g.restrictOpen U).inner x := by
  intro U δ hδ hU x hx
  have h1 : δ (x : M) = 1 := cutoff_eq_one_of_le_half_MY ha hx
  ext v w
  change Real.exp (2 * -Real.log (δ (x : M))) * (g.restrictOpen U).inner x v w = _
  rw [h1, Real.log_one, neg_zero, mul_zero, Real.exp_zero, one_mul]

/-- region `W = {ρ ≤ 0}` 上的特例。 -/
theorem canonicalPositiveDomainMetric_inner_eq_of_nonpos_MY
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a : ℝ} (ha : 0 < a)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ := (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x := fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    ∀ x : U, ρ (x : M) ≤ 0 →
      (canonicalPositiveDomainMetric_P2A g hδ U hU).inner x =
        (g.restrictOpen U).inner x := by
  intro U δ hδ hU x hx
  exact canonicalPositiveDomainMetric_inner_eq_of_le_half_MY g ha hρ x
    (hx.trans (by positivity))

/-- region 的每一点有一个邻域（`{ρ < a/2}`）上两度量相等：导数级量（conformality、tension、
曲率）的 transfer 用这个形状。 -/
theorem canonicalPositiveDomainMetric_inner_eventuallyEq_MY
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a : ℝ} (ha : 0 < a)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ := (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x := fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    ∀ x : U, ρ (x : M) ≤ 0 → ∀ᶠ y : U in 𝓝 x,
      (canonicalPositiveDomainMetric_P2A g hδ U hU).inner y =
        (g.restrictOpen U).inner y := by
  intro U δ hδ hU x hx
  have hopen : IsOpen {y : U | ρ (y : M) < a / 2} :=
    isOpen_lt (hρ.continuous.comp continuous_subtype_val) continuous_const
  have hmem : x ∈ {y : U | ρ (y : M) < a / 2} := by
    change ρ (x : M) < a / 2
    linarith
  filter_upwards [hopen.mem_nhds hmem] with y hy
  exact canonicalPositiveDomainMetric_inner_eq_of_le_half_MY g ha hρ y (le_of_lt hy)

/-- **Consumer.**  range 落在 `{ρ ≤ a/2}` 的盘，`G`-面积 = ambient `g`-面积（经 inclusion）。 -/
theorem riemannianDiskArea_canonicalPositiveDomainMetric_eq_MY
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a : ℝ} (ha : 0 < a)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ := (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x := fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    ∀ u : closedDisk → U, (∀ z, ρ (u z : M) ≤ a / 2) →
      riemannianDiskArea (canonicalPositiveDomainMetric_P2A g hδ U hU) u =
        riemannianDiskArea g (Subtype.val ∘ u) := by
  intro U δ hδ hU u hu
  rw [← riemannianDiskArea_restrictOpen g U u]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  unfold riemannianAreaDensity tangentTwoJacobian
  rw [canonicalPositiveDomainMetric_inner_eq_of_le_half_MY g ha hρ (diskExtension u z)
    (hu (diskRetraction z))]

end GC.LongTime.CuspP1
