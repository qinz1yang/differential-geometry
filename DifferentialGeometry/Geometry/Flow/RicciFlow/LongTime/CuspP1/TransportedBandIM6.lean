import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftCriterionIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization
import DifferentialGeometry.Topology.Manifold.ImmersionRange

/-!
# ⑧ `hγband`：prescribed 边界环不进 neck band 的闭包（O-W-IMS06 G5，后缀 `_IM6`）

蓝图论证（IMS06 / IAU02）："actual torus boundaries have negative scalar curvature, so they are
outside these positive bands"。`γ_s = M.transported s` 落在 cusp collar
`O_s := cores.map M.model s '' riemannianBallOf h x₀ (accuracy s)⁻¹`（`M.prescribed` +
`exterior.in_ball`），`O_s` 开（`cores.embedding` 同维 ⇒ 开嵌入，`riemannianBallOf` 开）；band 上
`R ≥ 1/2`（S-W-NECK G2/G5），collar 上 `R < 0` ⇒ `O_s` 是 `γ_s θ` 的开邻域且与 band 不交 ⇒
`γ_s θ ∉ closure band`。不需要标量曲率的连续性。

* `not_mem_closure_of_open_neg_IM6`：抽象版（`S : X → ℝ` 任意）。
* `isOpen_collar_IM6`、`transported_mem_collar_IM6`：`O_s` 开、`γ_s ⊆ O_s`。
* **`transported_not_mem_band_IM6`**：显式前提 `hneg`（collar 上 `metricScalarAt (postMetric s) < 0`）
  ⇒ `∀ b θ, γ_s θ ∉ closure {p ∈ N b | |Z b p| < 20}`
  （G3 `confined_of_neck_bands_HC2_IM6` 的 `hγband`）。
  `hneg` 的来源：`cores.metric_error`（`k ≤ 2`）⇒ `t⁻¹ g` 在 collar ball 上 `C²` 接近双曲模型
  （`R_h = −6`）⇒ `abs_scalar_curvature_sub_le_of_small_metric_derivatives` ⇒ `R < 0`（未做，见 HANDOVER）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- 抽象：`x` 有开邻域 `O`，`O` 上 `S < 0`，`B` 上 `S ≥ 1/2` ⇒ `x ∉ closure B`。 -/
theorem not_mem_closure_of_open_neg_IM6 {X : Type*} [TopologicalSpace X] (S : X → ℝ)
    {O B : Set X} (hO : IsOpen O) (hneg : ∀ x ∈ O, S x < 0) (hB : ∀ p ∈ B, 1 / 2 ≤ S p)
    {x : X} (hx : x ∈ O) : x ∉ closure B := by
  intro hcl
  obtain ⟨p, hpO, hpB⟩ := mem_closure_iff.mp hcl O hO hx
  linarith [hneg p hpO, hB p hpB]

/-- D-R3-6 的公共紧控制接口：固定紧片 `C ⊆ D′`（`D′` 开）⇒ `ι '' C ⊆ ι '' interior (closure D′)`，
即 c5 落在 `ψ_s '' C` 的盘也落在 `tpw_of_window_compact_IM6`（`KD = closure D′`）的 `K₀` 里。 -/
theorem image_subset_interior_closure_IM6 {D X : Type*} [TopologicalSpace D] (ι : D → X)
    {C D' : Set D} (hCD : C ⊆ D') (hD' : IsOpen D') :
    ι '' C ⊆ ι '' interior (closure D') :=
  image_mono (hCD.trans (interior_maximal subset_closure hD'))

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- cusp collar `O_s = map '' riemannianBallOf h x₀ (accuracy s)⁻¹` 是开集。 -/
theorem isOpen_collar_IM6 (i : Fin cores.count) {s : ℝ} (hs : cores.start ≤ s) :
    IsOpen (cores.map i s hs '' riemannianBallOf (cores.model i).metric
      (cores.model i).basepoint (cores.accuracy s)⁻¹) := by
  have hemb := cores.embedding i s hs
  have hoe : Topology.IsOpenEmbedding
      (fun x : cores.domain i s => cores.map i s hs x) :=
    ⟨hemb.isEmbedding, Manifold.isOpen_range_of_isSmoothEmbedding (by simp) hemb⟩
  have hball : riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy s)⁻¹ ⊆ cores.domain i s := cores.advertised_ball i s hs
  have himg : cores.map i s hs '' riemannianBallOf (cores.model i).metric
      (cores.model i).basepoint (cores.accuracy s)⁻¹ =
      (fun x : cores.domain i s => cores.map i s hs x) ''
        (Subtype.val ⁻¹' riemannianBallOf (cores.model i).metric
          (cores.model i).basepoint (cores.accuracy s)⁻¹) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hball hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himg]
  exact hoe.isOpenMap _ ((isOpen_riemannianBallOf _ _ _).preimage continuous_subtype_val)

/-- prescribed 边界环 `γ_s` 落在 cusp collar `O_s` 里。 -/
theorem transported_mem_collar_IM6 (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ}
    (hs : M.exterior.start ≤ s) (θ : loopCircle) :
    M.transported s hs θ ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹ := by
  rw [M.prescribed s hs θ]
  refine mem_image_of_mem _ (M.exterior.in_ball M.model s hs ?_)
  exact ⟨(M.exterior.truncation M.model).boundary.torusMap M.port (M.loop θ),
    ((M.exterior.truncation M.model).cusp_zero M.port (M.loop θ)).symm⟩

/-- **⑧ `hγband`**：cusp collar 上 `R < 0`（显式前提 `hneg`，`cores.metric_error` 的 `C²` 推论）、
neck band 上 `R ≥ 1/2` ⇒ `γ_s` 不进任何 band 的闭包。 -/
theorem transported_not_mem_band_IM6 (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ}
    (hs : M.exterior.start ≤ s)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    {ι : Type*} (N : ι → Set (postStage F.observation s).Carrier)
    (Z : ι → (postStage F.observation s).Carrier → ℝ)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 1 / 2 ≤ metricScalarAt (postMetric F.observation s) p)
    (b : ι) (θ : loopCircle) :
    M.transported s hs θ ∉ closure {p | p ∈ N b ∧ |Z b p| < 20} :=
  not_mem_closure_of_open_neg_IM6 (metricScalarAt (postMetric F.observation s))
    (isOpen_collar_IM6 M.model (M.exterior.after_cores.trans hs)) hneg
    (fun p hp => hR b p hp.1 hp.2) (transported_mem_collar_IM6 M hs θ)

/-- consumer：`transported_not_mem_band_IM6` 直接填入 G3 `hconf_of_neck_bands_IM6` 的 `hγband`
（`X = M_s`、`γ = γ_s`、`W = region s`），判据剩下 `hlamP`、band 数据、R3。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ} (hs : M.exterior.start ≤ s)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    {ι : Type} (N : ι → Set (postStage F.observation s).Carrier)
    (Z : ι → (postStage F.observation s).Carrier → ℝ)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 →
      1 / 2 ≤ metricScalarAt (postMetric F.observation s) p)
    (Us V K₀ : Set (postStage F.observation s).Carrier) :=
  hconf_of_neck_bands_IM6 (postMetric F.observation s) (M.transported s hs) (M.exterior.region s)
    (N := N) (Z := Z) (hR := hR) (hγband := transported_not_mem_band_IM6 M hs hneg N Z hR)
    (Us := Us) (V := V) (K₀ := K₀)

end GC.LongTime.CuspP1
