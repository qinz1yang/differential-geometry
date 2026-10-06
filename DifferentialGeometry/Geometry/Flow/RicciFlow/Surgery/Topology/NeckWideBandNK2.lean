import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSliceBandNK

/-!
# Route W, R3：surgery 前 slice 的 wide neck band（S-W-NECK-2 G1，后缀 `_NK2`）

S-W-NECK G5 的 `slice_band_estimates_NK` 只给 band `|z| < 20`。R3 的切割球面分离需要覆盖整段
static collar `{0 ≤ z_s ≤ 50}` = 原 neck 坐标 `z ∈ ±[1, 51]` 的 band。但 G5 的圆柱侧估计
`IncomingBackwardNeck.band_cyl_NK` 本来就在整个 `neckClosedTest δ = {|z| ≤ δ⁻¹}` 上成立
（`parabolic_closeness` 的 `x ∈ neckClosedTest δ`），所以 band 的宽度只是 `chart_band_estimates_NK`
里写死的 `20`。本文件把它换成任意高度集 `T ⊆ [-δ⁻¹, δ⁻¹]`：

* `closure_height_set_chart_NK2`、`chart_band_estimates_wide_NK2`：一般嵌入 `c` 上的转运
  （`chart_band_estimates_NK` 的 `|z| < 20` → `z ∈ T`）；
* **`IncomingBackwardNeck.slice_band_estimates_wide_NK2`**：`∃ d > 0`，`s ∈ [τ₀ − d, τ₀)` 时，
  对所有 `T ⊆ [-δ⁻¹, δ⁻¹]`：`closure {p ∈ range c | Z p ∈ T} ⊆ range c`、`R ≥ 3/5`、
  `(dz)² ≤ 2 g`（`d` 与 `T` 无关）；
* **`IncomingBackwardNeck.slice_band_estimates_center_NK2`**：`T = {|z − c₀| < w}`，`|c₀| + w ≤ δ⁻¹`
  （例如 `c₀ = ±26, w = 26`，`δ ≤ 1/40000` 时 `|c₀| + w = 52 ≤ δ⁻¹`）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private lemma infty_ne_zero_NK2 : (∞ : WithTop ℕ∞) ≠ 0 := by decide

universe u

section Chart

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

omit [IsManifold ThreeModel ∞ M] in
/-- 高度落在 `T ⊆ [-δ⁻¹, δ⁻¹]` 的点集的闭包仍在 `range c` 内（紧集 `c '' {|z| ≤ δ⁻¹}`）。 -/
theorem closure_height_set_chart_NK2 {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) {T : Set ℝ}
    (hT : ∀ z ∈ T, |z| ≤ δ⁻¹) :
    closure {p : M | p ∈ Set.range c ∧ chartHeight_NK c p ∈ T} ⊆ Set.range c := by
  have hK : IsCompact (c '' {y : neckBuffer δ | |y.1.2| ≤ δ⁻¹}) :=
    (isCompact_neckHeightLe_NK δ δ⁻¹ le_rfl).image hc.contMDiff.continuous
  have hsub : {p : M | p ∈ Set.range c ∧ chartHeight_NK c p ∈ T} ⊆
      c '' {y : neckBuffer δ | |y.1.2| ≤ δ⁻¹} := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    rw [chartHeight_chart_NK hc.isEmbedding.injective] at hy
    exact ⟨y, hT _ hy, rfl⟩
  exact (closure_minimal hsub hK.isClosed).trans (Set.image_subset_range _ _)

/-- **一般嵌入、一般高度集的 band 估计转运**：`ĝ = c^* gm` 在 `z ∈ T`（`T ⊆ [-δ⁻¹, δ⁻¹]`）上满足
`a ≤ R`、`(dz)² ≤ C ĝ`，则 `gm` 在 `range c` 的 `{Z ∈ T}` 上满足同样估计。 -/
theorem chart_band_estimates_wide_NK2 {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c)
    (gm : SmoothRiemannianMetric ThreeModel M)
    (ĝ : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (hĝ : ∀ x V W, ĝ.inner x V W = gm.inner (c x)
      (mfderiv NeckCylinderModel ThreeModel c x V) (mfderiv NeckCylinderModel ThreeModel c x W))
    {a C : ℝ} {T : Set ℝ}
    (hR : ∀ x : neckBuffer δ, x.1.2 ∈ T → a ≤ metricScalarAt ĝ x)
    (hdz : ∀ x : neckBuffer δ, x.1.2 ∈ T → ∀ w : TangentSpace NeckCylinderModel x,
      (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x w) ^ 2 ≤
        C * ĝ.inner x w w) :
    (∀ p ∈ Set.range c, chartHeight_NK c p ∈ T → a ≤ metricScalarAt gm p) ∧
    (∀ p ∈ Set.range c, chartHeight_NK c p ∈ T → ∀ w : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) p w) ^ 2 ≤
        C * gm.inner p w w) := by
  have hlocal := isLocalDiffeomorph_of_embedding_NK hc
  have hEq : ĝ = localPullMetric gm c hlocal := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [localPullMetric_inner, hĝ]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ hz
    rw [chartHeight_chart_NK hc.isEmbedding.injective] at hz
    have := hR x hz
    rwa [hEq, metricScalarAt_localPull] at this
  · rintro _ ⟨x, rfl⟩ hz w
    rw [chartHeight_chart_NK hc.isEmbedding.injective] at hz
    obtain ⟨v, hv⟩ := (hlocal.mfderivToContinuousLinearEquiv infty_ne_zero_NK2 x).surjective w
    have hv' : mfderiv NeckCylinderModel ThreeModel c x v = w := by
      rw [← hv]
      exact (hlocal.mfderivToContinuousLinearEquiv_coe infty_ne_zero_NK2 x ▸ rfl)
    have hZ : MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) (c x) :=
      (((contMDiffOn_chartHeight_NK hc) _ ⟨x, rfl⟩).contMDiffAt
        ((isOpen_range_chart_of_embedding_NK hc).mem_nhds ⟨x, rfl⟩)).mdifferentiableAt
        (by simp)
    have hC : MDifferentiableAt NeckCylinderModel ThreeModel c x :=
      hc.contMDiff.mdifferentiableAt (by simp)
    have hcomp : chartHeight_NK c ∘ c = fun y : neckBuffer δ => y.1.2 :=
      funext (chartHeight_chart_NK hc.isEmbedding.injective)
    have hchain := mfderiv_comp x hZ hC
    rw [hcomp] at hchain
    have hdz' : (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) (c x) w) =
        (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x v) := by
      rw [hchain]
      change _ = (mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) (c x))
        (mfderiv NeckCylinderModel ThreeModel c x v)
      rw [hv']
    rw [hdz', ← hv', ← hĝ]
    exact hdz x hz v

end Chart

section Slice

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

/-- **G1：surgery 前 slice 的 wide neck band 估计**。`d` 与高度集 `T` 无关；`T` 任意
`⊆ [-δ⁻¹, δ⁻¹]`（整个 `neckClosedTest δ`）。常数同 G5：`R ≥ 3/5`、`(dz)² ≤ 2 g`。 -/
theorem IncomingBackwardNeck.slice_band_estimates_wide_NK2
    (B : IncomingBackwardNeck H i neck r) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      IsOpen (Set.range B.sliceChart_NK) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ B.sliceHeight_NK (Set.range B.sliceChart_NK) ∧
      ∀ T : Set ℝ, (∀ z ∈ T, |z| ≤ δ⁻¹) →
        closure {p : (H.stage i.castSucc).Carrier |
            p ∈ Set.range B.sliceChart_NK ∧ B.sliceHeight_NK p ∈ T} ⊆
          Set.range B.sliceChart_NK ∧
        (∀ p ∈ Set.range B.sliceChart_NK, B.sliceHeight_NK p ∈ T →
          3 / 5 ≤ metricScalarAt (B.sliceMetric_NK s) p) ∧
        (∀ p ∈ Set.range B.sliceChart_NK, B.sliceHeight_NK p ∈ T →
          ∀ w : TangentSpace ThreeModel p,
            (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) B.sliceHeight_NK p w) ^ 2 ≤
              2 * (B.sliceMetric_NK s).inner p w w) := by
  have hr2 : 0 < r ^ 2 := pow_pos B.radius_pos 2
  have hlt : H.time i.castSucc < H.time i.succ := (H.event i).incoming.lt
  refine ⟨min (r ^ 2 / 2) (H.time i.succ - H.time i.castSucc), lt_min (by positivity)
    (by linarith), fun s hs1 hs2 => ?_⟩
  have hs1' : H.time i.succ - r ^ 2 / 2 ≤ s := hs1.trans' (by
    linarith [min_le_left (r ^ 2 / 2) (H.time i.succ - H.time i.castSucc)])
  have hs1'' : H.time i.castSucc ≤ s := hs1.trans' (by
    linarith [min_le_right (r ^ 2 / 2) (H.time i.succ - H.time i.castSucc)])
  set v : ℝ := (s - H.time i.succ) / r ^ 2 with hvdef
  have hv0 : v < 0 := div_neg_of_neg_of_pos (by linarith) hr2
  have hvhalf : -1 / 2 ≤ v := by
    rw [hvdef, le_div_iff₀ hr2]
    linarith
  have hsv : H.time i.succ + r ^ 2 * v = s := by
    have : r ^ 2 * v = s - H.time i.succ := by
      rw [hvdef, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hr2.ne'
    linarith
  have ha : H.time i.succ - r ^ 2 < H.time i.succ := sub_lt_self _ hr2
  have hslab := B.metric_on_slab i le_rfl ha v ⟨by linarith, hv0⟩ (by rw [hsv]; exact hs1'')
    (by rw [hsv]; exact hs2)
  have hemb := B.stageChart_smooth i le_rfl ha
  refine ⟨isOpen_range_chart_of_embedding_NK hemb, contMDiffOn_chartHeight_NK hemb,
    fun T hT => ⟨closure_height_set_chart_NK2 hemb hT, ?_⟩⟩
  have hclosed : ∀ x : neckBuffer δ, x.1.2 ∈ T → x ∈ neckClosedTest δ := fun x hx =>
    abs_le.mp (hT _ hx)
  exact chart_band_estimates_wide_NK2 hemb (B.sliceMetric_NK s) (B.metric v)
    (fun x V W => by
      change _ = (scaleMetric _ _ _).inner _ _ _
      rw [scaleMetric_inner, hslab x V W, hsv])
    (a := 3 / 5) (C := 2) (T := T)
    (fun x hx => (B.band_cyl_NK hk hδ v ⟨hvhalf, hv0.le⟩ x (hclosed x hx)).1)
    (fun x hx w => (B.band_cyl_NK hk hδ v ⟨hvhalf, hv0.le⟩ x (hclosed x hx)).2 w)

/-- **G1（带中心）**：band `{|z − c₀| < w}`，`|c₀| + w ≤ δ⁻¹`；`d` 与 `(c₀, w)` 无关。 -/
theorem IncomingBackwardNeck.slice_band_estimates_center_NK2
    (B : IncomingBackwardNeck H i neck r) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      ∀ c₀ w : ℝ, |c₀| + w ≤ δ⁻¹ →
        closure {p : (H.stage i.castSucc).Carrier |
            p ∈ Set.range B.sliceChart_NK ∧ |B.sliceHeight_NK p - c₀| < w} ⊆
          Set.range B.sliceChart_NK ∧
        (∀ p ∈ Set.range B.sliceChart_NK, |B.sliceHeight_NK p - c₀| < w →
          3 / 5 ≤ metricScalarAt (B.sliceMetric_NK s) p) ∧
        (∀ p ∈ Set.range B.sliceChart_NK, |B.sliceHeight_NK p - c₀| < w →
          ∀ v : TangentSpace ThreeModel p,
            (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) B.sliceHeight_NK p v) ^ 2 ≤
              2 * (B.sliceMetric_NK s).inner p v v) := by
  obtain ⟨d, hd, h⟩ := B.slice_band_estimates_wide_NK2 hk hδ
  refine ⟨d, hd, fun s hs1 hs2 c₀ w hcw => ?_⟩
  have hT : ∀ z ∈ {z : ℝ | |z - c₀| < w}, |z| ≤ δ⁻¹ := fun z hz => by
    have h1 : |z| ≤ |c₀| + |z - c₀| := by
      calc |z| = |c₀ + (z - c₀)| := by rw [add_sub_cancel]
        _ ≤ |c₀| + |z - c₀| := abs_add_le _ _
    exact (h1.trans (by linarith [(show |z - c₀| < w from hz)]))
  exact (h s hs1 hs2).2.2 {z : ℝ | |z - c₀| < w} hT

end Slice

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
