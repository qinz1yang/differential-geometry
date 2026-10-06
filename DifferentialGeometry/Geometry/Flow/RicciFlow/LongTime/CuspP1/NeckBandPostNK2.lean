import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandShiftNK2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepWindowSG2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TransportedNonnegIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SliceBandPost_TG

/-!
# R3：wide band 搬到 `postStage`，以及 `{0 ≤ z_s ≤ 50}` 上的标量曲率下界（S-W-NECK-2 G3，后缀 `_NK2`）

* `exists_pos_le_of_finite_NK2`：有限个正数的公共下界（对 retained boundary 取一致的 `d`）；
* `band_transport_wide_NK2`、**`slice_band_estimates_wide_post_NK2`**：G1 的
  `slice_band_estimates_wide_NK2` 搬到 `postStage F.observation s` / `postMetric`（照 TOPGLUE
  `band_transport_TG`，高度集 `T ⊆ [-δ⁻¹, δ⁻¹]` 任意，`postSliceChart_TG` 等直接 import）；
  `slice_band_estimates_center_post_NK2` 是 `T = {|z − c₀| < w}`（`|c₀| + w ≤ δ⁻¹`）的带中心形状；
* `scalar_lower_on_neckSlab_flow_NK2`：stage 层（`(H.stage i.castSucc).Carrier`，incoming flow 的度量
  `g_s`）：`∀ b, ∀ x ∈ neckSlab R b (Icc 0 50)`，`3/(5 r_b²) ≤ R_{g_s}(x)`（`s ∈ [τ₀ − d, τ₀)`；G1 的带中心版本
  `c₀ = σ_b · 26, w = 26` + G2 的 `neckSlab_subset_center_band_NK2` + `scaleMetric` 换算）；
* **`scalar_nonneg_on_retained_slab_NK2`**（coordinator 指定形状）：`∀ b, ∀ x ∈
  sliceHomeo_SG2 '' neckSlab R b (Icc 0 50), 0 ≤ metricScalarAt (postMetric T s) x`
  （`scalar_lower_on_retained_slab_NK2` 给 `3/(5 r_b²)` 的正下界），`T` 为任意 observation tower
  （`T := F.observation` 即 IMS06 的 `postMetric F.observation s`）；
* `transported_not_mem_retained_slab_NK2`（consumer）：与 IMS06 G10 的 `hneg` 版 ⑧ 合成，
  给 SURGERY-2 `exists_window_separation_SG2` 的 `hγ` 第二合取项
  `γ_s θ ∉ e_s '' neckSlab R b (Icc 0 50)`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
universe u

/-- 有限个正数有公共正下界。 -/
theorem exists_pos_le_of_finite_NK2 {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ b, 0 < f b) :
    ∃ d : ℝ, 0 < d ∧ ∀ b, d ≤ f b := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun b => isEmptyElim b⟩
  · obtain ⟨b₀, hb₀⟩ := Finite.exists_min f
    exact ⟨f b₀, hf b₀, hb₀⟩

section Transport

/-- **通用搬运（高度集版）**：`A` 上的 wide band 估计沿 `X = A` 与 `HEq gX gA` 搬到 `X`
（`band_transport_TG` 的 `|Z| < 20` → `Z ∈ T`；没有几何内容，`subst`）。 -/
theorem band_transport_wide_NK2 {A X : OrientedThreeStage.{u}} (h : X = A) {gA : A.Metric}
    {gX : X.Metric} (hg : HEq gX gA) {δ a C : ℝ} {c : C(neckBuffer δ, A.Carrier)}
    {Z : A.Carrier → ℝ} {T : Set ℝ} (h1 : IsOpen (Set.range c))
    (h2 : ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ Z (Set.range c))
    (h3 : closure {p : A.Carrier | p ∈ Set.range c ∧ Z p ∈ T} ⊆ Set.range c)
    (h4 : ∀ p ∈ Set.range c, Z p ∈ T → a ≤ metricScalarAt gA p)
    (h5 : ∀ p ∈ Set.range c, Z p ∈ T → ∀ w : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ C * gA.inner p w w) :
    IsOpen (Set.range (castChart_TG h c)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (castHeight_TG h Z) (Set.range (castChart_TG h c)) ∧
      closure {p : X.Carrier | p ∈ Set.range (castChart_TG h c) ∧
          castHeight_TG h Z p ∈ T} ⊆ Set.range (castChart_TG h c) ∧
      (∀ p ∈ Set.range (castChart_TG h c), castHeight_TG h Z p ∈ T →
        a ≤ metricScalarAt gX p) ∧
      (∀ p ∈ Set.range (castChart_TG h c), castHeight_TG h Z p ∈ T →
        ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (castHeight_TG h Z) p w) ^ 2 ≤
            C * gX.inner p w w) := by
  subst h
  rw [eq_of_heq hg]
  exact ⟨h1, h2, h3, h4, h5⟩

end Transport

section Post

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ)
  {i : Fin (F.tower.history n).toHistory.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck ((F.tower.history n).toHistory.event i).terminal.metric δ k} {r : ℝ}
  (B : IncomingBackwardNeck (F.tower.history n).toHistory i neck r)

/-- **G3：wide band 的 postStage 版**（`slice_band_estimates_post_TG` 的高度集推广）。 -/
theorem slice_band_estimates_wide_post_NK2 (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      IsOpen (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (postSliceHeight_TG F n B h0 h1)
        (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      ∀ T : Set ℝ, (∀ z ∈ T, |z| ≤ δ⁻¹) →
        closure {p : (postStage F.observation s).Carrier |
            p ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
              postSliceHeight_TG F n B h0 h1 p ∈ T} ⊆
          Set.range (postSliceChart_TG F n B h0 h1) ∧
        (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
          postSliceHeight_TG F n B h0 h1 p ∈ T →
          3 / 5 ≤ metricScalarAt (postSliceMetric_TG F n B s) p) ∧
        (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
          postSliceHeight_TG F n B h0 h1 p ∈ T → ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (postSliceHeight_TG F n B h0 h1) p w) ^ 2 ≤
            2 * (postSliceMetric_TG F n B s).inner p w w) := by
  obtain ⟨d, hd, h⟩ := B.slice_band_estimates_wide_NK2 hk hδ
  refine ⟨d, hd, fun s h0 hs1 h1 => ?_⟩
  obtain ⟨h1', h2', h3'⟩ := h s hs1 h1
  have hT := fun T hT => band_transport_wide_NK2 (postStage_eq_castSucc_TG F n i h0 h1)
    (postSliceMetric_heq_TG F n B h0 h1) h1' h2' (h3' T hT).1 (h3' T hT).2.1 (h3' T hT).2.2
  obtain ⟨hA, hB, -⟩ := hT {0} (fun z hz => by
    rw [mem_singleton_iff.mp hz, abs_zero]
    exact inv_nonneg.mpr (neck.delta_pos.le))
  exact ⟨hA, hB, fun T hTT => (hT T hTT).2.2⟩

/-- **G3（带中心，IMS06 `(N b, Z b)` 形状）**：`T = {|z − c₀| < w}`，`|c₀| + w ≤ δ⁻¹`。取
`Z b p := postSliceHeight p − c₀`、`N b := range (postSliceChart_TG …)` 即 `|Z b p| < w`
（`w = 20`、`c₀ = σ_b · 51` 是围绕切割球面 `Σ_b = {z_s = 50}` 的 band）。 -/
theorem slice_band_estimates_center_post_NK2 (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      IsOpen (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (postSliceHeight_TG F n B h0 h1)
        (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      ∀ c₀ w : ℝ, |c₀| + w ≤ δ⁻¹ →
        closure {p : (postStage F.observation s).Carrier |
            p ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
              |postSliceHeight_TG F n B h0 h1 p - c₀| < w} ⊆
          Set.range (postSliceChart_TG F n B h0 h1) ∧
        (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
          |postSliceHeight_TG F n B h0 h1 p - c₀| < w →
          3 / 5 ≤ metricScalarAt (postSliceMetric_TG F n B s) p) ∧
        (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
          |postSliceHeight_TG F n B h0 h1 p - c₀| < w → ∀ v : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (postSliceHeight_TG F n B h0 h1) p v) ^ 2 ≤
            2 * (postSliceMetric_TG F n B s).inner p v v) := by
  obtain ⟨d, hd, h⟩ := slice_band_estimates_wide_post_NK2 F n B hk hδ
  refine ⟨d, hd, fun s h0 hs1 h1 => ?_⟩
  obtain ⟨hA, hB, hC⟩ := h s h0 hs1 h1
  refine ⟨hA, hB, fun c₀ w hcw => ?_⟩
  have hT : ∀ z ∈ {z : ℝ | |z - c₀| < w}, |z| ≤ δ⁻¹ := fun z hz => by
    have h1 : |z| ≤ |c₀| + |z - c₀| := by
      calc |z| = |c₀ + (z - c₀)| := by rw [add_sub_cancel]
        _ ≤ |c₀| + |z - c₀| := abs_add_le _ _
    exact (h1.trans (by linarith [(show |z - c₀| < w from hz)]))
  exact hC {z : ℝ | |z - c₀| < w} hT

end Post

section Flow

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- **stage 层的标量曲率下界**：晚期（`R.delta b.1.1 ≤ 1/40000`）时，`s ∈ [τ₀ − d, τ₀)` 的 incoming flow 度量
`g_s` 在整段 static slab `{0 ≤ z_s ≤ 50}` 上 `R ≥ 3/(5 r_b²) > 0`（`r_b = nominalRadius`）。
`d` 对所有 retained boundary 一致。 -/
theorem scalar_lower_on_neckSlab_flow_NK2 (R : GeometricCutoffRecord H i p)
    (hδ : ∀ b : (H.event i).RetainedBoundaryIndex, R.delta b.1.1 ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      ∀ b : (H.event i).RetainedBoundaryIndex, ∀ x ∈ neckSlab_SG2 R b (Icc 0 50),
        3 / (5 * (R.nominalRadius ⟨b.1.1⟩) ^ 2) ≤
          metricScalarAt ((H.event i).incoming.flow.base.metric s) x := by
  have hex : ∀ b : (H.event i).RetainedBoundaryIndex, ∃ d : ℝ, 0 < d ∧
      ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      ∀ c₀ w : ℝ, |c₀| + w ≤ (R.delta b.1.1)⁻¹ →
        closure {x : (H.stage i.castSucc).Carrier |
            x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
              |(R.backward b.1.1).sliceHeight_NK x - c₀| < w} ⊆
          Set.range (R.backward b.1.1).sliceChart_NK ∧
        (∀ x ∈ Set.range (R.backward b.1.1).sliceChart_NK,
          |(R.backward b.1.1).sliceHeight_NK x - c₀| < w →
          3 / 5 ≤ metricScalarAt ((R.backward b.1.1).sliceMetric_NK s) x) ∧
        (∀ x ∈ Set.range (R.backward b.1.1).sliceChart_NK,
          |(R.backward b.1.1).sliceHeight_NK x - c₀| < w → ∀ v : TangentSpace ThreeModel x,
            (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (R.backward b.1.1).sliceHeight_NK x v) ^ 2 ≤
              2 * ((R.backward b.1.1).sliceMetric_NK s).inner x v v) :=
    fun b => (R.backward b.1.1).slice_band_estimates_center_NK2 (R.two_le_order_NK b.1.1) (hδ b)
  choose d hd hband using hex
  obtain ⟨d₀, hd₀, hle⟩ := exists_pos_le_of_finite_NK2 d hd
  refine ⟨d₀, hd₀, fun s hs1 hs2 b x hx => ?_⟩
  have hsb : H.time i.succ - d b ≤ s := by linarith [hle b]
  have hδb : (40000 : ℝ) ≤ (R.delta b.1.1)⁻¹ := by
    have hpos := R.delta_pos b.1.1
    rw [le_inv_comm₀ (by norm_num) hpos]
    simpa using hδ b
  have hc : |retainedSign_NK2 b * (1 + 25)| + 26 ≤ (R.delta b.1.1)⁻¹ := by
    rw [abs_mul, abs_retainedSign_NK2, one_mul, abs_of_pos (by norm_num)]
    linarith
  have hmem := neckSlab_subset_center_band_NK2 R b (S := Icc 0 50) (m := 25) (w := 26)
    (fun z hz => by
      rw [abs_lt]
      constructor <;> linarith [hz.1, hz.2]) hx
  have h35 := (hband b s hsb hs2 _ 26 hc).2.1 x hmem.1 hmem.2
  have hr2 : 0 < (R.nominalRadius ⟨b.1.1⟩) ^ 2 := pow_pos (R.backward b.1.1).radius_pos 2
  change 3 / 5 ≤ metricScalarAt (scaleMetric _ _ _) x at h35
  rw [metricScalarAt_scaleMetric, inv_inv] at h35
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Flow

section Retained

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) (N : ℕ)
  (i : Fin (T.history N).eventCount) {p : CutoffParameters}

/-- 沿 stage 等式的标量曲率搬运（`subst`）。 -/
theorem metricScalarAt_eq_of_heq_homeo_NK2 {A X : OrientedThreeStage.{u}} (h : X = A)
    {gX : X.Metric} {gA : A.Metric} (hg : HEq gX gA) (x : X.Carrier) :
    metricScalarAt gX x = metricScalarAt gA (carrierHomeo_CPD2 h x) := by
  subst h
  rw [eq_of_heq hg]
  rfl

/-- window 的 slice 上 `postMetric T s` 与 incoming flow 的度量 `HEq`（`activeStage s = i.castSucc`）。 -/
theorem postMetric_heq_flow_NK2 (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (T.history N).horizon)
    (hact : (T.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc) :
    HEq (postMetric T s) (((T.history N).event i).incoming.flow.base.metric s) := by
  refine (postMetric_heq_stageMetric_ST T N ⟨s, hs0, hsh⟩).trans ?_
  have key : ∀ j j' : Fin ((T.history N).eventCount + 1), j = j' →
      HEq ((T.history N).stageMetric j s) ((T.history N).stageMetric j' s) := by
    intro j j' hjj
    subst hjj
    exact HEq.rfl
  refine (key _ _ hact).trans ?_
  simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
  exact HEq.rfl

/-- `sliceHomeo_SG2` 搬运标量曲率：`R_{postMetric s}(e x) = R_{g_s}(x)`。 -/
theorem metricScalarAt_postMetric_sliceHomeo_NK2 (s : ℝ) (hs0 : 0 ≤ s)
    (hsh : s ≤ (T.history N).horizon)
    (hact : (T.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc)
    (x : ((T.history N).stage i.castSucc).Carrier) :
    metricScalarAt (postMetric T s) (sliceHomeo_SG2 T N i s hs0 hsh hact x) =
      metricScalarAt (((T.history N).event i).incoming.flow.base.metric s) x := by
  have h : postStage T s = (T.history N).stage i.castSucc :=
    (postStage_eq_stage_active_CPD2 T N ⟨s, hs0, hsh⟩).trans
      (congrArg (T.history N).stage hact)
  have hx : sliceHomeo_SG2 T N i s hs0 hsh hact x = carrierHomeo_CPD2 h.symm x := rfl
  rw [hx, metricScalarAt_eq_of_heq_homeo_NK2 h (postMetric_heq_flow_NK2 T N i s hs0 hsh hact),
    carrierHomeo_cancel_TG h x]

/-- **G3（正下界）**：`s ∈ [τ₀ − d, τ₀)` 时，`e_s '' {0 ≤ z_s ≤ 50}` 上
`R_{postMetric s} ≥ 3/(5 r_b²)`。 -/
theorem scalar_lower_on_retained_slab_NK2 (R : GeometricCutoffRecord (T.history N) i p)
    (hδ : ∀ b : ((T.history N).event i).RetainedBoundaryIndex,
      R.delta b.1.1 ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (T.history N).horizon)
      (hact : (T.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc),
      (T.history N).time i.succ - d ≤ s → s < (T.history N).time i.succ →
      ∀ b : ((T.history N).event i).RetainedBoundaryIndex,
        ∀ x ∈ sliceHomeo_SG2 T N i s hs0 hsh hact '' neckSlab_SG2 R b (Icc 0 50),
          3 / (5 * (R.nominalRadius ⟨b.1.1⟩) ^ 2) ≤ metricScalarAt (postMetric T s) x := by
  obtain ⟨d, hd, h⟩ := scalar_lower_on_neckSlab_flow_NK2 R hδ
  refine ⟨d, hd, fun s hs0 hsh hact hs1 hs2 b x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  rw [metricScalarAt_postMetric_sliceHomeo_NK2]
  exact h s hs1 hs2 b y hy

/-- **G3（coordinator 指定形状）**：`∀ b, ∀ x ∈ e_s '' neckSlab R b (Icc 0 50)`，
`0 ≤ metricScalarAt (postMetric T s) x`（`s ∈ [τ₀ − d, τ₀)`）。 -/
theorem scalar_nonneg_on_retained_slab_NK2 (R : GeometricCutoffRecord (T.history N) i p)
    (hδ : ∀ b : ((T.history N).event i).RetainedBoundaryIndex,
      R.delta b.1.1 ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (T.history N).horizon)
      (hact : (T.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc),
      (T.history N).time i.succ - d ≤ s → s < (T.history N).time i.succ →
      ∀ b : ((T.history N).event i).RetainedBoundaryIndex,
        ∀ x ∈ sliceHomeo_SG2 T N i s hs0 hsh hact '' neckSlab_SG2 R b (Icc 0 50),
          0 ≤ metricScalarAt (postMetric T s) x := by
  obtain ⟨d, hd, h⟩ := scalar_lower_on_retained_slab_NK2 T N i R hδ
  refine ⟨d, hd, fun s hs0 hsh hact hs1 hs2 b x hx => ?_⟩
  have hr2 : 0 < (R.nominalRadius ⟨b.1.1⟩) ^ 2 := pow_pos (R.backward b.1.1).radius_pos 2
  exact (div_nonneg (by norm_num) (by positivity)).trans (h s hs0 hsh hact hs1 hs2 b x hx)

end Retained

section Consumer

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} (N : ℕ) (i : Fin (F.observation.history N).eventCount)
  {p : CutoffParameters}

/-- **consumer**：`scalar_nonneg_on_retained_slab_NK2`（`T := F.observation`）+ IMS06 G10 的集合版 ⑧
⇒ `hγ` 第二合取项：cusp collar `R_post < 0`（`hneg`）时，`γ_s θ` 不落在任何 `e_s '' N_b`
（`N_b = {0 ≤ z_s ≤ 50}`）里。 -/
theorem transported_not_mem_retained_slab_NK2
    (R : GeometricCutoffRecord (F.observation.history N) i p)
    (hδ : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      R.delta b.1.1 ≤ 1 / 40000) (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (F.observation.history N).horizon)
      (hact : (F.observation.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc),
      (F.observation.history N).time i.succ - d ≤ s → s < (F.observation.history N).time i.succ →
      ∀ hs : M.exterior.start ≤ s,
      (∀ q ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
        riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
          (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) q < 0) →
      ∀ θ : loopCircle, ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
        M.transported s hs θ ∉
          sliceHomeo_SG2 F.observation N i s hs0 hsh hact '' neckSlab_SG2 R b (Icc 0 50) := by
  obtain ⟨d, hd, h⟩ := scalar_nonneg_on_retained_slab_NK2 F.observation N i R hδ
  refine ⟨d, hd, fun s hs0 hsh hact hs1 hs2 hs hneg θ => ?_⟩
  exact transported_not_mem_of_scalar_nonneg_IM6 M hs hneg
    (fun b => sliceHomeo_SG2 F.observation N i s hs0 hsh hact '' neckSlab_SG2 R b (Icc 0 50))
    (fun b => h s hs0 hsh hact hs1 hs2 b) θ

end Consumer

end GC.LongTime.CuspP1
