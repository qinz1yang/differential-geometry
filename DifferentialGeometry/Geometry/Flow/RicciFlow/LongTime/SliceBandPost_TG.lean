import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SliceMiddleSphereNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageGeneralST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelHistory

/-!
# Route W ⑦（S-W-TOPGLUE，后缀 `_TG`）：band 数据的类型桥 slice ↔ `postStage`

S-W-NECK G5 的 `IncomingBackwardNeck.slice_band_estimates_NK` 在 `(H.stage i.castSucc).Carrier`
与 `B.sliceMetric_NK s = scaleMetric (r²)⁻¹ ((H.event i).incoming.flow.base.metric s)` 上陈述；
Route W 的盘与 region 在 `(postStage F.observation s).Carrier` / `postMetric F.observation s` 上。
本文件取 `H = (F.tower.history n).toHistory`，对 `s ∈ [time i.castSucc, time i.succ)`：

* `activeStage_eq_castSucc_TG`、`postStage_eq_castSucc_TG`：`activeStage ⟨s, _⟩ = i.castSucc`，
  于是 `postStage F.observation s = H.stage i.castSucc`（S-A14-STATIC G5 的
  `postStage_eq_stageAt_tower_ST`）；
* `postMetric_heq_flow_TG`：
  `HEq (postMetric F.observation s) ((H.event i).incoming.flow.base.metric s)`
  （`postMetric_heq_stageMetric_tower_ST` + `stageMetric i.castSucc = incoming.flow.base.metric`）；
* `castChart_TG` / `castHeight_TG`：沿 stage 等式 `X = A` 搬 chart / 高度（`carrierHomeo_CPD2`）；
  `postSliceChart_TG` / `postSliceHeight_TG` / `postSliceMetric_TG` 是 G5 的 `sliceChart_NK` /
  `sliceHeight_NK` / `sliceMetric_NK s` 在 `postStage` 上的版本（函数，无新结构 / 新 Prop）；
* **`slice_band_estimates_post_TG`**：G5 的五联结论（`range` 开、高度光滑、band 闭包在 `range` 内、
  `R ≥ 3/5`、`(dz)² ≤ 2 g`）原样搬到 `postStage` 上；通用搬运引理 `band_transport_TG`
  （`subst` 两个 stage 等式，无任何几何内容）；
* **`not_mem_middle_sphere_of_slice_post_TG`**：形状 = NECK G4 consumer
  `not_mem_middle_sphere_of_slice_NK` 把 `(H.stage i.castSucc).Carrier`、`sliceMetric_NK s`
  换成 `postStage`、`postSliceMetric_TG`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime.CuspP1
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u

section Cast

/-- 沿 stage 等式 `X = A` 把 `A` 里的 chart 搬到 `X` 里（`carrierHomeo_CPD2`）。 -/
def castChart_TG {A X : OrientedThreeStage.{u}} {Y : Type*} [TopologicalSpace Y] (h : X = A)
    (c : C(Y, A.Carrier)) : C(Y, X.Carrier) :=
  ⟨fun y => carrierHomeo_CPD2 h.symm (c y), (carrierHomeo_CPD2 h.symm).continuous.comp c.continuous⟩

/-- 沿 stage 等式 `X = A` 把 `A` 上的函数（高度）搬到 `X` 上。 -/
def castHeight_TG {A X : OrientedThreeStage.{u}} (h : X = A) (Z : A.Carrier → ℝ) :
    X.Carrier → ℝ :=
  fun x => Z (carrierHomeo_CPD2 h x)

theorem carrierHomeo_symm_cancel_TG {A X : OrientedThreeStage.{u}} (h : X = A) (x : X.Carrier) :
    carrierHomeo_CPD2 h.symm (carrierHomeo_CPD2 h x) = x := by
  subst h
  rfl

theorem carrierHomeo_cancel_TG {A X : OrientedThreeStage.{u}} (h : X = A) (a : A.Carrier) :
    carrierHomeo_CPD2 h (carrierHomeo_CPD2 h.symm a) = a := by
  subst h
  rfl

/-- `HEq` 的度量沿 stage 等式 `inner` 逐点相等（载体点经 `carrierHomeo_CPD2`）。 -/
theorem inner_eq_of_heq_homeo_TG {A X : OrientedThreeStage.{u}} (h : X = A) {gX : X.Metric}
    {gA : A.Metric} (hg : HEq gX gA) (p : X.Carrier) (v w : TangentSpace ThreeModel p) :
    gX.inner p v w = gA.inner (carrierHomeo_CPD2 h p) v w := by
  subst h
  rw [eq_of_heq hg]
  rfl

/-- `HEq` 的度量经 `scaleMetric` 仍 `HEq`。 -/
theorem scaleMetric_heq_TG {A X : OrientedThreeStage.{u}} (h : X = A) {gX : X.Metric}
    {gA : A.Metric} (hg : HEq gX gA) (c : ℝ) (hc : 0 < c) :
    HEq (scaleMetric c hc gX) (scaleMetric c hc gA) := by
  subst h
  rw [eq_of_heq hg]

/-- **通用搬运**：A 上的 band 五联结论沿 `X = A` 与 `HEq gX gA` 搬到 `X` 上（chart、高度经
`castChart_TG` / `castHeight_TG`，度量 `gX`）。没有几何内容：`subst` 两个等式。 -/
theorem band_transport_TG {A X : OrientedThreeStage.{u}} (h : X = A) {gA : A.Metric}
    {gX : X.Metric} (hg : HEq gX gA) {δ a C : ℝ} {c : C(neckBuffer δ, A.Carrier)}
    {Z : A.Carrier → ℝ} (h1 : IsOpen (Set.range c))
    (h2 : ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ Z (Set.range c))
    (h3 : closure {p : A.Carrier | p ∈ Set.range c ∧ |Z p| < 20} ⊆ Set.range c)
    (h4 : ∀ p ∈ Set.range c, |Z p| < 20 → a ≤ metricScalarAt gA p)
    (h5 : ∀ p ∈ Set.range c, |Z p| < 20 → ∀ w : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ C * gA.inner p w w) :
    IsOpen (Set.range (castChart_TG h c)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (castHeight_TG h Z) (Set.range (castChart_TG h c)) ∧
      closure {p : X.Carrier | p ∈ Set.range (castChart_TG h c) ∧
          |castHeight_TG h Z p| < 20} ⊆ Set.range (castChart_TG h c) ∧
      (∀ p ∈ Set.range (castChart_TG h c), |castHeight_TG h Z p| < 20 →
        a ≤ metricScalarAt gX p) ∧
      (∀ p ∈ Set.range (castChart_TG h c), |castHeight_TG h Z p| < 20 →
        ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (castHeight_TG h Z) p w) ^ 2 ≤
            C * gX.inner p w w) := by
  subst h
  rw [eq_of_heq hg]
  exact ⟨h1, h2, h3, h4, h5⟩

end Cast

section Stage

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ)

/-- `s ∈ [time i.castSucc, time i.succ)` ⇒ `activeStage ⟨s, _⟩ = i.castSucc`。 -/
theorem activeStage_eq_castSucc_TG (H : ObservedHistory.{u}) (i : Fin H.eventCount) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) H.horizon) (h0 : H.time i.castSucc ≤ s) (h1 : s < H.time i.succ) :
    H.activeStage ⟨s, hs⟩ = i.castSucc := by
  refine H.activeStage_eq_of_maximal ⟨s, hs⟩ i.castSucc h0 (fun k hk => ?_)
  by_contra hlt
  have hsk : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hlt)
  exact absurd (lt_of_lt_of_le h1 ((H.time_strictMono.monotone hsk).trans hk)) (lt_irrefl _)

/-- `s ∈ [time i.castSucc, time i.succ)` 时，`s` 的 `s` 时刻 slice `postStage F.observation s`
就是 stage `H.stage i.castSucc`（`H = (F.tower.history n).toHistory`）。 -/
theorem postStage_eq_castSucc_TG (i : Fin (F.tower.history n).toHistory.eventCount) {s : ℝ}
    (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) :
    postStage F.observation s = (F.tower.history n).toHistory.stage i.castSucc := by
  have hs : s ∈ Icc (0 : ℝ) (F.tower.history n).toHistory.horizon :=
    ⟨(ObservedHistory.time_nonneg _ _).trans h0,
      (h1.trans_le (ObservedHistory.time_le_horizon_at _ _)).le⟩
  refine (postStage_eq_stageAt_tower_ST F n ⟨s, hs⟩).trans ?_
  exact congrArg (F.tower.history n).toHistory.stage
    (activeStage_eq_castSucc_TG _ i hs h0 h1)

/-- 同一区间上 `postMetric F.observation s` 与 incoming flow 的度量 `HEq`。 -/
theorem postMetric_heq_flow_TG (i : Fin (F.tower.history n).toHistory.eventCount) {s : ℝ}
    (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) :
    HEq (postMetric F.observation s)
      (((F.tower.history n).toHistory.event i).incoming.flow.base.metric s) := by
  have hs : s ∈ Icc (0 : ℝ) (F.tower.history n).toHistory.horizon :=
    ⟨(ObservedHistory.time_nonneg _ _).trans h0,
      (h1.trans_le (ObservedHistory.time_le_horizon_at _ _)).le⟩
  refine (postMetric_heq_stageMetric_tower_ST F n ⟨s, hs⟩).trans ?_
  have hact := activeStage_eq_castSucc_TG (F.tower.history n).toHistory i hs h0 h1
  have key : ∀ j j' : Fin ((F.tower.history n).toHistory.eventCount + 1), j = j' →
      HEq ((F.tower.history n).toHistory.stageMetric j s)
        ((F.tower.history n).toHistory.stageMetric j' s) := by
    intro j j' hjj
    subst hjj
    exact HEq.rfl
  refine (key _ _ hact).trans ?_
  simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
  exact HEq.rfl

end Stage

section Band

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ)
  {i : Fin (F.tower.history n).toHistory.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck ((F.tower.history n).toHistory.event i).terminal.metric δ k} {r : ℝ}
  (B : IncomingBackwardNeck (F.tower.history n).toHistory i neck r)

/-- `B.sliceChart_NK` 在 `postStage F.observation s` 里的版本。 -/
def postSliceChart_TG {s : ℝ} (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) :
    C(neckBuffer δ, (postStage F.observation s).Carrier) :=
  castChart_TG (postStage_eq_castSucc_TG F n i h0 h1) B.sliceChart_NK

/-- `B.sliceHeight_NK` 在 `postStage F.observation s` 里的版本。 -/
def postSliceHeight_TG {s : ℝ} (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) :
    (postStage F.observation s).Carrier → ℝ :=
  castHeight_TG (postStage_eq_castSucc_TG F n i h0 h1) B.sliceHeight_NK

/-- `B.sliceMetric_NK s` 的 `postStage` 版本：`(r²)⁻¹ · postMetric F.observation s`。 -/
def postSliceMetric_TG (s : ℝ) :
    SmoothRiemannianMetric ThreeModel (postStage F.observation s).Carrier :=
  scaleMetric (r ^ 2)⁻¹ (inv_pos.mpr (pow_pos B.radius_pos 2)) (postMetric F.observation s)

/-- `postSliceMetric_TG s` 与 `B.sliceMetric_NK s` `HEq`。 -/
theorem postSliceMetric_heq_TG {s : ℝ} (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) :
    HEq (postSliceMetric_TG F n B s) (B.sliceMetric_NK s) :=
  scaleMetric_heq_TG (postStage_eq_castSucc_TG F n i h0 h1) (postMetric_heq_flow_TG F n i h0 h1)
    _ _

/-- `postSliceChart_TG` 的像 = `B.sliceChart_NK` 的像沿 `carrierHomeo_CPD2` 的原像。 -/
theorem range_postSliceChart_TG {s : ℝ}
    (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) :
    Set.range (postSliceChart_TG F n B h0 h1) =
      carrierHomeo_CPD2 (postStage_eq_castSucc_TG F n i h0 h1) ⁻¹' Set.range B.sliceChart_NK := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (carrierHomeo_cancel_TG _ _).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change carrierHomeo_CPD2 (postStage_eq_castSucc_TG F n i h0 h1).symm (B.sliceChart_NK y) = p
    rw [hy]
    exact carrierHomeo_symm_cancel_TG _ _

theorem postSliceHeight_apply_TG {s : ℝ} (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ)
    (p : (postStage F.observation s).Carrier) :
    postSliceHeight_TG F n B h0 h1 p =
      B.sliceHeight_NK (carrierHomeo_CPD2 (postStage_eq_castSucc_TG F n i h0 h1) p) := rfl

/-- `postSliceMetric_TG s` 的 `inner` 就是 `(r²)⁻¹ ·` `postMetric F.observation s` 的 `inner`
（IMS05′ 在 `postMetric` 上陈述时的换算）。 -/
theorem postSliceMetric_inner_TG (s : ℝ) (p : (postStage F.observation s).Carrier)
    (v w : TangentSpace ThreeModel p) :
    (postSliceMetric_TG F n B s).inner p v w =
      (r ^ 2)⁻¹ * (postMetric F.observation s).inner p v w :=
  scaleMetric_inner _ _ _ _ _ _

/-- 沿 stage 等式，`postSliceMetric_TG s` 的 `inner` 与 `B.sliceMetric_NK s` 的 `inner` 逐点相等。 -/
theorem postSliceMetric_inner_eq_TG {s : ℝ}
    (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s)
    (h1 : s < (F.tower.history n).toHistory.time i.succ) (p : (postStage F.observation s).Carrier)
    (v w : TangentSpace ThreeModel p) :
    (postSliceMetric_TG F n B s).inner p v w =
      (B.sliceMetric_NK s).inner (carrierHomeo_CPD2 (postStage_eq_castSucc_TG F n i h0 h1) p)
        v w :=
  inner_eq_of_heq_homeo_TG (postStage_eq_castSucc_TG F n i h0 h1)
    (postSliceMetric_heq_TG F n B h0 h1) p v w

/-- **⑦ 主定理**：S-W-NECK G5 的 `slice_band_estimates_NK` 搬到 `postStage F.observation s` /
`postMetric` 上（`s ∈ [time i.castSucc, time i.succ)` 的 `d`-左邻域）。 -/
theorem slice_band_estimates_post_TG (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      IsOpen (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (postSliceHeight_TG F n B h0 h1)
        (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      closure {p : (postStage F.observation s).Carrier |
          p ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
            |postSliceHeight_TG F n B h0 h1 p| < 20} ⊆
        Set.range (postSliceChart_TG F n B h0 h1) ∧
      (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1), |postSliceHeight_TG F n B h0 h1 p| < 20 →
        3 / 5 ≤ metricScalarAt (postSliceMetric_TG F n B s) p) ∧
      (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1), |postSliceHeight_TG F n B h0 h1 p| < 20 →
        ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (postSliceHeight_TG F n B h0 h1) p w) ^ 2 ≤
            2 * (postSliceMetric_TG F n B s).inner p w w) := by
  obtain ⟨d, hd, h⟩ := B.slice_band_estimates_NK hk hδ
  refine ⟨d, hd, fun s h0 hs1 h1 => ?_⟩
  obtain ⟨h1', h2', h3', h4', h5'⟩ := h s hs1 h1
  exact band_transport_TG (postStage_eq_castSucc_TG F n i h0 h1)
    (postSliceMetric_heq_TG F n B h0 h1) h1' h2' h3' h4' h5'

/-- **⑦ consumer（形状 = `not_mem_middle_sphere_of_slice_NK`）**：`postStage F.observation s` 上、
开盘内光滑、`q(∂D)` 与 band 闭包不交、满足 IMS05′ 的盘 `q` 不碰中间球面 `{height = 0}`。 -/
theorem not_mem_middle_sphere_of_slice_post_TG (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      ∀ q : C(closedDisk, (postStage F.observation s).Carrier),
        DiskSmoothInterior (E := ThreeSpace) q →
        (∀ θ : loopCircle, diskTrace q θ ∉
          closure {p : (postStage F.observation s).Carrier |
            p ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
              |postSliceHeight_TG F n B h0 h1 p| < 20}) →
        (∀ (z₀ : ℂ) (ρ : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < ρ →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
            diskEDist_NK (postSliceMetric_TG F n B s) q z₀ z ≤ ENNReal.ofReal ρ} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n B s) q z₀ z = ENNReal.ofReal ρ) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n B s) q z₀ z ≤ ENNReal.ofReal ρ →
            ∀ᶠ w in 𝓝 z, 1 / 2 ≤
              metricScalarAt (postSliceMetric_TG F n B s) (diskExtension q w)) →
          ρ ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) →
        ∀ ζ : closedDisk, ¬ (q ζ ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
          postSliceHeight_TG F n B h0 h1 (q ζ) = 0) := by
  obtain ⟨d, hd, h⟩ := slice_band_estimates_post_TG F n B hk hδ
  refine ⟨d, hd, fun s h0 hs1 h1 q hq htrace hIMS05 => ?_⟩
  obtain ⟨hN, hZ, hcl, hR, hdz⟩ := h s h0 hs1 h1
  refine not_mem_middle_sphere_of_stability_bound_NK (postSliceMetric_TG F n B s) hq hN
    (hZ.of_le (by exact_mod_cast le_top)) hcl ?_ ?_ htrace hIMS05
  · exact fun p hp hz w => by
      have h5 := hdz p hp hz w
      have h0' := metric_inner_self_nonneg (postSliceMetric_TG F n B s) p w
      linarith
  · exact fun p hp hz => (by norm_num : (1 : ℝ) / 2 ≤ 3 / 5).trans (hR p hp hz)

end Band

/-- consumer：record 的 `backward α`（`GeometricCutoffRecord`）上 ⑦ 直接适用（型对齐，同 G5 的 example，
`H = (F.tower.history n).toHistory`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ)
    {i : Fin (F.tower.history n).toHistory.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord (F.tower.history n).toHistory i p)
    (α : ((F.tower.history n).toHistory.event i).transition.trace.tubes.Index)
    (hδ : R.delta α ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      IsOpen (Set.range (postSliceChart_TG F n (R.backward α) h0 h1)) := by
  obtain ⟨d, hd, h⟩ := slice_band_estimates_post_TG F n (R.backward α) (R.two_le_order_NK α) hδ
  exact ⟨d, hd, fun s h0 hs1 h1 => (h s h0 hs1 h1).1⟩

end GC.LongTime
