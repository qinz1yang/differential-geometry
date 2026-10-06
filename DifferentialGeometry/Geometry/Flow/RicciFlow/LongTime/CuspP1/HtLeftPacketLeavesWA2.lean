import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RetainedBandDataWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTpwTopRangeWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CollarScalarNegTopHN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftEventIM6

/-!
# surgery 时刻左侧 left packet `hpkt` 的总装（O-W-ASSEMBLY-2 G9，第 4 部分，后缀 `_WA2`）

`hpkt_of_leaves_WA2 H hdec M h6E`：结论 = O-W-IMS06 G3 `ht_left_at_event_IM6` 的 `hpkt` 逐字
（= ASSEMBLY G6 `…_WA6` 的 `hpkt` 槽位）。唯一显式前提 `h6E`（⑥：晚期每个 `_HC2` 形 Morrey 盘、每个
`σ > 0` 的 IMS05′，O-W-IMS06 G16 交付）。其余全部由已交付定理供给：

* window + TPW + `γ_s ⊆ range ι_s`：本车道 `exists_tpw_Top_range_WA2`（tight window，`∀ KD` 紧子句）；
* event 指标：S-A14-SURGERY-2 `window_event_stages_SG2`（`Fs = i.castSucc`、`Ls = i.succ`）；
* record `R = H.records N i`；`hcol`：S-A14-SURGERY G3 `exists_late_collar_SG`；
  `R.delta ≤ 1/40000`：`R.delta_le` + `H.accuracy_eq` + `hdec`；
* R3 分离 + c5：本车道 `exists_retained_confinement_WA2`（S-A14-SURGERY-2 G3′ + O-W-IMS06 G2/G8/G10）；
* ⑧ `hneg`：O-W-HNEG G2 `PrescribedCuspMeridianTop_CPQ.eventually_scalar_neg_on_collar_HN`；
* c9b：S-W-NECK-2 G3 `scalar_nonneg_on_retained_slab_NK2`；c9a：本车道 `retained_band_data_WA2`
  （S-W-NECK-2 G1–G3 的平移 band，中心 `σ_b · 51`）。

`T₁ := max (start + 1) (max (max (B_col + 1) (B_δ + 1)) (max T_neg T_6))`；
`η := min (min η_TPW (min d_slab d_band)) (τ₀ − a)`；`K₀ := ι_s '' interior KD`
（`KD` 来自 R3，与 `s`、`ε` 无关）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **HT-L left packet 总装**：`h6E`（⑥ 逐盘 IMS05′，晚期）⇒ `hpkt`（`ht_left_at_event_IM6` 逐字）。 -/
theorem hpkt_of_leaves_WA2 {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (h6E : ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
      ∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
          (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U) (q : C(closedDisk, U)),
          IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
          IsMorreyDisk G γU q →
          (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
            G.inner y = ((postMetric F.observation s).restrictOpen U).inner y) →
          DiskWeakJordanTrace (M.transported s hs)
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) →
          range ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U, (postStage F.observation s).Carrier)).comp q) ⊆ M.exterior.region s →
          (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z ∈
              interior (M.exterior.region s)) →
          (∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
            ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
          ∀ σ : ℝ, 0 < σ → ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
            IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r} →
            (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z = ENNReal.ofReal r) →
            (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r →
              ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation s) (diskExtension
                ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) w)) →
            r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
    ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
      t₀ - η < s → s < t₀ →
      ∃ (K₀ : Set (postStage F.observation s).Carrier)
        (φ : (postStage F.observation s).Carrier → (postStage F.observation t₀).Carrier),
        IsOpen K₀ ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K₀ ∧
        MapsTo φ (K₀ ∩ M.exterior.region s) (M.exterior.region t₀) ∧
        (∀ θ, φ (M.transported s hs θ) = M.transported t₀ ht₀ θ) ∧
        (∀ p ∈ K₀, ∀ w : TangentSpace (𝓡 3) p,
          (postMetric F.observation t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
              (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
            Real.exp ε * (postMetric F.observation s).inner p w w) ∧
        ∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
          (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U) (q : C(closedDisk, U)),
          IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
          IsMorreyDisk G γU q →
          (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
            G.inner y = ((postMetric F.observation s).restrictOpen U).inner y) →
          DiskWeakJordanTrace (M.transported s hs)
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) →
          range ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U, (postStage F.observation s).Carrier)).comp q) ⊆ M.exterior.region s →
          (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z ∈
              interior (M.exterior.region s)) →
          (∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
            ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
          range ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(U, (postStage F.observation s).Carrier)).comp q) ⊆ K₀ := by
  obtain ⟨Bc, hBc⟩ := exists_late_collar_SG H hdec
  obtain ⟨Bδ, hBδ⟩ := hdec (1 / 40000) (by norm_num)
  obtain ⟨Tn, hTn⟩ := M.eventually_scalar_neg_on_collar_HN
  obtain ⟨T6, hT6⟩ := h6E
  have hA := le_max_left (M.exterior.start + 1) (max (max (Bc + 1) (Bδ + 1)) (max Tn T6))
  have hB := le_max_right (M.exterior.start + 1) (max (max (Bc + 1) (Bδ + 1)) (max Tn T6))
  have hB1 := le_max_left (max (Bc + 1) (Bδ + 1)) (max Tn T6)
  have hB2 := le_max_right (max (Bc + 1) (Bδ + 1)) (max Tn T6)
  have hc1 := le_max_left (Bc + 1) (Bδ + 1)
  have hc2 := le_max_right (Bc + 1) (Bδ + 1)
  have hn1 := le_max_left Tn T6
  have hn2 := le_max_right Tn T6
  refine ⟨max (M.exterior.start + 1)
    (max (max (Bc + 1) (Bδ + 1)) (max Tn T6)), by linarith, ?_⟩
  intro t₀ ht₀ hT hE ε hε
  have hτ₀' : M.exterior.start < t₀ := by linarith
  obtain ⟨N, Fs, Ls, hFL, J, hJh, hst, hτJ, a, b, hJab, hτab, hEab, Φ, C, ha, -, hJo, ⟨w₀⟩, -, -,
    -, -, -, hleft, hright, hγι, hKD⟩ := exists_tpw_Top_range_WA2 cores M hτ₀'
  obtain ⟨i, hi, rfl, rfl⟩ := window_event_stages_SG2 F.observation N hE hJo hJh hτJ hleft hright
  have hcol : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      100 < (((H.records N i).static b).delta)⁻¹ := fun b =>
    hBc N i b (by
      change Bc < (F.observation.history N).time i.succ
      rw [hi]
      linarith)
  have hδb : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      (H.records N i).delta b.1.1 ≤ 1 / 40000 := fun b => by
    have h1 := (H.records N i).delta_le b.1.1
    rw [H.accuracy_eq] at h1
    have h2 : Bδ < (F.observation.history N).time i.succ := by
      rw [hi]
      linarith
    exact h1.trans (hBδ _ h2).le
  obtain ⟨KD, hKDc, hconf⟩ :=
    exists_retained_confinement_WA2 M N i (H.records N i) hcol hFL J hJh hst
  obtain ⟨d₁, hd₁, hslab⟩ :=
    scalar_nonneg_on_retained_slab_NK2 F.observation N i (H.records N i) hδb
  obtain ⟨d₂, hd₂, hband⟩ := retained_band_data_WA2 N i (H.records N i) hδb
  obtain ⟨η, hη, hmet⟩ := hKD KD hKDc ε hε
  have hm1 := min_le_left (min η (min d₁ d₂)) (t₀ - a)
  have hm2 := min_le_right (min η (min d₁ d₂)) (t₀ - a)
  have hm3 := min_le_left η (min d₁ d₂)
  have hm4 := min_le_right η (min d₁ d₂)
  have hm5 := min_le_left d₁ d₂
  have hm6 := min_le_right d₁ d₂
  refine ⟨min (min η (min d₁ d₂)) (t₀ - a), lt_min (lt_min hη (lt_min hd₁ hd₂)) (by linarith),
    fun s hs hTs hlo hhi => ?_⟩
  have hsab : s ∈ Icc a b := ⟨by linarith, (hhi.trans_le hτab.2).le⟩
  have habs : |s - t₀| < η := by
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨hopen, hsmooth, hmaps, htrans, hmetric⟩ := hmet s hsab hhi habs w₀
  have hsJ : s ∈ J := hJab hsab
  have hact := hleft s (hJh s hsJ).1 (hJh s hsJ).2 hsJ hhi
  have hs1 : (F.observation.history N).time i.succ - d₁ ≤ s := by
    rw [hi]
    linarith
  have hs1' : (F.observation.history N).time i.succ - d₂ ≤ s := by
    rw [hi]
    linarith
  have hs2 : s < (F.observation.history N).time i.succ := by
    rw [hi]
    exact hhi
  refine ⟨_, _, hopen, hsmooth, hmaps, htrans,
    fun p hp w => hmetric p (image_mono interior_subset hp) w, ?_⟩
  intro U G γU q hsm hMor hloc htr hW hint himm
  exact hconf s hs hsJ hact (hγι s hsab) (hTn s hs (by linarith))
    (hslab s (hJh s hsJ).1 (hJh s hsJ).2 hact hs1 hs2)
    (hband s (hJh s hsJ).1 (hJh s hsJ).2 hact hs1' hs2) (hT6 s hs (by linarith))
    U G γU q hsm hMor hloc htr hW hint himm

/-- consumer：`hpkt_of_leaves_WA2` 逐字填 O-W-IMS06 G3 `ht_left_at_event_IM6`，得到 ASSEMBLY 的
`hleftE`。 -/
example {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (M : PrescribedCuspMeridianTop_CPQ cores) :=
  fun h6E => ht_left_at_event_IM6 M (hpkt_of_leaves_WA2 H hdec M h6E)

end GC.LongTime.CuspP1
