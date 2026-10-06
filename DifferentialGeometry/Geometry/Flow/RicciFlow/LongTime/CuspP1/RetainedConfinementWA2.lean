import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepWindowSG2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Ims05HC2ReadyIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TransportedNonnegIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ConfinedOfIms05IM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.DiskDistScaleIM6

/-!
# surgery 时刻左侧的 confinement 总装（O-W-ASSEMBLY-2 G9，第 2 部分，后缀 `_WA2`）

event `i`（`τ₀ = time i.succ`）、record `R`、window（`Fs = i.castSucc`、`Ls = i.succ`）固定。
S-A14-SURGERY-2 G3′ `exists_window_separation_SG2` 给紧 `KD`（与 `s` 无关）与每个 `s` 的分离
`(Us, V)`；本文件把它与下列逐时刻输入串起来，得到 "每个 `_HC2` 形 Morrey 盘的像 `⊆ ι_s '' interior KD`"
（O-W-IMS06 G11 `hconfW` 的结论体）：

* **c9a**（S-W-NECK-2）：每个 retained boundary `b` 存在 `(N b, Z b)` 与尺度 `c_b > 0`：band
  `{|Z b| < 20}` 在 `c_b • g_post(s)` 下的五联数据（`N b` 开、`Z b` 为 `C¹`、band 闭包 `⊆ N b`、
  `(dZ)² ≤ 4 g′`、`R(g′) ≥ 1/2`），且切割球面 `e_s '' Σ_b ⊆ {Z b = 0}`（`e_s = sliceHomeo_SG2`）；
* **c9b**（S-W-NECK-2）：`e_s '' {0 ≤ z_s ≤ 50}` 上 `R_post ≥ 0`；
* **⑧**（O-W-HNEG）：cusp collar 上 `R_post < 0`；
* **⑥**（O-W-IMS06 G16 = S-W-STAB-2 G1/G4 逐盘 + IMS06 G9/G15）：每个 `_HC2` 形盘、每个 `σ > 0` 的
  IMS05′（S-W-NECK G4 形 `hIMS05`，`g_post(s)` 下）；
* `γ_s ⊆ range ι_s`（本车道 `exists_tpw_Top_range_WA2`）。

证明：⑥ + 缩放（IMS06 G8）⇒ `c_b • g_post` 下的 IMS05′ ⇒ S-W-NECK G4 不碰中间球面 `{Z b = 0}`；
⑧ + c9a 的 `R ≥ 1/2`（缩放保号）⇒ `γ_s` 不进 band 闭包；⑧ + c9b ⇒ `γ_s` 不碰 `e_s '' N_b` ⇒
`γ_s ⊆ Us`（R3 判据）；c5（`confined_in_survivor_of_neck_exclusion_IM6`）⇒ `range ⊆ ι_s '' interior KD`。
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

section Top

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **单个时刻 `s` 的 confinement**：R3 的 `(Us, V)` + c9a + c9b + ⑧ + ⑥ + `γ_s ⊆ range ι_s` ⇒
每个 `_HC2` 形 Morrey 盘的像 `⊆ K₀`（`Us ⊆ K₀`）。 -/
theorem range_subset_of_retained_bands_WA2 (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ}
    (hs : M.exterior.start ≤ s) {ιb : Type*}
    (e : ιb → Set (postStage F.observation s).Carrier)
    (Nb : ιb → Set (postStage F.observation s).Carrier)
    (Zb : ιb → (postStage F.observation s).Carrier → ℝ)
    {Us V K₀ ι₀ : Set (postStage F.observation s).Carrier}
    (hUs : IsOpen Us) (hV : IsOpen V) (hUV : Disjoint Us V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ Nb b ∧ Zb b x = 0)) → x ∈ Us ∪ V) (hUK : Us ⊆ K₀)
    (hcrit : ∀ x ∈ ι₀, (∀ b, x ∉ e b) → x ∈ Us)
    (hγι : ∀ θ, M.transported s hs θ ∈ ι₀)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    (hslab : ∀ b, ∀ x ∈ e b, 0 ≤ metricScalarAt (postMetric F.observation s) x)
    (hband : ∀ b, ∃ c : ℝ, ∃ hc : 0 < c,
      IsOpen (Nb b) ∧ ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) 1 (Zb b) (Nb b) ∧
      closure {p | p ∈ Nb b ∧ |Zb b p| < 20} ⊆ Nb b ∧
      (∀ p ∈ Nb b, |Zb b p| < 20 → ∀ w : TangentSpace (𝓡 3) p,
        (show ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (Zb b) p w) ^ 2 ≤
          4 * (scaleMetric c hc (postMetric F.observation s)).inner p w w) ∧
      (∀ p ∈ Nb b, |Zb b p| < 20 →
        1 / 2 ≤ metricScalarAt (scaleMetric c hc (postMetric F.observation s)) p))
    (h6 : ∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
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
  intro U G γU q hsm hMor hloc htr hW hint himm
  have hg := h6 U G γU q hsm hMor hloc htr hW hint himm
  have hv := diskSmoothInterior_comp_val_IM6 (E := EuclideanSpace ℝ (Fin 3)) hMor.smoothInterior
  refine confined_in_survivor_of_neck_exclusion_IM6 _ Nb Zb hUs hV hUV hsep hUK
    (fun θ => hcrit _ (hγι θ) fun b =>
      transported_not_mem_of_scalar_nonneg_IM6 M hs hneg e hslab θ b) htr fun b => ?_
  obtain ⟨c, hc, hN, hZ, hcl, hdz, hR⟩ := hband b
  have hS : ∀ p ∈ {p | p ∈ Nb b ∧ |Zb b p| < 20},
      0 ≤ metricScalarAt (postMetric F.observation s) p := by
    intro p hp
    have h1 := hR p hp.1 hp.2
    rw [metricScalarAt_scaleMetric] at h1
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hc)).1 (by linarith)
  exact not_mem_middle_sphere_of_stability_bound_NK (scaleMetric c hc (postMetric F.observation s))
    hv hN hZ hcl hdz hR
    (diskTrace_not_mem_of_weakTrace_IM6 htr fun θ =>
      transported_not_mem_closure_of_scalar_nonneg_IM6 M hs hneg hS θ)
    (ims05_radius_bound_scale_IM6 c hc _ hg (by norm_num))

/-- **R3 + c9 + ⑧ + ⑥ ⇒ 公共紧控制**（event `i`、record `R`、tight window `Fs = i.castSucc`、
`Ls = i.succ` 固定）：存在紧 `KD`（与 `s` 无关），使得 window 内每个 `s`（`activeStage s = i.castSucc`）
只要逐时刻输入成立（`e = sliceHomeo_SG2`），每个 `_HC2` 形 Morrey 盘的像 `⊆ ι_s '' interior KD`。 -/
theorem exists_retained_confinement_WA2 (M : PrescribedCuspMeridianTop_CPQ cores) (N : ℕ)
    (i : Fin (F.observation.history N).eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord (F.observation.history N) i p)
    (hcol : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      100 < ((R.static b).delta)⁻¹)
    (hFL : i.castSucc ≤ i.succ) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      i.castSucc ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ i.succ) :
    ∃ KD : Set ((F.observation.history N).backwardSurvivorDomain i.castSucc i.succ hFL),
      IsCompact KD ∧
      ∀ (s : ℝ) (hs : M.exterior.start ≤ s) (hsJ : s ∈ J)
        (hact : (F.observation.history N).activeStage ⟨s, (hJh s hsJ).1, (hJh s hsJ).2⟩ =
          i.castSucc),
        let e := sliceHomeo_SG2 F.observation N i s (hJh s hsJ).1 (hJh s hsJ).2 hact
        (∀ θ, M.transported s hs θ ∈
          range (windowEmbed_SG F.observation N i.castSucc i.succ hFL J hJh hst s hsJ)) →
        (∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
          riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
            (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0) →
        (∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
          ∀ x ∈ e '' neckSlab_SG2 R b (Icc 0 50),
            0 ≤ metricScalarAt (postMetric F.observation s) x) →
        (∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
          ∃ (Nb : Set (postStage F.observation s).Carrier)
            (Zb : (postStage F.observation s).Carrier → ℝ) (c : ℝ) (hc : 0 < c),
          IsOpen Nb ∧ ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) 1 Zb Nb ∧
          closure {x | x ∈ Nb ∧ |Zb x| < 20} ⊆ Nb ∧
          (∀ x ∈ Nb, |Zb x| < 20 → ∀ w : TangentSpace (𝓡 3) x,
            (show ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ) Zb x w) ^ 2 ≤
              4 * (scaleMetric c hc (postMetric F.observation s)).inner x w w) ∧
          (∀ x ∈ Nb, |Zb x| < 20 →
            1 / 2 ≤ metricScalarAt (scaleMetric c hc (postMetric F.observation s)) x) ∧
          e '' neckSlab_SG2 R b {50} ⊆ {x | x ∈ Nb ∧ Zb x = 0}) →
        (∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
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
            r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) →
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
            C(U, (postStage F.observation s).Carrier)).comp q) ⊆
            windowEmbed_SG F.observation N i.castSucc i.succ hFL J hJh hst s hsJ ''
              interior KD := by
  obtain ⟨KD, hKD, h⟩ := exists_window_separation_SG2 F.observation N i hFL J hJh hst R hcol
  refine ⟨KD, hKD, ?_⟩
  intro s hs hsJ hact e hγι hneg hslab hband h6
  obtain ⟨Us, V, hUo, hVo, hUV, hUK, hsep, hcrit⟩ := h s hsJ hact
  choose Nb Zb c hc hN hZ hcl hdz hR hcut using hband
  exact range_subset_of_retained_bands_WA2 M hs (fun b => e '' neckSlab_SG2 R b (Icc 0 50)) Nb Zb
    hUo hVo hUV (fun x hx => hsep x fun b hb => hx b (hcut b hb)) hUK hcrit hγι hneg hslab
    (fun b => ⟨c b, hc b, hN b, hZ b, hcl b, hdz b, hR b⟩) h6

end Top

end GC.LongTime.CuspP1
