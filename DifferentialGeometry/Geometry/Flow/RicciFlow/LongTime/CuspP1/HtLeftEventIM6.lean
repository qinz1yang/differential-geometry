import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.InteriorImmersionHC_KP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA

/-!
# HT-L at events：surgery 时刻 left-lsc 的 producer（O-W-IMS06 G3，后缀 `_IM6`）

O-W-ASSEMBLY G1 的 `hleftE`（`RouteWAssemblyWA.lean`，O-IFACE §A.3 HT-L 的 `A′ = morreyLeastAreaS` 写法）
逐字由下面的 `ht_left_at_event_IM6` 产出。近 minimizer 取 `_HC2` 盘 `ι ∘ q_s`
（S-K16B-PORT G_final 版 `exists_eventual_confined_morrey_disk_interior_immersion_HC_KP`）：
光滑到边界（`SmoothDiskExtension`）、弱 Jordan 迹、`⊆ region s`、面积 `= morreyLeastAreaS`
（S-A08-ATTAIN G4′ `morreyAreaS_eq_area_HC_AT` + G2′ `morreyAreaS_eq`）。剩下的是每个晚期 event 的
**left packet** `hpkt`（显式前提，未到输入的合成）：

* TPW 五字段（`IsOpen K₀`、`φ` 在 `K₀` 上 `C^∞`、`MapsTo φ (K₀ ∩ region s) (region t₀)`、送 `γ_s` 到
  `γ_{t₀}`、`φ^* g(t₀) ≤ e^ε g(s)` on `K₀`）——S-A14-SURGERY c7（已交付，`exists_surgery_transport_Top_SG`）
  + G4 `hmetric`（进行中），`K₀ = ι_s '' interior KD`（`tpw_of_window_compact_IM6`，见 R1/R2）；
* confinement 判据：每个 `_HC2` 形 Morrey 盘（下列子句）的像 `⊆ K₀`——G2
  `confined_of_ims05_HC2_IM6`（c3 + NECK G4/G5 + R3）。

`tpw_of_window_compact_IM6`：window 的开嵌入 `ι_s : D → M_s`、`φ` 在 `range ι_s` 上的性质（SG c7 输出）
+ `hmetric` 在 `ι_s '' KD` 上 ⇒ `K₀ := ι_s '' interior KD` 的 TPW 五字段。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

section Window

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ, E) ∞ Y]

/-- window ⇒ TPW 五字段（`K₀ = ι '' interior KD`）：`ι` 开嵌入，`φ` 在 `range ι` 上光滑并把
`W₀ ∩ range ι` 送进 `W₁`，度量比较 `φ^* g_Y ≤ c · g_X` 在 `ι '' KD` 上。 -/
theorem tpw_of_window_compact_IM6 {D : Type*} [TopologicalSpace D]
    (gX : SmoothRiemannianMetric 𝓘(ℝ, E) X) (gY : SmoothRiemannianMetric 𝓘(ℝ, E) Y)
    {ι : D → X} (hι : Topology.IsOpenEmbedding ι) {φ : X → Y}
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ (range ι)) {W₀ : Set X} {W₁ : Set Y}
    (hW : MapsTo φ (W₀ ∩ range ι) W₁) {KD : Set D} {c : ℝ}
    (hmet : ∀ p ∈ ι '' KD, ∀ w : TangentSpace 𝓘(ℝ, E) p,
      gY.inner (φ p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) ≤
        c * gX.inner p w w) :
    IsOpen (ι '' interior KD) ∧ ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ (ι '' interior KD) ∧
      MapsTo φ (ι '' interior KD ∩ W₀) W₁ ∧
      ∀ p ∈ ι '' interior KD, ∀ w : TangentSpace 𝓘(ℝ, E) p,
        gY.inner (φ p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) ≤
          c * gX.inner p w w :=
  ⟨hι.isOpenMap _ isOpen_interior, hφ.mono (image_subset_range _ _),
    fun _ hp => hW ⟨hp.2, image_subset_range _ _ hp.1⟩,
    fun p hp => hmet p (image_mono interior_subset hp)⟩

end Window

section Top

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **HT-L at events（G3 主定理）**：left packet `hpkt`（每个晚期 event `t₀`、`ε`：`s ↑ t₀` 时的
TPW 五字段 + "`_HC2` 形 Morrey 盘的像 `⊆ K₀`" 判据）⇒ O-W-ASSEMBLY `false_of_top_routeW_WA` 的
`hleftE`（逐字）。近 minimizer = `_HC2` 盘 `ι ∘ q_s`。 -/
theorem ht_left_at_event_IM6 (M : PrescribedCuspMeridianTop_CPQ cores)
    (hpkt : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
              C(U, (postStage F.observation s).Carrier)).comp q) ⊆ K₀) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
        t₀ - η < s → s < t₀ →
        ∃ (v : C(closedDisk, (postStage F.observation s).Carrier))
          (K₀ : Set (postStage F.observation s).Carrier)
          (φ : (postStage F.observation s).Carrier → (postStage F.observation t₀).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (M.transported s hs) v ∧ range v ⊆ M.exterior.region s ∧
          riemannianDiskArea (postMetric F.observation s) v ≤
            morreyLeastAreaS (postMetric F.observation s) (M.exterior.region s)
              (M.transported s hs) ∧
          range v ⊆ K₀ ∧ IsOpen K₀ ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K₀ ∧
          MapsTo φ (K₀ ∩ M.exterior.region s) (M.exterior.region t₀) ∧
          (∀ θ, φ (M.transported s hs θ) = M.transported t₀ ht₀ θ) ∧
          ∀ p ∈ K₀, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric F.observation t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric F.observation s).inner p w w := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP M.exterior.start
  obtain ⟨T₁, -, hP⟩ := hpkt
  refine ⟨max T₀ T₁, h₀.trans (le_max_left _ _), fun t₀ ht₀ hT hE ε hε => ?_⟩
  obtain ⟨η, hη, hd⟩ := hP t₀ ht₀ ((le_max_right _ _).trans hT) hE ε hε
  refine ⟨η, hη, fun s hs hTs hlo hhi => ?_⟩
  obtain ⟨K₀, φ, hK, hφ, hφW, hγφ, hmet, hconf⟩ :=
    hd s hs ((le_max_right _ _).trans hTs) hlo hhi
  have hT₀s : T₀ ≤ s := (le_max_left _ _).trans hTs
  obtain ⟨ρ, hρ, hreg, -, -, γU, q, hγ, hsm, hMor, hrange, hint, -, -, hweak, hloc, ⟨Q, hQ⟩,
    himm⟩ := hH T₀ le_rfl s hT₀s
  have h1 := morreyAreaS_eq_area_HC_AT F.observation M.exterior.region T₀
    (fun t ht => M.transported t (h₀.trans ht)) s hT₀s a ha ρ hρ hreg γU q hγ hsm hMor hrange
  have h2 := morreyAreaS_eq F.observation M.exterior.region T₀
    (fun t ht => M.transported t (h₀.trans ht)) s hT₀s
  refine ⟨(⟨Subtype.val, continuous_subtype_val⟩ :
      C(_, (postStage F.observation s).Carrier)).comp q, K₀, φ,
    (hQ.comp ⟨Subtype.val, continuous_subtype_val⟩ contMDiff_subtype_val).smoothUpToBoundary,
    hweak, hrange, (h1.symm.trans h2).le,
    hconf _ _ γU q hsm hMor (fun z => (hloc z).mono fun y hy => hy.1) hweak hrange hint himm,
    hK, hφ, hφW, hγφ, hmet⟩

/-- consumer：`ht_left_at_event_IM6 M hpkt` 逐字填入 O-W-ASSEMBLY `false_of_top_routeW_WA` 的
`hleftE`（无转换）；剩下 `hcmp hwin hbar hrightE ⇒ False`。 -/
example {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ) (M : PrescribedCuspMeridianTop_CPQ cores) :=
  fun hpkt => false_of_top_routeW_WA H M (hleftE := ht_left_at_event_IM6 M hpkt)

end Top

end GC.LongTime.CuspP1
