import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWGlueWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ObstructionOfIncompressible_RB

/-!
# Route W 端到端组装（O-W-ASSEMBLY G1，后缀 `_WA`）

主定理 `hasAttainedExteriorAreaObstructionAfter_of_routeW_WA`：A11 风格的 `K hK δ … L j hj C`、
`H : AnalyticSurgeryProfile F δ`（`hadm := ⟨H⟩`）、`hdec`，再加 Route W 的**剩余义务**（每条一个显式
∀-前提，不打包）⇒ `hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。

证明链：ROUTEB G3′ (a)（`Injective` ⇒ obstruction Prop）∘ `by_contra` ∘
`exists_primitive_meridian_top_CPA3`（Top meridian `M`）∘ `false_of_top_routeW_WA`；
后者 = O-IFACE G2 `false_of_morreyAreaS_transport_IF`（`A = morreyAreaS`、
`E = F.observation.eventTimes`、`c = H.scalarShift`、`T` = `_HC2` 的 `T₀` 与各义务的
晚期阈值取 max），HT-L / HT-R 的 producer 是 `RouteWGlueWA` 的 glue + 下列剩余义务：

* `hcmp`（c1，无人做）：window 上的单侧一致比较 `G t₀ ≤ e^ε Φ_s^* G s`（`MetricFamilySmoothOn` 的连续性
  + `Φ` joint `C^∞` + 紧性）。
* `hwin`（b，S-A14-STATIC G6）：regular 时刻 `t₀ ∉ E` 的 window 数据（O-IFACE §A.5，`MapsTo` 加强为
  image equality）。
* `hbar`（b，S-A10-DERIV G6 ← `hwin` + S-A10-BOUNDARY G5 的 `hbdry` + S-A10-GAUSS G4）：`t₀ ∉ E` 的
  C¹ barrier，`A′(t) := morreyLeastAreaS (g t) (W t) (γ t)`（与 `T` 无关的写法）。
* `hrightE`（c2，无人做）：event 时刻 `t₀ ∈ E` 之后（post-surgery stage）的全局 transport + `e^ε` 比较。
* `hleftE`（b/c 复合：S-A14-SURGERY G2 Top 版 + G4 `hmetric` + IMS06′ 的 `q_s ⊆ K₀`）：event 时刻的
  HT-L（O-IFACE §A.3 形状，`A′` 写法）。

所有义务都只要求在某个晚期阈值 `T₁ ≥ M.exterior.start` 之后成立（`∃ T₁`），由 producer 自选。
依赖树与叶子表：`docs/geometrization/chapter8/REMAINING-OBLIGATIONS-RouteW-20261006.md`。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

section Top

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Route W 的核心：对一个 Top meridian `M`，剩余义务 ⇒ `False`。 -/
theorem false_of_top_routeW_WA {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (hcmp : ∀ (t₀ : ℝ)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
      (D : RealTimeInterval), MetricFamilySmoothOn D G → D.regular ∈ 𝓝 t₀ →
      ∀ (I : Set ℝ), IsOpen I → t₀ ∈ I →
      ∀ (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (postStage F.observation t₀).Carrier),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) →
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ →
      ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 t₀, ∀ (p : (postStage F.observation t₀).Carrier)
        (w : TangentSpace (𝓡 3) p),
          (G t₀).inner p w w ≤ Real.exp ε *
            (G s).inner (Φ s p) (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w)
              (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w))
    (hwin : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (D : RealTimeInterval)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀ θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t)
    (hbar : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
        B t₀ = morreyLeastAreaS (postMetric F.observation t₀) (M.exterior.region t₀)
          (M.transported t₀ ht₀) ∧
        (∀ s ∈ V, ∀ hs : M.exterior.start ≤ s, T₁ ≤ s →
          morreyLeastAreaS (postMetric F.observation s) (M.exterior.region s)
            (M.transported s hs) ≤ B s) ∧
        d < 3 * morreyLeastAreaS (postMetric F.observation t₀) (M.exterior.region t₀)
          (M.transported t₀ ht₀) / (4 * (t₀ + H.scalarShift)) - Real.pi)
    (hrightE : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s),
        t₀ < s → s < t₀ + η →
        ∃ φ : (postStage F.observation t₀).Carrier → (postStage F.observation s).Carrier,
          ContMDiff (𝓡 3) (𝓡 3) ∞ φ ∧ MapsTo φ (M.exterior.region t₀) (M.exterior.region s) ∧
          (∀ θ, φ (M.transported t₀ ht₀ θ) = M.transported s hs θ) ∧
          ∀ (p : (postStage F.observation t₀).Carrier) (w : TangentSpace (𝓡 3) p),
            (postMetric F.observation s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric F.observation t₀).inner p w w)
    (hleftE : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
              Real.exp ε * (postMetric F.observation s).inner p w w) :
    False := by
  obtain ⟨T₀, h₀, -, h1, hmin⟩ := exists_smooth_minimizer_HC2_WA M 0
  obtain ⟨T₁, -, hW⟩ := hwin
  obtain ⟨T₂, -, hB⟩ := hbar
  obtain ⟨T₃, -, hRt⟩ := hrightE
  obtain ⟨T₄, -, hLt⟩ := hleftE
  set T : ℝ := max (max T₀ T₁) (max (max T₂ T₃) T₄) with hTdef
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hT₁ : T₁ ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hT₂ : T₂ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hT₃ : T₃ ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hT₄ : T₄ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hTs : M.exterior.start ≤ T := h₀.trans hT₀
  let γ : (t : ℝ) → T ≤ t → freeLoop (postStage F.observation t).Carrier :=
    fun t ht => M.transported t (hTs.trans ht)
  have hA : ∀ (t : ℝ) (ht : T ≤ t), morreyAreaS F.observation M.exterior.region T γ t =
      morreyLeastAreaS (postMetric F.observation t) (M.exterior.region t)
        (M.transported t (hTs.trans ht)) :=
    fun t ht => morreyAreaS_eq F.observation M.exterior.region T γ t ht
  have hmin' : ∀ (s : ℝ) (hs : T ≤ s), ∃ v : C(closedDisk, (postStage F.observation s).Carrier),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
      DiskWeakJordanTrace (γ s hs) v ∧ range v ⊆ M.exterior.region s ∧
      riemannianDiskArea (postMetric F.observation s) v ≤
        morreyAreaS F.observation M.exterior.region T γ s := by
    intro s hs
    obtain ⟨v, hvs, hvt, hvW, hvA⟩ := hmin T hT₀ s hs
    exact ⟨v, hvs, hvt, hvW, hvA.le⟩
  have hc : 0 < T + H.scalarShift := by linarith [H.scalarShift_pos, h1.trans hT₀]
  refine false_of_morreyAreaS_transport_IF F.observation M.exterior.region T γ H.scalarShift hc
    F.observation.eventTimes (countable_eventTimes_WA F.observation) ?_ ?_ ?_
  · intro t₀ ht₀ ε hε
    by_cases hE : t₀ ∈ F.observation.eventTimes
    · obtain ⟨η, hη, hd⟩ := hLt t₀ (hTs.trans ht₀) (hT₄.trans ht₀) hE ε hε
      refine ⟨η, hη, fun s hs hlo hhi => ?_⟩
      obtain ⟨v, K₀, φ, hvs, hvt, hvW, hvA, hvK, hK, hφ, hφW, hγφ, hmet⟩ :=
        hd s (hTs.trans hs) (hT₄.trans hs) hlo hhi
      exact ⟨v, K₀, φ, hvs, hvt, hvW, (hA s hs).symm ▸ hvA, hvK, hK, hφ, hφW, hγφ, hmet⟩
    · obtain ⟨I, G, D, Φ, hI, ht₀I, hG, hD, hG₀, hΦ, hΦ₀, hι⟩ :=
        hW t₀ (hTs.trans ht₀) (hT₁.trans ht₀) hE
      exact ht_left_of_window_WA F.observation M.exterior.region T γ ht₀ hmin' hI ht₀I hG₀
        (fun t ht ht' => hι t ht (hTs.trans ht'))
        (hcmp t₀ G D hG hD I hI ht₀I Φ hΦ hΦ₀) ε hε
  · intro t₀ hE ht₀ ε hε
    exact ht_right_of_transport_WA F.observation M.exterior.region T γ ht₀ (hmin' t₀ ht₀)
      (fun ε hε => by
        obtain ⟨η, hη, hd⟩ := hRt t₀ (hTs.trans ht₀) (hT₃.trans ht₀) hE ε hε
        exact ⟨η, hη, fun s hs hlo hhi => hd s (hTs.trans hs) hlo hhi⟩) ε hε
  · rintro t ⟨ht, hE⟩
    obtain ⟨V, B, d, hV, htV, hBd, hBt, hle, hd⟩ := hB t (hTs.trans ht) (hT₂.trans ht) hE
    refine ⟨V, B, d, hV, htV, hBd, by rw [hA t ht]; exact hBt, ?_, by rw [hA t ht]; exact hd⟩
    rintro s ⟨hsV, hs⟩
    rw [hA s hs]
    exact hle s hsV (hTs.trans hs) (hT₂.trans hs)

end Top

section Main

/-- **Route W 主组装定理**：A11 风格前提 + `H` + 剩余义务（显式 ∀-前提，量词在 Top meridian 上）⇒
`hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_WA
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hcmp : ∀ (t₀ : ℝ)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
      (D : RealTimeInterval), MetricFamilySmoothOn D G → D.regular ∈ 𝓝 t₀ →
      ∀ (I : Set ℝ), IsOpen I → t₀ ∈ I →
      ∀ (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (postStage F.observation t₀).Carrier),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) →
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ →
      ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 t₀, ∀ (p : (postStage F.observation t₀).Carrier)
        (w : TangentSpace (𝓡 3) p),
          (G t₀).inner p w w ≤ Real.exp ε *
            (G s).inner (Φ s p) (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w)
              (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w))
    (hwin : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (D : RealTimeInterval)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀ θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t)
    (hbar : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
        B t₀ = morreyLeastAreaS (postMetric F.observation t₀) (M.exterior.region t₀)
          (M.transported t₀ ht₀) ∧
        (∀ s ∈ V, ∀ hs : M.exterior.start ≤ s, T₁ ≤ s →
          morreyLeastAreaS (postMetric F.observation s) (M.exterior.region s)
            (M.transported s hs) ≤ B s) ∧
        d < 3 * morreyLeastAreaS (postMetric F.observation t₀) (M.exterior.region t₀)
          (M.transported t₀ ht₀) / (4 * (t₀ + H.scalarShift)) - Real.pi)
    (hrightE : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s),
        t₀ < s → s < t₀ + η →
        ∃ φ : (postStage F.observation t₀).Carrier → (postStage F.observation s).Carrier,
          ContMDiff (𝓡 3) (𝓡 3) ∞ φ ∧ MapsTo φ (M.exterior.region t₀) (M.exterior.region s) ∧
          (∀ θ, φ (M.transported t₀ ht₀ θ) = M.transported s hs θ) ∧
          ∀ (p : (postStage F.observation t₀).Carrier) (w : TangentSpace (𝓡 3) p),
            (postMetric F.observation s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric F.observation t₀).inner p w w)
    (hleftE : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
              Real.exp ε * (postMetric F.observation s).inner p w w) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_injective_RB F (L.decomposition j C) fun s x => by
    by_contra hcomp
    obtain ⟨M⟩ := exists_primitive_meridian_top_CPA3 K hK δ ⟨H⟩ hdec L j hj C s x hcomp
    exact false_of_top_routeW_WA H M hcmp (hwin M) (hbar M) (hrightE M) (hleftE M)

/-- consumer：Route W 组装定理供给 `LateDecomposition.hasLateSequenceTests_of_thick_thin_and_obstruction`
证明体里 `hasExteriorAreaObstructionAfter_of_producers` 那一格的 Prop（`.toObstruction`），即端点 re-point 时
替换 A08/A10/A11/A14 producer 的位置。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_WA
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hcmp : ∀ (t₀ : ℝ)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
      (D : RealTimeInterval), MetricFamilySmoothOn D G → D.regular ∈ 𝓝 t₀ →
      ∀ (I : Set ℝ), IsOpen I → t₀ ∈ I →
      ∀ (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (postStage F.observation t₀).Carrier),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) →
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ →
      ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 t₀, ∀ (p : (postStage F.observation t₀).Carrier)
        (w : TangentSpace (𝓡 3) p),
          (G t₀).inner p w w ≤ Real.exp ε *
            (G s).inner (Φ s p) (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w)
              (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w))
    (hwin : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (D : RealTimeInterval)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀ θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t)
    (hbar : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
        B t₀ = morreyLeastAreaS (postMetric F.observation t₀) (M.exterior.region t₀)
          (M.transported t₀ ht₀) ∧
        (∀ s ∈ V, ∀ hs : M.exterior.start ≤ s, T₁ ≤ s →
          morreyLeastAreaS (postMetric F.observation s) (M.exterior.region s)
            (M.transported s hs) ≤ B s) ∧
        d < 3 * morreyLeastAreaS (postMetric F.observation t₀) (M.exterior.region t₀)
          (M.transported t₀ ht₀) / (4 * (t₀ + H.scalarShift)) - Real.pi)
    (hrightE : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s),
        t₀ < s → s < t₀ + η →
        ∃ φ : (postStage F.observation t₀).Carrier → (postStage F.observation s).Carrier,
          ContMDiff (𝓡 3) (𝓡 3) ∞ φ ∧ MapsTo φ (M.exterior.region t₀) (M.exterior.region s) ∧
          (∀ θ, φ (M.transported t₀ ht₀ θ) = M.transported s hs θ) ∧
          ∀ (p : (postStage F.observation t₀).Carrier) (w : TangentSpace (𝓡 3) p),
            (postMetric F.observation s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric F.observation t₀).inner p w w)
    (hleftE : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
              Real.exp ε * (postMetric F.observation s).inner p w w) :
    hasExteriorAreaObstructionAfter F (L.decomposition j C) :=
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_WA K hK δ H hdec L j hj C hcmp hwin hbar
    hrightE hleftE).toObstruction

end Main

end GC.LongTime.CuspP1
