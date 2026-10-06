import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyBarrierHbConfDV

/-!
# Route W 端到端组装（O-W-ASSEMBLY G6，后缀 `_WA6`）

相对 G4：`hbarW` 的边界前提 `hbdry` 多给一个闭盘共形前提（S-A10-DERIV G6″），即 BOUNDARY
`boundary_integral_le_TBD` 要的 `hconf`；义务因此更弱。其余同 G4（`hcmp`、`hrightE` 已消，`hleftE` 经 IMS06
`ht_left_at_event_IM6` 换成 `hpkt`）。剩余显式义务：`hbarW`（共形版）、`hpkt`。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

section Top

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Route W 核心（G6）：对一个 Top meridian `M`，四条剩余义务 ⇒ `False`。 -/
theorem false_of_top_routeW_WA6 {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
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
    (hbarW : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D Gw ∧ D.regular ∈ 𝓝 t₀ ∧
        Gw t₀ = postMetric F.observation t₀ ∧
        (∀ (x : (postStage F.observation t₀).Carrier) (X Y : EuclideanSpace ℝ (Fin 3)),
          HasDerivAt (fun r : ℝ => (Gw r).inner x X Y)
            (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀) x X Y) t₀) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            Gw t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀ θ)) = M.transported t ht θ) ∧
            MapsTo (fun p => ι (Φ t p)) (M.exterior.region t₀) (M.exterior.region t)) ∧
        ∀ (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t₀).Carrier → ℝ)
          (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ), M.exterior.region t₀ = {x | ρ x ≤ 0} →
          let U : Opens (postStage F.observation t₀).Carrier :=
            ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
          let δ : (postStage F.observation t₀).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
          let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
            (cutoff_smooth_P2A a).contMDiff.comp hρ
          let hU : ∀ x : (postStage F.observation t₀).Carrier, x ∈ U ↔ 0 < δ x :=
            fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
          let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t₀) hδ U hU
          let ι : C(U, (postStage F.observation t₀).Carrier) :=
            ⟨Subtype.val, continuous_subtype_val⟩
          ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
            ι.comp γU = M.transported t₀ ht₀ →
            IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
            IsMorreyDisk G γU q →
            range (ι.comp q) ⊆ M.exterior.region t₀ →
            DiskWeakJordanTrace (M.transported t₀ ht₀) (ι.comp q) →
            (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t₀).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t₀).Carrier)) =
                  ρ (y : (postStage F.observation t₀).Carrier)) →
            ∀ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
              (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) →
              SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q → ContDiff ℝ ∞ φ →
              Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
              (Subtype.val ∘ Q) ∘ circleMap 0 1 =
                (fun s : ℝ =>
                  ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier)) ∘ φ →
              (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
                DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z) →
              (∫ θ in -Real.pi..Real.pi,
                  diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
                    (fun s : ℝ =>
                      ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier))
                    φ θ) -
                (∫ θ in -Real.pi..Real.pi,
                  (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
                    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                      (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
                    (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                      Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                        (circleMap 0 1 θ))) < Real.pi)
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
  obtain ⟨a, ha, T₀', h₀', -, -, hHC⟩ := M.exists_eventual_confined_morrey_disk_HC2 0
  obtain ⟨T₂, -, hB⟩ := hbarW
  obtain ⟨T₃, -, hRt⟩ := hrightE
  obtain ⟨T₄, -, hLt⟩ := hleftE
  set T : ℝ := max (max T₀ T₀') (max (max T₂ T₃) (max T₄ (M.exterior.start + 1))) with hTdef
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hT₀' : T₀' ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hT₂ : T₂ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hT₃ : T₃ ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hT₄ : T₄ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hT₅ : M.exterior.start + 1 ≤ T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
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
  have hT1 : 1 ≤ T := h1.trans hT₀
  have hc : 0 < T + H.scalarShift := by linarith [H.scalarShift_pos]
  refine false_of_morreyAreaS_transport_IF F.observation M.exterior.region T γ H.scalarShift hc
    F.observation.eventTimes (countable_eventTimes_WA F.observation) ?_ ?_ ?_
  · intro t₀ ht₀ ε hε
    by_cases hE : t₀ ∈ F.observation.eventTimes
    · obtain ⟨η, hη, hd⟩ := hLt t₀ (hTs.trans ht₀) (hT₄.trans ht₀) hE ε hε
      refine ⟨η, hη, fun s hs hlo hhi => ?_⟩
      obtain ⟨v, K₀, φ, hvs, hvt, hvW, hvA, hvK, hK, hφ, hφW, hγφ, hmet⟩ :=
        hd s (hTs.trans hs) (hT₄.trans hs) hlo hhi
      exact ⟨v, K₀, φ, hvs, hvt, hvW, (hA s hs).symm ▸ hvA, hvK, hK, hφ, hφW, hγφ, hmet⟩
    · have hlt : M.exterior.start < t₀ := (lt_add_one _).trans_le (hT₅.trans ht₀)
      obtain ⟨I, D, G, Φ, hI, ht₀I, hG, hD, hG₀, -, hΦ, hΦ₀, hι⟩ :=
        window_data_of_no_event_ST cores M.exterior M.model M.port M.loop M.transported
          M.prescribed hlt hE
      exact ht_left_of_window_WA F.observation M.exterior.region T γ ht₀ hmin' hI ht₀I hG₀
        (fun t ht ht' => hι t ht (hTs.trans ht'))
        (hcmp t₀ G D hG hD I hI ht₀I Φ hΦ hΦ₀) ε hε
  · intro t₀ hE ht₀ ε hε
    exact ht_right_of_transport_WA F.observation M.exterior.region T γ ht₀ (hmin' t₀ ht₀)
      (fun ε hε => by
        obtain ⟨η, hη, hd⟩ := hRt t₀ (hTs.trans ht₀) (hT₃.trans ht₀) hE ε hε
        exact ⟨η, hη, fun s hs hlo hhi => hd s (hTs.trans hs) hlo hhi⟩) ε hε
  · rintro t ⟨ht, hE⟩
    obtain ⟨I, D, Gw, Φ, hI, htI, hG, hD, hG₀, hder, hΦ, hΦ₀, hι, hbdry⟩ :=
      hB t (hTs.trans ht) (hT₂.trans ht) hE
    obtain ⟨ρ, hρ, hreg, -, -, γU, q, hγ, hsm, hMor, hrange, -, -, -, hweak, hloc⟩ :=
      hHC T hT₀' t ht
    exact morreyAreaS_barrier_of_confined_morrey_HC_conf_DV H M.exterior.region T γ ht
      (zero_le_one.trans (hT1.trans ht)) hI htI hG hD hG₀ hΦ hΦ₀
      (fun t' ht' hT' => hι t' ht' (hTs.trans hT'))
      hder a ha ρ hρ hreg γU q hγ hsm hMor hrange hloc
      (hbdry a ha ρ hρ hreg γU q hγ hsm hMor hrange hweak hloc)

end Top

/-- **Route W 主组装定理（G6）**：A11 风格前提 + `H` + `hbarW`（共形版）+ `hpkt`。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_WA6
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hbarW : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D Gw ∧ D.regular ∈ 𝓝 t₀ ∧
        Gw t₀ = postMetric F.observation t₀ ∧
        (∀ (x : (postStage F.observation t₀).Carrier) (X Y : EuclideanSpace ℝ (Fin 3)),
          HasDerivAt (fun r : ℝ => (Gw r).inner x X Y)
            (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀) x X Y) t₀) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            Gw t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀ θ)) = M.transported t ht θ) ∧
            MapsTo (fun p => ι (Φ t p)) (M.exterior.region t₀) (M.exterior.region t)) ∧
        ∀ (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t₀).Carrier → ℝ)
          (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ), M.exterior.region t₀ = {x | ρ x ≤ 0} →
          let U : Opens (postStage F.observation t₀).Carrier :=
            ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
          let δ : (postStage F.observation t₀).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
          let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
            (cutoff_smooth_P2A a).contMDiff.comp hρ
          let hU : ∀ x : (postStage F.observation t₀).Carrier, x ∈ U ↔ 0 < δ x :=
            fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
          let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t₀) hδ U hU
          let ι : C(U, (postStage F.observation t₀).Carrier) :=
            ⟨Subtype.val, continuous_subtype_val⟩
          ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
            ι.comp γU = M.transported t₀ ht₀ →
            IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
            IsMorreyDisk G γU q →
            range (ι.comp q) ⊆ M.exterior.region t₀ →
            DiskWeakJordanTrace (M.transported t₀ ht₀) (ι.comp q) →
            (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t₀).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t₀).Carrier)) =
                  ρ (y : (postStage F.observation t₀).Carrier)) →
            ∀ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
              (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) →
              SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q → ContDiff ℝ ∞ φ →
              Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
              (Subtype.val ∘ Q) ∘ circleMap 0 1 =
                (fun s : ℝ =>
                  ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier)) ∘ φ →
              (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
                DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z) →
              (∫ θ in -Real.pi..Real.pi,
                  diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
                    (fun s : ℝ =>
                      ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier))
                    φ θ) -
                (∫ θ in -Real.pi..Real.pi,
                  (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
                    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                      (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
                    (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                      Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                        (circleMap 0 1 θ))) < Real.pi)
    (hpkt : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_injective_RB F (L.decomposition j C) fun s x => by
    by_contra hcomp
    obtain ⟨M⟩ := exists_primitive_meridian_top_CPA3 K hK δ ⟨H⟩ hdec L j hj C s x hcomp
    exact false_of_top_routeW_WA6 H M (hcmp_of_window_WA F) (hbarW M) (hrightE_of_window_WA M)
      (ht_left_at_event_IM6 M (hpkt M))

/-- consumer：`.toObstruction`（`hasLateSequenceTests_of_thick_thin_and_obstruction` 的 producer 格）。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_WA6
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hbarW : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D Gw ∧ D.regular ∈ 𝓝 t₀ ∧
        Gw t₀ = postMetric F.observation t₀ ∧
        (∀ (x : (postStage F.observation t₀).Carrier) (X Y : EuclideanSpace ℝ (Fin 3)),
          HasDerivAt (fun r : ℝ => (Gw r).inner x X Y)
            (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀) x X Y) t₀) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            Gw t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀ θ)) = M.transported t ht θ) ∧
            MapsTo (fun p => ι (Φ t p)) (M.exterior.region t₀) (M.exterior.region t)) ∧
        ∀ (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t₀).Carrier → ℝ)
          (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ), M.exterior.region t₀ = {x | ρ x ≤ 0} →
          let U : Opens (postStage F.observation t₀).Carrier :=
            ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
          let δ : (postStage F.observation t₀).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
          let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
            (cutoff_smooth_P2A a).contMDiff.comp hρ
          let hU : ∀ x : (postStage F.observation t₀).Carrier, x ∈ U ↔ 0 < δ x :=
            fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
          let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t₀) hδ U hU
          let ι : C(U, (postStage F.observation t₀).Carrier) :=
            ⟨Subtype.val, continuous_subtype_val⟩
          ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
            ι.comp γU = M.transported t₀ ht₀ →
            IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
            IsMorreyDisk G γU q →
            range (ι.comp q) ⊆ M.exterior.region t₀ →
            DiskWeakJordanTrace (M.transported t₀ ht₀) (ι.comp q) →
            (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t₀).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t₀).Carrier)) =
                  ρ (y : (postStage F.observation t₀).Carrier)) →
            ∀ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
              (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) →
              SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q → ContDiff ℝ ∞ φ →
              Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
              (Subtype.val ∘ Q) ∘ circleMap 0 1 =
                (fun s : ℝ =>
                  ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier)) ∘ φ →
              (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
                DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z) →
              (∫ θ in -Real.pi..Real.pi,
                  diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
                    (fun s : ℝ =>
                      ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier))
                    φ θ) -
                (∫ θ in -Real.pi..Real.pi,
                  (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
                    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                      (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
                    (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                      Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                        (circleMap 0 1 θ))) < Real.pi)
    (hpkt : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
    hasExteriorAreaObstructionAfter F (L.decomposition j C) :=
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_WA6 K hK δ H hdec L j hj C hbarW
    hpkt).toObstruction

end GC.LongTime.CuspP1
