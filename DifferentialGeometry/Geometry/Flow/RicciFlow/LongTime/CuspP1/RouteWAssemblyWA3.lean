import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.WindowComparisonWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.WindowDataRightST

/-!
# Route W 端到端组装，第二次收缩（O-W-ASSEMBLY G3，后缀 `_WA3`）

相对 G2（`RouteWAssemblyWA2.lean`，保留）再消掉两条义务：
* `hcmp`（c1）：`hcmp_of_window_WA`——`eventually_comparison_of_window_WA`（`WindowComparisonWA`）取
  `J = I ∩ D.regular`（开，`𝓝[J] t₀ = 𝓝 t₀`）。
* `hrightE`（原 c2）：`hrightE_of_window_WA`——S-A14-STATIC G7 `window_data_right_of_no_event_ST`
  （event 时刻右侧 window，`J = Ico t₀ b`）+ 同一比较引理的上界方向 + `pullbackMetricCross_trans_inner_WA`，
  transport `φ = ι_s ∘ Φ_s`（`K = univ`）。

剩余显式义务 2 条：`hbarW`（DERIV G6′ 的 degree-one `hbdry` ← BOUNDARY 曲率界 + 合成）与 `hleftE`
（event 时刻 HT-L ← O-W-IMS06 + SURGERY G4）。
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

section Discharge

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **c1 消掉**：regular 时刻 window 上的单侧一致比较（G1/G2 的 `hcmp` 前提逐字）。 -/
theorem hcmp_of_window_WA (F : GC.Interface.RawSurgery P g) :
    ∀ (t₀ : ℝ)
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
              (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w) := by
  intro t₀ G D hG hD I hI ht₀I Φ hΦ hΦ₀ ε hε
  have hJ : IsOpen (I ∩ D.regular) := hI.inter D.regular_isOpen
  have ht₀J : t₀ ∈ I ∩ D.regular := ⟨ht₀I, mem_of_mem_nhds hD⟩
  have h := eventually_comparison_of_window_WA G D hG hJ.uniqueDiffOn
    (fun t ht => D.regular_subset ht.2) ht₀J (fun p => Φ p.1 p.2)
    (hΦ.mono (prod_mono inter_subset_left subset_rfl)) (fun x => by rw [hΦ₀]; rfl) hε
  rw [hJ.nhdsWithin_eq ht₀J] at h
  filter_upwards [h] with s hs p w
  exact (hs p w).1

variable {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}

/-- **原 c2 消掉**：event 时刻之后（post-surgery stage）的全局 transport + `e^ε`（G1/G2 的 `hrightE`
前提逐字，`T₁ = start + 1`）。 -/
theorem hrightE_of_window_WA (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s),
        t₀ < s → s < t₀ + η →
        ∃ φ : (postStage F.observation t₀).Carrier → (postStage F.observation s).Carrier,
          ContMDiff (𝓡 3) (𝓡 3) ∞ φ ∧ MapsTo φ (M.exterior.region t₀) (M.exterior.region s) ∧
          (∀ θ, φ (M.transported t₀ ht₀ θ) = M.transported s hs θ) ∧
          ∀ (p : (postStage F.observation t₀).Carrier) (w : TangentSpace (𝓡 3) p),
            (postMetric F.observation s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric F.observation t₀).inner p w w := by
  refine ⟨M.exterior.start + 1, by linarith, fun t₀ ht₀ hT₁ _ ε hε => ?_⟩
  have hlt : M.exterior.start < t₀ := by linarith
  obtain ⟨b₁, hb₁, hno⟩ := exists_noEvent_right_interval_ST F.observation t₀
  obtain ⟨b, D, G, Φ, htb, -, hG, hIcoD, -, hG₀, -, -, hΦ, hΦ₀, hι⟩ :=
    window_data_right_of_no_event_ST cores M.exterior M.model M.port M.loop M.transported
      M.prescribed hlt hb₁ hno
  have hev := eventually_comparison_of_window_WA G D hG (uniqueDiffOn_Ico t₀ b) hIcoD
    (left_mem_Ico.2 htb) (fun p => Φ p.1 p.2) hΦ (fun x => by rw [hΦ₀]; rfl) hε
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨min η (b - t₀), lt_min hη (by linarith), fun s hs hlo hhi => ?_⟩
  have hsI : s ∈ Ico t₀ b := ⟨hlo.le, by linarith [min_le_right η (b - t₀)]⟩
  have hsB : s ∈ Metric.ball t₀ η := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left η (b - t₀)]
  have hcs := hball ⟨hsB, hsI⟩
  obtain ⟨ι, hGι, hγι, hWι⟩ := hι s hsI hs
  refine ⟨(Φ s).trans ι, ((Φ s).trans ι).contMDiff, ?_, fun θ => hγι θ, ?_⟩
  · intro p hp
    rw [← hWι]
    exact ⟨p, hp, rfl⟩
  · intro p w
    have key : (Diffeomorph.pullbackMetricCross (postMetric F.observation s) ι).inner (Φ s p)
        (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w) (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w) ≤
          Real.exp ε * (postMetric F.observation t₀).inner p w w := by
      have h2 := (hcs p w).2
      rw [hGι, hG₀] at h2
      exact h2
    rw [← pullbackMetricCross_trans_inner_WA, Diffeomorph.pullbackMetricCross_inner] at key
    exact key

end Discharge

section Main

/-- **Route W 主组装定理（G3）**：A11 风格前提 + `H` + 两条剩余义务（`hbarW`、`hleftE`）
⇒ `hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_WA3
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
  hasAttainedExteriorAreaObstructionAfter_of_routeW_WA' K hK δ H hdec L j hj C
    (hcmp_of_window_WA F) hbarW (fun M => hrightE_of_window_WA M) hleftE

/-- consumer：G3 主定理供给 `hasLateSequenceTests_of_thick_thin_and_obstruction` 证明体里
`hasExteriorAreaObstructionAfter_of_producers` 那一格的 Prop（`.toObstruction`）。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_WA3
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
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_WA3 K hK δ H hdec L j hj C hbarW
    hleftE).toObstruction

end Main

end GC.LongTime.CuspP1
