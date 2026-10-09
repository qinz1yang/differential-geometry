import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.HbdryBlockTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.FinalAssembly

/-!
# IMS04 / G4c（O-W-CURV, suffix `_CV`）：`hbarW`（Top，ASSEMBLY G6 逐字）⇐ window-flux 数据

`hwin` = S-A14-STATIC-2 的 `window_data_flux_of_no_event_ST` 对 Top 对象 `M` 的结论形状（与
`window_data_of_no_event_ST` 同，多一条 `hvel` 合取，见 state-O-W-CURV §接口）。由 G4b
`hbdry_block_of_hvel_CV` 合成 O-W-ASSEMBLY G6 的 `hbarW`：`T := max T₁ (start + 1)`（STATIC 要
`start < t₀`），`hder` 取 `t = t₀`，image equality ⇒ `MapsTo`。STATIC-2 交付后
`M.hbarW_of_window_flux_CV (fun ht₀ hreg => window_data_flux_of_no_event_ST … ht₀ hreg)` 一行实例化。
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G4c**：window-flux 数据 `hwin` ⇒ O-W-ASSEMBLY G6 的 `hbarW`（逐字）。 -/
theorem PrescribedCuspMeridianTop_CPQ.hbarW_of_window_flux_CV
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (hwin : ∀ {t₀ : ℝ} (ht₀ : M.exterior.start < t₀), t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        (∀ t ∈ I, ∀ (x : (postStage F.observation t₀).Carrier) (A B : TangentSpace ThreeModel x),
          HasDerivAt (fun r : ℝ => (G r).inner x A B)
            (-2 * ricciTensor (I := ThreeModel) (G t) x A B) t) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ s : ℝ,
          Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀.le) s)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)) * Real.sqrt t₀ < cores.accuracy t₀) ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀.le θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
                        (circleMap 0 1 θ))) < Real.pi := by
  obtain ⟨T₁, hT₁s, hblock⟩ := M.hbdry_block_of_hvel_CV
  refine ⟨max T₁ (M.exterior.start + 1), hT₁s.trans (le_max_left _ _), ?_⟩
  intro t₀ ht₀ hT hreg
  have hlt : M.exterior.start < t₀ := by
    have := (le_max_right T₁ (M.exterior.start + 1)).trans hT
    linarith
  obtain ⟨I, D, G, Φ, hI, ht₀I, hG, hD, hG₀, hder, hΦ, hΦ₀, hvel, hι⟩ := hwin hlt hreg
  refine ⟨I, D, G, Φ, hI, ht₀I, hG, hD, hG₀, fun x X Y => hder t₀ ht₀I x X Y, hΦ, hΦ₀,
    fun t ht ht' => ?_, hblock t₀ ht₀ ((le_max_left _ _).trans hT) G Φ hG₀ hvel⟩
  obtain ⟨ι, hιG, hιγ, hιW⟩ := hι t ht ht'
  exact ⟨ι, hιG, hιγ, fun p hp => hιW ▸ mem_image_of_mem _ hp⟩

/-- consumer：`hbarW_of_window_flux_CV` 的输出逐字填进 O-W-ASSEMBLY G6 的 `false_of_top_routeW_WA6`。 -/
example {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ) (M : PrescribedCuspMeridianTop_CPQ cores)
    (hwin : ∀ {t₀ : ℝ} (ht₀ : M.exterior.start < t₀), t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        (∀ t ∈ I, ∀ (x : (postStage F.observation t₀).Carrier) (A B : TangentSpace ThreeModel x),
          HasDerivAt (fun r : ℝ => (G r).inner x A B)
            (-2 * ricciTensor (I := ThreeModel) (G t) x A B) t) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ s : ℝ,
          Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀.le) s)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)) * Real.sqrt t₀ < cores.accuracy t₀) ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀.le θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t) : True := by
  have _h := fun hcmp hrightE hleftE =>
    false_of_top_routeW_WA6 H M hcmp (M.hbarW_of_window_flux_CV hwin) hrightE hleftE
  trivial

/-- consumer（非 Top 版，G3 的 `hcurv` 实例化 BOUNDARY 的 `boundary_integral_lt_pi_BD`）。 -/
example (M : PrescribedCuspMeridian cores) :
    ∃ T : ℝ, ∀ (t : ℝ) (ht : M.exterior.start ≤ t), T ≤ t →
      ∀ (U : ℂ → (postStage F.observation t).Carrier) {s : Set ℂ}, IsOpen s →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U s → Metric.closedBall (0 : ℂ) 1 ⊆ s →
      (∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (postMetric F.observation t) U q) →
      ∀ {φ : ℝ → ℝ}, ContDiff ℝ ∞ φ → Monotone φ → φ Real.pi = φ (-Real.pi) + 1 →
      U ∘ circleMap 0 1 = loopLift (M.transported t ht) ∘ φ →
      |∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity (postMetric F.observation t) U
        (loopLift (M.transported t ht)) φ θ| < Real.pi :=
  M.boundary_integral_lt_pi_BD fun t ht hacc h12 x =>
    (M.curvature_bound_of_metric_error_CV t ht hacc h12.le x).trans (by norm_num)

end GC.LongTime.CuspP1
