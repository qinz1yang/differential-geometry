import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.HbarWTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.WindowDataFluxST2

/-!
# IMS04 / G5（O-W-CURV, suffix `_CV`）：`hbarW`（Top，O-W-ASSEMBLY G6 逐字）——无条件

G4 `hbarW_of_window_flux_CV` 的 `hwin` 由 S-A14-STATIC-2 G1 的 `window_data_flux_of_no_event_ST2`
（`window_data_of_no_event_ST` + `hvel`：`Φ` 在 `γ_{t₀}` 上的 `t₀`-速度 = patch track 速度）实例化。
于是 Route W 的边界/flux 叶子（`hbarW`）关闭：`∫k − f < π` 对 Top meridian 无剩余前提。
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

/-- **G5**：O-W-ASSEMBLY G6 的 `hbarW`（共形版），对每个 Top meridian 无条件成立。 -/
theorem PrescribedCuspMeridianTop_CPQ.hbarW_CV (M : PrescribedCuspMeridianTop_CPQ cores) :
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
                        (circleMap 0 1 θ))) < Real.pi :=
  M.hbarW_of_window_flux_CV fun ht₀ hreg =>
    window_data_flux_of_no_event_ST2 cores M.exterior M.model M.port M.loop M.transported
      M.prescribed ht₀ hreg

/-- consumer：G5 填进 O-W-ASSEMBLY G6 的 `false_of_top_routeW_WA6`（`hbarW` 槽位不再是前提）。 -/
example {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ) (M : PrescribedCuspMeridianTop_CPQ cores) :
    True := by
  have _h := fun hcmp hrightE hleftE => false_of_top_routeW_WA6 H M hcmp M.hbarW_CV hrightE hleftE
  trivial

end GC.LongTime.CuspP1
