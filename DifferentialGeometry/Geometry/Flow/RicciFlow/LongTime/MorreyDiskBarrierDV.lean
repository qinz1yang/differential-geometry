import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskBarrierDV
import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaAT

/-!
# G4'（S-A10-DERIV，Route W）：`morreyLeastArea` 上的 C¹ barrier 装配

`ExteriorDiskBarrierDV` 的类无关核心 `exists_C1_barrier_of_transport_DV` 在 Route W 的
competitor 类（弱 Jordan trace + `range ⊆ W s` + riemannian-Lipschitz；与
`morreyLeastArea`（S-A08-ATTAIN，`MorreyLeastAreaAT.lean`）逐字一致）下的特例。
面积函数 `A` 以显式参数给出，用 `hAeq : A s = morreyLeastArea (postMetric O s) (W s) (γ s hs)`
（`T ≤ s`）连接，所以不依赖 S-A08-ATTAIN 尚未冻结的流版本 `morreyArea`。
没有新 def / structure / 具名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology ContDiff Bundle Manifold ENNReal NNReal

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- Route W 的 G4：Morrey 类（Lipschitz + weak Jordan trace）最小面积 `A` 的 C¹ barrier。 -/
theorem exists_C1_barrier_morreyLeastArea_of_transport_DV
    (O : ObservationTower P g) (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) {A : ℝ → ℝ}
    (hAeq : ∀ (s : ℝ) (hs : T ≤ s), A s = morreyLeastArea (postMetric O s) (W s) (γ s hs))
    {t₀ : ℝ}
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [CompactSpace N] [T2Space N]
    (e : (t : ℝ) → N ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t).Carrier)
    {G : ℝ → SmoothRiemannianMetric (𝓡 3) N}
    (hGdef : ∀ t, G t = Diffeomorph.pullbackMetricCross (postMetric O t) (e t))
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G) (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → N ≃ₘ⟮𝓡 3, 𝓡 3⟯ N} {Tn : Set ℝ} (hTn : IsOpen Tn) (hTn₀ : t₀ ∈ Tn)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × N => Φ p.1 p.2) (Tn ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl (𝓡 3) N ∞)
    {u : C(closedDisk, N)} {U : ℂ → N}
    (hu : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (G t₀) U z = 0)
    (hspan : ∀ᶠ s in 𝓝 t₀, ∀ hs : T ≤ s,
      DiskWeakJordanTrace (γ s hs)
        ((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
          ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)) ∧
      Set.range
        ((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
          ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)) ⊆ W s ∧
      ∃ L : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf (postMetric O s)
        (((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
          ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)) z)
        (((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
          ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)) w) ≤
            (L : ℝ≥0∞) * edist z w)
    (hmin : A t₀ = riemannianDiskArea (G t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∃ (V : Set ℝ) (F : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt F d t₀ ∧
      F t₀ = A t₀ ∧ (∀ s ∈ V ∩ Set.Ici T, A s ≤ F s) ∧ d < b := by
  refine exists_C1_barrier_of_transport_DV O (A := A) (S := Set.Ici T)
    (Cls := fun s v => ∃ hs : T ≤ s, DiskWeakJordanTrace (γ s hs) v ∧ Set.range v ⊆ W s ∧
      ∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf (postMetric O s) (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w)
    ?_ e hGdef hG ht₀ hTn hTn₀ hΦ hΦ₀ hu hconf hharm ?_ hmin hb
  · rintro s hsS v ⟨hs, htr, hW, hL⟩
    rw [hAeq s hs]
    exact morreyLeastArea_le (postMetric O s) htr hW hL
  · filter_upwards [hspan] with s hs hsS
    exact ⟨hsS, hs hsS⟩

end GC.LongTime
