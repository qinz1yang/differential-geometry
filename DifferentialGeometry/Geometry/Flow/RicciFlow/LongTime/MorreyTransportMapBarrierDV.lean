import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.TransportMapBarrierDV
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaFlowAT

/-!
# G5'（S-A10-DERIV，Route W）：`morreyAreaS` 的 C¹ barrier（A.5 window 形状）

`TransportMapBarrierDV` 的类无关核心在 Route W 的**光滑竞争者类**
`{v | DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ v ∧ range v ⊆ W}`
（S-A08-ATTAIN 的 `morreyAreaS`，`morreyAreaS_le`）下的特例。与 G4prime 不同，这里 transported
盘 `ι s ∘ Φ s ∘ u` 的三个类条款被**证明**而非假设：

* 光滑到边界：`SmoothDiskExtension.comp` 两次 + `SmoothDiskExtension.smoothUpToBoundary`；
* weak Jordan trace：`σ` 不变，`ι s (Φ s (γ₀ θ)) = γ s hs θ`（A.5 的 γ 字段）；
* `range ⊆ W s`：A.5 的 `MapsTo (ι s ∘ Φ s) W₀ (W s)` 与 `range u ⊆ W₀`。

没有新 def / structure / 具名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology ContDiff Bundle Manifold

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- transported 盘属于 Route W 的光滑竞争者类（一个时刻 `s`）。 -/
theorem transported_mem_smoothClass_DV
    {N Q : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    (ι : N → Q) (hι : ContMDiff (𝓡 3) (𝓡 3) ∞ ι) (Φ : N ≃ₘ⟮𝓡 3, 𝓡 3⟯ N)
    {u : C(closedDisk, N)} {U : ℂ → N}
    (hu : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    {γ₀ : freeLoop N} (hu0 : DiskWeakJordanTrace γ₀ u) {γ₁ : freeLoop Q}
    (hγ : ∀ θ, ι (Φ (γ₀ θ)) = γ₁ θ) {W₀ : Set N} {W₁ : Set Q} (hrange : Set.range u ⊆ W₀)
    (hmaps : MapsTo (fun p => ι (Φ p)) W₀ W₁) (v : C(closedDisk, Q))
    (hv : ∀ z, v z = ι (Φ (u z))) :
    DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧ DiskWeakJordanTrace γ₁ v ∧
      Set.range v ⊆ W₁ := by
  refine ⟨?_, ?_, ?_⟩
  · have hΦu := hu.comp (⟨Φ, Φ.contMDiff.continuous⟩ : C(N, N)) Φ.contMDiff
    have hιΦu := hΦu.comp (⟨ι, hι.continuous⟩ : C(N, Q)) hι
    have hveq : v = (⟨ι, hι.continuous⟩ : C(N, Q)).comp
        ((⟨Φ, Φ.contMDiff.continuous⟩ : C(N, N)).comp u) := by
      ext z
      exact hv z
    rw [hveq]
    exact hιΦu.smoothUpToBoundary
  · obtain ⟨σ, hσ, htr⟩ := hu0
    refine ⟨σ, hσ, ?_⟩
    ext θ
    have h1 : u (diskBoundary θ) = γ₀ (σ θ) := congrArg (fun f : freeLoop N => f θ) htr
    change v (diskBoundary θ) = γ₁ (σ θ)
    rw [hv, h1, hγ]
  · rintro _ ⟨z, rfl⟩
    rw [hv z]
    exact hmaps (hrange ⟨z, rfl⟩)

/-- G5' 主定理（Route W，A.5 window 形状）：`A = morreyAreaS O W T γ` 在 `t₀` 的 C¹ barrier。
`u` 是 `N = M t₀` 上 `G t₀`-conformal harmonic 的光滑盘，`γ₀` 是它的弱 Jordan trace 曲线
（`hu0`），`W₀` 是 `range u` 所在的区域，A.5 的 `γ` 字段与 `MapsTo` 字段原样作为 `hγι`、`hmaps`。 -/
theorem exists_C1_barrier_morreyAreaS_of_transport_map_DV
    (O : ObservationTower P g) (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) {t₀ : ℝ}
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [CompactSpace N] [T2Space N]
    (ι : (t : ℝ) → N → (postStage O t).Carrier) {I : Set ℝ} (hI : I ∈ 𝓝 t₀)
    (hιsm : ∀ t ∈ I, ContMDiff (𝓡 3) (𝓡 3) ∞ (ι t))
    {G : ℝ → SmoothRiemannianMetric (𝓡 3) N}
    (hGι : ∀ t ∈ I, ∀ (p : N) (v w : TangentSpace (𝓡 3) p), (G t).inner p v w =
      (postMetric O t).inner (ι t p) (mfderiv (𝓡 3) (𝓡 3) (ι t) p v)
        (mfderiv (𝓡 3) (𝓡 3) (ι t) p w))
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G) (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → N ≃ₘ⟮𝓡 3, 𝓡 3⟯ N} {Tn : Set ℝ} (hTn : IsOpen Tn) (hTn₀ : t₀ ∈ Tn)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × N => Φ p.1 p.2) (Tn ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl (𝓡 3) N ∞)
    {u : C(closedDisk, N)} {U : ℂ → N}
    (hu : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (G t₀) U z = 0)
    {γ₀ : freeLoop N} (hu0 : DiskWeakJordanTrace γ₀ u) {W₀ : Set N} (hrange : Set.range u ⊆ W₀)
    (hγι : ∀ s ∈ I, ∀ (hs : T ≤ s) θ, ι s (Φ s (γ₀ θ)) = γ s hs θ)
    (hmaps : ∀ s ∈ I, T ≤ s → MapsTo (fun p => ι s (Φ s p)) W₀ (W s))
    (hmin : morreyAreaS O W T γ t₀ = riemannianDiskArea (G t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∃ (V : Set ℝ) (F : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt F d t₀ ∧
      F t₀ = morreyAreaS O W T γ t₀ ∧
      (∀ s ∈ V ∩ Set.Ici T, morreyAreaS O W T γ s ≤ F s) ∧ d < b := by
  refine exists_C1_barrier_of_transport_map_DV O (A := morreyAreaS O W T γ) (S := Set.Ici T)
    (Cls := fun s v => ∃ hs : T ≤ s, DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
      DiskWeakJordanTrace (γ s hs) v ∧ Set.range v ⊆ W s)
    ?_ ι hI hιsm hGι hG ht₀ hTn hTn₀ hΦ hΦ₀ hu hconf hharm ?_ hmin hb
  · rintro s hsS v ⟨hs, hv1, hv2, hv3⟩
    exact morreyAreaS_le O W T γ s hs hv1 hv2 hv3
  · filter_upwards [hI] with s hsI hsS v hv
    exact ⟨hsS, transported_mem_smoothClass_DV (ι s) (hιsm s hsI) (Φ s) hu hu0
      (hγι s hsI hsS) hrange (hmaps s hsI hsS) v hv⟩

end GC.LongTime
