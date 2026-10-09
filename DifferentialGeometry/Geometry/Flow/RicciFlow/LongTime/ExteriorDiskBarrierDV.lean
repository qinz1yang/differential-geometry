import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskAreaTwoParameterDV
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskAreaMetricVariation
import DifferentialGeometry.Analysis.ODE.AreaUpperBarrierC1DV

/-!
# G4（S-A10-DERIV）：`exteriorDiskArea` 上的 C¹ barrier 装配

* §1（固定类型 `M`）：G2 的 `HasDerivAt` + competitor 支配 ⇒ 显式 C¹ barrier
  `∃ V F d, IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt F d t₀ ∧ F t₀ = A t₀ ∧ (∀ s ∈ V ∩ S, A s ≤ F s) ∧ d < b`
  （正是 `AreaUpperBarrierC1DV` 的 hypothesis 形状；不需要 immersion，branch points 允许）。
* §2（`postStage` 随 `t` 变）：固定紧 3 维 `N` 与微分同胚族 `e t : N ≃ₘ (postStage O t).Carrier`
  （跨 stage 的识别），`G t := (e t)^* postMetric O t`；competitor `e s ∘ Φ s ∘ u` 属
  `isExteriorSpanningDisk (W s) (γ s)` ⇒ `exteriorDiskArea O W T γ` 的 C¹ barrier。
* §3 `d < b` 的转换引理（给 S-A10-GAUSS 的不等式接口）与 consumer。

没有新 def / structure / 具名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

section Fixed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

/-- §1 固定类型的 C¹ barrier 装配（G2 + competitor 支配）。`A` 为任意实函数（例如
`exteriorDiskArea`、Route W 的 Morrey 最小面积），`hdom` 是 transported competitor 给出的支配。 -/
theorem SmoothDiskExtension.exists_C1_barrier_of_area_two_parameter_DV
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension (G t₀) U z = 0)
    {A : ℝ → ℝ} {S : Set ℝ}
    (hdom : ∀ᶠ s in 𝓝 t₀, s ∈ S → A s ≤ riemannianDiskArea (G s)
      ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(M, M)).comp u))
    (hmin : A t₀ = riemannianDiskArea (G t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∃ (V : Set ℝ) (F : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt F d t₀ ∧
      F t₀ = A t₀ ∧ (∀ s ∈ V ∩ S, A s ≤ F s) ∧ d < b := by
  have hd := (hu.hasDerivAt_area_two_parameter_DV hG ht₀ hT hT₀ hΦ hΦ₀ hconf hharm).2.2
  obtain ⟨O, hOsub, hO, hO₀⟩ := _root_.mem_nhds_iff.mp hdom
  have hcomp : (⟨Φ t₀, (Φ t₀).contMDiff.continuous⟩ : C(M, M)).comp u = u := by
    ext z
    simp [hΦ₀]
  refine ⟨O, fun t => riemannianDiskArea (G t)
    ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u), _, hO, hO₀, hd, ?_, ?_, hb⟩
  · beta_reduce
    rw [hmin, hcomp]
  · intro s hs
    exact hOsub hs.1 hs.2

end Fixed

section Cross

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- 跨流形的面积等式：`Ψ : A ≃ₘ Q`，`w` 有光滑延拓 ⇒
`Area_g (Ψ ∘ w) = Area_{Ψ^* g} (w)`（`SmoothDiskExtension.area_pullback` 的 cross 版本）。 -/
theorem SmoothDiskExtension.area_comp_pullbackMetricCross_DV
    (Ψ : A ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ Q) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {w : C(closedDisk, A)} {W : ℂ → A} (hw : SmoothDiskExtension (E := E) w W) :
    riemannianDiskArea g ((⟨Ψ, Ψ.contMDiff.continuous⟩ : C(A, Q)).comp w) =
      riemannianDiskArea (Diffeomorph.pullbackMetricCross g Ψ) w := by
  have hΨw := hw.comp (⟨Ψ, Ψ.contMDiff.continuous⟩ : C(A, Q)) Ψ.contMDiff
  rw [riemannianDiskArea_eq_of_extension g _ _ hΨw.1,
    riemannianDiskArea_eq_of_extension (Diffeomorph.pullbackMetricCross g Ψ) w W hw.1]
  refine setIntegral_congr_fun measurableSet_closedBall fun z _ => ?_
  exact (riemannianAreaDensity_pullbackMetricCross g Ψ W z).symm

end Cross

end DifferentialGeometry.Geometry

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- competitor ⇒ `exteriorDiskArea ≤` 其面积。 -/
theorem exteriorDiskArea_le_of_isExteriorSpanningDisk_DV (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) {s : ℝ} (hs : T ≤ s)
    {v : C(closedDisk, (postStage O s).Carrier)} (hv : isExteriorSpanningDisk (W s) (γ s hs) v) :
    exteriorDiskArea O W T γ s ≤ riemannianDiskArea (postMetric O s) v := by
  rw [exteriorDiskArea_eq O W T γ s hs]
  exact leastExteriorDiskArea_le _ _ _ _ hv

/-- §2a 类无关的 G4 核心：固定紧 3 维流形 `N` 与跨 stage 微分同胚族
`e t : N ≃ₘ (postStage O t).Carrier`，`G t = (e t)^* postMetric O t`（显式参数 `G` 与 `hGdef`）。
`Cls s v` 是"stage `s` 上的 competitor 类"（显式性质参数；`exteriorDiskArea` 与 Route W 的
Morrey 类都是特例），`hle`：`A s ≤` 任意 competitor 的面积；`hspan`：`e s ∘ Φ s ∘ u` 在 `t₀` 附近属
该类；`hmin`：`u` 在 `t₀` 取到 `A t₀`。若 `m - f < b`，得到 `A` 在 `t₀` 的 C¹ barrier
（`F = Ā`，`HasDerivAt F (m - f) t₀`）。 -/
theorem exists_C1_barrier_of_transport_DV
    (O : ObservationTower P g) {A : ℝ → ℝ} {S : Set ℝ}
    {Cls : (s : ℝ) → C(closedDisk, (postStage O s).Carrier) → Prop}
    (hle : ∀ s ∈ S, ∀ v : C(closedDisk, (postStage O s).Carrier), Cls s v →
      A s ≤ riemannianDiskArea (postMetric O s) v) {t₀ : ℝ}
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
    (hspan : ∀ᶠ s in 𝓝 t₀, s ∈ S → Cls s
      ((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)))
    (hmin : A t₀ = riemannianDiskArea (G t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∃ (V : Set ℝ) (F : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt F d t₀ ∧
      F t₀ = A t₀ ∧ (∀ s ∈ V ∩ S, A s ≤ F s) ∧ d < b := by
  refine hu.exists_C1_barrier_of_area_two_parameter_DV hG ht₀ hTn hTn₀ hΦ hΦ₀ hconf hharm
    (A := A) (S := S) ?_ hmin hb
  filter_upwards [hspan] with s hs hsS
  have hw : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3))
      ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u) (⇑(Φ s) ∘ U) :=
    hu.comp (⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)) (Φ s).contMDiff
  calc A s ≤ riemannianDiskArea (postMetric O s)
        ((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
          ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)) := hle s hsS _ (hs hsS)
    _ = riemannianDiskArea (G s)
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u) := by
        rw [hGdef s]
        exact SmoothDiskExtension.area_comp_pullbackMetricCross_DV (e s) (postMetric O s) hw

/-- §2b G4 主定理（`exteriorDiskArea` 版）：`Cls s v := ∃ hs : T ≤ s, isExteriorSpanningDisk
(W s) (γ s hs) v`，`S = Ici T`。结论：`exteriorDiskArea O W T γ` 在 `t₀` 的 C¹ barrier。 -/
theorem exists_C1_barrier_exteriorDiskArea_of_transport_DV
    (O : ObservationTower P g) (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) {t₀ : ℝ}
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
    (hspan : ∀ᶠ s in 𝓝 t₀, ∀ hs : T ≤ s, isExteriorSpanningDisk (W s) (γ s hs)
      ((⟨e s, (e s).contMDiff.continuous⟩ : C(N, (postStage O s).Carrier)).comp
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ : C(N, N)).comp u)))
    (hmin : exteriorDiskArea O W T γ t₀ = riemannianDiskArea (G t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∃ (V : Set ℝ) (F : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt F d t₀ ∧
      F t₀ = exteriorDiskArea O W T γ t₀ ∧
      (∀ s ∈ V ∩ Set.Ici T, exteriorDiskArea O W T γ s ≤ F s) ∧ d < b := by
  refine exists_C1_barrier_of_transport_DV O (A := exteriorDiskArea O W T γ) (S := Set.Ici T)
    (Cls := fun s v => ∃ hs : T ≤ s, isExteriorSpanningDisk (W s) (γ s hs) v) ?_ e hGdef hG ht₀
    hTn hTn₀ hΦ hΦ₀ hu hconf hharm ?_ hmin hb
  · rintro s hsS v ⟨hs, hv⟩
    exact exteriorDiskArea_le_of_isExteriorSpanningDisk_DV O W T γ hs hv
  · filter_upwards [hspan] with s hs hsS
    exact ⟨hsS, hs hsS⟩

/-- §3 `d < b` 的转换引理（接 S-A10-GAUSS 的不等式）：`d ≤ 3A/(4(t₀+c)) - 2π + β` 且 `β < D`
⇒ `d < 3A/(4(t₀+c)) - 2π + D`。 -/
theorem lt_barrier_bound_of_estimate_DV {d A t₀ c β D : ℝ}
    (hd : d ≤ 3 * A / (4 * (t₀ + c)) - 2 * Real.pi + β) (hβ : β < D) :
    d < 3 * A / (4 * (t₀ + c)) - 2 * Real.pi + D := by linarith

/-- `D = π` 的 pi-shift 形状：`β < π` ⇒ `d < 3A/(4(t₀+c)) - π`。 -/
theorem lt_pi_shift_bound_of_estimate_DV {d A t₀ c β : ℝ}
    (hd : d ≤ 3 * A / (4 * (t₀ + c)) - 2 * Real.pi + β) (hβ : β < Real.pi) :
    d < 3 * A / (4 * (t₀ + c)) - Real.pi := by linarith

/-- G4 consumer（端到端）：逐点的 `exteriorDiskArea` C¹ barrier（即 G4 主定理的结论形状，
`b = 3A/(4(t+c)) - π`）+ `ContinuousOn` ⇒ `False`（用 G3alt 的 C¹ HG14 变体与
`exteriorDiskArea_nonneg`）。 -/
theorem not_nonnegative_exteriorDiskArea_of_C1_barriers_DV (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T c : ℝ) (hT : 0 < T + c)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)
    (hcont : ContinuousOn (exteriorDiskArea O W T γ) (Set.Ici T))
    (hbar : ∀ t ∈ Set.Ici T, ∃ (V : Set ℝ) (F : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t ∈ V ∧
      HasDerivAt F d t ∧ F t = exteriorDiskArea O W T γ t ∧
      (∀ s ∈ V ∩ Set.Ici T, exteriorDiskArea O W T γ s ≤ F s) ∧
      d < 3 * exteriorDiskArea O W T γ t / (4 * (t + c)) - Real.pi) : False :=
  DifferentialGeometry.Analysis.not_nonnegative_of_C1_majorants_pi_shift_DV
    (exteriorDiskArea O W T γ) T c hT hcont
    (fun t _ => exteriorDiskArea_nonneg O W T γ t) hbar

end GC.LongTime
