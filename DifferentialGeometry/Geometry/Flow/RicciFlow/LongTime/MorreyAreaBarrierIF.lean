import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaSemicontinuityIF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskBarrierDV
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaFlowAT
import DifferentialGeometry.Analysis.ODE.AreaUpperBarrierOffCountableDV

/-!
# IMS09′ / IMS10′（Route W）：window 数据 ⇒ C¹ barrier；transport 数据 ⇒ 矛盾（O-IFACE G2）

设计见 `docs/geometrization/chapter8/design-IFACE-K-transport-20261006.md` §A.4–A.5。

* `exists_C1_barrier_of_window_IF`（IMS09′，t₀ ∉ E）：window 数据——event-free 开区间 `I ∋ t₀`、
  固定流形 `M t₀` 上的 metric family `G`（`MetricFamilySmoothOn`，`G t₀ = postMetric O t₀`）、
  ambient isotopy `Φ`（joint `C^∞`，`Φ t₀ = refl`）、以及**对每个 `t ∈ I` 存在**的 stage 识别
  `ι : M t₀ ≃ₘ M t`（`G t = ι^* g(t)`、`ι ∘ Φ t ∘ γ_{t₀} = γ_t`、`ι ∘ Φ t` 保 region）——
  加上 `t₀` 处的 conformal harmonic 光滑类盘 `u`（`A t₀ = Area u`）与导数界 `m − f < b`
  ⇒ S-A10-DERIV G3alt 形状的 C¹ barrier。与 `exists_C1_barrier_of_transport_DV` 的区别：
  这里 `ι` 只需在 `t ∈ I` 时存在（不要求对所有 `t` 的整体 diffeo 族——不同 stage 的
  carrier 之间一般没有 diffeo），证明直接调用 DERIV 的固定流形版本
  `SmoothDiskExtension.exists_C1_barrier_of_area_two_parameter_DV`。
* `false_of_morreyAreaS_transport_IF`（IMS10′ 核心）：`A = morreyAreaS`（Route W 的 A′），
  可数 event 集 `E`；HT-L（处处）+ HT-R（`E` 上）+ C¹ barrier（`E` 外）⇒ `False`。
  证明：O-IFACE G1 的 `left_comparison_of_transport_IF` / `le_mul_of_smoothTransport_IF` +
  S-A10-DERIV 的 `not_nonnegative_of_C1_majorants_off_countable_pi_shift_DV`。
* Consumer：`morreyAreaS_barrier_of_window_IF`：`A = morreyAreaS`、`b = 3A/(4(t₀+c)) − π`，
  `m − f` 的界取 S-A10-GAUSS / S-A10-BOUNDARY 的形状 `≤ 3A/(4(t₀+c)) − 2π + β`、`β < π`
  （经 `lt_pi_shift_bound_of_estimate_DV`），恰好产出 `false_of_morreyAreaS_transport_IF` 的
  `hbar` 子句。

不引入新结构 / 新 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology ContDiff Manifold

namespace GC.LongTime

universe u

section Window

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
  (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
  (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (A : ℝ → ℝ)

/-- IMS09′：window 数据（t₀ ∉ E）+ `t₀` 处的 conformal harmonic 光滑类盘 ⇒ C¹ barrier。 -/
theorem exists_C1_barrier_of_window_IF {t₀ : ℝ} (ht₀ : T ≤ t₀)
    (hA_le : ∀ (t : ℝ) (ht : T ≤ t) (v : C(closedDisk, (postStage O t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
      A t ≤ riemannianDiskArea (postMetric O t) v)
    {I : Set ℝ} (hI : IsOpen I) (ht₀I : t₀ ∈ I)
    {G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage O t₀).Carrier}
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G) (hD : D.regular ∈ 𝓝 t₀)
    (hG₀ : G t₀ = postMetric O t₀)
    {Φ : ℝ → (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t₀).Carrier}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × (postStage O t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage O t₀).Carrier ∞)
    (hι : ∀ t ∈ I, ∀ ht : T ≤ t,
      ∃ ι : (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t).Carrier,
        G t = Diffeomorph.pullbackMetricCross (postMetric O t) ι ∧
        (∀ θ, ι (Φ t (γ t₀ ht₀ θ)) = γ t ht θ) ∧
        MapsTo (fun p => ι (Φ t p)) (W t₀) (W t))
    {u : C(closedDisk, (postStage O t₀).Carrier)} {U : ℂ → (postStage O t₀).Carrier}
    (hu : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hut : DiskWeakJordanTrace (γ t₀ ht₀) u) (huW : range u ⊆ W t₀)
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (G t₀) U z = 0)
    (hmin : A t₀ = riemannianDiskArea (postMetric O t₀) u) {b : ℝ}
    (hb : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) < b) :
    ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
      B t₀ = A t₀ ∧ (∀ s ∈ V ∩ Ici T, A s ≤ B s) ∧ d < b := by
  refine hu.exists_C1_barrier_of_area_two_parameter_DV hG hD hI ht₀I hΦ hΦ₀ hconf hharm
    (A := A) (S := Ici T) ?_ (by rw [hG₀]; exact hmin) hb
  filter_upwards [hI.mem_nhds ht₀I] with s hs hsT
  obtain ⟨ι, hGι, hγι, hWι⟩ := hι s hs hsT
  have hw : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3))
      ((⟨Φ s, (Φ s).contMDiff.continuous⟩ :
        C((postStage O t₀).Carrier, (postStage O t₀).Carrier)).comp u) (⇑(Φ s) ∘ U) :=
    hu.comp _ (Φ s).contMDiff
  have hv := hw.comp (⟨ι, ι.contMDiff.continuous⟩ :
    C((postStage O t₀).Carrier, (postStage O s).Carrier)) ι.contMDiff
  have htr : DiskWeakJordanTrace (γ s hsT)
      ((⟨ι, ι.contMDiff.continuous⟩ : C((postStage O t₀).Carrier, (postStage O s).Carrier)).comp
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ :
          C((postStage O t₀).Carrier, (postStage O t₀).Carrier)).comp u)) :=
    DiskWeakJordanTrace.map_K8 (φ := fun p => ι (Φ s p)) hγι (fun _ => rfl) hut
  have hrg : range
      ((⟨ι, ι.contMDiff.continuous⟩ : C((postStage O t₀).Carrier, (postStage O s).Carrier)).comp
        ((⟨Φ s, (Φ s).contMDiff.continuous⟩ :
          C((postStage O t₀).Carrier, (postStage O t₀).Carrier)).comp u)) ⊆ W s := by
    rintro _ ⟨z, rfl⟩
    exact hWι (huW ⟨z, rfl⟩)
  calc A s ≤ riemannianDiskArea (postMetric O s) _ :=
        hA_le s hsT _ hv.smoothUpToBoundary htr hrg
    _ = riemannianDiskArea (G s) _ := by
        rw [hGι]
        exact SmoothDiskExtension.area_comp_pullbackMetricCross_DV ι (postMetric O s) hw

/-- IMS10′ 核心：`A = morreyAreaS`；HT-L（处处）+ HT-R（可数 event 集 `E` 上）+ `E` 外的
C¹ barrier（`b = 3A/(4(t+c)) − π`）⇒ `False`。 -/
theorem false_of_morreyAreaS_transport_IF (c : ℝ) (hT : 0 < T + c) (E : Set ℝ)
    (hE : E.Countable)
    (hL : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (s : ℝ) (hs : T ≤ s), t₀ - δ < s → s < t₀ →
        ∃ (v : C(closedDisk, (postStage O s).Carrier)) (K : Set (postStage O s).Carrier)
          (φ : (postStage O s).Carrier → (postStage O t₀).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ s hs) v ∧ range v ⊆ W s ∧
          riemannianDiskArea (postMetric O s) v ≤ morreyAreaS O W T γ s ∧ range v ⊆ K ∧
          IsOpen K ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K ∧ MapsTo φ (K ∩ W s) (W t₀) ∧
          (∀ θ, φ (γ s hs θ) = γ t₀ ht₀ θ) ∧
          ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric O t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric O s).inner p w w)
    (hR : ∀ t₀ ∈ E, ∀ (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (s : ℝ) (hs : T ≤ s), t₀ < s → s < t₀ + δ →
        ∃ (v : C(closedDisk, (postStage O t₀).Carrier)) (K : Set (postStage O t₀).Carrier)
          (φ : (postStage O t₀).Carrier → (postStage O s).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ t₀ ht₀) v ∧ range v ⊆ W t₀ ∧
          riemannianDiskArea (postMetric O t₀) v ≤ morreyAreaS O W T γ t₀ ∧ range v ⊆ K ∧
          IsOpen K ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K ∧ MapsTo φ (K ∩ W t₀) (W s) ∧
          (∀ θ, φ (γ t₀ ht₀ θ) = γ s hs θ) ∧
          ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric O s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric O t₀).inner p w w)
    (hbar : ∀ t ∈ Ici T \ E, ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t ∈ V ∧
      HasDerivAt B d t ∧ B t = morreyAreaS O W T γ t ∧
      (∀ s ∈ V ∩ Ici T, morreyAreaS O W T γ s ≤ B s) ∧
      d < 3 * morreyAreaS O W T γ t / (4 * (t + c)) - Real.pi) : False := by
  have hA_le : ∀ (t : ℝ) (ht : T ≤ t) (v : C(closedDisk, (postStage O t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
      morreyAreaS O W T γ t ≤ riemannianDiskArea (postMetric O t) v :=
    fun t ht _ hv hw hW => morreyAreaS_le O W T γ t ht hv hw hW
  have hleft := left_comparison_of_transport_IF O W T γ (morreyAreaS O W T γ) hA_le hL
  have hright : ∀ t ∈ Ici T ∩ E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s, t < s → s < t + δ → morreyAreaS O W T γ s ≤
        Real.exp ε * morreyAreaS O W T γ t := by
    rintro t₀ ⟨ht₀, hE₀⟩ ε hε
    obtain ⟨δ, hδ, hd⟩ := hR t₀ hE₀ ht₀ ε hε
    refine ⟨δ, hδ, fun s hlo hhi => ?_⟩
    have hs : T ≤ s := le_trans ht₀ hlo.le
    obtain ⟨v, K, φ, hvs, hv, hvW, hvA, hvK, hK, hφ, hW, hγ, hmetric⟩ := hd s hs hlo hhi
    exact le_mul_of_smoothTransport_IF O W T γ (morreyAreaS O W T γ) ht₀ hs (hA_le s hs)
      (Real.exp_pos ε) v hvs hv hvW hvA φ hK hvK hφ hW hγ hmetric
  exact DifferentialGeometry.Analysis.not_nonnegative_of_C1_majorants_off_countable_pi_shift_DV
    (morreyAreaS O W T γ) T c E hE hT (fun t _ => morreyAreaS_nonneg O W T γ t)
    hleft hright hbar

end Window

section Consumer

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
  (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
  (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)

/-- Consumer：`A = morreyAreaS`，`b = 3A/(4(t₀+c)) − π`；`m − f` 的界取 S-A10-GAUSS/BOUNDARY 的
形状（`≤ 3A/(4(t₀+c)) − 2π + β`，`β < π`）。结论恰为 `false_of_morreyAreaS_transport_IF` 的
`hbar` 子句（在 `t₀` 处）。 -/
theorem morreyAreaS_barrier_of_window_IF {t₀ : ℝ} (ht₀ : T ≤ t₀) (c β : ℝ)
    {I : Set ℝ} (hI : IsOpen I) (ht₀I : t₀ ∈ I)
    {G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage O t₀).Carrier}
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G) (hD : D.regular ∈ 𝓝 t₀)
    (hG₀ : G t₀ = postMetric O t₀)
    {Φ : ℝ → (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t₀).Carrier}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × (postStage O t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage O t₀).Carrier ∞)
    (hι : ∀ t ∈ I, ∀ ht : T ≤ t,
      ∃ ι : (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t).Carrier,
        G t = Diffeomorph.pullbackMetricCross (postMetric O t) ι ∧
        (∀ θ, ι (Φ t (γ t₀ ht₀ θ)) = γ t ht θ) ∧
        MapsTo (fun p => ι (Φ t p)) (W t₀) (W t))
    {u : C(closedDisk, (postStage O t₀).Carrier)} {U : ℂ → (postStage O t₀).Carrier}
    (hu : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hut : DiskWeakJordanTrace (γ t₀ ht₀) u) (huW : range u ⊆ W t₀)
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (G t₀) U z = 0)
    (hmin : morreyAreaS O W T γ t₀ = riemannianDiskArea (postMetric O t₀) u)
    (hest : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
      (∫ θ in -Real.pi..Real.pi,
        (G t₀).inner (U (circleMap 0 1 θ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Φ r (U (circleMap 0 1 θ))) t₀ 1)
          (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))) ≤
        3 * morreyAreaS O W T γ t₀ / (4 * (t₀ + c)) - 2 * Real.pi + β)
    (hβ : β < Real.pi) :
    ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
      B t₀ = morreyAreaS O W T γ t₀ ∧ (∀ s ∈ V ∩ Ici T, morreyAreaS O W T γ s ≤ B s) ∧
      d < 3 * morreyAreaS O W T γ t₀ / (4 * (t₀ + c)) - Real.pi :=
  exists_C1_barrier_of_window_IF O W T γ (morreyAreaS O W T γ) ht₀
    (fun t ht _ hv hw hW => morreyAreaS_le O W T γ t ht hv hw hW) hI ht₀I hG hD hG₀ hΦ hΦ₀
    hι hu hut huW hconf hharm hmin (lt_pi_shift_bound_of_estimate_DV hest hβ)

end Consumer

end GC.LongTime
