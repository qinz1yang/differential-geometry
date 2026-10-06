import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskBarrierDV

/-!
# G5（S-A10-DERIV）：A.5 window 形状（`ι t` 为光滑映射 + pairing 恒等式）的 C¹ barrier 装配

O-IFACE design §A.5 的 window 数据用 **光滑映射** `ι t : M t₀ → M t`（不是 `Diffeomorph`）与
`(G t).inner p v w = (g t).inner (ι t p) (dι v) (dι w)` 给出 metric family。这里：

* `SmoothDiskExtension.area_comp_of_pairing_DV`：桥接
  `Area_g((ι ∘ w)) = Area_G(w)`（逐点 density 恒等：`mfderiv_comp` + pairing 字段；不需要 `ι` 是
  diffeo，不需要 `G` 是 `ι^* g` 的某个具体构造）；
* `GC.LongTime.exists_C1_barrier_of_transport_map_DV`：`exists_C1_barrier_of_transport_DV`（G4）的
  plain-map 版本；window `I ∈ 𝓝 t₀` 内才要求 `ι t` 光滑与 pairing 恒等式。
  transported 盘用 "任意 `v` 满足 `∀ z, v z = ι s (Φ s (u z))`" 刻画（避免在语句里放连续性证明）；
* `exists_C1_barrier_exteriorDiskArea_of_transport_map_DV`：exterior 类特例；
* `A.5 example`：`hwin`（A.5 的 ∃ 数据块的逐字 Lean 形状）拆开后对齐本定理的参数。
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

section Pairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] [T2Space A] in
/-- plain-map 桥接：`ι : A → Q` 光滑，`G`、`g` 满足 pairing 恒等式
`G.inner p v w = g.inner (ι p) (dι v) (dι w)`，`w` 有光滑延拓 ⇒ `Area_g(ι ∘ w) = Area_G(w)`。 -/
theorem SmoothDiskExtension.area_comp_of_pairing_DV
    (ι : A → Q) (hι : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) A) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hGι : ∀ (p : A) (v w : TangentSpace 𝓘(ℝ, E) p), G.inner p v w =
      g.inner (ι p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι p v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι p w))
    {w : C(closedDisk, A)} {W : ℂ → A} (hw : SmoothDiskExtension (E := E) w W) :
    riemannianDiskArea g ((⟨ι, hι.continuous⟩ : C(A, Q)).comp w) = riemannianDiskArea G w := by
  have hιw := hw.comp (⟨ι, hι.continuous⟩ : C(A, Q)) hι
  rw [riemannianDiskArea_eq_of_extension g _ _ hιw.1,
    riemannianDiskArea_eq_of_extension G w W hw.1]
  refine setIntegral_congr_fun measurableSet_closedBall fun z hz => ?_
  obtain ⟨_, N, hN, hDN, hW⟩ := hw
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) W z :=
    ((hW z (hDN hz)).contMDiffAt (hN.mem_nhds (hDN hz))).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun x => ι (W x)) z =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι (W z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) W z) :=
    mfderiv_comp z (hι.contMDiffAt.mdifferentiableAt (by simp)) hdiff
  have hv (c : ℂ) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι (W z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) W z c) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun x => ι (W x)) z c := by
    rw [hd]
    rfl
  simp only [riemannianAreaDensity, tangentTwoJacobian, Function.comp_apply, hGι, hv]
  rfl

omit [FiniteDimensional ℝ E] [T2Space A] in
/-- 单个时刻的桥接：`v z = ι (Φ (u z))` 的任意 `v : C(closedDisk, Q)` 满足
`Area_g(v) = Area_G(Φ ∘ u)`。 -/
theorem SmoothDiskExtension.area_transport_map_DV
    (ι : A → Q) (hι : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) A) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hGι : ∀ (p : A) (v w : TangentSpace 𝓘(ℝ, E) p), G.inner p v w =
      g.inner (ι p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι p v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι p w))
    (Φ : A ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ A) {u : C(closedDisk, A)} {U : ℂ → A}
    (hu : SmoothDiskExtension (E := E) u U) (v : C(closedDisk, Q))
    (hv : ∀ z, v z = ι (Φ (u z))) :
    riemannianDiskArea g v =
      riemannianDiskArea G ((⟨Φ, Φ.contMDiff.continuous⟩ : C(A, A)).comp u) := by
  have hw : SmoothDiskExtension (E := E) ((⟨Φ, Φ.contMDiff.continuous⟩ : C(A, A)).comp u)
      (⇑Φ ∘ U) := hu.comp (⟨Φ, Φ.contMDiff.continuous⟩ : C(A, A)) Φ.contMDiff
  have hveq : v = (⟨ι, hι.continuous⟩ : C(A, Q)).comp
      ((⟨Φ, Φ.contMDiff.continuous⟩ : C(A, A)).comp u) := by
    ext z
    exact hv z
  rw [hveq]
  exact SmoothDiskExtension.area_comp_of_pairing_DV ι hι G g hGι hw

end Pairing

end DifferentialGeometry.Geometry

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- G5 核心（A.5 window 形状，类无关）：`ι t : N → (postStage O t).Carrier` 为光滑映射，
`I ∈ 𝓝 t₀` 内满足 pairing 恒等式；`hspan` 用 "任意满足 `v z = ι s (Φ s (u z))` 的 `v`" 刻画
transported 盘；其余与 G4 相同。结论：`A` 在 `t₀` 的 C¹ barrier（`F = Ā`）。 -/
theorem exists_C1_barrier_of_transport_map_DV
    (O : ObservationTower P g) {A : ℝ → ℝ} {S : Set ℝ}
    {Cls : (s : ℝ) → C(closedDisk, (postStage O s).Carrier) → Prop}
    (hle : ∀ s ∈ S, ∀ v : C(closedDisk, (postStage O s).Carrier), Cls s v →
      A s ≤ riemannianDiskArea (postMetric O s) v) {t₀ : ℝ}
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
    (hspan : ∀ᶠ s in 𝓝 t₀, s ∈ S → ∀ v : C(closedDisk, (postStage O s).Carrier),
      (∀ z, v z = ι s (Φ s (u z))) → Cls s v)
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
  filter_upwards [hspan, hI] with s hs hsI hsS
  have hcont : Continuous fun z => ι s (Φ s (u z)) :=
    (hιsm s hsI).continuous.comp ((Φ s).continuous.comp u.continuous)
  let v : C(closedDisk, (postStage O s).Carrier) := ⟨fun z => ι s (Φ s (u z)), hcont⟩
  have h1 := hle s hsS v (hs hsS v fun z => rfl)
  have h2 := SmoothDiskExtension.area_transport_map_DV (ι s) (hιsm s hsI) (G s)
    (postMetric O s) (hGι s hsI) (Φ s) hu v fun z => rfl
  rw [h2] at h1
  exact h1

/-- G5 exterior 类特例：`Cls s v := ∃ hs : T ≤ s, isExteriorSpanningDisk (W s) (γ s hs) v`。 -/
theorem exists_C1_barrier_exteriorDiskArea_of_transport_map_DV
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
    (hspan : ∀ᶠ s in 𝓝 t₀, ∀ hs : T ≤ s, ∀ v : C(closedDisk, (postStage O s).Carrier),
      (∀ z, v z = ι s (Φ s (u z))) → isExteriorSpanningDisk (W s) (γ s hs) v)
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
  refine exists_C1_barrier_of_transport_map_DV O (A := exteriorDiskArea O W T γ)
    (S := Set.Ici T) (Cls := fun s v => ∃ hs : T ≤ s, isExteriorSpanningDisk (W s) (γ s hs) v)
    ?_ ι hI hιsm hGι hG ht₀ hTn hTn₀ hΦ hΦ₀ hu hconf hharm ?_ hmin hb
  · rintro s hsS v ⟨hs, hv⟩
    exact exteriorDiskArea_le_of_isExteriorSpanningDisk_DV O W T γ hs hv
  · filter_upwards [hspan] with s hs hsS v hv
    exact ⟨hsS, hs hsS v hv⟩

/-- A.5 对齐 `example`（O-IFACE design §A.5 的 window 数据块逐字照抄）：该块拆开后恰好给出
`exists_C1_barrier_of_transport_map_DV` 里关于 window 的全部参数
（`hI`、`hιsm`、`hGι`、`hG`、`ht₀`、`hTn`、`hΦ`、`hΦ₀`）。 -/
example (O : ObservationTower P g) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (t₀ : ℝ) (ht₀ : T ≤ t₀)
    (hwin : ∃ (I : Set ℝ) (ι : (t : ℝ) → (postStage O t₀).Carrier → (postStage O t).Carrier)
      (Φ : ℝ → (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t₀).Carrier)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage O t₀).Carrier),
      IsOpen I ∧ t₀ ∈ I ∧ (∀ p, ι t₀ p = p) ∧
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage O t₀).Carrier ∞ ∧
      (∀ t ∈ I, ∀ p (v w : TangentSpace (𝓡 3) p),
        (G t).inner p v w = (postMetric O t).inner (ι t p) (mfderiv (𝓡 3) (𝓡 3) (ι t) p v)
          (mfderiv (𝓡 3) (𝓡 3) (ι t) p w)) ∧
      (∀ t ∈ I, ContMDiff (𝓡 3) (𝓡 3) ∞ (ι t)) ∧
      (∀ t ∈ I, ∀ (ht : T ≤ t) θ, ι t (Φ t (γ t₀ ht₀ θ)) = γ t ht θ) ∧
      (∀ t ∈ I, T ≤ t → MapsTo (fun p => ι t (Φ t p)) (W t₀) (W t)) ∧
      (∃ D : RealTimeInterval, MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : ℝ × (postStage O t₀).Carrier => Φ q.1 q.2) (I ×ˢ univ)) :
    ∃ (I : Set ℝ) (ι : (t : ℝ) → (postStage O t₀).Carrier → (postStage O t).Carrier)
      (Φ : ℝ → (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t₀).Carrier)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage O t₀).Carrier) (D : RealTimeInterval),
      I ∈ 𝓝 t₀ ∧ (∀ t ∈ I, ContMDiff (𝓡 3) (𝓡 3) ∞ (ι t)) ∧
      (∀ t ∈ I, ∀ p (v w : TangentSpace (𝓡 3) p),
        (G t).inner p v w = (postMetric O t).inner (ι t p) (mfderiv (𝓡 3) (𝓡 3) (ι t) p v)
          (mfderiv (𝓡 3) (𝓡 3) (ι t) p w)) ∧
      MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧ IsOpen I ∧ t₀ ∈ I ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : ℝ × (postStage O t₀).Carrier => Φ q.1 q.2) (I ×ˢ univ) ∧
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage O t₀).Carrier ∞ := by
  obtain ⟨I, ι, Φ, G, hIo, ht₀I, -, hΦ₀, hGι, hιsm, -, -, ⟨D, hG, hD⟩, hΦsm⟩ := hwin
  exact ⟨I, ι, Φ, G, D, hIo.mem_nhds ht₀I, hιsm, hGι, hG, hD, hIo, ht₀I, hΦsm, hΦ₀⟩

end GC.LongTime
