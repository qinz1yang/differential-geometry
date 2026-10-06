import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyBarrierHbDegDV

/-!
# G6″（S-A10-DERIV，Route W）：G6′ 的共形版——`hbdry` 带 `Q` 的闭盘共形前提

与 `MorreyBarrierHbDegDV.lean`（G6′）完全相同，唯一区别：`hbdry` 的量化里（degree-one 之后）再加
前提 `∀ z ∈ closedBall 0 1, DiskMapConformalAt (postMetric F.observation t₀)
(Subtype.val ∘ Q) z`——S-A10-BOUNDARY 的 `boundary_integral_le_BD` / `_TBD`
要求 `hconf`，而 `exists_ambient_window_bound_deg_DV` 对**同一个** `Q` 已产出闭盘共形 `hconfA`
（关于 `Gw t₀`；经 `hG₀` 换成 `postMetric`），在内部调用时喂入。
`hbdry` 因此比 G6′ 的更弱，G6″ 严格强于 G6′；consumer `…_of_conf_DV` 用 G6″ 重新证明 G6′ 的陈述。

本文件只 import G6′ 并复用其 `exists_ambient_window_bound_deg_DV`（不重复证明），所以只有主定理与
consumer 两个声明。结论仍是 `false_of_morreyAreaS_transport_IF` 的 `hbar` 子句逐字。不引入新 def /
structure / 具名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace GC.LongTime

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime.CuspP1
open TopologicalSpace DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ' : ℝ → ℝ}

/-- **G6″ 主定理（degree-one + 共形版 `hb` 端到端）.**  `t₀ ∉ E`（`T ≤ t₀`）处的 barrier 子句，逐字为
`false_of_morreyAreaS_transport_IF` 的 `hbar`（`c = H.scalarShift`）。

输入：
* `H : AnalyticSurgeryProfile F δ'`（`scalar_lower`）；
* window 数据（O-IFACE A.5 rev3，与 `morreyAreaS_barrier_of_window_IF` 的参数逐个相同）；
* `hder`：window 度量族 `Gw` 在 `t₀` 满足 `∂_t Gw = −2 Ric(Gw t₀)`（逐点，所有 `x`）；
* `_HC` 的 confined Morrey 盘（`let U δ hδ hU G` 与 `_HC` / GAUSS G4 同形；只取需要的条款
  `hγγ hsm hMor hrange hloc`）；
* `hbdry`：对每个精确光滑迹 `(v, Q, φ)`（`v = q` 或其反射，`Q` 光滑延拓，`φ` 光滑单调，
  `φ (θ + 2π) = φ θ + 1`（degree one），`Q ∘ circleMap = γU ∘ φ`，**`Q` 闭盘共形**
  `DiskMapConformalAt (postMetric F.observation t₀) (val ∘ Q) z`），边界曲率项减 flux 项 `< π`
  （BOUNDARY G5：`∫k < D/4`、`|f| < D/4`，经 G6 的 `sub_lt_pi_of_boundary_bounds_DV`）。 -/
theorem morreyAreaS_barrier_of_confined_morrey_HC_conf_DV
    (H : AnalyticSurgeryProfile F δ')
    (W : (t : ℝ) → Set (postStage F.observation t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage F.observation t).Carrier)
    {t₀ : ℝ} (ht₀ : T ≤ t₀) (ht0 : 0 ≤ t₀)
    {I : Set ℝ} (hI : IsOpen I) (ht₀I : t₀ ∈ I)
    {Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier}
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D Gw) (hD : D.regular ∈ 𝓝 t₀)
    (hG₀ : Gw t₀ = postMetric F.observation t₀)
    {Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (postStage F.observation t₀).Carrier}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞)
    (hι : ∀ t ∈ I, ∀ ht : T ≤ t,
      ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage F.observation t).Carrier,
        Gw t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
        (∀ θ, ι (Φ t (γ t₀ ht₀ θ)) = γ t ht θ) ∧
        MapsTo (fun p => ι (Φ t p)) (W t₀) (W t))
    (hder : ∀ (x : (postStage F.observation t₀).Carrier) (X Y : EuclideanSpace ℝ (Fin 3)),
      HasDerivAt (fun r : ℝ => (Gw r).inner x X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀) x X Y) t₀)
    (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t₀).Carrier → ℝ)
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) (hW : W t₀ = {x | ρ x ≤ 0}) :
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
      ι.comp γU = γ t₀ ht₀ →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      range (ι.comp q) ⊆ W t₀ →
      (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
        G.inner y = ((postMetric F.observation t₀).restrictOpen U).inner y ∧
          barrier_P2A a (ρ (y : (postStage F.observation t₀).Carrier)) =
            ρ (y : (postStage F.observation t₀).Carrier)) →
      (∀ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
        (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) →
        SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q → ContDiff ℝ ∞ φ →
        Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
        (Subtype.val ∘ Q) ∘ circleMap 0 1 =
          (fun s : ℝ => ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier)) ∘ φ →
        (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
          DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z) →
        (∫ θ in -Real.pi..Real.pi,
            diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
              (fun s : ℝ => ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier))
              φ θ) -
          (∫ θ in -Real.pi..Real.pi,
            (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
              (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                  (circleMap 0 1 θ))) < Real.pi) →
      ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
        B t₀ = morreyAreaS F.observation W T γ t₀ ∧
        (∀ s ∈ V ∩ Ici T, morreyAreaS F.observation W T γ s ≤ B s) ∧
        d < 3 * morreyAreaS F.observation W T γ t₀ / (4 * (t₀ + H.scalarShift)) - Real.pi := by
  intro U δ hδ hU G ι γU q hγγ hsm hMor hrange hloc hbdry
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hloc' : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
      G.inner y = ((Gw t₀).restrictOpen U).inner y := by
    intro z
    rw [hG₀]
    exact (hloc z).mono fun y hy => hy.1
  have hR : ∀ w : closedDisk, -3 / (2 * (t₀ + H.scalarShift)) ≤
      metricScalarAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀)
        ((q w : U) : (postStage F.observation t₀).Carrier) := by
    intro w
    rw [hG₀]
    exact H.scalar_lower t₀ ht0 _
  have hderiv : ∀ w : closedDisk, ∀ X Y : EuclideanSpace ℝ (Fin 3),
      HasDerivAt (fun r : ℝ => (Gw r).inner ((q w : U) : (postStage F.observation t₀).Carrier) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀)
          ((q w : U) : (postStage F.observation t₀).Carrier) X Y) t₀ :=
    fun w X Y => hder _ X Y
  obtain ⟨v, Q, φ, hv, -, hext, hφ, hm, hdeg, htr, hA, hAq, hweak, hvq, hextA, hconfA, hharmA,
      hbound⟩ :=
    IsMorreyDisk.exists_ambient_window_bound_deg_DV (E := EuclideanSpace ℝ (Fin 3)) hdim U G Gw
      (t := t₀) (c := H.scalarShift) hsm hMor hloc' hderiv hR
  have hut : DiskWeakJordanTrace (γ t₀ ht₀) (ι.comp v) :=
    DiskWeakJordanTrace.map_K8 (φ := Subtype.val)
      (fun θ => congrArg (fun f : freeLoop (postStage F.observation t₀).Carrier => f θ) hγγ)
      (fun _ => rfl) hweak
  have huW : range (ι.comp v) ⊆ W t₀ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w', hw'⟩ := hvq z
    exact hrange ⟨w', by simp only [ContinuousMap.comp_apply, ι, hw']⟩
  rw [hG₀] at hA hAq
  have hmin : morreyAreaS F.observation W T γ t₀ =
      riemannianDiskArea (postMetric F.observation t₀) (ι.comp v) := by
    rw [morreyAreaS_eq_area_HC_AT F.observation W T γ t₀ ht₀ a ha ρ hρ hW γU q hγγ hsm hMor
      hrange]
    exact hAq.trans hA.symm
  have hAreaEq : morreyAreaS F.observation W T γ t₀ = riemannianDiskArea G q := by
    rw [hmin]
    exact hA
  have hconfP : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z := by
    rw [← hG₀]
    exact hconfA
  have hβ := hbdry v Q φ hv hext hφ hm hdeg htr hconfP
  refine morreyAreaS_barrier_of_window_IF F.observation W T γ ht₀ H.scalarShift _ hI ht₀I hG hD
    hG₀ hΦ hΦ₀ hι hextA hut huW hconfA hharmA hmin ?_ hβ
  rw [hG₀] at hbound
  rw [hAreaEq]
  linarith [hbound]

/-- Consumer：G6′（`MorreyBarrierHbDegDV.lean`）的陈述——`hbdry` **不带**共形前提——由 G6″
重新得到：此时 `hbdry` 更强，调用 G6″ 时丢弃共形前提即可
（`fun v Q φ hv hext hφ hm hdeg htr _ => hbdry v Q φ hv hext hφ hm hdeg htr`）。 -/
theorem morreyAreaS_barrier_of_confined_morrey_HC_of_conf_DV
    (H : AnalyticSurgeryProfile F δ')
    (W : (t : ℝ) → Set (postStage F.observation t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage F.observation t).Carrier)
    {t₀ : ℝ} (ht₀ : T ≤ t₀) (ht0 : 0 ≤ t₀)
    {I : Set ℝ} (hI : IsOpen I) (ht₀I : t₀ ∈ I)
    {Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier}
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D Gw) (hD : D.regular ∈ 𝓝 t₀)
    (hG₀ : Gw t₀ = postMetric F.observation t₀)
    {Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (postStage F.observation t₀).Carrier}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞)
    (hι : ∀ t ∈ I, ∀ ht : T ≤ t,
      ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage F.observation t).Carrier,
        Gw t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
        (∀ θ, ι (Φ t (γ t₀ ht₀ θ)) = γ t ht θ) ∧
        MapsTo (fun p => ι (Φ t p)) (W t₀) (W t))
    (hder : ∀ (x : (postStage F.observation t₀).Carrier) (X Y : EuclideanSpace ℝ (Fin 3)),
      HasDerivAt (fun r : ℝ => (Gw r).inner x X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Gw t₀) x X Y) t₀)
    (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t₀).Carrier → ℝ)
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) (hW : W t₀ = {x | ρ x ≤ 0}) :
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
      ι.comp γU = γ t₀ ht₀ →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      range (ι.comp q) ⊆ W t₀ →
      (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
        G.inner y = ((postMetric F.observation t₀).restrictOpen U).inner y ∧
          barrier_P2A a (ρ (y : (postStage F.observation t₀).Carrier)) =
            ρ (y : (postStage F.observation t₀).Carrier)) →
      (∀ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
        (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) →
        SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q → ContDiff ℝ ∞ φ →
        Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
        (Subtype.val ∘ Q) ∘ circleMap 0 1 =
          (fun s : ℝ => ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier)) ∘ φ →
        (∫ θ in -Real.pi..Real.pi,
            diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
              (fun s : ℝ => ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier))
              φ θ) -
          (∫ θ in -Real.pi..Real.pi,
            (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
              (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                  (circleMap 0 1 θ))) < Real.pi) →
      ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t₀ ∈ V ∧ HasDerivAt B d t₀ ∧
        B t₀ = morreyAreaS F.observation W T γ t₀ ∧
        (∀ s ∈ V ∩ Ici T, morreyAreaS F.observation W T γ s ≤ B s) ∧
        d < 3 * morreyAreaS F.observation W T γ t₀ / (4 * (t₀ + H.scalarShift)) - Real.pi := by
  intro U δ hδ hU G ι γU q hγγ hsm hMor hrange hloc hbdry
  exact morreyAreaS_barrier_of_confined_morrey_HC_conf_DV H W T γ ht₀ ht0 hI ht₀I hG hD hG₀ hΦ
    hΦ₀ hι hder a ha ρ hρ hW γU q hγγ hsm hMor hrange hloc
    (fun v Q φ hv hext hφ hm hdeg htr _ => hbdry v Q φ hv hext hφ hm hdeg htr)

end GC.LongTime
