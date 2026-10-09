import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaBarrierIF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MorreyIntegralBoundHC_GB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MorreyAreaHCAT
import DifferentialGeometry.Geometry.MinimalSurface.WeakDiskTransportK8

/-!
# G6′（S-A10-DERIV，Route W）：G6 的 degree-one 版——`hbdry` 带 `φ (θ + 2π) = φ θ + 1`

与 `MorreyBarrierHbDV.lean`（G6）完全相同，唯一区别：`exists_angle_parameter` 的第 3 个输出
（degree one：`∀ θ, φ (θ + 2 * Real.pi) = φ θ + 1`）不再被丢弃——

* `IsMorreyDisk.exists_ambient_window_bound_deg_DV` 多输出这一条；
* `morreyAreaS_barrier_of_confined_morrey_HC_deg_DV` 的 `hbdry` 量化里加前提
  `(∀ θ, φ (θ + 2 * Real.pi) = φ θ + 1)`（S-A10-BOUNDARY 的 `boundary_integral_le_BD` 需要
  degree one，否则积分是 `deg · L`）。所以 `hbdry` 比 G6 弱（更容易满足），G6′ 严格强于 G6；
  consumer `morreyAreaS_barrier_of_confined_morrey_HC_of_deg_DV` 用 G6′ 重新证明 G6 的陈述。

结论仍是 `false_of_morreyAreaS_transport_IF` 的 `hbar` 子句逐字。不引入新 def / structure / 具名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  [CompactSpace N] [T2Space N]

/-- G6 的 `exists_ambient_window_bound_DV` 加上 degree one 输出 `φ (θ + 2π) = φ θ + 1`。 -/
theorem IsMorreyDisk.exists_ambient_window_bound_deg_DV
    (hdim : Module.finrank ℝ E = 3) (Ω : TopologicalSpace.Opens N)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) Ω) (Gfam : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {t c : ℝ} {γU : freeLoop Ω} {q : C(closedDisk, Ω)}
    (hsm : IsSmoothEmbeddedLoop (E := E) γU) (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : Ω in 𝓝 (q z),
      G.inner y = ((Gfam t).restrictOpen Ω).inner y)
    (hderiv : ∀ w : closedDisk, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (Gfam r).inner ((q w : Ω) : N) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (Gfam t) ((q w : Ω) : N) X Y) t)
    (hR : ∀ w : closedDisk,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) (Gfam t) ((q w : Ω) : N)) :
    ∃ (v : C(closedDisk, Ω)) (Q : ℂ → Ω) (φ : ℝ → ℝ),
      (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea G v = riemannianDiskArea G q ∧
      SmoothDiskExtension (E := E) v Q ∧ ContDiff ℝ ∞ φ ∧ Monotone φ ∧
      (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) ∧
      (Subtype.val ∘ Q) ∘ circleMap 0 1 =
        (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) ∘ φ ∧
      riemannianDiskArea (Gfam t) (fun w => ((v w : Ω) : N)) = riemannianDiskArea G q ∧
      riemannianDiskArea (Gfam t) (fun w => ((q w : Ω) : N)) = riemannianDiskArea G q ∧
      DiskWeakJordanTrace γU v ∧ (∀ w : closedDisk, ∃ w' : closedDisk, v w = q w') ∧
      SmoothDiskExtension (E := E)
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(Ω, N)).comp v) (Subtype.val ∘ Q) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        DiskMapConformalAt (Gfam t) (Subtype.val ∘ Q) z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (Gfam t) (Subtype.val ∘ Q) z = 0) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationDensity Gfam t (Subtype.val ∘ Q) z) ≤
        3 * riemannianDiskArea G q / (4 * (t + c)) - 2 * Real.pi +
          ∫ θ in -Real.pi..Real.pi, diskMapTraceBoundaryDensity (Gfam t) (Subtype.val ∘ Q)
            (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) φ θ := by
  obtain ⟨Q₀, hQ₀⟩ := hMor.exists_smooth_extension G hdim hsm
  obtain ⟨v, σ, Q, hv, harea, hCMD⟩ := hMor.exists_conformal_minimizing_disk G hdim hsm ⟨Q₀, hQ₀⟩
  obtain ⟨φ, hφ, hm, hdeg, hl⟩ := hCMD.positiveTrace.exists_angle_parameter
  have htr := hCMD.extension.angle_trace hCMD.trace hl
  obtain ⟨hQv, N₀, hN₀, hDN₀, hQsm⟩ := hCMD.extension
  have hext : SmoothDiskExtension (E := E) v Q := ⟨hQv, N₀, hN₀, hDN₀, hQsm⟩
  -- 像集与 local metric clause 对 `v`
  have hvq : ∀ w : closedDisk, ∃ w' : closedDisk, v w = q w' := by
    rcases hv with rfl | rfl
    · exact fun w => ⟨w, rfl⟩
    · exact fun w => ⟨diskReflection w, rfl⟩
  have hlocv : ∀ w : closedDisk, ∀ᶠ y : Ω in 𝓝 (v w),
      G.inner y = ((Gfam t).restrictOpen Ω).inner y := by
    intro w
    obtain ⟨w', hw'⟩ := hvq w
    rw [hw']
    exact hloc w'
  have hpt : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ a b : TangentSpace 𝓘(ℝ, E) (Q z),
      G.inner (Q z) a b = ((Gfam t).restrictOpen Ω).inner (Q z) a b := by
    intro z hz a b
    have hQz : Q z = v ⟨z, hz⟩ := hQv ⟨z, hz⟩
    have h : G.inner (Q z) = ((Gfam t).restrictOpen Ω).inner (Q z) := by
      rw [hQz]
      exact (hlocv ⟨z, hz⟩).self_of_nhds
    exact congrArg (fun A => A a b) h
  have hev : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ᶠ y : Ω in 𝓝 (Q z),
      ∀ a b : TangentSpace 𝓘(ℝ, E) y,
        G.inner y a b = ((Gfam t).restrictOpen Ω).inner y a b := by
    intro z hz
    have hQz : Q z = v ⟨z, hz⟩ := hQv ⟨z, hz⟩
    rw [hQz]
    filter_upwards [hlocv ⟨z, hz⟩] with y hy a b
    exact congrArg (fun A => A a b) hy
  let ι : C(Ω, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hextA : SmoothDiskExtension (E := E) (ι.comp v) (Subtype.val ∘ Q) :=
    hext.comp ι contMDiff_subtype_val
  have hconfA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      DiskMapConformalAt (Gfam t) (Subtype.val ∘ Q) z := by
    intro z hz
    refine (diskMapConformalAt_restrictOpen (Gfam t) Ω Q z).mp ?_
    exact (diskMapConformalAt_congr_of_metric_GB G _ (hpt z hz)).mp (hCMD.conformal z hz)
  have hharmA : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskMapTension (Gfam t) (Subtype.val ∘ Q) z = 0 := by
    intro z hz'
    have hz := Metric.ball_subset_closedBall hz'
    have hcont : ContinuousAt Q z := hQsm.continuousOn.continuousAt (hN₀.mem_nhds (hDN₀ hz))
    rw [← diskMapTension_restrictOpen (Gfam t) Ω Q z hcont,
      ← diskMapTension_congr_of_metric_eventuallyEq_GB (U := Q) (z := z) G _ (hev z hz)]
    exact hCMD.harmonic z hz
  have hnonA : ¬ ∃ c : N, ∀ z : closedDisk, (ι.comp v) z = c := by
    rintro ⟨c, hc⟩
    exact hCMD.nonconstant hsm ⟨v (diskBoundary 0), fun z => Subtype.ext ((hc z).trans (hc _).symm)⟩
  have hγA : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) :=
    contMDiff_subtype_val.comp hsm.smooth
  have hiA : ∀ s : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) s (1 : ℝ) ≠ 0 := by
    intro s
    have h := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, E)) Ω (fun s : ℝ => γU (s : loopCircle)) s
    exact fun h0 => hsm.immersed s (by
      have h1 := congrArg (fun L => L (1 : ℝ)) h
      exact h1.symm.trans h0)
  have htrA : (Subtype.val ∘ Q) ∘ circleMap 0 1 =
      (fun s : ℝ => ((γU (s : loopCircle) : Ω) : N)) ∘ φ := by
    funext θ
    exact congrArg Subtype.val (congrFun htr θ)
  have hpts : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ w' : closedDisk,
      (Subtype.val ∘ Q) z = ((q w' : Ω) : N) := by
    intro z hz
    obtain ⟨w', hw'⟩ := hvq ⟨z, hz⟩
    have hQz : Q z = v ⟨z, hz⟩ := hQv ⟨z, hz⟩
    exact ⟨w', by simp only [Function.comp_apply]; rw [hQz, hw']⟩
  have hderivA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (Gfam r).inner ((Subtype.val ∘ Q) z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (Gfam t) ((Subtype.val ∘ Q) z) X Y) t := by
    intro z hz X Y
    obtain ⟨w', hw'⟩ := hpts z hz
    rw [hw']
    exact hderiv w' X Y
  have hRA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      -3 / (2 * (t + c)) ≤ metricScalarAt (I := 𝓘(ℝ, E)) (Gfam t) ((Subtype.val ∘ Q) z) := by
    intro z hz
    obtain ⟨w', hw'⟩ := hpts z hz
    rw [hw']
    exact hR w'
  have hptv : ∀ w : closedDisk, ∀ a b : TangentSpace 𝓘(ℝ, E) (v w),
      G.inner (v w) a b = ((Gfam t).restrictOpen Ω).inner (v w) a b := by
    intro w a b
    exact congrArg (fun A => A a b) (hlocv w).self_of_nhds
  have hareaG : riemannianDiskArea ((Gfam t).restrictOpen Ω) v = riemannianDiskArea G v := by
    unfold riemannianDiskArea riemannianArea
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    have hz' : diskExtension v z = v ⟨z, hz⟩ := diskExtension_coe v ⟨z, hz⟩
    exact riemannianAreaDensity_congr_of_metric_GB (U := diskExtension v) (z := z) _ _
      (fun a b => by rw [hz']; exact (hptv ⟨z, hz⟩ a b).symm)
  have hareaA : riemannianDiskArea (Gfam t) (fun w => ((v w : Ω) : N)) =
      riemannianDiskArea G q := by
    have h := riemannianDiskArea_restrictOpen (Gfam t) Ω v
    exact h.symm.trans (hareaG.trans harea)
  have key := DifferentialGeometry.Geometry.integral_metricVariationDensity_le_scalarShift_GB
    Gfam hdim hextA hderivA hconfA hharmA hnonA hγA hiA hφ hm htrA hRA
  have hareaGq : riemannianDiskArea ((Gfam t).restrictOpen Ω) q = riemannianDiskArea G q := by
    unfold riemannianDiskArea riemannianArea
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    have hz' : diskExtension q z = q ⟨z, hz⟩ := diskExtension_coe q ⟨z, hz⟩
    exact riemannianAreaDensity_congr_of_metric_GB (U := diskExtension q) (z := z) _ _
      (fun a b => by
        rw [hz']
        exact (congrArg (fun A => A a b) (hloc ⟨z, hz⟩).self_of_nhds).symm)
  have hareaQ : riemannianDiskArea (Gfam t) (fun w => ((q w : Ω) : N)) =
      riemannianDiskArea G q :=
    (riemannianDiskArea_restrictOpen (Gfam t) Ω q).symm.trans hareaGq
  refine ⟨v, Q, φ, hv, harea, hext, hφ, hm, hdeg, htrA, hareaA, hareaQ,
    hCMD.weakJordanTrace, hvq, hextA, hconfA, hharmA, ?_⟩
  have hk : riemannianDiskArea (Gfam t) ⇑(ι.comp v) = riemannianDiskArea G q := hareaA
  rw [hk] at key
  exact key

end DifferentialGeometry.Geometry

namespace GC.LongTime

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime.CuspP1
open TopologicalSpace DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ' : ℝ → ℝ}

/-- **G6′ 主定理（degree-one 版 `hb` 端到端）.**  `t₀ ∉ E`（`T ≤ t₀`）处的 barrier 子句，逐字为
`false_of_morreyAreaS_transport_IF` 的 `hbar`（`c = H.scalarShift`）。

输入：
* `H : AnalyticSurgeryProfile F δ'`（`scalar_lower`）；
* window 数据（O-IFACE A.5 rev3，与 `morreyAreaS_barrier_of_window_IF` 的参数逐个相同）；
* `hder`：window 度量族 `Gw` 在 `t₀` 满足 `∂_t Gw = −2 Ric(Gw t₀)`（逐点，所有 `x`）；
* `_HC` 的 confined Morrey 盘（`let U δ hδ hU G` 与 `_HC` / GAUSS G4 同形；只取需要的条款
  `hγγ hsm hMor hrange hloc`）；
* `hbdry`：对每个精确光滑迹 `(v, Q, φ)`（`v = q` 或其反射，`Q` 光滑延拓，`φ` 光滑单调，
  `φ (θ + 2π) = φ θ + 1`（degree one），`Q ∘ circleMap = γU ∘ φ`），边界曲率项减 flux 项 `< π`
  （BOUNDARY G5：`∫k < D/4`、`|f| < D/4`，经 G6 的 `sub_lt_pi_of_boundary_bounds_DV`）。 -/
theorem morreyAreaS_barrier_of_confined_morrey_HC_deg_DV
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
  have hβ := hbdry v Q φ hv hext hφ hm hdeg htr
  refine morreyAreaS_barrier_of_window_IF F.observation W T γ ht₀ H.scalarShift _ hI ht₀I hG hD
    hG₀ hΦ hΦ₀ hι hextA hut huW hconfA hharmA hmin ?_ hβ
  rw [hG₀] at hbound
  rw [hAreaEq]
  linarith [hbound]

/-- Consumer：G6（`MorreyBarrierHbDV.lean`）的陈述——`hbdry` **不带** degree-one 前提——由 G6′
重新得到：此时 `hbdry` 更强，调用 G6′ 时丢弃 degree 前提即可（`fun v Q φ hv hext hφ hm _ htr`）。
结论同 G6：`false_of_morreyAreaS_transport_IF` 的 `hbar` 子句。 -/
theorem morreyAreaS_barrier_of_confined_morrey_HC_of_deg_DV
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
        Monotone φ →
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
  exact morreyAreaS_barrier_of_confined_morrey_HC_deg_DV H W T γ ht₀ ht0 hI ht₀I hG hD hG₀ hΦ hΦ₀
    hι hder a ha ρ hρ hW γU q hγγ hsm hMor hrange hloc
    (fun v Q φ hv hext hφ hm _ htr => hbdry v Q φ hv hext hφ hm htr)

end GC.LongTime
