import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaBarrierIF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedMorreyHC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MorreyAreaHCAT

/-!
# Route W 组装的 glue 引理（O-W-ASSEMBLY G1，后缀 `_WA`）

`false_of_morreyAreaS_transport_IF`（O-IFACE G2）吃 HT-L（处处）、HT-R（event 集 `E` 上）、`E` 外的
C¹ barrier。本文件给出组装时需要、但没有其它车道在做的几个小零件：

* `countable_eventTimes_WA`：`E := O.eventTimes` 可数（`eventTimes_finite_Icc` 的可数并）。
* `exists_smooth_minimizer_HC2_WA`：每个 Top meridian 在晚期每个时刻都有光滑类 minimizer
  `ι ∘ q_t`（S-MIRRORS G4 的 `_HC2` Morrey 盘 + `IsMorreyDisk.exists_smooth_extension` +
  S-A08-ATTAIN G4′ 的 `morreyAreaS_eq_area_HC_AT`）。
* `ht_left_of_window_WA`：regular 时刻 `t₀ ∉ E` 的 HT-L（`K = univ`）⇐ O-IFACE §A.5 的 window 数据
  （`MapsTo` 加强成 image equality，因为左侧要用 `(ι_s ∘ Φ_s)⁻¹`）+ 单侧一致比较
  `G t₀ ≤ e^ε Φ_s^* G s`（剩余义务 c1）+ minimizer 存在。
* `ht_right_of_transport_WA`：event 时刻 `t₀ ∈ E` 的 HT-R（`K = univ`）⇐ post-surgery 侧的全局
  transport（剩余义务 c2）+ minimizer 存在。

不引入新结构 / 新 Prop；所有剩余义务在 `RouteWAssemblyWA.lean` 里以显式 ∀-前提出现。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

section Events

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- event 时刻集合可数：每个 `Icc (-k) k` 里只有有限个 event。 -/
theorem countable_eventTimes_WA (O : ObservationTower P g) : O.eventTimes.Countable := by
  have hcov : O.eventTimes ⊆ ⋃ k : ℕ, O.eventTimes ∩ Icc (-(k : ℝ)) k := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_ge |x|
    exact mem_iUnion.2 ⟨k, hx, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  exact (countable_iUnion fun k => (O.eventTimes_finite_Icc _ _).countable).mono hcov

end Events

section Minimizer

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- 晚期每个时刻都有光滑类 minimizer：`_HC2` 的 confined Morrey 盘 `ι ∘ q_t` 光滑到边界、弱 Jordan
迹、落在 region 里，且面积等于 `morreyAreaS`（S-A08-ATTAIN G4′）。 -/
theorem exists_smooth_minimizer_HC2_WA (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, tmin ≤ T₀ ∧ 1 ≤ T₀ ∧
      ∀ (T : ℝ) (hT : T₀ ≤ T) (t : ℝ) (ht : T ≤ t),
        ∃ v : C(closedDisk, (postStage F.observation t).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (M.transported t ((h₀.trans hT).trans ht)) v ∧
          range v ⊆ M.exterior.region t ∧
          riemannianDiskArea (postMetric F.observation t) v =
            morreyAreaS F.observation M.exterior.region T
              (fun s hs => M.transported s ((h₀.trans hT).trans hs)) t := by
  obtain ⟨a, ha, T₀, h₀, htmin, h1, hHC⟩ := M.exists_eventual_confined_morrey_disk_HC2 tmin
  refine ⟨T₀, h₀, htmin, h1, fun T hT t ht => ?_⟩
  obtain ⟨ρ, hρ, hreg, -, -, γU, q, hγ, hsm, hMor, hrange, -, -, -, hweak, -⟩ := hHC T hT t ht
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨Q, hQ⟩ := hMor.exists_smooth_extension _ hd hsm
  refine ⟨_,
    (hQ.comp ⟨Subtype.val, continuous_subtype_val⟩ contMDiff_subtype_val).smoothUpToBoundary,
    hweak, hrange, ?_⟩
  exact (morreyAreaS_eq_area_HC_AT F.observation M.exterior.region T
    (fun s hs => M.transported s ((h₀.trans hT).trans hs)) t ht a ha ρ hρ hreg γU q hγ hsm hMor
    hrange).symm

end Minimizer

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ, E) ∞ Y]

/-- `(Φ.trans ι)^* h = Φ^* (ι^* h)`（逐点，经 `mfderiv_comp`）。 -/
theorem pullbackMetricCross_trans_inner_WA (h : SmoothRiemannianMetric 𝓘(ℝ, E) Y)
    (Φ : X ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ X) (ι : X ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ Y) (q : X)
    (w w' : TangentSpace 𝓘(ℝ, E) q) :
    (Diffeomorph.pullbackMetricCross h (Φ.trans ι)).inner q w w' =
      (Diffeomorph.pullbackMetricCross h ι).inner (Φ q)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q w') := by
  rw [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner]
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.trans ι) q =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι (Φ q)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q) := by
    rw [Diffeomorph.coe_trans]
    exact mfderiv_comp q (ι.contMDiff.mdifferentiableAt (by simp))
      (Φ.contMDiff.mdifferentiableAt (by simp))
  rw [hd]
  rfl

end Transport

section Window

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
  (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
  (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)

/-- regular 时刻的 HT-L（`K = univ`，`φ = (ι_s ∘ Φ_s)⁻¹`）：window 数据（image equality 版）+
单侧一致比较 `G t₀ ≤ e^ε Φ_s^* G s` + 每个 `s` 的 minimizer ⇒ `false_of_morreyAreaS_transport_IF`
的 `hL` 在 `t₀` 处的子句。 -/
theorem ht_left_of_window_WA {t₀ : ℝ} (ht₀ : T ≤ t₀)
    (hmin : ∀ (s : ℝ) (hs : T ≤ s), ∃ v : C(closedDisk, (postStage O s).Carrier),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
      DiskWeakJordanTrace (γ s hs) v ∧ range v ⊆ W s ∧
      riemannianDiskArea (postMetric O s) v ≤ morreyAreaS O W T γ s)
    {I : Set ℝ} (hI : IsOpen I) (ht₀I : t₀ ∈ I)
    {G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage O t₀).Carrier}
    (hG₀ : G t₀ = postMetric O t₀)
    {Φ : ℝ → (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t₀).Carrier}
    (hι : ∀ t ∈ I, ∀ ht : T ≤ t,
      ∃ ι : (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O t).Carrier,
        G t = Diffeomorph.pullbackMetricCross (postMetric O t) ι ∧
        (∀ θ, ι (Φ t (γ t₀ ht₀ θ)) = γ t ht θ) ∧
        (fun p => ι (Φ t p)) '' W t₀ = W t)
    (hcmp : ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 t₀, ∀ (p : (postStage O t₀).Carrier)
      (w : TangentSpace (𝓡 3) p),
        (G t₀).inner p w w ≤ Real.exp ε *
          (G s).inner (Φ s p) (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w)
            (mfderiv (𝓡 3) (𝓡 3) (Φ s) p w)) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
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
              Real.exp ε * (postMetric O s).inner p w w := by
  intro ε hε
  have hIev : ∀ᶠ s in 𝓝 t₀, s ∈ I := hI.mem_nhds ht₀I
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hIev.and (hcmp ε hε))
  refine ⟨δ, hδ, fun s hs hlo hhi => ?_⟩
  have hd : dist s t₀ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨hsI, hcs⟩ := hball hd
  obtain ⟨ι, hGι, hγι, hWι⟩ := hι s hsI hs
  obtain ⟨v, hvs, hvt, hvW, hvA⟩ := hmin s hs
  let ψ : (postStage O t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage O s).Carrier := (Φ s).trans ι
  have hψ : ∀ p, ψ p = ι (Φ s p) := fun _ => rfl
  refine ⟨v, univ, ψ.symm, hvs, hvt, hvW, hvA, subset_univ _, isOpen_univ,
    ψ.symm.contMDiff.contMDiffOn, ?_, ?_, ?_⟩
  · rintro x ⟨-, hx⟩
    rw [← hWι] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    change ψ.symm (ψ p) ∈ W t₀
    rw [ψ.symm_apply_apply]
    exact hp
  · intro θ
    rw [← hγι θ, ← hψ, ψ.symm_apply_apply]
  · intro p _ w
    have key := hcs (ψ.symm p) (mfderiv (𝓡 3) (𝓡 3) ψ.symm p w)
    rw [hG₀, hGι, ← pullbackMetricCross_trans_inner_WA] at key
    have hgs : Diffeomorph.pullbackMetricCross
        (Diffeomorph.pullbackMetricCross (postMetric O s) ψ) ψ.symm = postMetric O s :=
      Diffeomorph.pullbackMetricCross_symm_eq_iff.mp rfl
    conv_rhs => rw [← hgs, Diffeomorph.pullbackMetricCross_inner]
    exact key

/-- event 时刻的 HT-R（`K = univ`）：post-surgery 侧的全局 transport（光滑映射 `φ`，保 γ、保 region、
`φ^* g(s) ≤ e^ε g(t₀)`）+ `t₀` 处的 minimizer ⇒ `false_of_morreyAreaS_transport_IF` 的 `hR` 子句。 -/
theorem ht_right_of_transport_WA {t₀ : ℝ} (ht₀ : T ≤ t₀)
    (hmin₀ : ∃ v : C(closedDisk, (postStage O t₀).Carrier),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
      DiskWeakJordanTrace (γ t₀ ht₀) v ∧ range v ⊆ W t₀ ∧
      riemannianDiskArea (postMetric O t₀) v ≤ morreyAreaS O W T γ t₀)
    (htr : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (s : ℝ) (hs : T ≤ s), t₀ < s → s < t₀ + δ →
      ∃ φ : (postStage O t₀).Carrier → (postStage O s).Carrier,
        ContMDiff (𝓡 3) (𝓡 3) ∞ φ ∧ MapsTo φ (W t₀) (W s) ∧
        (∀ θ, φ (γ t₀ ht₀ θ) = γ s hs θ) ∧
        ∀ (p : (postStage O t₀).Carrier) (w : TangentSpace (𝓡 3) p),
          (postMetric O s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
              (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
            Real.exp ε * (postMetric O t₀).inner p w w) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
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
              Real.exp ε * (postMetric O t₀).inner p w w := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := htr ε hε
  obtain ⟨v, hvs, hvt, hvW, hvA⟩ := hmin₀
  refine ⟨δ, hδ, fun s hs hlo hhi => ?_⟩
  obtain ⟨φ, hφ, hW, hγφ, hmet⟩ := hd s hs hlo hhi
  exact ⟨v, univ, φ, hvs, hvt, hvW, hvA, subset_univ _, isOpen_univ, hφ.contMDiffOn,
    fun _ hx => hW hx.2, hγφ, fun p _ w => hmet p w⟩

end Window

end GC.LongTime.CuspP1
