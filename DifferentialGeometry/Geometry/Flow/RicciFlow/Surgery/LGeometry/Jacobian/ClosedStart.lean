import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.EndpointContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.ClosedStart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AlongGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Integral.Measure (paramDensity chartDensity
  paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt)
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis chartGramMatrix)
open DifferentialGeometry.Geometry.Connection (trivToE)

open private inner_chartVector_sum from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
open private mem_regularizedStage_Icc mem_regularizedStage_Ioo LWindow.mem_range_of_mem_Icc
  contDiffAt_familySeed eq_of_mem_Ioo_of_mem_Icc from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity
open private isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn
  hasHistoryLInitialVector_of_eq_of_le exists_stage_window_lift
  stageRegularizedLagrangian_congr_nhds from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.ClosedStart
open private lt_stageEndTime_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Basic

universe u

private theorem continuousWithinAt_paramDensity_of_metricSmoothUpTo
    {P : OrientedThreeStage.{u}} {g : ℝ → P.Metric} {J : Set ℝ} (hg : P.MetricSmoothUpTo g J)
    {β : ThreeSpace × ℝ → P.Carrier} {V : Set ThreeSpace} {K : Set ℝ} (hV : IsOpen V)
    (hK : IsOpen K) (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
    {Z₀ : ThreeSpace} (hZ₀ : Z₀ ∈ V) {τ : ℝ → ℝ} (hτ : Continuous τ) {S : Set ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ K) (hτS : ∀ s ∈ S, τ s ∈ J) (hτs₀ : τ s₀ ∈ J) :
    ContinuousWithinAt (fun s => paramDensity (g (τ s)) (fun Z => β (Z, s)) Z₀) S s₀ := by
  set y₀ := β (Z₀, s₀) with hy₀
  obtain ⟨U, hU, hy₀U, hUb, V', hV', hτV', A, hA, hAeq⟩ := hg y₀ (τ s₀) hτs₀
  have hUsrc : ∀ y ∈ U, y ∈ (chartAt ThreeSpace y₀).source := fun y hy => by
    have h := hUb hy
    rwa [TangentBundle.trivializationAt_baseSet] at h
  set O : Set (ThreeSpace × ℝ) := (V ×ˢ K) ∩ β ⁻¹' U with hOdef
  have hO : IsOpen O := hβ.continuousOn.isOpen_inter_preimage (hV.prod hK) hU
  have hZs₀ : (Z₀, s₀) ∈ O := ⟨⟨hZ₀, hs₀⟩, hy₀U⟩
  let Φ : ThreeSpace × ℝ → ThreeSpace := fun q => extChartAt ThreeModel y₀ (β q)
  have hβ' : ContMDiffOn 𝓘(ℝ, ThreeSpace × ℝ) ThreeModel ∞ β (V ×ˢ K) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hβ
  have hΦ : ContDiffOn ℝ ∞ Φ O := by
    have h1 : ContMDiffOn 𝓘(ℝ, ThreeSpace × ℝ) 𝓘(ℝ, ThreeSpace) ∞ Φ O :=
      (contMDiffOn_extChartAt (I := ThreeModel) (x := y₀) (n := ∞)).comp
        (hβ'.mono inter_subset_left) fun q hq => hUsrc _ hq.2
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hΦd : ContinuousOn (fderiv ℝ Φ) O := hΦ.continuousOn_fderiv_of_isOpen hO (by simp)
  have hpair : Continuous fun s : ℝ => ((Z₀, s) : ThreeSpace × ℝ) := by fun_prop
  have hevO : ∀ᶠ s in 𝓝 s₀, (Z₀, s) ∈ O :=
    hpair.continuousAt.preimage_mem_nhds (hO.mem_nhds hZs₀)
  have hevV' : ∀ᶠ s in 𝓝 s₀, τ s ∈ V' := hτ.continuousAt.preimage_mem_nhds (hV'.mem_nhds hτV')
  let inlL : (ThreeSpace × ℝ →L[ℝ] ThreeSpace) →L[ℝ] (ThreeSpace →L[ℝ] ThreeSpace) :=
    (ContinuousLinearMap.compL ℝ ThreeSpace (ThreeSpace × ℝ) ThreeSpace).flip
      (ContinuousLinearMap.inl ℝ ThreeSpace ℝ)
  have hDc : ContinuousAt (fun s : ℝ => |(inlL (fderiv ℝ Φ (Z₀, s))).det|) s₀ := by
    have h1 : ContinuousAt (fun s : ℝ => fderiv ℝ Φ (Z₀, s)) s₀ :=
      (hΦd.continuousAt (hO.mem_nhds hZs₀)).comp hpair.continuousAt
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      (inlL.continuous.continuousAt.comp h1)).abs
  let M : ℝ → Matrix (Fin (Module.finrank ℝ ThreeSpace)) (Fin (Module.finrank ℝ ThreeSpace)) ℝ :=
    fun s => Matrix.of fun i k => ∑ a : Fin 3, ∑ b : Fin 3,
      (chartModelBasis ThreeSpace i) a * (chartModelBasis ThreeSpace k) b *
        A (τ s, β (Z₀, s)) a b
  have hβZ : ContinuousAt (fun s : ℝ => β (Z₀, s)) s₀ :=
    (hβ.continuousOn.continuousAt ((hV.prod hK).mem_nhds ⟨hZ₀, hs₀⟩)).comp hpair.continuousAt
  have hMc : ContinuousAt M s₀ := by
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun k => ?_
    change ContinuousAt (fun s => ∑ a : Fin 3, ∑ b : Fin 3,
      (chartModelBasis ThreeSpace i) a * (chartModelBasis ThreeSpace k) b *
        A (τ s, β (Z₀, s)) a b) s₀
    refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
    refine (continuousAt_const.mul ?_ : ContinuousAt (fun s =>
      (chartModelBasis ThreeSpace i) a * (chartModelBasis ThreeSpace k) b *
        A (τ s, β (Z₀, s)) a b) s₀)
    have hAab : ContinuousAt (fun z : ℝ × P.Carrier => A z a b) (τ s₀, y₀) :=
      ((hA a b).continuousOn).continuousAt ((hV'.prod hU).mem_nhds ⟨hτV', hy₀U⟩)
    exact ContinuousAt.comp (g := fun z : ℝ × P.Carrier => A z a b)
      (f := fun s => (τ s, β (Z₀, s))) hAab (hτ.continuousAt.prodMk hβZ)
  have hMdc : ContinuousAt (fun s => Real.sqrt (M s).det) s₀ :=
    Real.continuous_sqrt.continuousAt.comp ((continuous_id.matrix_det).continuousAt.comp hMc)
  have hkey : ∀ s, (Z₀, s) ∈ O → τ s ∈ V' ∩ J →
      paramDensity (g (τ s)) (fun Z => β (Z, s)) Z₀ =
        |(inlL (fderiv ℝ Φ (Z₀, s))).det| * Real.sqrt (M s).det := by
    intro s hs hτs
    have hsVK : (Z₀, s) ∈ V ×ˢ K := hs.1
    have hmd : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, s)) Z₀ :=
      (((hβ (Z₀, s) hsVK).contMDiffAt ((hV.prod hK).mem_nhds hsVK)).comp Z₀
        (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
    have hbase : β (Z₀, s) ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y₀).baseSet :=
      hUb hs.2
    rw [paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt (g (τ s))
      (fun Z => β (Z, s)) hmd y₀ hbase]
    have hfd : fderiv ℝ (fun z : ThreeSpace => extChartAt ThreeModel y₀ (β (z, s))) Z₀ =
        inlL (fderiv ℝ Φ (Z₀, s)) := by
      have hdiff : DifferentiableAt ℝ Φ (Z₀, s) :=
        (hΦ.contDiffAt (hO.mem_nhds hs)).differentiableAt (by simp)
      exact (hdiff.hasFDerivAt.comp Z₀ (hasFDerivAt_prodMk_left (𝕜 := ℝ) Z₀ s)).fderiv
    rw [hfd]
    congr 1
    unfold chartDensity
    congr 2
    ext i k
    rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
    simp only [M, Matrix.of_apply]
    unfold DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
    rw [inner_chartVector_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hAeq (τ s) hτs (β (Z₀, s)) hs.2 a b]
  have hcont : ContinuousAt (fun s => |(inlL (fderiv ℝ Φ (Z₀, s))).det| * Real.sqrt (M s).det)
      s₀ := hDc.mul hMdc
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_
    (hkey s₀ hZs₀ ⟨hτV', hτs₀⟩)
  filter_upwards [nhdsWithin_le_nhds hevO, nhdsWithin_le_nhds hevV', self_mem_nhdsWithin]
    with s hsO hsV' hsS
  exact hkey s hsO ⟨hsV', hτS s hsS⟩

section ClosedStartFamily

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T v : ℝ} {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_family_of_closedStart (hv : 0 < v) (hstart : T - v ^ 2 = H.time first)
    (htf : H.time first < H.stageEndTime first) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
      ∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p),
      ∃ s₀ < v, 0 < s₀ ∧ ∃ δ > 0, ∃ β : ThreeSpace × ℝ → (H.stage first).Carrier,
        ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ Ioo s₀ (v + δ)) ∧
        ∀ Z (hZ : Z ∈ V), ∀ r ∈ Ioc s₀ v,
          H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩ ⟨first, le_rfl, hle⟩ r = β (Z, r) := by
  classical
  obtain ⟨G, -, hGm⟩ := exists_incomingSlab_stageMetric first htf
  have hmetric := G.smoothUpTo.jointContMDiffOn
  have hSm : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first),
      G.flow.base.metric t = H.stageMetric first t := fun t ht => (hGm t ht).symm
  have hSreg : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first),
      t ∈ (RealTimeInterval.closedOpen (H.time first) (H.stageEndTime first) G.lt).regular :=
    fun t ht => ht
  set fZ : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  set Zd : H.historyLExpDomain hle T v p := ⟨Z₀, hZ₀⟩
  have hα₀ := isHistoryLGeodesicOn_historyLCurve Zd
  have hinit₀ := hasHistoryLInitialVector_historyLCurve Zd
  have hev1 : ∀ᶠ s in 𝓝[<] v, 0 < s ∧ T - s ^ 2 < H.stageEndTime first := by
    have hc : ContinuousAt (fun s : ℝ => T - s ^ 2) v := by fun_prop
    filter_upwards [nhdsWithin_le_nhds (hc.eventually_lt continuousAt_const
      (by rw [hstart]; exact htf)), nhdsWithin_le_nhds (lt_mem_nhds hv)] with s h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨s₁, ⟨hs₁pos, hs₁b⟩, hs₁v⟩ := (hev1.and self_mem_nhdsWithin).exists
  have hs₁v' : s₁ < v := hs₁v
  have hin : ∀ s ∈ Ioo s₁ v, T - s ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
    intro s hs
    have h1 : s₁ ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs.1 hs₁pos.le two_ne_zero
    have h2 : s ^ 2 < v ^ 2 := pow_lt_pow_left₀ hs.2 (hs₁pos.trans hs.1).le two_ne_zero
    constructor <;> linarith
  have hgeo₀ := isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn hα₀ G.flow hSm hSreg
    hs₁pos le_rfl hin
  obtain ⟨ξ, hlim⟩ := exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart
    G.flow G.equation htf hmetric hs₁pos hs₁v' hstart (fun s hs => hSreg _ (hin s hs)) hgeo₀
  set γ₀ : ℝ → (H.stage first).Carrier := H.historyLCurve hle T v p Zd fZ
  set x0 := ξ.proj
  set e := trivializationAt ThreeSpace (TangentSpace ThreeModel) x0
  set zl : ThreeSpace × ThreeSpace := (extChartAt ThreeModel x0 x0, (e ξ).2)
  have hξ : ξ ∈ e.source := by
    rw [e.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' x0
  have hzl : zl.1 ∈ interior (extChartAt ThreeModel x0).target := by
    rw [(isOpen_extChartAt_target (I := ThreeModel) x0).interior_eq]
    exact mem_extChartAt_target (I := ThreeModel) x0
  let st : ℝ → ThreeSpace × ThreeSpace := fun s =>
    (extChartAt ThreeModel x0 (γ₀ s),
      trivToE (I := ThreeModel) x0 (γ₀ s) (lVelocity (I := ThreeModel) γ₀ s))
  have hlim' := (e.tendsto_nhds_iff hξ).mp hlim
  have hproj : Tendsto γ₀ (𝓝[<] v) (𝓝 x0) := hlim'.1
  have hbase : ∀ᶠ s in 𝓝[<] v, γ₀ s ∈ (chartAt ThreeSpace x0).source :=
    hproj.eventually ((chartAt ThreeSpace x0).open_source.mem_nhds (mem_chart_source ThreeSpace x0))
  have hst : Tendsto st (𝓝[<] v) (𝓝 zl) := by
    refine ((continuousAt_extChartAt (I := ThreeModel) x0).tendsto.comp hproj).prodMk_nhds ?_
    refine hlim'.2.congr' ?_
    filter_upwards [hbase] with s hs
    have hsb : γ₀ s ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hs
    exact (e.continuousLinearMapAt_apply_of_mem (R := ℝ) hsb _).symm
  obtain ⟨ε, hε, W, hWo, hvW, -, Ψ, hΨ0, hΨsm, hΨd⟩ :=
    exists_lPhaseFlow_of_start G.flow htf hmetric hv hstart x0 zl hzl
  have hmax : max s₁ (v - ε) < v := max_lt hs₁v' (by linarith)
  have hpair : Tendsto (fun s => (s, st s)) (𝓝[<] v) (𝓝 (v, zl)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).prodMk_nhds hst
  obtain ⟨c₀, hc₀W, hc₀src, hc₀I⟩ := ((hpair.eventually (hWo.mem_nhds hvW)).and
    (hbase.and (Ioo_mem_nhdsLT hmax))).exists
  set c : ℝ := (c₀ + v) / 2 with hcdef
  have hc₀c : c₀ < c := by linarith [hc₀I.2]
  have hcv : c < v := by linarith [hc₀I.2]
  have hms : max s₁ (v - ε) < c₀ := hc₀I.1
  have hs₁c₀ : s₁ < c₀ := (le_max_left _ _).trans_lt hms
  have hc₀pos : 0 < c₀ := hs₁pos.trans hs₁c₀
  have hcpos : 0 < c := hc₀pos.trans hc₀c
  have hcin := hin c ⟨hs₁c₀.trans hc₀c, hcv⟩
  have hcdom : T - c ^ 2 ∈ H.stageDomain first := H.mem_stageDomain_of_mem_Ioo hcin
  have hαc := hα₀.truncate le_rfl hle hcpos hcv.le hcdom
  have hinitc := hinit₀.truncate hcpos le_rfl hcdom
  obtain ⟨lo, hi, hlo, hhi, Wc, hcW, -, γc, hγc, heqc⟩ := hα₀.2.2.1 c ⟨hcpos, hcv⟩
  have hjc : lo ≤ first ∧ first ≤ hi :=
    LWindow.mem_range_of_mem_Icc Wc hcW ⟨hcin.1.le, hcin.2.le⟩
  set a' : ℝ := max Wc.a c₀
  set b' : ℝ := min Wc.b ((c + v) / 2)
  have ha'c : a' < c := max_lt hcW.1 hc₀c
  have hcb' : c < b' := lt_min hcW.2 (by linarith)
  have ha'I : a' ∈ Ioo s₁ v := ⟨hs₁c₀.trans_le (le_max_right _ _), ha'c.trans hcv⟩
  have hb'I : b' ∈ Ioo s₁ v :=
    ⟨(hs₁c₀.trans hc₀c).trans hcb', (min_le_right _ _).trans_lt (by linarith)⟩
  let W₁ := Wc.restrict hjc.1 hjc.2 le_rfl (le_max_left _ _) (ha'c.trans hcb') (min_le_left _ _)
    (H.mem_stageDomain_of_mem_Ioo (hin a' ha'I)) (H.mem_stageDomain_of_mem_Ioo (hin b' hb'I))
  have hZ₀c : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T c p := by
    refine ⟨_, hαc, hinitc, W₁, ⟨ha'c, hcb'⟩, γc,
      fun r hr => hγc r ⟨(le_max_left _ _).trans_lt hr.1, hr.2.trans_le (min_le_left _ _)⟩,
      fun r hr => ?_⟩
    have ht := hin r ⟨hs₁c₀.trans_le ((le_max_right _ _).trans hr.1.le), hr.2.trans_lt hcv⟩
    exact heqc ⟨first, hjc⟩ (mem_regularizedStage_Icc Wc.nonneg
      ⟨(le_max_left _ _).trans hr.1.le, hr.2.trans hcW.2.le⟩ ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨V₁, hV₁, hZ₀V₁, -, hV₁dom, lo₁, hi₁, hlo₁, hhi₁, W₂, K₁, hK₁, hc₀K₁, hK₁W, β₁, hβ₁,
    hgeo₁, hrep₁⟩ := exists_contMDiffOn_window_family_historyLCurve hcpos hZ₀c ⟨hc₀pos, hc₀c⟩
  have ht₀ := hin c₀ ⟨hs₁c₀, hc₀c.trans hcv⟩
  have hj₁ : lo₁ ≤ first ∧ first ≤ hi₁ :=
    LWindow.mem_range_of_mem_Icc W₂ (hK₁W hc₀K₁) ⟨ht₀.1.le, ht₀.2.le⟩
  let F₁ : ThreeSpace × ℝ → (H.stage first).Carrier := fun q => W₂.f ⟨first, hj₁⟩ (β₁ q)
  set O₁ : Set ℝ := K₁ ∩ Ioo (H.regularizedStageStart T W₂.a first)
    (H.regularizedStageEnd T W₂.b first) ∩ Ioo (max s₁ (v - ε)) c
  have hO₁ : IsOpen O₁ := (hK₁.inter isOpen_Ioo).inter isOpen_Ioo
  have hc₀O₁ : c₀ ∈ O₁ :=
    ⟨⟨hc₀K₁, mem_regularizedStage_Ioo W₂.nonneg (hK₁W hc₀K₁) ht₀⟩, hms, hc₀c⟩
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 hO₁ c₀ hc₀O₁
  set J₁ : Set ℝ := Ioo (c₀ - δ₁) (c₀ + δ₁)
  have hJ₁ : J₁ ⊆ O₁ := fun r hr => hball₁ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  have hc₀J₁ : c₀ ∈ J₁ := ⟨by linarith, by linarith⟩
  have hJ₁in : ∀ r ∈ J₁, r ∈ Ioo s₁ v := fun r hr =>
    ⟨(le_max_left _ _).trans_lt (hJ₁ hr).2.1, (hJ₁ hr).2.2.trans hcv⟩
  have hJ₁L : J₁ ⊆ Ioo (max s₁ (v - ε)) v := fun r hr => ⟨(hJ₁ hr).2.1, (hJ₁ hr).2.2.trans hcv⟩
  have hF₁geo : ∀ Z ∈ V₁, IsLRegularizedGeodesicOn G.flow T (fun r => F₁ (Z, r)) J₁ :=
    fun Z hZ => LWindow.isLRegularizedGeodesicOn_comp W₂ ⟨first, hj₁⟩ G.flow isOpen_Ioo
      (fun r hr => (hJ₁ hr).1.2) (fun r hr => hSm _ (hin r (hJ₁in r hr)))
      (fun r hr => hSreg _ (hin r (hJ₁in r hr))) (fun r hr => hgeo₁ Z hZ r (hJ₁ hr).1.1)
  have hF₁rep : ∀ Z (hZ : Z ∈ V₁), ∀ r ∈ J₁,
      H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ⟩ fZ r = F₁ (Z, r) := fun Z hZ r hr =>
    hrep₁ Z hZ ⟨first, hj₁⟩ r (hJ₁ hr).1
  have hF₁at : ∀ Z ∈ V₁, ContMDiffAt (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ F₁ (Z, c₀) :=
    fun Z hZ => (W₂.localDiffeomorph _).contMDiff.contMDiffAt.comp (Z, c₀)
      ((hβ₁ (Z, c₀) ⟨hZ, hc₀K₁⟩).contMDiffAt ((hV₁.prod hK₁).mem_nhds ⟨hZ, hc₀K₁⟩))
  have hposC : ContinuousOn (fun Z => F₁ (Z, c₀)) V₁ := fun Z hZ =>
    (((hF₁at Z hZ).comp (f := fun Z' : ThreeSpace => (Z', c₀)) Z
      (contMDiffAt_id.prodMk contMDiffAt_const)).continuousAt).continuousWithinAt
  set V₁' : Set ThreeSpace := V₁ ∩ (fun Z => F₁ (Z, c₀)) ⁻¹' (chartAt ThreeSpace x0).source
  have hV₁' : IsOpen V₁' := hposC.isOpen_inter_preimage hV₁ (chartAt ThreeSpace x0).open_source
  let σ : ThreeSpace → ThreeSpace × ThreeSpace := fun Z =>
    (extChartAt ThreeModel x0 (F₁ (Z, c₀)),
      fderiv ℝ (fun s : ℝ => extChartAt ThreeModel x0 (F₁ (Z, s))) c₀ (1 : ℝ))
  have hσ : ContDiffOn ℝ ∞ σ V₁' := fun Z hZ =>
    (contDiffAt_familySeed x0 hZ.2 (hF₁at Z hZ.1)).contDiffWithinAt
  have hσv : ∀ Z ∈ V₁', σ Z = (extChartAt ThreeModel x0 (F₁ (Z, c₀)),
      trivToE (I := ThreeModel) x0 (F₁ (Z, c₀))
        (lVelocity (I := ThreeModel) (fun s => F₁ (Z, s)) c₀)) := fun Z hZ =>
    Prod.ext rfl (lPhaseSeed_velocity (I := ThreeModel) x0 ((hF₁geo Z hZ.1) c₀ hc₀J₁).2.1 hZ.2)
  set V₂ : Set ThreeSpace :=
    V₁' ∩ (fun Z => ((c₀, σ Z) : ℝ × (ThreeSpace × ThreeSpace))) ⁻¹' W
  have hV₂ : IsOpen V₂ :=
    (continuousOn_const.prodMk hσ.continuousOn).isOpen_inter_preimage hV₁' hWo
  have hγ₀F : ∀ r ∈ J₁, F₁ (Z₀, r) = γ₀ r := by
    intro r hr
    have ht := hin r (hJ₁in r hr)
    have hrc : r ∈ Icc (H.regularizedStageStart T 0 first) (H.regularizedStageEnd T c first) :=
      mem_regularizedStage_Icc le_rfl ⟨(hs₁pos.trans (hJ₁in r hr).1).le, (hJ₁ hr).2.2.le⟩
        ⟨ht.1.le, ht.2.le⟩
    rw [← hF₁rep Z₀ hZ₀V₁ r hr]
    exact eqOn_historyLCurve hcpos _ hαc hinitc fZ hrc
  have hγ₀germ : (fun r => F₁ (Z₀, r)) =ᶠ[𝓝 c₀] γ₀ :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hc₀J₁) fun r hr => hγ₀F r hr
  have hvelF : lVelocity (I := ThreeModel) (fun r => F₁ (Z₀, r)) c₀ =
      lVelocity (I := ThreeModel) γ₀ c₀ := by
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hγ₀germ
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  have hZ₀V₁' : Z₀ ∈ V₁' := by
    refine ⟨hZ₀V₁, ?_⟩
    change F₁ (Z₀, c₀) ∈ (chartAt ThreeSpace x0).source
    rw [hγ₀F c₀ hc₀J₁]
    exact hc₀src
  have hσZ₀ : σ Z₀ = st c₀ := by
    simp only [hσv Z₀ hZ₀V₁', hvelF]
    rw [hγ₀F c₀ hc₀J₁]
  have hZ₀V₂ : Z₀ ∈ V₂ := by
    refine ⟨hZ₀V₁', ?_⟩
    change ((c₀, σ Z₀) : ℝ × (ThreeSpace × ThreeSpace)) ∈ W
    rw [hσZ₀]
    exact hc₀W
  let zZ : ThreeSpace → ℝ → ThreeSpace × ThreeSpace := fun Z r => Ψ ((c₀, σ Z), r)
  let βt : ThreeSpace → ℝ → (H.stage first).Carrier := fun Z =>
    lPhaseCurve (I := ThreeModel) x0 (zZ Z)
  have hLsub : ∀ r ∈ Ioo (max s₁ (v - ε)) v, r ∈ Ioc (v - ε) v ∧ r ∈ Ioo s₁ v := fun r hr =>
    ⟨⟨(le_max_right _ _).trans_lt hr.1, hr.2.le⟩, ⟨(le_max_left _ _).trans_lt hr.1, hr.2⟩⟩
  have hzd : ∀ Z ∈ V₂, ∀ r ∈ Ioo (max s₁ (v - ε)) v,
      HasDerivAt (zZ Z) (lPhaseField G.flow T x0 r (zZ Z r)) r ∧
        T - r ^ 2 ∈ (RealTimeInterval.closedOpen (H.time first) (H.stageEndTime first)
          G.lt).regular ∧
        (zZ Z r).1 ∈ interior (extChartAt ThreeModel x0).target := fun Z hZ r hr =>
    ⟨(hΨd _ hZ.2 r (hLsub r hr).1).1, hSreg _ (hin r (hLsub r hr).2),
      (hΨd _ hZ.2 r (hLsub r hr).1).2.2⟩
  have hβtgeo : ∀ Z ∈ V₂,
      IsLRegularizedGeodesicOn G.flow T (βt Z) (Ioo (max s₁ (v - ε)) v) :=
    fun Z hZ => isLRegularizedGeodesicOn_lPhaseCurve G.flow T x0 isOpen_Ioo (hzd Z hZ)
  have hagreeJ : ∀ Z ∈ V₂, ∀ r ∈ J₁, F₁ (Z, r) = βt Z r := fun Z hZ r hr =>
    eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn G.flow G.equation T x0 isOpen_Ioo
      isPreconnected_Ioo (hF₁geo Z hZ.1.1) isOpen_Ioo isPreconnected_Ioo (hzd Z hZ) hc₀J₁
      (hJ₁L hc₀J₁) hZ.1.2 ((hΨ0 _ hZ.2).trans (hσv Z hZ.1)) ⟨hr, hJ₁L hr⟩
  have hαcgeo : ∀ Z (hZ : Z ∈ V₁), IsLRegularizedGeodesicOn G.flow T
      (H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ⟩ fZ) (Ioo s₁ c) := fun Z hZ =>
    isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn (isHistoryLGeodesicOn_historyLCurve _)
      G.flow hSm hSreg hs₁pos le_rfl fun s hs => hin s ⟨hs.1, hs.2.trans hcv⟩
  have hmc : max s₁ (v - ε) < c := hms.trans hc₀c
  have hagree : ∀ Z (hZ : Z ∈ V₂), ∀ r ∈ Ioc (max s₁ (v - ε)) c,
      H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ r = βt Z r := by
    intro Z hZ
    have hgerm : H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ =ᶠ[𝓝 c₀] βt Z :=
      eventually_of_mem (isOpen_Ioo.mem_nhds hc₀J₁) fun r hr =>
        (hF₁rep Z hZ.1.1 r hr).trans (hagreeJ Z hZ r hr)
    have hvel : lVelocity (I := ThreeModel) (H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ)
        c₀ = lVelocity (I := ThreeModel) (βt Z) c₀ := by
      have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hgerm
      with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
    have heq := lRegularizedSolution_eqOn G.flow G.equation T isOpen_Ioo isPreconnected_Ioo
      (⟨hs₁c₀, hc₀c⟩ : c₀ ∈ Ioo s₁ c) isOpen_Ioo isPreconnected_Ioo (hJ₁L hc₀J₁)
      (hαcgeo Z hZ.1.1) (hβtgeo Z hZ) hgerm.self_of_nhds hvel
    intro r hr
    rcases hr.2.lt_or_eq with hrc | hrc
    · exact heq ⟨⟨(le_max_left _ _).trans_lt hr.1, hrc⟩, hr.1, hrc.trans hcv⟩
    rw [hrc]
    have hcont1 := (isHistoryLGeodesicOn_historyLCurve
      (⟨Z, hV₁dom Z hZ.1.1⟩ : H.historyLExpDomain hle T c p)).2.2.2
    have hcont2 : ContinuousWithinAt (βt Z) (Iio c) c :=
      ((hβtgeo Z hZ) c ⟨hmc, hcv⟩).2.1.continuousAt.continuousWithinAt
    have hev : H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ =ᶠ[𝓝[<] c] βt Z := by
      filter_upwards [Ioo_mem_nhdsLT hmc] with r' hr'
      exact heq ⟨⟨(le_max_left _ _).trans_lt hr'.1, hr'.2⟩, hr'.1, hr'.2.trans hcv⟩
    exact tendsto_nhds_unique_of_eventuallyEq hcont1 hcont2 hev
  let A : ∀ Z ∈ V₂, (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun Z hZ j r => if h : j.val = first ∧ c < r then
      cast (congrArg (fun k => (H.stage k).Carrier) h.1.symm) (βt Z r)
    else H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ j r
  have hAle : ∀ Z (hZ : Z ∈ V₂) j r, r ≤ c →
      A Z hZ j r = H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ j r := fun Z hZ j r hr =>
    dite_eq_right fun h => (not_lt.2 hr) h.2
  have hAgt : ∀ Z (hZ : Z ∈ V₂) r, c < r → A Z hZ fZ r = βt Z r := fun Z hZ r hr => by
    simp only [A, dite_eq_left (show fZ.val = first ∧ c < r from ⟨rfl, hr⟩)]
    rfl
  have hAfirst : ∀ Z (hZ : Z ∈ V₂), ∀ r ∈ Ioc (max s₁ (v - ε)) v, A Z hZ fZ r = βt Z r := by
    intro Z hZ r hr
    rcases le_or_gt r c with hrc | hrc
    · rw [hAle Z hZ fZ r hrc]
      exact hagree Z hZ r ⟨hr.1, hrc⟩
    · exact hAgt Z hZ r hrc
  have hvI : v ∈ Ioo (v - ε) (v + ε) := ⟨by linarith, by linarith⟩
  have hvI' : v ∈ Ioc (v - ε) v := ⟨by linarith, le_rfl⟩
  have hmem : ∀ Z (hZ : Z ∈ V₂), H.IsHistoryLGeodesicOn hle T v (A Z hZ) ∧
      H.HasHistoryLInitialVector T (A Z hZ) p Z := by
    intro Z hZ
    have hαcZ := isHistoryLGeodesicOn_historyLCurve
      (⟨Z, hV₁dom Z hZ.1.1⟩ : H.historyLExpDomain hle T c p)
    have hinitcZ := hasHistoryLInitialVector_historyLCurve
      (⟨Z, hV₁dom Z hZ.1.1⟩ : H.historyLExpDomain hle T c p)
    refine ⟨⟨hα₀.1, fun i hf hl => ?_, fun s hs => ?_, ?_⟩,
      hasHistoryLInitialVector_of_eq_of_le hcpos hcdom hinitcZ fun j r hr => hAle Z hZ j r hr⟩
    · have h1 : H.stageEndTime first ≤ H.time i.succ := by
        rw [← stageEndTime_castSucc]
        exact H.stageEndTime_mono hf
      have hw : Real.sqrt (T - H.time i.succ) ≤ c :=
        ((Real.sqrt_lt' hcpos).2 (by linarith [hcin.2])).le
      rw [hAle Z hZ _ _ hw, hAle Z hZ _ _ hw]
      exact hαcZ.2.1 i hf hl
    · rcases lt_or_ge s c with hsc | hsc
      · obtain ⟨lo', hi', hlo', hhi', W', hsW', hbc, γ', hγ', heq'⟩ := hαcZ.2.2.1 s ⟨hs.1, hsc⟩
        refine ⟨lo', hi', hlo', hhi', W', hsW', hbc.trans hcv.le, γ', hγ', fun j r hr => ?_⟩
        rw [heq' j hr, hAle Z hZ _ r ((W'.piece_subset j hr).2.trans hbc)]
      · set a₂ : ℝ := (max s₁ (v - ε) + c) / 2 with ha₂def
        set b₂ : ℝ := (s + v) / 2 with hb₂def
        have ha₂c : a₂ < c := by linarith
        have hma₂ : max s₁ (v - ε) < a₂ := by linarith
        have hsb₂ : s < b₂ := by linarith [hs.2]
        have hb₂v : b₂ < v := by linarith [hs.2]
        have ha₂0 : 0 ≤ a₂ := (hs₁pos.le.trans (le_max_left _ _)).trans hma₂.le
        have htb₂ : H.time first < T - b₂ ^ 2 := by
          have : b₂ ^ 2 < v ^ 2 := pow_lt_pow_left₀ hb₂v (by linarith) two_ne_zero
          linarith
        have hta₂ : T - a₂ ^ 2 < H.stageEndTime first :=
          (hin a₂ ⟨(le_max_left _ _).trans_lt hma₂, ha₂c.trans hcv⟩).2
        obtain ⟨Wn, hWna, hWnb, γn, hγn, hγnf⟩ := exists_stage_window_lift G.flow hSm ha₂0
          ((ha₂c.trans_le hsc).trans hsb₂) htb₂ hta₂
          (fun r hr => hβtgeo Z hZ r ⟨hma₂.trans hr.1, hr.2.trans hb₂v⟩)
        refine ⟨first, first, le_rfl, hle, Wn, by rw [hWna, hWnb]; exact ⟨ha₂c.trans_le hsc, hsb₂⟩,
          by rw [hWnb]; exact hb₂v.le, γn, hγn, fun j r hr => ?_⟩
        obtain ⟨jv, hj1, hj2⟩ := j
        obtain rfl : first = jv := le_antisymm hj1 hj2
        have hrI : r ∈ Icc Wn.a Wn.b := Wn.piece_subset _ hr
        rw [hWna, hWnb] at hrI
        change Wn.f ⟨first, hj1, hj2⟩ (γn r) = A Z hZ fZ r
        rw [hγnf r]
        exact (hAfirst Z hZ r ⟨hma₂.trans_le hrI.1, hrI.2.trans hb₂v.le⟩).symm
    · have hint := (hΨd _ hZ.2 v hvI').2.2
      have hzc : ContinuousAt (zZ Z) v :=
        (hΨsm.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
          (fun r hr => ⟨hZ.2, hr⟩)).continuousAt (isOpen_Ioo.mem_nhds hvI)
      have hβc : ContinuousAt (βt Z) v :=
        (continuousAt_extChartAt_symm'' (interior_subset hint)).comp
          (f := fun r => (zZ Z r).1) hzc.fst
      refine hβc.continuousWithinAt.congr_of_eventuallyEq ?_ (hAgt Z hZ v hcv)
      filter_upwards [Ioo_mem_nhdsLT hcv] with r hr
      exact hAgt Z hZ r hr.1
  have hV₂dom : ∀ Z ∈ V₂, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p :=
    fun Z hZ => ⟨A Z hZ, hmem Z hZ⟩
  have hhist : ∀ Z (hZ : Z ∈ V₂), ∀ r ∈ Ioc (max s₁ (v - ε)) v,
      H.historyLCurve hle T v p ⟨Z, hV₂dom Z hZ⟩ fZ r = βt Z r := by
    intro Z hZ r hr
    have hr1 : s₁ < r := (le_max_left _ _).trans_lt hr.1
    have hr0 : 0 ≤ r := hs₁pos.le.trans hr1.le
    have ht : T - r ^ 2 ∈ Icc (H.time first) (H.stageEndTime first) := by
      have h1 : s₁ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr1 hs₁pos.le two_ne_zero
      have h2 : r ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
      constructor <;> linarith
    rw [eqOn_historyLCurve hv ⟨Z, hV₂dom Z hZ⟩ (hmem Z hZ).1 (hmem Z hZ).2 fZ
      (mem_regularizedStage_Icc le_rfl ⟨hr0, hr.2⟩ ht)]
    exact hAfirst Z hZ r hr
  have hΨsm' : ContDiffOn ℝ ∞ (fun q : ThreeSpace × ℝ => Ψ ((c₀, σ q.1), q.2))
      (V₂ ×ˢ Ioo (v - ε) (v + ε)) :=
    hΨsm.comp ((contDiffOn_const.prodMk ((hσ.mono inter_subset_left).comp contDiffOn_fst
      fun q hq => hq.1)).prodMk contDiffOn_snd) fun q hq => ⟨hq.1.2, hq.2⟩
  have hOΨ := hΨsm'.continuousOn.fst.isOpen_inter_preimage (hV₂.prod isOpen_Ioo)
    (isOpen_interior (s := (extChartAt ThreeModel x0).target))
  have hZ₀v : ((Z₀, v) : ThreeSpace × ℝ) ∈ (V₂ ×ˢ Ioo (v - ε) (v + ε)) ∩
      (fun q : ThreeSpace × ℝ => (Ψ ((c₀, σ q.1), q.2)).1) ⁻¹'
        interior (extChartAt ThreeModel x0).target :=
    ⟨⟨hZ₀V₂, hvI⟩, (hΨd _ hZ₀V₂.2 v hvI').2.2⟩
  obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.1 (hOΨ.mem_nhds hZ₀v)
  obtain ⟨V₄, hV₄u, hV₄, hZ₀V₄⟩ := mem_nhds_iff.1 hu
  obtain ⟨δ, hδ, hballδ⟩ := Metric.mem_nhds_iff.1 ht
  have hδ'pos : 0 < min δ ε := lt_min hδ hε
  have hK₂sub : Ioo (max s₁ (v - ε)) (v + min δ ε) ⊆ Ioo (v - ε) (v + ε) := fun r hr =>
    ⟨(le_max_right _ _).trans_lt hr.1, hr.2.trans_le (by linarith [min_le_right δ ε])⟩
  have hV₄' : IsOpen (V₄ ∩ V₂) := hV₄.inter hV₂
  have hint2 : ∀ q ∈ (V₄ ∩ V₂) ×ˢ Ioo (max s₁ (v - ε)) (v + min δ ε),
      (Ψ ((c₀, σ q.1), q.2)).1 ∈ interior (extChartAt ThreeModel x0).target := by
    rintro ⟨Z, r⟩ ⟨hZ, hr⟩
    rcases le_or_gt r v with hrv | hrv
    · exact (hΨd _ hZ.2.2 r ⟨(le_max_right _ _).trans_lt hr.1, hrv⟩).2.2
    · have hrt : r ∈ t := hballδ (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hr.2, min_le_left δ ε])
      exact (hut ⟨hV₄u hZ.1, hrt⟩).2
  have hBsm : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞
      (fun q : ThreeSpace × ℝ => βt q.1 q.2)
      ((V₄ ∩ V₂) ×ˢ Ioo (max s₁ (v - ε)) (v + min δ ε)) := by
    have hph : ContMDiffOn 𝓘(ℝ, ThreeSpace × ℝ) 𝓘(ℝ, ThreeSpace) ∞
        (fun q : ThreeSpace × ℝ => (Ψ ((c₀, σ q.1), q.2)).1)
        ((V₄ ∩ V₂) ×ˢ Ioo (max s₁ (v - ε)) (v + min δ ε)) :=
      (hΨsm'.fst.mono (prod_mono inter_subset_right hK₂sub)).contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hph
    exact (contMDiffOn_extChartAt_symm (I := ThreeModel) (n := ∞) x0).comp hph
      fun q hq => interior_subset (s := (extChartAt ThreeModel x0).target) (hint2 q hq)
  exact ⟨V₄ ∩ V₂, hV₄', ⟨hZ₀V₄, hZ₀V₂⟩, fun Z hZ => hV₂dom Z hZ.2, max s₁ (v - ε), hmax,
    hs₁pos.trans_le (le_max_left _ _), min δ ε, hδ'pos, fun q => βt q.1 q.2, hBsm,
    fun Z hZ r hr => hhist Z hZ.2 r hr⟩

end ClosedStartFamily

section ClosedStartContinuity

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w : ℝ} {p : (H.stage last).Carrier}

private theorem historyLAction_truncate_eq (Z : H.historyLExpDomain hle T w p) {v : ℝ}
    (hv : 0 < v) (hvw : v ≤ w) (hdom : T - v ^ 2 ∈ H.stageDomain first) :
    H.historyLAction hle T v p ⟨Z.1, mem_historyLExpDomain_of_le le_rfl hle hv hvw hdom Z.2⟩ =
      ∑ j : H.StageInterval first last,
        ∫ r in H.regularizedStageStart T 0 j.val..H.regularizedStageEnd T v j.val,
          H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T w p Z j) r := by
  have hgeo := isHistoryLGeodesicOn_historyLCurve Z
  have hinit := hasHistoryLInitialVector_historyLCurve Z
  have hT := stageDomain_last_of_historyLExpDomain Z
  have hupper : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa using
      And.intro (H.time_le_of_mem_stageDomain hT) (H.le_stageEndTime_of_mem_stageDomain hT)
  have heq := eqOn_historyLCurve hv
    (⟨Z.1, mem_historyLExpDomain_of_le le_rfl hle hv hvw hdom Z.2⟩ :
      H.historyLExpDomain hle T v p)
    (hgeo.truncate le_rfl hle hv hvw hdom) (hinit.truncate hv le_rfl hdom)
  unfold historyLAction stageRegularizedAction
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb := (H.regularizedStage_bounds le_rfl hv.le hupper hdom j).2.1
  rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  refine stageRegularizedLagrangian_congr_nhds j.val T ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  exact heq j (Ioo_subset_Icc_self hr)

private theorem continuousWithinAt_sum_integral_historyLCurve (hw : 0 < w)
    (Z : H.historyLExpDomain hle T w p) :
    ContinuousWithinAt (fun v => ∑ j : H.StageInterval first last,
        ∫ r in H.regularizedStageStart T 0 j.val..H.regularizedStageEnd T v j.val,
          H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T w p Z j) r)
      {v | 0 < v ∧ v ≤ w ∧ T - v ^ 2 ∈ H.stageDomain first} w := by
  have hT := stageDomain_last_of_historyLExpDomain Z
  have hupper : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa using
      And.intro (H.time_le_of_mem_stageDomain hT) (H.le_stageEndTime_of_mem_stageDomain hT)
  refine tendsto_finsetSum _ fun j _ => ?_
  have hbw := (H.regularizedStage_bounds le_rfl hw.le hupper
    (isHistoryLGeodesicOn_historyLCurve Z).1 j).2.1
  have hint := (intervalIntegrable_iff_integrableOn_Icc_of_le hbw).1
    (intervalIntegrable_stageRegularizedLagrangian_historyLCurve hw Z j)
  rw [← uIcc_of_le hbw] at hint
  have hF := intervalIntegral.continuousOn_primitive_interval hint
  have he : Continuous fun v : ℝ => H.regularizedStageEnd T v j.val := by
    unfold regularizedStageEnd
    fun_prop
  refine ContinuousWithinAt.comp (f := fun v : ℝ => H.regularizedStageEnd T v j.val)
    (hF _ right_mem_uIcc) he.continuousWithinAt fun v hv => ?_
  rw [uIcc_of_le hbw]
  exact ⟨(H.regularizedStage_bounds le_rfl hv.1.le hupper hv.2.2 j).2.1,
    regularizedStageEnd_le_of_le hv.1.le hv.2.1 j.val⟩

theorem continuousWithinAt_historyReducedJacobianAlong_of_closedStart (hw : 0 < w)
    (Z₀ : H.historyLExpDomain hle T w p) (hstart : T - w ^ 2 = H.time first) :
    ContinuousWithinAt (H.historyReducedJacobianAlong Z₀) (Iic w) w := by
  have hlower := (isHistoryLGeodesicOn_historyLCurve Z₀).1
  have hT := stageDomain_last_of_historyLExpDomain Z₀
  have hTh : T ≤ H.horizon :=
    (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
  have htf : H.time first < H.stageEndTime first := by
    rw [← hstart]
    exact lt_stageEndTime_of_mem_stageDomain hlower (by nlinarith [pow_pos hw 2])
  obtain ⟨G, hG0, hGm⟩ := exists_incomingSlab_stageMetric first htf
  obtain ⟨V, hV, hZV, hVdom, s₀, hs₀w, hs₀, δ, hδ, β, hβ, hrep⟩ :=
    exists_family_of_closedStart hw hstart htf Z₀.2
  set S : Set ℝ := Ioc s₀ w ∩ {v | T - v ^ 2 < H.stageEndTime first} with hSdef
  have hSmem : ∀ v ∈ S, 0 < v ∧ v ≤ w ∧ T - v ^ 2 ∈ Ico (H.time first) (H.stageEndTime first) :=
    fun v hv => by
      have h0 : 0 < v := hs₀.trans hv.1.1
      have h2 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ h0.le hv.1.2 2
      exact ⟨h0, hv.1.2, by linarith, hv.2⟩
  have hSdom : ∀ v ∈ S, T - v ^ 2 ∈ H.stageDomain first := fun v hv => by
    obtain ⟨h0, hvw, h1, h2⟩ := hSmem v hv
    rcases h1.eq_or_lt with h | h
    · rw [← h]
      exact hstart ▸ hlower
    · exact H.mem_stageDomain_of_mem_Ioo ⟨h, h2⟩
  have hmet : ∀ v ∈ S, H.stageMetric first (T - v ^ 2) = G.flow.base.metric (T - v ^ 2) :=
    fun v hv => by
      obtain ⟨h0, hvw, h1, h2⟩ := hSmem v hv
      rcases h1.eq_or_lt with h | h
      · rw [← h, H.stageMetric_initial, hG0]
      · exact hGm _ ⟨h, h2⟩
  let src := H.historyLSourceDensity T p
  let Fc : ℝ → ℝ := fun v =>
    paramDensity (G.flow.base.metric (T - v ^ 2)) (fun Z => β (Z, v)) Z₀.1 / src *
      Real.exp (-(∑ j : H.StageInterval first last,
          ∫ r in H.regularizedStageStart T 0 j.val..H.regularizedStageEnd T v j.val,
            H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T w p Z₀ j) r) / (2 * v) -
        (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi))
  have hwS : w ∈ S := ⟨⟨hs₀w, le_rfl⟩, by change T - w ^ 2 < _; rw [hstart]; exact htf⟩
  have heq : ∀ v ∈ S, H.historyReducedJacobianAlong Z₀ v = Fc v := by
    intro v hv
    obtain ⟨h0, hvw, -, -⟩ := hSmem v hv
    have hd := hSdom v hv
    have hZv := mem_historyLExpDomain_of_le le_rfl hle h0 hvw hd Z₀.2
    rw [historyReducedJacobianAlong_eq Z₀ h0 hvw hle hd ⟨Z₀.1, hZv⟩ rfl]
    unfold historyReducedJacobian
    have hf : (fun Z => β (Z, v)) =ᶠ[𝓝 Z₀.1]
        H.historyLCurveMap hle T v p ⟨Z₀.1, hZv⟩ ⟨first, le_rfl, hle⟩ v := by
      filter_upwards [hV.mem_nhds hZV] with Z hZ
      have hZv' := mem_historyLExpDomain_of_le le_rfl hle h0 hvw hd (hVdom Z hZ)
      rw [historyLCurveMap_of_mem _ _ hZv', ← historyLExp_eq_historyLCurve,
        historyLExp_eq_historyLCurve_of_mem_historyLExpDomain le_rfl hle h0 hvw hd
          ⟨Z, hVdom Z hZ⟩]
      exact (hrep Z hZ v ⟨hv.1.1, hvw⟩).symm
    rw [← paramDensity_eq_historyLJacobianDensity_of_eventuallyEq ⟨first, le_rfl, hle⟩ v hf,
      hmet v hv, historyLAction_truncate_eq Z₀ h0 hvw hd]
  have hdens : ContinuousWithinAt (fun v =>
      paramDensity (G.flow.base.metric (T - v ^ 2)) (fun Z => β (Z, v)) Z₀.1) S w :=
    continuousWithinAt_paramDensity_of_metricSmoothUpTo G.smoothUpTo hV isOpen_Ioo hβ hZV
      (by fun_prop) ⟨hs₀w, by linarith⟩ (fun v hv => (hSmem v hv).2.2)
      (by rw [hstart]; exact ⟨le_rfl, htf⟩)
  have hact := (continuousWithinAt_sum_integral_historyLCurve hw Z₀).mono
    fun v hv => ⟨(hSmem v hv).1, (hSmem v hv).2.1, hSdom v hv⟩
  have hFc : ContinuousWithinAt Fc S w := by
    refine (hdens.div_const src).mul (Real.continuous_exp.continuousAt.comp_continuousWithinAt ?_)
    refine ((hact.neg.div (continuousWithinAt_const.mul continuousWithinAt_id)
      (mul_ne_zero two_ne_zero hw.ne')).sub (continuousWithinAt_const.mul ?_)).sub
        continuousWithinAt_const
    exact ((continuous_pow 2).continuousWithinAt).log (pow_ne_zero 2 hw.ne')
  have hAl : ContinuousWithinAt (H.historyReducedJacobianAlong Z₀) S w :=
    hFc.congr (fun v hv => heq v hv) (heq w hwS)
  refine hAl.mono_of_mem_nhdsWithin (inter_mem (Ioc_mem_nhdsLE hs₀w) ?_)
  refine nhdsWithin_le_nhds ((isOpen_lt (by fun_prop) continuous_const).mem_nhds ?_)
  change T - w ^ 2 < H.stageEndTime first
  rw [hstart]
  exact htf

variable {B₀ : ℝ}

theorem continuousWithinAt_historyReducedJacobianAlong_of_mem_historyMinDomain
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p) :
    ContinuousWithinAt (H.historyReducedJacobianAlong Z₀) (Iic w) w := by
  have hlower := (isHistoryLGeodesicOn_historyLCurve Z₀).1
  have hT := stageDomain_last_of_historyLExpDomain Z₀
  have hTh : T ≤ H.horizon :=
    (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
  rcases (H.time_le_of_mem_stageDomain hlower).eq_or_lt with h | h
  · exact continuousWithinAt_historyReducedJacobianAlong_of_closedStart hw Z₀ h.symm
  · exact continuousWithinAt_historyReducedJacobianAlong hfloor hw Z₀ hZmin
      ⟨h, lt_stageEndTime_of_mem_stageDomain hlower (by nlinarith [pow_pos hw 2])⟩

end ClosedStartContinuity

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
