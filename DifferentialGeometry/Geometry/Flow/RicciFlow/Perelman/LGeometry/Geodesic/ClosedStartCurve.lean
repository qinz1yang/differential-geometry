import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedStartPhase

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isLRegularizedGeodesicOn_lPhaseCurve (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x0 : M) {z : ℝ → E × E} {K : Set ℝ} (hK : IsOpen K)
    (hz : ∀ s ∈ K, HasDerivAt z (lPhaseField S T x0 s (z s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z s).1 ∈ interior (extChartAt I x0).target) :
    IsLRegularizedGeodesicOn S T (lPhaseCurve (I := I) x0 z) K := by
  have hq : ∀ s ∈ K, HasDerivAt (fun r : ℝ => (z r).1) (z s).2 s := fun s hs => by
    simpa [lPhaseField, Function.comp_def] using
      hasFDerivAt_fst.comp_hasDerivAt s (hz s hs).1
  have hvel : EqOn (fun s => lVelocity (I := I) (lPhaseCurve (I := I) x0 z) s)
      (lPhaseVelocity (I := I) x0 z) K := fun s hs =>
    lPhase_velocity (I := I) x0 z s (hq s hs) (hz s hs).2.2
  intro s hs
  obtain ⟨hzs, hreg, hint⟩ := hz s hs
  have hv : HasDerivAt (fun r : ℝ => (z r).2) (lPhaseField S T x0 s (z s)).2 s := by
    simpa [Function.comp_def] using hasFDerivAt_snd.comp_hasDerivAt s hzs
  have hfield : (fun r => lVelocity (I := I) (lPhaseCurve (I := I) x0 z) r) =ᶠ[𝓝 s]
      lPhaseVelocity (I := I) x0 z := hvel.eventuallyEq_of_mem (hK.mem_nhds hs)
  refine ⟨hreg, lPhaseCurve_mdiff (I := I) x0 z s (hq s hs).differentiableAt hint, ?_, ?_⟩
  · exact (lPhaseVelocity_diff (I := I) x0 z s (hq s hs).differentiableAt
      hv.differentiableAt hint).congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) (lPhaseCurve (I := I) x0 z) hfield)
  · calc
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (lPhaseCurve (I := I) x0 z)
          (fun r => lVelocity (I := I) (lPhaseCurve (I := I) x0 z) r) s =
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (lPhaseCurve (I := I) x0 z)
          (lPhaseVelocity (I := I) x0 z) s :=
        covDerivAlong_congr_of_eventuallyEq (I := I) _ _ hfield
      _ = lRegularizedAccel S T s (lPhaseCurve (I := I) x0 z s)
          (lPhaseVelocity (I := I) x0 z s) := lPhase_accel S T x0 z s hzs hint
      _ = _ := by rw [hfield.eq_of_nhds]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem contDiffAt_chartSeed {α : E × ℝ → M} {Z0 : E} {s0 : ℝ} (x0 : M)
    (hsrc : α (Z0, s0) ∈ (chartAt H x0).source)
    (hα : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ α (Z0, s0)) :
    ContDiffAt ℝ ∞ (fun Z : E => (extChartAt I x0 (α (Z, s0)),
      fderiv ℝ (fun s : ℝ => extChartAt I x0 (α (Z, s))) s0 (1 : ℝ))) Z0 := by
  let F : E × ℝ → E := fun p => extChartAt I x0 (α p)
  have hF : ContDiffAt ℝ ∞ F (Z0, s0) := by
    have h := (contMDiffAt_extChartAt' (I := I) hsrc).comp (Z0, s0) hα
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  have hincl : ContDiffAt ℝ ∞ (fun Z : E => (Z, s0)) Z0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hpos : ContDiffAt ℝ ∞ (fun Z : E => F (Z, s0)) Z0 := by
    simpa only [Function.comp_def] using hF.comp Z0 hincl
  exact hpos.prodMk ((hF.fderiv contDiffAt_const (by simp)).clm_apply contDiffAt_const)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem continuousAt_lVelocity_lift {c : ℝ → M} {s0 : ℝ}
    (hc : ∀ᶠ s in 𝓝 s0, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ c s) :
    ContinuousAt (fun s => (TotalSpace.mk' E (c s) (lVelocity (I := I) c s) :
      TangentBundle I M)) s0 := by
  have hc0 := hc.self_of_nhds
  have hsrc : ∀ᶠ s in 𝓝 s0, c s ∈ (chartAt H (c s0)).source :=
    hc0.continuousAt.preimage_mem_nhds
      ((chartAt H (c s0)).open_source.mem_nhds (mem_chart_source H (c s0)))
  let F : ℝ → E := fun s => extChartAt I (c s0) (c s)
  have hF : ContDiffAt ℝ ∞ F s0 :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (I := I) (mem_chart_source H (c s0))).comp s0 hc0)
  have hdF : DifferentiableAt ℝ (fun s => fderiv ℝ F s (1 : ℝ)) s0 :=
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hV : DifferentiableAt ℝ
      (chartRepAt (I := I) c (fun s => lVelocity (I := I) c s) s0) s0 := by
    refine hdF.congr_of_eventuallyEq ?_
    filter_upwards [hsrc, hc] with s hs hcs
    exact (lPhaseSeed_velocity (I := I) (c s0) (hcs.mdifferentiableAt (by simp)) hs).symm
  exact continuousWithinAt_univ _ _ |>.mp
    (sectionAlongCurve_continuousWithinAt_totalSpace (I := I) c _ (mem_univ s0)
      hc0.continuousAt.continuousWithinAt hV)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedFamily_of_start (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {a c : ℝ} (hac : a < c)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a c ×ˢ (univ : Set M)))
    {T v : ℝ} (hv : 0 < v) (hstart : T - v ^ 2 = a) (x : M) {Z0 : TangentSpace I x}
    (hdom : Ico 0 v ⊆ lRegularizedDomain S T x Z0) {ξ : TangentBundle I M}
    (hlim : Tendsto (fun s => (TotalSpace.mk' E (lRegularizedCurve S T x Z0 s)
      (lVelocity (I := I) (lRegularizedCurve S T x Z0) s) : TangentBundle I M))
      (𝓝[<] v) (𝓝 ξ)) :
    ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ β : E × ℝ → M,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ β (V ×ˢ Ioo (v - δ) (v + δ)) ∧
      ∀ Z ∈ V, Ico 0 v ⊆ lRegularizedDomain S T x Z ∧
        EqOn (fun s => β (Z, s)) (lRegularizedCurve S T x Z) (Ioo (v - δ) v) := by
  classical
  let γ : ℝ → M := lRegularizedCurve S T x Z0
  let x0 : M := ξ.proj
  let e := trivializationAt E (TangentSpace I) x0
  let z0 : E × E := (extChartAt I x0 x0, (e ξ).2)
  have hξ : ξ ∈ e.source := by
    rw [e.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' x0
  have hz0 : z0.1 ∈ interior (extChartAt I x0).target := by
    rw [(isOpen_extChartAt_target (I := I) x0).interior_eq]
    exact mem_extChartAt_target (I := I) x0
  let st : ℝ → E × E := fun s =>
    (extChartAt I x0 (γ s), trivToE (I := I) x0 (γ s) (lVelocity (I := I) γ s))
  have hlim' := (e.tendsto_nhds_iff hξ).mp hlim
  have hproj : Tendsto γ (𝓝[<] v) (𝓝 x0) := hlim'.1
  have hbase : ∀ᶠ s in 𝓝[<] v, γ s ∈ (chartAt H x0).source :=
    hproj.eventually ((chartAt H x0).open_source.mem_nhds (mem_chart_source H x0))
  have hst : Tendsto st (𝓝[<] v) (𝓝 z0) := by
    refine ((continuousAt_extChartAt (I := I) x0).tendsto.comp hproj).prodMk_nhds ?_
    refine hlim'.2.congr' ?_
    filter_upwards [hbase] with s hs
    have hsb : γ s ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hs
    exact (e.continuousLinearMapAt_apply_of_mem (R := ℝ) hsb _).symm
  obtain ⟨ε, hε, W, hWo, hvW, -, Ψ, hΨ0, hΨsm, hΨd⟩ :=
    exists_lPhaseFlow_of_start S hac hmetric hv hstart x0 z0 hz0
  have hlt : max (v - ε / 2) (v / 2) < v := max_lt (by linarith) (by linarith)
  have hpair : Tendsto (fun s => (s, st s)) (𝓝[<] v) (𝓝 (v, z0)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).prodMk_nhds hst
  obtain ⟨s₁, hW1, hsrc1, hs₁⟩ := ((hpair.eventually (hWo.mem_nhds hvW)).and
    (hbase.and (Ioo_mem_nhdsLT hlt))).exists
  have hmax1 := le_max_left (v - ε / 2) (v / 2)
  have hmax2 := le_max_right (v - ε / 2) (v / 2)
  have hs₁pos : 0 < s₁ := by linarith [hs₁.1]
  have hs₁v : s₁ < v := hs₁.2
  have hregs : ∀ s, 0 ≤ s → s < v → T - s ^ 2 ∈ D.regular := fun s h0 h1 =>
    lRegularizedDomain_regularity S T x Z0 (hdom ⟨h0, h1⟩)
  obtain ⟨J, hJo, hJc, h0J, hs₁J, hch⟩ :=
    lRegularizedChosen_spec S T x Z0 (hdom ⟨hs₁pos.le, hs₁v⟩)
  obtain ⟨V, hVo, hZ0V, K, hKo, hKc, h0K, hs₁K, α, hα, hcurves⟩ :=
    lRegularizedFamily_extend S hS T hJo hJc h0J hs₁J hch
  have hγα : EqOn γ (fun s => α (Z0, s)) K :=
    lRegularizedCurve_eqOn S hS T hKo hKc h0K (hcurves Z0 hZ0V)
  have hαs₁ : α (Z0, s₁) = γ s₁ := (hγα hs₁K).symm
  have hsrcα : α (Z0, s₁) ∈ (chartAt H x0).source := hαs₁ ▸ hsrc1
  let sd : E → E × E := fun Z => (extChartAt I x0 (α (Z, s₁)),
    fderiv ℝ (fun s : ℝ => extChartAt I x0 (α (Z, s))) s₁ (1 : ℝ))
  have hseed0 : sd Z0 = st s₁ := by
    have hgerm : (fun s => α (Z0, s)) =ᶠ[𝓝 s₁] γ :=
      hγα.symm.eventuallyEq_of_mem (hKo.mem_nhds hs₁K)
    have hvel : lVelocity (I := I) (fun s => α (Z0, s)) s₁ = lVelocity (I := I) γ s₁ := by
      simp only [lVelocity]
      rw [hgerm.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)]
      rfl
    have h := lPhaseSeed_velocity (I := I) x0 ((hcurves Z0 hZ0V).2.2 s₁ hs₁K).2.1 hsrcα
    simp only [sd, st, h, hvel]
    rw [hαs₁]
  let U : Set (E × E) := {z | (s₁, z) ∈ W}
  have hUo : IsOpen U := hWo.preimage (continuous_const.prodMk continuous_id)
  have hseedU : sd Z0 ∈ U := by
    change (s₁, sd Z0) ∈ W
    rw [hseed0]
    exact hW1
  let L : Set ℝ := Ioo (s₁ - (v - s₁)) (s₁ + (v - s₁))
  have hwin : ∀ s ∈ L, s ∈ Ioc (v - ε) v ∧ 0 < s ∧ s < v := fun s hs =>
    ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, by linarith [hs.1], by linarith [hs.2]⟩
  have hs₁L : s₁ ∈ L := ⟨by linarith, by linarith⟩
  let Φ : (E × E) × ℝ → E × E := fun q => Ψ ((s₁, q.1), q.2)
  have hlift : ContDiff ℝ ∞ (fun q : (E × E) × ℝ => (((s₁, q.1) : ℝ × (E × E)), q.2)) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  have hΦsm : ContDiffOn ℝ ∞ Φ (U ×ˢ L) :=
    hΨsm.comp hlift.contDiffOn fun q hq =>
      ⟨hq.1, ⟨(hwin q.2 hq.2).1.1, by linarith [(hwin q.2 hq.2).1.2]⟩⟩
  obtain ⟨W₁, hW₁o, hZ0W₁, hW₁V, β₁, -, hβ₁⟩ :=
    lRegularizedFamily_step_of S hS T x x0 hVo hZ0V hKo hKc h0K hs₁K hα hcurves hsrcα
      (v - s₁) (by linarith) hUo hseedU Φ (fun z hz => hΨ0 (s₁, z) hz) hΦsm
      (fun z hz s hs => (hΨd (s₁, z) hz s (hwin s hs).1).1)
      (fun q hq => ⟨hregs q.2 (hwin q.2 hq.2).2.1.le (hwin q.2 hq.2).2.2,
        (hΨd (s₁, q.1) hq.1 q.2 (hwin q.2 hq.2).1).2.2⟩)
  let Kf : Set ℝ := K ∪ L
  have hKfo : IsOpen Kf := hKo.union isOpen_Ioo
  have hKfc : IsPreconnected Kf := hKc.union s₁ hs₁K hs₁L isPreconnected_Ioo
  have h0Kf : (0 : ℝ) ∈ Kf := Or.inl h0K
  have hs₁Kf : s₁ ∈ Kf := Or.inl hs₁K
  have hαAt : ∀ Z ∈ V, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ α (Z, s₁) := fun Z hZ =>
    (hα (Z, s₁) ⟨hZ, hs₁K⟩).contMDiffAt ((hVo.prod hKo).mem_nhds ⟨hZ, hs₁K⟩)
  have hposC : ContinuousOn (fun Z : E => α (Z, s₁)) V := fun Z hZ =>
    ((hαAt Z hZ).comp Z (contMDiffAt_id.prodMk contMDiffAt_const)).continuousAt
      |>.continuousWithinAt
  let V₀ : Set E := V ∩ (fun Z : E => α (Z, s₁)) ⁻¹' (chartAt H x0).source
  have hV₀o : IsOpen V₀ := hposC.isOpen_inter_preimage hVo (chartAt H x0).open_source
  have hsd : ContDiffOn ℝ ∞ sd V₀ := fun Z hZ =>
    (contDiffAt_chartSeed x0 hZ.2 (hαAt Z hZ.1)).contDiffWithinAt
  let V₁ : Set E := (V₀ ∩ sd ⁻¹' U) ∩ W₁
  have hV₁o : IsOpen V₁ := (hsd.continuousOn.isOpen_inter_preimage hV₀o hUo).inter hW₁o
  have hZ0V₁ : Z0 ∈ V₁ := ⟨⟨⟨hZ0V, hsrcα⟩, hseedU⟩, hZ0W₁⟩
  let ph : E × ℝ → E × E := fun p => Ψ ((s₁, sd p.1), p.2)
  have hph : ContDiffOn ℝ ∞ ph (V₁ ×ˢ Ioo (v - ε) (v + ε)) := by
    have hin : ContDiffOn ℝ ∞ (fun p : E × ℝ => (((s₁, sd p.1) : ℝ × (E × E)), p.2))
        (V₁ ×ˢ Ioo (v - ε) (v + ε)) :=
      ((contDiffOn_const.prodMk (hsd.comp contDiffOn_fst fun p hp => hp.1.1.1)).prodMk
        contDiffOn_snd)
    exact hΨsm.comp hin fun p hp => ⟨hp.1.1.2, hp.2⟩
  let η : E × ℝ → M := fun p => (extChartAt I x0).symm (ph p).1
  have hint0 : (ph (Z0, v)).1 ∈ interior (extChartAt I x0).target :=
    (hΨd (s₁, sd Z0) hseedU v ⟨by linarith, le_rfl⟩).2.2
  have hphC : ContinuousAt ph (Z0, v) := hph.continuousOn.continuousAt
    ((hV₁o.prod isOpen_Ioo).mem_nhds ⟨hZ0V₁, ⟨by linarith, by linarith⟩⟩)
  have hN : {p : E × ℝ | (ph p).1 ∈ interior (extChartAt I x0).target} ∩
      (V₁ ×ˢ Ioo (v - ε) (v + ε)) ∈ 𝓝 (Z0, v) :=
    inter_mem ((continuousAt_fst.comp hphC).preimage_mem_nhds
      (isOpen_interior.mem_nhds hint0))
      ((hV₁o.prod isOpen_Ioo).mem_nhds ⟨hZ0V₁, ⟨by linarith, by linarith⟩⟩)
  obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨V₂, hV₂u, hV₂o, hZ0V₂⟩ := mem_nhds_iff.mp hu
  obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.mp ht
  let δ : ℝ := min δ' (v - s₁)
  have hδ : 0 < δ := lt_min hδ' (by linarith)
  have hδs₁ : δ ≤ v - s₁ := min_le_right _ _
  have hbox : ∀ p ∈ V₂ ×ˢ Ioo (v - δ) (v + δ),
      (ph p).1 ∈ interior (extChartAt I x0).target ∧ p ∈ V₁ ×ˢ Ioo (v - ε) (v + ε) := by
    rintro ⟨Z, s⟩ ⟨hZ, hs⟩
    refine hut ⟨hV₂u hZ, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have := min_le_left δ' (v - s₁)
    constructor <;> linarith [hs.1, hs.2]
  refine ⟨V₂, hV₂o, hZ0V₂, δ, hδ, η, ?_, ?_⟩
  · have hphMD : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ (fun p => (ph p).1)
        (V₂ ×ˢ Ioo (v - δ) (v + δ)) :=
      (hph.mono fun p hp => (hbox p hp).2).fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphMD
    refine (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x0).comp hphMD ?_
    intro p hp
    exact (interior_subset (hbox p hp).1 : (ph p).1 ∈ (extChartAt I x0).target)
  intro Z hZ
  have hZ₁ : Z ∈ V₁ := (hbox (Z, v) ⟨hZ, ⟨by linarith, by linarith⟩⟩).2.1
  have hcurveZ := hβ₁ Z hZ₁.2
  refine ⟨fun s hs => ⟨fun r => β₁ (Z, r), Kf, hKfo, hKfc, h0Kf, ?_, hcurveZ⟩, ?_⟩
  · by_cases h : s ≤ s₁
    · exact Or.inl ((isPreconnected_iff_ordConnected.mp hKc).out h0K hs₁K ⟨hs.1, h⟩)
    · exact Or.inr ⟨by linarith [not_le.mp h], by linarith [hs.2]⟩
  let z : ℝ → E × E := fun s => ph (Z, s)
  have hsdU : sd Z ∈ U := hZ₁.1.2
  have hηreg : IsLRegularizedGeodesicOn S T (lPhaseCurve (I := I) x0 z) L :=
    isLRegularizedGeodesicOn_lPhaseCurve S T x0 isOpen_Ioo fun s hs =>
      ⟨(hΨd (s₁, sd Z) hsdU s (hwin s hs).1).1,
        hregs s (hwin s hs).2.1.le (hwin s hs).2.2,
        (hΨd (s₁, sd Z) hsdU s (hwin s hs).1).2.2⟩
  have hsrcZ : α (Z, s₁) ∈ (chartAt H x0).source := hZ₁.1.1.2
  have hzs₁ : z s₁ = sd Z := hΨ0 (s₁, sd Z) hsdU
  have hηs₁ : lPhaseCurve (I := I) x0 z s₁ = α (Z, s₁) := by
    change (extChartAt I x0).symm (z s₁).1 = α (Z, s₁)
    rw [hzs₁]
    apply (extChartAt I x0).left_inv
    rw [extChartAt_source]
    exact hsrcZ
  have hαβ : EqOn (fun s => α (Z, s)) (fun s => β₁ (Z, s)) (K ∩ Kf) :=
    lRegularizedCurve_eqOn_of_initial_data S hS T hKo hKc h0K hKfo hKfc h0Kf
      (hcurves Z hZ₁.1.1.1) hcurveZ
  have hαβg : (fun s => α (Z, s)) =ᶠ[𝓝 s₁] fun s => β₁ (Z, s) :=
    hαβ.eventuallyEq_of_mem ((hKo.inter hKfo).mem_nhds ⟨hs₁K, hs₁Kf⟩)
  have hvelαβ : lVelocity (I := I) (fun s => β₁ (Z, s)) s₁ =
      lVelocity (I := I) (fun s => α (Z, s)) s₁ := by
    simp only [lVelocity]
    rw [hαβg.symm.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)]
    rfl
  have hvelη : lVelocity (I := I) (lPhaseCurve (I := I) x0 z) s₁ =
      lVelocity (I := I) (fun s => α (Z, s)) s₁ := by
    have hq : HasDerivAt (fun r : ℝ => (z r).1) (z s₁).2 s₁ := by
      simpa [lPhaseField, Function.comp_def] using hasFDerivAt_fst.comp_hasDerivAt s₁
        (hΨd (s₁, sd Z) hsdU s₁ (hwin s₁ hs₁L).1).1
    rw [lPhase_velocity (I := I) x0 z s₁ hq (hΨd (s₁, sd Z) hsdU s₁ (hwin s₁ hs₁L).1).2.2]
    have hbaseZ : α (Z, s₁) ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrcZ
    have hseedZ : (sd Z).2 = trivToE (I := I) x0 (α (Z, s₁))
        (lVelocity (I := I) (fun s => α (Z, s)) s₁) :=
      lPhaseSeed_velocity (I := I) x0 ((hcurves Z hZ₁.1.1.1).2.2 s₁ hs₁K).2.1 hsrcZ
    change trivFromE (I := I) x0 (lPhaseCurve (I := I) x0 z s₁) (z s₁).2 = _
    rw [hηs₁, hzs₁, hseedZ]
    exact trivFromE_trivToE (I := I) x0 hbaseZ _
  have hβη : EqOn (fun s => β₁ (Z, s)) (lPhaseCurve (I := I) x0 z) (Kf ∩ L) :=
    lRegularizedSolution_eqOn S hS T hKfo hKfc hs₁Kf isOpen_Ioo isPreconnected_Ioo hs₁L
      hcurveZ.2.2 hηreg (by rw [hηs₁]; exact (hαβ ⟨hs₁K, hs₁Kf⟩).symm)
      (by rw [hvelαβ, hvelη])
  intro s hs
  have hsL : s ∈ L := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsKf : s ∈ Kf := Or.inr hsL
  calc η (Z, s) = β₁ (Z, s) := (hβη ⟨hsKf, hsL⟩).symm
    _ = lRegularizedCurve S T x Z s :=
      (lRegularizedCurve_eqOn S hS T hKfo hKfc h0Kf hcurveZ hsKf).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem tendsto_lVelocity_lift_of_family {c : ℝ → M} {β : ℝ → M} {v δ : ℝ} (hδ : 0 < δ)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ β (Ioo (v - δ) (v + δ)))
    (heq : EqOn β c (Ioo (v - δ) v)) :
    Tendsto (fun s => (TotalSpace.mk' E (c s) (lVelocity (I := I) c s) : TangentBundle I M))
      (𝓝[<] v) (𝓝 (TotalSpace.mk' E (β v) (lVelocity (I := I) β v))) := by
  have hvI : v ∈ Ioo (v - δ) (v + δ) := ⟨by linarith, by linarith⟩
  have hcont := continuousAt_lVelocity_lift (I := I) (c := β) (s0 := v)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hvI] with s hs
      exact (hβ s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs))
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show v - δ < v by linarith)] with s hs
  have hgerm : β =ᶠ[𝓝 s] c := heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
  have hvel : lVelocity (I := I) β s = lVelocity (I := I) c s := by
    simp only [lVelocity]
    rw [hgerm.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)]
    rfl
  change TotalSpace.mk' E (β s) (lVelocity (I := I) β s) =
    TotalSpace.mk' E (c s) (lVelocity (I := I) c s)
  rw [hvel, heq hs]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isOpen_setOf_tendsto_lRegularizedCurve_of_start (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {a c : ℝ} (hac : a < c)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a c ×ˢ (univ : Set M)))
    {T v : ℝ} (hv : 0 < v) (hstart : T - v ^ 2 = a) (x : M) :
    IsOpen {Z : E | Ico 0 v ⊆ lRegularizedDomain S T x Z ∧ ∃ ξ : TangentBundle I M,
      Tendsto (fun s => (TotalSpace.mk' E (lRegularizedCurve S T x Z s)
        (lVelocity (I := I) (lRegularizedCurve S T x Z) s) : TangentBundle I M))
        (𝓝[<] v) (𝓝 ξ)} := by
  rw [isOpen_iff_mem_nhds]
  rintro Z0 ⟨hdom, ξ, hlim⟩
  obtain ⟨V, hVo, hZ0V, δ, hδ, β, hβ, hfam⟩ :=
    exists_lRegularizedFamily_of_start S hS hac hmetric hv hstart x hdom hlim
  refine mem_of_superset (hVo.mem_nhds hZ0V) fun Z hZ => ⟨(hfam Z hZ).1, _,
    tendsto_lVelocity_lift_of_family hδ ?_ (hfam Z hZ).2⟩
  have hsec : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (Z, s)) :=
    contMDiff_const.prodMk contMDiff_id
  exact hβ.comp hsec.contMDiffOn fun s hs => ⟨hZ, hs⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
