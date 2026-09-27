import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessPerturbation

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance endpointPerturbationFlowC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem WindowedModelWitness.eventually_strict_of_tendsto_flows_endpoint
    {S₀ : SolutionOn (I := I3) (M := M) D} (hS₀ : IsSolutionOn S₀)
    {S : ℕ → SolutionOn (I := I3) (M := M) D} (hS : ∀ n, IsSolutionOn (S n))
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S₀ x t)
    {t₀ : ℝ} (ha : t₀ < t - (eps * S₀.scalar t x)⁻¹) (hslab : Icc t₀ t ⊆ D.carrier)
    (hreg : Ioo t₀ t ⊆ D.regular)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps)
    (R : SmoothRiemannianMetric I3 M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      ∀ τ ∈ Icc t₀ t, metricDerivNormSupOn K p ((S n).base.metric τ) (S₀.base.metric τ) R < e)
    {x' : ℕ → M} (hx' : Tendsto x' atTop (𝓝 x))
    (hscalar : Tendsto (fun n => (S n).scalar t (x' n)) atTop (𝓝 (S₀.scalar t x))) :
    ∀ᶠ n in atTop, ∃ W' : WindowedModelWitness eps kappa (S n) (x' n) t,
      (∀ (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M),
        (∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
          PreservesTangentOrientationAt oN o W.embedding y hf) →
        ∃ oN' : TangentOrientationSection W'.model.M, ∀ y ∈ W'.embedding.source,
          ∃ hf : Function.Bijective (mfderiv I3 I3 W'.embedding y),
            PreservesTangentOrientationAt oN' o W'.embedding y hf) ∧
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
            (modelRadius eps),
          tensor02CovDerivNormWith a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨c, hac, hclo⟩ := exists_between ha
  have hback : t - (eps * S₀.scalar t x)⁻¹ < t :=
    sub_lt_self _ (inv_pos.mpr (mul_pos W.eps_pos W.scalar_pos))
  have hcb : c < t := hclo.trans hback
  have hdepth : 0 < modelDepth eps := inv_pos.mpr W.eps_pos
  have hR : 0 < modelRadius eps := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  let L := Icc (-2 * modelDepth eps - 1) 0
  let K := riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
    (modelRadius eps + 1)
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hK : IsCompact K := RiemannianMetricComplete.closedEBall_isCompact hcomplete _ _
  obtain ⟨chi, hchi, _hcompact, hchiOne, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I3) hK W.embedding.open_source
      W.buffered_ball
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hchiOne
  let U : TopologicalSpace.Opens W.model.M :=
    ⟨V ∩ W.embedding.source, hV.inter W.embedding.open_source⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hKU : K ⊆ U := fun y hy => ⟨hKV hy, W.buffered_ball hy⟩
  have hU : (U : Set W.model.M) ⊆ W.embedding.source := fun _ hy => hy.2
  have hOne (y : W.model.M) (hy : y ∈ U) : chi y = 1 := hVone hy.1
  obtain ⟨A, hA₀', _hAout, hA⟩ := exists_closedWindow_pullback_metric_time_tower S₀ hS₀
    hac hcb hslab hreg W.embedding chi hchi hsupp
  choose A' hA'₀' _hA'out hA' using fun n => exists_closedWindow_pullback_metric_time_tower
    (S n) (hS n) hac hcb hslab hreg W.embedding chi hchi hsupp
  have hA₀ (s : ℝ) (y : W.model.M) (hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      A 0 s y v = (S₀.base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)) := by
    simpa only [hOne y hy, one_mul] using hA₀' s y (hU hy) v
  have hA'₀ (n : ℕ) (s : ℝ) (y : W.model.M) (hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      A' n 0 s y v = ((S n).base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)) := by
    simpa only [hOne y hy, one_mul] using hA'₀' n s y (hU hy) v
  have hmodelSlab : Icc (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.carrier :=
    fun _ hr => hr.2
  have hmodelReg : Ioo (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.regular :=
    fun _ hr => hr.2
  obtain ⟨B, hB₀, hBd⟩ := exists_closedWindow_metric_time_fields W.model.S W.model.isSolution
    (a := -2 * modelDepth eps - 2) (c := -2 * modelDepth eps - 1) (b := 0)
    (by linarith) (by linarith) hmodelSlab hmodelReg
  have hB (q : ℕ) (s : ℝ) (hs : s ∈ L) (y : W.model.M) :
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) L s := (hBd q s hs y).2
  have hp : W.model.basepoint ∈ W.embedding.source := by
    apply W.buffered_ball
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hx : x ∈ W.embedding.target := by
    simpa only [W.base_map] using W.embedding.map_source' hp
  have hinv : W.embedding.symm x = W.model.basepoint :=
    (congrArg (W.embedding.symm : M → W.model.M) W.base_map.symm).trans
      (W.embedding.left_inv' hp)
  have hcone : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hmodelSub : Icc (-modelDepth eps) 0 ⊆ L := fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hsourceMap₀ : MapsTo (parabolicTime t (S₀.scalar t x)) (Icc (-modelDepth eps) 0)
      (Icc c t) := by
    intro s hs
    have hQ₀ := W.scalar_pos
    have hl : t - (eps * S₀.scalar t x)⁻¹ ≤ parabolicTime t (S₀.scalar t x) s := by
      simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg,
        add_comm] using add_le_add_left (div_le_div_of_nonneg_right hs.1 hQ₀.le) t
    have hu : parabolicTime t (S₀.scalar t x) s ≤ t :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQ₀.le)
    exact ⟨hclo.le.trans hl, hu⟩
  have hsmallU : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ U :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans hKU
  have hOld := W.strict_original_error_of_time_towers A B U hsmallU
    (fun s y hy v => hA₀ s y hy v) hB₀ (Icc c t) L (fun q s hs y => hA q s hs y) hB
    hsourceMap₀ hmodelSub hstrict
  have hAreg := partial_pullback_time_tower_contDiffOn_closed S₀ hS₀ hac hcb hslab hreg
    W.embedding U hU A (fun s y hy v => hA₀ s y hy v) (fun q s hs y _hy => hA q s hs y)
  let F := PartialDiffeomorph.refl (I := I3) W.model.M
  have hBzero (s : ℝ) (y : W.model.M) (_hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      B 0 s y v = (W.model.S.base.metric s).inner (F y)
        (mfderiv I3 I3 F y (v 0)) (mfderiv I3 I3 F y (v 1)) := by
    change B 0 s y v = (W.model.S.base.metric s).inner y
      (mfderiv I3 I3 (id : W.model.M → W.model.M) y (v 0))
      (mfderiv I3 I3 (id : W.model.M → W.model.M) y (v 1))
    simp only [hB₀, metricTensorField_apply, mfderiv_id, ContinuousLinearMap.id_apply]
  have hBreg := partial_pullback_time_tower_contDiffOn_closed W.model.S W.model.isSolution
    (a := -2 * modelDepth eps - 2) (c := -2 * modelDepth eps - 1) (b := 0)
    (by linarith) (by linarith) hmodelSlab hmodelReg F U (Set.subset_univ _) B hBzero
    (fun q s hs y _hy => hB q s hs y)
  have hscaleOne (g : SmoothRiemannianMetric I3 W.model.M) :
      scaleMetric 1 zero_lt_one g = g :=
    SmoothRiemannianMetric.ext_inner (fun y v w => by simp only [scaleMetric_inner, one_mul])
  let center (n : ℕ) := W.embedding.symm (x' n)
  let Q (n : ℕ) := (S n).scalar t (x' n)
  let C (n : ℕ) := W.model.S.scalar 0 (center n)
  have hcenterLim : Tendsto center atTop (𝓝 W.model.basepoint) := by
    have hh := (W.embedding.symm.contMDiffOn_toFun.continuousOn.continuousAt
      (W.embedding.open_target.mem_nhds hx)).tendsto.comp hx'
    rw [hinv] at hh
    exact hh
  have hscalarModel : ContinuousAt (fun z => W.model.S.scalar 0 z) W.model.basepoint :=
    (metricScalar_smooth (W.model.S.base.metric 0)).continuous.continuousAt
  have hClim : Tendsto C atTop (𝓝 (1 : ℝ)) := by
    have hh := hscalarModel.tendsto.comp hcenterLim
    rw [hcone] at hh
    exact hh
  have hLowLim : Tendsto (fun n => t - (eps * Q n)⁻¹) atTop
      (𝓝 (t - (eps * S₀.scalar t x)⁻¹)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.mul hscalar).inv₀
      (mul_ne_zero W.eps_pos.ne' W.scalar_pos.ne'))
  have hBuff := eventually_scaled_closedBall_subset (W.model.S.base.metric 0) hcomplete
    W.model.basepoint (show 0 ≤ modelRadius eps + 1 by linarith) W.embedding.open_source
    W.buffered_ball (fun z => W.model.S.scalar 0 z) hscalarModel hcone
  have hOldSmall : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆
      riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps + 1) := by
    intro y hy
    have hyR : riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤
        ENNReal.ofReal (modelRadius eps) := hy
    exact hyR.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  have hCmp := eventually_scaled_closedBall_subset (W.model.S.base.metric 0) hcomplete
    W.model.basepoint hR.le (isOpen_lt (continuous_riemannianEDist (W.model.S.base.metric 0)
      W.model.basepoint) continuous_const) hOldSmall (fun z => W.model.S.scalar 0 z)
      hscalarModel hcone
  let Valid (n : ℕ) : Prop := x' n ∈ W.embedding.target ∧ ∃ hc : 0 < C n, 0 < Q n ∧
    riemannianClosedBallOf (scaleMetric (C n) hc (W.model.S.base.metric 0)) (center n)
      (modelRadius eps + 1) ⊆ W.embedding.source ∧
    riemannianClosedBallOf (scaleMetric (C n) hc (W.model.S.base.metric 0)) (center n)
      (modelRadius eps) ⊆ K ∧
    Icc (t - (eps * Q n)⁻¹) t ⊆ D.carrier ∧
    MapsTo (parabolicTime t (Q n)) (Icc (-modelDepth eps) 0) (Icc c t) ∧
    MapsTo (parabolicTime 0 (C n)) (Icc (-modelDepth eps) 0) L
  have hvalid : ∀ᶠ n in atTop, Valid n := by
    filter_upwards [hx'.eventually (W.embedding.open_target.mem_nhds hx),
      hscalar.eventually (Ioi_mem_nhds W.scalar_pos), hLowLim.eventually (Ioi_mem_nhds hclo),
      hClim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
      hcenterLim.eventually hBuff, hcenterLim.eventually hCmp] with n hxt hQpos hlo hcHalf hb hcb'
    obtain ⟨hc, hbuff⟩ := hb
    obtain ⟨_hc', hcmp⟩ := hcb'
    refine ⟨hxt, hc, hQpos, hbuff, ?_, ?_, ?_, ?_⟩
    · intro y hy
      change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤
        ENNReal.ofReal (modelRadius eps + 1)
      exact (hcmp hy).le
    · intro r hr
      exact hslab ⟨((hac.trans hlo).trans_le hr.1).le, hr.2⟩
    · intro s hs
      have hl : t - (eps * Q n)⁻¹ ≤ parabolicTime t (Q n) s := by
        simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg,
          add_comm] using add_le_add_left (div_le_div_of_nonneg_right hs.1 hQpos.le) t
      have hu : parabolicTime t (Q n) s ≤ t :=
        add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQpos.le)
      exact ⟨hlo.le.trans hl, hu⟩
    · intro s hs
      simp only [parabolicTime, zero_add]
      constructor
      · apply (le_div_iff₀ hc).mpr
        have hm := mul_le_mul_of_nonneg_left hcHalf.le
          (show 0 ≤ 2 * modelDepth eps + 1 by linarith)
        nlinarith [hs.1]
      · exact div_nonpos_of_nonpos_of_nonneg hs.2 hc.le
  let Good (n : ℕ) : Prop := ∃ W' : WindowedModelWitness eps kappa (S n) (x' n) t,
      (∀ (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M),
        (∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
          PreservesTangentOrientationAt oN o W.embedding y hf) →
        ∃ oN' : TangentOrientationSection W'.model.M, ∀ y ∈ W'.embedding.source,
          ∃ hf : Function.Bijective (mfderiv I3 I3 W'.embedding y),
            PreservesTangentOrientationAt oN' o W'.embedding y hf) ∧
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
            (modelRadius eps),
          tensor02CovDerivNormWith a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps
  change ∀ᶠ n in atTop, Good n
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ Good n := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_of_frequently_atTop (hfreq.and_eventually hvalid)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  choose hxt hc hQ hbuff hcmp hwin hsrc hmod using fun k => (hbad k).2
  have hconvφ : ∀ K' : Set M, IsCompact K' → ∀ r : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N₀ : ℕ, ∀ k ≥ N₀, ∀ τ ∈ Icc c t,
        metricDerivNormSupOn K' r ((S (φ k)).base.metric τ) (S₀.base.metric τ) R < e := by
    intro K' hK' r e he
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hconv K' hK' r e he)
    exact ⟨N₀, fun k hk τ hτ =>
      hN₀ (φ k) (hk.trans (hφ.id_le k)) τ ⟨hac.le.trans hτ.1, hτ.2⟩⟩
  have hQφ : Tendsto (fun k => Q (φ k)) atTop (𝓝 (S₀.scalar t x)) := hscalar.comp hφtop
  have hCφ : Tendsto (fun k => C (φ k)) atTop (𝓝 1) := hClim.comp hφtop
  have hpair (i j : ℕ) (hij : i + 2 * j ≤ modelOrder eps) :
      ∀ᶠ k in atTop, ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (scaleMetric (C (φ k)) (hc k) (W.model.S.base.metric 0))
            (center (φ k)) (modelRadius eps),
          tensor02CovDerivNormWith i
            (rescaledTensorTimeTower (A' (φ k)) t (Q (φ k)) j s -
              rescaledTensorTimeTower B 0 (C (φ k)) j s)
            (rescaledMetric W.model.S 0 (C (φ k)) (hc k) s)
            (rescaledMetric W.model.S 0 (C (φ k)) (hc k) s) y < eps := by
    have hAlpha : Tendsto (fun k => Q (φ k) * (Q (φ k))⁻¹ ^ j) atTop
        (𝓝 (S₀.scalar t x * (S₀.scalar t x)⁻¹ ^ j)) :=
      hQφ.mul ((hQφ.inv₀ W.scalar_pos.ne').pow j)
    have hBeta : Tendsto (fun k => C (φ k) * (C (φ k))⁻¹ ^ j) atTop (𝓝 (1 : ℝ)) := by
      simpa only [inv_one, one_pow, one_mul] using hCφ.mul ((hCφ.inv₀ one_ne_zero).pow j)
    have hh := eventually_strict_weighted_error_norm_on_scaled_ball_of_uniform_perturbation
      (fun s => W.model.S.base.metric s) (A j) (B j) (fun k => A' (φ k) j)
      W.model.basepoint (modelRadius eps) hK
      (fun y hy => by
        obtain ⟨V₁, hV₁, hp₁, ht₁, hAc⟩ := hAreg (⟨y, hKU hy⟩ : U)
        obtain ⟨V₂, hV₂, hp₂, _ht₂, hBc⟩ := hBreg (⟨y, hKU hy⟩ : U)
        obtain ⟨V₃, hV₃, hp₃, _ht₃, hgc⟩ := solution_chartGram_contDiffOn_closed
          W.model.S W.model.isSolution (a := -2 * modelDepth eps - 2)
          (c := -2 * modelDepth eps - 1) (b := 0) (by linarith) (by linarith) hmodelSlab
          hmodelReg y
        refine ⟨V₁ ∩ (V₂ ∩ V₃), hV₁.inter (hV₂.inter hV₃), ⟨hp₁, hp₂, hp₃⟩,
          (fun z hz => ht₁ hz.1), ?_, ?_, ?_⟩
        · intro r s
          exact (hgc r s).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2.2))
        · intro slots
          exact (hAc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.1))
        · intro slots
          exact (hBc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2.1)))
      (fun y hy => uniform_pullback_time_tower_chart_jets_of_metric_convergence
        (fun k => S (φ k)) (fun k => hS (φ k)) S₀ hS₀ hac hcb hslab hreg W.embedding U hU
        A (fun k => A' (φ k)) (fun s y hy v => hA₀ s y hy v) (fun q s hs y _hy => hA q s hs y)
        (fun k s y hy v => hA'₀ (φ k) s y hy v) (fun k q s hs y _hy => hA' (φ k) q s hs y)
        R hconvφ y (hKU hy) j)
      (fun k => center (φ k)) (hcenterLim.comp hφtop) (fun _ => t) (fun k => Q (φ k))
      (fun k => C (φ k)) (fun k => Q (φ k) * (Q (φ k))⁻¹ ^ j)
      (fun k => C (φ k) * (C (φ k))⁻¹ ^ j)
      W.scalar_pos hc zero_lt_one tendsto_const_nhds hQφ hCφ hAlpha hBeta i hcmp
      (fun k s hs => hsrc k hs)
      (fun k s hs => by simpa only [parabolicTime, zero_add] using hmod k hs)
      (fun s hs => hsourceMap₀ hs)
      (fun s hs => by simpa only [div_one] using hmodelSub hs)
      (fun s hs y hy => by
        have hy' : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
            (modelRadius eps) := by
          simpa only [hscaleOne] using hy
        simpa only [div_one, one_smul, hscaleOne] using hOld i j hij s hs y hy')
    simpa only [rescaledTensorTimeTower, rescaledMetric, parabolicTime, zero_add] using hh
  have hfinite : {ij : ℕ × ℕ | ij.1 + 2 * ij.2 ≤ modelOrder eps}.Finite := by
    apply ((Finset.range (modelOrder eps + 1)).product
      (Finset.range (modelOrder eps + 1))).finite_toSet.subset
    intro ij hij
    change ij.1 + 2 * ij.2 ≤ modelOrder eps at hij
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩
  have hall := (Filter.eventually_all_finite hfinite).mpr (fun ij hij => hpair ij.1 ij.2 hij)
  obtain ⟨k, hk⟩ := hall.exists
  have hright : W.embedding (center (φ k)) = x' (φ k) := W.embedding.right_inv' (hxt k)
  have hnew := W.exists_recentered_strict_of_flow_time_towers (S (φ k)) (center (φ k)) t
    (hc k) (by rw [hright]; exact hQ k) W.time_mem
    (by rw [hright]; exact hwin k)
    U hU (hbuff k) ((hcmp k).trans hKU) (A' (φ k)) B
    (fun s y hy v => hA'₀ (φ k) s y hy v) hB₀ (Icc c t) L
    (fun q s hs y => hA' (φ k) q s hs y) hB
    (by rw [hright]; exact hsrc k) (hmod k)
    (fun i j hij s hs y hy => by
      have hh := hk (i, j) hij s hs y hy
      simpa only [hright] using hh)
  apply (hbad k).1
  rw [hright] at hnew
  exact hnew

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
