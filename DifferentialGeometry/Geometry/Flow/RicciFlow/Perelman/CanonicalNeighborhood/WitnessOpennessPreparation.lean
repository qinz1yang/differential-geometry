import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessLocalTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessModelRecenter
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance opennessPreparationC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [T2Space M] [SigmaCompactSpace M] in
theorem WindowedModelWitness.exists_common_source_slab
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t)
    (hwindow : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular) :
    ∃ a c b : ℝ, a < c ∧ c < t - (eps * S.scalar t x)⁻¹ ∧ t < b ∧
      Icc a b ⊆ D.carrier ∧ Ioo a b ⊆ D.regular := by
  let lo := t - (eps * S.scalar t x)⁻¹
  have hlot : lo < t := sub_lt_self _ (inv_pos.mpr (mul_pos W.eps_pos W.scalar_pos))
  obtain ⟨a, ar, hlo, ha⟩ := D.exists_Icc_regular (hwindow ⟨le_rfl, hlot.le⟩)
  obtain ⟨bl, b, ht, hb⟩ := D.exists_Icc_regular (hwindow ⟨hlot.le, le_rfl⟩)
  have hreg : Icc a b ⊆ D.regular := by
    intro r hr
    by_cases hrl : r < lo
    · exact ha ⟨hr.1, (hrl.trans hlo.2).le⟩
    · by_cases hrt : r ≤ t
      · exact hwindow ⟨le_of_not_gt hrl, hrt⟩
      · exact hb ⟨(ht.1.trans (lt_of_not_ge hrt)).le, hr.2⟩
  refine ⟨a, (a + lo) / 2, b, ?_, ?_, ht.2, hreg.trans D.regular_subset, ?_⟩
  · linarith [hlo.1]
  · change (a + lo) / 2 < lo
    linarith [hlo.1]
  · exact Ioo_subset_Icc_self.trans hreg


theorem WindowedModelWitness.exists_common_raw_time_towers
    (hS : IsSolutionOn S) {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) :
    ∃ (U : TopologicalSpace.Opens W.model.M)
      (A B : ℕ → ℝ → Tensor0SField (I := I3) (M := W.model.M) (n := ∞) 2),
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
        (modelRadius eps + 1) ⊆ U ∧ (U : Set W.model.M) ⊆ W.embedding.source ∧
      (∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I3 y,
        A 0 s y v = (S.base.metric s).inner (W.embedding y)
          (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1))) ∧
      (∀ s, B 0 s = metricTensorField (W.model.S.base.metric s)) ∧
      (∀ q s, s ∈ Icc c b → ∀ y,
        HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) (Icc c b) s) ∧
      (∀ q s, s ∈ Icc (-2 * modelDepth eps - 1) 0 → ∀ y,
        HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y)
          (Icc (-2 * modelDepth eps - 1) 0) s) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  let K := riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps + 1)
  have hK : IsCompact K := RiemannianMetricComplete.closedEBall_isCompact hcomplete _ _
  obtain ⟨chi, hchi, _hcompact, hchiOne, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I3) hK W.embedding.open_source W.buffered_ball
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hchiOne
  let U : TopologicalSpace.Opens W.model.M := ⟨V ∩ W.embedding.source, hV.inter W.embedding.open_source⟩
  have hKU : K ⊆ U := fun y hy => ⟨hKV hy, W.buffered_ball hy⟩
  have hU : (U : Set W.model.M) ⊆ W.embedding.source := fun _ hy => hy.2
  have hOne (y : W.model.M) (hy : y ∈ U) : chi y = 1 := hVone hy.1
  obtain ⟨A, hA₀, _hout, hA⟩ := exists_closedWindow_pullback_metric_time_tower S hS
    hac hcb hslab hreg W.embedding chi hchi hsupp
  have hdepth : 0 < modelDepth eps := inv_pos.mpr W.eps_pos
  have hmodelSlab : Icc (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.carrier := by
    intro r hr
    exact hr.2
  have hmodelReg : Ioo (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.regular := by
    intro r hr
    exact hr.2
  obtain ⟨B, hB₀, hB⟩ := exists_closedWindow_metric_time_fields W.model.S W.model.isSolution
    (a := -2 * modelDepth eps - 2) (c := -2 * modelDepth eps - 1) (b := 0)
    (by linarith) (by linarith) hmodelSlab hmodelReg
  refine ⟨U, A, B, hKU, hU, ?_, hB₀, hA, fun q s hs y => (hB q s hs y).2⟩
  intro s y hy v
  simpa only [hOne y hy, one_mul] using hA₀ s y (hU hy) v

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.eventually_admissible_recentering
    (hS : IsSolutionOn S) {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    {a c b : ℝ} (hac : a < c) (hclo : c < t - (eps * S.scalar t x)⁻¹) (htb : t < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) :
    ∀ᶠ q : M × ℝ in 𝓝 (x, t), q.1 ∈ W.embedding.target ∧
      ∃ hc : 0 < W.model.S.scalar 0 (W.embedding.symm q.1),
      ∃ _hQ : 0 < S.scalar q.2 q.1,
        riemannianClosedBallOf
          (scaleMetric (W.model.S.scalar 0 (W.embedding.symm q.1)) hc (W.model.S.base.metric 0))
          (W.embedding.symm q.1) (modelRadius eps + 1) ⊆ W.embedding.source ∧
        riemannianClosedBallOf
          (scaleMetric (W.model.S.scalar 0 (W.embedding.symm q.1)) hc (W.model.S.base.metric 0))
          (W.embedding.symm q.1) (modelRadius eps) ⊆
            riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps + 1) ∧
        q.2 ∈ D.carrier ∧ Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular ∧
        MapsTo (parabolicTime q.2 (S.scalar q.2 q.1)) (Icc (-modelDepth eps) 0) (Icc c b) ∧
        MapsTo (parabolicTime 0 (W.model.S.scalar 0 (W.embedding.symm q.1))) (Icc (-modelDepth eps) 0)
          (Icc (-2 * modelDepth eps - 1) 0) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdepth : 0 < modelDepth eps := inv_pos.mpr W.eps_pos
  have hR : 0 < modelRadius eps := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have hback : t - (eps * S.scalar t x)⁻¹ < t :=
    sub_lt_self _ (inv_pos.mpr (mul_pos W.eps_pos W.scalar_pos))
  have htreg : t ∈ D.regular := hreg ⟨(hac.trans hclo).trans hback, htb⟩
  have hcar : D.carrier ×ˢ (Set.univ : Set M) ∈ 𝓝 (t, x) :=
    Filter.mem_of_superset ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨htreg, mem_univ x⟩)
      (fun q hq => ⟨D.regular_subset hq.1, hq.2⟩)
  have hScalarAt : ContinuousAt (fun q : ℝ × M => S.scalar q.1 q.2) (t, x) :=
    (hS.scalarCont (t, x) ⟨W.time_mem, mem_univ x⟩).continuousAt hcar
  have hswap : Continuous (fun q : M × ℝ => (q.2, q.1)) :=
    continuous_snd.prodMk continuous_fst
  have hQlim : Tendsto (fun q : M × ℝ => S.scalar q.2 q.1) (𝓝 (x, t)) (𝓝 (S.scalar t x)) := by
    exact Filter.Tendsto.comp (g := fun q : ℝ × M => S.scalar q.1 q.2)
      (f := fun q : M × ℝ => (q.2, q.1)) hScalarAt (hswap.tendsto (x, t))
  have hLowLim : Tendsto (fun q : M × ℝ => q.2 - (eps * S.scalar q.2 q.1)⁻¹)
      (𝓝 (x, t)) (𝓝 (t - (eps * S.scalar t x)⁻¹)) :=
    (continuous_snd.tendsto (x, t)).sub
      ((tendsto_const_nhds.mul hQlim).inv₀ (mul_ne_zero W.eps_pos.ne' W.scalar_pos.ne'))
  have hp : W.model.basepoint ∈ W.embedding.source := by
    apply W.buffered_ball
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hx : x ∈ W.embedding.target := by
    simpa only [W.base_map] using W.embedding.map_source' hp
  have hinv : W.embedding.symm x = W.model.basepoint :=
    (congrArg (W.embedding.symm : M → W.model.M) W.base_map.symm).trans (W.embedding.left_inv' hp)
  have hInvLim : Tendsto (fun q : M × ℝ => W.embedding.symm q.1) (𝓝 (x, t)) (𝓝 W.model.basepoint) := by
    have hh := (W.embedding.symm.contMDiffOn_toFun.continuousOn.continuousAt
      (W.embedding.open_target.mem_nhds hx)).tendsto.comp (continuous_fst.tendsto (x, t))
    rw [hinv] at hh
    exact hh
  have hscalar : ContinuousAt (fun z => W.model.S.scalar 0 z) W.model.basepoint :=
    (metricScalar_smooth (W.model.S.base.metric 0)).continuous.continuousAt
  have hcone : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hcLim : Tendsto (fun q : M × ℝ => W.model.S.scalar 0 (W.embedding.symm q.1))
      (𝓝 (x, t)) (𝓝 (1 : ℝ)) := by
    have hh := hscalar.tendsto.comp hInvLim
    rw [hcone] at hh
    exact hh
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hBuff := eventually_scaled_closedBall_subset (W.model.S.base.metric 0) hcomplete
    W.model.basepoint (show 0 ≤ modelRadius eps + 1 by linarith) W.embedding.open_source
    W.buffered_ball (fun z => W.model.S.scalar 0 z) hscalar hcone
  have hOldSmall : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) ⊆
      riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps + 1) := by
    intro y hy
    have hyR : riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤
        ENNReal.ofReal (modelRadius eps) := hy
    exact hyR.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < modelRadius eps + 1)).mpr
      (by linarith : modelRadius eps < modelRadius eps + 1))
  have hCmp := eventually_scaled_closedBall_subset (W.model.S.base.metric 0) hcomplete
    W.model.basepoint hR.le (isOpen_lt (continuous_riemannianEDist (W.model.S.base.metric 0)
      W.model.basepoint) continuous_const) hOldSmall (fun z => W.model.S.scalar 0 z) hscalar hcone
  filter_upwards [(continuous_fst.tendsto (x, t)).eventually (W.embedding.open_target.mem_nhds hx),
    hQlim.eventually (Ioi_mem_nhds W.scalar_pos), hLowLim.eventually (Ioi_mem_nhds hclo),
    (continuous_snd.tendsto (x, t)).eventually (Iio_mem_nhds htb),
    hcLim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hInvLim.eventually hBuff, hInvLim.eventually hCmp] with q hqt hqpos hlo hhi hcHalf hb hcball
  obtain ⟨hc, hbuff⟩ := hb
  obtain ⟨_hc', hcmp⟩ := hcball
  refine ⟨hqt, hc, hqpos, hbuff, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤ ENNReal.ofReal (modelRadius eps + 1)
    exact (hcmp hy).le
  · have hbackq := sub_lt_self q.2 (inv_pos.mpr (mul_pos W.eps_pos hqpos))
    exact hslab ⟨((hac.trans hlo).trans hbackq).le, hhi.le⟩
  · intro r hr
    exact hreg ⟨(hac.trans hlo).trans_le hr.1, hr.2.trans_lt hhi⟩
  · intro s hs
    have hl : q.2 - (eps * S.scalar q.2 q.1)⁻¹ ≤ parabolicTime q.2 (S.scalar q.2 q.1) s := by
      simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg, add_comm] using
        add_le_add_left (div_le_div_of_nonneg_right hs.1 hqpos.le) q.2
    have hu : parabolicTime q.2 (S.scalar q.2 q.1) s ≤ q.2 := by
      exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hqpos.le)
    exact ⟨hlo.le.trans hl, hu.trans hhi.le⟩
  · intro s hs
    simp only [parabolicTime, zero_add, mem_Icc]
    constructor
    · apply (le_div_iff₀ hc).mpr
      have hm := mul_le_mul_of_nonneg_left hcHalf.le (show 0 ≤ 2 * modelDepth eps + 1 by linarith)
      nlinarith [hs.1]
    · exact div_nonpos_of_nonpos_of_nonneg hs.2 hc.le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
